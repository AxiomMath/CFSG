module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4Fixed
public import CFSG.RankThree.Chevalley.EvenFourCommutingSL2
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SL2Pair
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Split

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped MatrixGroups commutatorElement

namespace F4InnerExAux

theorem isElemAbelian_sup_of_comm {Ω : Type*} [Group Ω] {p : ℕ} {P Q : Subgroup Ω}
    (hP : IsElemAbelian p P) (hQ : IsElemAbelian p Q)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) : IsElemAbelian p (P ⊔ Q) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, u, hu, hxu⟩ := i224_mem_sup_of_comm hc a.2
    obtain ⟨x', hx', u', hu', hxu'⟩ := i224_mem_sup_of_comm hc b.2
    apply Subtype.ext
    change (a : Ω) * b = b * a
    rw [hxu, hxu']
    have e1 : ∀ s ∈ P, ∀ t ∈ P, s * t = t * s := fun s hs t ht =>
      congrArg Subtype.val (hP.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    have e2 : ∀ s ∈ Q, ∀ t ∈ Q, s * t = t * s := fun s hs t ht =>
      congrArg Subtype.val (hQ.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    calc x * u * (x' * u') = x * (u * x') * u' := by group
      _ = x * (x' * u) * u' := by rw [← hc x' hx' u hu]
      _ = (x * x') * (u * u') := by group
      _ = (x' * x) * (u' * u) := by rw [e1 x hx x' hx', e2 u hu u' hu']
      _ = x' * (x * u') * u := by group
      _ = x' * (u' * x) * u := by rw [hc x hx u' hu']
      _ = x' * u' * (x * u) := by group
  · obtain ⟨x, hx, u, hu, rfl⟩ := i224_mem_sup_of_comm hc hy
    have hxp : x ^ p = 1 := hP.2 x hx
    have hup : u ^ p = 1 := hQ.2 u hu
    have e1 : Commute x u := hc x hx u hu
    rw [e1.mul_pow, hxp, hup, one_mul]

theorem isElemAbelian_zpowers {Ω : Type*} [Group Ω] {x : Ω} (hx : x ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem le_normalizer_zpowers_of_commute {Ω : Type*} [Group Ω] {S : Subgroup Ω} {u : Ω}
    (h : ∀ t ∈ S, Commute t u) : S ≤ Subgroup.normalizer (Subgroup.zpowers u : Set Ω) := by
  intro t ht
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  exact ((h t ht).symm.zpow_left n).eq

section SL2

open CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth

variable {F : Type} [Field F]

theorem u1_sq (h2 : (2 : F) = 0) : (u1 : SL(2, F)) ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u1, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

theorem u1_ne_one : (u1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [u1] at this

theorem c3_zpow_commute_u1 {n : ℤ} (h : Commute ((c3 : SL(2, F)) ^ n) u1) :
    (c3 : SL(2, F)) ^ n = 1 := by
  have hord : orderOf (c3 : SL(2, F)) = 3 := orderOf_eq_prime c3_pow_three c3_ne_one
  have h1 : (c3 : SL(2, F)) ^ n = c3 ^ (n % 3) := by
    have := zpow_mod_orderOf (c3 : SL(2, F)) n
    rw [hord] at this
    simpa using this.symm
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h0 | h0 | h0
  · rw [h1, h0, zpow_zero]
  · rw [h1, h0, zpow_one] at h ⊢
    exact absurd h c3_not_commute_u1
  · have e : (c3 : SL(2, F)) ^ (2 : ℤ) = c3 ^ 2 := by rw [zpow_two, sq]
    rw [h1, h0, e] at h ⊢
    exact absurd h c3_sq_not_commute_u1

theorem three_sl2_data {G : Type*} [Group G] (h2 : (2 : F) = 0) (ψ : Fin 3 → SL(2, F) →* G)
    (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    ψ 0 c3 ^ 3 = 1 ∧ ψ 1 c3 ^ 3 = 1 ∧ ψ 2 u1 ^ 2 = 1 ∧ ψ 2 u1 ≠ 1 ∧ ψ 0 c3 ≠ 1 ∧ ψ 1 c3 ≠ 1 ∧
      Commute (ψ 0 c3) (ψ 1 c3) ∧ Commute (ψ 0 c3) (ψ 2 u1) ∧ Commute (ψ 1 c3) (ψ 2 u1) ∧
      Subgroup.zpowers (ψ 0 c3) ⊓ Subgroup.zpowers (ψ 1 c3) = ⊥ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hc 0 1 (by decide) _ _, hc 0 2 (by decide) _ _,
    hc 1 2 (by decide) _ _, ?_⟩
  · rw [← map_pow, c3_pow_three, map_one]
  · rw [← map_pow, c3_pow_three, map_one]
  · rw [← map_pow, u1_sq h2, map_one]
  · intro h
    exact u1_ne_one (hψ 2 (h.trans (map_one (ψ 2)).symm))
  · intro h
    exact c3_ne_one (hψ 0 (h.trans (map_one (ψ 0)).symm))
  · intro h
    exact c3_ne_one (hψ 1 (h.trans (map_one (ψ 1)).symm))
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz0, hz1⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz0
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hz1
    have hcomm : Commute (ψ 0 c3 ^ n) (ψ 0 u1) := by
      rw [← hm]
      exact (hc 1 0 (by decide) c3 u1).zpow_left m
    have hcomm' : Commute ((c3 : SL(2, F)) ^ n) u1 := by
      apply hψ 0
      rw [map_mul, map_mul, map_zpow]
      exact hcomm.eq
    have h1 := c3_zpow_commute_u1 hcomm'
    rw [Subgroup.mem_bot, ← map_zpow, h1, map_one]

end SL2

section Counting

variable {X : Type} [Group X] [Finite X]

theorem card_le_three_mul {K B : Subgroup X} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (Θ : MulAut ↥K →* Multiplicative (ZMod (2 * 3)))
    (hΘ : Θ.ker ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    (hno : ∀ y ∈ B, Bal209F4Aux.InnerAt K y → y ∈ Subgroup.centralizer (K : Set X)) :
    Nat.card B ≤ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) := by
  classical
  let ρ : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let f : ↥B →* Multiplicative (ZMod (2 * 3)) := Θ.comp ρ
  have hker : ∀ b : ↥B, f b = 1 → (b : X) ∈ Subgroup.centralizer (K : Set X) := by
    intro b hb
    have hmem : ρ b ∈ Θ.ker := hb
    obtain ⟨k, hk⟩ := hΘ hmem
    apply hno b b.2
    refine ⟨(k : X), k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have key : (k : X) * x * (k : X)⁻¹ = (b : X) * x * (b : X)⁻¹ := by
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : X)) hk
      simpa [MulAut.conj_apply, ρ] using this
    have e : (k : X)⁻¹ * b * x = x * ((k : X)⁻¹ * b) := by
      calc (k : X)⁻¹ * b * x = (k : X)⁻¹ * (b * x * (b : X)⁻¹) * b := by group
        _ = (k : X)⁻¹ * ((k : X) * x * (k : X)⁻¹) * b := by rw [key]
        _ = x * ((k : X)⁻¹ * b) := by group
    exact e.symm
  obtain ⟨m, hm⟩ := i271_exists_card_eq Nat.prime_three hBel
  have hr6 : Nat.card f.range ∣ 2 * 3 := by
    have h := Subgroup.card_subgroup_dvd_card f.range
    rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
  have hr3m : Nat.card f.range ∣ 3 ^ m := hm ▸ Subgroup.card_range_dvd f
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hr3m
  have hk1 : k ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h9 : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
    have h6 : 3 ^ k ≤ 2 * 3 := Nat.le_of_dvd (by norm_num) (hk ▸ hr6)
    norm_num at h9 h6
    omega
  have hr3 : Nat.card f.range ≤ 3 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have hkerD : Nat.card f.ker ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) := by
    rw [← Subgroup.card_map_of_injective (f := B.subtype) B.subtype_injective (K := f.ker)]
    apply Subgroup.card_le_of_le
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.mem_inf.2 ⟨b.2, hker b hb⟩
  calc Nat.card B = Nat.card f.ker * Nat.card f.range := (Subgroup.card_ker_mul_card_range f).symm
    _ ≤ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) * 3 := Nat.mul_le_mul hkerD hr3
    _ = 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) := mul_comm _ _

theorem rank_lt_twoLocal {K B : Subgroup X} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set X) → z = 1)
    (Θ : MulAut ↥K →* Multiplicative (ZMod (2 * 3)))
    (hΘ : Θ.ker ≤ (MulAut.conj : ↥K →* MulAut ↥K).range)
    (hno : ∀ y ∈ B, Bal209F4Aux.InnerAt K y → y ∈ Subgroup.centralizer (K : Set X))
    {x₀ x₁ u : X} (hx₀K : x₀ ∈ K) (hx₁K : x₁ ∈ K) (huK : u ∈ K)
    (hx₀ : x₀ ^ 3 = 1) (hx₁ : x₁ ^ 3 = 1) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    (hx₀1 : x₀ ≠ 1) (hx₁1 : x₁ ≠ 1) (h01 : Commute x₀ x₁) (h0u : Commute x₀ u)
    (h1u : Commute x₁ u) (hind : Subgroup.zpowers x₀ ⊓ Subgroup.zpowers x₁ = ⊥) :
    CFSG.Open.pRank 3 B < GLATwoLocalRank 3 X := by
  classical
  have hBle := card_le_three_mul hBel hBN Θ hΘ hno
  set D : Subgroup X := B ⊓ Subgroup.centralizer (K : Set X) with hDdef
  have hDel : IsElemAbelian 3 D := i271_isElemAbelian_of_le hBel inf_le_left
  obtain ⟨c₀, hc₀⟩ := i271_exists_card_eq Nat.prime_three hDel
  obtain ⟨m, hm⟩ := i271_exists_card_eq Nat.prime_three hBel
  have hrk : CFSG.Open.pRank 3 B = m := i271_pRank_eq Nat.prime_three hBel hm
  have hmc : m ≤ c₀ + 1 := by
    have h1 : 3 ^ m ≤ 3 ^ (c₀ + 1) := by
      rw [← hm, pow_succ, mul_comm, ← hc₀]
      exact hBle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
  have hcomm01 : ∀ a ∈ Subgroup.zpowers x₀, ∀ b ∈ Subgroup.zpowers x₁, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (h01.zpow_zpow i j).eq
  have hz0card : Nat.card (Subgroup.zpowers x₀) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx₀ hx₀1]
  have hz1card : Nat.card (Subgroup.zpowers x₁) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx₁ hx₁1]
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup X, E = Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ := ⟨_, rfl⟩
  have hEK : E ≤ K := by
    rw [hEdef]
    exact sup_le (Subgroup.zpowers_le.2 hx₀K) (Subgroup.zpowers_le.2 hx₁K)
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hEdef, i224_card_sup hcomm01 hind, hz0card, hz1card]
    norm_num
  have hEel : IsElemAbelian 3 E := by
    rw [hEdef]
    exact isElemAbelian_sup_of_comm (isElemAbelian_zpowers hx₀) (isElemAbelian_zpowers hx₁) hcomm01
  have hED : ∀ a ∈ E, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 a (hEK ha)
  have hEDbot : E ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzE, hzD⟩ := Subgroup.mem_inf.1 hz
    exact (Subgroup.mem_bot).2 (hZ z (hEK hzE) (Subgroup.mem_inf.1 hzD).2)
  have hTel : IsElemAbelian 3 (E ⊔ D) := isElemAbelian_sup_of_comm hEel hDel hED
  have hTcard : Nat.card ↥(E ⊔ D) = 3 ^ (2 + c₀) := by
    rw [i224_card_sup hED hEDbot, hEcard, hc₀, pow_add]
  have hEle : E ≤ Subgroup.centralizer ({u} : Set X) := by
    rw [hEdef]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h0u.eq
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h1u.eq
  have hDle : D ≤ Subgroup.centralizer ({u} : Set X) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ht).2 u huK).symm
  have hTle : E ⊔ D ≤ Subgroup.centralizer ({u} : Set X) := sup_le hEle hDle
  have hTN : E ⊔ D ≤ Subgroup.normalizer (Subgroup.zpowers u : Set X) :=
    le_normalizer_zpowers_of_commute fun t ht => Subgroup.mem_centralizer_singleton_iff.1 (hTle ht)
  have hPne : Subgroup.zpowers u ≠ ⊥ := fun h => hu1 (Subgroup.zpowers_eq_bot.1 h)
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1, pow_one]
  have hloc : 2 + c₀ ≤ GLATwoLocalRank 3 X :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
      (by norm_num) hPne hP2 hTel hTN hTcard
  rw [hrk]
  omega

end Counting

theorem congr_eq_conj_imp {K C : Type} [Group K] [Group C] (e : K ≃* C) (α : MulAut K) (g : C)
    (h : MulAut.congr e α = MulAut.conj g) : α = MulAut.conj (e.symm g) := by
  refine MulEquiv.ext fun k => ?_
  apply e.injective
  have hk := congrArg (fun φ : MulAut C => φ (e k)) h
  simp only [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.symm_apply_apply] at hk
  rw [MulAut.conj_apply, map_mul, map_mul]
  simp only [MulEquiv.apply_symm_apply, map_inv]
  rw [← hk]
  simp

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

end F4InnerExAux

section Final

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Blueprint.Multiplier

set_option linter.unusedSectionVars false


namespace F4InnerExAux

theorem center_bot_and_equiv {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hLie : IsLieQuot Y IsF4EightIndex) :
    Subgroup.center Y = ⊥ ∧ Nonempty (Y ≃* adjointGroup Tag.F4 (GaloisField 2 3)) := by
  classical
  have hKq : CFSG.IsQuasisimple Y := isQuasisimple_of_open hY
  obtain ⟨d, hdF, ⟨eL⟩⟩ := hLie
  obtain ⟨d1, hv⟩ := d
  have hq8 : ∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.F4 q ∧ IsTwoPow q 3 := by
    cases d1 with
    | F4 q => exact ⟨q, rfl, hdF⟩
    | _ => simp [IsF4EightIndex] at hdF
  obtain ⟨q, rfl, hq3⟩ := hq8
  obtain ⟨hq2, hqe⟩ := hq3
  have hLM : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.F4 q, hv⟩).Group
      .F4 0 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, rfl⟩, Or.inr ⟨rfl, ⟨TauCeti.LieTypeIndex.F4 q, hv⟩, ⟨hq2, hqe⟩,
      ⟨MulEquiv.refl _⟩⟩⟩
  have hZK : Subgroup.center Y = ⊥ := by
    have h := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hKq eL hLM
    have h1 : (genericOrders .F4 0 2 3).1 * (genericOrders .F4 0 2 3).2 *
        ((exceptionalOrders .F4 0 2 3).1 * (exceptionalOrders .F4 0 2 3).2) = 1 := by
      decide
    rw [h1] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 h)
  refine ⟨hZK, ?_⟩
  have hK'card : Nat.card (GaloisField 2 3) = q.card := by
    rw [GaloisField.card 2 3 (by norm_num), TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨eB⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesEven).f4 q hv hq2 (GaloisField 2 3) hK'card
  let eKq : Y ≃* Y ⧸ Subgroup.center Y :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZK.symm)
  exact ⟨eKq.trans (eL.trans (eB.symm.trans (F4FixedAux.adjointEquiv Tag.F4 (GaloisField 2 3))))⟩

theorem chevalley_data {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    (hLie : IsLieQuot Y IsF4EightIndex) :
    Subgroup.center Y = ⊥ ∧ ∃ F : Type, ∃ _ : Field F, (2 : F) = 0 ∧
      (∃ Θ : MulAut Y →* Multiplicative (ZMod (2 * 3)),
        Θ.ker ≤ (MulAut.conj : Y →* MulAut Y).range) ∧
      ∃ ψ : Fin 3 → SL(2, F) →* Y, (∀ i, Function.Injective (ψ i)) ∧
        ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := by
  obtain ⟨hZ, ⟨e⟩⟩ := center_bot_and_equiv hY hLie
  have hKcard : Nat.card (GaloisField 2 3) = 2 ^ 3 := GaloisField.card 2 3 (by norm_num)
  refine ⟨hZ, GaloisField 2 3, inferInstance, ?_, ?_, ?_⟩
  · have h := CharP.cast_eq_zero (GaloisField 2 3) 2
    simpa using h
  · haveI : CharP (GaloisField 2 3) CFSG.LieType.Ree.ReeTag.F4.prime :=
      inferInstanceAs (CharP (GaloisField 2 3) 2)
    obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ :=
      CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := 3) (by norm_num)
        (GaloisField 2 3) hKcard
    refine ⟨Θ.comp (MulAut.congr e).toMonoidHom, fun α hα => ?_⟩
    have h1 : MulAut.congr e α ∈ Θ.ker := hα
    rw [hΘker] at h1
    obtain ⟨g, hg⟩ := h1
    exact ⟨e.symm g, (congr_eq_conj_imp e α g hg.symm).symm⟩
  · obtain ⟨ι, hinj, hc⟩ :=
      CFSG.RankThree.Chevalley.even_higher_ordinary_exceptional_four_commuting_faithful_SL2
        (GaloisField 2 3) Tag.F4 (Or.inl rfl)
    refine ⟨fun i => e.symm.toMonoidHom.comp (ι i.castSucc), fun i => ?_, fun i j hij A B => ?_⟩
    · exact e.symm.injective.comp (hinj i.castSucc)
    · have h := hc i.castSucc j.castSucc ((Fin.castSucc_injective 3).ne hij) A B
      change e.symm (ι i.castSucc A) * e.symm (ι j.castSucc B) =
        e.symm (ι j.castSucc B) * e.symm (ι i.castSucc A)
      rw [← map_mul, ← map_mul, h]

end F4InnerExAux

theorem f4InnerEx_holds : Bal209F4Aux.F4InnerEx := by
  intro X _ _ _hKG K B hK hBSC hBN hrank hLie
  by_contra hcon
  push Not at hcon
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  obtain ⟨hZ, F, hF, h2, ⟨Θ, hΘ⟩, ψ, hψ, hc⟩ := F4InnerExAux.chevalley_data hK.2.2 hLie
  have hZ' : ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set X) → z = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc (g : X) g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  let ψ' : Fin 3 → SL(2, F) →* X := fun i => K.subtype.comp (ψ i)
  have hψ' : ∀ i, Function.Injective (ψ' i) := fun i => K.subtype_injective.comp (hψ i)
  have hc' : ∀ i j, i ≠ j → ∀ A B, Commute (ψ' i A) (ψ' j B) := fun i j hij A B =>
    (hc i j hij A B).map K.subtype
  obtain ⟨hx0, hx1, hu2, hu1, hx01, hx11, h01, h0u, h1u, hind⟩ :=
    F4InnerExAux.three_sl2_data h2 ψ' hψ' hc'
  have hlt := F4InnerExAux.rank_lt_twoLocal hBel hBN hZ' Θ hΘ hcon (ψ 0 _).2 (ψ 1 _).2 (ψ 2 _).2
    hx0 hx1 hu2 hu1 hx01 hx11 h01 h0u h1u hind
  exact absurd hrank (not_le.2 hlt)

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
