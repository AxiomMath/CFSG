module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Tools

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.Open (aschbacherThm5Core aschbacherThm5OddCore)
open scoped MatrixGroups

theorem nonempty_mulEquiv_fin_zmod_two {E : Type*} [Group E] [Finite E]
    (hcomm : ∀ a b : E, a * b = b * a) (hE : ∀ x : E, x ^ 2 = 1) {n : ℕ}
    (hcard : Nat.card E = 2 ^ n) : Nonempty (E ≃* Multiplicative (Fin n → ZMod 2)) := by
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  have hA : ∀ x : Additive E, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, hE]
    rfl
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule hA
  let _ : Fintype (Additive E) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive E) = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, ← Nat.card_congr Additive.ofMul, hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  exact ⟨AddEquiv.toMultiplicativeRight
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hfin).equivFun.toAddEquiv⟩

noncomputable def mulEquivOfCommute {Y : Type*} [Group Y] {A B C : Subgroup Y} (hAC : A ≤ C)
    (hBC : B ≤ C) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : A ⊓ B = ⊥)
    (hsup : A ⊔ B = C) : A × B ≃* C :=
  MulEquiv.ofBijective (MonoidHom.noncommCoprod (inclusion hAC) (inclusion hBC)
      fun a b => Subtype.ext (hcomm a a.2 b b.2))
    ⟨fun x y hxy => by
      have h := congrArg Subtype.val hxy
      exact Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hinf) h,
    fun c => by
      have hc : (c : Y) ∈ ((A ⊔ B : Subgroup Y) : Set Y) := hsup ▸ c.2
      have hAC' : A ≤ centralizer (B : Set Y) := fun a ha =>
        mem_centralizer_iff.mpr fun b hb => (hcomm a ha b hb).symm
      have hAB : A ≤ normalizer (B : Set Y) := hAC'.trans (centralizer_le_normalizer _)
      rw [coe_mul_of_left_le_normalizer_right A B hAB] at hc
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hc
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩⟩

section Bar

variable {X : Type} [Group X] [Finite X]

theorem card_eq_of_thm3Alt3 {Qb Tb : Subgroup X} (hTbN : Tb ≤ normalizer (Qb : Set X))
    (hQT : Qb ⊓ Tb = ⊥) (hT2 : IsPGroup 2 Tb) {n : ℕ} (hn : 2 ≤ n)
    (hUeq : AschbacherTheorem3.oTwoPrime (Qb ⊔ Tb) =
      CFSG.Open.pCoreOf 2 (Qb ⊔ Tb) ⊔ AschbacherTheorem3.oTwoPrime Qb)
    (hinf : CFSG.Open.pCoreOf 2 (Qb ⊔ Tb) ⊓ AschbacherTheorem3.oTwoPrime Qb = ⊥)
    (hcomm : ⁅CFSG.Open.pCoreOf 2 (Qb ⊔ Tb), AschbacherTheorem3.oTwoPrime Qb⁆ = ⊥)
    (hel : CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 (Qb ⊔ Tb)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (Qb ⊔ Tb)) = 2 ^ n)
    (eL : AschbacherTheorem3.oTwoPrime Qb ≃* PSL(2, GaloisField 2 n)) :
    Nat.card Tb = 2 ^ n ∧ ∃ m : ℕ, Odd m ∧ Nat.card Qb = 2 ^ n * m := by
  set O2 := CFSG.Open.pCoreOf 2 (Qb ⊔ Tb)
  set Lq := AschbacherTheorem3.oTwoPrime Qb
  have hLqQ : Lq ≤ Qb := oUpperTwoPrime_le Qb
  have hO2U : O2 ≤ Qb ⊔ Tb := map_subtype_le _
  have hUN : Qb ⊔ Tb ≤ normalizer (Qb : Set X) := sup_le le_normalizer hTbN
  have hO2Q : Qb ⊓ O2 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ Lq := subset_closure ⟨hx.1, 1, by simpa using hel.2 x hx.2⟩
    have : x ∈ O2 ⊓ Lq := ⟨hx.2, hxL⟩
    rwa [hinf] at this
  have hQpos : 0 < Nat.card Qb := Nat.card_pos
  have h1 : Nat.card O2 ≤ Nat.card Tb := by
    have hc1 := AschbacherTheorem3.card_sup_of_le_normalizer (hO2U.trans hUN) hO2Q
    have hc2 := AschbacherTheorem3.card_sup_of_le_normalizer hTbN hQT
    have hle : Nat.card (Qb ⊔ O2 : Subgroup X) ≤ Nat.card (Qb ⊔ Tb : Subgroup X) :=
      card_le_of_le (sup_le le_sup_left hO2U)
    rw [hc1, hc2] at hle
    exact Nat.le_of_mul_le_mul_left hle hQpos
  have hLqN : Tb ≤ normalizer (Lq : Set X) :=
    hTbN.trans (normalizer_le_normalizer_oUpperTwoPrime Qb)
  have hLqT : Lq ⊓ Tb = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right _ hLqQ).trans hQT.le)
  have hO2L : O2 ≤ normalizer (Lq : Set X) :=
    (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (centralizer_le_normalizer _)
  have hTU : Tb ≤ AschbacherTheorem3.oTwoPrime (Qb ⊔ Tb) := fun x hx => by
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
    exact subset_closure ⟨mem_sup_right hx, k, by simpa using congrArg Subtype.val hk⟩
  have hLU : Lq ≤ AschbacherTheorem3.oTwoPrime (Qb ⊔ Tb) :=
    closure_mono fun x hx => ⟨mem_sup_left hx.1, hx.2⟩
  have hLpos : 0 < Nat.card Lq := Nat.card_pos
  have h2 : Nat.card Tb ≤ Nat.card O2 := by
    have hc1 := AschbacherTheorem3.card_sup_of_le_normalizer hLqN hLqT
    have hc2 := AschbacherTheorem3.card_sup_of_le_normalizer hO2L (by rw [inf_comm]; exact hinf)
    have hle : Nat.card (Lq ⊔ Tb : Subgroup X) ≤ Nat.card (Lq ⊔ O2 : Subgroup X) := by
      refine card_le_of_le (sup_le le_sup_left ?_)
      rw [sup_comm]
      exact hTU.trans hUeq.le
    rw [hc1, hc2] at hle
    exact Nat.le_of_mul_le_mul_left hle hLpos
  refine ⟨le_antisymm h2 (hcard ▸ h1) |>.trans hcard, ?_⟩
  have hnorm : (Lq.subgroupOf Qb).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLqQ).mpr
      (le_normalizer.trans (normalizer_le_normalizer_oUpperTwoPrime Qb))
  have hodd := odd_card_quotient_of_oUpperTwoPrime_le (X := Qb) (N := Lq) le_rfl
  have hQcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Lq.subgroupOf Qb)
  rw [Nat.card_congr (subgroupOfEquivOfLe hLqQ).toEquiv, Nat.card_congr eL.toEquiv,
    CFSG.Walter.psl2_even_card (by omega)] at hQcard
  refine ⟨Nat.card (Qb ⧸ Lq.subgroupOf Qb) * ((2 ^ n) ^ 2 - 1), hodd.mul ?_, ?_⟩
  · have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    rw [Nat.odd_sub this]
    simp [Nat.even_pow, show n ≠ 0 by omega]
  · rw [hQcard]
    ring

end Bar

section Bridge

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_bar_self_mul (Q : Subgroup G) :
    Nat.card (bar Q Q) * Nat.card (oddCoreIn Q) = Nat.card Q := by
  let e : Q ⧸ aschbacherThm5OddCore Q ≃* bar Q Q :=
    (MonoidHom.ofInjective (quotientEmbedding_injective Q)).trans
      (MulEquiv.subgroupCongr (bar_D_eq_range Q).symm)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherThm5OddCore Q),
    Nat.card_congr e.toEquiv, oddCoreIn, card_map_of_injective Q.subtype_injective]
  rfl

theorem exists_surjective_oUpperTwoPrime {Q T : Subgroup G} (hTH : T ≤ normalizer (Q : Set G)) :
    ∃ ρ : oUpperTwoPrime (Q ⊔ T) →* AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T),
      Function.Surjective ρ ∧ ρ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T)) := by
  have hKH : Q ⊔ T ≤ normalizer (Q : Set G) := sup_le le_normalizer hTH
  have hVN : oUpperTwoPrime (Q ⊔ T) ≤ normalizer (Q : Set G) :=
    (oUpperTwoPrime_le _).trans hKH
  have hbar : bar Q Q ⊔ bar Q T = bar Q (Q ⊔ T) := (bar_sup le_normalizer hTH).symm
  let ρ₀ : oUpperTwoPrime (Q ⊔ T) →* Bar Q := (toBar Q).comp (inclusion hVN)
  have hρ₀ : ∀ v, ρ₀ v ∈ AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T) := by
    set W : Subgroup G := ((AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T)).comap
      (toBar Q)).map (normalizer (Q : Set G)).subtype
    have hle : oUpperTwoPrime (Q ⊔ T) ≤ W := by
      rw [oUpperTwoPrime, closure_le]
      rintro x ⟨hx, k, hk⟩
      refine ⟨⟨x, hKH hx⟩, ?_, rfl⟩
      refine subset_closure ⟨hbar ▸ toBar_mem_bar Q (h := ⟨x, hKH hx⟩) hx, k, ?_⟩
      rw [← map_pow]
      have : (⟨x, hKH hx⟩ : normalizer (Q : Set G)) ^ (2 ^ k) = 1 :=
        Subtype.ext (by simpa using hk)
      rw [this, map_one]
    intro v
    obtain ⟨y, hy, hyv⟩ := hle v.2
    have : y = inclusion hVN v := Subtype.ext hyv
    show toBar Q (inclusion hVN v) ∈ _
    rw [← this]
    exact hy
  let ρ := ρ₀.codRestrict _ hρ₀
  refine ⟨ρ, ?_, ?_⟩
  ·
    have hle : AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T) ≤ ρ₀.range := by
      rw [AschbacherTheorem3.oTwoPrime, closure_le]
      rintro z ⟨hz, k, hk⟩
      rw [hbar] at hz
      obtain ⟨x, hx, rfl⟩ := (mem_bar_iff Q _ z).mp hz
      obtain ⟨y, hy, ⟨j, hj⟩, hyx⟩ := exists_two_element_pow (toBar Q) hk
      have hyQT : (y : G) ∈ Q ⊔ T := by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
        simp only [SubgroupClass.coe_zpow]
        exact zpow_mem hx m
      have hyV : (y : G) ∈ oUpperTwoPrime (Q ⊔ T) :=
        subset_closure ⟨hyQT, j, by simpa using congrArg Subtype.val hj⟩
      exact ⟨⟨y, hyV⟩, by rw [← hyx]; rfl⟩
    intro z
    obtain ⟨v, hv⟩ := hle z.2
    exact ⟨v, Subtype.ext hv⟩
  · ext v
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h1 : ρ₀ v = 1 := congrArg Subtype.val h
      rw [MonoidHom.comp_apply, toBar_eq_one_iff] at h1
      exact h1
    · intro h
      apply Subtype.ext
      show ρ₀ v = 1
      rw [MonoidHom.comp_apply, toBar_eq_one_iff]
      exact h

theorem exists_surjective_of_prod {Q T : Subgroup G} (hTH : T ≤ normalizer (Q : Set G))
    {n : ℕ} {A B : Subgroup (Bar Q)}
    (hsup : A ⊔ B = AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T)) (hinf : A ⊓ B = ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (eA : A ≃* Multiplicative (Fin n → ZMod 2))
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    ∃ φ : oUpperTwoPrime (Q ⊔ T) →*
        Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T)) := by
  obtain ⟨ρ, hρ, hker⟩ := exists_surjective_oUpperTwoPrime hTH
  let σ := mulEquivOfCommute (hsup ▸ le_sup_left) (hsup ▸ le_sup_right) hcomm hinf hsup
  refine ⟨((eA.prodCongr eB).toMonoidHom.comp σ.symm.toMonoidHom).comp ρ,
    (eA.prodCongr eB).surjective.comp (σ.symm.surjective.comp hρ), ?_⟩
  rw [← hker]
  ext v
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [map_eq_one_iff _ (eA.prodCongr eB).injective, map_eq_one_iff _ σ.symm.injective]

theorem exists_surjective_of_thm3Alt3_data {Q T : Subgroup G}
    (hTH : T ≤ normalizer (Q : Set G)) {n : ℕ}
    (hUeq : AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T) =
      CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T) ⊔ AschbacherTheorem3.oTwoPrime (bar Q Q))
    (hinf : CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T) ⊓ AschbacherTheorem3.oTwoPrime (bar Q Q) = ⊥)
    (hcomm : ⁅CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T), AschbacherTheorem3.oTwoPrime (bar Q Q)⁆ = ⊥)
    (hel : CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T)))
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T)) = 2 ^ n)
    (eL : AschbacherTheorem3.oTwoPrime (bar Q Q) ≃* PSL(2, GaloisField 2 n)) :
    ∃ φ : oUpperTwoPrime (Q ⊔ T) →*
        Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T)) := by
  have hc : ∀ a ∈ CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T),
      ∀ b ∈ AschbacherTheorem3.oTwoPrime (bar Q Q), a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
  obtain ⟨eE⟩ := nonempty_mulEquiv_fin_zmod_two
    (E := CFSG.Open.pCoreOf 2 (bar Q Q ⊔ bar Q T)) hel.1.is_comm.comm
    (fun x => Subtype.ext (by simpa using hel.2 x x.2)) hcard
  exact exists_surjective_of_prod hTH hUeq.symm hinf hc eE
    (eL.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)))

theorem exists_surjective_of_thm3Alt3 {Q T : Subgroup G} (hTH : T ≤ normalizer (Q : Set G))
    (h : Thm3Alt3 (bar Q Q) (bar Q T)) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (Q ⊔ T) →*
        Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
      Function.Surjective φ ∧ φ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T)) := by
  obtain ⟨n, hn, hUeq, hinf, hcomm, hel, hcard, ⟨eL⟩⟩ := h
  exact ⟨n, hn, exists_surjective_of_thm3Alt3_data hTH hUeq hinf hcomm hel hcard eL⟩

theorem thm4Case3_of_thm3Alt3 {Q : Subgroup G} (htight : TightlyEmbedded Q) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G)))
    (h : Thm3Alt3 (bar Q Q) (bar Q T)) : Thm4Case3 Q := by
  obtain ⟨n, hn, hUeq, hinf, hcomm, hel, hcard, ⟨eL⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  have hTQg : T ≤ rightConjugate Q g := hT.le.trans inf_le_left
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTQ : T ⊓ Q = ⊥ := two_subgroup_inf_conjugate_eq_bot Q T htight hT2 g hg hTQg
  have hTbN : bar Q T ≤ normalizer (bar Q Q : Set (Bar Q)) := bar_le_normalizer hTH le_normalizer
  have hQT : bar Q Q ⊓ bar Q T = ⊥ := by
    have h1 := bar_inf_of_core_le (D := Q) (Y := T) (Z := Q) (core_le Q)
    rw [hTQ] at h1
    rw [inf_comm, ← h1, bar, bot_subgroupOf, Subgroup.map_bot]
  obtain ⟨hTb, m, hm, hQb⟩ :=
    card_eq_of_thm3Alt3 hTbN hQT (isPGroup_bar hT2) hn hUeq hinf hcomm hel hcard eL
  have hTcard : Nat.card T = 2 ^ n := by rw [← card_bar_of_isPGroup hT2 hTH, hTb]
  have hQcard : Nat.card Q = 2 ^ n * (m * Nat.card (oddCoreIn Q)) := by
    rw [← card_bar_self_mul Q, hQb, mul_assoc]
  have hsyl : IsSylowOf 2 T (rightConjugate Q g) := by
    refine isSylowOf_iff.mpr ⟨hTQg, hT2, ?_⟩
    have h1 := Subgroup.relIndex_mul_card T (rightConjugate Q g)
    rw [inf_eq_left.mpr hTQg, rightConjugate_card, hTcard, hQcard] at h1
    have h2 : T.relIndex (rightConjugate Q g) = m * Nat.card (oddCoreIn Q) :=
      Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans (by ring))
    rw [h2]
    exact (hm.mul (odd_card_oddCoreIn Q)).not_two_dvd_nat
  exact ⟨g, hg, T, hsyl, hTH, n, hn,
    exists_surjective_of_thm3Alt3_data hTH hUeq hinf hcomm hel hcard eL⟩

theorem noThm3Alt3_of_not_thm4Case3 {Q : Subgroup G} (htight : TightlyEmbedded Q)
    (h3 : ¬ Thm4Case3 Q) : NoThm3Alt3 Q :=
  fun _ hg _ hT h => h3 (thm4Case3_of_thm3Alt3 htight hg hT h)

end Bridge

end CFSG.ComponentClassification.Asc75T4

