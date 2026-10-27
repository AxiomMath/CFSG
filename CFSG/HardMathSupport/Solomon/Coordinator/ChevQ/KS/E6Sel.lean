module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.FourUGenericLoc
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CompLift
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6RotRed
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Local
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Cent
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3
import CFSG.LocalAnalysis.GLTheoremA.PartI.BmaxCent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux
open scoped commutatorElement

section Algebra

theorem commutator_eq_bot_of_perfect {G : Type*} [Group G] {A B : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hAB : ⁅A, B⁆ ≤ Subgroup.center G) : ⁅A, B⁆ = ⊥ := by
  have hZ : ∀ H : Subgroup G, ⁅Subgroup.center G, H⁆ = ⊥ := fun H =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.center_le_centralizer _)
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ :=
    eq_bot_iff.2 ((Subgroup.commutator_mono_left hAB).trans (hZ A).le)
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by rw [Subgroup.commutator_comm B A]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := A) (H₂ := A) (H₃ := B) h1 h2
  rwa [hA] at h3

theorem exists_mul_of_mem_iSup_three {Q : Type*} [Group Q] {T : Fin 3 → Subgroup Q}
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, Commute u v) {z : Q}
    (hz : z ∈ ⨆ i, T i) (hzc : ∀ i, ∀ s ∈ T i, Commute s z) :
    ∃ t : Fin 3 → Q, (∀ i, t i ∈ T i) ∧ (∀ i, ∀ s ∈ T i, Commute s (t i)) ∧
      z = t 0 * t 1 * t 2 := by
  have hsup : (⨆ i, T i) = T 0 ⊔ T 1 ⊔ T 2 := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup T 0) (le_iSup T 1)) (le_iSup T 2)
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hc01 : ∀ u ∈ T 0, ∀ v ∈ T 1, Commute u v := hcomm 0 1 (Ne.symm h10)
  have hc02 : ∀ u ∈ T 0, ∀ v ∈ T 2, Commute u v := hcomm 0 2 (Ne.symm h20)
  have hc12 : ∀ u ∈ T 1, ∀ v ∈ T 2, Commute u v := hcomm 1 2 (Ne.symm h21)
  rw [hsup] at hz
  have h01 : T 0 ⊔ T 1 ≤ Subgroup.normalizer (T 2 : Set Q) := by
    refine sup_le ?_ ?_
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [(hc02 g hg h hh).eq, mul_assoc, mul_inv_cancel, mul_one]
        exact hh
      · intro hh
        have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
        rw [← h1, (hc02 g⁻¹ ((T 0).inv_mem hg) _ hh).eq, inv_mul_cancel_right]
        exact hh
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [(hc12 g hg h hh).eq, mul_assoc, mul_inv_cancel, mul_one]
        exact hh
      · intro hh
        have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
        rw [← h1, (hc12 g⁻¹ ((T 1).inv_mem hg) _ hh).eq, inv_mul_cancel_right]
        exact hh
  have h0 : T 0 ≤ Subgroup.normalizer (T 1 : Set Q) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [(hc01 g hg h hh).eq, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    · intro hh
      have h1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rw [← h1, (hc01 g⁻¹ ((T 0).inv_mem hg) _ hh).eq, inv_mul_cancel_right]
      exact hh
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ h01] at hz
  obtain ⟨p, hp, c, hc, rfl⟩ := hz
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ h0] at hp
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  have ha' : a ∈ T 0 := ha
  have hb' : b ∈ T 1 := hb
  have hc' : c ∈ T 2 := hc
  refine ⟨![a, b, c], ?_, ?_, rfl⟩
  · intro i
    fin_cases i
    · exact ha'
    · exact hb'
    · exact hc'
  · intro i
    fin_cases i
    · intro s hs
      have h := (hzc 0 s hs).eq
      have hsb : s * b = b * s := (hc01 s hs b hb').eq
      have hsc : s * c = c * s := (hc02 s hs c hc').eq
      have : s * a * (b * c) = a * s * (b * c) := by
        calc s * a * (b * c) = s * (a * b * c) := by group
          _ = a * b * c * s := h
          _ = a * b * (c * s) := by group
          _ = a * b * (s * c) := by rw [hsc]
          _ = a * (b * s) * c := by group
          _ = a * (s * b) * c := by rw [hsb]
          _ = a * s * (b * c) := by group
      exact mul_right_cancel this
    · intro s hs
      have h := (hzc 1 s hs).eq
      have hsa : s * a = a * s := ((hc01 a ha' s hs).symm).eq
      have hsc : s * c = c * s := (hc12 s hs c hc').eq
      have : a * (s * b) * c = a * (b * s) * c := by
        calc a * (s * b) * c = (a * s) * b * c := by group
          _ = (s * a) * b * c := by rw [hsa]
          _ = s * (a * b * c) := by group
          _ = a * b * c * s := h
          _ = a * b * (c * s) := by group
          _ = a * b * (s * c) := by rw [hsc]
          _ = a * (b * s) * c := by group
      exact (mul_left_cancel (mul_right_cancel this))
    · intro s hs
      have h := (hzc 2 s hs).eq
      have hsa : s * a = a * s := ((hc02 a ha' s hs).symm).eq
      have hsb : s * b = b * s := ((hc12 b hb' s hs).symm).eq
      have : a * b * (s * c) = a * b * (c * s) := by
        calc a * b * (s * c) = a * (b * s) * c := by group
          _ = a * (s * b) * c := by rw [hsb]
          _ = (a * s) * b * c := by group
          _ = (s * a) * b * c := by rw [hsa]
          _ = s * (a * b * c) := by group
          _ = a * b * c * s := h
          _ = a * b * (c * s) := by group
      exact mul_left_cancel this

theorem conj_eq_self_of_card_dvd_three {X : Type*} [Group X] [Finite X] {Z : Subgroup X}
    (hZ : Nat.card Z ∣ 3) {b : X} (hb3 : b ^ 3 = 1) (hbZ : ∀ z ∈ Z, b * z * b⁻¹ ∈ Z) :
    ∀ z ∈ Z, b * z * b⁻¹ = z := by
  intro z hz
  by_cases hz1 : z = 1
  · subst hz1
    simp
  have hcard : Nat.card Z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h | h
    · exfalso
      have : Subsingleton Z := (Nat.card_eq_one_iff_unique.1 h).1
      exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : Z) 1))
    · exact h
  have hord : orderOf z = 3 := by
    have h1 : orderOf z ∣ 3 := by
      have := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
      rw [← Subgroup.orderOf_coe, hcard] at this
      exact this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hZeq : Subgroup.zpowers z = Z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz)
    rw [hcard, Nat.card_zpowers, hord]
  obtain ⟨k, hk⟩ :=
    Subgroup.mem_zpowers_iff.1 (hZeq ▸ hbZ z hz : b * z * b⁻¹ ∈ Subgroup.zpowers z)
  have hconj : ∀ m : ℤ, b * z ^ m * b⁻¹ = z ^ (k * m) := by
    intro m
    rw [← conj_zpow, ← hk, ← zpow_mul]
  have hb3' : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
  have h3 : z = z ^ (k * (k * k)) := by
    have e1 : b * (b * (b * z * b⁻¹) * b⁻¹) * b⁻¹ = (b * (b * b)) * z * (b * (b * b))⁻¹ := by
      group
    rw [hb3'] at e1
    simp only [one_mul, inv_one, mul_one] at e1
    calc z = b * (b * (b * z * b⁻¹) * b⁻¹) * b⁻¹ := e1.symm
      _ = b * (b * z ^ k * b⁻¹) * b⁻¹ := by rw [← hk]
      _ = b * z ^ (k * k) * b⁻¹ := by rw [hconj k]
      _ = z ^ (k * (k * k)) := by rw [hconj (k * k)]
  have h4 : ((3 : ℕ) : ℤ) ∣ k * (k * k) - 1 := by
    have h5 : z ^ (k * (k * k) - 1) = 1 := by
      rw [zpow_sub_one, ← h3, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.2 h5
    rwa [hord] at this
  have h6 : (k : ZMod 3) * ((k : ZMod 3) * k) - 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * (k * k) - 1) 3).2 h4
    simpa using this
  have h7 : (k : ZMod 3) = 1 := by
    revert h6
    generalize (k : ZMod 3) = a
    revert a
    decide
  have h8 : ((3 : ℕ) : ℤ) ∣ k - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).1
    push_cast
    rw [h7]
    ring
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hord] at this
  obtain ⟨m, hm⟩ := h8
  have hk' : k = 1 + 3 * m := by
    push_cast at hm
    omega
  rw [← hk, hk', zpow_add, zpow_one, zpow_mul]
  simp [hz3]

theorem pow_three_eq_one_of_card_dvd_three {X : Type*} [Group X] {Z : Subgroup X}
    (hZ : Nat.card Z ∣ 3) {u : X} (hu : u ∈ Z) : u ^ 3 = 1 := by
  obtain ⟨m, hm⟩ := hZ
  have h1 : (⟨u, hu⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
  have h2 : (⟨u, hu⟩ : Z) ^ 3 = 1 := by
    have : (⟨u, hu⟩ : Z) ^ 3 = ((⟨u, hu⟩ : Z) ^ Nat.card Z) ^ m := by rw [← pow_mul, ← hm]
    rw [this, h1, one_pow]
  exact congrArg Subtype.val h2

end Algebra

section Normalizes

theorem le_normalizer_inf_centralizer_of_fixed {X : Type} [Group X] {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) {w : X} (hwK : w ∈ K)
    (hfix : ∀ (b : X) (hb : b ∈ B), actHom K ⟨b, hBN hb⟩ (QuotientGroup.mk ⟨w, hwK⟩) =
      QuotientGroup.mk ⟨w, hwK⟩) :
    B ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({w} : Set X) : Subgroup X) : Set X) := by
  have key : ∀ b ∈ B, ∀ d ∈ K ⊓ Subgroup.centralizer ({w} : Set X),
      b * d * b⁻¹ ∈ K ⊓ Subgroup.centralizer ({w} : Set X) := by
    intro b hb d hd
    obtain ⟨hdK, hdC⟩ := Subgroup.mem_inf.1 hd
    have hdw : d * w = w * d := Subgroup.mem_centralizer_singleton_iff.1 hdC
    have hb' : b⁻¹ ∈ B := B.inv_mem hb
    have hc : w * b⁻¹ * w⁻¹ * b ∈ centreOf K := by
      simpa using comm_mem_centreOf_of_fixed K (hBN hb') ⟨w, hwK⟩ (hfix b⁻¹ hb')
    obtain ⟨c, hcdef⟩ : ∃ c : X, c = w * b⁻¹ * w⁻¹ * b := ⟨_, rfl⟩
    rw [← hcdef] at hc
    have hcC : c ∈ Subgroup.centralizer (K : Set X) := mem_centralizer_of_mem_centreOf hc
    have hcd : d * c = c * d := Subgroup.mem_centralizer_iff.1 hcC d hdK
    have hcd' : c⁻¹ * d = d * c⁻¹ := by
      calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * d) * c⁻¹ := by rw [hcd]
        _ = d * c⁻¹ := by group
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hBN hb) d).1 hdK, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbw : b⁻¹ * w * b = c⁻¹ * w := by rw [hcdef]; group
    calc b * d * b⁻¹ * w = b * d * (b⁻¹ * w * b) * b⁻¹ := by group
      _ = b * d * (c⁻¹ * w) * b⁻¹ := by rw [hbw]
      _ = b * (d * c⁻¹) * w * b⁻¹ := by group
      _ = b * (c⁻¹ * d) * w * b⁻¹ := by rw [hcd']
      _ = b * c⁻¹ * (d * w) * b⁻¹ := by group
      _ = b * c⁻¹ * (w * d) * b⁻¹ := by rw [hdw]
      _ = b * (c⁻¹ * w) * d * b⁻¹ := by group
      _ = b * (b⁻¹ * w * b) * d * b⁻¹ := by rw [hbw]
      _ = w * (b * d * b⁻¹) := by group
  intro b hb
  refine Subgroup.mem_normalizer_iff.2 fun d => ⟨fun hd => key b hb d hd, fun hd => ?_⟩
  have h := key b⁻¹ (B.inv_mem hb) _ hd
  have e : b⁻¹ * (b * d * b⁻¹) * b⁻¹⁻¹ = d := by group
  rwa [e] at h


theorem normalized_of_component_of_fixed {X : Type} [Group X] [Finite X]
    (hKG : CFSG.Open.IsKGroup X) {K B J : Subgroup X} (hBSC : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hrank : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) {w : X} (hwK : w ∈ K)
    (hfix : ∀ (b : X) (hb : b ∈ B), actHom K ⟨b, hBN hb⟩ (QuotientGroup.mk ⟨w, hwK⟩) =
      QuotientGroup.mk ⟨w, hwK⟩)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({w} : Set X)) J)
    (hJL : IsLieQuot ↥J IsU3EightIndex) : B ≤ Subgroup.normalizer (J : Set X) := by
  have hBD := le_normalizer_inf_centralizer_of_fixed hBN hwK hfix
  set D : Subgroup X := K ⊓ Subgroup.centralizer ({w} : Set X) with hD
  set W : Subgroup X := Subgroup.normalizer (D : Set X) with hW
  have hJW : GLAPComponent 3 W J :=
    Lemma510Ns.glaPComponent_of_normal_sub Nat.prime_three Subgroup.le_normalizer
      Subgroup.normal_in_normalizer hJ
  have hJWle : J ≤ W := hJW.1
  have hSC' : IsSCp 3 ⊤ (B.subgroupOf W) := Bal209F4Aux.isSCp_subgroupOf hBD hBSC
  have hJtop : GLAPComponent 3 ⊤ (J.subgroupOf W) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_top_subgroupOf Nat.prime_three hJW
  have hLie : IsLieQuot ↥(J.subgroupOf W) IsU3EightIndex :=
    isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJWle).symm hJL
  have hrank' : GLATwoLocalRank 3 ↥W ≤ CFSG.Open.pRank 3 (B.subgroupOf W) := by
    have h1 := glaTwoLocalRank_subgroup_le Nat.prime_three W
    have h2 := pRank_map_eq_of_injective (by norm_num : 1 < 3) W.subtype W.subtype_injective
      (B.subgroupOf W)
    rw [Subgroup.map_subgroupOf_eq_of_le hBD] at h2
    exact h1.trans (hrank.trans h2.le)
  have hmain := normalized_of_u3_component (hKG.subgroup W) hSC'.2.1 hrank' hJtop hLie
  exact (CFSG.LocalAnalysis.GLTheoremA.le_normalizer_subgroupOf_iff hJWle hBD).1 hmain

end Normalizes

section Lifting

theorem actHom_eq_conj_mk {X : Type} [Group X] {K : Subgroup X} (k : ↥K)
    (hk : (k : X) ∈ Subgroup.normalizer (K : Set X)) :
    actHom K ⟨(k : X), hk⟩ = MulAut.conj (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [actHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

theorem fixSubgroup_conj_eq_centralizer {Q : Type*} [Group Q] (z : Q) :
    fixSubgroup (MulAut.conj z) = Subgroup.centralizer ({z} : Set Q) := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem isLieQuot_of_centralQuotient_equiv {Y Y' : Type*} [Group Y] [Group Y']
    (e : (Y ⧸ Subgroup.center Y) ≃* (Y' ⧸ Subgroup.center Y'))
    {P : TauCeti.LieTypeIndex → Prop} (h : IsLieQuot Y' P) : IsLieQuot Y P := by
  obtain ⟨d, hd, ⟨φ⟩⟩ := h
  exact ⟨d, hd, ⟨e.trans φ⟩⟩

section Multiplier

open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag


theorem card_center_dvd_three_of_u3 {J : Type} [Group J] [Finite J]
    (hq : CFSG.Open.IsQuasisimple J) (hL : IsLieQuot J IsU3EightIndex) :
    Nat.card (Subgroup.center J) ∣ 3 := by
  obtain ⟨F, _, h, ⟨e⟩⟩ := u3_model hL
  by_cases hZ : Subgroup.center J = ⊥
  · rw [hZ, Subgroup.card_bot]
    exact one_dvd 3
  · obtain ⟨ψ, -⟩ := KSU3Core.exists_mulEquiv_unitarySU_three_compat h (by norm_num) hq.1 e hZ
    have h1 := Subgroup.map_center_eq ψ
    have h2 : Nat.card (Subgroup.center J) = Nat.card (Subgroup.center (unitarySU 2 3 F 3)) := by
      rw [← h1]
      exact Subgroup.card_map_of_injective ψ.injective
    rw [h2, center_unitarySU_three (h := h) (by norm_num),
      card_unitaryScalars (n := 3) h (by norm_num)]
    norm_num

end Multiplier

theorem card_inf_centralizer_eq_card_center {K : Type*} [Group K] (A : Subgroup K) :
    Nat.card ↥(A ⊓ Subgroup.centralizer (A : Set K)) = Nat.card (Subgroup.center ↥A) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩
      invFun := fun z => ⟨z.1.1, Subgroup.mem_inf.2 ⟨z.1.2, ?_⟩⟩
      left_inv := fun x => rfl
      right_inv := fun z => rfl }
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2 g.1 g.2)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩
    exact congrArg Subtype.val this

theorem commute_of_map_commute_image {G Q : Type*} [Group G] [Group Q] [Finite G] {J₁ : Subgroup G}
    (hperf : ⁅J₁, J₁⁆ = J₁) (π : G →* Q) (hker : π.ker ≤ Subgroup.center G) {u : G}
    (hu : u ∈ J₁) (hc : ∀ s ∈ J₁.map π, Commute s (π u)) : ∀ l ∈ J₁, Commute l u := by
  have hperf' : commutator ↥J₁ = ⊤ := (Subgroup.isPerfect_iff.2 hperf).commutator_eq_top
  have h := LieComp.comap_center_of_surjective hperf' (π.subgroupMap J₁)
    (MonoidHom.subgroupMap_surjective π J₁) (ker_subgroupMap_le_center π hker J₁)
  have hmem : (⟨u, hu⟩ : ↥J₁) ∈ Subgroup.center ↥J₁ := by
    rw [← h, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hc s s.2).eq
  intro l hl
  have := Subgroup.mem_center_iff.1 hmem ⟨l, hl⟩
  exact congrArg Subtype.val this

theorem commute_of_map_commute {G Q : Type*} [Group G] [Group Q] {A B : Subgroup G}
    (hA : ⁅A, A⁆ = A) (π : G →* Q) (hker : π.ker ≤ Subgroup.center G)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, Commute (π a) (π b)) : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
  have hle : ⁅A, B⁆ ≤ Subgroup.center G := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    apply hker
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hAB a ha b hb).eq
  have h0 := commutator_eq_bot_of_perfect hA hle
  intro a ha b hb
  have : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := h0 ▸ Subgroup.commutator_mem_commutator ha hb
  exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 this)

theorem exists_comp_over {X : Type} [Group X] [Finite X] {K : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (K : Set X)) {T : Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hT : GLAPComponent 3 (fixSubgroup (actHom K ⟨a, ha⟩)) T)
    (hTq : CFSG.Open.IsQuasisimple ↥T) :
    ∃ J₁ : Subgroup ↥K, J₁.map (QuotientGroup.mk' (Subgroup.center ↥K)) = T ∧ ⁅J₁, J₁⁆ = J₁ ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) (J₁.map K.subtype) ∧
      CFSG.Open.IsQuasisimple ↥(J₁.map K.subtype) ∧
      Nonempty ((↥(J₁.map K.subtype) ⧸ Subgroup.center ↥(J₁.map K.subtype)) ≃*
        (↥T ⧸ Subgroup.center ↥T)) := by
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  have hαβ : ∀ k : ↥K, π (K.normalizerMonoidHom ⟨a, ha⟩ k) =
      actHom K ⟨a, ha⟩ (π k) := fun k => (actHom_mk K ⟨a, ha⟩ k).symm
  obtain ⟨J₁, hJ₁, hJ₁map⟩ :=
    exists_glaPComponent_map_fixSubgroup π hker (K.normalizerMonoidHom ⟨a, ha⟩)
      (actHom K ⟨a, ha⟩) hαβ hπ Nat.prime_three hT
  have hC : fixSubgroup (K.normalizerMonoidHom ⟨a, ha⟩) =
      (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K :=
    fixSubgroup_normalizerMonoidHom ha
  have hJ₁' : GLAPComponent 3 ((K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K) J₁ := by
    rw [← hC]
    exact hJ₁
  have hJ₀ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) (J₁.map K.subtype) := by
    have hc : ∀ y ∈ ((K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K) ⊓ K.subtype.ker,
        ∀ x ∈ (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K, x * y = y * x := by
      intro y hy x _
      have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
      rw [this, mul_one, one_mul]
    have h := glaPComponent_map_central Nat.prime_three K.subtype hc hJ₁'
    rwa [Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K)] at h
  obtain ⟨hq, hiso⟩ := liftComp_quasisimple_iso ha hJ₁ hJ₁map hTq
  exact ⟨J₁, hJ₁map, glaPComponent_perfect hJ₁, hJ₀, hq, hiso⟩

end Lifting

section FixedLift


theorem exists_fixed_lift {X : Type} [Group X] [Finite X] (hKG : CFSG.Open.IsKGroup X)
    {K B : Subgroup X} (hBSC : IsSCp 3 ⊤ B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hrank : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) {z : ↥K ⧸ Subgroup.center ↥K}
    (hzfix : ∀ φ ∈ autImage B K, φ z = z) {T : Fin 3 → Subgroup (↥K ⧸ Subgroup.center ↥K)}
    (hTc : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
      GLAPComponent 3 (Subgroup.centralizer ({z} : Set (↥K ⧸ Subgroup.center ↥K))) L ↔
        ∃ i, L = T i)
    (hTq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i) ∧ IsLieQuot ↥(T i) IsU3EightIndex)
    (hTcomm : ∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, Commute u v) (hzT : z ∈ ⨆ i, T i) :
    ∃ y : ↥K, (y : X) ∈ B ∧ (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = z := by
  classical
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have hker : (QuotientGroup.mk' (Subgroup.center ↥K)).ker ≤ Subgroup.center ↥K := by
    rw [QuotientGroup.ker_mk']
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective z
  have hwK : (k₀ : X) ∈ K := k₀.2
  have hwN : (k₀ : X) ∈ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer hwK
  have hact : actHom K ⟨(k₀ : X), hwN⟩ = MulAut.conj z := by
    rw [← hk₀]
    exact actHom_eq_conj_mk k₀ hwN
  have hfixw : ∀ (b : X) (hb : b ∈ B), actHom K ⟨b, hBN hb⟩ (QuotientGroup.mk ⟨(k₀ : X), hwK⟩) =
      QuotientGroup.mk ⟨(k₀ : X), hwK⟩ := by
    intro b hb
    have h1 : (QuotientGroup.mk ⟨(k₀ : X), hwK⟩ : ↥K ⧸ Subgroup.center ↥K) = z := hk₀
    rw [h1]
    exact hzfix _ (mem_autImage.2 ⟨b, hBN hb, hb, rfl⟩)
  have hTc' : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
      GLAPComponent 3 (fixSubgroup (actHom K ⟨(k₀ : X), hwN⟩)) L ↔ ∃ i, L = T i := by
    intro L
    rw [hact, fixSubgroup_conj_eq_centralizer]
    exact hTc L
  choose J₁ hmapJ hperfJ hJcomp hJq hJiso using fun i =>
    exists_comp_over hwN ((hTc' (T i)).2 ⟨i, rfl⟩) (hTq i).1
  have hLie : ∀ i, IsLieQuot ↥((J₁ i).map K.subtype) IsU3EightIndex := fun i =>
    isLieQuot_of_centralQuotient_equiv (hJiso i).some (hTq i).2
  have hBJ : ∀ i, B ≤ Subgroup.normalizer (((J₁ i).map K.subtype : Subgroup X) : Set X) :=
    fun i => normalized_of_component_of_fixed hKG hBSC hBN hrank hwK hfixw (hJcomp i) (hLie i)
  have hzc : ∀ i, ∀ s ∈ T i, Commute s z := fun i s hs =>
    Subgroup.mem_centralizer_singleton_iff.1 (((hTc (T i)).2 ⟨i, rfl⟩).1 hs)
  obtain ⟨t, htT, htc, hzt⟩ := exists_mul_of_mem_iSup_three hTcomm hzT hzc
  have hmem : ∀ i, t i ∈ (J₁ i).map (QuotientGroup.mk' (Subgroup.center ↥K)) := fun i => by
    rw [hmapJ i]
    exact htT i
  choose u hu huπ using fun i => Subgroup.mem_map.1 (hmem i)
  have hucent : ∀ i, ∀ l ∈ J₁ i, Commute l (u i) := fun i =>
    commute_of_map_commute_image (hperfJ i) (QuotientGroup.mk' (Subgroup.center ↥K)) hker (hu i)
      (fun s hs => by
        rw [hmapJ i] at hs
        rw [huπ i]
        exact htc i s hs)
  have hucomm : ∀ i j, i ≠ j → Commute (u i) (u j) := fun i j hij =>
    commute_of_map_commute (hperfJ i) (QuotientGroup.mk' (Subgroup.center ↥K)) hker
      (fun a ha b hb => by
        have ha' : QuotientGroup.mk' (Subgroup.center ↥K) a ∈ T i := by
          rw [← hmapJ i]
          exact Subgroup.mem_map_of_mem _ ha
        have hb' : QuotientGroup.mk' (Subgroup.center ↥K) b ∈ T j := by
          rw [← hmapJ j]
          exact Subgroup.mem_map_of_mem _ hb
        exact hTcomm i j hij _ ha' _ hb') (u i) (hu i) (u j) (hu j)
  have hmemZ : ∀ i, ((u i : ↥K) : X) ∈ ((J₁ i).map K.subtype) ⊓
      Subgroup.centralizer ((((J₁ i).map K.subtype : Subgroup X)) : Set X) := by
    intro i
    refine ⟨⟨u i, hu i, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    exact congrArg Subtype.val (hucent i l hl)
  have hZ : ∀ i, Nat.card ↥(((J₁ i).map K.subtype) ⊓
      Subgroup.centralizer ((((J₁ i).map K.subtype : Subgroup X)) : Set X)) ∣ 3 := fun i => by
    rw [card_inf_centralizer_eq_card_center]
    exact card_center_dvd_three_of_u3 (hJq i) (hLie i)
  have hfixu : ∀ i, ∀ b ∈ B, b * ((u i : ↥K) : X) * b⁻¹ = ((u i : ↥K) : X) := by
    intro i b hb
    refine conj_eq_self_of_card_dvd_three (hZ i) (hBel.2 b hb) ?_ _ (hmemZ i)
    intro z' hz'
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hBJ i hb) z').1 hz'.1,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    intro s hs
    have hs' : b⁻¹ * s * b ∈ ((J₁ i).map K.subtype : Subgroup X) := by
      have := (Subgroup.mem_normalizer_iff.1 (hBJ i (B.inv_mem hb)) s).1 hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hz'.2 _ hs'
    calc s * (b * z' * b⁻¹) = b * ((b⁻¹ * s * b) * z') * b⁻¹ := by group
      _ = b * (z' * (b⁻¹ * s * b)) * b⁻¹ := by rw [h1]
      _ = b * z' * b⁻¹ * s := by group
  have hu3 : ∀ i, ((u i : ↥K) : X) ^ 3 = 1 := fun i =>
    pow_three_eq_one_of_card_dvd_three (hZ i) (hmemZ i)
  have hcu : ∀ i j, i ≠ j → Commute ((u i : ↥K) : X) ((u j : ↥K) : X) := fun i j hij =>
    congrArg Subtype.val (hucomm i j hij).eq
  have hyc : ((u 0 * u 1 * u 2 : ↥K) : X) = (u 0 : X) * (u 1 : X) * (u 2 : X) := rfl
  have hy3 : ((u 0 * u 1 * u 2 : ↥K) : X) ^ 3 = 1 := by
    rw [hyc]
    have c02 := hcu 0 2 (by decide)
    have c12 := hcu 1 2 (by decide)
    have c01 := hcu 0 1 (by decide)
    rw [(c02.mul_left c12).mul_pow, c01.mul_pow, hu3 0, hu3 1, hu3 2]
    simp
  have hyfix : ∀ b ∈ B, b * ((u 0 * u 1 * u 2 : ↥K) : X) * b⁻¹ = ((u 0 * u 1 * u 2 : ↥K) : X) := by
    intro b hb
    rw [hyc]
    calc b * ((u 0 : X) * (u 1 : X) * (u 2 : X)) * b⁻¹
        = (b * (u 0 : X) * b⁻¹) * (b * (u 1 : X) * b⁻¹) * (b * (u 2 : X) * b⁻¹) := by group
      _ = (u 0 : X) * (u 1 : X) * (u 2 : X) := by
        rw [hfixu 0 b hb, hfixu 1 b hb, hfixu 2 b hb]
  refine ⟨u 0 * u 1 * u 2, ?_, ?_⟩
  · have hcomm : ∀ a ∈ B, ∀ c ∈ Subgroup.zpowers ((u 0 * u 1 * u 2 : ↥K) : X), a * c = c * a := by
      intro a ha c hc
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      have hay : Commute a ((u 0 * u 1 * u 2 : ↥K) : X) := by
        have h1 := hyfix a ha
        show a * _ = _ * a
        calc a * ((u 0 * u 1 * u 2 : ↥K) : X) = (a * ((u 0 * u 1 * u 2 : ↥K) : X) * a⁻¹) * a := by
              group
          _ = ((u 0 * u 1 * u 2 : ↥K) : X) * a := by rw [h1]
      exact (hay.zpow_right n).eq
    have hE : CFSG.Open.IsElemAbelian 3 (B ⊔ Subgroup.zpowers ((u 0 * u 1 * u 2 : ↥K) : X)) :=
      CFSG.Open.IsElemAbelian.sup_of_commute hBel (CFSG.Open.isElemAbelian_zpowers hy3) hcomm
    have hBeq := hBSC.2.2 _ le_top hE le_sup_left
    exact (le_sup_right.trans hBeq.le) (Subgroup.mem_zpowers _)
  · have e : ∀ i, (QuotientGroup.mk (u i) : ↥K ⧸ Subgroup.center ↥K) = t i := fun i => huπ i
    rw [hzt, QuotientGroup.mk_mul, QuotientGroup.mk_mul, e 0, e 1, e 2]

end FixedLift

section Selection

set_option linter.unusedSectionVars false


theorem e6_exists_threeCentral_good (h209U3 : Bal209FourUAt IsU3EightIndex (FieldAutU 3))
    {X : Type} [Group X] [Finite X]
    (hKG : CFSG.Open.IsKGroup X) {K B : Subgroup X} {x : X}
    (hK : CFSG.Open.IsComponentOf K ⊤) (hBSC : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hrank : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) (hLie : IsLieQuot ↥K IsTwE6EightIndex)
    (hxB : x ∈ B) (hxI : ¬ InnerAt K x)
    (hFx : FieldAutTwE6 (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨x, hBN hxB⟩)) :
    ∃ (y : X) (hyB : y ∈ B), InnerAt K y ∧ y ∉ Subgroup.centralizer (K : Set X) ∧
      GoodAt K B y ∧ ∃ z : ↥K ⧸ Subgroup.center ↥K,
        actHom K ⟨y, hBN hyB⟩ = MulAut.conj z ∧ IsThreeCentral (↥K ⧸ Subgroup.center ↥K) z := by
  classical
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hA : IsPGroup 3 ↥(autImage B K) := by
    intro g
    obtain ⟨b, hbN, hbB, hg⟩ := mem_autImage.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    have hb3 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (hBel.2 b hbB)
    calc ((g ^ 3 ^ 1 : ↥(autImage B K)) : MulAut (↥K ⧸ Subgroup.center ↥K))
        = (g : MulAut (↥K ⧸ Subgroup.center ↥K)) ^ 3 := by simp
      _ = actHom K (⟨b, hbN⟩ ^ 3) := by rw [← hg, map_pow]
      _ = 1 := by rw [hb3, map_one]
  have h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [E6LocalAux.card_eq_ordTwistedE6 hLie]
    norm_num [ordTwistedE6]
  obtain ⟨z, hz, hzfix⟩ := exists_fixed_threeCentral (autImage B K) hA h3
  obtain ⟨T, hTinj, hTc, hTq, hTcomm, hzT⟩ := e6_threeCentral_shape hLie hz
  obtain ⟨y, hyB, hyz⟩ := exists_fixed_lift hKG hBSC hBN hrank hzfix hTc hTq hTcomm hzT
  have hyact : actHom K ⟨(y : X), hBN hyB⟩ = MulAut.conj z := by
    rw [← hyz]
    exact actHom_eq_conj_mk y _
  have hyI : InnerAt K (y : X) := innerAt_iff.2 ⟨y, y.2, 1, Subgroup.one_mem _, by simp⟩
  refine ⟨(y : X), hyB, hyI, ?_, ?_, z, hyact, hz⟩
  · intro hyC
    have hyZ : y ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyC g g.2)
    have hz1 : z = 1 := by
      rw [← hyz]
      exact (QuotientGroup.eq_one_iff y).2 hyZ
    have h31 := hz.1
    rw [hz1, orderOf_one] at h31
    exact absurd h31 (by norm_num)
  · intro J hJ
    have hTc2 : ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
        GLAPComponent 3 (CFSG.RankThree.PartOne.CTP.fixedSubgroup
          (actHom K ⟨(y : X), hBN hyB⟩)) L ↔ ∃ i, L = T i := by
      intro L
      rw [hyact, fixedSubgroup_eq_fixSubgroup, fixSubgroup_conj_eq_centralizer]
      exact hTc L
    obtain ⟨J', -, hJ'c, hJ'q⟩ :=
      threeComponents_lift hq (hBN hyB) hTinj hTc2 (fun i => (hTq i).1)
    obtain ⟨i, rfl⟩ := (hJ'c J).1 hJ
    have hJL : IsLieQuot ↥(J' i) IsU3EightIndex :=
      isLieQuot_of_centralQuotient_equiv (hJ'q i).2.some (hTq i).2
    have hfixy : ∀ (b : X) (hb : b ∈ B), actHom K ⟨b, hBN hb⟩ (QuotientGroup.mk ⟨(y : X), y.2⟩) =
        QuotientGroup.mk ⟨(y : X), y.2⟩ := by
      intro b hb
      have h1 : (QuotientGroup.mk ⟨(y : X), y.2⟩ : ↥K ⧸ Subgroup.center ↥K) = z := hyz
      rw [h1]
      exact hzfix _ (mem_autImage.2 ⟨b, hBN hb, hb, rfl⟩)
    have hBJ : B ≤ Subgroup.normalizer ((J' i : Subgroup X) : Set X) :=
      normalized_of_component_of_fixed hKG hBSC hBN hrank y.2 hfixy hJ hJL
    refine ⟨hBJ, ?_⟩
    have hF := e6_fieldAut_on_u3_component hK hBel hBN hLie hxB hyB hFx hyact hz hJ hJL hBJ
    exact sLOB_of_u3_component h209U3 hKG hK hBSC hrank hyB hJ (hJ'q i).1 hJL hBJ hF

end Selection

section SelLoc

set_option linter.unusedSectionVars false


theorem e6SelLoc (h209U3 : Bal209FourUAt IsU3EightIndex (FieldAutU 3)) :
    FourUSelLoc IsTwE6EightIndex FieldAutTwE6 := by
  have h1 : E6ThreeCentralCore := fun Q _ _ hQ z hz => e6_threeCentral_core hQ hz
  intro X _ _ hKG K B x hK hBSC hBN hrank hLie hxB hxI _ hFall
  obtain ⟨y, hyB, hyI, hyC, hyG, z, hyz, hz⟩ :=
    e6_exists_threeCentral_good h209U3 hKG hK hBSC hBN hrank hLie hxB hxI (hFall x hxB hxI)
  have hBel : CFSG.Open.IsElemAbelian 3 B := hBSC.2.1
  have hxy : Commute x y := commute_of_elemAbelian hBel hxB hyB
  refine ⟨y, hyB, hyI, hyC, hyG, ?_⟩
  have hsub : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hyB)
  exact e6_localBalance_at_threeCentral_of_core h1 hK hLie (hBN hxB) (hBN hyB) hxy
    (hBel.2 x hxB) (hBel.2 y hyB) hyz hz (fun h => absurd h hxI)
    (fun a ha haN hna => hFall a (hsub ha) hna)

end SelLoc

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
