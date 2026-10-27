module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgD4Graph
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz10
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28Parabolic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped Pointwise

theorem centerQuotientHom_mem_innAutDerived_of_inv_d4b {S : Type} [Group S] {K : Subgroup S}
    {x σ : MulAut S} (hx : x ∈ CFSG.GroupActions.subgroupStabAut K)
    (hσ : σ ∈ CFSG.GroupActions.subgroupStabAut K) (hx3 : x ^ 3 = 1)
    (hinv : σ * x * σ⁻¹ = x⁻¹) :
    centerQuotientHom ↥K (CFSG.GroupActions.subgroupStabRestrict K ⟨x, hx⟩) ∈
      innAutDerived (↥K ⧸ Subgroup.center ↥K) := by
  set ρ := (centerQuotientHom ↥K).comp (CFSG.GroupActions.subgroupStabRestrict K) with hρ
  have hα3 : ρ ⟨x, hx⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hx⟩ : CFSG.GroupActions.subgroupStabAut K) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [h1, map_one]
  have hconj : ρ ⟨σ, hσ⟩ * ρ ⟨x, hx⟩ * (ρ ⟨σ, hσ⟩)⁻¹ * ρ ⟨x, hx⟩ = 1 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    have h1 : (⟨σ, hσ⟩ : CFSG.GroupActions.subgroupStabAut K) * ⟨x, hx⟩ * (⟨σ, hσ⟩)⁻¹ *
        ⟨x, hx⟩ = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hinv, inv_mul_cancel]
    rw [h1, map_one]
  have hinn : CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (ρ ⟨σ, hσ⟩ * ρ ⟨x, hx⟩ * (ρ ⟨σ, hσ⟩)⁻¹ * ρ ⟨x, hx⟩) := by
    rw [hconj]
    exact ⟨1, map_one _⟩
  exact mem_innAutDerived_of_inner_inv_of_odd (p := 3) (by decide) hα3 hinn

theorem fixSubgroup_map_of_conj_d4b {S : Type} [Group S] (σ β : MulAut S) :
    (fixSubgroup β).map σ.toMonoidHom = fixSubgroup (σ * β * σ⁻¹) := by
  ext y
  rw [Subgroup.mem_map, mem_fixSubgroup]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_fixSubgroup] at hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, hz]
  · intro hy
    refine ⟨σ⁻¹ y, ?_, by simp⟩
    rw [mem_fixSubgroup]
    have h : σ (β (σ.symm y)) = y := by simpa [MulAut.mul_apply] using hy
    rw [MulAut.inv_apply]
    exact σ.eq_symm_apply.mpr h

theorem fixSubgroup_inv_d4b {S : Type} [Group S] (β : MulAut S) :
    fixSubgroup β⁻¹ = fixSubgroup β := by
  ext y
  rw [mem_fixSubgroup, mem_fixSubgroup, MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]

theorem isComponentOf_map_of_inv_d4b {S : Type} [Group S] {σ β : MulAut S}
    (hσβ : σ * β * σ⁻¹ = β ∨ σ * β * σ⁻¹ = β⁻¹) {K : Subgroup S}
    (hK : IsComponentOf K (fixSubgroup β)) :
    IsComponentOf (K.map σ.toMonoidHom) (fixSubgroup β) := by
  have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map σ hK
  have h2 : (fixSubgroup β).map (σ : S →* S) = fixSubgroup β := by
    have h3 := fixSubgroup_map_of_conj_d4b σ β
    rcases hσβ with h | h
    · rw [h] at h3
      exact h3
    · rw [h, fixSubgroup_inv_d4b] at h3
      exact h3
  rw [h2] at h1
  exact h1

theorem eq_of_isComponentOf_of_nineteen_d4b {S : Type} [Group S] [Finite S] {H K K' : Subgroup S}
    (hK : IsComponentOf K H) (hK' : IsComponentOf K' H)
    (h19 : 19 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (h19' : 19 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K'))
    (hS : ¬ 19 ^ 2 ∣ Nat.card S) : K = K' := by
  by_contra hne
  have hcomm : ∀ a ∈ K, ∀ c ∈ K', a * c = c * a := fun a ha c hc =>
    CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hK' hne ha hc
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K K' hcomm
  have hKcard : Nat.card K =
      Nat.card (Subgroup.center K) * Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), mul_comm]
  have hK'card : Nat.card K' =
      Nat.card (Subgroup.center K') * Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K'), mul_comm]
  have h19K : 19 ∣ Nat.card K := hKcard ▸ dvd_mul_of_dvd_right h19 _
  have h19K' : 19 ∣ Nat.card K' := hK'card ▸ dvd_mul_of_dvd_right h19' _
  have hZ : ¬ 19 ∣ Nat.card (Subgroup.center K) := by
    intro h
    apply hS
    have h2 : 19 ^ 2 ∣ Nat.card K := by
      rw [hKcard, pow_two]
      exact Nat.mul_dvd_mul h h19
    exact h2.trans (Subgroup.card_subgroup_dvd_card K)
  have hinf : ¬ 19 ∣ Nat.card (K ⊓ K' : Subgroup S) := by
    intro h
    apply hZ
    have hle : (K ⊓ K').subgroupOf K ≤ Subgroup.center K := by
      intro a ha
      rw [Subgroup.mem_center_iff]
      intro g
      have haK' : (a : S) ∈ K' := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2
      exact Subtype.ext (hcomm g g.2 a haK')
    have hcard : Nat.card ((K ⊓ K').subgroupOf K) = Nat.card (K ⊓ K' : Subgroup S) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    exact (hcard ▸ h).trans (Subgroup.card_dvd_of_le hle)
  have h361 : 19 ^ 2 ∣ Nat.card (K ⊔ K' : Subgroup S) * Nat.card (K ⊓ K' : Subgroup S) := by
    rw [hprod, pow_two]
    exact Nat.mul_dvd_mul h19K h19K'
  have hcop : Nat.Coprime (19 ^ 2) (Nat.card (K ⊓ K' : Subgroup S)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hinf)
  exact hS ((hcop.dvd_of_dvd_mul_right h361).trans (Subgroup.card_subgroup_dvd_card _))

theorem exists_fixed_orderOf_three_d4b {S : Type} [Group S] [Finite S] {K : Subgroup S}
    {x : MulAut S} (hxK : x ∈ CFSG.GroupActions.subgroupStabAut K) (hx3 : x ^ 3 = 1)
    (h3K : 3 ∣ Nat.card K) : ∃ y ∈ K, orderOf y = 3 ∧ x y = y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set α : MulAut K := CFSG.GroupActions.subgroupStabRestrict K ⟨x, hxK⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have h1 : (⟨x, hxK⟩ : CFSG.GroupActions.subgroupStabAut K) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [h1, map_one]
  have hmod := CFSG.HardMathSupport.Lang.Proving.card_modEq_card_fixedPoints_of_pow_prime α hα3
  set F : Subgroup K := α.toMonoidHom.eqLocus (MonoidHom.id K) with hF
  have hFcard : Nat.card {k : K // α k = k} = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight fun k => Iff.rfl)
  rw [hFcard] at hmod
  have h3F : 3 ∣ Nat.card F := (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans
    (Nat.modEq_zero_iff_dvd.mpr h3K)))
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' 3 h3F
  refine ⟨((f : K) : S), (f : K).2, ?_, ?_⟩
  · rw [← hf, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  · have h := f.2
    change α (f : K) = (f : K) at h
    have h2 := congrArg (fun k : K => (k : S)) h
    simpa [hα, CFSG.GroupActions.subgroupStabRestrict_apply] using h2

theorem exists_elemAbelian_twentySeven_d4b {S : Type} [Group S] [Finite S] {b : S}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {x : MulAut S} (hx3 : x ^ 3 = 1) (hxb : x b = b)
    {K K' : Subgroup S} (hK : IsComponentOf K (fixSubgroup (MulAut.conj b)))
    (hK' : IsComponentOf K' (fixSubgroup (MulAut.conj b))) (hne : K ≠ K')
    (hxK : x ∈ CFSG.GroupActions.subgroupStabAut K)
    (hxK' : x ∈ CFSG.GroupActions.subgroupStabAut K')
    (hZK : Subgroup.center K = ⊥) (hZK' : Subgroup.center K' = ⊥)
    (h3K : 3 ∣ Nat.card K) (h3K' : 3 ∣ Nat.card K') :
    ∃ A : Subgroup S, IsElemAbelian 3 A ∧ (∀ a ∈ A, x a = a) ∧ ¬ Nat.card A ≤ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hyK, hy3, hxy⟩ := exists_fixed_orderOf_three_d4b hxK hx3 h3K
  obtain ⟨y', hy'K, hy'3, hxy'⟩ := exists_fixed_orderOf_three_d4b hxK' hx3 h3K'
  have hbc : ∀ g ∈ fixSubgroup (MulAut.conj b), b * g = g * b := by
    intro g hg
    rw [mem_fixSubgroup, MulAut.conj_apply] at hg
    calc b * g = b * g * b⁻¹ * b := by group
      _ = g * b := by rw [hg]
  have hcommKK' : ∀ a ∈ K, ∀ c ∈ K', a * c = c * a := fun a ha c hc =>
    CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hK' hne ha hc
  have hcenK : ∀ a ∈ K, (∀ g ∈ K, a * g = g * a) → a = 1 := by
    intro a ha hag
    have hmem : (⟨a, ha⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hag g g.2).symm
    rw [hZK, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hcenK' : ∀ a ∈ K', (∀ g ∈ K', a * g = g * a) → a = 1 := by
    intro a ha hag
    have hmem : (⟨a, ha⟩ : K') ∈ Subgroup.center K' := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hag g g.2).symm
    rw [hZK', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  set Zb := Subgroup.zpowers b with hZb
  set Zy := Subgroup.zpowers y with hZy
  set Zy' := Subgroup.zpowers y' with hZy'
  have hZyK : Zy ≤ K := (Subgroup.zpowers_le).2 hyK
  have hZy'K' : Zy' ≤ K' := (Subgroup.zpowers_le).2 hy'K
  have hZbcomm : ∀ g ∈ K, ∀ h ∈ Zb, g * h = h * g := by
    intro g hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute b g from hbc g (hK.1 hg)) k)).symm.eq
  have hZbcomm' : ∀ g ∈ K', ∀ h ∈ Zb, g * h = h * g := by
    intro g hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute b g from hbc g (hK'.1 hg)) k)).symm.eq
  have hc1 : ∀ a ∈ Zy, ∀ c ∈ Zy', a * c = c * a := fun a ha c hc =>
    hcommKK' a (hZyK ha) c (hZy'K' hc)
  obtain ⟨hprod1, hset1⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Zy Zy' hc1
  have hinf1 : Zy ⊓ Zy' = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha
    exact hcenK a (hZyK ha1) fun g hg => (hcommKK' g hg a (hZy'K' ha2)).symm
  have hcardZy : Nat.card Zy = 3 := by rw [hZy, Nat.card_zpowers, hy3]
  have hcardZy' : Nat.card Zy' = 3 := by rw [hZy', Nat.card_zpowers, hy'3]
  have hcardZb : Nat.card Zb = 3 := by rw [hZb, Nat.card_zpowers, hbord]
  rw [hinf1, Subgroup.card_bot, mul_one, hcardZy, hcardZy'] at hprod1
  have hc2 : ∀ a ∈ Zb, ∀ c ∈ Zy ⊔ Zy', a * c = c * a := by
    intro a ha c hc
    have hc' : c ∈ (Zy : Set S) * (Zy' : Set S) := by rw [← hset1]; exact hc
    obtain ⟨u, hu, v, hv, rfl⟩ := hc'
    rw [← mul_assoc, (hZbcomm u (hZyK hu) a ha).symm, mul_assoc, (hZbcomm' v (hZy'K' hv) a ha).symm,
      mul_assoc]
  obtain ⟨hprod2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Zb (Zy ⊔ Zy') hc2
  have hinf2 : Zb ⊓ (Zy ⊔ Zy') = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha
    have ha2' : a ∈ (Zy : Set S) * (Zy' : Set S) := by rw [← hset1]; exact ha2
    obtain ⟨u, hu, v, hv, huv⟩ := ha2'
    have hu1 : u = 1 := by
      refine hcenK u (hZyK hu) fun g hg => ?_
      have hu' : u = a * v⁻¹ := by rw [← huv]; group
      rw [hu']
      have h1 := hZbcomm g hg a ha1
      have h2 := hcommKK' g hg v⁻¹ (K'.inv_mem (hZy'K' hv))
      calc a * v⁻¹ * g = a * (v⁻¹ * g) := by group
        _ = a * (g * v⁻¹) := by rw [h2]
        _ = (a * g) * v⁻¹ := by group
        _ = (g * a) * v⁻¹ := by rw [h1]
        _ = g * (a * v⁻¹) := by group
    rw [hu1] at huv
    have hva : v = a := by simpa using huv
    subst hva
    exact hcenK' v (hZy'K' hv) fun g hg => (hZbcomm' g hg v ha1).symm
  rw [hinf2, Subgroup.card_bot, mul_one, hcardZb, hprod1] at hprod2
  set A : Subgroup S := Subgroup.closure ({b, y, y'} : Set S) with hA
  have hpair : ({b, y, y'} : Set S).Pairwise Commute := by
    have hby : Commute b y := hbc y (hK.1 hyK)
    have hby' : Commute b y' := hbc y' (hK'.1 hy'K)
    have hyy' : Commute y y' := hcommKK' y hyK y' hy'K
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  have hAcomm : IsMulCommutative A := Subgroup.isMulCommutative_closure hpair
  have hle : Zb ⊔ (Zy ⊔ Zy') ≤ A := by
    refine sup_le ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))) (sup_le ?_ ?_)
    · exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
    · exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  refine ⟨A, ⟨hAcomm, ?_⟩, ?_, ?_⟩
  · intro a ha
    induction ha using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hb3
      · rw [← hy3]; exact pow_orderOf_eq_one _
      · rw [← hy'3]; exact pow_orderOf_eq_one _
    | one => exact one_pow 3
    | mul u v hu hv ihu ihv =>
      have hcuv : Commute u v := by
        have h := hAcomm.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
        exact congrArg Subtype.val h
      rw [hcuv.mul_pow, ihu, ihv, one_mul]
    | inv u hu ihu => rw [inv_pow, ihu, inv_one]
  · intro a ha
    induction ha using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact hxb
      · exact hxy
      · exact hxy'
    | one => exact map_one x
    | mul u v hu hv ihu ihv => rw [map_mul, ihu, ihv]
    | inv u hu ihu => rw [map_inv, ihu]
  · intro h9
    have h27 : 27 ≤ Nat.card A :=
      calc 27 = 3 * (3 * 3) := by norm_num
        _ = Nat.card (Zb ⊔ (Zy ⊔ Zy') : Subgroup S) := hprod2.symm
        _ ≤ Nat.card A := Subgroup.card_le_of_le hle
    omega

@[expose] def PGU38OrderThreeAutClasses : Prop :=
  ∀ (C : Type) [Group C], CFSG.RankThree.PartTwo.Sec8.IsoPGUThree C (2 ^ 3) →
    ∀ (θ : MulAut C) (b : C), b ^ 3 = 1 → ∃ h : C, h * θ b * h⁻¹ = b ∨ h * θ b * h⁻¹ = b⁻¹

section SL2Eight

open CFSG.LieType.Chevalley

variable {F : Type} [Field F] [Finite F]

theorem exists_inv_conj_sl2_d4b (hF : Nat.card F = 2 ^ 3) {B : SL2 F} (hB3 : B ^ 3 = 1)
    (hB1 : B ≠ 1) : ∃ A : SL2 F, A * B * A⁻¹ = B⁻¹ ∧ A * A = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (k := 3) (by norm_num) hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have htr := CFSG.HardMathSupport.Seitz.Proving.trace_eq_neg_one_of_cube hB3 hB1
  set a := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (B : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (B : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (B : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hdet : a * d - b * c = 1 := det_SL2 B
  have hc0 : c ≠ 0 := by
    intro hc0
    have had : a * d = 1 := by rw [hc0, mul_zero, sub_zero] at hdet; exact hdet
    have hq : a ^ 2 + a + 1 = 0 := by
      have hd' : d = -1 - a := by linear_combination htr
      rw [hd'] at had
      linear_combination -had
    have ha3 : a ^ 3 = 1 := by linear_combination (a - 1) * hq
    have ha0 : a ≠ 0 := by
      rintro h0
      rw [h0] at hq
      norm_num at hq
    have hcard : Nat.card Fˣ = 7 := by
      haveI : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
      norm_num
    have h7 : a ^ 7 = 1 := by
      have h := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 a ha0)
      rw [hcard] at h
      have h' := congrArg Units.val h
      simpa using h'
    have ha1 : a = 1 := by
      calc a = a ^ 7 * ((a ^ 3) ^ 2)⁻¹ := by field_simp
        _ = 1 := by rw [h7, ha3]; simp
    rw [ha1] at hq
    have h3 : (3 : F) = 0 := by linear_combination hq
    have h31 : (3 : F) = 1 := by linear_combination h2
    rw [h31] at h3
    exact one_ne_zero h3
  refine ⟨uSL c⁻¹, ?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    have hBm : (B : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, coe_uSL, hBm, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hc0]
      linear_combination htr - d * h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination b * h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination c * h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hc0]
      linear_combination -htr + (1 + d) * h2
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination c⁻¹ * h2

end SL2Eight

section D4


set_option linter.unusedSectionVars false

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three (d4Graph d4P coe_d4Graph d4Rho)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz (d4Q d4Q_mul_self d4Q_inv
  d4SwapMap d4Swap d4Swap_cartan labelMap labelMap_conj_mem labelMap_mul_xOp labelMap_mul_yOp
  d4P_mul_swap_mul_d4P)
open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph (sl2At gammaP coe_sl2At sl2At_uSL
  sl2At_vSL sl2_hom_ext d4Graph_sl2At IsG2Type IsA2Type)

variable {F : Type} [Field F]

theorem map_conj_d4Q_d4b :
    (adjointGroup Tag.D4 F).map (MulAut.conj (d4Q F)).toMonoidHom = adjointGroup Tag.D4 F := by
  have hmem : ∀ g ∈ adjointGroup Tag.D4 F, d4Q F * g * (d4Q F)⁻¹ ∈ adjointGroup Tag.D4 F :=
    fun g hg => labelMap_conj_mem (τ := TwistTag.D4.tag) F d4Swap_cartan hg
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact hmem g hg
  · intro g hg
    refine ⟨d4Q F * g * (d4Q F)⁻¹, hmem g hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [d4Q_inv]
    calc d4Q F * (d4Q F * g * d4Q F) * d4Q F
        = (d4Q F * d4Q F) * g * (d4Q F * d4Q F) := by group
      _ = g := by rw [d4Q_mul_self, one_mul, mul_one]

variable (F) in
@[expose] noncomputable def swapAutD4b : MulAut (adjointGroup Tag.D4 F) :=
  mulAutRestrict (adjointGroup Tag.D4 F) (MulAut.conj (d4Q F)) map_conj_d4Q_d4b

theorem coe_swapAutD4b (h : adjointGroup Tag.D4 F) :
    (swapAutD4b F h : ModGL Tag.D4 F) = d4Q F * h * (d4Q F)⁻¹ := rfl

theorem swapAutD4b_mul_self : swapAutD4b F * swapAutD4b F = 1 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_swapAutD4b, coe_swapAutD4b, MulAut.one_apply, d4Q_inv]
  calc d4Q F * (d4Q F * (h : ModGL Tag.D4 F) * d4Q F) * d4Q F
      = (d4Q F * d4Q F) * (h : ModGL Tag.D4 F) * (d4Q F * d4Q F) := by group
    _ = h := by rw [d4Q_mul_self, one_mul, mul_one]

theorem swapAutD4b_inv : (swapAutD4b F)⁻¹ = swapAutD4b F :=
  inv_eq_of_mul_eq_one_right swapAutD4b_mul_self

theorem d4Q_mul_d4P_mul_inv_d4b : d4Q F * d4P F * (d4Q F)⁻¹ = (d4P F)⁻¹ := by
  have h := d4P_mul_swap_mul_d4P F
  change d4P F * d4Q F * d4P F = d4Q F at h
  calc d4Q F * d4P F * (d4Q F)⁻¹ = (d4P F)⁻¹ * (d4P F * d4Q F * d4P F) * (d4Q F)⁻¹ := by group
    _ = (d4P F)⁻¹ := by rw [h, mul_inv_cancel_right]

theorem swapAutD4b_conj_d4Graph_one :
    swapAutD4b F * d4Graph F 1 * (swapAutD4b F)⁻¹ = d4Graph F 2 := by
  have hP3 : d4P F ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 F
  have hP2 : d4P F ^ 2 = (d4P F)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hP3
  have hQP := d4Q_mul_d4P_mul_inv_d4b (F := F)
  rw [swapAutD4b_inv]
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_swapAutD4b, coe_d4Graph, coe_swapAutD4b,
    coe_d4Graph, pow_one, hP2, d4Q_inv]
  have hQP' : d4Q F * d4P F * d4Q F = (d4P F)⁻¹ := by rw [← d4Q_inv]; exact hQP
  calc d4Q F * (d4P F * (d4Q F * (h : ModGL Tag.D4 F) * d4Q F) * (d4P F)⁻¹) * d4Q F
      = (d4Q F * d4P F * d4Q F) * (h : ModGL Tag.D4 F) *
          (d4Q F * (d4P F)⁻¹ * d4Q F) := by group
    _ = (d4P F)⁻¹ * (h : ModGL Tag.D4 F) * (d4P F)⁻¹⁻¹ := by
        rw [hQP']
        congr 1
        calc d4Q F * (d4P F)⁻¹ * d4Q F = (d4Q F * d4P F * d4Q F)⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, d4Q_inv, mul_assoc]
          _ = (d4P F)⁻¹⁻¹ := by rw [hQP']

theorem d4Graph_one_inv_d4b : (d4Graph F 1)⁻¹ = d4Graph F 2 := by
  rw [inv_eq_iff_mul_eq_one, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three]

theorem swapAutD4b_conj_d4Graph_two :
    swapAutD4b F * d4Graph F 2 * (swapAutD4b F)⁻¹ = d4Graph F 1 := by
  have h := swapAutD4b_conj_d4Graph_one (F := F)
  rw [← h, swapAutD4b_inv]
  rw [show swapAutD4b F * (swapAutD4b F * d4Graph F 1 * swapAutD4b F) * swapAutD4b F =
      (swapAutD4b F * swapAutD4b F) * d4Graph F 1 * (swapAutD4b F * swapAutD4b F) by group,
    swapAutD4b_mul_self, one_mul, mul_one]

theorem swapAutD4b_sl2At_two (A : SL2 F) :
    swapAutD4b F (sl2At F ⟨2, by decide⟩ A) = sl2At F ⟨2, by decide⟩ A := by
  have hs : d4Swap ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have h : (swapAutD4b F).toMonoidHom.comp (sl2At F ⟨2, by decide⟩) = sl2At F ⟨2, by decide⟩ := by
    refine sl2_hom_ext (fun c => ?_) fun c => ?_
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, sl2At_uSL]
      refine Subtype.ext (Units.ext ?_)
      rw [coe_swapAutD4b]
      change (d4Q F : Module.End F (RootModule Tag.D4 F)) * xOp Tag.D4 F ⟨2, by decide⟩ c *
          ((d4Q F)⁻¹ : ModGL Tag.D4 F) = xOp Tag.D4 F ⟨2, by decide⟩ c
      have h1 := labelMap_mul_xOp (τ := TwistTag.D4.tag) F d4Swap_cartan ⟨2, by decide⟩ c
      change (d4Q F : Module.End F (RootModule Tag.D4 F)) * xOp Tag.D4 F ⟨2, by decide⟩ c =
          xOp Tag.D4 F (d4Swap ⟨2, by decide⟩) c * (d4Q F : Module.End F (RootModule Tag.D4 F))
        at h1
      rw [h1, hs, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rfl
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, sl2At_vSL]
      refine Subtype.ext (Units.ext ?_)
      rw [coe_swapAutD4b]
      change (d4Q F : Module.End F (RootModule Tag.D4 F)) * yOp Tag.D4 F ⟨2, by decide⟩ c *
          ((d4Q F)⁻¹ : ModGL Tag.D4 F) = yOp Tag.D4 F ⟨2, by decide⟩ c
      have h1 := labelMap_mul_yOp (τ := TwistTag.D4.tag) F d4Swap_cartan ⟨2, by decide⟩ c
      change (d4Q F : Module.End F (RootModule Tag.D4 F)) * yOp Tag.D4 F ⟨2, by decide⟩ c =
          yOp Tag.D4 F (d4Swap ⟨2, by decide⟩) c * (d4Q F : Module.End F (RootModule Tag.D4 F))
        at h1
      rw [h1, hs, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rfl
  exact congrArg (fun f => f A) h

theorem d4Graph_sl2At_two_d4b (ε : ℕ) (A : SL2 F) :
    d4Graph F ε (sl2At F ⟨2, by decide⟩ A) = sl2At F ⟨2, by decide⟩ A := by
  rw [d4Graph_sl2At]
  have h : ∀ n : ℕ, (d4Rho ^ n) (⟨2, by decide⟩ : Fin Tag.D4.rank) = ⟨2, by decide⟩ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      have h2 : d4Rho (⟨2, by decide⟩ : Fin Tag.D4.rank) = ⟨2, by decide⟩ := by decide
      rw [h2, ih]
  rw [h ε]

theorem exists_inv_gammaP_d4b [Finite F] (hF : Nat.card F = 2 ^ 3) {B : SL2 F} (hB3 : B ^ 3 = 1)
    (hB1 : B ≠ 1) :
    ∃ δ : MulAut (adjointGroup Tag.D4 F), δ * δ = 1 ∧ δ * gammaP F B * δ⁻¹ = (gammaP F B)⁻¹ := by
  obtain ⟨A, hAB, hAA⟩ := exists_inv_conj_sl2_d4b hF hB3 hB1
  set ψ := sl2At F ⟨2, by decide⟩ with hψ
  set δ := swapAutD4b F with hδ
  have hδψ : ∀ C : SL2 F, δ * MulAut.conj (ψ C) = MulAut.conj (ψ C) * δ := by
    intro C
    rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq, hδ, swapAutD4b_sl2At_two]
  have hγψ : ∀ (ε : ℕ) (C : SL2 F), d4Graph F ε * MulAut.conj (ψ C) =
      MulAut.conj (ψ C) * d4Graph F ε := by
    intro ε C
    rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq, d4Graph_sl2At_two_d4b]
  have hδinv : δ⁻¹ = δ := swapAutD4b_inv
  have hδγ : δ * d4Graph F 1 * δ = d4Graph F 2 := by
    have h := swapAutD4b_conj_d4Graph_one (F := F)
    rwa [← hδ, hδinv] at h
  refine ⟨MulAut.conj (ψ A) * δ, ?_, ?_⟩
  · calc MulAut.conj (ψ A) * δ * (MulAut.conj (ψ A) * δ)
        = MulAut.conj (ψ A) * (δ * MulAut.conj (ψ A)) * δ := by group
      _ = MulAut.conj (ψ A) * (MulAut.conj (ψ A) * δ) * δ := by rw [hδψ]
      _ = MulAut.conj (ψ (A * A)) * (δ * δ) := by rw [map_mul, map_mul]; group
      _ = 1 := by
          have hδδ : δ * δ = 1 := swapAutD4b_mul_self
          rw [hAA, map_one, map_one, hδδ, mul_one]
  · have hgP : gammaP F B = MulAut.conj (ψ B) * d4Graph F 1 := rfl
    have hinvγ : (d4Graph F 1)⁻¹ = d4Graph F 2 := d4Graph_one_inv_d4b
    have hiA : (MulAut.conj (ψ A))⁻¹ = MulAut.conj (ψ A⁻¹) := by rw [map_inv, map_inv]
    have hiB : (MulAut.conj (ψ B))⁻¹ = MulAut.conj (ψ B⁻¹) := by rw [map_inv, map_inv]
    rw [hgP, mul_inv_rev, mul_inv_rev, hδinv, hinvγ, hiA, hiB]
    calc MulAut.conj (ψ A) * δ * (MulAut.conj (ψ B) * d4Graph F 1) *
          (δ * MulAut.conj (ψ A⁻¹))
        = MulAut.conj (ψ A) * (δ * MulAut.conj (ψ B)) * d4Graph F 1 * δ *
            MulAut.conj (ψ A⁻¹) := by group
      _ = MulAut.conj (ψ A) * MulAut.conj (ψ B) * (δ * d4Graph F 1 * δ) *
            MulAut.conj (ψ A⁻¹) := by rw [hδψ]; group
      _ = MulAut.conj (ψ A) * MulAut.conj (ψ B) * (d4Graph F 2 * MulAut.conj (ψ A⁻¹)) := by
            rw [hδγ]; group
      _ = MulAut.conj (ψ (A * B * A⁻¹)) * d4Graph F 2 := by
            rw [hγψ, map_mul, map_mul, map_mul, map_mul]; group
      _ = MulAut.conj (ψ B⁻¹) * d4Graph F 2 := by rw [hAB]
      _ = d4Graph F 2 * MulAut.conj (ψ B⁻¹) := (hγψ 2 B⁻¹).symm

theorem exists_inverting_involution_d4b [Finite F] (hF : Nat.card F = 2 ^ 3)
    {x : MulAut (adjointGroup Tag.D4 F)} (hx3 : x ^ 3 = 1)
    (hA : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType x fun ε σ => ε ≠ 0 ∧ σ = 1) :
    ∃ δ : MulAut (adjointGroup Tag.D4 F), δ * δ = 1 ∧ δ * x * δ⁻¹ = x⁻¹ := by
  have h2 : ringChar F = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.ringChar_eq_two_of_card hF
  have hstd : ∃ (ψ x₀ δ₀ : MulAut (adjointGroup Tag.D4 F)), ψ * x * ψ⁻¹ = x₀ ∧ δ₀ * δ₀ = 1 ∧
      δ₀ * x₀ * δ₀⁻¹ = x₀⁻¹ := by
    have hδ1 : swapAutD4b F * d4Graph F 1 * (swapAutD4b F)⁻¹ = (d4Graph F 1)⁻¹ := by
      rw [swapAutD4b_conj_d4Graph_one, d4Graph_one_inv_d4b]
    have hδ2 : swapAutD4b F * d4Graph F 2 * (swapAutD4b F)⁻¹ = (d4Graph F 2)⁻¹ := by
      rw [swapAutD4b_conj_d4Graph_two, ← d4Graph_one_inv_d4b, inv_inv]
    rcases CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.isG2Type_or_isA2Type_of_charTwo
        F h2 x hx3 hA with ⟨ψ, h | h⟩ | ⟨ψ, B, hB3, hB1, h | h⟩
    · exact ⟨ψ, _, _, h, swapAutD4b_mul_self, hδ1⟩
    · exact ⟨ψ, _, _, h, swapAutD4b_mul_self, hδ2⟩
    · obtain ⟨δ₀, hδ₀2, hδ₀⟩ := exists_inv_gammaP_d4b hF hB3 hB1
      exact ⟨ψ, _, δ₀, h, hδ₀2, hδ₀⟩
    · obtain ⟨δ₀, hδ₀2, hδ₀⟩ := exists_inv_gammaP_d4b hF hB3 hB1
      refine ⟨ψ, _, δ₀, h, hδ₀2, ?_⟩
      rw [inv_inv]
      calc δ₀ * (gammaP F B)⁻¹ * δ₀⁻¹ = (δ₀ * gammaP F B * δ₀⁻¹)⁻¹ := by group
        _ = gammaP F B := by rw [hδ₀, inv_inv]
  obtain ⟨ψ, x₀, δ₀, hx₀, hδ₀2, hδ₀⟩ := hstd
  refine ⟨ψ⁻¹ * δ₀ * ψ, ?_, ?_⟩
  · calc ψ⁻¹ * δ₀ * ψ * (ψ⁻¹ * δ₀ * ψ) = ψ⁻¹ * (δ₀ * δ₀) * ψ := by group
      _ = 1 := by rw [hδ₀2]; group
  · have hx : x = ψ⁻¹ * x₀ * ψ := by rw [← hx₀]; group
    rw [hx]
    calc ψ⁻¹ * δ₀ * ψ * (ψ⁻¹ * x₀ * ψ) * (ψ⁻¹ * δ₀ * ψ)⁻¹ = ψ⁻¹ * (δ₀ * x₀ * δ₀⁻¹) * ψ := by
          group
      _ = (ψ⁻¹ * x₀ * ψ)⁻¹ := by rw [hδ₀]; group

theorem conj_inv_conj_of_fix_d4b {G : Type} [Group G] {x : MulAut G} {c : G} (hc : x c = c) :
    MulAut.conj c * x⁻¹ * (MulAut.conj c)⁻¹ = x⁻¹ := by
  have h : x * MulAut.conj c = MulAut.conj c * x := by
    rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq, hc]
  calc MulAut.conj c * x⁻¹ * (MulAut.conj c)⁻¹
      = x⁻¹ * (x * MulAut.conj c) * x⁻¹ * (MulAut.conj c)⁻¹ := by group
    _ = x⁻¹ * (MulAut.conj c * x) * x⁻¹ * (MulAut.conj c)⁻¹ := by rw [h]
    _ = x⁻¹ := by group

theorem exists_inv_fix_d4b [Finite F] (hF : Nat.card F = 2 ^ 3) (hP : PGU38OrderThreeAutClasses)
    {x : MulAut (adjointGroup Tag.D4 F)} (hx3 : x ^ 3 = 1)
    (hA : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType x fun ε σ => ε ≠ 0 ∧ σ = 1)
    {b : adjointGroup Tag.D4 F} (hb3 : b ^ 3 = 1) (hxb : x b = b) :
    ∃ σ : MulAut (adjointGroup Tag.D4 F), σ * x * σ⁻¹ = x⁻¹ ∧ (σ b = b ∨ σ b = b⁻¹) := by
  classical
  obtain ⟨δ, hδ2, hδx⟩ := exists_inverting_involution_d4b hF hx3 hA
  set C := fixSubgroup x with hC
  have hδC : C.map δ.toMonoidHom = C := by
    rw [hC, fixSubgroup_map_of_conj_d4b, hδx, fixSubgroup_inv_d4b]
  set θ : MulAut C := mulAutRestrict C δ hδC with hθ
  have hθapp : ∀ c : C, ((θ c : C) : adjointGroup Tag.D4 F) = δ c := fun c => rfl
  have hθ2 : θ * θ = 1 := by
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [MulAut.mul_apply, hθapp, hθapp, MulAut.one_apply, ← MulAut.mul_apply, hδ2,
      MulAut.one_apply]
  have hbC : b ∈ C := hxb
  have hfix : CFSG.RankThree.PartOne.CTP.fixedSubgroup x = C := Subgroup.ext fun _ => Iff.rfl
  have hinvC : ∀ c ∈ C, MulAut.conj c * δ * x * (MulAut.conj c * δ)⁻¹ = x⁻¹ := by
    intro c hc
    calc MulAut.conj c * δ * x * (MulAut.conj c * δ)⁻¹
        = MulAut.conj c * (δ * x * δ⁻¹) * (MulAut.conj c)⁻¹ := by group
      _ = x⁻¹ := by rw [hδx]; exact conj_inv_conj_of_fix_d4b hc
  rcases CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2.graphFix_cases hF hx3 hA
    with ⟨F', hF'f, hF'fin, hF'card, ⟨eG⟩⟩ | hPGU
  · letI := hF'f
    letI := hF'fin
    set eC : C ≃* adjointGroup Tag.G2 F' := (MulEquiv.subgroupCongr hfix).symm.trans eG with heC
    obtain ⟨-, Θ, -, -, hker, hinv⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        (f := 3) (by norm_num) F' hF'card
    set θ' := MulAut.congr eC θ with hθ'
    have hθ'2 : θ' ^ 2 = 1 := by rw [pow_two, hθ', ← map_mul, hθ2, map_one]
    have hΘ : Θ θ' = 1 := by
      rcases hinv θ' hθ'2 with h | ⟨he, -⟩
      · exact h
      · exact absurd he (by decide)
    obtain ⟨g', hg'⟩ : θ' ∈ (MulAut.conj : adjointGroup Tag.G2 F' →* MulAut _).range := by
      rw [← hker]
      exact hΘ
    set g : C := eC.symm g' with hg
    have hθg : θ = MulAut.conj g := by
      apply (MulAut.congr eC).injective
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, hg,
        MulEquiv.apply_symm_apply]
      exact hg'.symm
    have hδc : ∀ c ∈ C, δ c = (g : adjointGroup Tag.D4 F) * c * (g : adjointGroup Tag.D4 F)⁻¹ := by
      intro c hc
      have h := congrArg (fun φ : MulAut C => ((φ ⟨c, hc⟩ : C) : adjointGroup Tag.D4 F)) hθg
      simpa [hθapp, MulAut.conj_apply] using h
    refine ⟨MulAut.conj ((g : adjointGroup Tag.D4 F))⁻¹ * δ, hinvC _ (C.inv_mem g.2), Or.inl ?_⟩
    rw [MulAut.mul_apply, hδc b hbC, MulAut.conj_apply]
    group
  · have hPGU' : CFSG.RankThree.PartTwo.Sec8.IsoPGUThree C (2 ^ 3) := by
      obtain ⟨K, hK1, hK2, hK3, ⟨e⟩⟩ := hPGU
      exact ⟨K, hK1, hK2, hK3, ⟨(MulEquiv.subgroupCongr hfix).symm.trans e⟩⟩
    have hb3' : (⟨b, hbC⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    obtain ⟨h, hh⟩ := hP C hPGU' θ ⟨b, hbC⟩ hb3'
    refine ⟨MulAut.conj (h : adjointGroup Tag.D4 F) * δ, hinvC _ h.2, ?_⟩
    rw [MulAut.mul_apply, MulAut.conj_apply]
    rcases hh with hh | hh
    · left
      have h1 := congrArg (fun c : C => (c : adjointGroup Tag.D4 F)) hh
      simpa [hθapp] using h1
    · right
      have h1 := congrArg (fun c : C => (c : adjointGroup Tag.D4 F)) hh
      simpa [hθapp] using h1

end D4

section Assembly


set_option linter.unusedSectionVars false

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three (d4Graph)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10 (card_le_nine_of_graphType_d4Eight)

theorem not_sq_nineteen_dvd_ordD_four_eight_d4b : ¬ 19 ^ 2 ∣ CFSG.Open.ordD 4 (2 ^ 3) := by
  unfold CFSG.Open.ordD
  decide

theorem d4EightTrialityInnerPairs_of_pgu38 (hP : PGU38OrderThreeAutClasses) :
    D4EightTrialityInnerPairs := by
  intro F _ _ hF β hβmem hβ3 hβ1 K hK e he hiso x hxmem hx3 hβx hR hxstab
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ringChar F = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.ringChar_eq_two_of_card hF
  have hZ : Subgroup.center (adjointGroup Tag.D4 F) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨b, hb3, rfl⟩ := exists_pow_eq_one_of_mem_inner hZ hR.1 hβ3
  have hb1 : b ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  obtain ⟨ε, s, hε, hxeq⟩ : ∃ (ε : ℕ) (s : adjointGroup Tag.D4 F), (ε = 1 ∨ ε = 2) ∧
      x = MulAut.conj s * d4Graph F ε := by
    rcases exists_conj_or_exists_conj_mul_d4Graph h2 hxmem hx3 with ⟨s, hs⟩ | h
    · exact absurd ⟨s, hs.symm⟩ hR.2
    · exact h
  have hone : exactNormalAut Tag.D4 F (1 : Fin Tag.D4.rank → Fˣ) 1 0 = 1 := by
    rw [← CFSG.LieType.SeitzGeneration.ExcWideThree.rootDiagAut_eq_normalAut]
    exact (rootDiagAutHom Tag.D4 F).map_one
  have hA : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType x
      fun ε σ => ε ≠ 0 ∧ σ = 1 :=
    ⟨s, 1, 1, ε, by omega, by simp, ⟨by omega, rfl⟩, by rw [hxeq, hone, one_mul]⟩
  have hG : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType x fun ε _ => ε ≠ 0 := by
    obtain ⟨g, a, σ, ε', h1, h2', h3, h4⟩ := hA
    exact ⟨g, a, σ, ε', h1, h2', h3.1, h4⟩
  have hxb : x b = b := by
    have h1 : x * MulAut.conj b = MulAut.conj b * x := hβx.symm
    rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq] at h1
    exact CFSG.mulAutConj_injective_of_center_eq_bot hZ (mul_right_cancel h1)
  obtain ⟨σ, hσx, hσb⟩ := exists_inv_fix_d4b hF hP hx3 hA hb3 hxb
  have hσβ : σ * MulAut.conj b * σ⁻¹ = MulAut.conj b ∨
      σ * MulAut.conj b * σ⁻¹ = (MulAut.conj b)⁻¹ := by
    rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq, mul_inv_cancel_right]
    rcases hσb with h | h
    · left
      rw [h]
    · right
      rw [h, map_inv]
  set L := K.map σ.toMonoidHom with hLdef
  have hL : IsComponentOf L (fixSubgroup (MulAut.conj b)) := isComponentOf_map_of_inv_d4b hσβ hK
  set eKL : ↥K ≃* ↥L := K.equivMapOfInjective σ.toMonoidHom σ.injective with heKL
  have hcardQ : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    (Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥L) eKL
      (Subgroup.map_center_eq eKL)).toEquiv).symm
  have hLK : L = K := by
    obtain ⟨q, hq, hqcard⟩ := he
    obtain ⟨ei, hv⟩ := e
    rcases hq with hA1 | htw
    ·
      simp only at hA1
      subst hA1
      have hk8 : Nat.card (GaloisField 2 3) = 8 := by
        rw [GaloisField.card 2 3 (by norm_num)]
        norm_num
      obtain ⟨eP⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
        (n := 1) (k := GaloisField 2 3) q hv (by rw [hk8, hqcard])
      obtain ⟨eK⟩ := hiso
      have ePSL : ↥K ⧸ Subgroup.center ↥K ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
        (eK.trans eP.symm).trans (QuotientGroup.quotientMulEquivOfEq
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 _))
      haveI : Finite ↥K := inferInstance
      have hZK : Subgroup.center ↥K = ⊥ :=
        CFSG.AGLEmbedding.L28Parabolic.center_eq_bot hK.2.2 ePSL
      have hZL : Subgroup.center ↥L = ⊥ := by
        rw [← Subgroup.map_center_eq eKL, hZK, Subgroup.map_bot]
      have hcardK : Nat.card ↥K = 504 := by
        rw [← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZK).trans
          QuotientGroup.quotientBot).toEquiv, Nat.card_congr eK.toEquiv,
          card_catGroup_A_one_eight hk8 hqcard]
      have hcardL : Nat.card ↥L = 504 := by rw [← hcardK]; exact (Nat.card_congr eKL.toEquiv).symm
      have hσinv : σ⁻¹ * x * σ = x⁻¹ := by
        calc σ⁻¹ * x * σ = (σ⁻¹ * x⁻¹ * σ)⁻¹ := by group
          _ = (σ⁻¹ * (σ * x * σ⁻¹) * σ)⁻¹ := by rw [hσx]
          _ = x⁻¹ := by group
      have hxL : x ∈ CFSG.GroupActions.subgroupStabAut L := by
        change L.map x.toMonoidHom = L
        have hxK' : K.map (x⁻¹).toMonoidHom = K := (inv_mem hxstab : x⁻¹ ∈ _)
        rw [hLdef, Subgroup.map_map]
        have hcomp : x.toMonoidHom.comp σ.toMonoidHom = σ.toMonoidHom.comp (x⁻¹).toMonoidHom := by
          refine MonoidHom.ext fun g => ?_
          have h := congrArg (fun φ : MulAut (adjointGroup Tag.D4 F) => φ g)
            (show x * σ = σ * x⁻¹ by rw [← hσinv]; group)
          simpa [MulAut.mul_apply] using h
        rw [hcomp, ← Subgroup.map_map, hxK']
      by_contra hne
      obtain ⟨A, hAel, hAfix, hA9⟩ := exists_elemAbelian_twentySeven_d4b hb3 hb1 hx3 hxb hL hK hne
        hxL hxstab hZL hZK (by rw [hcardL]; norm_num) (by rw [hcardK]; norm_num)
      exact hA9 (card_le_nine_of_graphType_d4Eight hF hx3 hG A hAel hAfix)
    ·
      simp only at htw
      subst htw
      obtain ⟨eK⟩ := hiso
      have hcardK : Nat.card (↥K ⧸ Subgroup.center ↥K) = 5515776 := by
        rw [Nat.card_congr eK.toEquiv, card_catGroup_twistedA_two_eight hqcard]
      have h19 : 19 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by rw [hcardK]; norm_num
      have hS : ¬ 19 ^ 2 ∣ Nat.card (adjointGroup Tag.D4 F) := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz.card_adjointGroup_D4_eight
          hF]
        exact not_sq_nineteen_dvd_ordD_four_eight_d4b
      exact eq_of_isComponentOf_of_nineteen_d4b hL hK (hcardQ ▸ h19) h19 hS
  have hσK : σ ∈ CFSG.GroupActions.subgroupStabAut K := hLK
  exact centerQuotientHom_mem_innAutDerived_of_inv_d4b hxstab hσK hx3 hσx

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
