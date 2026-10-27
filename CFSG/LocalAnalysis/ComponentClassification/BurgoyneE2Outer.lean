module

public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer
public import CFSG.LieType.Chevalley.GraphFixedOddComponents
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Comp

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.FieldGraphFieldPointwise (mem_zpowers_of_forall_fixedFieldImage
  mem_zpowers_of_forall_graphFixedRootGroup graphField_eq_exactNormalAut
  exactNormalAut_one_mul_graphField graphField_apply exactNormalAut_one_zero_eq)

theorem burgCoreFor_of_normal_quasisimple {T : Type} [Group T]
    [Finite T] (hZ : center T = ⊥) {α : MulAut T} {J : Subgroup T} (hJα : J ≤ fixedSubgroup α)
    (hJn : ∀ g ∈ fixedSubgroup α, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hJq : IsQuasisimple J)
    (hfix : ∀ β : MulAut T, Odd (orderOf β) → (∀ x ∈ J, β x = x) → β = 1) :
    BurgCoreFor α := by
  have hinj := conj_injective hZ
  have hodd1 : ∀ n : T, Odd (orderOf n) → (∀ j ∈ J, n * j = j * n) → n = 1 := by
    intro n hn hc
    apply hinj
    rw [map_one]
    refine hfix _ (by rwa [orderOf_injective _ hinj]) fun x hx => ?_
    rw [MulAut.conj_apply, hc x hx, mul_inv_cancel_right]
  refine ⟨?_, fun β hβ _ hβfix => hfix β hβ fun x hx => hβfix x (hJα hx)⟩
  rw [pPrimeCore_eq_bot_iff]
  intro N hNn hNodd
  have hcopN : ∀ n ∈ N, Odd (orderOf (n : T)) := by
    intro n hn
    have h1 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    have h2 : Odd (Nat.card N) := Nat.coprime_two_left.1 hNodd
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat h2 h1
  have hNJ : ∀ n ∈ N, (n : T) ∈ J → n = 1 := by
    intro n hn hnJ
    let D : Subgroup J := (N.map (fixedSubgroup α).subtype).subgroupOf J
    have hDn : D.Normal := ⟨fun d hd j => by
      obtain ⟨m, hm, hmd⟩ := hd
      refine ⟨⟨(j : T), hJα j.2⟩ * m * ⟨(j : T), hJα j.2⟩⁻¹, hNn.conj_mem m hm _, ?_⟩
      have hmd' : (m : T) = (d : T) := hmd
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hmd']⟩
    have hDodd : Nat.Coprime 2 (Nat.card D) := by
      let φ : D →* N :=
        { toFun := fun d => ⟨⟨(d : J), hJα (d : J).2⟩, by
            obtain ⟨m, hm, hmd⟩ := d.2
            have : m = ⟨((d : J) : T), hJα (d : J).2⟩ := Subtype.ext hmd
            rw [← this]
            exact hm⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hφ : Function.Injective φ := fun d d' h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : N => ((x : fixedSubgroup α) : T)) h
      exact hNodd.coprime_dvd_right (Subgroup.card_dvd_of_injective φ hφ)
    have hDZ := le_center_of_odd_normal_of_isQuasisimple hJq D hDodd
    have hz : (⟨(n : T), hnJ⟩ : J) ∈ center J := hDZ ⟨n, hn, rfl⟩
    refine Subtype.ext (hodd1 n (hcopN n hn) fun j hj => ?_)
    have := (mem_center_iff.1 hz) ⟨j, hj⟩
    exact (congrArg Subtype.val this).symm
  rw [eq_bot_iff]
  intro n hn
  have hc : ∀ j ∈ J, (n : T) * j = j * n := by
    intro j hj
    set jF : fixedSubgroup α := ⟨j, hJα hj⟩
    have hcN : n * jF * n⁻¹ * jF⁻¹ ∈ N := by
      have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) jF)
      rwa [show n * (jF * n⁻¹ * jF⁻¹) = n * jF * n⁻¹ * jF⁻¹ by group] at this
    have hcJ : ((n * jF * n⁻¹ * jF⁻¹ : fixedSubgroup α) : T) ∈ J := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (hJn _ n.2 _ hj) (inv_mem hj)
    have h1 := congrArg Subtype.val (hNJ _ hcN hcJ)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h1
    calc (n : T) * j = (n * j * (n : T)⁻¹ * j⁻¹) * (j * n) := by group
      _ = j * n := by rw [h1, one_mul]
  exact Subgroup.mem_bot.2 (Subtype.ext (hodd1 n (hcopN n hn) hc))

theorem eq_one_of_odd_of_mem_zpowers {T : Type} [Group T] {α β : MulAut T} (hα : α ^ 2 = 1)
    (hβ : Odd (orderOf β)) (hmem : β ∈ zpowers α) : β = 1 := by
  have h1 : orderOf β ∣ 2 := (orderOf_dvd_of_mem_zpowers hmem).trans (orderOf_dvd_of_pow_eq_one hα)
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at hβ
    exact absurd hβ (by decide)


theorem burgCoreFor_E6_entrywise {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {δ : K ≃+* K} (hδ : δ * δ = 1) : BurgCoreFor (entrywiseAdjointAut TwistTag.E6.tag δ) := by
  classical
  obtain ⟨-, hinj, -, hJΓ, -, hJn, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup TwistTag.E6.tag K δ
  have hk2 := ringChar_fixSubfield_ne_two hK δ
  obtain ⟨hsimp, hnab, -⟩ := odd_pinned_Chevalley_p_components TwistTag.E6.tag (fixSubfield δ) hk2
  set J := (fixedFieldImage TwistTag.E6.tag δ).subgroupOf (adjointGroup TwistTag.E6.tag K) with hJ
  have hJle : fixedFieldImage TwistTag.E6.tag δ ≤ adjointGroup TwistTag.E6.tag K :=
    fun j hj => (hJΓ hj).1
  have hmemF : ∀ g : adjointGroup TwistTag.E6.tag K,
      g ∈ fixedSubgroup (entrywiseAdjointAut TwistTag.E6.tag δ) ↔
        (g : ModGL TwistTag.E6.tag K) ∈ entrywiseFixedGroup TwistTag.E6.tag δ := by
    intro g
    rw [mem_entrywiseFixedGroup]
    change entrywiseAdjointAut TwistTag.E6.tag δ g = g ↔ _
    rw [← Subtype.coe_inj, coe_entrywiseAdjointAut]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have hJq : IsQuasisimple J := by
    let e : J ≃* adjointGroup TwistTag.E6.tag (fixSubfield δ) :=
      (Subgroup.subgroupOfEquivOfLe hJle).trans
        (Subgroup.equivMapOfInjective (adjointGroup TwistTag.E6.tag (fixSubfield δ)) _ hinj).symm
    have := hsimp
    exact LocalCores.isQuasisimple_of_mulEquiv e.symm
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  refine burgCoreFor_of_normal_quasisimple (center_adjointGroup_eq_bot_field _ K) (J := J)
    (fun j hj => (hmemF j).2 (hJΓ hj)) (fun g hg j hj => ?_) hJq fun β hβ hfix => ?_
  ·
    have hgΓ := (hmemF g).1 hg
    have h := hJn.conj_mem ⟨j, hJΓ hj⟩ hj ⟨g, hgΓ⟩
    exact h
  ·
    refine eq_one_of_odd_of_mem_zpowers ?_ hβ
      (mem_zpowers_of_forall_fixedFieldImage δ fun j hj => hfix j hj)
    rw [sq, ← entrywiseAdjointAut_mul, hδ, entrywiseAdjointAut_one]

theorem burgCoreFor_E6_graphField {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2)
    {δ : K ≃+* K} (hδ : δ * δ = 1) :
    BurgCoreFor (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag δ) := by
  classical
  have hδδ : ∀ c, δ (δ c) = c := fun c => by
    rw [← RingAut.mul_apply, hδ]
    rfl
  obtain ⟨hsimp, hnab, -⟩ := odd_diagram_field_fixed_p_components TwistTag.E6 K hK δ
  obtain ⟨-, -, hcomm⟩ := odd_diagram_fixed_root_group_perfect TwistTag.E6 K hK δ
  set C0 := graphFixedRootGroup TwistTag.E6 K δ.toRingHom with hC0
  set J := C0.subgroupOf (adjointGroup TwistTag.E6.tag K) with hJ
  have hC0le : C0 ≤ adjointGroup TwistTag.E6.tag K := fun j hj =>
    (graphFixedRootGroup_le _ _ _ hj).1
  have hmemF : ∀ g : adjointGroup TwistTag.E6.tag K,
      g ∈ fixedSubgroup (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag δ) ↔
        (g : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K δ.toRingHom := by
    intro g
    rw [mem_twistedFixedGroup_iff_twistHom]
    change (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag δ) g = g ↔ _
    rw [← Subtype.coe_inj, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut,
      twistHom_apply]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  have hJq : IsQuasisimple J := by
    have hnab' : ∃ a b : C0, a * b ≠ b * a := hnab
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hC0le).symm
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab').1
  refine burgCoreFor_of_normal_quasisimple (center_adjointGroup_eq_bot_field _ K) (J := J)
    (fun j hj => graphField_apply δ hj) (fun g hg j hj => ?_) hJq fun β hβ hfix => ?_
  ·
    have hgΓ := (hmemF g).1 hg
    set Γ := twistedFixedGroup TwistTag.E6 K δ.toRingHom with hΓ
    change ((g * j * g⁻¹ : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈ C0
    rw [← hcomm]
    have hj' : (j : ModGL TwistTag.E6.tag K) ∈ ⁅Γ, Γ⁆ := by
      rw [hcomm]
      exact hj
    have hmap : (⁅Γ, Γ⁆).map (MulAut.conj (g : ModGL TwistTag.E6.tag K)).toMonoidHom ≤ ⁅Γ, Γ⁆ := by
      rw [Subgroup.map_commutator]
      have hle : Γ.map (MulAut.conj (g : ModGL TwistTag.E6.tag K)).toMonoidHom ≤ Γ := by
        rintro _ ⟨y, hy, rfl⟩
        exact mul_mem (mul_mem hgΓ hy) (inv_mem hgΓ)
      exact Subgroup.commutator_mono hle hle
    exact hmap ⟨_, hj', rfl⟩
  ·
    refine eq_one_of_odd_of_mem_zpowers ?_ hβ
      (mem_zpowers_of_forall_graphFixedRootGroup δ hδδ fun j hj => hfix j hj)
    rw [sq]
    nth_rewrite 1 [graphField_eq_exactNormalAut]
    rw [exactNormalAut_one_mul_graphField, hδ, exactNormalAut_one_zero_eq, entrywiseAdjointAut_one]

end CFSG.ComponentClassification.Burgoyne.E2
