module

public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenLinearTwo

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.oddCore_eq_bot_of_mulEquiv
  EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer EvenCatalog.oddCore_eq_bot_of_isSimpleGroup)

theorem oddCore_centralizer_inf_eq_bot_of_normal {C : Type*} [Group C] [Finite (MulAut C)]
    {η : MulAut C} (hη2 : η ^ 2 = 1) {N H : Subgroup (MulAut C)} (hNI : N ≤ inner C)
    (hIH : inner C ≤ H) (hNη : N ≤ Subgroup.centralizer {η})
    (hNnorm : (N.subgroupOf (Subgroup.centralizer {η})).Normal) (hNcore : CFSG.oddCore N = ⊥)
    (hcent : ∀ x ∈ Subgroup.centralizer {η}, x ∈ Subgroup.centralizer (N : Set (MulAut C)) →
      x ∈ Subgroup.zpowers η) :
    CFSG.oddCore ↥(Subgroup.centralizer {η} ⊓ H) = ⊥ := by
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer (R := N) ?_ ?_ hNcore ?_
  · exact fun n hn => Subgroup.mem_inf.2 ⟨hNη hn, hIH (hNI hn)⟩
  · intro c hc n hn
    have h := hNnorm.conj_mem ⟨n, hNη hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨c, (Subgroup.mem_inf.1 hc).1⟩
    exact Subgroup.mem_subgroupOf.1 h
  · intro c hc hcN
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hcent c (Subgroup.mem_inf.1 hc).1
      (Subgroup.mem_centralizer_iff.2 fun n hn => (hcN n hn).symm))
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat, zpow_two,
      ← pow_two, hη2, one_zpow]

theorem even_F4_outer_involution_full_centralizer_odd_core
    {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup ReeTag.F4.tag K)))
    (hIH : inner (adjointGroup ReeTag.F4.tag K) ≤ H) {α : MulAut (adjointGroup ReeTag.F4.tag K)}
    (hαI : α ∉ inner (adjointGroup ReeTag.F4.tag K)) (hα : orderOf α = 2) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have : Finite (adjointGroup ReeTag.F4.tag K) := generated_group_finite ReeTag.F4.tag K
  have : Finite (MulAut (adjointGroup ReeTag.F4.tag K)) :=
    Finite.of_injective (fun β : MulAut (adjointGroup ReeTag.F4.tag K) =>
      (β : adjointGroup ReeTag.F4.tag K → adjointGroup ReeTag.F4.tag K))
      fun _ _ h => MulEquiv.ext (congrFun h)
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨ψ, hψ, -, -, -, -, -, hH⟩ := even_F4_all_outer_involutions_canonical hf K hK α hα2 hαI
  obtain ⟨hIH', -, eH, -⟩ := hH H hIH
  have hη2 : (ReeTag.F4.finiteExceptionalAut K ^ f) ^ 2 = 1 := by
    rw [← hψ, show ψ * α * ψ⁻¹ = MulAut.conj ψ α from rfl, ← map_pow, hα2, map_one]
  have key : CFSG.oddCore ↥(Subgroup.centralizer {ReeTag.F4.finiteExceptionalAut K ^ f} ⊓
      H.map (MulAut.conj ψ).toMonoidHom) = ⊥ := by
    rcases Nat.even_or_odd f with ⟨e, he⟩ | ⟨m, hm⟩
    ·
      have he1 : 1 ≤ e := by omega
      have hf2 : f = 2 * e := by omega
      obtain ⟨φ₀, hφ₀, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
          Nat.prime_two hf hK
      have hσ : ∀ c, (φ₀ ^ e) c = c ^ 2 ^ e := ringAut_pow_apply_of_frobenius hφ₀ e
      have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, hf2]
      obtain ⟨-, -, -, -, hJC, -, ⟨hJfin, hJsimple, hJeven, -⟩, ⟨ι, -⟩, -, -, hNδ, hNnorm,
        hcent⟩ := even_F4_canonical_field_full_centralizer he1 K hK' (φ₀ ^ e) hσ
      rw [hf2] at hη2 ⊢
      have hNcore : CFSG.oddCore (((fixedFieldImage ReeTag.F4.tag (φ₀ ^ e)).subgroupOf
          (adjointGroup ReeTag.F4.tag K)).map MulAut.conj) = ⊥ := by
        have hJcore := @EvenCatalog.oddCore_eq_bot_of_isSimpleGroup _ _ hJfin hJsimple hJeven
        exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
          ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans ι) hJcore
      refine oddCore_centralizer_inf_eq_bot_of_normal hη2 ?_ hIH' hNδ hNnorm hNcore
        fun x hx hxN => ?_
      · rintro _ ⟨j, -, rfl⟩
        exact ⟨j, rfl⟩
      · rw [← hcent]
        exact Subgroup.mem_inf.2 ⟨hx, hxN⟩
    ·
      have hK' : Nat.card K = 2 ^ (2 * m + 1) := by rw [hK, hm]
      obtain ⟨-, -, -, hNcore, -, hNη, hNnorm, hcent⟩ :=
        ReeTag.even_F4_canonical_exceptional_full_centralizer m K hK'
      rw [hm] at hη2 ⊢
      refine oddCore_centralizer_inf_eq_bot_of_normal hη2 ?_ hIH' hNη hNnorm hNcore
        fun x hx hxN => ?_
      · rintro _ ⟨j, -, rfl⟩
        exact ⟨j, rfl⟩
      · rw [← hcent]
        exact Subgroup.mem_inf.2 ⟨hxN, hx⟩
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    ((MulEquiv.subgroupCongr (inf_comm H (Subgroup.centralizer {α}))).trans eH).symm key

end CFSG.LieType.Chevalley
