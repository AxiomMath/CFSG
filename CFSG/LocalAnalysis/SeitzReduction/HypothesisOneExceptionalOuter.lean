module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalBasic
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag (reeFixedEquivReeGamma large_Ree_fixed_group_center_trivial)
open CFSG.LieType.Simplicity
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem abelianNormalCardLeTwo_entrywiseAdjointAut_E7_E8
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ (2 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (H : Subgroup (MulAut (adjointGroup τ K))) (hIH : inner (adjointGroup τ K) ≤ H)
    (hσI : entrywiseAdjointAut τ σ ∉ inner (adjointGroup τ K)) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer {entrywiseAdjointAut τ σ}) := by
  obtain ⟨-, -, hJC, -, ⟨-, hJsimple, -, -, -⟩, ⟨ι, -⟩, -, -, hNδ, hNnorm, hcent⟩ :=
    even_E7_E8_canonical_field_full_centralizer τ hτ he K hK σ hσ
  have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * e / 2) := fun c => by
    rw [hσ, show 2 * e / 2 = e by omega]
  obtain ⟨hσσ, -, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_zpowers_of_forall_fixed
      (by omega) ⟨e, two_mul e⟩ hK hσ'
  have hδ2 : entrywiseAdjointAut τ σ ^ 2 = 1 := by
    rw [pow_two, ← entrywiseAdjointAut_mul, hσσ, entrywiseAdjointAut_one]
  have : IsSimpleGroup ↥(((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map
      MulAut.conj) := ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans ι).symm.isSimpleGroup
  refine abelianNormalCardLeTwo_of_isSimpleGroup hδ2 ?_ hNδ ?_ ?_ ?_
  · rintro _ ⟨j, -, rfl⟩
    exact hIH ⟨j, rfl⟩
  · rintro ⟨j, -, hj⟩
    exact hσI ⟨j, hj⟩
  · intro c hc n hn
    exact mem_subgroupOf.1 (hNnorm.conj_mem ⟨n, hNδ hn⟩ (mem_subgroupOf.2 hn) ⟨c, hc⟩)
  · intro c hc hcN
    rw [← hcent]
    exact mem_inf.2 ⟨hc, mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩

theorem even_E7_E8_outer_involution_abelianNormalCardLeTwo
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (H : Subgroup (MulAut (adjointGroup τ K)))
    (hIH : inner (adjointGroup τ K) ≤ H) {α : MulAut (adjointGroup τ K)}
    (hαI : α ∉ inner (adjointGroup τ K)) (hα : orderOf α = 2) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer {α}) := by
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
  have hΘα : Θ α = σ := hΘ α g σ hgσ
  have hσ1 : Θ α ≠ 1 := fun h1 => hαI (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨e, he⟩, hσc⟩ := (hinv α hα2).resolve_left hσ1
  rw [hΘα] at hσc
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show f / 2 = e by omega]
  obtain ⟨hQ1, -⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
  obtain ⟨β, -, hdesc⟩ := hQ1 τ
  obtain ⟨-, hdα⟩ := hdesc g fun _ => 1
  have hαform : ∀ u, (α u : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ (fun _ => 1) *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL τ K) * (rootDiagUnit τ fun _ => 1)⁻¹ *
        (g : ModGL τ K)⁻¹ := by
    intro u
    rw [show (fun _ => (1 : Kˣ)) = (1 : Fin τ.rank → Kˣ) from rfl, rootDiagUnit_one, mul_one,
      inv_one, mul_one]
    exact hgσ u
  obtain ⟨ψ, hψ, -⟩ := hdα α hαform (by rw [← pow_two]; exact hα2)
  have hψα : ψ * α * ψ⁻¹ = entrywiseAdjointAut τ σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hψ u, coe_entrywiseAdjointAut])
  have hσI : entrywiseAdjointAut τ σ ∉ inner (adjointGroup τ K) := fun h => hαI (by
    have := (inner_normal _).conj_mem _ h ψ⁻¹
    rwa [← hψα, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this)
  exact AbelianNormalCardLeTwo.of_conj hψα
    (abelianNormalCardLeTwo_entrywiseAdjointAut_E7_E8 τ hτ he1 K hK' σ hσ' _
      (inner_le_map_conj_of_le hIH ψ) hσI)

theorem reeFixed_F4_noAbelianNormal
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m + 1)) : NoAbelianNormal (reeFixed ReeTag.F4 K m) := by
  intro M hM hab
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    have hK2 : Nat.card K = 2 := by simpa using hK
    set T := titsData K hK2
    rcases T.le_of_normal hK2 M with h | h
    · exact h
    · exfalso
      have hD := (T.isQuasisimple hK2).1
      have hcomm : commutator (commutator (reeFixed ReeTag.F4 K 0)) = ⊥ := by
        change ⁅(⊤ : Subgroup (commutator (reeFixed ReeTag.F4 K 0))), ⊤⁆ = ⊥
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [mem_centralizer_iff]
        intro y _
        exact Subtype.ext (hab _ (h y.2) _ (h x.2))
      have hg : (⟨T.g₀, T.g₀_mem⟩ : commutator (reeFixed ReeTag.F4 K 0)) ∈
          (⊥ : Subgroup (commutator (reeFixed ReeTag.F4 K 0))) := by
        rw [← hcomm, hD.commutator_eq_top]
        exact mem_top _
      exact T.g₀_ne_one (congrArg Subtype.val (mem_bot.1 hg))
  ·
    have hperf : Group.IsPerfect (reeFixed ReeTag.F4 K m) := ⟨commutator_reeFixed_F4 m hm hK⟩
    have hB := isSolvable_reeBorelPart (t := ReeTag.F4) (K := K) m
    have hgen : normalClosure (reeUnipPart ReeTag.F4 K m : Set (reeFixed ReeTag.F4 K m)) = ⊤ :=
      CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf hB
        (sup_reeBorelPart_eq_top_F4 _ (not_normalClosure_le_reeBorelPart m))
    by_cases hMB : M ≤ reeBorelPart ReeTag.F4 K m
    ·
      have hcen := le_center_of_le_reeBorelPart hgen M hMB
      rw [eq_bot_iff]
      intro x hx
      have hex : reeFixedEquivReeGamma K m x ∈ center (ReeTag.F4.reeGamma K m) := by
        refine mem_center_iff.2 fun z => ?_
        obtain ⟨w, rfl⟩ := (reeFixedEquivReeGamma K m).surjective z
        rw [← map_mul, ← map_mul, (mem_center_iff.1 (hcen hx)) w]
      rw [large_Ree_fixed_group_center_trivial m K hK, mem_bot] at hex
      rw [mem_bot]
      exact (reeFixedEquivReeGamma K m).injective (hex.trans (map_one _).symm)
    ·
      exfalso
      have htop := CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf hB
        (sup_reeBorelPart_eq_top_F4 M hMB)
      have := nontrivial_reeFixed (t := ReeTag.F4) (K := K) m
      have hcomm : commutator (reeFixed ReeTag.F4 K m) = ⊥ := by
        change ⁅(⊤ : Subgroup (reeFixed ReeTag.F4 K m)), ⊤⁆ = ⊥
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [mem_centralizer_iff]
        intro y _
        exact hab _ (htop ▸ mem_top y) _ (htop ▸ mem_top x)
      rw [hperf.commutator_eq_top] at hcomm
      exact top_ne_bot hcomm

theorem even_F4_outer_involution_abelianNormalCardLeTwo
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (MulAut (adjointGroup ReeTag.F4.tag K)))
    (hIH : inner (adjointGroup ReeTag.F4.tag K) ≤ H) {α : MulAut (adjointGroup ReeTag.F4.tag K)}
    (hαI : α ∉ inner (adjointGroup ReeTag.F4.tag K)) (hα : orderOf α = 2) :
    AbelianNormalCardLeTwo ↥(H ⊓ centralizer {α}) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have hα2 : α ^ 2 = 1 := by
    rw [← hα]
    exact pow_orderOf_eq_one α
  obtain ⟨ψ, hψ, -, -, -, -, -, -⟩ := even_F4_all_outer_involutions_canonical hf K hK α hα2 hαI
  have hη2 : (ReeTag.F4.finiteExceptionalAut K ^ f) ^ 2 = 1 := by
    rw [← hψ, show ψ * α * ψ⁻¹ = MulAut.conj ψ α from rfl, ← map_pow, hα2, map_one]
  have hηI : ReeTag.F4.finiteExceptionalAut K ^ f ∉ inner (adjointGroup ReeTag.F4.tag K) :=
    fun h => hαI (by
      have := (inner_normal _).conj_mem _ h ψ⁻¹
      rwa [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this)
  refine AbelianNormalCardLeTwo.of_conj hψ ?_
  have hIH' := inner_le_map_conj_of_le hIH ψ
  rcases Nat.even_or_odd f with ⟨e, he⟩ | ⟨m, hm⟩
  ·
    have he1 : 1 ≤ e := by omega
    have hf2 : f = 2 * e := by omega
    obtain ⟨φ₀, hφ₀, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    have hσ : ∀ c, (φ₀ ^ e) c = c ^ 2 ^ e := ringAut_pow_apply_of_frobenius hφ₀ e
    have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, hf2]
    obtain ⟨-, -, -, -, hJC, -, ⟨-, hJsimple, -, -⟩, ⟨ι, -⟩, -, -, hNδ, hNnorm, hcent⟩ :=
      even_F4_canonical_field_full_centralizer he1 K hK' (φ₀ ^ e) hσ
    rw [hf2] at hη2 hηI ⊢
    have : IsSimpleGroup ↥(((fixedFieldImage ReeTag.F4.tag (φ₀ ^ e)).subgroupOf
        (adjointGroup ReeTag.F4.tag K)).map MulAut.conj) :=
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans ι).symm.isSimpleGroup
    refine abelianNormalCardLeTwo_of_isSimpleGroup hη2 ?_ hNδ ?_ ?_ ?_
    · rintro _ ⟨j, -, rfl⟩
      exact hIH' ⟨j, rfl⟩
    · rintro ⟨j, -, hj⟩
      exact hηI ⟨j, hj⟩
    · intro c hc n hn
      exact mem_subgroupOf.1 (hNnorm.conj_mem ⟨n, hNδ hn⟩ (mem_subgroupOf.2 hn) ⟨c, hc⟩)
    · intro c hc hcN
      rw [← hcent]
      exact mem_inf.2 ⟨hc, mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩
  ·
    have hK' : Nat.card K = 2 ^ (2 * m + 1) := by rw [hK, hm]
    obtain ⟨-, hΓ, ⟨eΓ, -⟩, -, -, hNη, hNnorm, hcent⟩ :=
      CFSG.LieType.Ree.ReeTag.even_F4_canonical_exceptional_full_centralizer m K hK'
    rw [hm] at hη2 ⊢
    have hNab : NoAbelianNormal ↥((ReeTag.F4.finiteReeFixedGroup K m).map
        (MulAut.conj : adjointGroup ReeTag.F4.tag K →* MulAut (adjointGroup ReeTag.F4.tag K))) :=
      (reeFixed_F4_noAbelianNormal hK').of_mulEquiv
        ((reeFixedEquivReeGamma K m).trans ((MulEquiv.subgroupCongr hΓ).symm.trans
          (((ReeTag.F4.finiteReeFixedGroup K m).equivMapOfInjective
            (adjointGroup ReeTag.F4.tag K).subtype Subtype.val_injective).symm.trans eΓ)))
    refine abelianNormalCardLeTwo_of_normal_of_centralizer hη2 ?_ hNη ?_ hNab ?_
    · rintro _ ⟨j, -, rfl⟩
      exact hIH' ⟨j, rfl⟩
    · intro c hc n hn
      exact mem_subgroupOf.1 (hNnorm.conj_mem ⟨n, hNη hn⟩ (mem_subgroupOf.2 hn) ⟨c, hc⟩)
    · intro c hc hcN
      rw [← hcent]
      exact mem_inf.2 ⟨mem_centralizer_iff.2 fun n hn => (hcN n hn).symm, hc⟩

end CFSG.SeitzReduction
