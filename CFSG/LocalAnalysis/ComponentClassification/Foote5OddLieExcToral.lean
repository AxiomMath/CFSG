module

public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank

variable {τ : Tag} {K : Type} [Field K]

theorem gw_isQuasisimple_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    GorensteinWalter.IsQuasisimple Q := by
  obtain ⟨hperf, hs, a, b, hab⟩ := h
  refine ⟨?_, hperf.commutator_eq_top, hs⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [@Subsingleton.elim _ hnt x y]

theorem isSubnormal_subgroupOf_of_conj {G : Type*} [Group G] {E A T : Subgroup G}
    (hEA : E ≤ A) (hAn : ∀ t ∈ T, ∀ a ∈ A, t * a * t⁻¹ ∈ A)
    (hEn : ∀ a ∈ A, a ∈ T → ∀ e ∈ E, a * e * a⁻¹ ∈ E) : (E.subgroupOf T).IsSubnormal := by
  have hle : E.subgroupOf T ≤ (A ⊓ T).subgroupOf T := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hEA (Subgroup.mem_subgroupOf.1 hx), x.2⟩)
  have hAT : ((A ⊓ T).subgroupOf T).Normal := ⟨fun n hn g =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hAn g g.2 n
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hn)).1, (g * n * g⁻¹).2⟩)⟩
  refine Subgroup.IsSubnormal.step _ _ hle hAT.isSubnormal ⟨fun n hn g => ?_⟩
  have hg := Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 g.2)
  exact hEn _ hg.1 hg.2 _ hn

@[expose] def ClosedRoots (S : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → IsRoot τ (m • α + n • β) → m • α + n • β ∈ S

theorem closedRoots_pos : ClosedRoots {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} := by
  intro α hα β hβ m n hm hn hmn
  refine ⟨hmn, ?_⟩
  rw [height_nsmul_add_nsmul]
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
  nlinarith [hα.2, hβ.2]

theorem closedRoots_inter {a : Fin τ.rank → Kˣ} {S : Set (Fin τ.rank → ℤ)} (hS : ClosedRoots S) :
    ClosedRoots (rootCharKernel a ∩ S) := by
  intro α hα β hβ m n hm hn hr
  refine ⟨⟨hr, ?_⟩, hS α hα.2 β hβ.2 m n hm hn hr⟩
  rw [rootChar_add, ← Nat.cast_smul_eq_nsmul ℤ m α, ← Nat.cast_smul_eq_nsmul ℤ n β,
    rootChar_zsmul, rootChar_zsmul, hα.1.2, hβ.1.2, one_zpow, one_zpow, one_mul]

theorem closedRoots_inversionSet (w : WeylGroup τ) : ClosedRoots (inversionSet w) :=
  inversionSet_closed w

theorem mem_rootSpan_inter_of_conj_eq'
    {a : Fin τ.rank → Kˣ} {S : Set (Fin τ.rank → ℤ)}
    (hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α) (hScl : ClosedRoots S) {u : ModGL τ K}
    (hu : u ∈ rootSpan τ K S) (hfix : rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u) :
    u ∈ rootSpan τ K (rootCharKernel a ∩ S) := by
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun α hα => (hSpos α hα).1
  exact mem_rootSpan_inter_of_conj_eq a hfin (fun α hα => (hSpos α hα).1)
    (fun α hα hrange => bijOn_prod_pinnedX K hSpos hScl α hα hrange) hu hfix

theorem rootSpan_empty :
    rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by
  simp [rootSpan]

theorem eq_one_of_conj_rootDiagUnit_eq
    {S : Set (Fin τ.rank → ℤ)} (hSpos : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hScl : ClosedRoots S) {u : ModGL τ K} (hu : u ∈ rootSpan τ K S)
    (A : (Fin τ.rank → ℤ) → Fin τ.rank → Kˣ)
    (hA : ∀ β ∈ S, rootDiagUnit τ (A β) * u * (rootDiagUnit τ (A β))⁻¹ = u)
    (hAβ : ∀ β ∈ S, rootChar (A β) β ≠ 1) : u = 1 := by
  have hfin : ∀ S' ⊆ S, S'.Finite := fun S' hS' =>
    (finite_setOf_isRoot τ).subset fun α hα => (hSpos α (hS' hα)).1
  suffices h : ∀ n : ℕ, ∀ S' ⊆ S, S'.ncard ≤ n → ClosedRoots S' → u ∈ rootSpan τ K S' → u = 1
    from h _ S le_rfl le_rfl hScl hu
  intro n
  induction n with
  | zero =>
    intro S' hS' hcard _ hu'
    have hS'0 : S' = ∅ := (Set.ncard_eq_zero (hfin S' hS')).1 (Nat.le_zero.1 hcard)
    rw [hS'0, rootSpan_empty, Subgroup.mem_bot] at hu'
    exact hu'
  | succ n ih =>
    intro S' hS' hcard hcl hu'
    rcases S'.eq_empty_or_nonempty with h0 | ⟨β, hβ⟩
    · rw [h0, rootSpan_empty, Subgroup.mem_bot] at hu'
      exact hu'
    · have hu'' := mem_rootSpan_inter_of_conj_eq' (fun α hα => hSpos α (hS' hα)) hcl hu'
        (hA β (hS' hβ))
      have hss : rootCharKernel (A β) ∩ S' ⊂ S' :=
        ⟨Set.inter_subset_right, fun h => hAβ β (hS' hβ) (h hβ).1.2⟩
      have hlt := Set.ncard_lt_ncard hss (hfin S' hS')
      exact ih (rootCharKernel (A β) ∩ S') (Set.inter_subset_right.trans hS') (by omega)
        (closedRoots_inter hcl) hu''

theorem commute_rootSL2_of_commute
    {x : ModGL τ K} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hp : ∀ t, x * pinnedX τ K β t = pinnedX τ K β t * x)
    (hn : ∀ t, x * pinnedX τ K (-β) t = pinnedX τ K (-β) t * x) (A : SL2 K) :
    x * rootSL2 τ K β A = rootSL2 τ K β A * x := by
  obtain ⟨ε, -, hv⟩ := exists_rootSL2_vSL_eq (K := K) hβ
  have hle : (⊤ : Subgroup (SL2 K)) ≤
      (Subgroup.centralizer ({x} : Set (ModGL τ K))).comap (rootSL2 τ K β) := by
    rw [← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) <;>
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    · rw [show sl2Upper K t = uSL t from rfl, rootSL2_uSL_eq]
      exact (hp _).symm
    · rw [show sl2Lower K t = vSL t from rfl, hv]
      exact (hn _).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top A))).symm

theorem exists_mem_rootCharKernel
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hτ : ∃ i k : Fin τ.rank, τ.cartan i k = -1) : ∃ β, β ∈ rootCharKernel c := by
  by_cases h : ∃ i, c i = 1
  · obtain ⟨i, hi⟩ := h
    exact ⟨Pi.single i 1, isRoot_single τ i, by
      rw [show (Pi.single i 1 : Fin τ.rank → ℤ) = (1 : ℕ) • Pi.single i 1 by rw [one_smul],
        rootChar_nsmul_single, pow_one, hi]⟩
  · push Not at h
    obtain ⟨i, k, hik⟩ := hτ
    have hc' : ∀ j, c j = -1 := fun j => (hc j).resolve_left (h j)
    refine ⟨Pi.single k 1 + Pi.single i 1,
      CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single hik, ?_⟩
    rw [rootChar_add, show (Pi.single k 1 : Fin τ.rank → ℤ) = (1 : ℕ) • Pi.single k 1 by
      rw [one_smul], show (Pi.single i 1 : Fin τ.rank → ℤ) = (1 : ℕ) • Pi.single i 1 by
      rw [one_smul], rootChar_nsmul_single, rootChar_nsmul_single, pow_one, pow_one, hc', hc',
      neg_one_mul, neg_neg]

theorem neg_mem_rootCharKernel {c : Fin τ.rank → Kˣ} {β : Fin τ.rank → ℤ}
    (hβ : β ∈ rootCharKernel c) : -β ∈ rootCharKernel c := by
  refine ⟨IsRoot.neg hβ.1, ?_⟩
  rw [← neg_one_smul ℤ β, rootChar_zsmul, hβ.2, one_zpow]

theorem eq_of_pinnedX_eq_pinnedX_of_pos'
    {δ γ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hγ : IsRoot τ γ) (hγp : 0 < height γ) {d e : K}
    (he : e ≠ 0) (h : pinnedX τ K δ d = pinnedX τ K γ e) : δ = γ := by
  by_contra hne
  rcases IsRoot.height_pos_or_neg hδ with hpos | hneg
  · have hL := pinnedX_list_prod_injective (R := K) [δ, γ]
      (by simpa using hne)
      (by
        intro α hα
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
        rcases hα with rfl | rfl
        · exact ⟨hδ, hpos⟩
        · exact ⟨hγ, hγp⟩)
      (fun α => if α = δ then d else 0)
      (fun α => if α = γ then e else 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hne,
          Ne.symm hne, ↓reduceIte, pinnedX_zero, one_mul]
        exact h)
      γ (by simp)
    simp only [Ne.symm hne, ↓reduceIte] at hL
    exact he hL.symm
  · have hneg' : pinnedX τ K δ d ∈ negUnipotent τ K :=
      pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ height α < 0}) ⟨hδ, hneg⟩ d
    have hB : pinnedX τ K δ d ∈ borelGroup τ K := by
      rw [h]
      exact Subgroup.mem_sup_right
        (pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α}) ⟨hγ, hγp⟩ e)
    have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
    rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, h] at h0
    exact he (pinnedX_injective τ K _ (h0.trans (pinnedX_zero τ K _).symm))

theorem componentRootSpan_quasisimple
    [Finite K] (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  induction i using Quotient.inductionOn with
  | h a =>
  obtain ⟨α, hα⟩ := a
  have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  by_cases h2 : 2 < (componentRoots χ ⟦⟨α, hα⟩⟧).ncard
  · exact (odd_sign_root_component_quasisimple τ K χ _).2.2 hK h2
  · have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots χ ⟦⟨α, hα⟩⟧ :=
      Set.insert_subset hαΨ (Set.singleton_subset_iff.2 (hΨ.neg_mem α hαΨ))
    have hfin : (componentRoots χ ⟦⟨α, hα⟩⟧).Finite :=
      (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
    have hne : α ≠ -α := fun h => (hΨ.isRoot α hαΨ).ne_zero (funext fun j => by
      have := congrFun h j
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega)
    have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
    have heq : componentRoots χ ⟦⟨α, hα⟩⟧ = {α, -α} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; omega) hfin).symm
    have hS : componentRootSpan K χ ⟦⟨α, hα⟩⟧ = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
      change rootSpan τ K (componentRoots χ ⟦⟨α, hα⟩⟧) = _
      rw [heq, OddToralFixed.rootSpan_pair]
    obtain ⟨-, -, -, hfinK⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK
      (hΨ.isRoot α hαΨ)
    rw [hS]
    exact ((@hfinK inferInstance).2 hK5).1

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
