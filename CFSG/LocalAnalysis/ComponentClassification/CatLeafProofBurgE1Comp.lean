module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Torus
public import CFSG.LieType.HighestRoot.CentChevalleyCenter
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleNotTwoGroupQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification

variable {τ : Tag} {K : Type} [Field K]

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {S : Subgroup G} {x : G} {n : ℕ}
    (hn : Nat.Coprime n (orderOf x)) (hx : x ^ n ∈ S) : x ∈ S := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hn
  rw [← hm]
  exact pow_mem hx m

theorem le_center_of_odd_normal_of_isQuasisimple
    {G : Type*} [Group G] [Finite G]
    (hq : CFSG.IsQuasisimple G) (D : Subgroup G) [hD : D.Normal]
    (hodd : Nat.Coprime 2 (Nat.card D)) : D ≤ center G := by
  have hq' : CFSG.GorensteinWalter.IsQuasisimple G := by
    have : Nontrivial (G ⧸ center G) := hq.2.1.toNontrivial
    exact ⟨(QuotientGroup.mk'_surjective (center G)).nontrivial,
      Group.isPerfect_def.mp hq.1, hq.2.1⟩
  exact (le_sSup ⟨hD, hodd⟩ : D ≤ pPrimeCore 2 G).trans
    (CFSG.GorensteinWalter.pPrimeCore_le_center_of_isQuasisimple hq')

theorem le_center_of_odd_normal_of_mulEquiv_SL2
    [Finite K] (hK : ringChar K ≠ 2) {G : Type*} [Group G]
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) K) (D : Subgroup G) [hD : D.Normal]
    (hodd : Nat.Coprime 2 (Nat.card D)) : D ≤ center G := by
  have : Fintype K := Fintype.ofFinite K
  have hKodd : Nat.card K % 2 = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.odd_card_of_char_ne_two hK
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  rcases (show Nat.card K = 3 ∨ 5 ≤ Nat.card K by omega) with h3 | h5
  · by_contra hc
    have h8 := CFSG.LieType.HighestRoot.eight_le_card_of_normal h3 e D hc
    have h24 := CFSG.LieType.HighestRoot.card_eq_24 h3 e
    have : Finite G := Nat.finite_of_card_ne_zero (by rw [h24]; norm_num)
    have hdvd : Nat.card D ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card D
    have h3' : Nat.card D ∣ 3 := by
      have hc8 : Nat.Coprime (Nat.card D) 8 :=
        Nat.Coprime.pow_right 3 (Nat.coprime_comm.1 hodd)
      exact hc8.dvd_of_dvd_mul_left (by simpa using hdvd)
    have := Nat.le_of_dvd (by norm_num) h3'
    omega
  · have hq : CFSG.IsQuasisimple G :=
      (isQuasisimple_congr e).2 (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl
        (Or.inr (by omega)) (Or.inr (by omega)))
    have : Finite G := Finite.of_equiv _ e.toEquiv.symm
    exact le_center_of_odd_normal_of_isQuasisimple hq D hodd

theorem le_center_of_odd_normal_componentRootSpan
    [Finite K] (hK : ringChar K ≠ 2) (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (i : KernelComponent χ) (D : Subgroup (componentRootSpan K χ i)) [D.Normal]
    (hodd : Nat.Coprime 2 (Nat.card D)) : D ≤ center (componentRootSpan K χ i) := by
  have : Finite (ModGL τ K) := finite_modGL
  by_cases h2 : 2 < (componentRoots χ i).ncard
  · exact le_center_of_odd_normal_of_isQuasisimple
      ((odd_sign_root_component_quasisimple τ K χ i).2.2 hK h2) D hodd
  · obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
    have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
    have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
    have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots χ ⟦⟨α, hα⟩⟧ :=
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
      rw [heq, rootSpan, iSup_insert, iSup_singleton]
    obtain ⟨-, ⟨e₀⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK (hΨ.isRoot α hαΨ)
    exact le_center_of_odd_normal_of_mulEquiv_SL2 hK
      ((MulEquiv.subgroupCongr hS).trans e₀.symm) D hodd

theorem sq_eq_one_of_mem_center_componentRootSpan
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (h2 : ∀ j : Fin τ.rank,
      (2 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ AddSubgroup.closure (kernelRoots χ))
    {i : KernelComponent χ} {z : componentRootSpan K χ i}
    (hz : z ∈ center (componentRootSpan K χ i)) : (z : ModGL τ K) ^ 2 = 1 := by
  classical
  obtain ⟨-, -, hcomm, -, -, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  have hzT : (z : ModGL τ K) ∈ torusGroup τ K :=
    componentTorus_le_torusGroup K χ i
      (CFSG.LieType.HighestRoot.coe_mem_componentTorus_of_mem_center hz)
  refine sq_eq_one_of_commute_pinnedX (fun α hα => hα.1) h2 hzT fun α hα c => ?_
  have hmem : pinnedX τ K α c ∈ componentRootSpan K χ ⟦⟨α, hα⟩⟧ :=
    (le_iSup₂ (f := fun β (_ : β ∈ componentRoots χ ⟦⟨α, hα⟩⟧) => rootSubgroup τ K β) α
      ⟨hα, rfl⟩) (Subgroup.subset_closure ⟨c, rfl⟩)
  by_cases hi : (⟦⟨α, hα⟩⟧ : KernelComponent χ) = i
  · subst hi
    have := (Subgroup.mem_center_iff.1 hz) ⟨_, hmem⟩
    exact (congrArg Subtype.val this).symm
  · have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i _ (Ne.symm hi))
    exact ((Subgroup.mem_centralizer_iff.1 (hc z.2)) _ hmem).symm

theorem sq_eq_one_of_commute_componentRootSpan
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (h2 : ∀ j : Fin τ.rank,
      (2 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ AddSubgroup.closure (kernelRoots χ))
    {n : ModGL τ K} (hn : n ∈ rootSpan τ K (kernelRoots χ))
    (hc : ∀ i, ∀ s ∈ componentRootSpan K χ i, n * s = s * n) : n ^ 2 = 1 := by
  classical
  obtain ⟨-, -, -, -, ⟨μ, hμ1, hμs, -⟩, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  obtain ⟨f, hf⟩ := hμs ⟨n, hn⟩
  have hμ : ∀ g, (μ g : ModGL τ K) = ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) :=
    fun _ => rfl
  have hfc : ∀ i, f i ∈ center (componentRootSpan K χ i) := by
    intro i
    rw [Subgroup.mem_center_iff]
    intro x
    set g := f * (Pi.mulSingle i (f i))⁻¹ with hg_def
    have hg : g * Pi.mulSingle i x = Pi.mulSingle i x * g := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hg_def]
      · simp [hg_def, Pi.mulSingle_eq_of_ne hj]
    have hfg : f = g * Pi.mulSingle i (f i) := by
      rw [hg_def, inv_mul_cancel_right]
    have e1 : (μ g : ModGL τ K) * x = x * μ g := by
      have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hg
      simpa only [map_mul, Subgroup.coe_mul, hμ1] using h1
    have e3 : n = (μ g : ModGL τ K) * (f i : ModGL τ K) := by
      have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hfg
      simp only [map_mul, Subgroup.coe_mul, hμ1, hf] at h1
      exact h1
    have e2 : n * x = x * n := hc i x x.2
    rw [e3] at e2
    refine Subtype.ext ?_
    change (x : ModGL τ K) * f i = f i * x
    have e4 : (μ g : ModGL τ K) * (f i * x) = (μ g : ModGL τ K) * (x * f i) := by
      calc (μ g : ModGL τ K) * (f i * x) = (μ g : ModGL τ K) * f i * x := by group
        _ = x * ((μ g : ModGL τ K) * f i) := e2
        _ = (μ g : ModGL τ K) * (x * f i) := by rw [← mul_assoc, ← e1, mul_assoc]
    exact (mul_left_cancel e4).symm
  have hff : f ^ 2 = 1 := by
    funext i
    refine Subtype.ext ?_
    rw [Pi.pow_apply, Pi.one_apply, Subgroup.coe_pow, Subgroup.coe_one]
    exact sq_eq_one_of_mem_center_componentRootSpan h2 (hfc i)
  have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hff
  simpa only [map_pow, map_one, hf, Subgroup.coe_pow, Subgroup.coe_one] using h1

end CFSG.ComponentClassification.CatLeafProof
