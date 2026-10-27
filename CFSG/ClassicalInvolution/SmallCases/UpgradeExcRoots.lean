module

public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution

variable {τ : Tag}

theorem sl2_neg_one_eq_HSL {K : Type} [Field K] : (-1 : SL2 K) = HSL (-1) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem ringChar_ne_two_of_odd_card {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K)) :
    ringChar K ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  intro h2
  have := FiniteField.even_card_iff_char_two.mp h2
  rw [Nat.card_eq_fintype_card] at hK
  obtain ⟨k, hk⟩ := hK
  omega

theorem act_rootVec_of_involution {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    {s : ModGL τ K} (hs : s ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ))
    (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    (s : Module.End K (RootModule τ K)) (rootVec τ K δ) =
      (((-1 : Kˣ) ^ corootPair γ δ : Kˣ) : K) • rootVec τ K δ := by
  have hring : ringChar K ≠ 2 := ringChar_ne_two_of_odd_card hK
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hγ
  obtain ⟨e, he⟩ := exists_mulEquiv_rootSubgroup_sup hring hw
  subst hw
  obtain ⟨x, hxdef⟩ : ∃ x, e x = ⟨s, hs⟩ := ⟨e.symm ⟨s, hs⟩, by simp⟩
  have hxx : x * x = 1 := by
    apply e.injective
    rw [map_mul, hxdef, map_one]
    apply Subtype.ext
    exact hs2
  have hx1 : x ≠ 1 := by
    intro h1
    apply hs1
    rw [h1, map_one] at hxdef
    exact congrArg Subtype.val hxdef.symm
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hxneg : x = -1 := (sl2_orderOf_eq_two_iff hK x).mp hx2
  set n := canonicalRep (coxeterSystem τ) K w with hn_def
  have hsval : s = n * torusElt τ K j (-1) * n⁻¹ := by
    have h1 := he x
    rw [hxdef, hxneg, sl2_neg_one_eq_HSL, simpleRootSL2_HSL] at h1
    exact h1
  have hn := mapsRootLines_canonicalRep (τ := τ) (R := K) w
  have hu : IsRoot τ (w⁻¹ • δ) := IsRoot.smul hδ w⁻¹
  obtain ⟨c₁, hc₁⟩ := hn.inv δ hδ
  obtain ⟨c₂, hc₂⟩ := hn (w⁻¹ • δ) hu
  rw [smul_inv_smul] at hc₂
  have hd := torusElt_rootVec (τ := τ) (R := K) j (-1) hu
  have hv0 : rootVec τ K δ ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hδ]
    exact Finsupp.single_ne_zero.mpr one_ne_zero
  have hnn : ((c₁ : K) * c₂) = 1 := by
    have h1 : (n : Module.End K (RootModule τ K)) (((n⁻¹ : (Module.End K (RootModule τ K))ˣ) :
        Module.End K (RootModule τ K)) (rootVec τ K δ)) = rootVec τ K δ := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    rw [hc₁, map_smul, hc₂, smul_smul] at h1
    have h2 : ((c₁ : K) * c₂) • rootVec τ K δ = (1 : K) • rootVec τ K δ := by
      rw [h1, one_smul]
    exact smul_left_injective K hv0 h2
  rw [hsval, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hc₁,
    map_smul, hd, map_smul, map_smul, hc₂, smul_smul, smul_smul, corootPair_smul_single]
  congr 1
  linear_combination (((-1 : Kˣ) ^ (∑ k, τ.cartan j k * (w⁻¹ • δ) k) : Kˣ) : K) * hnn

theorem odd_corootPair_or_odd_corootPair {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h0 : iform γ δ ≠ 0) :
    Odd (corootPair γ δ) ∨ Odd (corootPair δ γ) := by
  have hγγ := iform_self_pos_of_isRoot hγ
  have hδδ := iform_self_pos_of_isRoot hδ
  have h1 := corootPair_mul hγ δ
  have h2 := corootPair_mul hδ γ
  rw [iform_comm δ γ] at h2
  have hcs := iform_sq_lt hγ hδ hne hne'
  set a := corootPair γ δ with ha
  set b := corootPair δ γ with hb
  set s := iform γ δ with hs
  set P := iform γ γ * iform δ δ with hP
  have hPpos : 0 < P := mul_pos hγγ hδδ
  have hab : (a * b) * P = 4 * s ^ 2 := by
    calc (a * b) * P = (a * iform γ γ) * (b * iform δ δ) := by rw [hP]; ring
      _ = 4 * s ^ 2 := by rw [h1, h2]; ring
  have hs2 : 0 < s ^ 2 := by positivity
  have hpos : 0 < a * b := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hlt : a * b < 4 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  by_contra hno
  push Not at hno
  have hae : Even a := by simpa using hno.1
  have hbe : Even b := by simpa using hno.2
  have h4 : 4 ∣ a * b := by
    have := mul_dvd_mul (even_iff_two_dvd.mp hae) (even_iff_two_dvd.mp hbe)
    simpa using this
  omega

theorem iform_neg_left_eq (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]
  ring

theorem exists_iform_ne_zero_of_not_subset {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ Ψ) (hsub : ¬ Ψ ⊆ {γ, -γ}) :
    ∃ δ ∈ Ψ, δ ≠ γ ∧ δ ≠ -γ ∧ iform γ δ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hS : ({γ, -γ} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hγ
    · exact hΨ.neg_mem _ hγ
  rcases hΨ.irreducible {γ, -γ} hS (by
    intro α hα β hβ hβS
    have hβ1 : β ≠ γ := fun h => hβS (Or.inl h)
    have hβ2 : β ≠ -γ := fun h => hβS (Or.inr h)
    rcases hα with rfl | rfl
    · exact hcon β hβ hβ1 hβ2
    · rw [iform_neg_left_eq, hcon β hβ hβ1 hβ2, neg_zero]) with h | h
  · exact (Set.mem_empty_iff_false γ).mp (h ▸ Or.inl rfl)
  · exact hsub (h ▸ Set.Subset.rfl)

theorem rootDiagUnit_act_rootVec {K : Type} [Field K] (b : Fin τ.rank → Kˣ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K β) =
      ((rootChar b β : Kˣ) : K) • rootVec τ K β := by
  rw [rootVec_eq_single_of_isRoot hβ]
  exact rootDiag_single_inr b ⟨β, hβ⟩

theorem exists_involution_mem_rootPair {K : Type} [Field K] [Finite K] (hK : Odd (Nat.card K))
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ s : ModGL τ K, s ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ∧ s * s = 1 ∧ s ≠ 1 := by
  have hring : ringChar K ≠ 2 := ringChar_ne_two_of_odd_card hK
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hγ
  obtain ⟨e, -⟩ := exists_mulEquiv_rootSubgroup_sup hring hw
  refine ⟨((e (-1) : ↥(rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ))) : ModGL τ K),
    (e (-1)).2, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul]
    have : (-1 : SL2 K) * (-1) = 1 := by simp
    rw [this, map_one]
    rfl
  · intro h1
    have h2 : e (-1) = 1 := Subtype.ext h1
    exact sl2_neg_one_ne_one hK (e.injective (h2.trans (map_one e).symm))

theorem not_two_lt_ncard_componentRoots {K : Type} [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (i : KernelComponent (maskChar (signTupleBits b)))
    (huniq : ∀ a ∈ componentRootSpan K (maskChar (signTupleBits b)) i, a * a = 1 → a ≠ 1 →
      a = rootDiagUnit τ b) :
    ¬ 2 < (componentRoots (maskChar (signTupleBits b)) i).ncard := by
  intro h2
  have hring := ringChar_ne_two_of_odd_card hK
  obtain ⟨⟨γ, hγk⟩, rfl⟩ := Quotient.exists_rep i
  have hΨ := isRootComponent_componentRoots (χ := maskChar (signTupleBits b)) ⟦⟨γ, hγk⟩⟧
  have hγΨ : γ ∈ componentRoots (maskChar (signTupleBits b)) ⟦⟨γ, hγk⟩⟧ := ⟨hγk, rfl⟩
  have key : ∀ α ∈ componentRoots (maskChar (signTupleBits b)) ⟦⟨γ, hγk⟩⟧,
      ∀ β ∈ componentRoots (maskChar (signTupleBits b)) ⟦⟨γ, hγk⟩⟧,
      Odd (corootPair α β) → False := by
    intro α hα β hβ hodd
    have hαr : IsRoot τ α := hΨ.isRoot α hα
    have hβr : IsRoot τ β := hΨ.isRoot β hβ
    obtain ⟨s, hsQ, hs2, hs1⟩ := exists_involution_mem_rootPair (K := K) hK hαr
    have hQle : rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ≤
        componentRootSpan K (maskChar (signTupleBits b)) ⟦⟨γ, hγk⟩⟧ := by
      obtain ⟨hαk, hαi⟩ := hα
      obtain ⟨hnk, hni⟩ := hΨ.neg_mem α ⟨hαk, hαi⟩
      refine sup_le ?_ ?_
      · have := rootSubgroup_le_componentRootSpan K ⟨α, hαk⟩
        rwa [hαi] at this
      · have := rootSubgroup_le_componentRootSpan K ⟨-α, hnk⟩
        rwa [hni] at this
    have hz : s = rootDiagUnit τ b := huniq s (hQle hsQ) hs2 hs1
    have h1 := act_rootVec_of_involution hK hαr hβr hsQ hs2 hs1
    have h3 := rootDiagUnit_act_rootVec (K := K) b hβr
    have hβker : β ∈ rootCharKernel b := by
      rw [rootCharKernel_eq_kernelRoots hring hb]
      exact hβ.1
    have hχ : rootChar b β = 1 := hβker.2
    rw [hz, h3, hχ, hodd.neg_one_zpow] at h1
    have hv0 : rootVec τ K β ≠ 0 := by
      rw [rootVec_eq_single_of_isRoot hβr]
      exact Finsupp.single_ne_zero.mpr one_ne_zero
    have h4 : ((1 : Kˣ) : K) = (((-1 : Kˣ)) : K) := smul_left_injective K hv0 h1
    have h5 : (2 : K) = 0 := by
      simp only [Units.val_one, Units.val_neg] at h4
      linear_combination h4
    exact Ring.two_ne_zero hring h5
  have hnsub : ¬ componentRoots (maskChar (signTupleBits b)) ⟦⟨γ, hγk⟩⟧ ⊆ {γ, -γ} := by
    intro hsub
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h3 : ({γ, -γ} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 :=
      (Set.ncard_insert_le γ {-γ}).trans (by simp)
    omega
  obtain ⟨δ, hδΨ, hδ1, hδ2, hδ3⟩ := exists_iform_ne_zero_of_not_subset hΨ hγΨ hnsub
  have hγr : IsRoot τ γ := hγk.1
  have hδr : IsRoot τ δ := hΨ.isRoot δ hδΨ
  rcases odd_corootPair_or_odd_corootPair hγr hδr (Ne.symm hδ1)
      (fun h => hδ2 (by rw [h]; simp)) hδ3 with hodd | hodd
  · exact key γ hγΨ δ hδΨ hodd
  · exact key δ hδΨ γ hγΨ hodd

theorem exists_componentRootSpan_eq_pair {K : Type} [Field K]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} (i : KernelComponent χ)
    (h : (componentRoots χ i).ncard ≤ 2) :
    ∃ γ, IsRoot τ γ ∧ componentRootSpan K χ i = rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  induction i using Quotient.inductionOn with
  | h a =>
  obtain ⟨α, hα⟩ := a
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
    (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact h) hfin).symm
  refine ⟨α, hα.1, ?_⟩
  change rootSpan τ K (componentRoots χ ⟦⟨α, hα⟩⟧) = _
  rw [heq, CFSG.LieType.Chevalley.OddToralFixed.rootSpan_pair]

end CFSG.ClassicalInvolution.Upgrade
