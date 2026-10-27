module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotToral
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LieType.Chevalley.GraphFixedMonomialQuotient
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat

public section

namespace CFSG.SeitzReduction.EPilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

theorem symmetrizer_eq_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : τ.symmetrizer = 1 := by
  rcases hτ with rfl | rfl | rfl <;> rfl

theorem coPair_sub (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    coPair τ i (x - y) = coPair τ i x - coPair τ i y := by
  simp only [coPair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem coPair_zsmul (i : Fin τ.rank) (c : ℤ) (x : Fin τ.rank → ℤ) :
    coPair τ i (c • x) = c * coPair τ i x := by
  simp only [coPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

section Form


theorem iform_single_eq_coPair (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (x : Fin τ.rank → ℤ)
    (i : Fin τ.rank) : iform x (Pi.single i 1) = coPair τ i x := by
  rw [iform_single_right, symmetrizer_eq_one hτ, Matrix.one_apply_eq, one_mul]
  rfl

theorem coPair_highRoot (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    coPair τ i (highRoot τ) = if i = highNode τ then 1 else 0 := by
  rw [← iform_single_eq_coPair hτ, iform_highRoot_single hτ]

theorem iform_self_nonneg (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

theorem eq_zero_of_forall_iform_single_eq_zero {x : Fin τ.rank → ℤ}
    (h : ∀ j, iform x (Pi.single j 1) = 0) : x = 0 := by
  by_contra hx
  have hpos := iform_self_pos hx
  rw [F4Pilot.iform_eq_sum_mul_iform_single] at hpos
  simp only [h, mul_zero, Finset.sum_const_zero] at hpos
  exact lt_irrefl _ hpos

section Roots

variable (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
include hτ

theorem abs_coPair_le_two {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank) :
    |coPair τ i α| ≤ 2 := by
  have h1 := iform_self_nonneg (α + Pi.single i 1)
  have h2 := iform_self_nonneg (α - Pi.single i 1)
  have hαα := iform_self_eq_two hτ hα
  have hii := iform_self_eq_two hτ (isRoot_single τ i)
  have hc := iform_single_eq_coPair hτ α i
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm (Pi.single i 1) α] at h1
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm (Pi.single i 1) α] at h2
  rw [abs_le]
  constructor <;> linarith

theorem eq_zsmul_highRoot_of_coPair_eq_zero {x : Fin τ.rank → ℤ}
    (h : ∀ j, j ≠ highNode τ → coPair τ j x = 0) :
    x = coPair τ (highNode τ) x • highRoot τ := by
  refine sub_eq_zero.1 (eq_zero_of_forall_iform_single_eq_zero fun j => ?_)
  rw [iform_single_eq_coPair hτ, coPair_sub, coPair_zsmul, coPair_highRoot hτ]
  by_cases hj : j = highNode τ
  · subst hj
    simp
  · simp [hj, h j hj]

theorem eq_highRoot_or_neg_of_coPair_eq_zero {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h : ∀ j, j ≠ highNode τ → coPair τ j α = 0) : α = highRoot τ ∨ α = -highRoot τ := by
  have e := eq_zsmul_highRoot_of_coPair_eq_zero hτ h
  set c := coPair τ (highNode τ) α
  have hαα := iform_self_eq_two hτ hα
  rw [e, iform_smul_left, iform_smul_right, iform_highRoot_self hτ] at hαα
  have hc : c = 1 ∨ c = -1 := by
    have h' : 2 * ((c - 1) * (c + 1)) = 0 := by linear_combination hαα
    rcases mul_eq_zero.1 h' with h1 | h1
    · omega
    rcases mul_eq_zero.1 h1 with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hc with hc | hc
  · left
    rw [e, hc, one_smul]
  · right
    rw [e, hc, neg_one_smul]

theorem eq_single_or_sub_highRoot_of_iform_eq {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h : ∀ j, j ≠ highNode τ →
      iform α (Pi.single j 1) = iform (Pi.single (highNode τ) 1) (Pi.single j 1)) :
    α = Pi.single (highNode τ) 1 ∨ α = Pi.single (highNode τ) 1 - highRoot τ := by
  have h0 : ∀ j, j ≠ highNode τ → coPair τ j (α - Pi.single (highNode τ) 1) = 0 := by
    intro j hj
    rw [coPair_sub, ← iform_single_eq_coPair hτ, ← iform_single_eq_coPair hτ, h j hj, sub_self]
  have e := eq_zsmul_highRoot_of_coPair_eq_zero hτ h0
  set c := coPair τ (highNode τ) (α - Pi.single (highNode τ) 1)
  have eα : α = Pi.single (highNode τ) 1 + c • highRoot τ := by
    rw [← e]
    abel
  have hαα := iform_self_eq_two hτ hα
  have h11 := iform_self_eq_two hτ (isRoot_single τ (highNode τ))
  have h1θ : iform (Pi.single (highNode τ) 1 : Fin τ.rank → ℤ) (highRoot τ) = 1 := by
    rw [iform_comm, iform_highRoot hτ, Pi.single_eq_same]
  rw [eα, iform_add_left, iform_add_right, iform_add_right, iform_smul_left, iform_smul_right,
    iform_smul_left, iform_smul_right, iform_comm (highRoot τ), h11, h1θ,
    iform_highRoot_self hτ] at hαα
  have hc : c = 0 ∨ c = -1 := by
    have h' : 2 * (c * (c + 1)) = 0 := by linear_combination hαα
    rcases mul_eq_zero.1 h' with h1 | h1
    · omega
    rcases mul_eq_zero.1 h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  rcases hc with hc | hc
  · left
    rw [eα, hc, zero_smul, add_zero]
  · right
    rw [eα, hc, neg_one_smul, sub_eq_add_neg]

end Roots

section Reflection

variable (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
include hτ

theorem smul_conj_simple_eq {v : WeylGroup τ} {i : Fin τ.rank}
    (hv : v • (Pi.single i 1 : Fin τ.rank → ℤ) = highRoot τ) (x : Fin τ.rank → ℤ) :
    (v * simple τ i * v⁻¹) • x = x - x (highNode τ) • highRoot τ := by
  have hpair : coPair τ i (v⁻¹ • x) = x (highNode τ) := by
    rw [← iform_single_eq_coPair hτ, ← iform_smul v, smul_inv_smul, hv, iform_comm,
      iform_highRoot hτ]
  rw [mul_smul, mul_smul, simple_smul, reflect_eq_sub_coPair, hpair, smul_sub, smul_inv_smul,
    smul_comm v (x (highNode τ)), hv]

end Reflection

end Form

theorem eq_zero_of_zpow_eq_one_of_charTwo {K : Type} [Field K] [CharP K 2] {l : Kˣ} (hl : l ≠ 1)
    {n : ℤ} (hn : |n| ≤ 2) (h : l ^ n = 1) : n = 0 := by
  have hsq : l ^ (2 : ℤ) ≠ 1 := by
    intro h2
    apply hl
    have h2' : (l : K) * l = 1 := by
      have := congrArg Units.val h2
      simpa [sq] using this
    exact Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero CharTwo.two_eq_zero h2')
  rw [abs_le] at hn
  rcases (show n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact absurd (by rw [zpow_neg, inv_eq_one] at h; exact h) hsq
  · exact absurd (by rw [zpow_neg, zpow_one, inv_eq_one] at h; exact h) hl
  · rfl
  · exact absurd (by rw [zpow_one] at h; exact h) hl
  · exact absurd h hsq

variable {K : Type} [Field K]

theorem rootChar_cartan_row (l : Kˣ) (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    rootChar (fun j => l ^ τ.cartan i j) γ = l ^ coPair τ i γ := by
  simp only [rootChar, coPair, ← zpow_mul]
  exact Finset.prod_zpow_eq_zpow_sum _ _ _


theorem rootChar_single_eq (a : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    rootChar a (Pi.single j 1) = a j := by
  have h := rootChar_nsmul_single a j 1
  rwa [one_smul, pow_one] at h

theorem rootChar_cartanChar_highRoot
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (c : Fin τ.rank → Kˣ) :
    rootChar (cartanChar c) (highRoot τ) = c (highNode τ) := by
  have h : ∀ j, ∑ l, τ.cartan j l * highRoot τ l = if j = highNode τ then 1 else 0 :=
    fun j => coPair_highRoot hτ j
  simp only [rootChar, cartanChar, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  simp only [Finset.prod_zpow_eq_zpow_sum, h]
  rw [Finset.prod_eq_single (highNode τ) (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem rootDiagUnit_highDiag_eq_conj
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {v : WeylGroup τ}
    {i : Fin τ.rank}
    (hv : v • (Pi.single i 1 : Fin τ.rank → ℤ) = highRoot τ) (c : Kˣ) :
    rootDiagUnit τ (highDiag τ c) =
      canonicalRep (coxeterSystem τ) K v * torusElt τ K i c *
        (canonicalRep (coxeterSystem τ) K v)⁻¹ := by
  rw [torusElt_eq_rootDiagUnit]
  refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ v).2 fun x => ?_
  rw [rootChar_highDiag, rootChar_cartan_row]
  congr 1
  rw [← iform_highRoot hτ (v • x), ← hv, iform_smul, iform_comm, iform_single_eq_coPair hτ]

section Commute


theorem highRootSL2_le_centralizer_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    highRootSL2 τ K ≤ Subgroup.centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)) :=
  Subgroup.le_centralizer_iff.1 (rootSpan_perpRoots_le_centralizer_highRootSL2 hτ)

end Commute

section Members


theorem weylElt_mem_rootPair (i : Fin τ.rank) (t : Kˣ) :
    weylElt τ K i t ∈ rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, ← pinnedX_single, ← pinnedX_neg_single]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩))
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)))
    (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩))

theorem pinnedX_single_mem_perpLevi {j : Fin τ.rank} (hj : j ≠ highNode τ) (c : K) :
    pinnedX τ K (Pi.single j 1) c ∈ rootSpan τ K (perpRoots τ) :=
  rootSubgroup_le_rootSpan_perpRoots (single_mem_perpRoots hj) (Subgroup.subset_closure ⟨c, rfl⟩)

theorem rootSpan_le_adjointGroup' (S : Set (Fin τ.rank → ℤ)) :
    rootSpan τ K S ≤ adjointGroup τ K :=
  iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ

theorem highRootSL2_le_adjointGroup : highRootSL2 τ K ≤ adjointGroup τ K :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

theorem rootSubgroup_highRoot_le_highRootSL2 :
    rootSubgroup τ K (highRoot τ) ≤ highRootSL2 τ K :=
  le_sup_left

end Members

section Torus

variable
  (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
include hτ

omit hτ in
theorem map_conj_rootPair_eq_highRootSL2 {v : WeylGroup τ} {i : Fin τ.rank}
    (hv : v • (Pi.single i 1 : Fin τ.rank → ℤ) = highRoot τ) :
    (rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1)).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K v)).toMonoidHom = highRootSL2 τ K := by
  rw [Subgroup.map_sup, (canonical_weyl_root_transport τ K).2.1 v _ (isRoot_single τ i),
    (canonical_weyl_root_transport τ K).2.1 v _ (IsRoot.neg (isRoot_single τ i)), smul_neg, hv]
  rfl

omit hτ in
theorem conj_mem_highRootSL2 {v : WeylGroup τ} {i : Fin τ.rank}
    (hv : v • (Pi.single i 1 : Fin τ.rank → ℤ) = highRoot τ) {x : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1)) :
    canonicalRep (coxeterSystem τ) K v * x * (canonicalRep (coxeterSystem τ) K v)⁻¹ ∈
      highRootSL2 τ K := by
  rw [← map_conj_rootPair_eq_highRootSL2 hv]
  exact ⟨x, hx, rfl⟩

theorem rootDiagUnit_highDiag_mem_highRootSL2 (c : Kˣ) :
    rootDiagUnit τ (highDiag τ c) ∈ highRootSL2 τ K := by
  obtain ⟨v, i, hv⟩ := isRoot_iff_exists_smul_single.1 (isRoot_highRoot τ)
  rw [rootDiagUnit_highDiag_eq_conj hτ hv]
  exact conj_mem_highRootSL2 hv (F4Pilot.torusElt_mem_rootPair i c)

theorem highTorusLine_le_highRootSL2 : highTorusLine τ K ≤ highRootSL2 τ K := by
  rintro _ ⟨c, rfl⟩
  exact rootDiagUnit_highDiag_mem_highRootSL2 hτ c

omit hτ in
theorem eq_one_of_rootDiagUnit_mem_centralizer {b : Fin τ.rank → Kˣ}
    (hb : rootDiagUnit τ b ∈
      Subgroup.centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K)))
    {j : Fin τ.rank} (hj : j ≠ highNode τ) : b j = 1 := by
  have hc := Subgroup.mem_centralizer_iff.1 hb _ (pinnedX_single_mem_perpLevi hj 1)
  have e : pinnedX τ K (Pi.single j 1) ((rootChar b (Pi.single j 1) : K) * 1) =
      pinnedX τ K (Pi.single j 1) 1 := by
    rw [← rootDiagUnit_conj_pinnedX b (isRoot_single τ j), ← hc, mul_inv_cancel_right]
  have e' := pinnedX_injective τ K _ e
  rw [mul_one, rootChar_single_eq] at e'
  exact Units.ext e'

theorem mem_highRootSL2_of_mem_torusGroup {t : ModGL τ K} (ht : t ∈ torusGroup τ K)
    (htD : t ∈ Subgroup.centralizer (rootSpan τ K (perpRoots τ) : Set (ModGL τ K))) :
    t ∈ highRootSL2 τ K := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hb : b = highDiag τ (b (highNode τ)) := by
    funext j
    by_cases hj : j = highNode τ
    · subst hj
      rw [highDiag, Pi.mulSingle_eq_same]
    · rw [highDiag, Pi.mulSingle_eq_of_ne hj, eq_one_of_rootDiagUnit_mem_centralizer htD hj]
  rw [hb]
  exact rootDiagUnit_highDiag_mem_highRootSL2 hτ _

theorem mem_perpLevi_of_mem_torusGroup {t : ModGL τ K} (ht : t ∈ torusGroup τ K)
    (hθ : t * pinnedX τ K (highRoot τ) 1 * t⁻¹ = pinnedX τ K (highRoot τ) 1) :
    t ∈ rootSpan τ K (perpRoots τ) := by
  obtain ⟨c, rfl⟩ := exists_cartanChar_eq_of_mem_torusGroup ht
  have hc : c (highNode τ) = 1 := by
    rw [rootDiagUnit_conj_pinnedX _ (isRoot_highRoot τ)] at hθ
    have e := pinnedX_injective τ K _ hθ
    rw [mul_one, rootChar_cartanChar_highRoot hτ] at e
    exact Units.ext e
  rw [← list_prod_torusElt_eq_rootDiagUnit]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j = highNode τ
  · subst hj
    rw [hc, torusElt_eq_rootDiagUnit]
    simp only [one_zpow]
    rw [show (fun _ : Fin τ.rank => (1 : Kˣ)) = 1 from rfl, rootDiagUnit_one]
    exact one_mem _
  · exact torusElt_mem_rootSpan_perpRoots hj _

end Torus

end CFSG.SeitzReduction.EPilot
