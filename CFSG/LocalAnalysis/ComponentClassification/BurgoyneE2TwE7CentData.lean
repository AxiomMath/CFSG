module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7Cent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Kernel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

@[expose] def e7Gamma2 : List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  [(![1, 2, 2, 3, 2, 1, 0], 3), (![0, 0, 0, 0, 0, 0, 1], -5), (![0, 0, 0, 0, 0, 1, 0], -3),
    (![0, 0, 0, 0, 1, 0, 0], 3), (![0, 0, 0, 1, 0, 0, 0], -4), (![0, 0, 1, 0, 0, 0, 0], -3),
    (![1, 0, 0, 0, 0, 0, 0], 4)]

@[expose] def e7Gamma3 : List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  [(![0, 0, 1, 0, 0, 0, 0], 2), (![1, 1, 1, 1, 0, 0, 0], -3), (![0, 0, 0, 1, 0, 0, 0], 3),
    (![0, 0, 0, 0, 1, 0, 0], 1), (![0, 0, 0, 0, 0, 1, 0], -6), (![0, 0, 0, 0, 0, 0, 1], 5)]

theorem e7Gamma2_reg : ∀ α ∈ rootFinset .E7,
    (∑ j, regCoweight e7Gamma2 j * α j) ≠ 0 ∧ (∑ j, regCoweight e7Gamma2 j * α j).natAbs < 19 := by
  decide +kernel

theorem e7Gamma3_reg : ∀ α ∈ rootFinset .E7,
    (∑ j, regCoweight e7Gamma3 j * α j) ≠ 0 ∧ (∑ j, regCoweight e7Gamma3 j * α j).natAbs < 19 := by
  decide +kernel

theorem e7Gamma2_mem : ∀ y ∈ e7Gamma2, y.1 ∈ Set.range e7A7Root := by
  intro y hy
  simp only [e7Gamma2, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨5, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨6, by funext i; fin_cases i <;> rfl⟩

theorem e7Gamma3_mem : ∀ y ∈ e7Gamma3, y.1 ∈ Set.range e7E6Root := by
  intro y hy
  simp only [e7Gamma3, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
  · exact ⟨5, by funext i; fin_cases i <;> rfl⟩



variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem e7A7Root_isRoot (i : Fin 7) : IsRoot .E7 (e7A7Root i) := by
  by_cases h : i = 0
  · rw [h, show e7A7Root 0 = e7BetaRoot by simp [e7A7Root]]
    exact isRoot_e7BetaRoot
  · rw [show e7A7Root i = Pi.single (e7A7Node i) 1 by simp [e7A7Root, h]]
    exact isRoot_single _ _

theorem e7E6Root_isRoot (i : Fin 6) : IsRoot .E7 (e7E6Root i) := by
  by_cases h : i = 1
  · rw [h, show e7E6Root 1 = e7GammaRoot by simp [e7E6Root]]
    exact isRoot_e7GammaRoot
  · rw [show e7E6Root i = Pi.single (e7E6Node i) 1 by simp [e7E6Root, h]]
    exact isRoot_single _ _

omit
  [IsAlgClosed k] [Fact p.Prime]
  [CharP k p] in
theorem rootChar_E7 (b : Fin (Tag.rank .E7) → kˣ) (v : Fin (Tag.rank .E7) → ℤ) :
    rootChar b v = b (e7Node 0) ^ v (e7Node 0) * b (e7Node 1) ^ v (e7Node 1) *
      b (e7Node 2) ^ v (e7Node 2) * b (e7Node 3) ^ v (e7Node 3) * b (e7Node 4) ^ v (e7Node 4) *
        b (e7Node 5) ^ v (e7Node 5) * b (e7Node 6) ^ v (e7Node 6) := by
  show ∏ i : Fin 7, b i ^ v i = _
  rw [Fin.prod_univ_seven]
  rfl

section Datum

variable (D : OrthogonalSemilinearFixedRootDatum .E7 p k)

theorem sq_eq_one_of_commute_orbitGroup_two (hq : 3 ≤ D.q) (hχ : D.χ = signMaskChar .E7 2)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    [Subsingleton (KernelComponent D.χ)] {z : ModGL .E7 k} (hzG : z ∈ adjointGroup .E7 k)
    (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) : z ^ 2 = 1 := by
  have hcard := orbitCard_of_e7Word D (Or.inl rfl) hχ hθ
  have hΔ : D.simpleRootsJ = Set.range e7A7Root := by
    rw [simpleRootsJ_eq_simpleUnion, hχ, simpleUnion_e7_two]
  have hmem : ∀ β ∈ Set.range e7A7Root, ∀ A : SL2 k,
      z * rootSL2 .E7 k β A = rootSL2 .E7 k β A * z := fun β hβ A =>
    commute_rootSL2_of_commute_orbitGroup D hq hcard hz (hΔ ▸ hβ) A
  have hroot : ∀ y ∈ e7Gamma2, IsRoot .E7 y.1 := fun y hy => by
    obtain ⟨i, hi⟩ := e7Gamma2_mem y hy
    rw [← hi]
    exact (e7A7Root_isRoot i)
  have hT := mem_torusGroup_of_commute_rootTorus p (Or.inr (Or.inl rfl)) hzG e7Gamma2 hroot
    (fun y hy s => hmem y.1 (e7Gamma2_mem y hy) (HSL s)) 19
    (fun α hα => e7Gamma2_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hχb : ∀ β ∈ Set.range e7A7Root, rootChar b β = 1 := fun β hβ => by
    obtain ⟨i, rfl⟩ := hβ
    exact rootChar_eq_one_of_commute (e7A7Root_isRoot i) (hmem _ ⟨i, rfl⟩ (uSL 1))
  have hb : ∀ j : Fin 7, j ≠ 1 → b (e7Node j) = 1 := by
    intro j hj
    have hj' : ∃ i : Fin 7, e7A7Root i = Pi.single (e7Node j) 1 := by
      fin_cases j
      · exact ⟨6, by funext i; fin_cases i <;> rfl⟩
      · exact absurd rfl hj
      · exact ⟨5, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨1, by funext i; fin_cases i <;> rfl⟩
    obtain ⟨i, hi⟩ := hj'
    have h := hχb _ ⟨i, hi⟩
    rwa [rootChar_single'] at h
  have hb1 : b (e7Node 1) ^ 2 = 1 := by
    have h := hχb ![1, 2, 2, 3, 2, 1, 0] ⟨0, by funext i; fin_cases i <;> rfl⟩
    have h' := (rootChar_E7 b ![1, 2, 2, 3, 2, 1, 0]).symm.trans h
    rw [hb 0 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
      hb 5 (by decide), hb 6 (by decide)] at h'
    have e : (![1, 2, 2, 3, 2, 1, 0] : Fin (Tag.rank .E7) → ℤ) (e7Node 1) = 2 := rfl
    rw [e] at h'
    simpa using h'
  rw [sq, ← rootDiagUnit_mul]
  convert rootDiagUnit_one (τ := .E7) (K := k) using 2
  funext j
  obtain ⟨j', rfl⟩ : ∃ j' : Fin 7, e7Node j' = j := ⟨j, rfl⟩
  by_cases hj : j' = 1
  · subst hj
    rw [Pi.mul_apply, ← sq, hb1]
    rfl
  · rw [Pi.mul_apply, hb j' hj, one_mul]
    rfl

theorem eq_of_commute_orbitGroup_three (hq : 3 ≤ D.q) (hχ : D.χ = signMaskChar .E7 3)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    [Subsingleton (KernelComponent D.χ)] {z : ModGL .E7 k} (hzG : z ∈ adjointGroup .E7 k)
    (hz : ∀ w ∈ D.orbitGroup, z * w = w * z) :
    ∃ b : Fin (Tag.rank .E7) → kˣ, z = rootDiagUnit .E7 b ∧
      (∀ j : Fin 7, 2 ≤ j.val → b (e7Node j) = 1) ∧ b (e7Node 0) * b (e7Node 1) = 1 := by
  have hcard := orbitCard_of_e7Word D (Or.inr rfl) hχ hθ
  have hΔ : D.simpleRootsJ = Set.range e7E6Root := by
    rw [simpleRootsJ_eq_simpleUnion, hχ, simpleUnion_e7_three]
  have hmem : ∀ β ∈ Set.range e7E6Root, ∀ A : SL2 k,
      z * rootSL2 .E7 k β A = rootSL2 .E7 k β A * z := fun β hβ A =>
    commute_rootSL2_of_commute_orbitGroup D hq hcard hz (hΔ ▸ hβ) A
  have hroot : ∀ y ∈ e7Gamma3, IsRoot .E7 y.1 := fun y hy => by
    obtain ⟨i, hi⟩ := e7Gamma3_mem y hy
    rw [← hi]
    exact (e7E6Root_isRoot i)
  have hT := mem_torusGroup_of_commute_rootTorus p (Or.inr (Or.inl rfl)) hzG e7Gamma3 hroot
    (fun y hy s => hmem y.1 (e7Gamma3_mem y hy) (HSL s)) 19
    (fun α hα => e7Gamma3_reg α (mem_rootFinset.2 hα))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hχb : ∀ β ∈ Set.range e7E6Root, rootChar b β = 1 := fun β hβ => by
    obtain ⟨i, rfl⟩ := hβ
    exact rootChar_eq_one_of_commute (e7E6Root_isRoot i) (hmem _ ⟨i, rfl⟩ (uSL 1))
  have hb : ∀ j : Fin 7, 2 ≤ j.val → b (e7Node j) = 1 := by
    intro j hj
    have hj' : ∃ i : Fin 6, e7E6Root i = Pi.single (e7Node j) 1 := by
      fin_cases j
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
      · exact ⟨0, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨2, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨3, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨4, by funext i; fin_cases i <;> rfl⟩
      · exact ⟨5, by funext i; fin_cases i <;> rfl⟩
    obtain ⟨i, hi⟩ := hj'
    have h := hχb _ ⟨i, hi⟩
    rwa [rootChar_single'] at h
  refine ⟨b, rfl, hb, ?_⟩
  have h := hχb ![1, 1, 1, 1, 0, 0, 0] ⟨1, by funext i; fin_cases i <;> rfl⟩
  have h' := (rootChar_E7 b ![1, 1, 1, 1, 0, 0, 0]).symm.trans h
  rw [hb 2 (by decide), hb 3 (by decide)] at h'
  have e0 : (![1, 1, 1, 1, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) (e7Node 0) = 1 := rfl
  have e1 : (![1, 1, 1, 1, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) (e7Node 1) = 1 := rfl
  have e4 : (![1, 1, 1, 1, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) (e7Node 4) = 0 := rfl
  have e5 : (![1, 1, 1, 1, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) (e7Node 5) = 0 := rfl
  have e6 : (![1, 1, 1, 1, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) (e7Node 6) = 0 := rfl
  rw [e0, e1, e4, e5, e6] at h'
  simpa using h'

end Datum

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
