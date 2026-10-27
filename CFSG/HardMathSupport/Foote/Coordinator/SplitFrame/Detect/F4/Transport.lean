module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Centralizer

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false

@[expose] def sGamma (v : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  f4Word.foldr (reflect .F4) (reflect .F4 1 (f4Word.reverse.foldr (reflect .F4) v))

theorem orbit_data :
    reflect .F4 0 theta = root1342 ∧ sGamma theta = alpha1 ∧
    reflect .F4 0 alpha1 = -alpha1 ∧ sGamma (root1342) = -(root1342) ∧
    reflect .F4 0 (-(root1342)) = -theta := by decide +kernel

theorem orbit_data_neg :
    reflect .F4 0 (-theta) = -root1342 ∧ sGamma (-theta) = -alpha1 ∧
    reflect .F4 0 (-alpha1) = alpha1 ∧ sGamma (-(root1342)) = root1342 ∧
    reflect .F4 0 root1342 = theta := by decide +kernel


variable (K : Type) [Field K]

@[expose] def nA : ModGL Tag.F4 K := weylElt Tag.F4 K 0 1

@[expose] def nOmega : ModGL Tag.F4 K := (f4Word.map fun i => weylElt Tag.F4 K i 1).prod

@[expose] def nB : ModGL Tag.F4 K := nOmega K * weylElt Tag.F4 K 1 1 * (nOmega K)⁻¹

theorem single_zero_eq : (Pi.single 0 1 : Fin Tag.F4.rank → ℤ) = alpha1 := by decide +kernel
theorem neg_single_zero_eq : (-Pi.single 0 1 : Fin Tag.F4.rank → ℤ) = -alpha1 := by
  rw [single_zero_eq]
theorem f4Word_single_one : f4Word.foldr (reflect .F4) (Pi.single 1 1) = root1342 := by
  decide +kernel
theorem root1342_mem_S1set : root1342 ∈ S1set := by
  show _ ∈ f4LongList
  decide +kernel
theorem neg_root1342_mem_S1set : -root1342 ∈ S1set := by
  show _ ∈ f4LongList
  decide +kernel

theorem weylElt_one_eq (i : Fin Tag.F4.rank) :
    weylElt Tag.F4 K i 1 = xUnit Tag.F4 K i 1 * yUnit Tag.F4 K i (-1) * xUnit Tag.F4 K i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem nA_mem : nA K ∈ X1 K := by
  have hx : ∀ c, xUnit Tag.F4 K 0 c ∈ X1 K := fun c => by
    rw [← pinnedX_single, single_zero_eq]
    exact pinnedX_mem_rootSpan alpha1_mem_S1set c
  have hy : ∀ c, yUnit Tag.F4 K 0 c ∈ X1 K := fun c => by
    rw [← pinnedX_neg_single, neg_single_zero_eq]
    exact pinnedX_mem_rootSpan neg_alpha1_mem_S1set c
  rw [nA, weylElt_one_eq]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem nB_mem : nB K ∈ X1 K := by
  have hx : ∀ c, nOmega K * xUnit Tag.F4 K 1 c * (nOmega K)⁻¹ ∈ X1 K := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K f4Word
      (IsRoot.basis (τ := Tag.F4) 1)
    rw [← pinnedX_single]
    have h' := h c
    rw [wordProd_smul_eq_foldr, f4Word_single_one] at h'
    unfold nOmega
    rw [h']
    exact pinnedX_mem_rootSpan root1342_mem_S1set _
  have hy : ∀ c, nOmega K * yUnit Tag.F4 K 1 c * (nOmega K)⁻¹ ∈ X1 K := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K f4Word
      (isRoot_neg_single Tag.F4 1)
    rw [← pinnedX_neg_single]
    have h' := h c
    rw [wordProd_smul_eq_foldr, show f4Word.foldr (reflect .F4) (-Pi.single 1 1) =
      -root1342 by rw [← f4Word_single_one, ← wordProd_smul_eq_foldr, ← wordProd_smul_eq_foldr,
        smul_neg]] at h'
    unfold nOmega
    rw [h']
    exact pinnedX_mem_rootSpan neg_root1342_mem_S1set _
  have e : nB K = (nOmega K * xUnit Tag.F4 K 1 1 * (nOmega K)⁻¹) *
      (nOmega K * yUnit Tag.F4 K 1 (-1) * (nOmega K)⁻¹) *
      (nOmega K * xUnit Tag.F4 K 1 1 * (nOmega K)⁻¹) := by
    rw [nB, weylElt_one_eq]
    group
  rw [e]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem conjSub_nA {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    conjSub (nA K) (rootSubgroup Tag.F4 K γ) = rootSubgroup Tag.F4 K (reflect Tag.F4 0 γ) :=
  map_conj_weylElt_rootSubgroup K 0 hγ

theorem conjSub_nB {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    conjSub (nB K) (rootSubgroup Tag.F4 K γ) = rootSubgroup Tag.F4 K (sGamma γ) := by
  have hrev : ∀ v, (coxeterSystem Tag.F4).wordProd f4Word.reverse • v =
      f4Word.reverse.foldr (reflect .F4) v := fun v => wordProd_smul_eq_foldr _ _ _
  have hN : ∀ δ, IsRoot Tag.F4 δ → conjSub (nOmega K) (rootSubgroup Tag.F4 K δ) =
      rootSubgroup Tag.F4 K (f4Word.foldr (reflect .F4) δ) := by
    intro δ hδ
    have := map_conj_prod_weylElt_rootSubgroup K f4Word hδ
    rw [wordProd_smul_eq_foldr] at this
    exact this
  have hγ' : IsRoot Tag.F4 (f4Word.reverse.foldr (reflect .F4) γ) := by
    rw [← hrev]
    exact IsRoot.smul hγ _
  have e : f4Word.foldr (reflect .F4) (f4Word.reverse.foldr (reflect .F4) γ) = γ := by
    rw [← hrev, ← wordProd_smul_eq_foldr, CoxeterSystem.wordProd_reverse, smul_inv_smul]
  have h1 : conjSub (nOmega K)⁻¹ (rootSubgroup Tag.F4 K γ) =
      rootSubgroup Tag.F4 K (f4Word.reverse.foldr (reflect .F4) γ) := by
    have h2 := hN _ hγ'
    rw [e] at h2
    rw [← h2]
    simpa using conjSub_conjSub_inv (nOmega K)⁻¹ (rootSubgroup Tag.F4 K
      (f4Word.reverse.foldr (reflect .F4) γ))
  have hn1 : conjSub (weylElt Tag.F4 K 1 1)
      (rootSubgroup Tag.F4 K (f4Word.reverse.foldr (reflect .F4) γ)) =
      rootSubgroup Tag.F4 K (reflect Tag.F4 1 (f4Word.reverse.foldr (reflect .F4) γ)) :=
    map_conj_weylElt_rootSubgroup K 1 hγ'
  rw [nB, conjSub_mul, conjSub_mul, h1, hn1, hN _ (IsRoot.reflect 1 hγ')]
  rfl

theorem f4LongList_cases' : ∀ α ∈ f4LongList, α = theta ∨ α = root1342 ∨ α = alpha1 ∨
    α = -alpha1 ∨ α = -root1342 ∨ α = -theta := by decide +kernel

theorem isRoot_alpha1 : IsRoot Tag.F4 alpha1 := isRoot_of_mem_S1set alpha1_mem_S1set
theorem isRoot_root1342 : IsRoot Tag.F4 root1342 := isRoot_of_mem_S1set root1342_mem_S1set
theorem isRoot_neg_root1342 : IsRoot Tag.F4 (-root1342) :=
  isRoot_of_mem_S1set neg_root1342_mem_S1set

theorem transport_theta {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ S1set) :
    ∃ n ∈ X1 K, conjSub n (Uθ Tag.F4 K) = rootSubgroup Tag.F4 K α := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := orbit_data
  have hUθ : Uθ Tag.F4 K = rootSubgroup Tag.F4 K theta := rfl
  rcases f4LongList_cases' α hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, by rw [conjSub_one, hUθ]⟩
  · exact ⟨nA K, nA_mem K, by rw [hUθ, conjSub_nA K isRoot_theta, h1]⟩
  · exact ⟨nB K, nB_mem K, by rw [hUθ, conjSub_nB K isRoot_theta, h2]⟩
  · refine ⟨nA K * nB K, mul_mem (nA_mem K) (nB_mem K), ?_⟩
    rw [hUθ, conjSub_mul, conjSub_nB K isRoot_theta, h2, conjSub_nA K isRoot_alpha1, h3]
  · refine ⟨nB K * nA K, mul_mem (nB_mem K) (nA_mem K), ?_⟩
    rw [hUθ, conjSub_mul, conjSub_nA K isRoot_theta, h1, conjSub_nB K isRoot_root1342, h4]
  · refine ⟨nA K * nB K * nA K, mul_mem (mul_mem (nA_mem K) (nB_mem K)) (nA_mem K), ?_⟩
    rw [hUθ, conjSub_mul, conjSub_mul, conjSub_nA K isRoot_theta, h1,
      conjSub_nB K isRoot_root1342, h4, conjSub_nA K isRoot_neg_root1342, h5]

theorem isRoot_neg_theta : IsRoot Tag.F4 (-theta) := Heis.isRoot_neg_highRoot Tag.F4
theorem isRoot_neg_alpha1 : IsRoot Tag.F4 (-alpha1) := isRoot_of_mem_S1set neg_alpha1_mem_S1set

theorem transport_pair {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ S1set) :
    ∃ n ∈ X1 K, conjSub n (Uθ Tag.F4 K) = rootSubgroup Tag.F4 K α ∧
      conjSub n (Heis.Uneg Tag.F4 K) = rootSubgroup Tag.F4 K (-α) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := orbit_data
  obtain ⟨g1, g2, g3, g4, g5⟩ := orbit_data_neg
  have hUθ : Uθ Tag.F4 K = rootSubgroup Tag.F4 K theta := rfl
  have hUn : Heis.Uneg Tag.F4 K = rootSubgroup Tag.F4 K (-theta) := rfl
  rcases f4LongList_cases' α hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, by rw [conjSub_one, hUθ], by rw [conjSub_one, hUn]⟩
  · refine ⟨nA K, nA_mem K, by rw [hUθ, conjSub_nA K isRoot_theta, h1], ?_⟩
    rw [hUn, conjSub_nA K isRoot_neg_theta, g1]
  · refine ⟨nB K, nB_mem K, by rw [hUθ, conjSub_nB K isRoot_theta, h2], ?_⟩
    rw [hUn, conjSub_nB K isRoot_neg_theta, g2]
  · refine ⟨nA K * nB K, mul_mem (nA_mem K) (nB_mem K), ?_, ?_⟩
    · rw [hUθ, conjSub_mul, conjSub_nB K isRoot_theta, h2, conjSub_nA K isRoot_alpha1, h3]
    · rw [hUn, conjSub_mul, conjSub_nB K isRoot_neg_theta, g2, conjSub_nA K isRoot_neg_alpha1, g3,
        neg_neg]
  · refine ⟨nB K * nA K, mul_mem (nB_mem K) (nA_mem K), ?_, ?_⟩
    · rw [hUθ, conjSub_mul, conjSub_nA K isRoot_theta, h1, conjSub_nB K isRoot_root1342, h4]
    · rw [hUn, conjSub_mul, conjSub_nA K isRoot_neg_theta, g1, conjSub_nB K isRoot_neg_root1342,
        g4, neg_neg]
  · refine ⟨nA K * nB K * nA K, mul_mem (mul_mem (nA_mem K) (nB_mem K)) (nA_mem K), ?_, ?_⟩
    · rw [hUθ, conjSub_mul, conjSub_mul, conjSub_nA K isRoot_theta, h1,
        conjSub_nB K isRoot_root1342, h4, conjSub_nA K isRoot_neg_root1342, h5]
    · rw [hUn, conjSub_mul, conjSub_mul, conjSub_nA K isRoot_neg_theta, g1,
        conjSub_nB K isRoot_neg_root1342, g4, conjSub_nA K isRoot_root1342, g5, neg_neg]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
