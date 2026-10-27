module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis

set_option linter.unusedSectionVars false

@[expose] def omegaW : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6]

@[expose] def sTheta (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  omegaW.foldr (reflect .E8) (reflect .E8 7 (omegaW.reverse.foldr (reflect .E8) v))

@[expose] def reflGen (i : Fin 4) (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  if i = 0 then reflect .E8 5 v else if i = 1 then reflect .E8 6 v
    else if i = 2 then reflect .E8 7 v else sTheta v

theorem omegaW_single : omegaW.foldr (reflect .E8) (Pi.single 7 1) = theta := by decide +kernel

@[expose] def transportTable : List ((Fin Tag.E8.rank → ℤ) × List (Fin 4)) := [
  (![2, 3, 4, 6, 5, 4, 3, 2], []),
  (![2, 3, 4, 6, 5, 4, 3, 1], [2]),
  (![-2, -3, -4, -6, -5, -4, -3, -2], [3]),
  (![2, 3, 4, 6, 5, 4, 2, 1], [1, 2]),
  (![0, 0, 0, 0, 0, 0, 0, -1], [3, 2]),
  (![-2, -3, -4, -6, -5, -4, -3, -1], [2, 3]),
  (![2, 3, 4, 6, 5, 3, 2, 1], [0, 1, 2]),
  (![0, 0, 0, 0, 0, 0, -1, -1], [3, 1, 2]),
  (![0, 0, 0, 0, 0, 0, 0, 1], [2, 3, 2]),
  (![-2, -3, -4, -6, -5, -4, -2, -1], [1, 2, 3]),
  (![0, 0, 0, 0, 0, -1, -1, -1], [3, 0, 1, 2]),
  (![0, 0, 0, 0, 0, 0, -1, 0], [2, 3, 1, 2]),
  (![0, 0, 0, 0, 0, 0, 1, 1], [1, 2, 3, 2]),
  (![-2, -3, -4, -6, -5, -3, -2, -1], [0, 1, 2, 3]),
  (![0, 0, 0, 0, 0, -1, -1, 0], [2, 3, 0, 1, 2]),
  (![0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 3, 1, 2]),
  (![0, 0, 0, 0, 0, 1, 1, 1], [0, 1, 2, 3, 2]),
  (![0, 0, 0, 0, 0, -1, 0, 0], [1, 2, 3, 0, 1, 2]),
  (![0, 0, 0, 0, 0, 1, 1, 0], [0, 1, 2, 3, 1, 2]),
  (![0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 2, 3, 0, 1, 2])]

theorem transportTable_ok : ∀ p ∈ transportTable,
    p.2.foldr reflGen theta = p.1 ∧ p.2.foldr reflGen (-theta) = -p.1 := by decide +kernel

theorem transportTable_cover : ∀ α ∈ e8ListB, α ∈ transportTable.map Prod.fst := by
  decide +kernel

theorem single_mem_S1set : ∀ j : Fin Tag.E8.rank, j.val = 5 ∨ j.val = 6 ∨ j.val = 7 →
    (Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ e8ListB ∧ (-Pi.single j 1 : Fin Tag.E8.rank → ℤ) ∈ e8ListB := by
  decide +kernel


theorem wordProd_smul_foldr (ω : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd ω • v = ω.foldr (reflect .E8) v := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

variable (K : Type) [Field K]

@[expose] def nOmega : ModGL Tag.E8 K := (omegaW.map fun i => weylElt Tag.E8 K i 1).prod

@[expose] def nTheta : ModGL Tag.E8 K := nOmega K * weylElt Tag.E8 K 7 1 * (nOmega K)⁻¹

@[expose] def genE (i : Fin 4) : ModGL Tag.E8 K :=
  if i = 0 then weylElt Tag.E8 K 5 1 else if i = 1 then weylElt Tag.E8 K 6 1
    else if i = 2 then weylElt Tag.E8 K 7 1 else nTheta K

theorem weylElt_one_eq (i : Fin Tag.E8.rank) :
    weylElt Tag.E8 K i 1 = xUnit Tag.E8 K i 1 * yUnit Tag.E8 K i (-1) * xUnit Tag.E8 K i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem weylElt_mem_X1 {j : Fin Tag.E8.rank} (h : j.val = 5 ∨ j.val = 6 ∨ j.val = 7) :
    weylElt Tag.E8 K j 1 ∈ X1 K := by
  obtain ⟨h1, h2⟩ := single_mem_S1set j h
  have hx : ∀ c, xUnit Tag.E8 K j c ∈ X1 K := fun c => by
    rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan h1 c
  have hy : ∀ c, yUnit Tag.E8 K j c ∈ X1 K := fun c => by
    rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan h2 c
  rw [weylElt_one_eq]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem nTheta_mem : nTheta K ∈ X1 K := by
  have hx : ∀ c, nOmega K * xUnit Tag.E8 K 7 c * (nOmega K)⁻¹ ∈ X1 K := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K omegaW
      (IsRoot.basis (τ := Tag.E8) 7)
    rw [← pinnedX_single]
    have h' := h c
    rw [wordProd_smul_foldr, omegaW_single] at h'
    unfold nOmega
    rw [h']
    exact pinnedX_mem_rootSpan theta_mem_S1set _
  have hy : ∀ c, nOmega K * yUnit Tag.E8 K 7 c * (nOmega K)⁻¹ ∈ X1 K := by
    intro c
    obtain ⟨ε, -, h⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K omegaW
      (isRoot_neg_single Tag.E8 7)
    rw [← pinnedX_neg_single]
    have h' := h c
    rw [wordProd_smul_foldr, show omegaW.foldr (reflect .E8) (-Pi.single 7 1) = -theta by
      rw [← omegaW_single, ← wordProd_smul_foldr, ← wordProd_smul_foldr, smul_neg]] at h'
    unfold nOmega
    rw [h']
    exact pinnedX_mem_rootSpan neg_theta_mem_S1set _
  have e : nTheta K = (nOmega K * xUnit Tag.E8 K 7 1 * (nOmega K)⁻¹) *
      (nOmega K * yUnit Tag.E8 K 7 (-1) * (nOmega K)⁻¹) *
      (nOmega K * xUnit Tag.E8 K 7 1 * (nOmega K)⁻¹) := by
    rw [nTheta, weylElt_one_eq]
    group
  rw [e]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem genE_mem (i : Fin 4) : genE K i ∈ X1 K := by
  unfold genE
  split_ifs
  · exact weylElt_mem_X1 K (Or.inl rfl)
  · exact weylElt_mem_X1 K (Or.inr (Or.inl rfl))
  · exact weylElt_mem_X1 K (Or.inr (Or.inr rfl))
  · exact nTheta_mem K

theorem isRoot_sTheta {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) :
    IsRoot Tag.E8 (sTheta γ) := by
  have hrev : ∀ v, (coxeterSystem Tag.E8).wordProd omegaW.reverse • v =
      omegaW.reverse.foldr (reflect .E8) v := fun v => wordProd_smul_foldr _ _
  have h1 : IsRoot Tag.E8 (omegaW.reverse.foldr (reflect .E8) γ) := by
    rw [← hrev]
    exact IsRoot.smul hγ _
  have h2 : IsRoot Tag.E8 (reflect .E8 7 (omegaW.reverse.foldr (reflect .E8) γ)) :=
    IsRoot.reflect 7 h1
  unfold sTheta
  rw [← wordProd_smul_foldr]
  exact IsRoot.smul h2 _

theorem isRoot_reflGen (i : Fin 4) {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) :
    IsRoot Tag.E8 (reflGen i γ) := by
  unfold reflGen
  split_ifs
  · exact IsRoot.reflect 5 hγ
  · exact IsRoot.reflect 6 hγ
  · exact IsRoot.reflect 7 hγ
  · exact isRoot_sTheta hγ

theorem conjSub_nTheta {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) :
    conjSub (nTheta K) (rootSubgroup Tag.E8 K γ) = rootSubgroup Tag.E8 K (sTheta γ) := by
  have hrev : ∀ v, (coxeterSystem Tag.E8).wordProd omegaW.reverse • v =
      omegaW.reverse.foldr (reflect .E8) v := fun v => wordProd_smul_foldr _ _
  have hN : ∀ δ, IsRoot Tag.E8 δ → conjSub (nOmega K) (rootSubgroup Tag.E8 K δ) =
      rootSubgroup Tag.E8 K (omegaW.foldr (reflect .E8) δ) := by
    intro δ hδ
    have := map_conj_prod_weylElt_rootSubgroup K omegaW hδ
    rw [wordProd_smul_foldr] at this
    exact this
  have hγ' : IsRoot Tag.E8 (omegaW.reverse.foldr (reflect .E8) γ) := by
    rw [← hrev]
    exact IsRoot.smul hγ _
  have e : omegaW.foldr (reflect .E8) (omegaW.reverse.foldr (reflect .E8) γ) = γ := by
    rw [← hrev, ← wordProd_smul_foldr, CoxeterSystem.wordProd_reverse, smul_inv_smul]
  have h1 : conjSub (nOmega K)⁻¹ (rootSubgroup Tag.E8 K γ) =
      rootSubgroup Tag.E8 K (omegaW.reverse.foldr (reflect .E8) γ) := by
    have h2 := hN _ hγ'
    rw [e] at h2
    rw [← h2]
    simpa using conjSub_conjSub_inv (nOmega K)⁻¹ (rootSubgroup Tag.E8 K
      (omegaW.reverse.foldr (reflect .E8) γ))
  have hn1 : conjSub (weylElt Tag.E8 K 7 1)
      (rootSubgroup Tag.E8 K (omegaW.reverse.foldr (reflect .E8) γ)) =
      rootSubgroup Tag.E8 K (reflect Tag.E8 7 (omegaW.reverse.foldr (reflect .E8) γ)) :=
    map_conj_weylElt_rootSubgroup K 7 hγ'
  rw [nTheta, conjSub_mul, conjSub_mul, h1, hn1, hN _ (IsRoot.reflect 7 hγ')]
  rfl

theorem conjSub_genE (i : Fin 4) {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) :
    conjSub (genE K i) (rootSubgroup Tag.E8 K γ) = rootSubgroup Tag.E8 K (reflGen i γ) := by
  unfold genE reflGen
  split_ifs
  · exact map_conj_weylElt_rootSubgroup K 5 hγ
  · exact map_conj_weylElt_rootSubgroup K 6 hγ
  · exact map_conj_weylElt_rootSubgroup K 7 hγ
  · exact conjSub_nTheta K hγ

theorem exists_word_transport (w : List (Fin 4)) :
    ∃ n ∈ X1 K, ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ →
      conjSub n (rootSubgroup Tag.E8 K γ) = rootSubgroup Tag.E8 K (w.foldr reflGen γ) := by
  induction w with
  | nil => exact ⟨1, one_mem _, fun γ _ => by rw [conjSub_one]; rfl⟩
  | cons i w ih =>
    obtain ⟨n, hn, h⟩ := ih
    refine ⟨genE K i * n, mul_mem (genE_mem K i) hn, fun γ hγ => ?_⟩
    have hroot : IsRoot Tag.E8 (w.foldr reflGen γ) := by
      clear h hn
      induction w with
      | nil => exact hγ
      | cons j w' ih' => exact isRoot_reflGen j ih'
    rw [conjSub_mul, h γ hγ, conjSub_genE K i hroot]
    rfl

theorem transport_pair {α : Fin Tag.E8.rank → ℤ} (hα : α ∈ S1set) :
    ∃ n ∈ X1 K, conjSub n (Uθ Tag.E8 K) = rootSubgroup Tag.E8 K α ∧
      conjSub n (Heis.Uneg Tag.E8 K) = rootSubgroup Tag.E8 K (-α) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (transportTable_cover α hα)
  obtain ⟨n, hn, h⟩ := exists_word_transport K p.2
  obtain ⟨h1, h2⟩ := transportTable_ok p hp
  refine ⟨n, hn, ?_, ?_⟩
  · have := h theta (mem_rootFinset.1 theta_mem)
    rw [h1] at this
    exact this
  · have := h (-theta) (Heis.isRoot_neg_highRoot Tag.E8)
    rw [h2] at this
    exact this

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
