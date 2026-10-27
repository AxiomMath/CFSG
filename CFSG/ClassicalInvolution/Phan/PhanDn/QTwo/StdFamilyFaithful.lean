module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.StdFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.AmalgamFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyDisj

public section


namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.Timmesfeld (edgeD)

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

private abbrev finM (m : ℕ) : Fin (m + 1) :=
  Fin.last m

private abbrev finM1 (m : ℕ) : Fin (m + 1) :=
  ⟨m - 1, by omega⟩

private abbrev finM2 (m : ℕ) : Fin (m + 1) :=
  ⟨m - 2, by omega⟩

@[simp] private theorem finM_val (m : ℕ) : (finM m).val = m := rfl

@[simp] private theorem finM1_val (m : ℕ) : (finM1 m).val = m - 1 := rfl

@[simp] private theorem finM2_val (m : ℕ) : (finM2 m).val = m - 2 := rfl

private theorem label_three_symm {m : ℕ} {i j : Fin (m + 1)}
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 :=
  ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply i j).trans h

private theorem label_three_finM2_finM1 {m : ℕ} (hm : 3 ≤ m) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM2 m) (finM1 m) = 3 := by
  rw [CFSG.ClassicalInvolution.PhanDn.ggCoxeterMatrixD_eq_three_iff (by omega)]
  left
  rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
  left
  refine ⟨?_, ?_⟩
  · rw [finM2_val, finM1_val]
    omega
  · rw [finM1_val]
    omega

private theorem label_three_finM2_finM {m : ℕ} (hm : 3 ≤ m) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM2 m) (finM m) = 3 := by
  rw [CFSG.ClassicalInvolution.PhanDn.ggCoxeterMatrixD_eq_three_iff (by omega)]
  left
  rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
  right
  refine ⟨?_, ?_⟩
  · rw [finM2_val, show (m + 1) - 3 = m - 2 from by omega]
  · rw [finM_val, show (m + 1) - 1 = m from by omega]

private theorem eq_finM2_of_label_three_finM1 {m : ℕ} (hm : 3 ≤ m) {j : Fin (m + 1)}
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM1 m) j = 3) : j = finM2 m := by
  rcases (CFSG.ClassicalInvolution.PhanDn.ggCoxeterMatrixD_eq_three_iff (by omega)
    (finM1 m) j).1 h with hE | hE
  · rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h1' : m - 1 + 1 = j.val := by simpa using h1
      omega
    · have h1' : m - 1 = (m + 1) - 3 := by simpa using h1
      omega
  · rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply Fin.ext
      show j.val = m - 2
      have h1' : j.val + 1 = m - 1 := by simpa using h1
      omega
    · have h2' : m - 1 = (m + 1) - 1 := by simpa using h2
      omega

private theorem eq_finM2_of_label_three_finM {m : ℕ} (hm : 3 ≤ m) {j : Fin (m + 1)}
    (h : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM m) j = 3) : j = finM2 m := by
  rcases (CFSG.ClassicalInvolution.PhanDn.ggCoxeterMatrixD_eq_three_iff (by omega)
    (finM m) j).1 h with hE | hE
  · exact absurd (edgeD_lt (by omega) hE) (not_lt.mpr (Fin.le_last j))
  · rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h2' : (finM m).val + 1 < m + 1 := h2
      have hvm : (finM m).val = m := rfl
      omega
    · apply Fin.ext
      show j.val = m - 2
      have h1' : j.val = (m + 1) - 3 := h1
      omega

private def nodeSupp (m : ℕ) (i : Fin (m + 1)) : Set (Fin (m + 1)) :=
  {c | (i.val < m ∧ (c.val = i.val ∨ c.val = i.val + 1)) ∨
    (m ≤ i.val ∧ (c.val = m - 1 ∨ c.val = m))}

private theorem nodeSupp_chain {m : ℕ} (k : Fin m) :
    nodeSupp m (Fin.castSucc k) = {c : Fin (m + 1) | c.val = k.val ∨ c.val = k.val + 1} := by
  ext c
  simp only [nodeSupp, Set.mem_setOf_eq, Fin.val_castSucc]
  constructor
  · rintro (⟨-, h⟩ | ⟨hge, -⟩)
    · exact h
    · omega
  · exact fun h => Or.inl ⟨k.isLt, h⟩

private theorem nodeSupp_fork (m : ℕ) :
    nodeSupp m (finM m) = {c : Fin (m + 1) | c.val = m - 1 ∨ c.val = m} := by
  ext c
  simp only [nodeSupp, finM, Fin.val_last, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hlt, -⟩ | ⟨-, h⟩)
    · omega
    · exact h
  · exact fun h => Or.inr ⟨le_rfl, h⟩

private theorem nodeSupp_finM1 {m : ℕ} (hm : 3 ≤ m) :
    nodeSupp m (finM1 m) = {c : Fin (m + 1) | c.val = m - 1 ∨ c.val = m} := by
  ext c
  simp only [nodeSupp, Set.mem_setOf_eq]
  constructor
  · rintro (⟨-, h | h⟩ | ⟨hge, -⟩)
    · exact Or.inl h
    · exact Or.inr (by omega)
    · omega
  · rintro (h | h)
    · exact Or.inl ⟨by omega, Or.inl h⟩
    · exact Or.inl ⟨by omega, Or.inr (by omega)⟩

private theorem nodeSupp_finM2 {m : ℕ} (hm : 3 ≤ m) :
    nodeSupp m (finM2 m) = {c : Fin (m + 1) | c.val = m - 2 ∨ c.val = m - 1} := by
  ext c
  simp only [nodeSupp, Set.mem_setOf_eq]
  constructor
  · rintro (⟨-, h | h⟩ | ⟨hge, -⟩)
    · exact Or.inl h
    · exact Or.inr (by omega)
    · omega
  · rintro (h | h)
    · exact Or.inl ⟨by omega, Or.inl h⟩
    · exact Or.inl ⟨by omega, Or.inr (by omega)⟩

private theorem qTwoStdIota_single_of_not_mem_nodeSupp {m : ℕ} (hm : 3 ≤ m)
    (i : Fin (m + 1)) (a : Su K 2 1 2) {c : Fin (m + 1)} (hc : c ∉ nodeSupp m i) :
    ((qTwoStdIota E m hm i a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c (1 : K)) =
      Pi.single c (1 : K) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · have h1 : c.val ≠ k.val := by
      intro h
      exact hc (by simp only [nodeSupp_chain, Set.mem_setOf_eq]; exact Or.inl h)
    have h2 : c.val ≠ k.val + 1 := by
      intro h
      exact hc (by simp only [nodeSupp_chain, Set.mem_setOf_eq]; exact Or.inr h)
    rw [coe_qTwoStdIota, stdFamilyV_ι_castSucc]
    exact stdChainIota_single_of_not_mem k a h1 h2
  · have h1 : c.val ≠ m - 1 := by
      intro h
      exact hc (by simp only [nodeSupp_fork, Set.mem_setOf_eq]; exact Or.inl h)
    have h2 : c.val ≠ m := by
      intro h
      exact hc (by simp only [nodeSupp_fork, Set.mem_setOf_eq]; exact Or.inr h)
    rw [coe_qTwoStdIota, stdFamilyV_ι_last]
    exact stdForkIota_single_of_not_mem E hm a h1 h2

private theorem stdFamilyV_theta_eq_chainTheta_of_lt {m : ℕ} (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hij : i < j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3)
    (hi : i.val < m) (hj : j.val < m) :
    (stdFamilyV E m hm).θ i j =
      stdChainTheta (F := F) (f := 1) m ⟨i.val, hi⟩ (by
        show i.val + 1 < m
        omega) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · have hchain : i.val + 1 = j'.val := by
      have hE : edgeD (m + 1) i (Fin.castSucc j') := by
        rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.castSucc j')).1 hM
          with h | h
        · exact h
        · exact absurd (edgeD_lt (by omega) h) (not_lt.mpr (le_of_lt hij))
      rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
      rcases hE with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · simp only [Fin.val_castSucc] at h2
        omega
    rw [stdFamilyV_θ, stdTheta_castSucc, stdThetaAt_eq_chainTheta hchain hi]
  · simp only [Fin.val_last] at hj
    omega

private theorem qTwoStdTheta_single_of_not_mem_nodes_of_lt {m : ℕ} (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hij : i < j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) (a : Su K 2 1 3)
    {c : Fin (m + 1)} (hi : c ∉ nodeSupp m i) (hj : c ∉ nodeSupp m j) :
    ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c (1 : K)) =
      Pi.single c (1 : K) := by
  rw [coe_qTwoStdTheta_of_lt E m hm hij]
  rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
  · have hi_lt : i.val < m := by
      have h1 : i.val < (Fin.castSucc j').val := Fin.lt_def.mp hij
      rw [Fin.val_castSucc] at h1
      omega
    have hchain : i.val + 1 = j'.val := by
      have hE : edgeD (m + 1) i (Fin.castSucc j') := by
        rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.castSucc j')).1 hM
          with h | h
        · exact h
        · exact absurd (edgeD_lt (by omega) h) (not_lt.mpr (le_of_lt hij))
      rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
      rcases hE with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · simp only [Fin.val_castSucc] at h2
        omega
    have hii : i = Fin.castSucc ⟨i.val, hi_lt⟩ := Fin.ext rfl
    rw [stdFamilyV_θ, stdTheta_castSucc, stdThetaAt_eq_chainTheta hchain hi_lt]
    have hci : c.val ≠ i.val ∧ c.val ≠ i.val + 1 := by
      rw [hii, nodeSupp_chain] at hi
      simpa using hi
    have hcj : c.val ≠ j'.val ∧ c.val ≠ j'.val + 1 := by
      rw [nodeSupp_chain] at hj
      simpa using hj
    have hcj2 : c.val ≠ i.val + 2 := by
      intro h
      exact hcj.2 (by omega)
    refine stdChainTheta_single_of_not_mem (k := ⟨i.val, hi_lt⟩) (hk := by
      show i.val + 1 < m
      omega) (a := a) ?_
    rintro ⟨hle, hlt⟩
    change i.val ≤ c.val at hle
    change c.val < i.val + 3 at hlt
    rcases eq_or_ne c.val i.val with h | h
    · exact hci.1 h
    rcases eq_or_ne c.val (i.val + 1) with h' | h'
    · exact hci.2 h'
    rcases eq_or_ne c.val (i.val + 2) with h'' | h''
    · exact hcj2 h''
    · omega
  · have hE : edgeD (m + 1) i (Fin.last m) := by
      rcases (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) i (Fin.last m)).1 hM
        with h | h
      · exact h
      · exact absurd (edgeD_lt (by omega) h) (not_lt.mpr (le_of_lt hij))
    rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)] at hE
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Fin.val_last] at h2
      omega
    · have hi_eq : i = finM2 m := by
        apply Fin.ext
        show i.val = m - 2
        omega
      rw [stdFamilyV_θ, stdTheta_last]
      rw [hi_eq, nodeSupp_finM2 hm] at hi
      have hci : c.val ≠ m - 2 ∧ c.val ≠ m - 1 := by
        simpa using hi
      rw [nodeSupp_fork] at hj
      have hcj : c.val ≠ m - 1 ∧ c.val ≠ m := by
        simpa using hj
      exact stdForkTheta_single_of_not_mem E hm a hci.1 hci.2 hcj.2

private theorem qTwoStdTheta_single_of_not_mem_nodes {m : ℕ} (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3)
    (a : Su K 2 1 3) {c : Fin (m + 1)} (hi : c ∉ nodeSupp m i) (hj : c ∉ nodeSupp m j) :
    ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c (1 : K)) =
      Pi.single c (1 : K) := by
  have hne : i ≠ j := by
    rintro rfl
    have h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i i = 1 :=
      (CFSG.StandardType.ggCoxeterMatrixD (m + 1)).diagonal i
    rw [h1] at hM
    omega
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact qTwoStdTheta_single_of_not_mem_nodes_of_lt E hm hl hM a hi hj
  · rw [qTwoStdTheta_of_gt E m hm hl, MonoidHom.comp_apply]
    exact qTwoStdTheta_single_of_not_mem_nodes_of_lt E hm hl (label_three_symm hM)
      (revSU3 K 2 1 a) hj hi

private theorem qTwoStdTheta_smul_of_lt {m : ℕ} (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hij : i < j)
    (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3)
    (hi : i.val < m) (hj : j.val < m) (a : Su K 2 1 3) (c : K)
    (v : Fin (m + 1) → K) :
    ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (c • v) =
      c • ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived
        (Qn E (m + 1)))) : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v := by
  rw [coe_qTwoStdTheta_of_lt E m hm hij,
    stdFamilyV_theta_eq_chainTheta_of_lt E hm hij hM hi hj]
  exact stdChainTheta_smul (k := ⟨i.val, hi⟩) (hk := by
    show i.val + 1 < m
    omega) a c v

private theorem qTwoStdTheta_smul {m : ℕ} (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3)
    (hi : i.val < m) (hj : j.val < m) (a : Su K 2 1 3) (c : K)
    (v : Fin (m + 1) → K) :
    ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (c • v) =
      c • ((qTwoStdTheta E m hm i j a : ↥(CFSG.RankThree.Classical2.orthDerived
        (Qn E (m + 1)))) : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v := by
  have hne : i ≠ j := by
    rintro rfl
    have h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i i = 1 :=
      (CFSG.StandardType.ggCoxeterMatrixD (m + 1)).diagonal i
    rw [h1] at hM
    omega
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact qTwoStdTheta_smul_of_lt E hm hl hM hi hj a c v
  · rw [qTwoStdTheta_of_gt E m hm hl]
    exact qTwoStdTheta_smul_of_lt E hm hl (label_three_symm hM) hj hi
      (revSU3 K 2 1 a) c v


private def kLinSubgroup (m : ℕ) :
    Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) where
  carrier := {g | ∀ (c : K) (v : Fin (m + 1) → K), g.val (c • v) = c • g.val v}
  one_mem' := by
    intro c v
    rfl
  mul_mem' := by
    intro x y hx hy c v
    change (x.val * y.val) (c • v) = c • (x.val * y.val) v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx c v
    change (x.val)⁻¹ (c • v) = c • (x.val)⁻¹ v
    apply x.val.injective
    change x.val ((x.val).symm (c • v)) = x.val (c • (x.val).symm v)
    calc x.val ((x.val).symm (c • v)) = c • v :=
          LinearEquiv.apply_symm_apply x.val (c • v)
      _ = c • x.val ((x.val).symm v) := by rw [LinearEquiv.apply_symm_apply]
      _ = x.val (c • (x.val).symm v) := (hx c ((x.val).symm v)).symm

private def fixSubgroup (m : ℕ) (c : Fin (m + 1)) :
    Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) where
  carrier := {g | g.val (Pi.single c (1 : K)) = Pi.single c (1 : K)}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change (x.val * y.val) (Pi.single c (1 : K)) = Pi.single c (1 : K)
    rw [LinearEquiv.mul_apply, hy, hx]
  inv_mem' := by
    intro x hx
    change (x.val)⁻¹ (Pi.single c (1 : K)) = Pi.single c (1 : K)
    apply x.val.injective
    change x.val ((x.val).symm (Pi.single c (1 : K))) = x.val (Pi.single c (1 : K))
    calc x.val ((x.val).symm (Pi.single c (1 : K))) = Pi.single c (1 : K) :=
          LinearEquiv.apply_symm_apply x.val (Pi.single c (1 : K))
      _ = x.val (Pi.single c (1 : K)) := hx.symm

private theorem qTwoStdIota_smul_of_not_last {m : ℕ} (hm : 3 ≤ m)
    {i : Fin (m + 1)} (hi : i ≠ finM m) (a : Su K 2 1 2) (c : K)
    (v : Fin (m + 1) → K) :
    ((qTwoStdIota E m hm i a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (c • v) =
      c • ((qTwoStdIota E m hm i a : ↥(CFSG.RankThree.Classical2.orthDerived
        (Qn E (m + 1)))) : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) v := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
  · rw [coe_qTwoStdIota, stdFamilyV_ι_castSucc]
    exact stdChainIota_smul k a c v
  · exact absurd rfl hi

private theorem levi_le_kLin (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    (C : Set (Fin (m + 1))) (hmC : finM m ∉ C) :
    (qTwoStdFamily E hK m hm).levi C ≤ kLinSubgroup E m := by
  unfold QTwoPhanFamily.levi
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => ?_
    rintro x ⟨a, rfl⟩
    have hi' : i ≠ finM m := fun h => hmC (h ▸ hi)
    intro c v
    exact qTwoStdIota_smul_of_not_last E hm hi' a c v
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
      iSup_le fun hij => ?_
    rintro x ⟨a, rfl⟩
    have hi' : i.val < m := by
      have hne : i ≠ finM m := fun h => hmC (h ▸ hi)
      have h : i.val ≠ m := by
        intro h
        exact hne (Fin.ext h)
      have := i.isLt
      omega
    have hj' : j.val < m := by
      have hne : j ≠ finM m := fun h => hmC (h ▸ hj)
      have h : j.val ≠ m := by
        intro h
        exact hne (Fin.ext h)
      have := j.isLt
      omega
    intro c v
    exact qTwoStdTheta_smul E hm hij hi' hj' a c v

private def CSupp (m : ℕ) (C : Set (Fin (m + 1))) : Set (Fin (m + 1)) :=
  {c | ∃ i ∈ C, c ∈ nodeSupp m i}

private theorem levi_le_fix (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    (C : Set (Fin (m + 1))) {c : Fin (m + 1)} (hc : c ∉ CSupp m C) :
    (qTwoStdFamily E hK m hm).levi C ≤ fixSubgroup E m c := by
  unfold QTwoPhanFamily.levi
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => ?_
    rintro x ⟨a, rfl⟩
    exact qTwoStdIota_single_of_not_mem_nodeSupp E hm i a (fun h => hc ⟨i, hi, h⟩)
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
      iSup_le fun hij => ?_
    rintro x ⟨a, rfl⟩
    exact qTwoStdTheta_single_of_not_mem_nodes E hm hij a
      (fun h => hc ⟨i, hi, h⟩) (fun h => hc ⟨j, hj, h⟩)


private theorem mem_sup_of_commute {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (hc : ∀ h ∈ H₁, ∀ k ∈ H₂, h * k = k * h) {x : G} (hx : x ∈ H₁ ⊔ H₂) :
    ∃ h ∈ H₁, ∃ k ∈ H₂, x = h * k := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H₁, ∃ k ∈ H₂, x = h * k}
      one_mem' := ⟨1, H₁.one_mem, 1, H₂.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro x y ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H₁.mul_mem hh₁ hh₂, k₁ * k₂, H₂.mul_mem hk₁ hk₂, ?_⟩
        calc (h₁ * k₁) * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [(hc h₂ hh₂ k₁ hk₁).symm]
          _ = (h₁ * h₂) * (k₁ * k₂) := by group
      inv_mem' := by
        rintro x ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H₁.inv_mem hh, k⁻¹, H₂.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact (hc h⁻¹ (H₁.inv_mem hh) k⁻¹ (H₂.inv_mem hk)).symm }
  have hle : H₁ ⊔ H₂ ≤ S := by
    refine sup_le ?_ ?_
    · intro h hh
      exact ⟨h, hh, 1, H₂.one_mem, (mul_one h).symm⟩
    · intro k hk
      exact ⟨1, H₁.one_mem, k, hk, (one_mul k).symm⟩
  exact hle hx

private theorem levi_le_sup_of_isolated {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} {M : CoxeterMatrix (Fin n)} {X : Type} [Group X]
    (S : QTwoPhanFamily K M X) (C : Set (Fin n)) (k : Fin n) (hkC : k ∈ C)
    (hiso : ∀ j ∈ C, M k j ≠ 3) :
    S.levi C ≤ (S.ι k).range ⊔ S.levi (C \ {k}) := by
  rw [QTwoPhanFamily.levi]
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => ?_
    by_cases hik : i = k
    · subst hik
      exact le_sup_left
    · have hi' : i ∈ C \ {k} := ⟨hi, by simpa using hik⟩
      exact (S.le_levi_node hi').trans le_sup_right
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
      iSup_le fun hij => ?_
    have hik : i ≠ k := by
      intro h
      exact hiso j hj (h ▸ hij)
    have hjk : j ≠ k := by
      intro h
      exact hiso i hi (h ▸ ((M.symmetric j i).trans hij))
    have hi' : i ∈ C \ {k} := ⟨hi, by simpa using hik⟩
    have hj' : j ∈ C \ {k} := ⟨hj, by simpa using hjk⟩
    exact (S.le_levi_edge hi' hj' hij).trans le_sup_right

private theorem eq_fork_pair_of_common_support {m : ℕ} (hm : 3 ≤ m) {i j : Fin (m + 1)}
    (h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2) {c : Fin (m + 1)}
    (hci : c ∈ nodeSupp m i) (hcj : c ∈ nodeSupp m j) (hij : i ≠ j) :
    (i = finM1 m ∧ j = finM m) ∨ (i = finM m ∧ j = finM1 m) := by
  rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨a, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨b, rfl⟩ | rfl
    · rw [nodeSupp_chain] at hci hcj
      simp only [Set.mem_setOf_eq] at hci hcj
      have hedge : edgeD (m + 1) (Fin.castSucc a) (Fin.castSucc b) ∨
          edgeD (m + 1) (Fin.castSucc b) (Fin.castSucc a) := by
        rcases hci with h | h <;> rcases hcj with h' | h'
        · exact absurd (Fin.ext (by show a.val = b.val; omega)) hij
        · right
          rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
          exact Or.inl ⟨by show b.val + 1 = a.val; omega,
            by show a.val + 1 < m + 1; omega⟩
        · left
          rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
          exact Or.inl ⟨by show a.val + 1 = b.val; omega,
            by show b.val + 1 < m + 1; omega⟩
        · exact absurd (Fin.ext (by show a.val = b.val; omega)) hij
      have h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.castSucc a) (Fin.castSucc b) = 3 :=
        (ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1) _ _).2 hedge
      rw [h3] at h2
      exact (by omega : False).elim
    · rw [nodeSupp_chain] at hci
      rw [nodeSupp_fork] at hcj
      simp only [Set.mem_setOf_eq] at hci hcj
      have hcases : a.val = m - 1 ∨ a.val = m - 2 := by omega
      rcases hcases with h | h
      · left
        refine ⟨Fin.ext (by show a.val = m - 1; exact h), rfl⟩
      · have h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.castSucc a) (Fin.last m) = 3 := by
          rw [ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1)]
          left
          rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
          refine Or.inr ⟨?_, ?_⟩
          · show a.val = (m + 1) - 3
            omega
          · show m = (m + 1) - 1
            omega
        rw [h3] at h2
        exact (by omega : False).elim
  · rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨b, rfl⟩ | rfl
    · rw [nodeSupp_fork] at hci
      rw [nodeSupp_chain] at hcj
      simp only [Set.mem_setOf_eq] at hci hcj
      have hcases : b.val = m - 1 ∨ b.val = m - 2 := by omega
      rcases hcases with h | h
      · right
        refine ⟨rfl, Fin.ext (by show b.val = m - 1; exact h)⟩
      · have h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (Fin.last m) (Fin.castSucc b) = 3 := by
          rw [ggCoxeterMatrixD_eq_three_iff (by omega : 4 ≤ m + 1)]
          right
          rw [edgeD_iff_of_four_le (by omega : 4 ≤ m + 1)]
          refine Or.inr ⟨?_, ?_⟩
          · show b.val = (m + 1) - 3
            omega
          · show m = (m + 1) - 1
            omega
        rw [h3] at h2
        exact (by omega : False).elim
    · exact absurd rfl hij


private theorem label_three_finM1_finM2 {m : ℕ} (hm : 3 ≤ m) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM1 m) (finM2 m) = 3 :=
  label_three_symm (label_three_finM2_finM1 hm)

private theorem qTwoStdIota_range_inf_eq_bot (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    ((qTwoStdFamily E hK m hm).ι i).range ⊓
      ((qTwoStdFamily E hK m hm).ι j).range = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx1 : ((x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      ((stdFamilyV E m hm).ι i).range := by
    obtain ⟨a, ha⟩ := (Subgroup.mem_inf.mp hx).1
    refine ⟨a, ?_⟩
    rw [← ha]
    exact coe_qTwoStdIota E m hm i a
  have hx2 : ((x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      ((stdFamilyV E m hm).ι j).range := by
    obtain ⟨a, ha⟩ := (Subgroup.mem_inf.mp hx).2
    refine ⟨a, ?_⟩
    rw [← ha]
    exact coe_qTwoStdIota E m hm j a
  have hzero : ((x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      (⊥ : Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) := by
    rw [← stdFamilyV_disj E hm i j hij]
    exact Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot] at hzero
  exact Subtype.ext hzero

private theorem levi_le_centralizer_iota (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {k : Fin (m + 1)} {C : Set (Fin (m + 1))} (hkC : k ∉ C)
    (hiso : ∀ j ∈ C, CFSG.StandardType.ggCoxeterMatrixD (m + 1) k j ≠ 3) :
    (qTwoStdFamily E hK m hm).levi C ≤
      Subgroup.centralizer (((qTwoStdFamily E hK m hm).ι k).range :
        Set ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
  rw [QTwoPhanFamily.levi]
  refine sup_le ?_ ?_
  · refine iSup_le fun i => iSup_le fun hi => ?_
    intro y hy
    obtain ⟨a, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    have hik : i ≠ k := fun h => hkC (h ▸ hi)
    have h2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i k = 2 := by
      rcases ggCoxeterMatrixD_two_or_three i k hik with h | h
      · exact h
      · exact absurd (label_three_symm h) (hiso i hi)
    exact ((qTwoStdFamily E hK m hm).comm i k h2 a b).symm
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj =>
      iSup_le fun hij => ?_
    intro y hy
    obtain ⟨a, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := hx
    have hik : i ≠ k := fun h => hkC (h ▸ hi)
    have hjk : j ≠ k := fun h => hkC (h ▸ hj)
    have hik2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k i = 2 := by
      rcases ggCoxeterMatrixD_two_or_three k i (Ne.symm hik) with h | h
      · exact h
      · exact absurd h (hiso i hi)
    have hjk2 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) k j = 2 := by
      rcases ggCoxeterMatrixD_two_or_three k j (Ne.symm hjk) with h | h
      · exact h
      · exact absurd h (hiso j hj)
    exact (qTwoStdFamily E hK m hm).farNodeEdge k i j hij hik2 hjk2 b a

private theorem val_le_of_mem_diff_finM1 {m : ℕ} (hm : 3 ≤ m) {i : Fin (m + 1)}
    {C : Set (Fin (m + 1))} (hi : i ∈ C \ {finM1 m}) (hmC : finM m ∉ C)
    (hm2 : finM2 m ∉ C) : i.val ≤ m - 3 := by
  have hiC : i ∈ C := hi.1
  have hne1 : i ≠ finM1 m := fun h => hi.2 (by simpa using h)
  have hne2 : i ≠ finM2 m := fun h => hm2 (h ▸ hiC)
  have hne3 : i ≠ finM m := fun h => hmC (h ▸ hiC)
  have hval1 : i.val ≠ m - 1 := fun h => hne1 (Fin.ext h)
  have hval2 : i.val ≠ m - 2 := fun h => hne2 (Fin.ext h)
  have hval3 : i.val ≠ m := fun h => hne3 (Fin.ext h)
  have := i.isLt
  omega

private theorem val_le_of_mem_diff_finM {m : ℕ} (hm : 3 ≤ m) {i : Fin (m + 1)}
    {C : Set (Fin (m + 1))} (hi : i ∈ C \ {finM m}) (hm1 : finM1 m ∉ C)
    (hm2 : finM2 m ∉ C) : i.val ≤ m - 3 := by
  have hiC : i ∈ C := hi.1
  have hne3 : i ≠ finM m := fun h => hi.2 (by simpa using h)
  have hne1 : i ≠ finM1 m := fun h => hm1 (h ▸ hiC)
  have hne2 : i ≠ finM2 m := fun h => hm2 (h ▸ hiC)
  have hval1 : i.val ≠ m - 1 := fun h => hne1 (Fin.ext h)
  have hval2 : i.val ≠ m - 2 := fun h => hne2 (Fin.ext h)
  have hval3 : i.val ≠ m := fun h => hne3 (Fin.ext h)
  have := i.isLt
  omega

private theorem eq_one_of_mem_levi_low (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))} (hC : ∀ i ∈ C, i.val ≤ m - 3)
    {a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (haC : a ∈ (qTwoStdFamily E hK m hm).levi C)
    (hafix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      ((a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c (1 : K)) =
        Pi.single c (1 : K)) : a = 1 := by
  have haK : a ∈ kLinSubgroup E m := by
    refine levi_le_kLin E hK hm C ?_ haC
    intro h
    have := hC (finM m) h
    simp only [finM_val] at this
    omega
  have hfixall : ∀ c : Fin (m + 1), ((a : ↥(CFSG.RankThree.Classical2.orthDerived
        (Qn E (m + 1)))) : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    intro c
    by_cases hc : c.val ≤ m - 2
    · exact hafix c hc
    · have hcC : c ∉ CSupp m C := by
        rintro ⟨i, hi, hci⟩
        have hival : i.val ≤ m - 3 := hC i hi
        have hi_lt : i.val < m := by omega
        have hci' : c.val = i.val ∨ c.val = i.val + 1 := by
          have h := hci
          rw [show i = Fin.castSucc ⟨i.val, hi_lt⟩ from Fin.ext rfl, nodeSupp_chain] at h
          simpa using h
        omega
      exact levi_le_fix E hK hm C hcC haC
  exact Subtype.ext (eq_one_of_forall_single (fun c v => haK c v) hfixall)


private theorem fixes_of_mem_levi_pair (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C₁ C₂ : Set (Fin (m + 1))} (hdisj : Disjoint C₁ C₂)
    (hlabel : ∀ i ∈ C₁, ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    {g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hg1 : g ∈ (qTwoStdFamily E hK m hm).levi C₁)
    (hg2 : g ∈ (qTwoStdFamily E hK m hm).levi C₂) :
    ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      g.val (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
  intro c hc
  by_cases hc1 : c ∈ CSupp m C₁
  · have hc2 : c ∉ CSupp m C₂ := by
      rintro ⟨j, hj, hcj⟩
      obtain ⟨i, hi, hci⟩ := hc1
      have hij : i ≠ j := by
        rintro rfl
        exact (Set.disjoint_left.mp hdisj) hi hj
      rcases eq_fork_pair_of_common_support hm (hlabel i hi j hj) hci hcj hij with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [nodeSupp_finM1 hm] at hci
        simp only [Set.mem_setOf_eq] at hci
        omega
      · rw [nodeSupp_fork] at hci
        simp only [Set.mem_setOf_eq] at hci
        omega
    exact levi_le_fix E hK hm C₂ hc2 hg2
  · exact levi_le_fix E hK hm C₁ hc1 hg1

private theorem eq_one_of_mul_fork_left (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C₁ C₂ : Set (Fin (m + 1))} (h2 : finM m ∈ C₂)
    (hdisj : Disjoint C₁ C₂)
    (hlabel : ∀ i ∈ C₁, ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    {g g1 a : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hga : g = g1 * a) (hg1H : g1 ∈ ((qTwoStdFamily E hK m hm).ι (finM1 m)).range)
    (haA : a ∈ (qTwoStdFamily E hK m hm).levi (C₁ \ {finM1 m}))
    (hgfix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      g.val (Pi.single c (1 : K)) = Pi.single c (1 : K)) : a = 1 := by
  have hM_not_C1 : finM m ∉ C₁ := fun hh => (Set.disjoint_left.mp hdisj) hh h2
  have hm2_not_C1 : finM2 m ∉ C₁ := by
    intro h
    have hh := hlabel (finM2 m) h (finM m) h2
    rw [label_three_finM2_finM hm] at hh
    omega
  have hg1fix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      g1.val (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    intro c hc
    obtain ⟨d, rfl⟩ := hg1H
    exact qTwoStdIota_single_of_not_mem_nodeSupp E hm (finM1 m) d (by
      rw [nodeSupp_finM1 hm]
      simp only [Set.mem_setOf_eq, not_or]
      exact ⟨by omega, by omega⟩)
  have hafix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      a.val (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    intro c hc
    have hg1c := hg1fix c hc
    have hgc := hgfix c hc
    have haeq : a = g1⁻¹ * g := by rw [hga]; group
    have hcoea : a.val = (g1.val)⁻¹ * g.val := by
      rw [haeq, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoea, LinearEquiv.mul_apply, hgc]
    change (g1.val).symm (Pi.single c (1 : K)) = Pi.single c (1 : K)
    rw [LinearEquiv.symm_apply_eq]
    exact hg1c.symm
  refine eq_one_of_mem_levi_low E hK hm ?_ haA hafix
  intro i hi
  exact val_le_of_mem_diff_finM1 hm hi hM_not_C1 hm2_not_C1

private theorem eq_one_of_mul_fork_right (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C₁ C₂ : Set (Fin (m + 1))} (h1 : finM1 m ∈ C₁)
    (hdisj : Disjoint C₁ C₂)
    (hlabel : ∀ i ∈ C₁, ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    {g g2 b : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hgb : g = g2 * b) (hg2H : g2 ∈ ((qTwoStdFamily E hK m hm).ι (finM m)).range)
    (hbB : b ∈ (qTwoStdFamily E hK m hm).levi (C₂ \ {finM m}))
    (hgfix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      g.val (Pi.single c (1 : K)) = Pi.single c (1 : K)) : b = 1 := by
  have hM1_not_C2 : finM1 m ∉ C₂ := fun hh => (Set.disjoint_left.mp hdisj) h1 hh
  have hm2_not_C2 : finM2 m ∉ C₂ := by
    intro h
    have hh := hlabel (finM1 m) h1 (finM2 m) h
    rw [label_three_finM1_finM2 hm] at hh
    omega
  have hg2fix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      g2.val (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    intro c hc
    obtain ⟨d, rfl⟩ := hg2H
    exact qTwoStdIota_single_of_not_mem_nodeSupp E hm (finM m) d (by
      rw [nodeSupp_fork]
      simp only [Set.mem_setOf_eq, not_or]
      exact ⟨by omega, by omega⟩)
  have hbfix : ∀ c : Fin (m + 1), c.val ≤ m - 2 →
      b.val (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    intro c hc
    have hg2c := hg2fix c hc
    have hgc := hgfix c hc
    have hbeq : b = g2⁻¹ * g := by rw [hgb]; group
    have hcoeb : b.val = (g2.val)⁻¹ * g.val := by
      rw [hbeq, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoeb, LinearEquiv.mul_apply, hgc]
    change (g2.val).symm (Pi.single c (1 : K)) = Pi.single c (1 : K)
    rw [LinearEquiv.symm_apply_eq]
    exact hg2c.symm
  refine eq_one_of_mem_levi_low E hK hm ?_ hbB hbfix
  intro i hi
  exact val_le_of_mem_diff_finM hm hi hM1_not_C2 hm2_not_C2

private theorem levi_inf_levi_eq_bot_of_fork_pair (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C₁ C₂ : Set (Fin (m + 1))} (h1 : finM1 m ∈ C₁) (h2 : finM m ∈ C₂)
    (hdisj : Disjoint C₁ C₂)
    (hlabel : ∀ i ∈ C₁, ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2) :
    (qTwoStdFamily E hK m hm).levi C₁ ⊓ (qTwoStdFamily E hK m hm).levi C₂ = ⊥ := by
  have hM_not_C1 : finM m ∉ C₁ := fun hh => (Set.disjoint_left.mp hdisj) hh h2
  have hm2_not_C1 : finM2 m ∉ C₁ := by
    intro h
    have hh := hlabel (finM2 m) h (finM m) h2
    rw [label_three_finM2_finM hm] at hh
    omega
  have hm2_not_C2 : finM2 m ∉ C₂ := by
    intro h
    have hh := hlabel (finM1 m) h1 (finM2 m) h
    rw [label_three_finM1_finM2 hm] at hh
    omega
  have hiso1 : ∀ j ∈ C₁, CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM1 m) j ≠ 3 := by
    intro j hj h3
    exact hm2_not_C1 (by rw [eq_finM2_of_label_three_finM1 hm h3] at hj; exact hj)
  have hiso2 : ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) (finM m) j ≠ 3 := by
    intro j hj h3
    exact hm2_not_C2 (by rw [eq_finM2_of_label_three_finM hm h3] at hj; exact hj)
  have hle1 := levi_le_sup_of_isolated (qTwoStdFamily E hK m hm) C₁ (finM1 m) h1 hiso1
  have hle2 := levi_le_sup_of_isolated (qTwoStdFamily E hK m hm) C₂ (finM m) h2 hiso2
  have hcent1 : (qTwoStdFamily E hK m hm).levi (C₁ \ {finM1 m}) ≤
      Subgroup.centralizer (((qTwoStdFamily E hK m hm).ι (finM1 m)).range :
        Set ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
    refine levi_le_centralizer_iota E hK hm ?_ ?_
    · simp
    · intro j hj
      exact hiso1 j hj.1
  have hcent2 : (qTwoStdFamily E hK m hm).levi (C₂ \ {finM m}) ≤
      Subgroup.centralizer (((qTwoStdFamily E hK m hm).ι (finM m)).range :
        Set ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) := by
    refine levi_le_centralizer_iota E hK hm ?_ ?_
    · simp
    · intro j hj
      exact hiso2 j hj.1
  have hcomm1 : ∀ x ∈ ((qTwoStdFamily E hK m hm).ι (finM1 m)).range,
      ∀ y ∈ (qTwoStdFamily E hK m hm).levi (C₁ \ {finM1 m}), x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent1 hy)) x hx
  have hcomm2 : ∀ x ∈ ((qTwoStdFamily E hK m hm).ι (finM m)).range,
      ∀ y ∈ (qTwoStdFamily E hK m hm).levi (C₂ \ {finM m}), x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent2 hy)) x hx
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg1 : g ∈ (qTwoStdFamily E hK m hm).levi C₁ := (Subgroup.mem_inf.mp hg).1
  have hg2 : g ∈ (qTwoStdFamily E hK m hm).levi C₂ := (Subgroup.mem_inf.mp hg).2
  obtain ⟨g1, hg1H, a, haA, hga⟩ := mem_sup_of_commute hcomm1 (hle1 hg1)
  obtain ⟨g2, hg2H, b, hbB, hgb⟩ := mem_sup_of_commute hcomm2 (hle2 hg2)
  have hgfix := fixes_of_mem_levi_pair E hK hm hdisj hlabel hg1 hg2
  have haone : a = 1 := eq_one_of_mul_fork_left E hK hm h2 hdisj hlabel hga hg1H haA hgfix
  have hbone : b = 1 := eq_one_of_mul_fork_right E hK hm h1 hdisj hlabel hgb hg2H hbB hgfix
  have hg_eq1 : g = g1 := by rw [hga, haone, mul_one]
  have hg_eq2 : g = g2 := by rw [hgb, hbone, mul_one]
  have hne : finM1 m ≠ finM m := by
    intro h
    have hh : (finM1 m).val = (finM m).val := congrArg Fin.val h
    have h1' : (finM1 m).val = m - 1 := rfl
    have h2' : (finM m).val = m := rfl
    omega
  have hbot : ((qTwoStdFamily E hK m hm).ι (finM1 m)).range ⊓
      ((qTwoStdFamily E hK m hm).ι (finM m)).range = ⊥ :=
    qTwoStdIota_range_inf_eq_bot E hK hm hne
  have hmem : g ∈ ((qTwoStdFamily E hK m hm).ι (finM1 m)).range ⊓
      ((qTwoStdFamily E hK m hm).ι (finM m)).range := by
    rw [Subgroup.mem_inf]
    exact ⟨hg_eq1 ▸ hg1H, hg_eq2 ▸ hg2H⟩
  rw [hbot] at hmem
  simpa using hmem

private theorem levi_inf_levi_eq_bot_of_disjoint_supp (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C₁ C₂ : Set (Fin (m + 1))} (hmC1 : finM m ∉ C₁) (hdisj : Disjoint C₁ C₂)
    (hlabel : ∀ i ∈ C₁, ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2)
    (hno : ¬ ((finM1 m ∈ C₁ ∧ finM m ∈ C₂) ∨ (finM m ∈ C₁ ∧ finM1 m ∈ C₂))) :
    (qTwoStdFamily E hK m hm).levi C₁ ⊓ (qTwoStdFamily E hK m hm).levi C₂ = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg1 : g ∈ (qTwoStdFamily E hK m hm).levi C₁ := (Subgroup.mem_inf.mp hg).1
  have hg2 : g ∈ (qTwoStdFamily E hK m hm).levi C₂ := (Subgroup.mem_inf.mp hg).2
  have hKlin : g ∈ kLinSubgroup E m := levi_le_kLin E hK hm C₁ hmC1 hg1
  have hfix : ∀ c : Fin (m + 1), g.val (Pi.single c (1 : K)) = Pi.single c (1 : K) := by
    intro c
    by_cases hc1 : c ∈ CSupp m C₁
    · have hc2 : c ∉ CSupp m C₂ := by
        rintro ⟨j, hj, hcj⟩
        obtain ⟨i, hi, hci⟩ := hc1
        have hij : i ≠ j := by
          rintro rfl
          exact (Set.disjoint_left.mp hdisj) hi hj
        rcases eq_fork_pair_of_common_support hm (hlabel i hi j hj) hci hcj hij with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hno (Or.inl ⟨hi, hj⟩)
        · exact hno (Or.inr ⟨hi, hj⟩)
      exact levi_le_fix E hK hm C₂ hc2 hg2
    · exact levi_le_fix E hK hm C₁ hc1 hg1
  exact Subtype.ext (eq_one_of_forall_single (fun c v => hKlin c v) hfix)

theorem qTwoStdFamily_ι_inj (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (i : Fin (m + 1)) :
    Function.Injective ((qTwoStdFamily E hK m hm).ι i) := by
  change Function.Injective (qTwoStdIota E m hm i)
  intro a b hab
  apply stdFamilyV_inj E hm i
  have h := congrArg (fun x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) =>
    ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) hab
  simpa only [coe_qTwoStdIota] using h

theorem qTwoStdFamily_θ_inj (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (i j : Fin (m + 1)) (hM : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3) :
    Function.Injective ((qTwoStdFamily E hK m hm).θ i j) := by
  have hne : i ≠ j := by
    rintro rfl
    have h1 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i i = 1 :=
      (CFSG.StandardType.ggCoxeterMatrixD (m + 1)).diagonal i
    rw [h1] at hM
    omega
  rcases lt_or_gt_of_ne hne with hij | hji
  · change Function.Injective (qTwoStdTheta E m hm i j)
    intro a b hab
    apply stdFamilyV_θ_inj E hm i j hij hM
    have h := congrArg (fun x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) =>
      ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) hab
    simpa only [coe_qTwoStdTheta_of_lt E m hm hij] using h
  · have hsymm : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 := label_three_symm hM
    have hinj : Function.Injective (qTwoStdTheta E m hm j i) := by
      intro a b hab
      apply stdFamilyV_θ_inj E hm j i hji hsymm
      have h := congrArg (fun x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) =>
        ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) hab
      simpa only [coe_qTwoStdTheta_of_lt E m hm hji] using h
    change Function.Injective (qTwoStdTheta E m hm i j)
    rw [qTwoStdTheta_of_gt E m hm hji]
    intro a b hab
    exact (revSU3 K 2 1).injective (hinj hab)

theorem qTwoStdFamily_split (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    ∀ C₁ C₂ : Set (Fin (m + 1)),
      C₁ ∪ C₂ ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)) →
      Disjoint C₁ C₂ →
      (∀ i ∈ C₁, ∀ j ∈ C₂, CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2) →
      (qTwoStdFamily E hK m hm).levi C₁ ⊓ (qTwoStdFamily E hK m hm).levi C₂ = ⊥ := by
  intro C₁ C₂ _hshape hdisj hlabel
  by_cases hcase : (finM1 m ∈ C₁ ∧ finM m ∈ C₂) ∨ (finM m ∈ C₁ ∧ finM1 m ∈ C₂)
  · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact levi_inf_levi_eq_bot_of_fork_pair E hK hm h1 h2 hdisj hlabel
    · rw [inf_comm]
      exact levi_inf_levi_eq_bot_of_fork_pair E hK hm h2 h1 hdisj.symm
        (fun i hi j hj =>
          ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply j i).trans
            (hlabel j hj i hi))
  · by_cases hmC1 : finM m ∈ C₁
    · have hmC2 : finM m ∉ C₂ := fun h => (Set.disjoint_left.mp hdisj) hmC1 h
      have hno' : ¬ ((finM1 m ∈ C₂ ∧ finM m ∈ C₁) ∨ (finM m ∈ C₂ ∧ finM1 m ∈ C₁)) := by
        intro h
        exact hcase (by
          rcases h with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · exact Or.inr ⟨h2', h1'⟩
          · exact Or.inl ⟨h2', h1'⟩)
      rw [inf_comm]
      exact levi_inf_levi_eq_bot_of_disjoint_supp E hK hm hmC2 hdisj.symm
        (fun i hi j hj =>
          ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply j i).trans
            (hlabel j hj i hi)) hno'
    · exact levi_inf_levi_eq_bot_of_disjoint_supp E hK hm hmC1 hdisj hlabel hcase

theorem qTwoStdFamily_faithful (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m) :
    (qTwoStdFamily E hK m hm).Faithful := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact qTwoStdFamily_ι_inj E hK m hm i
  · intro i j hM
    exact qTwoStdFamily_θ_inj E hK m hm i j hM
  · intro C₁ C₂ hshape hdisj hlabel
    exact qTwoStdFamily_split E hK m hm C₁ C₂ hshape hdisj hlabel

theorem qTwoStdFamily_levi_single_of_lt (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))} {k : ℕ} (hC : ∀ i ∈ C, i.val < k) {c : Fin (m + 1)}
    (hc : k < c.val) {g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hg : g ∈ (qTwoStdFamily E hK m hm).levi C) :
    (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c 1) = Pi.single c 1 := by
  refine levi_le_fix E hK hm C ?_ hg
  rintro ⟨i, hi, hci⟩
  simp only [nodeSupp, Set.mem_setOf_eq] at hci
  have hik := hC i hi
  omega

theorem qTwoStdFamily_levi_single_of_gt (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))} {k : ℕ} (hk : k + 2 ≤ m) (hC : ∀ i ∈ C, k < i.val)
    {c : Fin (m + 1)} (hc : c.val ≤ k)
    {g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hg : g ∈ (qTwoStdFamily E hK m hm).levi C) :
    (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c 1) = Pi.single c 1 := by
  refine levi_le_fix E hK hm C ?_ hg
  rintro ⟨i, hi, hci⟩
  simp only [nodeSupp, Set.mem_setOf_eq] at hci
  have hik := hC i hi
  omega

end CFSG.ClassicalInvolution.PhanDn.QTwo
