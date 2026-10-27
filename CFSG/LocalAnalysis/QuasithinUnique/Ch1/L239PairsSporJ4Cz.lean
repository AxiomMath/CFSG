module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4CzCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Syl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Pair
public import CFSG.Sporadic.J4.QT2ACons
public import CFSG.Sporadic.J4.QT2LocCntMain

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native
open scoped commutatorElement

theorem qGenW_length : QT2A.qGenW.length = 12 := by
  have h := QT2A.chkQgens_true
  unfold QT2A.chkQgens at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem Mx_qJ_inv {k : ℕ} (hne : ∀ l ∈ QT2A.qGenW.getD k [], l ≠ 0) :
    Mx (QT2A.qJ k)⁻¹ = rowsMatrix (QT2A.wR (QT2A.invW (QT2A.qGenW.getD k []))) := by
  have hM := j4Facts.mat
  have h : (QT2A.qJ k)⁻¹ = QT2A.el5 (QT2A.invW (QT2A.qGenW.getD k [])) := by
    unfold QT2A.qJ QT2A.el5
    rw [QT2A.invW_eq, QT2A.wordProd_invWord _ _ hne]
  rw [h, QT2A.Mx_el5 hM]

theorem Mx_commutator_qJ_yJ
    {k n : ℕ} (hne : ∀ l ∈ QT2A.qGenW.getD k [], l ≠ 0)
    (hy3 : QT2A.yJ n * (QT2A.yJ n * QT2A.yJ n) = 1) :
    Mx ⁅QT2A.qJ k, QT2A.yJ n⁆ = rowsMatrix (hCommRows k n) := by
  have hM := j4Facts.mat
  have hinv : (QT2A.yJ n)⁻¹ = QT2A.yJ n * QT2A.yJ n := inv_eq_of_mul_eq_one_right hy3
  rw [commutatorElement_def, hinv]
  simp only [map_mul]
  rw [Mx_qJ_inv hne, QT2A.Mx_yJ hM, QT2A.Mx_qJ hM]
  simp only [hCommRows, rowsMatrix_mulRows]

theorem noncomm_commutator_yJ
    {n : ℕ} (hn0 : 0 < n) (hn : n < 27) :
    ∃ x ∈ ⁅QT2A.Qz, Subgroup.zpowers (QT2A.yJ n)⁆,
      ∃ y ∈ ⁅QT2A.Qz, Subgroup.zpowers (QT2A.yJ n)⁆, x * y ≠ y * x := by
  have hM := j4Facts.mat
  have h := chkHE_true
  unfold chkHE at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hnz, hall⟩ := h
  have hnz' : ∀ w ∈ QT2A.qGenW, ∀ l ∈ w, l ≠ 0 := by
    intro w hw l hl
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hnz w hw) l hl
    simpa using h1
  have hn' := List.all_eq_true.1 hall n (List.mem_range.2 hn)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hn'
  rcases hn' with h0 | ⟨hcube, hany⟩
  · omega
  obtain ⟨p, hp, hpp⟩ := List.any_eq_true.1 hany
  simp only [Bool.and_eq_true] at hpp
  obtain ⟨⟨hw1, hw2⟩, hnc⟩ := hpp
  have hp12 : p.1 < 12 ∧ p.2 < 12 := by
    simp only [hePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  have hne : ∀ k : ℕ, k < 12 → ∀ l ∈ QT2A.qGenW.getD k [], l ≠ 0 := by
    intro k hk l hl
    have hmem : QT2A.qGenW.getD k [] ∈ QT2A.qGenW := by
      rw [List.getD_eq_getElem _ _ (by rw [qGenW_length]; exact hk)]
      exact List.getElem_mem _
    exact hnz' _ hmem l hl
  have hy3 : QT2A.yJ n * (QT2A.yJ n * QT2A.yJ n) = 1 := by
    apply Mx_injective
    rw [map_mul, map_mul, map_one, QT2A.Mx_yJ hM]
    have := congrArg rowsMatrix (eqRows_iff.1 hcube)
    rwa [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_idRows] at this
  exact ⟨_, Subgroup.commutator_mem_commutator (QT2A.qJ_mem_Qz hM hp12.1)
    (Subgroup.mem_zpowers (QT2A.yJ n)), _, Subgroup.commutator_mem_commutator
    (QT2A.qJ_mem_Qz hM hp12.2) (Subgroup.mem_zpowers (QT2A.yJ n)),
    QT2A.nocomm_ne (Mx_commutator_qJ_yJ (hne _ hp12.1) hy3)
      (Mx_commutator_qJ_yJ (hne _ hp12.2) hy3) hw1 hw2 hnc⟩

theorem exists_yJ_of_mem_Ycl
    {b : J} (hb : b ∈ QT2A.Ycl) : ∃ n, n < 27 ∧ b = QT2A.yJ n := by
  obtain ⟨n, hn, rfl⟩ := QT2A.Ycl_subset j4Facts.mat hb
  exact ⟨n, hn, rfl⟩

theorem isPGroup_Ycl :
    IsPGroup 3 ↥QT2A.Ycl :=
  IsPGroup.of_card (n := 3) (by rw [QT2A.card_Ycl j4Facts.mat]; norm_num)

theorem not_dvd_index_Ycl
    : ¬ 3 ∣ (QT2A.Ycl.subgroupOf QT2A.Cz).index := by
  have hM := j4Facts.mat
  have h1 := Subgroup.index_mul_card QT2A.Ycl
  rw [QT2A.card_Ycl hM, card_J j4Facts] at h1
  have h2 : QT2A.Ycl.index = 3213910038743613440 := by omega
  have h3 := Subgroup.relIndex_mul_index (QT2A.Ycl_le_Cz hM)
  intro hdvd
  have h4 : 3 ∣ QT2A.Ycl.index := by
    rw [← h3]
    exact Dvd.dvd.mul_right hdvd _
  rw [h2] at h4
  norm_num at h4

theorem goodLocal_centralizer_of
    (N : Subgroup J) (hNY : N ≤ QT2A.Cz)
    (hNn : ∀ q ∈ QT2A.Cz, ∀ e ∈ N, q * e * q⁻¹ ∈ N) (hN2 : IsPGroup 2 ↥N)
    (hC : ∀ q ∈ QT2A.Cz, (∀ e ∈ N, q * e = e * q) → q ∈ N) (hQ2 : IsPGroup 2 ↥QT2A.Qz) :
    GoodLocal QT2A.Cz := by
  refine goodLocal_of_sylow3_witnesses QT2A.Cz N QT2A.Qz hNY hNn hN2 hC QT2A.Qz_le_Cz
    (fun y hy q hq => QT2A.Qz_conj hy hq) hQ2 QT2A.Ycl (QT2A.Ycl_le_Cz j4Facts.mat) isPGroup_Ycl
    not_dvd_index_Ycl ?_
  intro b hb hord
  obtain ⟨n, hn, rfl⟩ := exists_yJ_of_mem_Ycl hb
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      simp [QT2A.yJ] at hord
    · exact h
  exact noncomm_commutator_yJ hn0 hn

theorem goodLocal_centralizer_zJ
    : GoodLocal (Subgroup.centralizer ({zJ} : Set J)) := by
  have hM := j4Facts.mat
  have hC : Nat.card QT2A.Cz = 21799895040 := QT2.card_centralizer_eta_1131
  obtain ⟨N, hNY, hNn, hN2, hNc⟩ := QT2A.exists_normal_two_group_selfcentralizing hM hC
  exact goodLocal_centralizer_of N hNY hNn hN2 hNc (QT2A.isPGroup_Qz hM hC)

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
