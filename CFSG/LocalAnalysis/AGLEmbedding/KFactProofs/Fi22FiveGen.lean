module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreWords
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveStar
public import Certificates.Certificate9556

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Certificates CFSG.Open

theorem gen_check : genCheck = true :=
  Certificates.certificate9556

theorem normalizer_gens
    {x y : fi22P} (hx : Rep 3510 xA x.1) (hy : Rep 3510 yA y.1) :
    ∃ N₁ N₂ : fi22P, Rep 3510 n1A N₁.1 ∧ Rep 3510 n2A N₂.1 ∧
      N₁ ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set fi22P) : Subgroup fi22P) : Set _) ∧
      N₂ ∈ Subgroup.normalizer
        ((Subgroup.closure ({x, y} : Set fi22P) : Subgroup fi22P) : Set _) := by
  have h := orb_check
  unfold orbCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, hl1, hl2, -, -, -, -, c1x, c1y, c2x, c2y, -⟩ := h
  obtain ⟨M1, hM1P, hM1⟩ := exists_rep_evalW hl1
  obtain ⟨M2, hM2P, hM2⟩ := exists_rep_evalW hl2
  have hM1' : Rep 3510 n1A M1 := hM1
  have hM2' : Rep 3510 n2A M2 := hM2
  have hN1X : M1 * x.1 = x.1 ^ 2 * y.1 ^ 3 * M1 :=
    (eqA_iff (rep_compA hM1' hx) (rep_compA (rep_planeA hx hy 2 3) hM1')).1 c1x
  have hN1Y : M1 * y.1 = x.1 ^ 1 * y.1 ^ 2 * M1 :=
    (eqA_iff (rep_compA hM1' hy) (rep_compA (rep_planeA hx hy 1 2) hM1')).1 c1y
  have hN2X : M2 * x.1 = x.1 ^ 4 * y.1 ^ 1 * M2 :=
    (eqA_iff (rep_compA hM2' hx) (rep_compA (rep_planeA hx hy 4 1) hM2')).1 c2x
  have hN2Y : M2 * y.1 = x.1 ^ 1 * y.1 ^ 1 * M2 :=
    (eqA_iff (rep_compA hM2' hy) (rep_compA (rep_planeA hx hy 1 1) hM2')).1 c2y
  set n1 : fi22P := ⟨M1, hM1P⟩ with hn1_def
  set n2 : fi22P := ⟨M2, hM2P⟩ with hn2_def
  have hxm : ∀ i j : ℕ, x ^ i * y ^ j ∈ Subgroup.closure ({x, y} : Set fi22P) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hconj_of : ∀ (n a b : fi22P), n * a = b * n → n * a * n⁻¹ = b := fun n a b h => by
    rw [h]
    group
  have hn1x : n1 * x * n1⁻¹ = x ^ 2 * y ^ 3 := hconj_of _ _ _ (Subtype.ext hN1X)
  have hn1y : n1 * y * n1⁻¹ = x ^ 1 * y ^ 2 := hconj_of _ _ _ (Subtype.ext hN1Y)
  have hn2x : n2 * x * n2⁻¹ = x ^ 4 * y ^ 1 := hconj_of _ _ _ (Subtype.ext hN2X)
  have hn2y : n2 * y * n2⁻¹ = x ^ 1 * y ^ 1 := hconj_of _ _ _ (Subtype.ext hN2Y)
  exact ⟨n1, n2, hM1', hM2',
    mem_normalizer_closure_pair (x := x) (y := y) (n := n1)
      (by rw [hn1x]; exact hxm 2 3) (by rw [hn1y]; exact hxm 1 2),
    mem_normalizer_closure_pair (x := x) (y := y) (n := n2)
      (by rw [hn2x]; exact hxm 4 1) (by rw [hn2y]; exact hxm 1 1)⟩

theorem centralizing_H
    {x : fi22P} (hx : Rep 3510 xA x.1) :
    ∃ H : fi22P, Rep 3510 hA H.1 ∧ H * x = x * H := by
  have hC := cent_check
  unfold centCheck centGensOK centClosureOK centStarOK at hC
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hC
  obtain ⟨hlh, -, hcomH, -⟩ := hC
  obtain ⟨H, hHP, hH0⟩ := exists_rep_evalW hlh
  have hH : Rep 3510 hA H := hH0
  exact ⟨⟨H, hHP⟩, hH, Subtype.ext ((eqA_iff (rep_compA hH hx) (rep_compA hx hH)).1 hcomH)⟩

theorem z_gen {x : fi22P}
    (hx : Rep 3510 xA x.1) : ∃ Z : fi22P, Rep 3510 zA Z.1 ∧ Z * x = x ^ 2 * Z := by
  have h := gen_check
  unfold genCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hlz, hzx, -⟩ := h
  obtain ⟨Z, hZP, hZ0⟩ := exists_rep_evalW hlz
  have hZ : Rep 3510 zA Z := hZ0
  exact ⟨⟨Z, hZP⟩, hZ, Subtype.ext ((eqA_iff (rep_compA hZ hx) (rep_compA (rep_pw hx 2) hZ)).1 hzx)⟩

theorem gen_part
    {x y : fi22P} (hx : Rep 3510 xA x.1) (hy : Rep 3510 yA y.1) (hD : PlaneData x y) :
    ∃ G₁ G₂ : fi22P, Rep 3510 g1A G₁.1 ∧ Rep 3510 g2A G₂.1 ∧
      G₁ ∈ GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) ∧
      G₂ ∈ GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) := by
  obtain ⟨n1, n2, hn1, hn2, hn1N, hn2N⟩ := normalizer_gens hx hy
  obtain ⟨H, hH, hHx⟩ := centralizing_H hx
  obtain ⟨Z, hZ, hZx⟩ := z_gen hx
  have hg := gen_check
  unfold genCheck at hg
  simp only [Bool.and_eq_true, and_assoc] at hg
  obtain ⟨-, -, hl1, hl2, hinv⟩ := hg
  set Γ := GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) with hΓ
  have hT : Subgroup.closure ({x, y} : Set fi22P) ≤ Γ :=
    Subgroup.le_normalizer.trans hD.normalizer_le
  have hxΓ : x ∈ Γ := hT (Subgroup.subset_closure (by simp))
  have hyΓ : y ∈ Γ := hT (Subgroup.subset_closure (by simp))
  have hn1Γ : n1 ∈ Γ := hD.normalizer_le hn1N
  have hn2Γ : n2 ∈ Γ := hD.normalizer_le hn2N
  have hHΓ : H ∈ Γ := by
    refine hD.normalizer_zpowers_le (Subgroup.mem_normalizer_fintype fun t ht => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    have hc : H * x ^ k = x ^ k * H := ((show Commute H x from hHx).zpow_right k).eq
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hZΓ : Z ∈ Γ := by
    refine hD.normalizer_zpowers_le (Subgroup.mem_normalizer_fintype fun t ht => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    have hZx' : Z * x * Z⁻¹ = x ^ 2 := by rw [hZx]; group
    rw [← conj_zpow, hZx']
    exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2) k
  let Gs : ℕ → Equiv.Perm (Fin 3510) := fun k => [x.1, y.1, H.1, n1.1, n2.1, Z.1].getD k 1
  have hS : ∀ k < 6, Rep 3510 gens6A[k]! (Gs k) := by
    intro k hk
    interval_cases k
    · have : gens6A[0]! = xA := by simp [gens6A]
      rw [this]; exact hx
    · have : gens6A[1]! = yA := by simp [gens6A]
      rw [this]; exact hy
    · have : gens6A[2]! = hA := by simp [gens6A]
      rw [this]; exact hH
    · have : gens6A[3]! = n1A := by simp [gens6A]
      rw [this]; exact hn1
    · have : gens6A[4]! = n2A := by simp [gens6A]
      rw [this]; exact hn2
    · have : gens6A[5]! = zA := by simp [gens6A]
      rw [this]; exact hZ
  have hSinv : ∀ k < 6, Rep 3510 gens6Inv[k]! (Gs k)⁻¹ := fun k hk =>
    rep_inv_of_isInvA (hS k hk) (allLt_spec hinv hk)
  have hK : ∀ k < 6, Gs k ∈ Γ.map fi22P.subtype := by
    intro k hk
    interval_cases k
    exacts [⟨x, hxΓ, rfl⟩, ⟨y, hyΓ, rfl⟩, ⟨H, hHΓ, rfl⟩, ⟨n1, hn1Γ, rfl⟩, ⟨n2, hn2Γ, rfl⟩,
      ⟨Z, hZΓ, rfl⟩]
  obtain ⟨_, hg1K, hg1⟩ := exists_rep_wordA hS hSinv hK g1w hl1
  obtain ⟨_, hg2K, hg2⟩ := exists_rep_wordA hS hSinv hK g2w hl2
  obtain ⟨G₁, hG₁, rfl⟩ := Subgroup.mem_map.1 hg1K
  obtain ⟨G₂, hG₂, rfl⟩ := Subgroup.mem_map.1 hg2K
  exact ⟨G₁, G₂, hg1, hg2, hG₁, hG₂⟩

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
