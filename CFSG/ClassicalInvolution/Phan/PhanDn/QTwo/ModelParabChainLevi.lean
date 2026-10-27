module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.StdFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.AmalgamFamily
public import CFSG.LocalAnalysis.StandardType.GGQTwoBSGen

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

private theorem qtt_chain_label_three (m b i : ℕ) (hglob : b + i + 3 ≤ m + 1) :
    (CFSG.StandardType.ggCoxeterMatrixD (m + 1)).M
      (⟨b + i, by omega⟩ : Fin (m + 1))
      (⟨b + i + 1, by omega⟩ : Fin (m + 1)) = 3 := by
  have hne : (⟨b + i, by omega⟩ : Fin (m + 1)) ≠ ⟨b + i + 1, by omega⟩ := by
    intro h'
    have := congrArg Fin.val h'
    simp at this
  have hD : CartanMatrix.D (m + 1) ⟨b + i, by omega⟩ ⟨b + i + 1, by omega⟩ = -1 := by
    simp [CartanMatrix.D, Fin.ext_iff, show ¬ m + 1 ≤ 2 by omega]
    omega
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_neg hne]
  simp [hD]

private theorem qtt_theta_threeBlock_coe (m : ℕ) (hm : 3 ≤ m)
    {b i : ℕ} (hglob : b + i + 3 ≤ m + 1) (A : Su K 2 1 3) :
    ((qTwoStdTheta E m hm
        (⟨b + i, by omega⟩ : Fin (m + 1))
        (⟨b + i + 1, by omega⟩ : Fin (m + 1))) A :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
        (blockEmb K 2 1 (m + 1) 3 (b + i) hglob A) := by
  rw [coe_qTwoStdTheta_of_lt E m hm (Fin.mk_lt_mk.2 (by omega)), stdFamilyV_θ]
  rw [show (⟨b + i + 1, by omega⟩ : Fin (m + 1)) =
      Fin.castSucc (⟨b + i + 1, by omega⟩ : Fin m) from rfl]
  rw [stdTheta_castSucc]
  simp [stdThetaAt, stdChainTheta, blockEmb3]


private theorem qtt_twoBlock_mem_levi (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    {b : ℕ} (hbk : b + 2 ≤ m + 1) {C : Set (Fin (m + 1))}
    (hCb : (⟨b, by omega⟩ : Fin (m + 1)) ∈ C) (u : Su K 2 1 2) :
    ∃ l ∈ (qTwoStdFamily E hK m hm).levi C,
      (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
        suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb K 2 1 (m + 1) 2 b hbk u) := by
  let node : Fin (m + 1) := ⟨b, by omega⟩
  refine ⟨(qTwoStdFamily E hK m hm).ι node u,
    (qTwoStdFamily E hK m hm).mem_levi_node hCb u, ?_⟩
  change ((qTwoStdIota E m hm node) u :
    (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) = _
  rw [coe_qTwoStdIota]
  change ((stdFamilyV E m hm).ι (Fin.castSucc (⟨b, by omega⟩ : Fin m))) u = _
  rw [stdFamilyV_ι_castSucc]
  simp [stdChainIota, blockEmb2]


theorem qTwo_blockEmb_mem_levi (hK : Nat.card K = 4) (m : ℕ) (hm : 3 ≤ m)
    (k b : ℕ) (hk : 2 ≤ k) (hbk : b + k ≤ m + 1)
    {C : Set (Fin (m + 1))}
    (hC : ∀ j : Fin (k - 1), (⟨b + j.val, by omega⟩ : Fin (m + 1)) ∈ C)
    (u : Su K 2 1 k) :
    ∃ l ∈ (qTwoStdFamily E hK m hm).levi C,
      (l : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
        suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb K 2 1 (m + 1) k b hbk u) := by
  classical
  by_cases hk2 : k = 2
  · subst k
    have hCb : (⟨b, by omega⟩ : Fin (m + 1)) ∈ C := by
      simpa using hC (⟨0, by omega⟩ : Fin (2 - 1))
    exact qtt_twoBlock_mem_levi E hK m hm hbk hCb u
  · have hk3 : 3 ≤ k := by omega
    let S := qTwoStdFamily E hK m hm
    let V := (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)
    let L : Subgroup V := (S.levi C).map
      (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))).subtype
    let φ : Su K 2 1 k →* V :=
      (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).comp
        (blockEmb K 2 1 (m + 1) k b hbk)
    have hφu : φ u ∈ L := by
      let H : Subgroup (Su K 2 1 k) :=
        ⨆ i, ⨆ (h : i + 3 ≤ k), (blockEmb K 2 1 k 3 i h).range
      have hH : H = ⊤ := CFSG.StandardType.QTwo.iSup_range_blockEmb_three hK hk3
      have huH : u ∈ H := by
        rw [hH]
        exact Subgroup.mem_top u
      have hmap : H.map φ ≤ L := by
        rw [Subgroup.map_le_iff_le_comap]
        refine iSup_le fun i => iSup_le fun hi => ?_
        rintro A ⟨B, rfl⟩
        have hglob : b + i + 3 ≤ m + 1 := by omega
        let i0 : Fin (m + 1) := ⟨b + i, by omega⟩
        let i1 : Fin (m + 1) := ⟨b + i + 1, by omega⟩
        change (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1))
          ((blockEmb K 2 1 (m + 1) k b hbk)
            ((blockEmb K 2 1 k 3 i hi) B)) ∈ L
        rw [blockEmb_comp_apply (K := K) (p := 2) (f := 1) hbk hi]
        change (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1))
          ((blockEmb K 2 1 (m + 1) 3 (b + i) hglob) B) ∈ L
        rw [(qtt_theta_threeBlock_coe (E := E) m hm (b := b) (i := i) hglob B).symm]
        have hC1 : i1 ∈ C := by
          have := hC (⟨i + 1, by omega⟩ : Fin (k - 1))
          convert this using 2
        refine Subgroup.mem_map.mpr ⟨(qTwoStdTheta E m hm i0 i1) B, ?_, rfl⟩
        exact S.mem_levi_edge (by simpa [i0] using hC (⟨i, by omega⟩ : Fin (k - 1)))
          hC1 (qtt_chain_label_three m b i hglob) B
      have hφH : φ u ∈ H.map φ := Subgroup.mem_map.mpr ⟨u, huH, rfl⟩
      exact hmap hφH
    rcases Subgroup.mem_map.mp hφu with ⟨l, hl, hcoe⟩
    exact ⟨l, hl, by simpa [φ] using hcoe⟩


end CFSG.ClassicalInvolution.PhanDn.QTwo
