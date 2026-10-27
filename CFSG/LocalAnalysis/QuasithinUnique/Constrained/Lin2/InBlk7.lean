module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk8

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Block

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.block_of_Zne1 (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L ≠ ⊥) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hf1 : f ≠ 1) (hf2 : f ^ 2 = 1) :
    Lin2BlockConcl L f n := by
  have hff : f * f = 1 := by rw [← sq]; exact hf2
  obtain ⟨-, hZcardf, -, hTrU, hTrZ'⟩ := counts_Zne1 h8 hcfg hB hc hf hf1 hf2
  obtain ⟨hOL, hUel, hLU⟩ := hcfg.block_facts h8
  obtain ⟨K, _, _, N, hK2, hσ⟩ := hcfg.exists_normData h8 hB hf hf1 hff
  have hZeq : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hOL
  have hTrZ : ∀ x ∈ blockZ L, (f * x) * (f * x) = 1 → ∃ m ∈ blockZ L, m⁻¹ * f * m = f * x := by
    rw [hZeq]
    exact hTrZ'
  obtain ⟨m, F, _, _, α, β, hnm, hcard, hF2, hαs, hαk, hβs, hβk, hβe, hRα⟩ :=
    N.exists_data hK2 hOL hTrU hTrZ hσ
  obtain ⟨⟨t, htC, htt, htU⟩, hZW⟩ :=
    hcfg.nonsplit h8 hB hc hf hf1 hff α β hαs hαk hRα hβs hβk hβe
  have hlin2Z : lin2Z L (thompsonJ S) = centerOf L := by simp [lin2Z, hc]
  have hZc : Nat.card (blockZ L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = 2 ^ m := by
    rw [hZeq, ← hlin2Z, hZcardf]
    congr 1
    omega
  by_cases hm : 2 ≤ m
  · left
    have hZ4 : 4 ≤ Nat.card (blockZ L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) := by
      rw [hZc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    obtain ⟨hshort, hlin, hU, hP⟩ :=
      lin2_of_blockData hm hcard hF2 hUel hLU (hZW hZ4) α β hαs hαk hβs hβk hβe
    exact ⟨m, by omega, by omega, hshort, hlin, hU, hP⟩
  · right
    have hm1 : m = 1 := by
      have := hcfg.one_pos
      omega
    subst hm1
    have hcard' : Fintype.card F = 2 := by simpa using hcard
    have hZ2 : Nat.card (blockZ L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = 2 := by
      rw [hZc]
      norm_num
    have hVel' : IsElemAbelian 2 (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) :=
      IsElemAbelian.mono inf_le_left hUel
    have hVn := blockV_conj (f := f) hLU
    have hαk' : ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)),
        α c = 1 ↔ (c : G) ∈ blockU L ⊓ Subgroup.centralizer ({f} : Set G) := fun c => by
      rw [hαk, mem_blockV_iff]
    have hβk' : ∀ v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)),
        β v = 1 ↔ (v : G) ∈ blockZ L ⊓ Subgroup.centralizer ({f} : Set G) := fun v => by
      rw [hβk, mem_blockZf_iff]
    have hiso := z2_s4_of_data (C := L ⊓ Subgroup.centralizer ({f} : Set G))
      (V := blockU L ⊓ Subgroup.centralizer ({f} : Set G))
      (Zf := blockZ L ⊓ Subgroup.centralizer ({f} : Set G)) hcard' hF2
      (blockV_le (L := L) (f := f)) hVel' (blockZf_le (L := L) (f := f))
      (blockZf_comm (L := L) (f := f)) hZ2 α hαs hαk' β hβs hβk' hβe htC htt (fun h => htU h.1)
    have hP := pCoreOf_eq_of_data hF2 (blockV_le (L := L) (f := f)) hVel' hVn α hαs hαk'
    exact ⟨by omega, Or.inr ⟨hc, hiso, hP⟩⟩

theorem lemma2_4_12_block (h8 : Lemma2_4_8) : Lemma2_4_12_block := by
  intro G _ _ T M H S L D n hcfg B hB f hf hf1 hf2
  by_cases hc : centerOf L = ⊥
  · exact hcfg.block_of_Zeq1 h8 hB hc hf hf1 hf2
  · exact hcfg.block_of_Zne1 h8 hB hc hf hf1 hf2

end Block

end CFSG.QuasithinUnique.Lin2
