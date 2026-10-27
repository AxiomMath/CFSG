module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

open CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev

private theorem cartanC_ne_zero_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    cartanC m i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [cartanC, Matrix.of_apply, if_neg hij]
  split_ifs <;> omega

private theorem edgeCond_pair {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (H : Fin (rootDatum n F).rank → Subgroup (StatedSp n F)) (hrank : 3 ≤ n) (k : Fin n)
    (hk : k.val + 1 < n) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond (rootDatum n F) H k ⟨k.val + 1, hk⟩ ∧
      CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond (rootDatum n F) H ⟨k.val + 1, hk⟩ k := by
  by_cases htail : k.val + 2 = n
  ·
    have hdeg := degree_ne_of_path hrank (isFiniteType_cartanC n)
      (fun i j hij => cartanC_ne_zero_iff hij) (i := ⟨k.val + 1, hk⟩) (j := k)
      (by show k.val + 1 + 1 = n; omega) htail
    exact ⟨Or.inr (Or.inl hdeg.symm), Or.inr (Or.inl hdeg)⟩
  ·
    have hv2 : (⟨k.val + 1, hk⟩ : Fin n).val + 1 < n := by
      show k.val + 1 + 1 < n
      omega
    have hij : k ≠ ⟨k.val + 1, hk⟩ := SpExtras.ne_succ' hk
    have hjk : (⟨k.val + 1, hk⟩ : Fin n) ≠ ⟨(⟨k.val + 1, hk⟩ : Fin n).val + 1, hv2⟩ :=
      SpExtras.ne_succ' hv2
    have hik : k ≠ ⟨(⟨k.val + 1, hk⟩ : Fin n).val + 1, hv2⟩ :=
      Fin.ne_of_val_ne (by show k.val ≠ k.val + 1 + 1; omega)
    have h1 : (shortBlock F hij).range = CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k :=
      range_shortBlock_eq_rankOne (K := F) hk
    have h2 : (shortBlock F hjk).range =
        CFSG.LieType.CurtisTits.rankOne (rootGroup n F) ⟨k.val + 1, hk⟩ :=
      range_shortBlock_eq_rankOne (K := F) hv2
    have hr : (leviSL3 F hij hjk hik).range =
        CFSG.LieType.CurtisTits.rankOne (rootGroup n F) k ⊔
          CFSG.LieType.CurtisTits.rankOne (rootGroup n F) ⟨k.val + 1, hk⟩ := by
      apply le_antisymm
      · have h := linearBlockStandardPair_le_sup
          (linearBlockStandardPair_shortBlock (K := F) hij hjk hik)
        rw [h1, h2] at h
        exact h
      · refine sup_le ?_ ?_
        · rw [← h1, ← leviSL3_comp_blockSL_zero (K := F) hij hjk hik]
          intro y hy
          obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
          exact MonoidHom.mem_range.2 ⟨_, rfl⟩
        · rw [← h2, ← leviSL3_comp_blockSL_one (K := F) hij hjk hik]
          intro y hy
          obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
          exact MonoidHom.mem_range.2 ⟨_, rfl⟩
    have hinj := leviSL3_injective (K := F) hij hjk hik
    exact ⟨Or.inl (edgeLevi_of_sl3 (D := rootDatum n F) (leviSL3 F hij hjk hik) hinj hr),
      Or.inl (edgeLevi_of_sl3 (D := rootDatum n F) (leviSL3 F hij hjk hik) hinj
        (hr.trans (sup_comm _ _)))⟩

theorem edgeCond_sp {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (H : Fin (rootDatum n F).rank → Subgroup (StatedSp n F))
    (hrank : 3 ≤ (rootDatum n F).rank) (u v : Fin (rootDatum n F).rank)
    (hadj : (TauCeti.diagramGraph (rootDatum n F).cartan).Adj u v) :
    CFSG.AGLEmbeddingD2.Tits.GN516.Core.EdgeCond (rootDatum n F) H u v := by
  obtain ⟨huv, hne⟩ :=
    (TauCeti.IsFiniteType.diagramGraph_adj_iff (isFiniteType_cartanC n)).1 hadj
  rcases (cartanC_ne_zero_iff (m := n) huv).1 hne with h | h
  · have hvn : v.val < n := v.isLt
    have hu : u.val + 1 < n := by omega
    have hv : v = ⟨u.val + 1, hu⟩ := Fin.ext h.symm
    subst hv
    exact (edgeCond_pair H hrank u hu).1
  · have hun : u.val < n := u.isLt
    have hv : v.val + 1 < n := by omega
    have hu : u = ⟨v.val + 1, hv⟩ := Fin.ext h.symm
    subst hu
    exact (edgeCond_pair H hrank v hv).2

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
