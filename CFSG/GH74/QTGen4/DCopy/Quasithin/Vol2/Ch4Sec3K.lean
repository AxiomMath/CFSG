module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch4Sec3K

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Blueprint

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem exists_K_F4 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (hC48 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC48Statement G)
    (hInsp : InspC48L2) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ L ≤ K ∧
      C48Case1 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K ∧
      ¬ K ≤ H ⊓ M ∧ H ⊓ M ≤ Subgroup.normalizer (K : Set G) ∧
      C48KDescribed H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K := by
  have hC28 := s.hyp4_2_3N.lemma_4_2_4N h36 h37 h38 h39 s.inH s.not_le_M
  have hlt : H ⊓ M < H := inf_lt_left.mpr s.not_le_M
  obtain ⟨-, K, hK, hKq, hLK, hcase⟩ := hC48 G H _ (H ⊓ M) L _ hC28 hlt
  rcases hcase with h10 | ⟨h19, hKM, hMK, hdesc⟩
  ·
    exfalso
    have hS := s.isSylowTwoOf_S_H hR hC h37 h38 h39
    have hSHM : T ⊓ H ≤ H ⊓ M := le_inf inf_le_right (inf_le_left.trans s.hyp.T_le)
    have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ H) (H ⊓ M) H hSHM inf_le_left
    rw [h10.2.2.2] at hmul
    exact hS.2.2 (Dvd.intro_left _ hmul)
  · rcases h19 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
    · exact ⟨K, hK, hKq, hLK, h1, hKM, hMK, hdesc⟩
    all_goals exfalso
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inl h2)
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inr (Or.inl h3))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inr (Or.inr (Or.inl h4)))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))))
    · exact hInsp G H _ _ L _ K n s.hyp.two_le s.hyp.lie
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h9)))))))

end Setting432

end CFSG.Quasithin.H13.Ch4
