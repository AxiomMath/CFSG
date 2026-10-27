module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Prime
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113TypeF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def Stmt5_1_13_type_j1_seven_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ → conjClosure Kh₁ T = Kh₁ →
    IsSporadic .J1 ↥(o2Img X Kh₁) →
    (∀ d ∈ o2Img X (D ⊓ X),
      d ^ 7 ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    ¬ (∀ d ∈ o2Img X (D ⊓ X), ∃ k : ℕ,
      d ^ (3 ^ k) ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    False

theorem stmt5_1_13_type_j1_of_F4 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h36 : Vol2Native.A36ForSQTKCat) (h510 : Stmt5_1_10_F4)
    (hlie : Stmt5_1_13_lieC_F4) (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34)
    (h312 : A312ForSQTK) (hTc : FactType513Aut) (hTp : FactType513Prime)
    (h7 : Stmt5_1_13_type_j1_seven_F4) : Stmt5_1_13_type_j1_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam_F4 m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  obtain ⟨hst, hnot⟩ := m.star513_F4 h37 h38 h510 heq hcl hL24
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have h36Q := Vol2Native.lemma_1_2_1_four_strong hloc h36 m.inH.2 m.hat.1
  have h314 := hc5.2.2.2
  rw [hcl] at h314
  obtain ⟨eH⟩ := modO2_mulEquiv m.hat.1
  have hnr : ¬ IsRank2LieChar2 ↥(modO2Image X Kh₁) := fun hR2 => by
    refine m.false_of_a314One_F4 hM hM23 h312 h510 hlie hL24 heq ?_
    rw [hcl]
    exact IsRank2LieChar2.of_mulEquiv eH.symm hR2
  rcases Star513.three_or_j1 hst hnot hTc hTp h36Q h314 hnr with h3 | ⟨hJ, h7'⟩
  · exact h3
  · by_contra hne
    exact h7 G T M L V H B D K₁ X Kh₁ n m hc5 hcl hJ h7' hne

end CFSG.Quasithin.H13
