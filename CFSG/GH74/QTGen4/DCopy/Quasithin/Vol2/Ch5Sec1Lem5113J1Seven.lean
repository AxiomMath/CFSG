module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Prime
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113J1FSU
public import CFSG.Quasithin.Vol2.Ch11SecSZK
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_13_type_j1_ZK_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ → conjClosure Kh₁ T = Kh₁ →
    IsSporadic .J1 ↥(o2Img X Kh₁) →
    (∀ d ∈ o2Img X (D ⊓ X),
      d ^ 7 ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    ¬ (∀ d ∈ o2Img X (D ⊓ X), ∃ k : ℕ,
      d ^ (3 ^ k) ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    ⁅quasithinOmegaOneCenter T, Kh₁⁆ ≠ ⊥

theorem stmt5_1_13_type_j1_seven_of_F4
    (h312 : A312ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h325 : Stmt3_2_5_F4) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C_F4)
    (hZK : Stmt5_1_13_type_j1_ZK_F4) : Stmt5_1_13_type_j1_seven_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hJ h7 hn3
  have h := m.hyp.toHyp5_0_1
  have hZK' := hZK G T M L V H B D K₁ X Kh₁ n m hc5 hcl hJ h7 hn3
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hTX : T ≤ X := hTH.1.trans m.inH.1
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hKhc : Kh₁ ∈ cComp X := m.hat.1
  have hloc : quasithinIsLocal T Kh₁ := isLocal_of_mem_cComp_of_sylow hTXs m.inH.2 hKhc

  have hJ' : IsSporadic .J1 (O2Q Kh₁) := by
    obtain ⟨f⟩ := hJ
    obtain ⟨g⟩ := modO2_mulEquiv hKhc
    exact ⟨g.trans f⟩

  have hf : quasithinIsFaithfulLocal T Kh₁ :=
    Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter h.qtke h.sylow hloc hZK'
  have hmax : quasithinIsMaximalLocal T Kh₁ :=
    Ch1Four.lemma128Four_of h312 G h.qtke h.simple h.nonabelian T Kh₁ hloc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hJ')))))))
  have hTL : T ≤ Subgroup.normalizer (Kh₁ : Set G) := by
    rw [← hcl]
    exact le_normalizer_conjClosure Kh₁ T
  exact false_of_j1_of_faithful_F4 (stmt3_2_3_of h37 h38 h39) h325 h328 h329 h.simple h.nonabelian
    h.qtke h.sylow hmax hf hTL hJ'

end CFSG.Quasithin.H13
