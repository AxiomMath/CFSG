module

public import CFSG.Quasithin.H13.A7Nat1238NQ21
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238NQBase

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem nonQ_dichotomy_F4
    (h3214 : Stmt3_2_14_F4) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) {T K₀ Ke : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hK₀ : quasithinIsLocal T K₀) (hKe : Ke ∈ lFamily T)
    (hKeK₀ : Ke ≤ K₀) (hq : ¬ CFSG.IsQuasisimple (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :
    K₀ ≤ (K₀ ⊓ centralizer (conjClosure (quasithinOmegaOneCenter T) (K₀ ⊔ T) : Set G)) ⊔ Ke ∨
      ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
        IsSL2 p (↥(modO2Image (K₀ ⊔ T) K₀) ⧸ CFSG.oddCore ↥(modO2Image (K₀ ⊔ T) K₀)) := by
  have : IsSimpleGroup G := hs
  set H := K₀ ⊔ T with hH
  set P := CFSG.pCore 2 ↥H with hP
  have hK₀H : K₀ ≤ H := le_sup_left
  have hLocal : LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hSQ : Vol2Native.SQTKHypCat (↥H ⧸ P) :=
    Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hLocal hK₀.2.2.2
  have hSH : IsSylowTwoOf T H := ⟨le_sup_right, hT.1, fun h2 => hT.2 (h2.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le
      (le_sup_right : T ≤ H)))⟩
  have hTbar : IsSylowTwoOf ((T.subgroupOf H).map (QuotientGroup.mk' P)) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSH) _
      (QuotientGroup.mk'_surjective P)
  have hK₀c : K₀ ∈ cComp H := hK₀.2.1
  have hLc : modO2Image H K₀ ∈ cComp (⊤ : Subgroup (↥H ⧸ P)) := modO2Image_mem_cComp hK₀c
  have hBl : modO2Image H Ke ∈ lFamily ((T.subgroupOf H).map (QuotientGroup.mk' P)) :=
    modO2Image_mem_lFamily hSH (hKeK₀.trans hK₀H) hKe
  have hBL : modO2Image H Ke ≤ modO2Image H K₀ := Subgroup.map_mono fun x hx => hKeK₀ hx
  have hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image H K₀) := by
    intro h
    obtain ⟨e⟩ := modO2_mulEquiv hK₀c
    exact hq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm h)
  have h36 : A36Strong (modO2Image H K₀) :=
    (Vol2Native.a36CoreForSQTKCat_proved (↥H ⧸ P) hSQ _ hLc).toStrong hnq
  have hNQ := A312.nonquasi_of_lFamily a312SL2Fact hTbar hLc hBL hBl h36 hnq
  unfold A312Nonquasi at hNQ
  dsimp only at hNQ
  rcases hNQ with ⟨-, hLB, -⟩ | ⟨-, hp, -⟩
  · left
    exact le_sup_of_le_sup_oddCore hK₀H hKeK₀
      (solvableRadical_le_centralizer_conjClosure_F4 h3214 hs hnab hQ hT hK₀ hq) hLB.le
  · right
    exact hp

end CFSG.Quasithin.H13.A7
