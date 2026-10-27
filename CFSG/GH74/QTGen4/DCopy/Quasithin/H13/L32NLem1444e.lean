module

public import CFSG.Quasithin.H13.L32NLem1444e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1444d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open Q8SqE9 in

theorem exists_setup3_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest_F4) {T L V V₂ : Subgroup G} {g : G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5)
    (hG2 : ¬ LieModel G .G2 0 3 1) (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V)
    (hgH : g ∉ l32nH T V) :
    ∃ (D : HatModelU (fsuU T V)) (Q₁ Q₂ : Subgroup G), Setup3 G T L V V₂ g D Q₁ Q₂ := by
  obtain ⟨D, S⟩ := exists_setup2_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest h hext h32 hV₂ hgP
    hgH
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  have hQ8 : IsQ8Sq ↥(fsuU T V) :=
    isQ8Sq_of_isQ8CentralPow_two (lemma1442Q8Four_of_inputs_F4 hV h hext h32)
  obtain ⟨hQ32, A', B', ⟨hAB, hgen⟩, ⟨eA⟩, ⟨eB⟩⟩ := hQ8
  have hsup : A'.map (fsuU T V).subtype ⊔ B'.map (fsuU T V).subtype = fsuU T V := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm : A'.map (fsuU T V).subtype ≤
      Subgroup.centralizer (B'.map (fsuU T V).subtype : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb)
  have hcfg : Cfg (A'.map (fsuU T V).subtype) (B'.map (fsuU T V).subtype) :=
    ⟨hcomm,
      ⟨(A'.equivMapOfInjective _ (fsuU T V).subtype_injective).symm.trans eA⟩,
      ⟨(B'.equivMapOfInjective _ (fsuU T V).subtype_injective).symm.trans eB⟩,
      by rw [hsup]; exact hQ32⟩
  obtain ⟨hK, -⟩ :=
    lemma1444One_of_inputs_F4 h1332 h1334 h1222 h12213 h37 h38 h39 hRest G T L V h hext h32 hG2
  exact ⟨D, _, _, { toSetup2 := S, cfg := hcfg, sup := hsup, kElem := hK }⟩

end L1444

end CFSG.Quasithin.H13
