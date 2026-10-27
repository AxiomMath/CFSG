module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinAt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinWiredFields

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

set_option linter.unusedSectionVars false

theorem twinThinInput_of_thinAEAt {n : ℕ} (hA : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hAE : TwinThin.ThinAEAt n) : TwinThinInput n := by
  intro Y _ _ R S t h hconn hall
  have hD : TC.Thin.ThmDGenBelow 3 n := TC.Thin.thmDGenBelow_of_absBelow hP.thmD.d2
  obtain ⟨hodd, hmem, -, hs⟩ := twinConnPreludeOut_proved n hA hP _ _ _ _ h hconn
  classical
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  obtain ⟨K', hK', hne⟩ := h.twin
  obtain ⟨π, hmax, -, hH1⟩ := twin_noCentralInv hs hZ hK₀ hK'.1 hne hz
  have hπ : π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) := by
    rw [hmax]
    rfl
  have hos := hs.orbitStd
  obtain ⟨g, hg⟩ := TwinSecXg.exists_conj_mem hos hK₀ hπ
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (g * t * g⁻¹) := hz.conj g
  have hXw := (hos.conj_piGen_le_centralizer hK₀ hπ hH1 hz g).1
  have hXn := hos.conj_piGen_normal hK₀ hπ hH1 hz g
  have hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hXn hXw (hodd _ ⟨g, rfl⟩ _ hw)
  have hXlt : Nat.card ↥(conjSub g (piGen π)) < n :=
    lt_of_lt_of_eq (TwinSecXg.card_conj_lt hos hK₀ hπ hH1 hZ hz g) h.card
  exact TwinThin.thin_false_at hAE hD
    ⟨hs, hK₀, hK', hne, (hmem _ hK₀).2, h.aEmpty, hz, hπ, hH1, hg, hO, hall⟩
    h.simple h.nonab hodd h.card.le hXlt

theorem twinThinPack_of_thinAE
    (hAE : ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TwinThin.ThinAEAt n) :
    ∀ n, CIT3Below n → TL4.TightBelowRPlus 3 n → TwinThinInput n :=
  fun n hA hP => twinThinInput_of_thinAEAt hA hP (hAE n hA hP)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
