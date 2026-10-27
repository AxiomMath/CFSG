
module

public import Certificates.Data.Kernel.L34W.Tab42
public import Certificates.Data.GrSLitL34Sec5SWIsoCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.L34W.ModelSound
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

abbrev Cn (p : ℕ) : Prop := canonK 42 6 (mask 6) (42 * 6) p = true

@[expose] def GensG (G : ℕ → ℕ) : Prop := ∀ j < 6, gTabs[j]! = unpack 42 6 (G j) ∧ Cn (G j)

theorem pword_nil (G : ℕ → ℕ) (p : ℕ) : pword G [] p = p := rfl

theorem pword_cons (G : ℕ → ℕ) (j : ℕ) (w : List ℕ) (p : ℕ) :
    pword G (j :: w) p = pword G w (pcomp 42 6 (mask 6) p (G j)) := by
  unfold pword
  exact strictN_eq' _ _

theorem pword_spec (G : ℕ → ℕ) (tab : ℕ → Tab) :
    ∀ (w : List ℕ) (p : ℕ), Cn p → (∀ j ∈ w, Cn (G j) ∧ tab j = unpack 42 6 (G j)) →
      Cn (pword G w p) ∧
        w.foldl (fun t j => comp 42 t (tab j)) (unpack 42 6 p) = unpack 42 6 (pword G w p)
  | [], p, hp, _ => ⟨hp, rfl⟩
  | j :: w, p, hp, h => by
    obtain ⟨hj, ht⟩ := h j List.mem_cons_self
    rw [pword_cons, List.foldl_cons, ht, CFSG.KC.L34KSnd.comp_unpack' hp hj]
    exact pword_spec G tab w _ (CFSG.KC.BfsPin.canonK_pcomp hp hj)
      (fun j' hj' => h j' (List.mem_cons_of_mem j hj'))

theorem szOK42 : szOK 42 6 = true := by decide +kernel

theorem idTab42 : idTab 42 = unpack 42 6 (pidn 42 6) := CFSG.KC.L34KSnd.idTab_unpack' szOK42

theorem cn_pidn : Cn (pidn 42 6) := CFSG.KC.L34KSnd.canon_pidn szOK42

variable {G : ℕ → ℕ}

theorem genT_gS (hG : GensG G) (j : ℕ) : Cn (gS G j) ∧ genT j = unpack 42 6 (gS G j) := by
  rcases j with _ | _ | j
  · exact ⟨(hG 0 (by norm_num)).2, (hG 0 (by norm_num)).1⟩
  · exact ⟨(hG 1 (by norm_num)).2, (hG 1 (by norm_num)).1⟩
  · exact ⟨(hG 2 (by norm_num)).2, (hG 2 (by norm_num)).1⟩

theorem tgK_eq (hG : GensG G) (t : ℕ) : Cn (tgK G t) ∧ wordTab (tg t) = unpack 42 6 (tgK G t) := by
  unfold wordTab tgK
  rw [idTab42]
  exact pword_spec (gS G) genT (tg t) _ cn_pidn fun j _ => genT_gS hG j

theorem repK_eq (hG : GensG G) {i : ℕ} (hi : i < 36) :
    Cn (repK G i) ∧ repTab i = unpack 42 6 (repK G i) := by
  unfold repTab rTab repK
  rw [idTab42]
  exact pword_spec G (fun j => gTabs[j]!) _ _ cn_pidn fun j hj =>
    ⟨(hG j (repWords_lt i hi j hj)).2, (hG j (repWords_lt i hi j hj)).1⟩

theorem yK_eq (hG : GensG G) (t : ℕ) {i : ℕ} (hi : i < 36) :
    Cn (yK G t i) ∧ yTab t i = unpack 42 6 (yK G t i) := by
  obtain ⟨h1, e1⟩ := tgK_eq hG t
  obtain ⟨h2, e2⟩ := repK_eq hG hi
  refine ⟨CFSG.KC.BfsPin.canonK_pcomp h1 h2, ?_⟩
  unfold yTab yK
  rw [e1, e2, CFSG.KC.L34KSnd.comp_unpack' h1 h2]

end CFSG.KC.L34W

end
