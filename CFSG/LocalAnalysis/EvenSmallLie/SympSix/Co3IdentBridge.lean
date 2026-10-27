module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCard
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Co3
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDefs
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentBridgeInputs
public import Certificates.Certificate3092
public import Certificates.Certificate3090
public import Certificates.Certificate3091
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.SurjD.Native
  CFSG.Sporadic.Bridge.VecSurj

local notation "D3" => CFSG.Sporadic.Co3.Native.co3Data

theorem vBridge_check :
    seedLetterChecks CFSG.Sporadic.Co3.Native.co3Data vSpec = true :=
  Certificates.certificate3092

theorem vBridgeFacts : BridgeFacts D3 vSpec (seedLetters D3) :=
    bridge_facts vBridge_check

noncomputable abbrev vImg (k : ℕ) : J D3 := img vSpec (seedG D3) k

theorem lift_mk_seven {G : Type*} [Group G] (x : ℕ → G) (w : List (Fin 7 × Bool)) :
    FreeGroup.lift (fun i : Fin 7 => x i.val) (FreeGroup.mk w) =
      wordProd x (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := l
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte]

theorem vImg_rels :
    ∀ r ∈ relsV, FreeGroup.lift
    (fun i : Fin 7 => vImg i) (FreeGroup.mk r) = 1 := by
  intro r hr
  rw [lift_mk_seven]
  exact relators_eval CFSG.Sporadic.Co3.co3Facts vBridgeFacts (seedG D3)
    (rep_seedLetters CFSG.Sporadic.Co3.co3Facts) _ (List.mem_map_of_mem hr)

noncomputable abbrev vToJ :
    V →* J D3 := vLift
    (fun i : Fin 7 => vImg i) vImg_rels

@[expose] noncomputable def vLetter (z : ℤ) : V :=
  if h : 0 < z ∧ (z - 1).toNat < 7 then PresentedGroup.of ⟨(z - 1).toNat, h.2⟩
  else if h' : (-z - 1).toNat < 7 then (PresentedGroup.of ⟨(-z - 1).toNat, h'⟩)⁻¹ else 1

theorem vToJ_vLetter {z : ℤ}
    (hz : z.natAbs ≤ 7) :
    vToJ (vLetter z) = imgG vSpec (seedG D3) z := by
  unfold vLetter imgG
  by_cases hpos : 0 < z
  · have h1 : 0 < z ∧ (z - 1).toNat < 7 := ⟨hpos, by omega⟩
    simp only [h1, and_self, ↓reduceDIte, ↓reduceIte, vLift_of]
  · have h2 : (-z - 1).toNat < 7 := by omega
    simp only [h2, hpos, false_and, ↓reduceDIte, ↓reduceIte, map_inv, vLift_of]

theorem wordG_mem_range {w : List ℤ}
    (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 7) :
    CFSG.Sporadic.Th.wordG (imgG vSpec (seedG D3)) w ∈ vToJ.range := by
  refine ⟨CFSG.Sporadic.Th.wordG vLetter w, ?_⟩
  unfold CFSG.Sporadic.Th.wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact vToJ_vLetter (hw z hz).2

theorem surjWord_mem_range {i : ℕ}
    (hi : i < 2) :
    CFSG.Sporadic.Th.wordG (imgG vSpec (seedG D3)) vSpec.surjWords[i]! ∈ vToJ.range :=
  wordG_mem_range fun z hz => vBridgeFacts.letters _ (surjWords_mem vBridgeFacts hi) z hz

theorem exists_surjective_V :
    Function.Surjective vToJ := by
  have hF := CFSG.Sporadic.Co3.co3Facts
  have hG := rep_seedLetters hF
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab D3, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · have hr := rep_surjWord hF vBridgeFacts (seedG D3) hG (i := 0) (by decide)
    rw [vBridgeFacts.surjA] at hr
    rw [← eq_of_rep_eq hF hr (rep_a hF.toBaseFacts)]
    exact surjWord_mem_range (by decide)
  · have hr := rep_surjWord hF vBridgeFacts (seedG D3) hG (i := 1) (by decide)
    rw [vBridgeFacts.surjB] at hr
    rw [← eq_of_rep_eq hF hr (rep_b hF.toBaseFacts)]
    exact surjWord_mem_range (by decide)

noncomputable def co3NativeEquiv :
    CFSG.Blueprint.NativeSporadic.Co3 ≃* J D3 :=
  seedEquiv CFSG.Sporadic.Co3.co3Facts.toBaseFacts

theorem card_J3 : Nat.card (J D3) = 495766656000 := by
  rw [← Nat.card_congr co3NativeEquiv.toEquiv, CFSG.Sporadic.Co3.card_Co3]

theorem vEquivNative :
    VEquivNative :=
    by
  obtain ⟨hfin, hcard⟩ := vCardLe
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective vToJ exists_surjective_V hcard card_J3.ge
  exact ⟨co3NativeEquiv.trans e⟩

end CFSG.EvenSmallLie.SympSix.Co3Ident
