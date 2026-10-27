module

public import CFSG.Certificates.Kernel.AS91K468.Common

public section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K CFSG.Quasithin.H13.AS91.Two
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
  CFSG.GF2Type.Smith1979.GammaU.Enum

theorem base_sound (P P2 Eb I : List ℕ) (EP : enumGrp (pQ.map unpackA) = P.map unpackA)
    (E2 : enumGrp (p2Q.map unpackA) = P2.map unpackA)
    (EE : enumGrp (ebQ.map unpackA) = Eb.map unpackA)
    (EI : enumGrp (iQ.map unpackA) = I.map unpackA) (BP : ∀ q ∈ P, q < 2 ^ 144)
    (B2 : ∀ q ∈ P2, q < 2 ^ 144) (BE : ∀ q ∈ Eb, q < 2 ^ 144) (BI : ∀ q ∈ I, q < 2 ^ 144)
    (h : baseAt P P2 Eb I = true) : baseOK47 () = true := by
  simp only [baseAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  simp only [baseOK47, Bool.and_eq_true]
  rw [pRows_eq, p2Rows_eq, ebRows_eq, iRows_eq, EP, E2, EE, EI]
  refine ⟨⟨⟨⟨⟨⟨?_, gensS iQ h2⟩, ?_⟩, ?_⟩, dedupS BI 4 h5 h6⟩, ?_⟩, ?_⟩
  · exact (all_map_congr fun x hx => ofListS BP (p2Q_lt x hx)).trans h1
  · rw [idRS, containsS BI oneQ_lt]
    exact h3
  · rw [closedS _ _ BI]
    exact h4
  · refine (all_map_congr fun x hx => ?_).trans h7
    rw [containsS BE (iQ_lt x hx), containsS B2 (iQ_lt x hx)]
  · refine (all_map_congr fun x hx => ?_).trans h8
    rw [containsS B2 (BE x hx), containsS BI (BE x hx)]

theorem fGQ_getD_lt (i : ℕ) : fGQ.getD i oneQ < 2 ^ 144 := fRQ_lt i _ List.mem_cons_self

theorem f_sound (Eb : List ℕ) (FL : List (List ℕ))
    (EE : enumGrp (ebQ.map unpackA) = Eb.map unpackA) (BE : ∀ q ∈ Eb, q < 2 ^ 144)
    (EF : ∀ i < 3, enumGrp ((fRQ i).map unpackA) = (FL.getD i []).map unpackA)
    (BF : ∀ i < 3, ∀ q ∈ FL.getD i [], q < 2 ^ 144) (h : fAt Eb FL = true) :
    fOK47 () = true := by
  rw [fAt, List.all_eq_true] at h
  simp only [fOK47]
  rw [ebRows_eq, EE, List.all_eq_true]
  intro i hi
  have hi3 := List.mem_range.1 hi
  have hh := h i hi
  simp only [Bool.and_eq_true] at hh ⊢
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hh
  rw [fRows_eq i, EF i hi3]
  refine ⟨⟨⟨⟨⟨gensS _ h1, ?_⟩, ?_⟩, dedupS (BF i hi3) 8 h4 h5⟩, ?_⟩, ?_⟩
  · rw [idRS, containsS (BF i hi3) oneQ_lt]
    exact h2
  · rw [closedS _ _ (BF i hi3)]
    exact h3
  · exact (all_map_congr fun x hx => containsS BE (fRQ_lt i x hx)).trans h6
  · rw [List.all_eq_true] at h7 ⊢
    intro j hj
    have hj3 := List.mem_range.1 hj
    rw [fRows_eq j, EF j hj3, fGen_eq, idRS, List.getD_map,
      containsS (BF j hj3) (fGQ_getD_lt i)]
    exact h7 j hj

theorem conj_eq (x : ℕ) {F F' : List ℕ} (hF : ∀ q ∈ F, q < 2 ^ 144)
    (hF' : ∀ q ∈ F', q < 2 ^ 144) :
    conjInto (unpackA x) (F.map unpackA) (F'.map unpackA) = conjQ x F F' := by
  rw [conjInto, conjQ]
  refine all_map_congr fun f _ => any_map_congr fun f' _ => ?_
  rw [mulRS, mulRS, beqS (mulQ_lt' _ _) (mulQ_lt' _ _)]

theorem presW1_eq (x : ℕ) :
    (w1List.all fun c => w1List.contains (appN (unpackA x) c)) = presW1 x := by
  rw [presW1]
  exact allc fun c _ => by rw [appNS, w1_contains]

theorem g_sound (G P2 Eb : List ℕ) (FL : List (List ℕ))
    (EG : enumGrp (gZQ.map unpackA) = G.map unpackA)
    (E2 : enumGrp (p2Q.map unpackA) = P2.map unpackA)
    (EE : enumGrp (ebQ.map unpackA) = Eb.map unpackA)
    (EFL : fLists () = FL.map fun F => F.map unpackA) (BG : ∀ q ∈ G, q < 2 ^ 144)
    (B2 : ∀ q ∈ P2, q < 2 ^ 144) (BE : ∀ q ∈ Eb, q < 2 ^ 144)
    (BF : ∀ F ∈ FL, ∀ q ∈ F, q < 2 ^ 144) (h : gAt (G.filter presW1) P2 Eb FL = true) :
    gOK47 () = true := by
  have hg1 : g1List () = (G.filter presW1).map unpackA := by
    rw [g1List, gZRows_eq, EG]
    exact filter_map_congr fun x _ => presW1_eq x
  rw [gAt] at h
  simp only [gOK47]
  rw [hg1, p2Rows_eq, ebRows_eq, E2, EE, EFL]
  refine (all_map_congr fun x hx => ?_).trans h
  have bx := BG x (List.mem_filter.1 hx).1
  have hc : ∀ F ∈ FL, ∀ F' ∈ FL,
      conjInto (unpackA x) (F.map unpackA) (F'.map unpackA) = conjQ x F F' :=
    fun F hF F' hF' => conj_eq x (BF F hF) (BF F' hF')
  exact congrArg₂ (fun a b => a && b) (all_mapL fun F hF => any_mapL fun F' hF' => hc F hF F' hF')
    (congrArg₂ (fun a b => !a || b) (all_mapL fun F hF => hc F hF F hF)
      (any_mapL fun e _ => any_mapL fun p _ => by rw [mulRS, beqS (mulQ_lt' _ _) bx]))

theorem fLQ_enum : ∀ i < 3, enumGrp ((fRQ i).map unpackA) = (fLQ.getD i []).map unpackA
  | 0, _ => enumS _
  | 1, _ => enumS _
  | 2, _ => enumS _
  | _ + 3, h => absurd h (by omega)

theorem fLQ_lt : ∀ i < 3, ∀ q ∈ fLQ.getD i [], q < 2 ^ 144
  | 0, _ => enumS_lt (fRQ 0)
  | 1, _ => enumS_lt (fRQ 1)
  | 2, _ => enumS_lt (fRQ 2)
  | _ + 3, h => absurd h (by omega)

theorem fLists_eq : fLists () = fLQ.map fun F => F.map unpackA := by
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [fLists, hr, fLQ, List.map_cons, List.map_cons, List.map_cons, List.map_nil, List.map_cons,
    List.map_cons, List.map_cons, List.map_nil, fRows_eq, fRows_eq, fRows_eq, enumS, enumS, enumS]

theorem fLQ_all_lt : ∀ F ∈ fLQ, ∀ q ∈ F, q < 2 ^ 144 := by
  intro F hF
  rw [fLQ, List.mem_cons, List.mem_cons, List.mem_singleton] at hF
  rcases hF with rfl | rfl | rfl <;> exact enumS_lt _

theorem ok47_of (h1 : base47Q = true) (h2 : f47Q = true) (h3 : g47Q = true) : ok47 () = true := by
  have e1 := base_sound _ _ _ _ (enumS pQ) (enumS p2Q) (enumS ebQ) (enumS iQ) (enumS_lt _)
    (enumS_lt _) (enumS_lt _) (enumS_lt _) h1
  have e2 := f_sound _ _ (enumS ebQ) (enumS_lt _) fLQ_enum fLQ_lt h2
  have e3 := g_sound _ _ _ _ (enumS gZQ) (enumS p2Q) (enumS ebQ) fLists_eq (enumS_lt _)
    (enumS_lt _) (enumS_lt _) fLQ_all_lt h3
  rw [ok47, e1, e2, e3]
  rfl

end Certificates.Kernel.AS91K468
