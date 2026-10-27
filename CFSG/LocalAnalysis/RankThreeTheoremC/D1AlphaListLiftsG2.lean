module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsAlg
public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.Adapters.TauCetiExceptional.BridgeG2
public import Certificates.Certificate19800

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Multipliers.G23 CFSG.Sporadic.He.Native
  TauCeti

noncomputable def elt (w : List (Fin 4)) : adjointGroup .G2 (ZMod 3) :=
  (w.map (rootElt (RingEquiv.refl (ZMod 3)))).prod

theorem elt_append (u v : List (Fin 4)) : elt (u ++ v) = elt u * elt v := by
  simp [elt]

theorem elt_nil : elt [] = 1 := by
  simp [elt]

theorem elt_wpow (w : List (Fin 4)) (k : ℕ) : elt (wpow w k) = elt w ^ k := by
  induction k with
  | zero => simp [wpow, elt_nil]
  | succ k ih =>
    rw [pow_succ', ← ih, ← elt_append, wpow, wpow, List.replicate_succ, List.flatten_cons]

theorem val_matHom_elt (w : List (Fin 4)) :
    ((matHom (RingEquiv.refl (ZMod 3)) (elt w) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = toMat 3 14 (rootProd w) :=
  val_matHom_prod _ w

theorem rootArrs_getElem (j : Fin 4) : rootArrs[j.val]! = rootArr j := by
  fin_cases j <;> simp [rootArrs]

theorem wordM_eq (w : List (Fin 4)) : wordM w = rootProd w := by
  induction w with
  | nil => simp only [wordM, rootProd, List.foldr_nil]
  | cons j w ih =>
    simp only [wordM, rootProd, List.foldr_cons] at ih ⊢
    rw [rootArrs_getElem, ih]

theorem elt_eq_of_wordM {u v : List (Fin 4)} (h : (wordM u == wordM v) = true) :
    elt u = elt v := by
  apply matHom_injective (RingEquiv.refl (ZMod 3))
  refine Units.ext ?_
  rw [val_matHom_elt, val_matHom_elt, ← wordM_eq, ← wordM_eq]
  exact toMat_eq_of_beq h

theorem elt_ne_one_of_neOne {w : List (Fin 4)} (h : neOne (wordM w) = true) : elt w ≠ 1 := by
  intro h1
  have hm : toMat 3 14 (wordM w) = 1 := by
    rw [wordM_eq, ← val_matHom_elt, h1, map_one, Units.val_one]
  unfold neOne at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨i, hi, j, hj, hne⟩ := h
  have key := congrFun (congrFun hm ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, Matrix.one_apply] at key
  rcases eq_or_ne i j with rfl | hij
  · have h1 : ((((wordM w)[i]!)[i]! : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3) := by simpa using key
    exact hne (by simpa using (ZMod.natCast_eq_natCast_iff' _ _ 3).mp h1)
  · have h1 : ((((wordM w)[i]!)[j]! : ℕ) : ZMod 3) = ((0 : ℕ) : ZMod 3) := by
      simpa [Fin.ext_iff, hij] using key
    exact hne (by simpa [hij] using (ZMod.natCast_eq_natCast_iff' _ _ 3).mp h1)

theorem cube_mem_eqPairs (i : Fin 3) : (wY i ++ wY i ++ wY i, []) ∈ eqPairs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))

theorem comm_mem_eqPairs (i j : Fin 3) : (wY i ++ wY j, wY j ++ wY i) ∈ eqPairs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr
      ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩)))

theorem inv_mem_eqPairs (i : Fin 3) : (wInv i ++ wY i, wY i ++ wY i ++ wInv i) ∈ eqPairs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))

theorem sw_mem_eqPairs {p : Fin 3 × Fin 3} (hp : p ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)]) :
    (wSw p.1 p.2 ++ wY p.1, wY p.2 ++ wSw p.1 p.2) ∈ eqPairs ∧
      (wSw p.1 p.2 ++ wY p.2, wY p.1 ++ wSw p.1 p.2) ∈ eqPairs :=
  ⟨List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, by simp⟩),
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, by simp⟩)⟩

theorem hasLiftableTriple_adjointG2 :
    HasLiftableTriple (adjointGroup .G2 (ZMod 3)) := by
  have h := Certificates.certificate19800
  unfold liftCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hEq, hNe⟩ := h
  have hE : ∀ p ∈ eqPairs, elt p.1 = elt p.2 := fun p hp => elt_eq_of_wordM (hEq p hp)
  have hN : ∀ w ∈ nePairs, elt w ≠ 1 := fun w hw => elt_ne_one_of_neOne (hNe w hw)
  refine HasLiftableTriple.of_relations (fun i => elt (wY i)) ?_ ?_ ?_
    (fun i => elt (wInv i)) ?_ (fun i j => elt (wSw i j)) ?_
  · intro i
    have := hE _ (cube_mem_eqPairs i)
    simpa [elt_append, elt_nil, mul_assoc] using this
  · intro i j
    have := hE _ (comm_mem_eqPairs i j)
    simpa [elt_append] using this
  · intro a b c habc
    by_contra hne
    have hmem : wMono a.val b.val c.val ∈ nePairs := by
      unfold nePairs
      rw [List.mem_map]
      refine ⟨(a.val, b.val, c.val), ?_, rfl⟩
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · simp [List.mem_flatMap, List.mem_range, ZMod.val_lt]
      · simpa [ZMod.val_eq_zero] using hne
    apply hN _ hmem
    simpa [wMono, elt_append, elt_wpow, mul_assoc] using habc
  · intro i
    have := hE _ (inv_mem_eqPairs i)
    simpa [elt_append, mul_assoc] using this
  · intro i j hij
    have hp : (i, j) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    obtain ⟨h1, h2⟩ := sw_mem_eqPairs hp
    exact ⟨by simpa [elt_append] using hE _ h1, by simpa [elt_append] using hE _ h2⟩

section TauCeti

theorem hasLiftableTriple_G2 (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (hq : q.card = 3) :
    HasLiftableTriple (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  obtain ⟨hp, he⟩ := primePower_eq_three hq
  have hK : Nat.card (ZMod 3) = q.card := by
    rw [Nat.card_zmod, PrimePower.card_def, hp, he, pow_one]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by rw [hp]; decide) (ZMod 3) hK
  let c : AdjointQuotient .G2 (ZMod 3) ≃* adjointGroup .G2 (ZMod 3) :=
    (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  exact HasLiftableTriple.of_mulEquiv (c.symm.trans b) hasLiftableTriple_adjointG2

end TauCeti

end CFSG.LocalAnalysis.RankThreeTheoremC.G2Lift
