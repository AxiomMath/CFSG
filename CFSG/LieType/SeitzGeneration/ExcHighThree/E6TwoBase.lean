
module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.F4Two
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4FrameCentral
public import Certificates.Data.E6F4Letters

@[expose] public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.Ree CFSG.LieType.SeitzGeneration.ExcHighThree.F4Two

section Links

variable {K : Type} [Field K] [CharP K 2]

theorem coe_evalG6 (w : List E6Bits.Letter) :
    ((E6Bits.evalG K w : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (w.map fun l => ((l.elt K : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)).prod := by
  induction w with
  | nil => simp
  | cons l w ih => simp [ih]

theorem orbitWord_one :
    TwistTag.E6.orbitWord (f4FoldedIndex ⟨0, by decide⟩) = [⟨1, by decide⟩] := by decide

theorem orbitWord_three :
    TwistTag.E6.orbitWord (f4FoldedIndex ⟨1, by decide⟩) = [⟨3, by decide⟩] := by decide

theorem orbitWord_two_four :
    TwistTag.E6.orbitWord (f4FoldedIndex ⟨2, by decide⟩) = [⟨2, by decide⟩, ⟨4, by decide⟩] := by
  decide

theorem orbitWord_zero_five :
    TwistTag.E6.orbitWord (f4FoldedIndex ⟨3, by decide⟩) = [⟨0, by decide⟩, ⟨5, by decide⟩] := by
  decide

theorem embE6F4_xE_coe' (L : Type) [Field L] (j : Fin Tag.F4.rank) (c : L) :
    ((embE6F4 L (xE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) = f4OrbitXUnit L j c := by
  have hT : (e6FixedF4EquivAll L).symm (xE Tag.F4 L j c) = OX j c := by
    rw [MulEquiv.symm_apply_eq, psi_OX]
  have h1 : ((embE6F4 L (xE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) =
      (((e6FixedF4EquivAll L).symm (xE Tag.F4 L j c) :
        twistedFixedGroup TwistTag.E6 L (RingHom.id L)) : ModGL TwistTag.E6.tag L) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

theorem xUnit_one_sq (τ : Tag) (i : Fin τ.rank) :
    xUnit τ K i 1 * xUnit τ K i 1 = 1 := by
  have h : xElement (τ := τ) (K := K) i 1 * xElement i 1 = 1 := by
    rw [← xElement_add, CharTwo.add_self_eq_zero, xElement_zero]
  exact congrArg Subtype.val h

theorem weylElt_one_eq_xyx' (τ : Tag) (i : Fin τ.rank) :
    weylElt τ K i 1 = xUnit τ K i 1 * yUnit τ K i 1 * xUnit τ K i 1 := by
  apply Units.ext
  have : (-1 : K) = 1 := CharTwo.neg_eq (1 : K)
  simp [weylElt, xUnit, yUnit, this]

theorem xUnit_weylElt_xUnit (τ : Tag) (i : Fin τ.rank) :
    xUnit τ K i 1 * weylElt τ K i 1 * xUnit τ K i 1 = yUnit τ K i 1 := by
  rw [weylElt_one_eq_xyx']
  calc xUnit τ K i 1 * (xUnit τ K i 1 * yUnit τ K i 1 * xUnit τ K i 1) * xUnit τ K i 1
      = (xUnit τ K i 1 * xUnit τ K i 1) * yUnit τ K i 1 * (xUnit τ K i 1 * xUnit τ K i 1) := by
        group
    _ = yUnit τ K i 1 := by rw [xUnit_one_sq, one_mul, mul_one]

theorem embE6F4_yE_coe' (L : Type) [Field L] (j : Fin Tag.F4.rank) (c : L) :
    ((embE6F4 L (yE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) = f4OrbitYUnit L j c := by
  have hT : (e6FixedF4EquivAll L).symm (yE Tag.F4 L j c) = OY j c := by
    rw [MulEquiv.symm_apply_eq, psi_OY]
  have h1 : ((embE6F4 L (yE Tag.F4 L j c) : adjointGroup .E6 L) : ModGL Tag.E6 L) =
      (((e6FixedF4EquivAll L).symm (yE Tag.F4 L j c) :
        twistedFixedGroup TwistTag.E6 L (RingHom.id L)) : ModGL TwistTag.E6.tag L) := by
    unfold embE6F4 isoE6F4
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      Subgroup.coe_subtype]
    rfl
  rw [h1, hT]
  rfl

theorem iota_xE : ∀ j : Fin Tag.F4.rank, (embE6F4 K (xE Tag.F4 K j 1) : ModGL Tag.E6 K) =
    (E6Bits.evalG K (wordOfCodes6 (orbitNodes j)) : ModGL Tag.E6 K)
  | ⟨0, _⟩ => by
    rw [embE6F4_xE_coe', coe_evalG6]
    simp only [f4OrbitXUnit, orbitWord_one, wordOfCodes6, orbitNodes, letterOfCode6, List.map,
      List.prod_cons, List.prod_nil]
    rfl
  | ⟨1, _⟩ => by
    rw [embE6F4_xE_coe', coe_evalG6]
    simp only [f4OrbitXUnit, orbitWord_three, wordOfCodes6, orbitNodes, letterOfCode6, List.map,
      List.prod_cons, List.prod_nil]
    rfl
  | ⟨2, _⟩ => by
    rw [embE6F4_xE_coe', coe_evalG6]
    simp only [f4OrbitXUnit, orbitWord_two_four, wordOfCodes6, orbitNodes, letterOfCode6, List.map,
      List.prod_cons, List.prod_nil]
    rfl
  | ⟨3, _⟩ => by
    rw [embE6F4_xE_coe', coe_evalG6]
    simp only [f4OrbitXUnit, orbitWord_zero_five, wordOfCodes6, orbitNodes, letterOfCode6, List.map,
      List.prod_cons, List.prod_nil]
    rfl

theorem coe_evalG6_xnx (i : Fin Tag.E6.rank) :
    ((E6Bits.evalG K [E6Bits.Letter.x i, E6Bits.Letter.n i, E6Bits.Letter.x i] :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = yUnit Tag.E6 K i 1 := by
  rw [coe_evalG6]
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc]
  exact xUnit_weylElt_xUnit Tag.E6 i

theorem f4OrbitYUnit_one : f4OrbitYUnit K ⟨0, by decide⟩ 1 = yUnit Tag.E6 K ⟨1, by decide⟩ 1 := by
  simp only [f4OrbitYUnit, orbitWord_one, List.map, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem f4OrbitYUnit_three : f4OrbitYUnit K ⟨1, by decide⟩ 1 = yUnit Tag.E6 K ⟨3, by decide⟩ 1 := by
  simp only [f4OrbitYUnit, orbitWord_three, List.map, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem f4OrbitYUnit_two_four : f4OrbitYUnit K ⟨2, by decide⟩ 1 =
    yUnit Tag.E6 K ⟨2, by decide⟩ 1 * yUnit Tag.E6 K ⟨4, by decide⟩ 1 := by
  simp only [f4OrbitYUnit, orbitWord_two_four, List.map, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem f4OrbitYUnit_zero_five : f4OrbitYUnit K ⟨3, by decide⟩ 1 =
    yUnit Tag.E6 K ⟨0, by decide⟩ 1 * yUnit Tag.E6 K ⟨5, by decide⟩ 1 := by
  simp only [f4OrbitYUnit, orbitWord_zero_five, List.map, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem iota_yE : ∀ j : Fin Tag.F4.rank, (embE6F4 K (yE Tag.F4 K j 1) : ModGL Tag.E6 K) =
    (E6Bits.evalG K (wordOfCodes6 ((orbitNodes j).flatMap fun i => [i, 6 + i, i])) :
      ModGL Tag.E6 K)
  | ⟨0, _⟩ => by
    have hw : wordOfCodes6 ((orbitNodes 0).flatMap fun i => [i, 6 + i, i]) =
        [E6Bits.Letter.x ⟨1, by decide⟩, E6Bits.Letter.n ⟨1, by decide⟩,
          E6Bits.Letter.x ⟨1, by decide⟩] := rfl
    rw [hw]
    exact (embE6F4_yE_coe' K ⟨0, by decide⟩ 1).trans
      (f4OrbitYUnit_one.trans (coe_evalG6_xnx ⟨1, by decide⟩).symm)
  | ⟨1, _⟩ => by
    have hw : wordOfCodes6 ((orbitNodes 1).flatMap fun i => [i, 6 + i, i]) =
        [E6Bits.Letter.x ⟨3, by decide⟩, E6Bits.Letter.n ⟨3, by decide⟩,
          E6Bits.Letter.x ⟨3, by decide⟩] := rfl
    rw [hw]
    exact (embE6F4_yE_coe' K ⟨1, by decide⟩ 1).trans
      (f4OrbitYUnit_three.trans (coe_evalG6_xnx ⟨3, by decide⟩).symm)
  | ⟨2, _⟩ => by
    have hw : wordOfCodes6 ((orbitNodes 2).flatMap fun i => [i, 6 + i, i]) =
        [E6Bits.Letter.x ⟨2, by decide⟩, E6Bits.Letter.n ⟨2, by decide⟩,
          E6Bits.Letter.x ⟨2, by decide⟩] ++
        [E6Bits.Letter.x ⟨4, by decide⟩, E6Bits.Letter.n ⟨4, by decide⟩,
          E6Bits.Letter.x ⟨4, by decide⟩] := rfl
    rw [hw, E6Bits.evalG_append, Subgroup.coe_mul]
    exact (embE6F4_yE_coe' K ⟨2, by decide⟩ 1).trans
      (f4OrbitYUnit_two_four.trans
        (congrArg₂ (· * ·) (coe_evalG6_xnx ⟨2, by decide⟩).symm (coe_evalG6_xnx ⟨4, by decide⟩).symm))
  | ⟨3, _⟩ => by
    have hw : wordOfCodes6 ((orbitNodes 3).flatMap fun i => [i, 6 + i, i]) =
        [E6Bits.Letter.x ⟨0, by decide⟩, E6Bits.Letter.n ⟨0, by decide⟩,
          E6Bits.Letter.x ⟨0, by decide⟩] ++
        [E6Bits.Letter.x ⟨5, by decide⟩, E6Bits.Letter.n ⟨5, by decide⟩,
          E6Bits.Letter.x ⟨5, by decide⟩] := rfl
    rw [hw, E6Bits.evalG_append, Subgroup.coe_mul]
    exact (embE6F4_yE_coe' K ⟨3, by decide⟩ 1).trans
      (f4OrbitYUnit_zero_five.trans
        (congrArg₂ (· * ·) (coe_evalG6_xnx ⟨0, by decide⟩).symm (coe_evalG6_xnx ⟨5, by decide⟩).symm))

theorem weylElement_F4_eq (j : Fin Tag.F4.rank) :
    weylElement Tag.F4 K j = xE Tag.F4 K j 1 * yE Tag.F4 K j 1 * xE Tag.F4 K j 1 := by
  apply Subtype.ext
  exact weylElt_one_eq_xyx' Tag.F4 j

theorem iota_nE (j : Fin Tag.F4.rank) :
    embE6F4 K (weylElement Tag.F4 K j) =
      E6Bits.evalG K (wordOfCodes6 (f4ToE6Letter (4 + j.val))) := by
  apply Subtype.ext
  have hl : f4ToE6Letter (4 + j.val) = orbitNodes j.val ++
      (orbitNodes j.val).flatMap (fun i => [i, 6 + i, i]) ++ orbitNodes j.val := by
    unfold f4ToE6Letter
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rw [hl, wordOfCodes6, List.map_append, List.map_append]
  change _ = ((E6Bits.evalG K (wordOfCodes6 (orbitNodes j.val) ++
    wordOfCodes6 ((orbitNodes j.val).flatMap fun i => [i, 6 + i, i]) ++
    wordOfCodes6 (orbitNodes j.val)) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)
  rw [E6Bits.evalG_append, E6Bits.evalG_append, Subgroup.coe_mul, Subgroup.coe_mul,
    ← iota_xE j, ← iota_yE j, weylElement_F4_eq, map_mul, map_mul, Subgroup.coe_mul,
    Subgroup.coe_mul]

theorem iota_letter {c : ℕ} (hc : c < 8) :
    embE6F4 K ((CFSG.RankThree.PartOne.SEITZX.letterOfCode c).elt K) =
      E6Bits.evalG K (wordOfCodes6 (f4ToE6Letter c)) := by
  unfold CFSG.RankThree.PartOne.SEITZX.letterOfCode
  by_cases h : c < 4
  · rw [dif_pos h]
    apply Subtype.ext
    have := iota_xE (K := K) ⟨c, h⟩
    unfold f4ToE6Letter
    rw [if_pos h]
    exact this
  · rw [dif_neg h]
    have h2 : (c - 4) % 4 = c - 4 := Nat.mod_eq_of_lt (by omega)
    have hn := iota_nE (K := K) ⟨(c - 4) % 4, by simp only [Tag.rank]; omega⟩
    simp only [Fin.val_mk] at hn
    rw [show 4 + (c - 4) % 4 = c by omega] at hn
    exact hn

end Links

section Closing

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem xElement_weylElement_xElement (i : Fin Tag.E6.rank) :
    xElement (τ := Tag.E6) (K := K) i 1 * weylElement Tag.E6 K i * xElement i 1 =
      yElement i 1 :=
  Subtype.ext (xUnit_weylElt_xUnit Tag.E6 i)

theorem evalG6_x (i : Fin Tag.E6.rank) :
    E6Bits.evalG K (wordOfCodes6 [i.val]) = xElement i 1 := by
  have hi : i.val < 6 := i.2
  have : wordOfCodes6 [i.val] = [E6Bits.Letter.x i] := by
    show [letterOfCode6 i.val] = _
    rw [letterOfCode6, dif_pos hi]
    rfl
  rw [this, E6Bits.evalG_singleton]
  rfl

theorem evalG6_xnx (i : Fin Tag.E6.rank) :
    E6Bits.evalG K (wordOfCodes6 [i.val, 6 + i.val, i.val]) = yElement i 1 := by
  have hi : i.val < 6 := i.2
  have hn : letterOfCode6 (6 + i.val) = E6Bits.Letter.n i := by
    rw [letterOfCode6, dif_neg (by omega)]
    exact congrArg E6Bits.Letter.n (Fin.ext (by simp only [Fin.val_mk]; omega))
  have : wordOfCodes6 [i.val, 6 + i.val, i.val] =
      [E6Bits.Letter.x i, E6Bits.Letter.n i, E6Bits.Letter.x i] := by
    show [letterOfCode6 i.val, letterOfCode6 (6 + i.val), letterOfCode6 i.val] = _
    rw [letterOfCode6, dif_pos hi, hn]
    rfl
  rw [this]
  apply Subtype.ext
  exact coe_evalG6_xnx i

def E6CloseAtTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ E₃ : Subgroup (adjointGroup .F4 K), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
      ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure (((embE6F4 K).range : Set (adjointGroup .E6 K)) ∪
        (Subgroup.centralizer ({embE6F4 K e} : Set (adjointGroup .E6 K)) :
          Set (adjointGroup .E6 K))) = ⊤

end Closing

section Glue

theorem e6HighInF4_two_of_close (hNR : LangPlaneKillsRoot Tag.F4) (hT : E6TwistedTransport)
    (h2 : E6CloseAtTwo) : E6HighInF4 2 :=
  e6HighInF4_of_closing_emb (fun K _ _ hK E₀ hexp _ _ => conj_into_fixE6_two K hK hexp)
    (fun K _ _ hK E₃ hexp hcard hnF => by
      by_cases h : Nat.card K = 2
      · exact h2 K h E₃ hexp hcard
      · obtain ⟨e, he, he1, X, hX, hclose, hnorm⟩ := frame_two_of_three_le hNR hT
          e6FrameCentral_holds K hK (by have := Finite.one_lt_card (α := K); omega) E₃ hexp hcard hnF
        refine ⟨e, he, he1, ?_⟩
        rw [range_embE6F4]
        exact closure_of_frame (fixE6 K) (embE6F4 K e) X hX hclose hnorm)

end Glue

end CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two
