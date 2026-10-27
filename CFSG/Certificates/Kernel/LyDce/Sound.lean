module

public import Certificates.Data.Kernel.LyDce.Defs
public import CFSG.Sporadic.Recognition.LyonsFinalDist2

public section

namespace CFSG.KC.LyDce

open CFSG.KC.LyReplay CFSG.Sporadic.Recognition.LyonsSims.LyFinal

variable {G : Type*} [Group G] {g : Fin 6 → G}

theorem stepOKD_sound {bOK : List (Fin 6 × Bool) → Bool}
    {kR eR tR dR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))}
    (hB : ∀ w, bOK w = true → FreeGroup.lift g (FreeGroup.mk w) = 1)
    (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1)
    (hK : ∀ p ∈ kR, FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2))
    (hE : ∀ p ∈ eR, FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2))
    (hT : ∀ p ∈ tR, FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2))
    (hD : ∀ p ∈ dR, FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2))
    {k : Nat} {old new : List (Fin 6 × Bool)} (h : stepOKD bOK kR eR tR dR k old new = true) :
    FreeGroup.lift g (FreeGroup.mk old) = FreeGroup.lift g (FreeGroup.mk new) := by
  match k, h with
  | 0, h =>
    have h1 := hB _ h
    rw [lift_mk_append, lift_derivInv hinv] at h1
    exact mul_inv_eq_one.1 h1
  | 1, h => exact ruleOK_sound hK h
  | 2, h => exact ruleOK_sound hE h
  | 3, h => exact ruleOK_sound hT h
  | 4, h => exact ruleOK_sound hD h
  | _ + 5, h => exact absurd h (by simp [stepOKD])

theorem replayD_sound {bOK : List (Fin 6 × Bool) → Bool}
    {kR eR tR dR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))}
    (hstep : ∀ k old new, stepOKD bOK kR eR tR dR k old new = true →
      FreeGroup.lift g (FreeGroup.mk old) = FreeGroup.lift g (FreeGroup.mk new)) :
    ∀ (ss : List (Nat × Nat × List Nat × List Nat)) (cur : List (Fin 6 × Bool)),
      replayD bOK kR eR tR dR cur ss = true → FreeGroup.lift g (FreeGroup.mk cur) = 1
  | [], cur, h => by
    have e : cur = [] := List.isEmpty_iff.1 h
    rw [e, lift_mk_nil]
  | s :: ss, cur, h => by
    rw [replayD, Bool.and_eq_true] at h
    obtain ⟨hs, h⟩ := h
    cases hc : replaceAt cur s.1 (wordOf s.2.2.1) (wordOf s.2.2.2) with
    | none => rw [hc] at h; exact absurd h Bool.false_ne_true
    | some cur' =>
      rw [hc] at h
      rw [lift_replaceAt hc (hstep _ _ _ hs)]
      exact replayD_sound hstep ss cur' h

theorem factOKD_sound {bOK : List (Fin 6 × Bool) → Bool}
    {kR eR tR dR : List (List (Fin 6 × Bool) × List (Fin 6 × Bool))}
    (hstep : ∀ k old new, stepOKD bOK kR eR tR dR k old new = true →
      FreeGroup.lift g (FreeGroup.mk old) = FreeGroup.lift g (FreeGroup.mk new))
    {nt : Nat × Nat} {r v a : List Nat} {ss : List (Nat × Nat × List Nat × List Nat)}
    (h : factOKD bOK kR eR tR dR nt r v a ss = true) :
    nt.1 < 5 ∧ nt.2 < 5 ∧ isBWord (wordOf r) = true ∧ isBWord (wordOf v) = true ∧
      isBWord (wordOf a) = true ∧ FreeGroup.lift g (FreeGroup.mk (startW nt.1 nt.2 r v a)) = 1 := by
  simp only [factOKD, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, h3, h4, h5,
    replayD_sound hstep ss _ h6⟩

theorem lift_startW (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1) (i j : Nat)
    (r v a : List Nat) (h : FreeGroup.lift g (FreeGroup.mk (startW i j r v a)) = 1) :
    FreeGroup.lift g (FreeGroup.mk (wordOf (rootC i))) * FreeGroup.lift g (FreeGroup.mk (wordOf r)) *
        g 5 =
      FreeGroup.lift g (FreeGroup.mk (wordOf a)) *
        FreeGroup.lift g (FreeGroup.mk (wordOf (rootC j))) *
        FreeGroup.lift g (FreeGroup.mk (wordOf v)) := by
  have ek : FreeGroup.lift g (FreeGroup.mk (wordOf [10])) = g 5 := lift_mk_kLetter g
  simp only [startW, wordOf, List.map_append] at h
  simp only [wordOf] at ek ⊢
  rw [lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_append, ek,
    lift_derivInv hinv, lift_derivInv hinv, lift_derivInv hinv] at h
  rw [← mul_inv_eq_one, ← h]
  group

theorem dRuleOf_sound (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1)
    {r : List (Fin 6 × Bool)} {m l : Nat} (hs : dShapeOK r m l = true)
    (hr : FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∀ p ∈ dRuleOf r m l,
      FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2) := by
  have e : r = r.take (m + l) ++ derivInv (r.take m) ++ r.drop (m + l + m) :=
    beq_iff_eq.1 hs
  have eA : r.take (m + l) = r.take m ++ (r.drop m).take l := List.take_add ..
  rw [e, lift_mk_append, lift_mk_append, lift_derivInv hinv] at hr
  set A := FreeGroup.lift g (FreeGroup.mk (r.take (m + l))) with hA
  set X := FreeGroup.lift g (FreeGroup.mk (r.take m))
  set S := FreeGroup.lift g (FreeGroup.mk ((r.drop m).take l))
  set C := FreeGroup.lift g (FreeGroup.mk (r.drop (m + l + m)))
  have hAXS : A = X * S := by rw [hA, eA, lift_mk_append]
  have hC : C = (A * X⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hr
  intro p hp
  simp only [dRuleOf, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · change A = FreeGroup.lift g (FreeGroup.mk (derivInv (r.drop (m + l + m)) ++ r.take m))
    rw [lift_mk_append, lift_derivInv hinv]
    change A = C⁻¹ * X
    rw [hC]
    group
  · change FreeGroup.lift g (FreeGroup.mk (r.take m ++ derivInv ((r.drop m).take l))) =
      FreeGroup.lift g (FreeGroup.mk (r.drop (m + l + m) ++ r.take m))
    rw [lift_mk_append, lift_mk_append, lift_derivInv hinv]
    change X * S⁻¹ = C * X
    rw [hC, hAXS]
    group

theorem dRulesOK_sound (hinv : ∀ i : Fin 6, i.val ≠ 1 → g i * g i = 1)
    {RD : List (List (Fin 6 × Bool))} {lens : List (Nat × Nat)} {dR : List (List Nat × List Nat)}
    (h : dRulesOK RD lens dR = true) (hRD : ∀ r ∈ RD, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    ∀ p ∈ rulesOf dR,
      FreeGroup.lift g (FreeGroup.mk p.1) = FreeGroup.lift g (FreeGroup.mk p.2) := by
  simp only [dRulesOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨-, hshape⟩, he⟩ := h
  intro p hp
  rw [he, List.mem_flatMap] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  exact dRuleOf_sound hinv (hshape q hq) (hRD q.1 (List.of_mem_zip hq).1) p hpq

end CFSG.KC.LyDce

end
