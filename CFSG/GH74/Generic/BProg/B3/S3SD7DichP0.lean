module

public import CFSG.GH74.Generic.BProg.B3.S3SD7DichGen

public section

namespace CFSG.GH74.Generic.BProg.B3.S3SD7DichP0

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.Generic.BProg.B3.S3SD7DichGen

@[expose] def tl (l : List (Fin 7)) (i : Fin 7) : Fin 7 := l.getD i.val 0

@[expose] def invT (l : List (Fin 7)) (i : Fin 7) : Fin 7 :=
  ((List.finRange 7).find? fun j => tl l j == i).getD 0

@[expose] def validT (l : List (Fin 7)) : Bool :=
  (List.finRange 7).all fun i => invT l (tl l i) == i && tl l (invT l i) == i

theorem validT_spec {l : List (Fin 7)} (h : validT l = true) :
    (∀ i, invT l (tl l i) = i) ∧ (∀ i, tl l (invT l i) = i) := by
  unfold validT at h
  rw [List.all_eq_true] at h
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := h i (List.mem_finRange i)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · have := h i (List.mem_finRange i)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2

@[expose] def ofTab (l : List (Fin 7)) : Perm (Fin 7) :=
  if h : validT l = true then ⟨tl l, invT l, (validT_spec h).1, (validT_spec h).2⟩ else 1

@[expose] def pe (a b : Perm (Fin 7)) : Bool := (List.finRange 7).all fun i => a i == b i

theorem pe_iff {a b : Perm (Fin 7)} : pe a b = true ↔ a = b := by
  unfold pe
  rw [List.all_eq_true]
  constructor
  · intro h
    refine Equiv.ext fun i => ?_
    have := h i (List.mem_finRange i)
    simpa using this
  · rintro rfl i _
    simp

theorem pe_eq_false_iff {a b : Perm (Fin 7)} : pe a b = false ↔ a ≠ b := by
  constructor
  · intro h e
    have := pe_iff.2 e
    rw [h] at this
    exact Bool.false_ne_true this
  · intro h
    cases hb : pe a b with
    | false => rfl
    | true => exact absurd (pe_iff.1 hb) h

theorem any_pe_iff {l : List (Perm (Fin 7))} {a : Perm (Fin 7)} : l.any (pe a) = true ↔ a ∈ l := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hb, h⟩
    rw [pe_iff.1 h]
    exact hb
  · intro h
    exact ⟨a, h, pe_iff.2 rfl⟩

@[expose] def commb (σ x : Perm (Fin 7)) : Bool := (List.finRange 7).all fun i => σ (x i) == x (σ i)

theorem commb_iff {σ x : Perm (Fin 7)} : commb σ x = true ↔ σ * x = x * σ := by
  unfold commb
  rw [List.all_eq_true]
  constructor
  · intro h
    refine Equiv.ext fun i => ?_
    have := h i (List.mem_finRange i)
    simpa using this
  · intro h i _
    have := congrArg (fun f : Perm (Fin 7) => f i) h
    simpa using this

@[expose] def P0tabs : List (List (Fin 7)) :=
  [[0,1,2,3,4,5,6], [0,1,2,3,5,4,6], [0,1,3,2,4,5,6], [1,0,2,3,4,5,6], [0,1,3,2,5,4,6],
   [1,0,2,3,5,4,6], [1,0,3,2,4,5,6], [2,3,0,1,4,5,6], [3,2,1,0,4,5,6], [1,0,3,2,5,4,6],
   [2,3,0,1,5,4,6], [2,3,1,0,4,5,6], [3,2,0,1,4,5,6], [3,2,1,0,5,4,6], [2,3,1,0,5,4,6],
   [3,2,0,1,5,4,6]]

@[expose] def P0l : List (Perm (Fin 7)) := P0tabs.map ofTab

theorem P0l_mul_check : P0l.all (fun a => P0l.all fun b => P0l.any (pe (a * b))) = true := by
  decide +kernel

theorem P0l_inv_check : P0l.all (fun a => P0l.any (pe a⁻¹)) = true := by decide +kernel

theorem P0l_one_check : P0l.any (pe 1) = true := by decide +kernel

@[expose] def P0 : Subgroup (Perm (Fin 7)) where
  carrier := {σ | σ ∈ P0l}
  one_mem' := any_pe_iff.1 P0l_one_check
  mul_mem' := by
    intro a b ha hb
    exact any_pe_iff.1 (List.all_eq_true.1 (List.all_eq_true.1 P0l_mul_check a ha) b hb)
  inv_mem' := by
    intro a ha
    exact any_pe_iff.1 (List.all_eq_true.1 P0l_inv_check a ha)

theorem mem_P0 {σ : Perm (Fin 7)} : σ ∈ P0 ↔ σ ∈ P0l := Iff.rfl

@[expose] def nodupB : List (Perm (Fin 7)) → Bool
  | [] => true
  | a :: l => !(l.any (pe a)) && nodupB l

theorem nodupB_sound : ∀ l : List (Perm (Fin 7)), nodupB l = true → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
    intro h
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ih h.2⟩
    have := any_pe_iff.2 hmem
    rw [h.1] at this
    exact Bool.false_ne_true this

theorem P0l_nodup : P0l.Nodup := nodupB_sound _ (by decide +kernel)

theorem P0l_length : P0l.length = 16 := by decide +kernel

theorem card_P0 : Nat.card ↥P0 = 16 := by
  have h1 : Nat.card ↥P0 = Nat.card ↥(P0l.toFinset) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => by simp [mem_P0])
  rw [h1, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup P0l_nodup, P0l_length]

theorem index_P0 : P0.index = 315 := by
  have h := Subgroup.card_mul_index P0
  rw [card_P0, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have h7 : (7 : ℕ).factorial = 5040 := by decide
  omega

theorem P0_isPGroup : IsPGroup 2 ↥P0 := IsPGroup.of_card (n := 4) (by rw [card_P0]; norm_num)

@[expose] def P0Sylow : Sylow 2 (Perm (Fin 7)) :=
  P0_isPGroup.toSylow (by rw [index_P0]; decide)

theorem finite_sylow : Finite (Sylow 2 (Perm (Fin 7))) := Sylow.finite_of_finiteIndex P0Sylow

theorem exists_conj_le_P0 (E : Subgroup (Perm (Fin 7))) (hE : IsPGroup 2 ↥E) :
    ∃ σ : Perm (Fin 7), E.map (MulAut.conj σ).toMonoidHom ≤ P0 := by
  have := finite_sylow
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) Q P0Sylow
  refine ⟨σ, ?_⟩
  have h1 : E.map (MulAut.conj σ).toMonoidHom ≤
      (Q : Subgroup (Perm (Fin 7))).map (MulAut.conj σ).toMonoidHom := Subgroup.map_mono hQ
  have h2 : ((σ • Q : Sylow 2 (Perm (Fin 7))) : Subgroup (Perm (Fin 7))) =
      (Q : Subgroup (Perm (Fin 7))).map (MulAut.conj σ).toMonoidHom := rfl
  rw [hσ] at h2
  exact h1.trans (le_of_eq h2.symm)

theorem P0_noncomm : ∃ a ∈ P0, ∃ b ∈ P0, a * b ≠ b * a := by
  refine ⟨ofTab [1,0,2,3,4,5,6], mem_P0.2 (any_pe_iff.1 (by decide +kernel)),
    ofTab [2,3,0,1,4,5,6], mem_P0.2 (any_pe_iff.1 (by decide +kernel)), ?_⟩
  intro h
  have : pe (ofTab [1,0,2,3,4,5,6] * ofTab [2,3,0,1,4,5,6])
      (ofTab [2,3,0,1,4,5,6] * ofTab [1,0,2,3,4,5,6]) = true := pe_iff.2 h
  revert this
  decide +kernel

@[expose] def cand2 (g h : Perm (Fin 7)) : List Quad :=
  S0q.filter fun q => commb (qp q) g || commb (qp q) h || commb (qp q) (g * h)

@[expose] def suppL (x : Perm (Fin 7)) : List (Fin 7) := (List.finRange 7).filter fun i => x i != i

@[expose] def evenB (x : Perm (Fin 7)) : Bool := decide (Perm.sign x = 1)

@[expose] def rfb (g h : Perm (Fin 7)) : Bool :=
  (suppL g).length == 4 && suppL h == suppL g && suppL (g * h) == suppL g && evenB g && evenB h

@[expose] def r2 (g h : Perm (Fin 7)) : Bool :=
  !pe g 1 && !pe h 1 && !pe g h && pe (g * g) 1 && pe (h * h) 1 && pe (g * h) (h * g)

@[expose] def code (x : Perm (Fin 7)) : ℕ :=
  (List.finRange 7).foldl (fun acc i => 8 * acc + (x i).val) 0

@[expose] def canon (g h : Perm (Fin 7)) : Bool :=
  decide (code g < code h) && decide (code h < code (g * h))

theorem canon_exists : P0l.all (fun g => P0l.all fun h => !(r2 g h) ||
    [g, h, g * h].any fun g' => [g, h, g * h].any fun h' => r2 g' h' && canon g' h') = true := by
  decide +kernel

theorem good2_all : P0l.all (fun g => P0l.all fun h =>
    !(r2 g h && canon g h) || rfb g h || genOKb (cand2 g h)) = true := by
  decide +kernel

@[expose] def r3 (g h k : Perm (Fin 7)) : Bool :=
  r2 g h && !pe k 1 && !pe k g && !pe k h && !pe k (g * h) && pe (k * k) 1 && pe (g * k) (k * g) &&
    pe (h * k) (k * h)

@[expose] def E8 (g h k : Perm (Fin 7)) : List (Perm (Fin 7)) :=
  [1, g, h, k, g * h, g * k, h * k, g * h * k]

@[expose] def sub8 (S : List (Perm (Fin 7))) (g h k : Perm (Fin 7)) : Bool :=
  S.all fun m => (E8 g h k).any (pe m)

@[expose] def ta : Perm (Fin 7) := ofTab [1,0,2,3,4,5,6]
@[expose] def tb : Perm (Fin 7) := ofTab [0,1,3,2,4,5,6]
@[expose] def tc : Perm (Fin 7) := ofTab [0,1,2,3,5,4,6]

@[expose] def M1l : List (Perm (Fin 7)) :=
  [1, ta, tb, tc, ta * tb, ta * tc, tb * tc, ta * tb * tc]

@[expose] def ub : Perm (Fin 7) := ofTab [1,0,3,2,4,5,6]
@[expose] def vb : Perm (Fin 7) := ofTab [2,3,0,1,4,5,6]
@[expose] def Vbl : List (Perm (Fin 7)) := [1, ub, vb, ub * vb]

theorem cls3_all : P0l.all (fun g => P0l.all fun h => !(r2 g h) || P0l.all fun k =>
    !(r3 g h k) || sub8 M1l g h k || sub8 Vbl g h k) = true := by
  decide +kernel

@[expose] def M1hyp : List (Perm (Fin 7) × Perm (Fin 7)) :=
  [(ta, tb), (ta, tc), (tb, tc), (ta, tb * tc), (tb, ta * tc), (tc, ta * tb), (ta * tb, ta * tc)]

@[expose] def L1 : List Quad :=
  S0q.filter fun q => M1hyp.any fun p => commb (qp q) p.1 && commb (qp q) p.2

theorem M1hyp_check :
    M1hyp.all (fun p => r2 p.1 p.2 && M1l.any (pe p.1) && M1l.any (pe p.2)) = true := by
  decide +kernel

theorem L1_gen : genOKb L1 = true := by decide +kernel

theorem Vb_check : r2 ub vb = true ∧ rfb ub vb = true := by decide +kernel

end CFSG.GH74.Generic.BProg.B3.S3SD7DichP0
