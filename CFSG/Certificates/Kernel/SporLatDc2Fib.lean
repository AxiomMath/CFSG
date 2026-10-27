module

public import CFSG.Certificates.Kernel.SporLatDc2Key

public section

namespace CFSG.KC.SLD2

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F
open CFSG.KC.SLDc (sortedLt lookC chunksOK chunksOK_pos)
open CFSG.KC.LQT.PW (imgW)
open MulAction

theorem eq_of_mul_le {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) (h : a * b ≤ a' * b')
    (ha' : 0 < a') (hb' : 0 < b') : a = a' ∧ b = b' := by
  have h1 : a' * b ≤ a * b := Nat.mul_le_mul_right b ha
  have h2 : a' * b' ≤ a' * b := Nat.mul_le_mul_left a' hb
  have hbb : b = b' := Nat.eq_of_mul_eq_mul_left ha' (le_antisymm (h1.trans h) h2)
  subst hbb
  exact ⟨Nat.eq_of_mul_eq_mul_right hb' (le_antisymm h h1), rfl⟩

namespace Dc2SoundCtx

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (P : Dc2SoundCtx Γ n)

theorem fRest_facts : chunksOK P.D.fB P.D.fC = true ∧ P.D.fC.flatten.headD [] = P.C.Δ ∧
    P.D.fC.flatten.length = P.C.N2 ∧ P.D.fC.flatten.Nodup ∧ ∀ i < P.C.N2, i ≠ 0 →
      ∃ j < i, ∃ v < P.C.nf, imgW P.D.fw (P.D.fpc.getD v 0) j = i := by
  have h := P.parts.2.2.2.1
  unfold fRestOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  rw [beq_iff_eq] at h2
  rw [Nat.beq_eq] at h3 h4 h5 h7
  have h8' : ∀ i ∈ P.D.ford, i < P.D.fC.flatten.length := fun i hi => by
    have e := List.all_eq_true.1 h8 i hi
    rw [Nat.blt_eq] at e
    omega
  obtain ⟨-, hnd⟩ := perm_of_ord h1 (by omega) h8' h9
  refine ⟨h1, h2, h3, hnd, fun i hi hi0 => ?_⟩
  have hiz : i < (List.zip P.D.fpar P.D.fvia).length := by
    rw [List.length_zip, h4, h5, Nat.min_self]
    exact hi
  have e := (SLDc.allIdx_iff _ 0 _).1 h6 i hiz
  simp only [Nat.zero_add, List.getElem_zip, Bool.or_eq_true, Nat.beq_eq, hi0, false_or,
    Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨_, e.1.1, _, e.1.2, e.2⟩

theorem fRow_spec {l : ℕ} (hl : l < P.C.nf) : ∀ j < P.C.N2,
    imgW P.D.fw (P.D.fpc.getD l 0) j < P.C.N2 ∧
    P.D.fC.flatten.getD (imgW P.D.fw (P.D.fpc.getD l 0) j) [] =
      fAct P.C l (P.D.fC.flatten.getD j []) :=
  rowC_spec P.fRest_facts.1 P.fRest_facts.2.2.1 (fAct P.C l) (P.parts.2.2.2.2.1 l hl)

theorem fib_reach : ∀ i < P.C.N2, ∃ h ∈ P.H, P.D.fC.flatten.getD i [] = (h • P.Δl).val := by
  obtain ⟨-, hhead, -, -, htree⟩ := P.fRest_facts
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      refine ⟨1, P.H.one_mem, ?_⟩
      rw [one_smul, ← List.headD_eq_getD, hhead]
      rfl
    · obtain ⟨j, hj, v, hv, he⟩ := htree i hi hi0
      obtain ⟨h, hh, e⟩ := ih j hj (by omega)
      refine ⟨P.els.getD v 1 * h, P.H.mul_mem (P.getD_mem_take hv) hh, ?_⟩
      rw [← he, (P.fRow_spec hv j (by omega)).2, e, mul_smul, P.smul_fAct hv]

theorem fib_closed {h : Γ} (hh : h ∈ P.H) :
    ∀ z : PrL n, z.val ∈ P.D.fC.flatten → (h • z).val ∈ P.D.fC.flatten := by
  obtain ⟨-, -, hlen, -⟩ := P.fRest_facts
  refine P.smul_mem_take (F := {z : PrL n | z.val ∈ P.D.fC.flatten}) (fun l hl _ z hz => ?_) hh
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hz
  obtain ⟨h1, h2⟩ := P.fRow_spec hl j (by omega)
  have h1' : imgW P.D.fw (P.D.fpc.getD l 0) j < P.D.fC.flatten.length := by omega
  show (P.els.getD l 1 • z).val ∈ P.D.fC.flatten
  rw [P.smul_fAct hl, ← e, ← List.getD_eq_getElem _ [] hj, ← h2, List.getD_eq_getElem _ _ h1']
  exact List.getElem_mem _

theorem orbit_H_Δ : orbit P.H P.Δl = {z : PrL n | z.val ∈ P.D.fC.flatten} := by
  obtain ⟨hC, hhead, hlen, -⟩ := P.fRest_facts
  ext z
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    have hpos : 0 < P.D.fC.flatten.length := (chunksOK_pos hC).2
    have hΔ : P.Δl.val ∈ P.D.fC.flatten := by
      show P.C.Δ ∈ P.D.fC.flatten
      rw [← hhead, List.headD_eq_getD, List.getD_eq_getElem _ _ hpos]
      exact List.getElem_mem hpos
    exact P.fib_closed hh P.Δl hΔ
  · intro hz
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hz
    obtain ⟨h, hh, e'⟩ := P.fib_reach i (by omega)
    refine ⟨⟨h, hh⟩, PrL.ext ?_⟩
    show (h • P.Δl).val = z.val
    rw [← e', List.getD_eq_getElem _ _ hi, e]

theorem ncard_orbit_H_Δ : (orbit P.H P.Δl).ncard = P.C.N2 := by
  obtain ⟨-, -, hlen, hnd, -⟩ := P.fRest_facts
  rw [P.orbit_H_Δ, ← hlen]
  refine ncard_label_mem PrL.val (fun _ _ h => PrL.ext h) hnd fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨h, -, e⟩ := P.fib_reach i (by omega)
  exact ⟨h • P.Δl, by rw [← e, List.getD_eq_getElem _ _ hi]⟩

theorem count : P.U1 P.D.R1 = orbit Γ P.Λl ∧ stabilizer Γ P.Λl = P.H ∧
    stabilizer Γ P.Δl ⊓ P.H = P.S := by
  have hΓ : Nat.card (stabilizer Γ P.Λl) * (orbit Γ P.Λl).ncard =
      P.C.N1 * P.C.N2 * 2 ^ P.C.k := by
    rw [← index_stabilizer, Subgroup.card_mul_index, P.hN]
  have hfin : (orbit Γ P.Λl).Finite := Set.finite_range _
  have ha : P.C.N1 ≤ (orbit Γ P.Λl).ncard :=
    P.ncard_lev1 ▸ Set.ncard_le_ncard (P.U1_sub _) hfin
  have hb : Nat.card P.H ≤ Nat.card (stabilizer Γ P.Λl) := Subgroup.card_le_of_le P.H_le_stab
  have hH : Nat.card P.H = P.C.N2 * Nat.card (stabilizer Γ P.Δl ⊓ P.H : Subgroup Γ) := by
    rw [card_eq_ncard_mul P.H P.Δl, P.ncard_orbit_H_Δ, card_stabilizer_eq]
  have hSle : P.S ≤ stabilizer Γ P.Δl ⊓ P.H := le_inf P.S_le_stabΔ P.S_le_H
  have hS : Nat.card P.S = 2 ^ P.C.k := P.hk
  have hc : 2 ^ P.C.k ≤ Nat.card (stabilizer Γ P.Δl ⊓ P.H : Subgroup Γ) :=
    hS ▸ Subgroup.card_le_of_le hSle
  have hpos : 0 < P.C.N1 * P.C.N2 * 2 ^ P.C.k := P.hN ▸ Nat.card_pos
  have h1 : 0 < P.C.N1 := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have h2 : 0 < P.C.N2 := Nat.pos_of_ne_zero fun h => by simp [h] at hpos
  have hle : (orbit Γ P.Λl).ncard * Nat.card (stabilizer Γ P.Λl) ≤ P.C.N1 * Nat.card P.H := by
    rw [mul_comm, hΓ, hH, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
  obtain ⟨e1, e2⟩ := eq_of_mul_le ha hb hle h1 Nat.card_pos
  have e3 : Nat.card (stabilizer Γ P.Δl ⊓ P.H : Subgroup Γ) = 2 ^ P.C.k := by
    rw [e1, e2, hH] at hΓ
    have e : P.C.N1 * P.C.N2 * Nat.card (stabilizer Γ P.Δl ⊓ P.H : Subgroup Γ) =
        P.C.N1 * P.C.N2 * 2 ^ P.C.k := by
      rw [← hΓ]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos h1 h2) e
  refine ⟨Set.eq_of_subset_of_ncard_le (P.U1_sub _) (e1.trans P.ncard_lev1.symm).le hfin,
    (Subgroup.eq_of_le_of_card_ge P.H_le_stab e2.le).symm,
    (Subgroup.eq_of_le_of_card_ge hSle (by rw [e3, hS])).symm⟩

end Dc2SoundCtx

end CFSG.KC.SLD2

end
