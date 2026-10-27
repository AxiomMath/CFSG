module

public import Certificates.Data.Kernel.Misc.PermFuse
public import CFSG.Certificates.Kernel.Misc.PermClosWSound
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.KC.Misc.Fuse

open Equiv CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW

private theorem w_pos_of_lt {n w : ℕ} (hw : n < 2 ^ w) (hn0 : n ≠ 0) : 0 < w := by
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · subst h0
    rw [pow_zero] at hw
    omega
  · exact h0

private theorem wcode_shr_of_lt {n w : ℕ} (hw : n < 2 ^ w) (hw0 : 0 < w) (σ : Perm (Fin n)) :
    wcode w σ >>> (n * w) = 0 :=
  CFSG.KS.PF.shr_zero_of_fld hw0 (fld_wcode hw σ) (fun i hi => by
    have : ¬ i < n := by omega
    simp [this])

private theorem wcode_mul_of_lt {n w : ℕ} (hw : n < 2 ^ w) (hn : n < 2 ^ 32)
    (a b : Perm (Fin n)) :
    wcode w (a * b) = CFSG.KC.Enum.pcomp n w (CFSG.KS.mask w) (wcode w a) (wcode w b) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have e : wcode w (a * b) = 0 := by simp [wcode]
    rw [e]
    rfl
  · have hw0 := w_pos_of_lt hw (by omega)
    refine CFSG.KS.PF.eq_of_fields hw0 (wcode_shr_of_lt hw hw0 _)
      (CFSG.KS.PF.pcomp_shr _ _ hn hw0) fun i hi => ?_
    rw [pg_wcode_nat hw (a * b) hi, CFSG.KS.PF.pg_pcomp hn hi, pg_wcode_nat hw b hi,
      pg_wcode hw a (b ⟨i, hi⟩)]
    rfl

private theorem wcode_inv_of_lt {n w : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) :
    CFSG.KS.pinvS n w (CFSG.KS.mask w) (wcode w σ) = wcode w σ⁻¹ := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have e : wcode w σ⁻¹ = 0 := by simp [wcode]
    rw [e]
    rfl
  · have hw0 := w_pos_of_lt hw (by omega)
    refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PinvS.pinvS_shr hw (injK_wcode hw σ).1)
      (wcode_shr_of_lt hw hw0 _) fun i hi => ?_
    have e : CFSG.KC.Enum.pg w (CFSG.KS.mask w) (wcode w σ) (σ⁻¹ ⟨i, hi⟩) = i := by
      rw [pg_wcode hw σ]
      simp
    have h1 := CFSG.KS.PinvS.pg_pinvS hw (injK_wcode hw σ) (Fin.isLt (σ⁻¹ ⟨i, hi⟩))
    rw [e] at h1
    rw [h1, pg_wcode_nat hw σ⁻¹ hi]

private theorem conjM_wcode {n w : ℕ} (hw : n < 2 ^ w) (hn : n < 2 ^ 32) (x g : Perm (Fin n)) :
    conjM n w (wcode w x) (wcode w g) = wcode w (g * x * g⁻¹) := by
  unfold conjM
  rw [wcode_inv_of_lt hw, ← wcode_mul_of_lt hw hn g x, ← wcode_mul_of_lt hw hn (g * x) g⁻¹]

theorem orb_tree {n w : ℕ} (hw : n < 2 ^ w) (hn : n < 2 ^ 32) (gs : List (Perm (Fin n)))
    (r : Perm (Fin n)) {G E PA : ℕ → ℕ} {N : ℕ}
    (hG : ∀ j < gs.length, G j = wcode w (gs.getD j 1))
    (ht : ∀ k < N, treeAt (conjM n w) (wcode w r) G gs.length E PA k = true) :
    ∀ k < N, ∃ t ∈ Subgroup.closure {g | g ∈ gs}, wcode w (t * r * t⁻¹) = E k := by
  have hgen : ∀ l < gs.length, gs.getD l 1 ∈ Subgroup.closure {g | g ∈ gs} := fun l hl =>
    Subgroup.subset_closure (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact List.getElem_mem hl)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h0 : Nat.beq (E 0) (wcode w r) = true := ht 0 hk
      exact ⟨1, Subgroup.one_mem _, by rw [one_mul, inv_one, mul_one, Nat.eq_of_beq_eq_true h0]⟩
    | succ k =>
      have h : CFSG.KC.LQT.P.letB (PA (k + 1)) (fun r =>
          CFSG.KC.LQT.P.letB (Nat.land r 16777215) fun p =>
            CFSG.KC.LQT.P.letB (Nat.shiftRight r 24) fun l =>
              CFSG.KC.Ord.andB (Nat.blt p (k + 1)) (CFSG.KC.Ord.andB (Nat.blt l gs.length)
                (Nat.beq (E (k + 1)) (conjM n w (E p) (G l))))) = true := ht (k + 1) hk
      rw [letB_eq, letB_eq, letB_eq] at h
      obtain ⟨hp, h⟩ := andB_eq_true h
      obtain ⟨hl, h⟩ := andB_eq_true h
      have hp' := Nat.blt_eq.mp hp
      have hl' := Nat.blt_eq.mp hl
      obtain ⟨t, htm, hte⟩ := ih _ hp' (by omega)
      refine ⟨gs.getD _ 1 * t, Subgroup.mul_mem _ (hgen _ hl') htm, ?_⟩
      rw [Nat.eq_of_beq_eq_true h, hG _ hl', ← hte, conjM_wcode hw hn]
      simp only [mul_inv_rev, mul_assoc]

theorem card_mul_cent_le {G : Type*} [Group G] (S : Subgroup G) [Finite S] (r : G) (N : ℕ)
    (t : ℕ → G) (ht : ∀ k < N, t k ∈ S)
    (hinj : ∀ i < N, ∀ j < N, t i * r * (t i)⁻¹ = t j * r * (t j)⁻¹ → i = j) :
    N * Nat.card ↥(S ⊓ Subgroup.centralizer {r}) ≤ Nat.card S := by
  have hC : S ⊓ Subgroup.centralizer {r} ≤ S := inf_le_left
  let f : Fin N × ↥(S ⊓ Subgroup.centralizer {r}) → S := fun p =>
    ⟨t p.1 * p.2, S.mul_mem (ht p.1 p.1.2) (hC p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨j, d⟩ h
    have h' : t i * (c : G) = t j * d := congrArg Subtype.val h
    have hcr : (c : G) * r = r * c :=
      Subgroup.mem_centralizer_singleton_iff.1 (c.2.2)
    have hdr : (d : G) * r = r * d :=
      Subgroup.mem_centralizer_singleton_iff.1 (d.2.2)
    have hconj : ∀ (u : G) (e : G), e * r = r * e → (u * e) * r * (u * e)⁻¹ = u * r * u⁻¹ := by
      intro u e he
      rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc e r, he, mul_assoc r,
        mul_inv_cancel_left, ← mul_assoc]
    have hij : (i : ℕ) = j := by
      refine hinj i i.2 j j.2 ?_
      rw [← hconj (t i) c hcr, ← hconj (t j) d hdr, h']
    have hij' : i = j := Fin.ext hij
    subst hij'
    have hcd : (c : G) = d := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext hcd)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at this

end CFSG.KC.Misc.Fuse

end
