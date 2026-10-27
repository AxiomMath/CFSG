module

public import CFSG.Certificates.Kernel.Spor.ONNQSound
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQRelab

public section

namespace CFSG.KS.ONNQ

open CFSG.KS.TW CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

variable {n : ℕ}

theorem foldr_GZ_eq {T U : ℕ → ℕ → ℕ} {f : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hT : ∀ h < j, ∀ x : Fin n, T h x = (f h x : ℕ))
    (hU : ∀ h < j, ∀ x : Fin n, U h x = ((f h)⁻¹ x : ℕ)) :
    ∀ w : List ℤ, plettersOK j w = true → ∀ x : Fin n,
      w.foldr (fun z y => GZ T U z y) (x : ℕ) =
        (Quiver.SchreierGraph.evalWord (fun h : Fin j => f h) (ptoLetters j w) x : ℕ)
  | [], _, x => by simp [Quiver.SchreierGraph.evalWord_nil, ptoLetters]
  | l :: w, hw, x => by
    obtain ⟨⟨hl0, hlj⟩, hw'⟩ := plettersOK_cons hw
    rw [List.foldr_cons, foldr_GZ_eq hT hU w hw' x, ptoLetters_cons' hl0 hlj]
    unfold GZ
    by_cases hp : 0 < l
    · rw [if_pos hp, decide_eq_true hp, Quiver.SchreierGraph.evalWord_cons_true,
        Equiv.Perm.mul_apply, show l.toNat - 1 = l.natAbs - 1 by omega]
      exact hT _ (by omega) _
    · rw [if_neg hp, decide_eq_false hp, Quiver.SchreierGraph.evalWord_cons_false,
        Equiv.Perm.mul_apply, show (-l).toNat - 1 = l.natAbs - 1 by omega]
      exact hU _ (by omega) _

theorem gz_inv {T U : ℕ → ℕ → ℕ} {f : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    (hT : ∀ h < j, ∀ x : Fin n, T h x = (f h x : ℕ))
    (hU : ∀ h < j, ∀ x : Fin n, U h x = ((f h)⁻¹ x : ℕ)) {z : ℤ} (hz0 : z ≠ 0)
    (hzj : z.natAbs ≤ j) {y : ℕ} (hy : y < n) :
    GZ T U z y < n ∧ GZ T U (-z) (GZ T U z y) = y := by
  unfold GZ
  by_cases hp : 0 < z
  · have hn : ¬ (0 < -z) := by omega
    rw [if_pos hp, if_neg hn, show (-(-z)).toNat - 1 = z.toNat - 1 by omega]
    have h1 : T (z.toNat - 1) y = (f (z.toNat - 1) ⟨y, hy⟩ : ℕ) := hT _ (by omega) ⟨y, hy⟩
    rw [h1, hU _ (by omega) (f (z.toNat - 1) ⟨y, hy⟩)]
    exact ⟨Fin.isLt _, by simp⟩
  · have hn : 0 < -z := by omega
    rw [if_neg hp, if_pos hn]
    have h1 : U ((-z).toNat - 1) y = ((f ((-z).toNat - 1))⁻¹ ⟨y, hy⟩ : ℕ) :=
      hU _ (by omega) ⟨y, hy⟩
    rw [h1, hT _ (by omega) ((f ((-z).toNat - 1))⁻¹ ⟨y, hy⟩)]
    exact ⟨Fin.isLt _, by simp⟩

variable {TT UU : ℕ → ℕ → ℕ} {f : ℕ → Equiv.Perm (Fin n)}

theorem ev_eq8 (hT : ∀ h < 8, ∀ x : Fin n, TT h x = (f h x : ℕ))
    (hU : ∀ h < 8, ∀ x : Fin n, UU h x = ((f h)⁻¹ x : ℕ)) {b : ℕ} (hb : ∀ h < 8, twH b h < 8)
    {w : List ℤ} (hw : plettersOK 8 w = true) (x : Fin n) :
    ev TT UU b w x =
      (Quiver.SchreierGraph.evalWord (fun h : Fin 8 => f (twH b h)) (ptoLetters 8 w) x : ℕ) :=
  foldr_GZ_eq (T := actT TT b) (U := actT UU b) (f := fun h => f (twH b h))
    (fun h hh y => hT _ (hb h hh) y)
    (fun h hh y => hU _ (hb h hh) y) w hw x

theorem ev_winv (hT : ∀ h < 8, ∀ x : Fin n, TT h x = (f h x : ℕ))
    (hU : ∀ h < 8, ∀ x : Fin n, UU h x = ((f h)⁻¹ x : ℕ)) {b : ℕ} (hb : ∀ h < 8, twH b h < 8)
    {w : List ℤ} (hw : plettersOK 8 w = true) {E : Equiv.Perm (Fin n)}
    (hE : ∀ x : Fin n, ev TT UU b w x = (E x : ℕ)) (x : Fin n) :
    ev TT UU b (winv w) x = (E⁻¹ x : ℕ) := by
  have hG : ∀ z ∈ w, ∀ y < n, GZ (actT TT b) (actT UU b) z y < n ∧
      GZ (actT TT b) (actT UU b) (-z) (GZ (actT TT b) (actT UU b) z y) = y := by
    intro z hz y hy
    have hzv := List.all_eq_true.1 hw z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hzv
    exact gz_inv (T := actT TT b) (U := actT UU b) (f := fun h => f (twH b h))
      (fun h hh y => hT _ (hb h hh) y)
      (fun h hh y => hU _ (hb h hh) y) hzv.1 hzv.2 hy
  have h := (foldr_inv (G := fun z y => GZ (actT TT b) (actT UU b) z y) w hG
    ((E⁻¹ x : Fin n) : ℕ) (E⁻¹ x).isLt).2
  have e : w.foldr (fun z y => GZ (actT TT b) (actT UU b) z y) ((E⁻¹ x : Fin n) : ℕ) = x := by
    have h1 := hE (E⁻¹ x)
    unfold ev at h1
    rw [h1]
    simp
  rw [e] at h
  unfold ev winv
  exact h

@[expose] def wcl (c : ℕ) : Fin 5 × Bool :=
  (⟨if c / 2 < 4 then c / 2 else 4, by split_ifs <;> omega⟩, decide (c % 2 = 0))

theorem ev_wit (hT : ∀ h < 8, ∀ x : Fin n, TT h x = (f h x : ℕ))
    (hU : ∀ h < 8, ∀ x : Fin n, UU h x = ((f h)⁻¹ x : ℕ)) {b : ℕ} (hb : ∀ h < 8, twH b h < 8)
    {D : ℕ → ℕ} {a i : ℕ} (S R : List ℤ → Equiv.Perm (Fin n)) (g nw m : ℕ → List ℤ)
    (hnw : ∀ k < 4, plettersOK 8 (wd (D (36 + k))) = true)
    (hmw : plettersOK 8 (wd (D (40 + i))) = true) (hgw : plettersOK 8 (wd (D (a + 1))) = true)
    (hn : ∀ k < 4, ∀ x : Fin n, ev TT UU b (wd (D (36 + k))) x = (S (nw k) x : ℕ))
    (hm : ∀ x : Fin n, ev TT UU b (wd (D (40 + i))) x = (S (m i) x : ℕ))
    (hg : ∀ x : Fin n, ev TT UU b (wd (D (a + 1))) x = (R (g (a + 1)) x : ℕ)) (cs : List ℕ) :
    ∀ x : Fin n, ev TT UU b (cs.flatMap (wlw D a i)) x =
      (Quiver.SchreierGraph.evalWord (nqWitL S R g nw m a i) (cs.map wcl) x : ℕ) := by
  have hlet : ∀ c, ∀ y : Fin n, ev TT UU b (wlw D a i c) y =
      ((if c % 2 = 0 then nqWitL S R g nw m a i (wcl c).1
        else (nqWitL S R g nw m a i (wcl c).1)⁻¹) y : ℕ) := by
    intro c y
    by_cases h4 : c / 2 < 4
    · have hσ : nqWitL S R g nw m a i (wcl c).1 = S (nw (c / 2)) := by
        simp [nqWitL, wcl, h4]
      rw [hσ]
      unfold wlw
      rw [if_pos h4]
      by_cases h2 : c % 2 = 0
      · rw [if_pos h2, if_pos h2]
        exact hn _ h4 y
      · rw [if_neg h2, if_neg h2]
        exact ev_winv hT hU hb (hnw _ h4) (hn _ h4) y
    · have hσ : nqWitL S R g nw m a i (wcl c).1 = R (g (a + 1)) * S (m i) := by
        simp [nqWitL, wcl, h4]
      rw [hσ]
      unfold wlw
      rw [if_neg h4]
      by_cases h2 : c % 2 = 0
      · rw [if_pos h2, if_pos h2, ev_append, hm, hg, Equiv.Perm.mul_apply]
      · rw [if_neg h2, if_neg h2, ev_append, ev_winv hT hU hb hgw hg y,
          ev_winv hT hU hb hmw hm, mul_inv_rev, Equiv.Perm.mul_apply]
  induction cs with
  | nil =>
    intro x
    simp [ev, Quiver.SchreierGraph.evalWord_nil]
  | cons c cs ih =>
    intro x
    rw [List.flatMap_cons, ev_append, ih x, List.map_cons, hlet c]
    have hc : Quiver.SchreierGraph.evalWord (nqWitL S R g nw m a i) (wcl c :: cs.map wcl) =
        (if c % 2 = 0 then nqWitL S R g nw m a i (wcl c).1
          else (nqWitL S R g nw m a i (wcl c).1)⁻¹) *
          Quiver.SchreierGraph.evalWord (nqWitL S R g nw m a i) (cs.map wcl) := by
      by_cases h2 : c % 2 = 0
      · have e : wcl c = ((wcl c).1, true) := Prod.ext rfl (by simp [wcl, h2])
        rw [e, Quiver.SchreierGraph.evalWord_cons_true, if_pos h2]
      · have e : wcl c = ((wcl c).1, false) := Prod.ext rfl (by simp [wcl, h2])
        rw [e, Quiver.SchreierGraph.evalWord_cons_false, if_neg h2]
    rw [hc, Equiv.Perm.mul_apply]

end CFSG.KS.ONNQ

end
