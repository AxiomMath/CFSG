module

public import CFSG.Certificates.Kernel.He7222.CovSound
public import CFSG.Certificates.Kernel.He7222.KeyGrp
public import CFSG.Certificates.Kernel.He7222.ChainPRep
import CFSG.Certificates.Kernel.OrbRow.LevelSound
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KS.PF CFSG.KC.OrbRow CFSG.Sporadic.Schreier

variable {n w : ℕ}

theorem stkRep_map {rec : ℕ → ℕ → Equiv.Perm (Fin n)} {Tl : ℕ → List ℕ} {f : ℕ → ℕ}
    {l : List ℕ} (h : ∀ i ∈ l, PRep n w ((Tl i).getD (f i) 0) (rec i (f i))) :
    StkRep n w (l.map fun i => (Tl i).getD (f i) 0) (l.map fun i => rec i (f i)) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, StkRep, List.forall₂_cons]
    exact ⟨h a List.mem_cons_self, ih fun i hi => h i (List.mem_cons_of_mem _ hi)⟩

theorem cover_key (hn : n < 16777216) (hw : n + 1 < 2 ^ w) (h5 : 5 ≤ n)
    {H P : Subgroup (Equiv.Perm (Fin n))} (hH : BaseFaithful H [0, 1, 2, 3, 4]) (hPH : P ≤ H)
    {τ : Equiv.Perm (Fin n)} {tauP : ℕ} (hτP : τ ∈ P) (hτ : PRep n w tauP τ)
    {L : ℕ} (hL : 0 < L) {Tl : ℕ → List ℕ} {b0 : ℕ} (hb0 : b0 < n)
    (hrep : ∀ i < L, ∀ j < (Tl i).length, PRep n w ((Tl i).getD j 0) (recP n w ((Tl i).getD j 0)))
    (hfix : ∀ i < L, 0 < i → ∀ j < (Tl i).length,
      recP n w ((Tl i).getD j 0) ⟨b0, hb0⟩ = ⟨b0, hb0⟩)
    (hfac : ∀ g ∈ P, ∃ f : ℕ → ℕ, (∀ i < L, f i < (Tl i).length) ∧
      g = ((List.range L).map fun i => recP n w ((Tl i).getD (f i) 0)).prod)
    {ncl : ℕ} {CK : List (List ℕ)} {Cc : List ℕ} {Cov : List (List ℕ)}
    (hCc : ∀ i < (Tl 0).length, getS Cc i < n)
    (hcov : ∀ i < (Tl 0).length, covK w (mask w) 5 ncl tauP CK b0 (Tl 0)
      ((List.range' 1 (L - 1)).map Tl).reverse Cc Cov i = true) :
    ∀ x ∈ P, x * x = 1 → x ≠ 1 → x ≠ τ → ∃ F : ℕ → ℕ, (∀ p : Fin n, (p : ℕ) < 5 → F p = x p) ∧
      ∃ cl < ncl, ∃ pos, keyF w F 5 = getS (getLs CK cl) pos := by
  intro x hx hx2 hx1 hxτ
  obtain ⟨f, hf, hxe⟩ := hfac x hx
  set rec : ℕ → ℕ → Equiv.Perm (Fin n) := fun i j => recP n w ((Tl i).getD j 0) with hrec
  have hL1 : L = (L - 1) + 1 := by omega
  have hrange : List.range L = 0 :: List.range' 1 (L - 1) := by
    rw [List.range_eq_range', hL1, List.range'_succ]
    simp
  set stk := (List.range' 1 (L - 1)).map fun i => (Tl i).getD (f i) 0 with hstk
  set gs := (List.range' 1 (L - 1)).map fun i => rec i (f i) with hgs
  have hmem' : ∀ i ∈ List.range' 1 (L - 1), i < L ∧ 0 < i := fun i hi => by
    have := List.mem_range'_1.mp hi
    omega
  have hst : StkRep n w stk gs := stkRep_map fun i hi => hrep i (hmem' i hi).1 (f i)
    (hf i (hmem' i hi).1)
  set t0 := (Tl 0).getD (f 0) 0 with ht0
  have ht0r : PRep n w t0 (rec 0 (f 0)) := hrep 0 hL (f 0) (hf 0 hL)
  have hys : StkRep n w (t0 :: stk) (rec 0 (f 0) :: gs) := by
    rw [StkRep, List.forall₂_cons]
    exact ⟨ht0r, hst⟩
  have hxprod : x = rec 0 (f 0) * gs.prod := by
    rw [hxe, hrange, List.map_cons, List.prod_cons]
  have hevx : ∀ p : Fin n, evK w (mask w) (t0 :: stk) p = x p := by
    intro p
    rw [evK_rep hys p, List.prod_cons, ← hxprod]
  have hufix : gs.prod ⟨b0, hb0⟩ = ⟨b0, hb0⟩ := by
    have : ∀ l : List ℕ, (∀ i ∈ l, i < L ∧ 0 < i) →
        ((l.map fun i => rec i (f i)).prod) ⟨b0, hb0⟩ = ⟨b0, hb0⟩ := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro hl
        rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
          ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
        exact hfix a (hl a List.mem_cons_self).1 (hl a List.mem_cons_self).2 (f a)
          (hf a (hl a List.mem_cons_self).1)
    exact this _ hmem'
  obtain ⟨hc, hleaf⟩ := covK_sound (hcov (f 0) (hf 0 hL))
  have hts : List.Forall₂ (· ∈ ·) stk.reverse ((List.range' 1 (L - 1)).map Tl).reverse := by
    rw [List.forall₂_reverse_iff, hstk, List.forall₂_map_left_iff, List.forall₂_map_right_iff,
      List.forall₂_same]
    intro i hi
    have hiL := (hmem' i hi).1
    rw [List.getD_eq_getElem _ _ (hf i hiL)]
    exact List.getElem_mem _
  have hL' := hleaf stk.reverse hts
  rw [List.reverse_reverse, foldl_eq_evK, List.reverse_reverse] at hL'
  set c := getS Cc (f 0) with hcdef
  have hcn : c < n := hCc (f 0) (hf 0 hL)
  rw [getS_eq] at hc hL'
  have hq : evK w (mask w) stk (pg w (mask w) t0 b0) = c := by
    have e1 : pg w (mask w) t0 b0 = rec 0 (f 0) ⟨b0, hb0⟩ := ht0r ⟨b0, hb0⟩
    have e2 : rec 0 (f 0) ⟨c, hcn⟩ = ⟨b0, hb0⟩ := Fin.ext (by rw [← ht0r ⟨c, hcn⟩]; exact hc)
    rw [e1, evK_rep hst]
    have hxx : x (x ⟨b0, hb0⟩) = ⟨b0, hb0⟩ := by
      rw [← Equiv.Perm.mul_apply, hx2]
      rfl
    have hxb : x ⟨b0, hb0⟩ = rec 0 (f 0) ⟨b0, hb0⟩ := by
      rw [hxprod, Equiv.Perm.mul_apply, hufix]
    have h3 : (rec 0 (f 0)) (gs.prod (rec 0 (f 0) ⟨b0, hb0⟩)) = (rec 0 (f 0)) ⟨c, hcn⟩ := by
      rw [e2]
      rw [hxb] at hxx
      rw [hxprod, Equiv.Perm.mul_apply] at hxx
      exact hxx
    exact congrArg Fin.val ((rec 0 (f 0)).injective h3)
  have hnw : n ≤ 2 ^ w := by omega
  have hinv : invP w (mask w) (t0 :: stk) 5 = true := by
    unfold invP
    refine CFSG.KS.PackFld.allN_of_forall fun k hk => ?_
    have hk' : k < n := by omega
    have e : evK w (mask w) (t0 :: stk) k = x ⟨k, hk'⟩ := hevx ⟨k, hk'⟩
    rw [e, hevx (x ⟨k, hk'⟩), ← Equiv.Perm.mul_apply, hx2]
    exact Nat.beq_refl k
  have hFx : ∀ p : Fin n, (p : ℕ) < 5 → evK w (mask w) (t0 :: stk) p = x p := fun p _ => hevx p
  have hkt : keyN w (mask w) (t0 :: stk) 5 ≠ keyN w (mask w) [tauP] 5 := by
    intro he
    have hτs : StkRep n w [tauP] [τ] := List.Forall₂.cons hτ List.Forall₂.nil
    exact hxτ (eq_of_keyF hH hnw (hPH hx) (hPH hτP) hFx
      (fun p _ => by rw [evK_rep hτs p]; simp) h5 he)
  have hk1 : keyN w (mask w) (t0 :: stk) 5 ≠ keyN w (mask w) [] 5 := by
    intro he
    exact hx1 (eq_of_keyF hH hnw (hPH hx) (hPH P.one_mem) hFx (fun p _ => rfl) h5 he)
  obtain ⟨r, -, hcl, hkey⟩ := hL' hq hinv hkt hk1
  exact ⟨_, hFx, _, hcl, _, hkey⟩

end CFSG.KC.HeChain

end
