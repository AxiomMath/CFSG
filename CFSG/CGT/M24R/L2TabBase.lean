
module

public import CFSG.CGT.M24R.L2InputsD
public import CFSG.CGT.M24R.Interfaces
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

@[expose] public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

abbrev N8 : Type := PG 10 relsN8Ten

@[expose] def n8 (w : List (Fin 10 × Bool)) : N8 := PresentedGroup.mk _ (FreeGroup.mk w)

theorem n8_nil : n8 [] = 1 := map_one _

theorem n8_append (w w' : List (Fin 10 × Bool)) : n8 (w ++ w') = n8 w * n8 w' := by
  rw [n8, n8, n8, ← map_mul, FreeGroup.mul_mk]

theorem gInvVec_gVec : ∀ j p, gInvVec j (gVec j p) = p := by decide

theorem gVec_gInvVec : ∀ j p, gVec j (gInvVec j p) = p := by decide

@[expose] def gPerm (j : Fin 10) : Equiv.Perm (Fin 16) :=
  ⟨gVec j, gInvVec j, gInvVec_gVec j, gVec_gInvVec j⟩

@[expose] def letPerm (l : Fin 10 × Bool) : Equiv.Perm (Fin 16) :=
  if l.2 then gPerm l.1 else (gPerm l.1)⁻¹

theorem idx16 (σ : Equiv.Perm (Fin 16)) {i : ℕ} (hi : i < 16) :
    idx 16 σ i = (σ ⟨i, hi⟩).val := by
  rw [idx_of_lt σ hi]
  rfl

theorem rep_gT (j : Fin 10) : Rep 16 (gT j) (gPerm j) := by
  intro i hi
  rw [idx16 _ hi]
  unfold gT
  rw [ap_ofFn _ hi, UInt32.toNat_ofNat', Nat.mod_eq_of_lt ((gVec j _).isLt.trans (by norm_num))]
  rfl

theorem rep_gTi (j : Fin 10) : Rep 16 (gTi j) (gPerm j)⁻¹ := by
  intro i hi
  rw [idx16 _ hi]
  unfold gTi
  rw [ap_ofFn _ hi, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt ((gInvVec j _).isLt.trans (by norm_num))]
  rfl

theorem rep_letTab (l : Fin 10 × Bool) : Rep 16 (letTab l) (letPerm l) := by
  obtain ⟨j, b⟩ := l
  have h1 : gTc[j.val]! = gT j := by
    unfold gTc
    rw [getElem!_pos _ j.val (by simp), Array.getElem_ofFn]
  have h2 : gTic[j.val]! = gTi j := by
    unfold gTic
    rw [getElem!_pos _ j.val (by simp), Array.getElem_ofFn]
  cases b
  · simp only [letTab, letPerm, Bool.false_eq_true, ↓reduceIte, h2]
    exact rep_gTi j
  · simp only [letTab, letPerm, ↓reduceIte, h1]
    exact rep_gT j

theorem lift_gPerm_cons (l : Fin 10 × Bool) (w : List (Fin 10 × Bool)) :
    FreeGroup.lift gPerm (FreeGroup.mk (l :: w)) =
      letPerm l * FreeGroup.lift gPerm (FreeGroup.mk w) := by
  rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
  obtain ⟨i, b⟩ := l
  cases b
  · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
      FreeGroup.lift_apply_of]
    rfl
  · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
    rfl

theorem rep_foldl (w : List (Fin 10 × Bool)) :
    ∀ (X : Table) (σ : Equiv.Perm (Fin 16)), Rep 16 X σ →
      Rep 16 (w.foldl (fun X l => compT 16 X (letTab l)) X)
        (σ * FreeGroup.lift gPerm (FreeGroup.mk w)) := by
  induction w with
  | nil =>
    intro X σ h
    simpa using h
  | cons l w ih =>
    intro X σ h
    rw [List.foldl_cons, lift_gPerm_cons, ← mul_assoc]
    exact ih _ _ (Rep.compT h (rep_letTab l))

theorem rep_wTab (w : List (Fin 10 × Bool)) :
    Rep 16 (wTab w) (FreeGroup.lift gPerm (FreeGroup.mk w)) := by
  have := rep_foldl w (idT 16) 1 (Rep.idT (by norm_num))
  rwa [one_mul] at this

theorem perm_eq_of_rep {X : Table} {σ τ : Equiv.Perm (Fin 16)} (hσ : Rep 16 X σ)
    (hτ : Rep 16 X τ) : σ = τ := by
  refine Equiv.ext fun p => Fin.ext ?_
  have h1 := hσ p.val p.isLt
  have h2 := hτ p.val p.isLt
  rw [idx16 _ p.isLt] at h1 h2
  exact h1.symm.trans h2

theorem lift_gPerm_eq_one (h : relCheck = true) :
    ∀ r ∈ {r : FreeGroup (Fin 10) | r ∈ relsN8Ten.map FreeGroup.mk},
      FreeGroup.lift gPerm r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  have h3 : wTab w = idT 16 := by
    simp only [relCheck, List.all_eq_true, beq_iff_eq] at h
    exact h w hw
  have hr := rep_wTab w
  rw [h3] at hr
  exact perm_eq_of_rep hr (Rep.idT (by norm_num))

theorem compT_size (X Y : Table) : (compT 16 X Y).size = 16 := Array.size_ofFn

theorem idT_size : (idT 16).size = 16 := Array.size_ofFn

theorem wTab_size (w : List (Fin 10 × Bool)) : (wTab w).size = 16 := by
  have key : ∀ (w : List (Fin 10 × Bool)) (X : Table), X.size = 16 →
      (w.foldl (fun X l => compT 16 X (letTab l)) X).size = 16 := by
    intro w
    induction w with
    | nil => intro X h; exact h
    | cons l w ih => intro X _; exact ih _ (compT_size _ _)
  exact key w _ idT_size

theorem table_eq_of_rep {X Y : Table} {σ : Equiv.Perm (Fin 16)} (hX : Rep 16 X σ)
    (hY : Rep 16 Y σ) (hXs : X.size = 16) (hYs : Y.size = 16) : X = Y := by
  refine Array.ext (by rw [hXs, hYs]) fun i hi1 hi2 => ?_
  have hi : i < 16 := by rwa [hXs] at hi1
  have := (hX i hi).trans (hY i hi).symm
  unfold ap at this
  rw [getElem!_pos X i hi1, getElem!_pos Y i hi2] at this
  exact UInt32.toNat_inj.1 this

end CFSG.CGT.M24R
