module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable Subgroup

section Words

variable {m n : ℕ}

@[expose] def letterT (T Ti : Fin m → Table) : Fin m × Bool → Table
  | (i, true) => T i
  | (i, false) => Ti i

@[expose] def evalT (n : ℕ) (T Ti : Fin m → Table) (w : List (Fin m × Bool)) : Table :=
  w.foldr (fun l acc => compT n (letterT T Ti l) acc) (idT n)

theorem rep_evalT {H : Type*} [Group H] [MulAction H (Fin n)] (hn : n < 2 ^ 32) (g : Fin m → H)
    {T Ti : Fin m → Table} (hT : ∀ i, Rep n (T i) (g i)) (hTi : ∀ i, Rep n (Ti i) (g i)⁻¹)
    (w : List (Fin m × Bool)) : Rep n (evalT n T Ti w) (FreeGroup.lift g (FreeGroup.mk w)) := by
  induction w with
  | nil =>
    have := Rep.idT (G := H) hn
    simpa [evalT] using this
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have hl : Rep n (letterT T Ti (i, b)) (if b then g i else (g i)⁻¹) := by
      cases b
      · simpa [letterT] using hTi i
      · simpa [letterT] using hT i
    have h2 := Rep.compT hl ih
    have : FreeGroup.lift g (FreeGroup.mk ((i, b) :: w)) =
        (if b then g i else (g i)⁻¹) * FreeGroup.lift g (FreeGroup.mk w) := by
      rw [show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w from rfl,
        map_mul]
      congr 1
      cases b <;> simp
    rw [this]
    exact h2

@[expose] def wordsTrivial (n : ℕ) (T Ti : Fin m → Table) (ws : List (List (Fin m × Bool))) :
    Bool :=
  ws.all fun w => tblEq n (evalT n T Ti w) (idT n)

theorem lift_eq_one_of_wordsTrivial (hn : n < 2 ^ 32) (g : Fin m → Equiv.Perm (Fin n))
    {T Ti : Fin m → Table} (hT : ∀ i, Rep n (T i) (g i)) (hTi : ∀ i, Rep n (Ti i) (g i)⁻¹)
    {ws : List (List (Fin m × Bool))} (h : wordsTrivial n T Ti ws = true) :
    ∀ w ∈ ws, FreeGroup.lift g (FreeGroup.mk w) = 1 := by
  intro w hw
  have h1 := List.all_eq_true.1 h w hw
  exact (tblEq_iff_eq (rep_evalT hn g hT hTi w) (Rep.idT hn)).1 h1

section Substitution

variable {m k : ℕ}

@[expose] def invW {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  w.reverse.map fun l => (l.1, !l.2)

@[expose] def mkRel {m : ℕ} (lhs rhs : List (Fin m × Bool)) : List (Fin m × Bool) :=
  lhs ++ invW rhs

@[expose] def powW {m : ℕ} (w : List (Fin m × Bool)) (k : ℕ) : List (Fin m × Bool) :=
  (List.replicate k w).flatten

theorem lift_mk_invW {H : Type*} [Group H] (g : Fin m → H) (w : List (Fin m × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (invW w)) = (FreeGroup.lift g (FreeGroup.mk w))⁻¹ := by
  induction w with
  | nil => simp [invW]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have h1 : invW ((i, b) :: w) = invW w ++ [(i, !b)] := by simp [invW]
    rw [h1, show FreeGroup.mk (invW w ++ [(i, !b)]) =
        FreeGroup.mk (invW w) * FreeGroup.mk [(i, !b)] from rfl, map_mul, ih,
      show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w from rfl, map_mul,
      mul_inv_rev]
    congr 1
    cases b <;> simp

theorem lift_mk_powW {H : Type*} [Group H] (g : Fin m → H) (w : List (Fin m × Bool)) (j : ℕ) :
    FreeGroup.lift g (FreeGroup.mk (powW w j)) = (FreeGroup.lift g (FreeGroup.mk w)) ^ j := by
  induction j with
  | zero => simp [powW]
  | succ j ih =>
    have h1 : powW w (j + 1) = w ++ powW w j := by simp [powW, List.replicate_succ]
    rw [h1, show FreeGroup.mk (w ++ powW w j) = FreeGroup.mk w * FreeGroup.mk (powW w j) from rfl,
      map_mul, ih, pow_succ']

theorem lift_mk_append {H : Type*} [Group H] (g : Fin m → H) (w₁ w₂ : List (Fin m × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (w₁ ++ w₂)) =
      FreeGroup.lift g (FreeGroup.mk w₁) * FreeGroup.lift g (FreeGroup.mk w₂) := by
  rw [show FreeGroup.mk (w₁ ++ w₂) = FreeGroup.mk w₁ * FreeGroup.mk w₂ from rfl, map_mul]

theorem lift_mk_single {H : Type*} [Group H] (g : Fin m → H) (i : Fin m) :
    FreeGroup.lift g (FreeGroup.mk [(i, true)]) = g i := by
  show FreeGroup.lift g (FreeGroup.of i) = g i
  exact FreeGroup.lift_apply_of

theorem lift_mk_mkRel {H : Type*} [Group H] (g : Fin m → H) (lhs rhs : List (Fin m × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (mkRel lhs rhs)) =
      FreeGroup.lift g (FreeGroup.mk lhs) * (FreeGroup.lift g (FreeGroup.mk rhs))⁻¹ := by
  unfold mkRel
  rw [lift_mk_append, lift_mk_invW]

theorem lift_mkRel_eq_one {H : Type*} [Group H] (g : Fin m → H) {lhs rhs : List (Fin m × Bool)}
    (h : FreeGroup.lift g (FreeGroup.mk lhs) = FreeGroup.lift g (FreeGroup.mk rhs)) :
    FreeGroup.lift g (FreeGroup.mk (mkRel lhs rhs)) = 1 := by
  rw [lift_mk_mkRel, h, mul_inv_cancel]

theorem lift_mk_congr {H : Type*} [Group H] {g g' : Fin m → H} {r : List (Fin m × Bool)}
    (h : ∀ l ∈ r, g l.1 = g' l.1) :
    FreeGroup.lift g (FreeGroup.mk r) = FreeGroup.lift g' (FreeGroup.mk r) := by
  induction r with
  | nil => simp
  | cons l r ih =>
    rw [show FreeGroup.mk (l :: r) = FreeGroup.mk [l] * FreeGroup.mk r from rfl, map_mul, map_mul,
      ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))]
    congr 1
    obtain ⟨i, b⟩ := l
    have := h (i, b) List.mem_cons_self
    cases b <;> simp [this]

@[expose] def substW (W : Fin m → List (Fin k × Bool)) (w : List (Fin m × Bool)) :
    List (Fin k × Bool) :=
  w.flatMap fun l => if l.2 then W l.1 else invW (W l.1)

theorem substW_append (W : Fin m → List (Fin k × Bool)) (w₁ w₂ : List (Fin m × Bool)) :
    substW W (w₁ ++ w₂) = substW W w₁ ++ substW W w₂ := by
  simp [substW]

theorem lift_comp_substW {K H : Type*} [Group K] [Group H] (φ : K →* H)
    (W : Fin m → List (Fin k × Bool)) (f : Fin k → K) (r : List (Fin m × Bool)) :
    FreeGroup.lift (fun i => φ (FreeGroup.lift f (FreeGroup.mk (W i)))) (FreeGroup.mk r) =
      φ (FreeGroup.lift f (FreeGroup.mk (substW W r))) := by
  induction r with
  | nil => simp [substW]
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    have h1 : substW W ((i, b) :: r) =
        (if b then W i else invW (W i)) ++ substW W r := by
      simp [substW]
    rw [h1, show FreeGroup.mk ((i, b) :: r) = FreeGroup.mk [(i, b)] * FreeGroup.mk r from rfl,
      map_mul, ih,
      show FreeGroup.mk ((if b then W i else invW (W i)) ++ substW W r) =
        FreeGroup.mk (if b then W i else invW (W i)) * FreeGroup.mk (substW W r) from rfl,
      map_mul, map_mul]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [lift_mk_invW, map_inv]
      simp
    · simp

end Substitution

end Words


section PresModel

variable {m n : ℕ}

@[expose] noncomputable def presHom (ws : List (List (Fin m × Bool))) {H : Type*} [Group H]
    (g : Fin m → H) (hrel : ∀ r ∈ ws, FreeGroup.lift g (FreeGroup.mk r) = 1) : PG m ws →* H :=
  PresentedGroup.toGroup (f := g) (fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hrel w hw)

theorem presHom_mk (ws : List (List (Fin m × Bool))) {H : Type*} [Group H] (g : Fin m → H)
    (hrel : ∀ r ∈ ws, FreeGroup.lift g (FreeGroup.mk r) = 1) (w : List (Fin m × Bool)) :
    presHom ws g hrel (PresentedGroup.mk _ (FreeGroup.mk w)) = FreeGroup.lift g (FreeGroup.mk w) :=
  rfl

theorem range_presHom (ws : List (List (Fin m × Bool))) {H : Type*} [Group H] (g : Fin m → H)
    (hrel : ∀ r ∈ ws, FreeGroup.lift g (FreeGroup.mk r) = 1) :
    (presHom ws g hrel).range = closure (Set.range g) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2
  funext i
  exact PresentedGroup.toGroup.of _

theorem lift_eq_one_of_presModel (ws : List (List (Fin m × Bool))) (g : Fin m → Equiv.Perm (Fin n))
    (hrel : ∀ r ∈ ws, FreeGroup.lift g (FreeGroup.mk r) = 1) (hfin : Finite (PG m ws))
    (hle : Nat.card (PG m ws) ≤ Nat.card (closure (Set.range g)))
    {H : Type*} [Group H] (x : Fin m → H) (hx : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (w : List (Fin m × Bool)) (hw : FreeGroup.lift g (FreeGroup.mk w) = 1) :
    FreeGroup.lift x (FreeGroup.mk w) = 1 := by
  have hinj : Function.Injective (presHom ws g hrel) := by
    have hsurj : Function.Surjective (presHom ws g hrel).rangeRestrict :=
      (presHom ws g hrel).rangeRestrict_surjective
    have hcard : Nat.card (PG m ws) ≤ Nat.card (presHom ws g hrel).range := by
      rw [range_presHom]; exact hle
    have hb := hsurj.bijective_of_nat_card_le hcard
    intro a b hab
    apply hb.1
    exact Subtype.ext hab
  have h1 : presHom ws g hrel (PresentedGroup.mk _ (FreeGroup.mk w)) = 1 := by
    rw [presHom_mk]; exact hw
  have h2 : PresentedGroup.mk _ (FreeGroup.mk w) = (1 : PG m ws) := hinj (by rw [h1, map_one])
  have h3 := congrArg (presHom ws x hx) h2
  rw [presHom_mk, map_one] at h3
  exact h3

end PresModel

end CFSG.EvenSporadicStandard.M12Std.Yosh
