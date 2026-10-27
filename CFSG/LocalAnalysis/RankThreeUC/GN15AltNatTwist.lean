module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

theorem altNat_perm_unique {n : ℕ} (hn : Odd n) {σ τ : Perm (Fin n)}
    (h : ∀ x : evenWeight n, evenWeightPerm σ x = evenWeightPerm τ x) : σ = τ := by
  have h1 : τ⁻¹ * σ = 1 := by
    refine eq_one_of_evenWeightPerm_eq_self hn fun x => ?_
    rw [altNat_evenWeightPerm_mul, h x, ← altNat_evenWeightPerm_mul, inv_mul_cancel,
      altNat_evenWeightPerm_one]
  exact (inv_mul_eq_one.1 h1).symm

section Twist

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} {M : Subgroup V} {n : ℕ}

@[expose] def altNatConjL (a : MulAut V) (ha : ∀ l ∈ L, a * l * a⁻¹ ∈ L ∧ a⁻¹ * l * a ∈ L) :
    ↥L ≃* ↥L where
  toFun l := ⟨a * l * a⁻¹, (ha l l.2).1⟩
  invFun l := ⟨a⁻¹ * l * a, (ha l l.2).2⟩
  left_inv l := Subtype.ext (by show a⁻¹ * (a * (l : MulAut V) * a⁻¹) * a = l; group)
  right_inv l := Subtype.ext (by show a * (a⁻¹ * (l : MulAut V) * a) * a⁻¹ = l; group)
  map_mul' x y := Subtype.ext (by
    show a * ((x : MulAut V) * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹); group)

theorem exists_altNatTwist (D : AltNatModule L M n) (hodd : Odd n) (h7 : 7 ≤ n)
    (hαinj : Function.Injective D.α) {a : MulAut V}
    (ha : ∀ l ∈ L, a * l * a⁻¹ ∈ L ∧ a⁻¹ * l * a ∈ L)
    (hM : ∀ m ∈ M, a m ∈ M) :
    ∃ σ : Perm (Fin n),
      (∀ m : ↥M, Multiplicative.toAdd (D.e ⟨a (m : V), hM m m.2⟩) =
        evenWeightPerm σ (Multiplicative.toAdd (D.e m))) ∧
      ∀ l : ↥L, (D.α ⟨a * l * a⁻¹, (ha l l.2).1⟩ : Perm (Fin n)) =
        σ * (D.α l : Perm (Fin n)) * σ⁻¹ := by
  let actM : ↥M → ↥M := fun m => ⟨a (m : V), hM m m.2⟩
  have hactM : Function.Injective actM := fun m m' h =>
    Subtype.ext (a.injective (congrArg Subtype.val h))
  let θ : evenWeight n →+ evenWeight n :=
    { toFun := fun x => Multiplicative.toAdd (D.e (actM (D.e.symm (Multiplicative.ofAdd x))))
      map_zero' := by
        show Multiplicative.toAdd (D.e (actM (D.e.symm 1))) = 0
        have : actM (D.e.symm 1) = 1 := Subtype.ext (by simp [actM])
        rw [this, map_one]; rfl
      map_add' := fun x y => by
        show Multiplicative.toAdd (D.e (actM (D.e.symm (Multiplicative.ofAdd (x + y))))) = _
        have : actM (D.e.symm (Multiplicative.ofAdd (x + y))) =
            actM (D.e.symm (Multiplicative.ofAdd x)) * actM (D.e.symm (Multiplicative.ofAdd y)) :=
          Subtype.ext (by simp [actM])
        rw [this, map_mul, toAdd_mul] }
  have hθ : ∀ m : ↥M, θ (Multiplicative.toAdd (D.e m)) = Multiplicative.toAdd (D.e (actM m)) := by
    intro m
    show Multiplicative.toAdd (D.e (actM (D.e.symm (Multiplicative.ofAdd
      (Multiplicative.toAdd (D.e m)))))) = _
    simp
  have hθinj : Function.Injective θ := by
    intro x y hxy
    obtain ⟨m, hm⟩ := D.e.surjective (Multiplicative.ofAdd x)
    obtain ⟨m', hm'⟩ := D.e.surjective (Multiplicative.ofAdd y)
    have hx : x = Multiplicative.toAdd (D.e m) := by rw [hm]; rfl
    have hy : y = Multiplicative.toAdd (D.e m') := by rw [hm']; rfl
    subst hx hy
    have h1 : θ (Multiplicative.toAdd (D.e m)) = θ (Multiplicative.toAdd (D.e m')) := hxy
    rw [hθ, hθ] at h1
    have h2 : actM m = actM m' := D.e.injective (Multiplicative.toAdd.injective h1)
    have h3 : m = m' := hactM h2
    rw [h3]
  let αe : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective D.α ⟨hαinj, D.surj⟩
  let c : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
    αe.symm.trans ((altNatConjL a ha).trans αe)
  have hc : ∀ (g : alternatingGroup (Fin n)) (v : evenWeight n),
      θ (evenWeightPerm (g : Perm (Fin n)) v) = evenWeightPerm (c g : Perm (Fin n)) (θ v) := by
    intro g v
    obtain ⟨m, hm⟩ := D.e.surjective (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (D.e m) := by rw [hm]; rfl
    subst hv
    set l : ↥L := αe.symm g with hl
    have hαl : (D.α l : Perm (Fin n)) = (g : Perm (Fin n)) := by
      have : αe l = g := by rw [hl]; exact αe.apply_symm_apply g
      exact congrArg Subtype.val this
    have h1 : evenWeightPerm (g : Perm (Fin n)) (Multiplicative.toAdd (D.e m)) =
        Multiplicative.toAdd (D.e (D.act l m)) := by rw [D.e_act, hαl]
    have h2 : actM (D.act l m) = D.act (altNatConjL a ha l) (actM m) := by
      apply Subtype.ext
      show a ((l : MulAut V) (m : V)) = (a * (l : MulAut V) * a⁻¹) (a (m : V))
      simp [MulAut.mul_apply]
    have h3 : θ (Multiplicative.toAdd (D.e (D.act l m))) =
        evenWeightPerm (D.α (altNatConjL a ha l) : Perm (Fin n)) (θ (Multiplicative.toAdd (D.e m))) := by
      rw [hθ, hθ, h2, D.e_act]
    have h4 : (D.α (altNatConjL a ha l) : Perm (Fin n)) = (c g : Perm (Fin n)) := by
      have : αe (altNatConjL a ha l) = c g := by
        show αe (altNatConjL a ha (αe.symm g)) = αe (altNatConjL a ha (αe.symm g))
        rfl
      exact congrArg Subtype.val this
    rw [h1, h3, h4]
  obtain ⟨σ, hσθ, hσc⟩ := altNat_eq_perm_of_twisted hodd h7 hθinj c hc
  refine ⟨σ, fun m => ?_, fun l => ?_⟩
  · have := hσθ (Multiplicative.toAdd (D.e m))
    rw [hθ] at this
    exact this
  · have h1 := hσc (αe l)
    have h2 : (c (αe l) : Perm (Fin n)) = (D.α (altNatConjL a ha l) : Perm (Fin n)) := by
      have : c (αe l) = αe (altNatConjL a ha l) := by
        show αe (altNatConjL a ha (αe.symm (αe l))) = αe (altNatConjL a ha l)
        rw [MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this
    rw [h2] at h1
    exact h1

end Twist

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
