module

public import CFSG.Quasithin.Background.FixVLattice
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem commV_mono {A B : Subgroup (MulAut V)} (h : A ≤ B) : commV A ≤ commV B :=
  Subgroup.closure_mono fun _ ⟨x, hx, v, hxv⟩ => ⟨x, h hx, v, hxv⟩

theorem commV_invariant {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) {w : V}
    (hw : w ∈ commV X) : x w ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hw

theorem commV_sup_le (A B : Subgroup (MulAut V)) : commV (A ⊔ B) ≤ commV A ⊔ commV B :=
  CFSG.Quasithin.FixVLat.commV_sup_le A B

theorem eq_one_of_trivial_on_commV (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {x : MulAut V} (hx : x ∈ X) (hodd : Odd (orderOf x)) (htriv : ∀ w ∈ commV X, x w = w) :
    x = 1 := by
  have hsq : x ^ 2 = 1 := by
    ext v
    have hmem : x v * v⁻¹ ∈ commV X := Subgroup.subset_closure ⟨x, hx, v, rfl⟩
    have h := htriv _ hmem
    rw [map_mul, map_inv] at h
    have hvv : v * v = 1 := by rw [← pow_two]; exact hV v
    have hxx : x v * x v = 1 := by rw [← pow_two]; exact hV _
    have h2 : (x ^ 2) v = x (x v) := by simp [pow_two, MulAut.mul_apply]
    rw [h2]
    calc x (x v) = (x (x v) * (x v)⁻¹) * x v := (inv_mul_cancel_right _ _).symm
      _ = (x v * v⁻¹) * x v := by rw [h]
      _ = (x v * x v) * v⁻¹ := mul_right_comm _ _ _
      _ = v⁻¹ := by rw [hxx, one_mul]
      _ = v := inv_eq_of_mul_eq_one_right hvv
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

@[expose] def restrictAut (e : MulAut V) (H : Subgroup V) (h1 : ∀ h ∈ H, e h ∈ H)
    (h2 : ∀ h ∈ H, e⁻¹ h ∈ H) : MulAut ↥H where
  toFun h := ⟨e (h : V), h1 h h.2⟩
  invFun h := ⟨e⁻¹ (h : V), h2 h h.2⟩
  left_inv h := Subtype.ext (by simp [MulAut.inv_apply])
  right_inv h := Subtype.ext (by simp [MulAut.inv_apply])
  map_mul' a b := Subtype.ext (map_mul e (a : V) (b : V))

@[expose] noncomputable def resHom (X : Subgroup (MulAut V)) : X →* MulAut ↥(commV X) where
  toFun x := restrictAut x (commV X) (fun _ hh => commV_invariant x.2 hh)
    (fun _ hh => commV_invariant (X.inv_mem x.2) hh)
  map_one' := by
    ext h
    rfl
  map_mul' x y := by
    ext h
    rfl

theorem resHom_apply (X : Subgroup (MulAut V)) (x : X) (w : ↥(commV X)) :
    ((resHom X x w : ↥(commV X)) : V) = (x : MulAut V) (w : V) := rfl

theorem injective_resHom (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hodd : ∀ x ∈ X, Odd (orderOf x)) : Function.Injective (resHom X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have htriv : ∀ w ∈ commV X, (x : MulAut V) w = w := by
    intro w hw
    have := congrArg (fun φ : MulAut ↥(commV X) => ((φ ⟨w, hw⟩ : ↥(commV X)) : V)) hx
    simpa [resHom_apply] using this
  exact Subtype.ext (eq_one_of_trivial_on_commV hV x.2 (hodd x x.2) htriv)

variable [Finite V]

theorem card_le_nine_of_three_group {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W ≤ 16) {P : Subgroup (MulAut W)} (hP : IsPGroup 3 P) : Nat.card P ≤ 9 := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  have hdvd : Nat.card (MulAut W) ∣ 20160 := by
    rw [hGL, Matrix.card_GL_field]
    interval_cases n <;> simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
  have hP' : Nat.card P ∣ 20160 := (Subgroup.card_subgroup_dvd_card P).trans hdvd
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    have : k ≤ 2 := by omega
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h27 : 3 ^ 3 ∣ 3 ^ k := Nat.pow_dvd_pow 3 hk3
  rw [← hk] at h27
  have := h27.trans hP'
  omega

theorem commute_of_three_group (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hX : IsPGroup 3 X) (hcard : Nat.card (commV X) ≤ 16) : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  have hodd : ∀ x ∈ X, Odd (orderOf x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
    have h1 : (x : MulAut V) ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h1
    exact Odd.of_dvd_nat (Odd.pow (by decide)) h2
  have hinj := injective_resHom hV hodd
  have hW : ∀ w : ↥(commV X), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hrange : IsPGroup 3 (resHom X).range :=
    hX.of_surjective (resHom X).rangeRestrict (resHom X).rangeRestrict_surjective
  have h9 : Nat.card (resHom X).range ≤ 9 := card_le_nine_of_three_group hW hcard hrange
  have hXcard : Nat.card X = Nat.card (resHom X).range :=
    Nat.card_congr (Equiv.ofInjective _ hinj)
  have hX9 : Nat.card X ≤ 9 := hXcard ▸ h9
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcomm : ∀ a b : X, a * b = b * a := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    interval_cases k
    · intro a b
      have : Nat.card X = 1 := by simpa using hk
      have h1 : Subsingleton X := (Nat.card_eq_one_iff_unique.mp this).1
      exact Subsingleton.elim _ _
    · have hp : Nat.card X = 3 := by simpa using hk
      have : IsCyclic X := isCyclic_of_prime_card hp
      exact fun a b => (IsCyclic.commGroup (α := X)).mul_comm a b
    · have hp : Nat.card X = 3 ^ 2 := hk
      have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hp
      exact fun a b => this.is_comm.comm a b
  intro a ha b hb
  have := hcomm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

end CFSG.CGT.PushingUpLit.CGT6
