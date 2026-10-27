module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_fixed_in_coset {Y : Type*} [Group Y] [Finite Y] (Q : Subgroup Y) [Q.Normal]
    (hodd : Odd (Nat.card Q)) {z : Y} (hz2 : z * z = 1) {g : Y}
    (hg : z * g * z⁻¹ * g⁻¹ ∈ Q) : ∃ k ∈ Q, z * (g * k) = (g * k) * z := by
  classical
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  let S : Set Y := {x | g⁻¹ * x ∈ Q}
  have hmap : ∀ x ∈ S, z * x * z⁻¹ ∈ S := by
    intro x hx
    have hx' : g⁻¹ * x ∈ Q := hx
    show g⁻¹ * (z * x * z⁻¹) ∈ Q
    have h1 : z * (g⁻¹ * x) * z⁻¹ ∈ Q := Normal.conj_mem inferInstance _ hx' z
    have h2 : g⁻¹ * (z * g * z⁻¹ * g⁻¹) * g⁻¹⁻¹ ∈ Q := Normal.conj_mem inferInstance _ hg g⁻¹
    have e : g⁻¹ * (z * x * z⁻¹) =
        (g⁻¹ * (z * g * z⁻¹ * g⁻¹) * g⁻¹⁻¹) * (z * (g⁻¹ * x) * z⁻¹) := by group
    rw [e]
    exact mul_mem h2 h1
  let f : Function.End S := fun x => ⟨z * x * z⁻¹, hmap x x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show z * (z * (x : Y) * z⁻¹) * z⁻¹ = x
    calc z * (z * (x : Y) * z⁻¹) * z⁻¹ = (z * z) * x * (z⁻¹ * z⁻¹) := by group
      _ = x := by rw [hz2, hzi, hz2]; group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype S := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  have hcard : Fintype.card S = Nat.card Q := by
    rw [Fintype.card_eq_nat_card]
    exact Nat.card_congr
      { toFun := fun x => ⟨g⁻¹ * x, x.2⟩
        invFun := fun k => ⟨g * k, by show g⁻¹ * (g * (k : Y)) ∈ Q; simp⟩
        left_inv := fun x => by apply Subtype.ext; simp
        right_inv := fun k => by apply Subtype.ext; simp }
  have hne : Fintype.card f.fixedPoints ≠ 0 := by
    intro h0
    rw [hcard, h0] at hmod
    have := (Nat.modEq_zero_iff_dvd.1 hmod)
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  obtain ⟨⟨x, hxfix⟩⟩ := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hne)
  have hx : (f x : S) = x := hxfix
  have hxz : z * (x : Y) * z⁻¹ = x := congrArg Subtype.val hx
  refine ⟨g⁻¹ * x, x.2, ?_⟩
  have : g * (g⁻¹ * (x : Y)) = x := by group
  rw [this]
  calc z * (x : Y) = z * x * z⁻¹ * z := by group
    _ = x * z := by rw [hxz]

theorem exists_conj_of_perfect {T Ut : Type*} [Group T] [Group Ut] [Group.IsPerfect T]
    (hout : Group.IsSolvable (Outer Ut)) (α : T →* MulAut Ut) (t : T) :
    ∃ e : Ut, α t = MulAut.conj e := by
  have h1 : (QuotientGroup.mk' (inner Ut)).comp α = 1 :=
    CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one _
  have h2 : α t ∈ inner Ut := by
    have := DFunLike.congr_fun h1 t
    simpa using (QuotientGroup.eq_one_iff (α t)).1 this
  obtain ⟨e, he⟩ := h2
  exact ⟨e, he.symm⟩

@[expose] def conjAct {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : MulAut H where
  toFun h := ⟨g * h * g⁻¹, hg h h.2⟩
  invFun h := ⟨g⁻¹ * h * g, hg' h h.2⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem conjAct_apply {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (h : H) :
    ((conjAct H g hg hg' h : H) : G) = g * h * g⁻¹ := rfl

end CFSG.EvenSporadicStandard.M24Std
