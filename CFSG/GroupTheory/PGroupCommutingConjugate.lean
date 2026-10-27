module

public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace CFSG

open MulAction

theorem exists_commuting_conjugate_of_noncentral {P : Type*} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) (hP : IsPGroup p P) {x : P} (hx : x ∉ Subgroup.center P) :
    ∃ g : P, g * x * g⁻¹ ≠ x ∧ (g * x * g⁻¹) * x = x * (g * x * g⁻¹) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let C : Subgroup P := Subgroup.centralizer ({x} : Set P)
  let X : Type u_1 := ↥(MulAction.orbit (ConjAct P) x)
  haveI : Finite X := by
    dsimp [X]
    infer_instance
  haveI : Nonempty X := ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  haveI : MulAction (ConjAct P) X := by
    dsimp [X]
    infer_instance
  haveI : Fintype X := Fintype.ofFinite X
  letI : MulAction C X :=
    { smul := fun c y =>
      ⟨(c : P) * (y : P) * (c : P)⁻¹, by
        have h := MulAction.mem_orbit_of_mem_orbit (ConjAct.toConjAct (c : P)) y.property
        simpa [ConjAct.toConjAct_smul] using h⟩
      one_smul := fun y => by
        apply Subtype.ext
        change (1 : P) * (y : P) * (1 : P)⁻¹ = (y : P)
        simp
      mul_smul := fun a b y => by
        apply Subtype.ext
        change ((a : P) * (b : P)) * (y : P) * ((a : P) * (b : P))⁻¹ =
          (a : P) * ((b : P) * (y : P) * (b : P)⁻¹) * (a : P)⁻¹
        group }
  have hsmul : ∀ (c : C) (y : X), ((c • y : X) : P) = (c : P) * (y : P) * (c : P)⁻¹ :=
    fun _ _ => rfl
  have hXgt1 : 1 < Nat.card X := by
    by_contra hle
    have hpos : 0 < Nat.card X := Nat.card_pos
    have hcard1 : Nat.card X = 1 := by omega
    have hxfix : x ∈ MulAction.fixedPoints (ConjAct P) P := by
      rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
      rw [← Nat.card_eq_fintype_card]
      simpa [X] using hcard1
    rw [ConjAct.fixedPoints_eq_center] at hxfix
    exact hx hxfix
  obtain ⟨n, hn⟩ := (hP.of_equiv ConjAct.toConjAct).card_orbit (a := x)
  have hnX : Nat.card X = p ^ n := by simpa [X] using hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hnX
    omega
  have hdvdX : p ∣ Nat.card X := by
    rw [hnX]
    exact dvd_pow_self p hn0
  have hC : IsPGroup p C := hP.to_subgroup C
  let xX : X := ⟨x, MulAction.mem_orbit_self x⟩
  have hxmemC : x ∈ C := by
    change x ∈ Subgroup.centralizer ({x} : Set P)
    rw [Subgroup.mem_centralizer_singleton_iff]
  let xC : C := ⟨x, hxmemC⟩
  have hxfix : xX ∈ MulAction.fixedPoints C X := by
    intro c
    apply Subtype.ext
    rw [hsmul c xX]
    change (c : P) * x * (c : P)⁻¹ = x
    have hc : (c : P) * x = x * (c : P) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.property
    rw [hc]
    simp
  obtain ⟨yX, hyXfix, hxy⟩ :=
    hC.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := X) hdvdX hxfix
  have hyOrbit : (yX : P) ∈ MulAction.orbit (ConjAct P) x := yX.property
  rw [MulAction.mem_orbit_iff] at hyOrbit
  obtain ⟨g, hg⟩ := hyOrbit
  let gP : P := ConjAct.ofConjAct g
  have hg' : gP * x * gP⁻¹ = (yX : P) := by
    rw [ConjAct.smul_def] at hg
    exact hg
  have hyne : gP * x * gP⁻¹ ≠ x := by
    intro heq
    apply hxy
    apply Subtype.ext
    rw [← hg', heq]
  have hxyfix : x * (yX : P) * x⁻¹ = (yX : P) := by
    have h := congrArg Subtype.val (hyXfix xC)
    rw [hsmul xC yX] at h
    simpa [xC] using h
  have hcomm : (yX : P) * x = x * (yX : P) := by
    calc (yX : P) * x = (x * (yX : P) * x⁻¹) * x := by rw [hxyfix]
      _ = x * (yX : P) := by group
  refine ⟨gP, hyne, ?_⟩
  rw [hg']
  exact hcomm

end CFSG
