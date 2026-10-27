module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.A2ModCfgSL
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Timmesfeld.ARS.CaseOADegGraph

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YT

open Module Matrix CFSG.Timmesfeld.ARS CFSG.Blueprint A2Mod

section SL

variable {n : ℕ}

theorem exists_ne_of_two_le (hn : 2 ≤ n) (i : Fin n) : ∃ j : Fin n, j ≠ i := by
  by_cases h : i.val = 0
  · exact ⟨⟨1, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩
  · exact ⟨⟨0, by omega⟩, fun e => by simp [Fin.ext_iff] at e; omega⟩

theorem eq_zero_of_forall_mulVec_eq (hn : 2 ≤ n) {x : Fin n → ZMod 2}
    (hx : ∀ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x) :
    x = 0 := by
  by_contra hx0
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext h)
  obtain ⟨j, hj⟩ := exists_ne_of_two_le hn i
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hxi : x i = 1 := (h01 (x i)).resolve_left hi
  have hφv : (Pi.single i 1 : Fin n → ZMod 2) ⬝ᵥ Pi.single j 1 = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hj.symm]
  have h1 := hx (tv (Pi.single j 1) (Pi.single i 1))
  rw [tv_mulVec hφv, single_dotProduct, one_mul, hxi, one_smul, add_eq_left] at h1
  have := congrFun h1 j
  simp at this

theorem eq_zero_of_forall_contra_eq (hn : 2 ≤ n) {ψ : Fin n → ZMod 2}
    (hψ : ∀ g : SpecialLinearGroup (Fin n) (ZMod 2), contra g ψ = ψ) : ψ = 0 := by
  by_contra hψ0
  obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ0 (funext h)
  obtain ⟨j, hj⟩ := exists_ne_of_two_le hn i
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hψi : ψ i = 1 := (h01 (ψ i)).resolve_left hi
  have hφv : (Pi.single j 1 : Fin n → ZMod 2) ⬝ᵥ Pi.single i 1 = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hj]
  have h1 := hψ (tv (Pi.single i 1) (Pi.single j 1))
  rw [contra_tv hφv, dotProduct_single, mul_one, hψi, one_smul, sub_eq_self] at h1
  have := congrFun h1 j
  simp at this

end SL

section PointMaps

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ' : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}

theorem fix_eq_zero_of_isPointMaps (hn : 2 ≤ n) {P Pd : (Fin n → ZMod 2) →ₗ[ZMod 2] V}
    (h : IsPointMaps ρ' Q P Pd) {v : V} (hv : v ∈ commSpaceOf ρ' ⊤)
    (hfix : ∀ g, ρ' g v = v) : v = 0 := by
  rw [h.commSpaceOf_top] at hv
  obtain ⟨a, ⟨x, rfl⟩, b, ⟨φ, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
  have hsplit : ∀ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x ∧ contra g φ = φ := by
    intro g
    have e := hfix g
    rw [map_add, ← h.map_mulVec, ← h.map_contra] at e
    have e1 : P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x) = Pd (φ - contra g φ) := by
      rw [map_sub, map_sub]
      linear_combination (norm := abel_nf) e
    have hmem : P ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x - x) ∈
        LinearMap.range P ⊓ LinearMap.range Pd :=
      ⟨⟨_, rfl⟩, ⟨_, e1.symm⟩⟩
    rw [h.range_inf_range, Submodule.mem_bot] at hmem
    have hx := h.injective (hmem.trans (map_zero P).symm)
    have hφ : Pd (φ - contra g φ) = Pd 0 := by rw [← e1, hmem, map_zero]
    exact ⟨sub_eq_zero.mp hx, (sub_eq_zero.mp (h.injective_dual hφ)).symm⟩
  rw [eq_zero_of_forall_mulVec_eq hn fun g => (hsplit g).1,
    eq_zero_of_forall_contra_eq hn fun g => (hsplit g).2, map_zero, map_zero, add_zero]

end PointMaps

end CFSG.LargeExtraspecial.AS35YT
