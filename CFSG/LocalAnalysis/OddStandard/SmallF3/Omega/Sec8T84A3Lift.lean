module

public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

theorem exists_lift_equiv {M P Q : Type*} [Group M] [Group P] [Group Q] (f : M →* P) (g : M →* Q)
    (hfg : ∀ m : M, f m = 1 → g m = 1) (hgf : ∀ m : M, g m = 1 → f m = 1) (H : Subgroup P)
    (hH : H ≤ f.range) :
    ∃ H' : Subgroup Q, Nonempty (↥H' ≃* ↥H) ∧ ∀ m : M, f m ∈ H → g m ∈ H' := by
  classical
  let C : Subgroup M := H.comap f
  have hC : ∀ m : M, m ∈ C ↔ f m ∈ H := fun m => Subgroup.mem_comap
  let φ1 : ↥C →* ↥H := (f.comp C.subtype).codRestrict H fun m => (hC m).mp m.2
  let φ2 : ↥C →* ↥(C.map g) :=
    (g.comp C.subtype).codRestrict (C.map g) fun m => Subgroup.mem_map_of_mem g m.2
  have hφ1_val : ∀ x : ↥C, ((φ1 x : ↥H) : P) = f x.1 := fun x => rfl
  have hφ2_val : ∀ x : ↥C, ((φ2 x : ↥(C.map g)) : Q) = g x.1 := fun x => rfl
  have hφ1 : Function.Surjective φ1 := by
    rintro ⟨h, hh⟩
    obtain ⟨m, hm⟩ := hH hh
    refine ⟨⟨m, (hC m).mpr (by rw [hm]; exact hh)⟩, ?_⟩
    exact Subtype.ext (by rw [hφ1_val]; exact hm)
  have hφ2 : Function.Surjective φ2 := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hmC, hmy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨m, hmC⟩, Subtype.ext (by rw [hφ2_val]; exact hmy)⟩
  have hker : φ2.ker = φ1.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have hgx : g x.1 = 1 := by
        have h := congrArg Subtype.val hx
        rw [hφ2_val x] at h
        simpa using h
      exact Subtype.ext (by rw [hφ1_val]; exact hgf x.1 hgx)
    · intro hx
      have hfx : f x.1 = 1 := by
        have h := congrArg Subtype.val hx
        rw [hφ1_val x] at h
        simpa using h
      exact Subtype.ext (by rw [hφ2_val]; exact hfg x.1 hfx)
  refine ⟨C.map g, ⟨(QuotientGroup.quotientKerEquivOfSurjective φ2 hφ2).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ1 hφ1))⟩, ?_⟩
  intro m hm
  exact Subgroup.mem_map_of_mem g ((hC m).mpr hm)

end A3

end CFSG.OddStandard.SmallF3.Omega
