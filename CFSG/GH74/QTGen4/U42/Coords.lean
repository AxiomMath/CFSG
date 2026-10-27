module

public import CFSG.Quasithin.H13.A5Setting

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5

abbrev Mc : Type := W5 ⋊[pact] Equiv.Perm (Fin 5)

def Mof (R : Subgroup (Equiv.Perm (Fin 5))) : Subgroup Mc where
  carrier := {x | x.right ∈ R}
  one_mem' := R.one_mem
  mul_mem' := fun ha hb => R.mul_mem ha hb
  inv_mem' := fun ha => R.inv_mem ha

theorem mem_Mof {R : Subgroup (Equiv.Perm (Fin 5))} {x : Mc} : x ∈ Mof R ↔ x.right ∈ R :=
  Iff.rfl

structure CoordData (M : Type*) [Group M] where
  V : Subgroup M
  hV : V.Normal
  ψ : ↥V ≃* W5
  ρ : M →* Equiv.Perm (Fin 5)
  ker_ρ : ρ.ker = V
  conj_ψ : ∀ (m : M) (v : ↥V), ψ ⟨m * v * m⁻¹, hV.conj_mem (v : M) v.2 m⟩ = pact (ρ m) (ψ v)

theorem W5_mul_self (w : W5) : w * w = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, Ev_add_self, toAdd_one]

namespace CoordData

variable {M : Type*} [Group M] (C : CoordData M)

theorem rho_eq_one_of_mem {v : M} (hv : v ∈ C.V) : C.ρ v = 1 := by
  have h : v ∈ C.ρ.ker := by rw [C.ker_ρ]; exact hv
  exact MonoidHom.mem_ker.mp h

theorem mem_of_rho_eq_one {g : M} (h : C.ρ g = 1) : g ∈ C.V := by
  rw [← C.ker_ρ]
  exact MonoidHom.mem_ker.mpr h

theorem isPGroup_V : IsPGroup 2 C.V := by
  intro g
  refine ⟨1, ?_⟩
  rw [Nat.pow_one]
  apply C.ψ.injective
  rw [map_pow, map_one, pow_two]
  exact W5_mul_self _

theorem pact_fix_iff (m : M) (v : ↥C.V) :
    pact (C.ρ m) (C.ψ v) = C.ψ v ↔ m * v * m⁻¹ = v := by
  constructor
  · intro h
    have h1 := C.conj_ψ m v
    rw [h] at h1
    have h2 : (⟨m * v * m⁻¹, C.hV.conj_mem (v : M) v.2 m⟩ : ↥C.V) = v := C.ψ.injective h1
    exact congrArg Subtype.val h2
  · intro h
    rw [← C.conj_ψ m v]
    congr 1
    exact Subtype.ext h

end CoordData

end CFSG.GH74.QTGen4.U42
