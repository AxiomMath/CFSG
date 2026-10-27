module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKInfl
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNGlue

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Mix11cN Mix11cK CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.IVK

namespace Mix11cK

theorem two_ne_zero_of_charP {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F p] :
    (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')

theorem negOne_ne_one {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP F p] :
    T2.negOne F ≠ 1 := by
  intro h
  have h2 : ((T2.negOne F : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((1 : SLm F) : Matrix (Fin 2) (Fin 2) F) 0 0 := by rw [h]
  simp at h2
  apply two_ne_zero_of_charP hp hp2 (F := F)
  linear_combination (-1 : F) * h2

@[expose] noncomputable def slToL2 (F : Type) [Field F] : SLm F →* L2 F :=
  (L2.mk F).comp (specialLinearGroupEquivStatedSL 2 F).toMonoidHom

theorem slToL2_surjective (F : Type) [Field F] : Function.Surjective (slToL2 F) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g, rfl⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective y
  exact ⟨g, rfl⟩

theorem slToL2_eq_one_iff (F : Type) [Field F] (g : SLm F) :
    slToL2 F g = 1 ↔ ∃ c : Fˣ, (Matrix.scalar (Fin 2) (c : F) : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) := by
  show (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 F g) : L2 F) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← Matrix.GeneralLinearGroup.coe_scalar, hc]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨c, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, hc]
    rfl

theorem slToL2_negOne (F : Type) [Field F] : slToL2 F (T2.negOne F) = 1 := by
  rw [slToL2_eq_one_iff]
  refine ⟨-1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem slToL2_unipotent_ne_one (F : Type) [Field F] :
    slToL2 F (CFSG.GH74.GLS.Stage4.Hex.sl2U (1 : F)) ≠ 1 := by
  rw [Ne, slToL2_eq_one_iff]
  rintro ⟨c, hc⟩
  have h := congrFun (congrFun hc 0) 1
  simp at h


end Mix11cK

end CFSG.GH74.GLS.Stage4.Rest
