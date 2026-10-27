module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathOddAbelian
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [CharP k 2] [Finite V]

theorem minimal_parabolic_odd_nilpotent_S3_wreath {H T M Fn E : Subgroup (V ≃ₗ[k] V)}
    (hFH : Fn ≤ H) (hFn : (Fn.subgroupOf H).Normal) [Group.IsNilpotent ↥Fn]
    (hFodd : Odd (Nat.card Fn))
    (hCF : H ⊓ Subgroup.centralizer (Fn : Set (V ≃ₗ[k] V)) ≤ Fn)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) : S3Wreath H T Fn := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have hO2 := pCore_trivial_of_centralizer_le hFH hFn hFodd hCF
  obtain ⟨A, hA⟩ := exists_minOffender hEH hEne hEel hEoff
  obtain ⟨hAH, hAne, hAel, hAoff, hAstrict⟩ := hA
  have hcomm := commutator_ne_bot_of_centralizer_le hAH hAne hAel hFodd hCF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨ι, hfin, g0, F0⟩, hall⟩ :=
    nilpotent_offender_natural_S3_factors hFH hFn hFodd hAH hAel hAne hAoff hAstrict hcomm
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hF : ConjFamily H Fn A (g0 ∘ e) := F0.reindex e
  have hnat : NaturalS3Factors H Fn A (g0 ∘ e) := (hall (g0 ∘ e) hF).toNatural
  exact s3Wreath_of_natural hnat hF hFH hFn hFodd hAne hAel hO2 hT hTn hTM hMH hmax

end CFSG.QuasithinUnique.Setup.Wreath
