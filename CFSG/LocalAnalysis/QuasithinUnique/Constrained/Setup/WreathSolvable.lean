module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathOddNilpotent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathFitting

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped commutatorElement

theorem odd_card_fittingSubgroup {Hg : Type*} [Group Hg] [Finite Hg] (h : CFSG.pCore 2 Hg = ⊥) :
    Odd (Nat.card (CFSG.fittingSubgroup Hg)) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (CFSG.fittingSubgroup Hg) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥(CFSG.fittingSubgroup Hg) := default
  have hle := Sylow.map_le_pCore (CFSG.fittingSubgroup_normal (G := Hg))
    (CFSG.fittingSubgroup_nilpotent (G := Hg)) 2 P
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hle
  have hcard := Sylow.card_eq_multiplicity P
  have hP1 : Nat.card ↥(P : Subgroup ↥(CFSG.fittingSubgroup Hg)) = 1 := by
    rw [hle]
    exact Subgroup.card_bot
  have hF0 : Nat.card (CFSG.fittingSubgroup Hg) ≠ 0 := Nat.card_pos.ne'
  have h3 : 1 ≤ (Nat.card (CFSG.fittingSubgroup Hg)).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hF0).1 h2
  have h4 : 2 ^ 1 ≤ 2 ^ (Nat.card (CFSG.fittingSubgroup Hg)).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) h3
  have : Nat.card ↥(P : Subgroup ↥(CFSG.fittingSubgroup Hg)) = 2 ^ (Nat.card (CFSG.fittingSubgroup Hg)).factorization 2 := hcard
  omega

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V] [CharP k 2] [Finite V]

theorem solvable_minimal_parabolic_S3_wreath {H T M E : Subgroup (V ≃ₗ[k] V)}
    (hsolv : Group.IsSolvable ↥H)
    (hO2 : ∀ N' : Subgroup (V ≃ₗ[k] V), N' ≤ H → (N'.subgroupOf H).Normal → IsPGroup 2 N' →
      N' = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 ↥E)
    (hEoff : Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[k] V)) E) :
    S3Wreath H T ((CFSG.fittingSubgroup ↥H).map H.subtype) := by
  classical
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  have : Finite ↥H := Finite.of_injective H.subtype H.subtype_injective
  have hpc : CFSG.pCore 2 ↥H = ⊥ := (abstract_setting hO2 hT hTM hMH hmax).2.2.2.2
  set F : Subgroup (V ≃ₗ[k] V) := (CFSG.fittingSubgroup ↥H).map H.subtype with hF
  have hFH : F ≤ H := Subgroup.map_subtype_le _
  have hFsub : F.subgroupOf H = CFSG.fittingSubgroup ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hFn : (F.subgroupOf H).Normal := by
    rw [hFsub]
    exact CFSG.fittingSubgroup_normal
  let eF : ↥(CFSG.fittingSubgroup ↥H) ≃* ↥F :=
    (CFSG.fittingSubgroup ↥H).equivMapOfInjective H.subtype H.subtype_injective
  have : Group.IsNilpotent ↥F := Group.nilpotent_of_mulEquiv eF
  have hFodd : Odd (Nat.card F) := by
    rw [← Nat.card_congr eF.toEquiv]
    exact odd_card_fittingSubgroup hpc
  have hCF : H ⊓ Subgroup.centralizer (F : Set (V ≃ₗ[k] V)) ≤ F := by
    rintro x ⟨hxH, hxC⟩
    have h1 : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.centralizer
        ((CFSG.fittingSubgroup ↥H : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (y : V ≃ₗ[k] V) ∈ F := ⟨y, hy, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hxC _ hy'
      exact Subtype.ext (by simpa using this)
    have h2 := solvable_fitting_self_centralizing hsolv h1
    exact ⟨⟨x, hxH⟩, h2, rfl⟩
  exact minimal_parabolic_odd_nilpotent_S3_wreath hFH hFn hFodd hCF hT hTn hTM hMH hmax hEH hEne hEel
    hEoff

end CFSG.QuasithinUnique.Setup.Wreath
