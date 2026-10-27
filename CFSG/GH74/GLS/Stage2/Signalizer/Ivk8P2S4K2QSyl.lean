module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2QGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2L31
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SimpleGroupReductions

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {J : Type} [Group J] [Finite J]

theorem exists_sylow_dihedral (hq : IsQuasisimple J) (hev : 2 ∣ Nat.card J) (T : Sylow 2 J)
    {D : Type} [Group D] (A : Subgroup D) (hA : A.index = 2) [IsCyclic A]
    (hinv : ∀ σ ∉ A, ∀ x ∈ A, σ * x * σ⁻¹ = x⁻¹) (ι : ↥(T : Subgroup J) →* D)
    (hι : Function.Injective ι)
    (hsq : ∀ u : ↥(T : Subgroup J), ι u ∉ A → (u : J) ^ 2 ∈ Subgroup.center J) :
    ∃ P : Sylow 2 (J ⧸ Subgroup.center J), ∃ n : ℕ,
      Nonempty (↥(P : Subgroup (J ⧸ Subgroup.center J)) ≃* DihedralGroup n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hq.2.1
  have hnonab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    exact ⟨a, b, hab⟩
  have hevY : Even (Nat.card (J ⧸ Subgroup.center J)) := by
    by_contra hodd
    have hsol : Group.IsSolvable (J ⧸ Subgroup.center J) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)
  have hTnc : ¬ IsCyclic ↥(T : Subgroup J) := perfect_sylow_two_not_cyclic hq.1 hev T
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ↥(T : Subgroup J), ι u₀ ∉ A := by
    by_contra h
    push Not at h
    apply hTnc
    exact isCyclic_of_injective (ι.codRestrict A h)
      (fun x y hxy => hι (congrArg Subtype.val hxy))
  obtain ⟨ρ, σ, hgen, hσA, hrel⟩ := exists_dihedral_pair ι hι A hA hinv hu₀
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let P : Sylow 2 (J ⧸ Subgroup.center J) := T.mapSurjective hπ
  have hPcoe : (P : Subgroup (J ⧸ Subgroup.center J)) = (T : Subgroup J).map π := rfl
  have hmem : ∀ t : ↥(T : Subgroup J), π t ∈ (P : Subgroup (J ⧸ Subgroup.center J)) := fun t =>
    ⟨t, t.2, rfl⟩
  let φ : ↥(T : Subgroup J) →* ↥(P : Subgroup (J ⧸ Subgroup.center J)) :=
    (π.comp (T : Subgroup J).subtype).codRestrict _ hmem
  have hφ : Function.Surjective φ := by
    rintro ⟨y, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hgen' : (⊤ : Subgroup ↥(P : Subgroup (J ⧸ Subgroup.center J))) =
      Subgroup.zpowers (φ ρ) ⊔ Subgroup.zpowers (φ σ) := by
    have h1 := congrArg (Subgroup.map φ) hgen
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective φ hφ] at h1
    exact h1.symm
  have hσ2 : φ σ ^ 2 = 1 := by
    rw [← map_pow]
    apply Subtype.ext
    show π ((σ : J) ^ 2) = 1
    rw [map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq σ hσA)
  have hrel' : φ σ * φ ρ * (φ σ)⁻¹ = (φ ρ)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hrel, map_inv]
  rcases CFSG.GorensteinWalter.isCyclic_or_dihedral_of_generators (φ ρ) (φ σ) hgen' hσ2 hrel'
    with hc | ⟨⟨e⟩⟩
  · exact absurd hc (CFSG.DisconnectedInvolutionGraph.Helpers.simple_even_sylow_two_not_cyclic
      hnonab hevY P)
  · exact ⟨P, _, ⟨e⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
