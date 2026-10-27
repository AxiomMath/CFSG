module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem fa8fin_type4 (hL : IsOm6Z2 L) {φ : ↥L →* omegaGroup hQ} (hφ : IsCoverMap L φ)
    (hcov : OddCentralCover φ) {z : G} (hI4 : IsI4PlusIn L z) (hzL : z ∈ L) :
    sec5cdPhi φ ⟨z, hzL⟩ * sec5cdPhi φ ⟨z, hzL⟩ = 1 ∧
      Module.finrank (ZMod 3) (commSp (sec5cdPhi φ ⟨z, hzL⟩)) = 4 ∧
      Module.finrank (ZMod 3) (fixSp (sec5cdPhi φ ⟨z, hzL⟩)) = 2 ∧
      quadSign (Q.restrict (fixSp (sec5cdPhi φ ⟨z, hzL⟩))) = -1 := by
  have hz2 : orderOf z = 2 := hI4.1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hφzz : φ zL * φ zL = 1 := by
    rw [← map_mul, show zL * zL = 1 from Subtype.ext hzz, map_one]
  have hφz1 : φ zL ≠ 1 := by
    intro h
    have hzL2 : zL ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      exact Subtype.ext hzz
    have h1 : zL = 1 :=
      fa8fin_cover_inj (k := 1) hcov hzL2 (one_pow _) (h.trans (map_one φ).symm)
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz2
    omega
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hztt : ((φ zL : omegaGroup hQ) : OGroup Q) * ((φ zL : omegaGroup hQ) : OGroup Q) = 1 :=
    congrArg Subtype.val hφzz
  have hzt4 : invType ((φ zL : omegaGroup hQ) : OGroup Q) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn hztt hφz1).mp ((t5_isI4PlusIn_iff hL hφ hzL hz2).mp hI4)
  let D : Om6Par Q ((φ zL : omegaGroup hQ) : OGroup Q) := Om6Par.mk' hQ hdim hsgn hztt hzt4
  exact ⟨hztt, D.dimW, D.dimP, D.signP⟩

theorem fa8fin_image {φ : ↥L →* omegaGroup hQ} (hcov : OddCentralCover φ) {M : Subgroup G}
    (hML : M ≤ L) (hcard : Nat.card M = 32) {z : G} (hzM : z ∈ M)
    (hzc : ∀ g ∈ M, g * z = z * g) (hsq : ∀ g ∈ M, g * g = 1 ∨ g * g = z)
    (hpart : ∀ g ∈ M, g ≠ 1 → g ≠ z → ∃ h ∈ M, h * g * h⁻¹ = z * g) :
    ∃ R : Subgroup (OGroup Q), Nat.card R = 32 ∧ R ≤ omegaGroup hQ ∧
      (∀ l : ↥L, (l : G) ∈ M → sec5cdPhi φ l ∈ R) ∧
      (∀ g ∈ R, ∃ l : ↥L, (l : G) ∈ M ∧ sec5cdPhi φ l = g) ∧
      sec5cdPhi φ ⟨z, hML hzM⟩ ∈ R ∧
      (∀ g ∈ R, g * sec5cdPhi φ ⟨z, hML hzM⟩ = sec5cdPhi φ ⟨z, hML hzM⟩ * g) ∧
      (∀ g ∈ R, g * g = 1 ∨ g * g = sec5cdPhi φ ⟨z, hML hzM⟩) ∧
      (∀ g ∈ R, g ≠ 1 → g ≠ sec5cdPhi φ ⟨z, hML hzM⟩ →
        ∃ h ∈ R, h * g * h⁻¹ = sec5cdPhi φ ⟨z, hML hzM⟩ * g) := by
  let ψ : ↥M →* OGroup Q := (sec5cdPhi φ).comp (Subgroup.inclusion hML)
  have hψ : ∀ a : ↥M, ψ a = sec5cdPhi φ ⟨(a : G), hML a.2⟩ := fun _ => rfl
  have hpow : ∀ a : ↥M, (Subgroup.inclusion hML a) ^ 2 ^ 5 = 1 := by
    intro a
    rw [← map_pow, show (2 : ℕ) ^ 5 = Nat.card ↥M by rw [hcard]; norm_num,
      pow_card_eq_one', map_one]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact Subgroup.inclusion_injective hML
      (fa8fin_cover_inj hcov (hpow a) (hpow b) (Subtype.ext hab))
  have hzψ : ψ ⟨z, hzM⟩ = sec5cdPhi φ ⟨z, hML hzM⟩ := rfl
  refine ⟨ψ.range, ?_, ?_, ?_, ?_, ⟨⟨z, hzM⟩, rfl⟩, ?_, ?_, ?_⟩
  · rw [← hcard]
    exact Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm
  · rintro _ ⟨a, rfl⟩
    exact (φ ⟨(a : G), hML a.2⟩).2
  · intro l hl
    exact ⟨⟨l, hl⟩, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨⟨(a : G), hML a.2⟩, a.2, rfl⟩
  · rintro _ ⟨a, rfl⟩
    have h1 : a * ⟨z, hzM⟩ = ⟨z, hzM⟩ * a := Subtype.ext (hzc (a : G) a.2)
    rw [← hzψ, ← map_mul, ← map_mul, h1]
  · rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    rcases hsq (a : G) a.2 with h | h
    · left
      rw [show a * a = 1 from Subtype.ext h, map_one]
    · right
      rw [show a * a = ⟨z, hzM⟩ from Subtype.ext h]
      exact hzψ
  · rintro _ ⟨a, rfl⟩ hg1 hgs
    have ha1 : (a : G) ≠ 1 := fun h => hg1 (by rw [show a = 1 from Subtype.ext h, map_one])
    have haz : (a : G) ≠ z := fun h => hgs (by
      rw [show a = ⟨z, hzM⟩ from Subtype.ext h]
      exact hzψ)
    obtain ⟨h, hh, hhg⟩ := hpart (a : G) a.2 ha1 haz
    refine ⟨ψ ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩, ?_⟩
    have hconj : (⟨h, hh⟩ : ↥M) * a * (⟨h, hh⟩ : ↥M)⁻¹ = ⟨z, hzM⟩ * a := Subtype.ext hhg
    calc ψ ⟨h, hh⟩ * ψ a * (ψ ⟨h, hh⟩)⁻¹
        = ψ ((⟨h, hh⟩ : ↥M) * a * (⟨h, hh⟩ : ↥M)⁻¹) := by simp only [map_mul, map_inv]
      _ = ψ (⟨z, hzM⟩ * a) := by rw [hconj]
      _ = sec5cdPhi φ ⟨z, hML hzM⟩ * ψ a := by rw [map_mul]; rfl

end CFSG.OddStandard.SmallF3.Omega
