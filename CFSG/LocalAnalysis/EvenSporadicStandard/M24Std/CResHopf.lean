module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open
open scoped commutatorElement

variable {P E : Type} [Group P] [Group E]

theorem exists_surjective_hopfMultiplier (hP : commutator P = ⊤) (π : P →* E)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center P) :
    ∃ ψ : griessHopfMultiplier E →* π.ker, Function.Surjective ψ := by
  classical
  choose s hs using hπ
  let ε : FreeGroup E →* E := FreeGroup.lift (id : E → E)
  let φ : FreeGroup E →* P := FreeGroup.lift s
  have hεφ : π.comp φ = ε := by
    apply FreeGroup.ext_hom
    intro x
    simp [φ, ε, hs]
  have hR : ∀ f : FreeGroup E, f ∈ griessHopfRelations E → φ f ∈ π.ker := by
    intro f hf
    rw [MonoidHom.mem_ker] at hf ⊢
    have := DFunLike.congr_fun hεφ f
    simp only [MonoidHom.comp_apply] at this
    rw [this]
    exact hf
  let M0 : Subgroup (FreeGroup E) := griessHopfRelations E ⊓ commutator (FreeGroup E)
  let ψ0 : M0 →* π.ker :=
    (φ.comp M0.subtype).codRestrict π.ker fun m => hR m (mem_inf.1 m.2).1
  have hN : (⁅(⊤ : Subgroup (FreeGroup E)), griessHopfRelations E⁆).subgroupOf M0 ≤ ψ0.ker := by
    intro m hm
    rw [mem_subgroupOf] at hm
    have hker : ⁅(⊤ : Subgroup (FreeGroup E)), griessHopfRelations E⁆ ≤ φ.ker := by
      rw [Subgroup.commutator_le]
      intro f _ r hr
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hz : φ r ∈ center P := hcen (hR r hr)
      exact commutatorElement_eq_one_iff_commute.2 (mem_center_iff.1 hz (φ f))
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (MonoidHom.mem_ker.1 (hker hm))
  refine ⟨QuotientGroup.lift _ ψ0 hN, ?_⟩
  have hsurj : Function.Surjective ψ0 := by
    intro z
    have hz : (z : P) ∈ commutator P := hP ▸ mem_top _
    have hle : commutator P ≤ (commutator (FreeGroup E)).map φ := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      set a' := (φ (FreeGroup.of (π a)))⁻¹ * a with ha'
      set b' := (φ (FreeGroup.of (π b)))⁻¹ * b with hb'
      have hπa : π (φ (FreeGroup.of (π a))) = π a := by
        have := DFunLike.congr_fun hεφ (FreeGroup.of (π a))
        simpa [ε] using this
      have hπb : π (φ (FreeGroup.of (π b))) = π b := by
        have := DFunLike.congr_fun hεφ (FreeGroup.of (π b))
        simpa [ε] using this
      have ha1 : a' ∈ center P := hcen (by
        rw [MonoidHom.mem_ker, ha', map_mul, map_inv, hπa, inv_mul_cancel])
      have hb1 : b' ∈ center P := hcen (by
        rw [MonoidHom.mem_ker, hb', map_mul, map_inv, hπb, inv_mul_cancel])
      have ea : a = φ (FreeGroup.of (π a)) * a' := by rw [ha']; group
      have eb : b = φ (FreeGroup.of (π b)) * b' := by rw [hb']; group
      have key : ⁅a, b⁆ = ⁅φ (FreeGroup.of (π a)), φ (FreeGroup.of (π b))⁆ := by
        conv_lhs => rw [ea, eb]
        rw [← CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center
          (one_mem _) (one_mem _) (φ (FreeGroup.of (π a))) (φ (FreeGroup.of (π b)))]
        have h1 : ⁅φ (FreeGroup.of (π a)) * a', φ (FreeGroup.of (π b)) * b'⁆ =
            ⁅a' * φ (FreeGroup.of (π a)), b' * φ (FreeGroup.of (π b))⁆ := by
          rw [mem_center_iff.1 ha1 (φ (FreeGroup.of (π a))),
            mem_center_iff.1 hb1 (φ (FreeGroup.of (π b)))]
        rw [h1, CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center ha1 hb1,
          one_mul, one_mul]
      rw [key, ← map_commutatorElement]
      rw [_root_.commutator_def]
      exact mem_map_of_mem φ (Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
    obtain ⟨c, hc, hcz⟩ := hle hz
    refine ⟨⟨c, ?_, hc⟩, Subtype.ext hcz⟩
    show c ∈ (FreeGroup.lift (id : E → E)).ker
    rw [MonoidHom.mem_ker]
    have := DFunLike.congr_fun hεφ c
    simp only [MonoidHom.comp_apply] at this
    rw [← this, hcz]
    exact z.2
  intro z
  obtain ⟨m, hm⟩ := hsurj z
  exact ⟨QuotientGroup.mk m, by simpa using hm⟩

theorem card_ker_dvd_hopfMultiplier (hP : commutator P = ⊤) (π : P →* E)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center P) :
    Nat.card π.ker ∣ Nat.card (griessHopfMultiplier E) := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_hopfMultiplier hP π hπ hcen
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  exact Dvd.intro _ rfl

theorem card_ker_eq_one_of_odd [Finite P] (hP : commutator P = ⊤) (π : P →* E)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center P) (hodd : Odd (Nat.card π.ker))
    (hM : Nat.card (griessHopfMultiplier E) ∣ 2) : Nat.card π.ker = 1 := by
  have h := (card_ker_dvd_hopfMultiplier hP π hπ hcen).trans hM
  have h2 : Nat.card π.ker = 1 ∨ Nat.card π.ker = 2 := (Nat.dvd_prime Nat.prime_two).1 h
  rcases h2 with h2 | h2
  · exact h2
  · rw [h2] at hodd
    exact absurd hodd (by decide)

end CFSG.EvenSporadicStandard.M24Std
