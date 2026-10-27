module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CCnt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CP

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem map_ne_of_isPComponent_centralizer {X : Type*} [Group X] [Finite X] {β : X}
    (hβ : β * β = 1) {M₁ M₂ : Subgroup X}
    (h₁C : M₁ ≤ centralizer ({β} : Set X)) (h₂C : M₂ ≤ centralizer ({β} : Set X))
    (h₁ : IsPComponent 2 (M₁.subgroupOf (centralizer ({β} : Set X))))
    (h₂ : IsPComponent 2 (M₂.subgroupOf (centralizer ({β} : Set X)))) (hne : M₁ ≠ M₂) :
    M₁.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≠ M₂.map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  set C₀ := centralizer ({β} : Set X) with hC₀
  set C := centralizer ({π β} : Set (X ⧸ pPrimeCore 2 X)) with hCdef
  have hC : C = C₀.map π := OddQuot.centralizer_singleton_map_eq hβ
  let ρ : C₀ →* C := (π.comp C₀.subtype).codRestrict C fun c => by
    rw [hC]
    exact mem_map_of_mem _ c.2
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [hC] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hρk : ¬ 2 ∣ Nat.card ρ.ker := by
    rw [MonoidHom.ker_codRestrict]
    exact OddQuot.not_two_dvd_card_ker_domRestrict π OddQuot.not_two_dvd_card_ker C₀
  obtain ⟨hbij, -, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection ρ hρs hρk
  have hcomp : C.subtype.comp ρ = π.comp C₀.subtype := MonoidHom.ext fun _ => rfl
  have hmap : ∀ M : Subgroup X, M ≤ C₀ → ((M.subgroupOf C₀).map ρ).map C.subtype = M.map π := by
    intro M hM
    rw [map_map, hcomp, ← map_map, subgroupOf_map_subtype, inf_of_le_left hM]
  intro heq
  apply hne
  have h1 : (M₁.subgroupOf C₀).map ρ = (M₂.subgroupOf C₀).map ρ := by
    apply map_injective C.subtype_injective
    rw [hmap M₁ h₁C, hmap M₂ h₂C, heq]
  have h2 := hbij.injOn h₁ h₂ h1
  rwa [subgroupOf_inj, inf_of_le_left h₁C, inf_of_le_left h₂C] at h2

theorem add_le_padicValNat_sup {Y : Type*} [Group Y] [Finite Y] (r : ℕ) [Fact r.Prime]
    (hr : r ≠ 2) {P₁ P₂ : Subgroup Y} (h₁ : IsPComponent 2 P₁) (h₂ : IsPComponent 2 P₂)
    (hne : P₁ ≠ P₂) :
    padicValNat r (Nat.card (P₁ ⧸ pPrimeCore 2 P₁)) +
        padicValNat r (Nat.card (P₂ ⧸ pPrimeCore 2 P₂)) ≤
      padicValNat r (Nat.card (P₁ ⊔ P₂ : Subgroup Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  obtain ⟨hbij, -, hiso⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    π (QuotientGroup.mk'_surjective _) OddQuot.not_two_dvd_card_ker
  have hO : pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hQ₁ : IsComponent (P₁.map π) := B5a.isComponent_of_isPComponent hO (hbij.mapsTo h₁)
  have hQ₂ : IsComponent (P₂.map π) := B5a.isComponent_of_isPComponent hO (hbij.mapsTo h₂)
  have hQne : P₁.map π ≠ P₂.map π := fun h => hne (hbij.injOn h₁ h₂ h)
  have hcomm := (LocalCores.distinct_components_commute hQ₁ hQ₂).resolve_left hQne
  have hQ₂Q₁ : P₂.map π ≤ centralizer ((P₁.map π : Subgroup _) : Set (Y ⧸ pPrimeCore 2 Y)) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hcomm
  have h1 := X10CV.nu_sup_add_nu_inf r (hQ₂Q₁.trans (centralizer_le_normalizer _))
  have h2 : padicValNat r (Nat.card (P₁.map π ⊓ P₂.map π : Subgroup _)) = 0 := by
    obtain ⟨-, hZ⟩ := X10CC.isPGroup_center_of_isComponent hO hQ₁
    have hle : P₁.map π ⊓ P₂.map π ≤ (center (P₁.map π)).map (P₁.map π).subtype := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
      refine ⟨⟨y, hy1⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp (hQ₂Q₁ hy2) g g.2)
    obtain ⟨n, hn⟩ := hZ.exists_card_eq
    have hdvd : Nat.card (P₁.map π ⊓ P₂.map π : Subgroup _) ∣ 2 ^ n := by
      rw [← hn, ← card_map_of_injective (P₁.map π).subtype_injective]
      exact card_dvd_of_le hle
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hm]
    refine padicValNat.eq_zero_of_not_dvd fun h => hr ?_
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : r.Prime).dvd_of_dvd_pow h)
  have h3 : ∀ P : Subgroup Y, IsPComponent 2 P →
      padicValNat r (Nat.card (P ⧸ pPrimeCore 2 P)) ≤ padicValNat r (Nat.card (P.map π)) := by
    intro P hP
    obtain ⟨e, -⟩ := hiso P hP
    rw [Nat.card_congr e.toEquiv]
    exact X10CV.padicValNat_le_of_dvd' r Nat.card_pos.ne' (card_quotient_dvd_card _)
  have h4 : padicValNat r (Nat.card (P₁.map π ⊔ P₂.map π : Subgroup _)) ≤
      padicValNat r (Nat.card (P₁ ⊔ P₂ : Subgroup Y)) := by
    rw [← Subgroup.map_sup]
    exact X10CV.nu_map_le r π (P₁ ⊔ P₂)
  have h5 := h3 P₁ h₁
  have h6 := h3 P₂ h₂
  omega

end CFSG.ComponentClassification.CatLeafProof.X10CP
