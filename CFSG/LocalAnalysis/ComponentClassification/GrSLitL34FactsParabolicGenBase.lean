
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPositionBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFrattini

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] {J P : Subgroup G}

variable {q : Jhat J →* Equiv.Perm (Fin 42)}

theorem conj_mem_pullP (hP : IsSylowTwoIn P J) {U : Subgroup (Equiv.Perm (Fin 42))} {n : G}
    (hn : n ∈ J) (hnP : n ∈ normalizer (P : Set G))
    (hnU : q (jq J ⟨n, hn⟩) ∈ normalizer (U : Set (Equiv.Perm (Fin 42)))) {g : G}
    (hg : g ∈ pullP J P hP.1 (U.comap q)) : n * g * n⁻¹ ∈ pullP J P hP.1 (U.comap q) := by
  obtain ⟨hgP, hgU⟩ := mem_pullP.1 hg
  refine mem_pullP.2 ⟨(mem_normalizer_iff.mp hnP g).mp hgP, ?_⟩
  have e : (⟨n * g * n⁻¹, hP.1 ((mem_normalizer_iff.mp hnP g).mp hgP)⟩ : J) =
      ⟨n, hn⟩ * ⟨g, hP.1 hgP⟩ * (⟨n, hn⟩ : J)⁻¹ := rfl
  rw [mem_comap, e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.mp hnU _).mp hgU

theorem mem_normalizer_pullP (hP : IsSylowTwoIn P J) {U : Subgroup (Equiv.Perm (Fin 42))} {n : G}
    (hn : n ∈ J) (hnP : n ∈ normalizer (P : Set G))
    (hnU : q (jq J ⟨n, hn⟩) ∈ normalizer (U : Set (Equiv.Perm (Fin 42)))) :
    n ∈ normalizer (pullP J P hP.1 (U.comap q) : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_pullP hP hn hnP hnU, fun hg => ?_⟩
  have hn' : n⁻¹ ∈ J := J.inv_mem hn
  have hnU' : q (jq J ⟨n⁻¹, hn'⟩) ∈ normalizer (U : Set (Equiv.Perm (Fin 42))) := by
    have : (⟨n⁻¹, hn'⟩ : J) = (⟨n, hn⟩ : J)⁻¹ := rfl
    rw [this, map_inv, map_inv]
    exact inv_mem hnU
  have := conj_mem_pullP hP hn' (inv_mem hnP) hnU' hg
  rwa [show n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g by group] at this

theorem le_normalizer_pullP (hP : IsSylowTwoIn P J)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {U : Subgroup (Equiv.Perm (Fin 42))} (hU : T0 ≤ normalizer (U : Set (Equiv.Perm (Fin 42)))) :
    P ≤ normalizer (pullP J P hP.1 (U.comap q) : Set G) := fun p hp =>
  mem_normalizer_pullP hP (hP.1 hp) (le_normalizer hp) (hU ((hT _).2 ⟨p, hp, _, rfl⟩))

theorem exists_lift_normalizer [Finite G] (hP : IsSylowTwoIn P J) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e)
    {U : Subgroup (Equiv.Perm (Fin 42))} (hUT : U ≤ T0) {s : Equiv.Perm (Fin 42)} (hs : s ∈ S)
    (hsU : s ∈ normalizer (U : Set (Equiv.Perm (Fin 42)))) :
    ∃ n, ∃ hn : n ∈ J, n ∈ normalizer (pullP J P hP.1 (U.comap q) : Set G) ∧
      q (jq J ⟨n, hn⟩) * s⁻¹ ∈ U := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨e₀, he₀⟩ := hqsurj s hs
  obtain ⟨j₀, rfl⟩ := jq_surjective J e₀
  set M : Subgroup G := ((U.comap q).comap (jq J)).map J.subtype with hM
  have hmemM : ∀ g : G, g ∈ M ↔ ∃ hg : g ∈ J, q (jq J ⟨g, hg⟩) ∈ U := by
    intro g
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, hj⟩
    · rintro ⟨hg, h⟩
      exact ⟨⟨g, hg⟩, h, rfl⟩
  set T := pullP J P hP.1 (U.comap q) with hTd
  have hTM : T ≤ M := fun g hg => by
    obtain ⟨hgP, hgU⟩ := mem_pullP.1 hg
    exact (hmemM g).2 ⟨hP.1 hgP, hgU⟩
  have hcardT : Nat.card T = Nat.card (U.comap q) := card_pullP hP2 hT (comap_mono hUT)
  have hcardM : Nat.card M = Nat.card T * Nat.card (pPrimeCore 2 ↥J) := by
    rw [hM, Subgroup.card_map_of_injective Subtype.val_injective,
      card_comap_eq (jq J) (U.comap q) (fun e _ => jq_surjective J e), hcardT,
      QuotientGroup.ker_mk']
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl : IsSylowTwoIn T M := isSylowTwoIn_of_card hTM (hP2.to_le (pullP_le _)) hcardM
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card)
  have hconj : ∀ k : J, q (jq J k) ∈ normalizer (U : Set (Equiv.Perm (Fin 42))) →
      ∀ g ∈ M, (k : G) * g * (k : G)⁻¹ ∈ M := by
    intro k hk g hg
    obtain ⟨hgJ, hgU⟩ := (hmemM g).1 hg
    refine (hmemM _).2 ⟨J.mul_mem (J.mul_mem k.2 hgJ) (J.inv_mem k.2), ?_⟩
    have e : (⟨(k : G) * g * (k : G)⁻¹, J.mul_mem (J.mul_mem k.2 hgJ) (J.inv_mem k.2)⟩ : J) =
        k * ⟨g, hgJ⟩ * k⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hk _).mp hgU
  have hj₀M : (j₀ : G) ∈ normalizer (M : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hconj j₀ (he₀ ▸ hsU) g, fun hg => ?_⟩
    have hk : q (jq J j₀⁻¹) ∈ normalizer (U : Set (Equiv.Perm (Fin 42))) := by
      rw [map_inv, map_inv, he₀]
      exact inv_mem hsU
    have := hconj j₀⁻¹ hk _ hg
    rwa [show ((j₀⁻¹ : J) : G) * ((j₀ : G) * g * (j₀ : G)⁻¹) * ((j₀⁻¹ : J) : G)⁻¹ = g by
      simp only [Subgroup.coe_inv]
      group] at this
  obtain ⟨m, hmM, hmn⟩ := exists_mul_mem_normalizer hSyl hj₀M
  obtain ⟨hmJ, hmU⟩ := (hmemM m).1 hmM
  refine ⟨m * j₀, J.mul_mem hmJ j₀.2, hmn, ?_⟩
  have e : (⟨m * (j₀ : G), J.mul_mem hmJ j₀.2⟩ : J) = ⟨m, hmJ⟩ * j₀ := rfl
  rw [e, map_mul, map_mul, he₀, mul_inv_cancel_right]
  exact hmU

end CFSG.ComponentClassification.GrSLit.L34Facts
