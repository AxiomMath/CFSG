module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Skeleton
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDataCore

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.HSFLit

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}

theorem card_T_eq_two_pow :
    Nat.card A.T = 2 ^ (Nat.card (centralizer ({t} : Set X))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SDData.T, Config.sylowIn, card_map_of_injective (subtype_injective _),
    Sylow.card_eq_multiplicity]

theorem card_T_eq_of_le {H : Subgroup X} (hTH : A.T ≤ H)
    (hH : H ≤ centralizer ({t} : Set X)) :
    Nat.card A.T = 2 ^ (Nat.card H).factorization 2 := by
  have hC := card_T_eq_two_pow (A := A)
  have h1 : Nat.card H ∣ Nat.card (centralizer ({t} : Set X)) := Subgroup.card_dvd_of_le hH
  have h2 : Nat.card A.T ∣ Nat.card H := Subgroup.card_dvd_of_le hTH
  have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hposC : Nat.card (centralizer ({t} : Set X)) ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card H).factorization 2 ≤
      (Nat.card (centralizer ({t} : Set X))).factorization 2 :=
    (Nat.factorization_le_iff_dvd hpos hposC).mpr h1 2
  have h4 : (Nat.card (centralizer ({t} : Set X))).factorization 2 ≤
      (Nat.card H).factorization 2 := by
    rw [hC] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp h2
  rw [hC, le_antisymm h3 h4]

theorem exists_conj_le_T {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPt : P ≤ centralizer ({t} : Set X)) :
    ∃ h ∈ centralizer ({t} : Set X), P.map (MulAut.conj h).toMonoidHom ≤ A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({t} : Set X))) :=
    hP.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) Q A.syl
  refine ⟨h, h.2, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hpC : p ∈ centralizer ({t} : Set X) := hPt hp
  have hpQ : (⟨p, hpC⟩ : centralizer ({t} : Set X)) ∈ (Q : Subgroup _) := hQ hp
  have : h * (⟨p, hpC⟩ : centralizer ({t} : Set X)) * h⁻¹ ∈ (A.syl : Subgroup _) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact ⟨_, hpQ, rfl⟩
  exact ⟨_, this, rfl⟩

theorem mem_normalizer_L2E {z w k d : X} (h₁ : d * z * d⁻¹ ∈ L2E z w t k)
    (h₂ : d * w * d⁻¹ ∈ L2E z w t k) (h₃ : d * t * d⁻¹ ∈ L2E z w t k)
    (h₄ : d * k * d⁻¹ ∈ L2E z w t k) : d ∈ normalizer (L2E z w t k : Set X) := by
  have hle : L2E z w t k ≤ (L2E z w t k).comap (MulAut.conj d).toMonoidHom := by
    rw [L2E, closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hs with rfl | rfl | rfl | rfl
    exacts [h₁, h₂, h₃, h₄]
  have hle' : (L2E z w t k).map (MulAut.conj d).toMonoidHom ≤ L2E z w t k := by
    rintro _ ⟨e, he, rfl⟩
    exact hle he
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hle'
    (card_map_of_injective (MulAut.conj d).injective).ge)

end CFSG.OddStandard.SmallF3.L33.KD.SD
