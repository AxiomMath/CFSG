module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81KLoc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Conf

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem card_le_card_sylow_of_card_eq {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (hc : Nat.card G = Nat.card G') {A : Subgroup G} (hA : IsPGroup 2 A) (T : Sylow 2 G') :
    Nat.card A ≤ Nat.card (T : Subgroup G') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := hA.exists_le_sylow
  calc Nat.card A ≤ Nat.card (T₀ : Subgroup G) := card_le_of_le hT₀
    _ = Nat.card (T : Subgroup G') := by
        rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, hc]

theorem mem_normalizer_subgroupOf_of_inf {G : Type*} [Group G] {M Q : Subgroup G} {g : G}
    (hgM : g ∈ M) (hg : g ∈ normalizer ((Q ⊓ M : Subgroup G) : Set G)) :
    (⟨g, hgM⟩ : M) ∈ normalizer ((Q.subgroupOf M : Subgroup M) : Set M) := by
  rw [mem_normalizer_iff]
  intro m
  have h1 := mem_normalizer_iff.mp hg m
  simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, mem_inf] at h1 ⊢
  constructor
  · intro hm
    exact (h1.mp ⟨hm, m.2⟩).1
  · intro hm
    exact (h1.mpr ⟨hm, mul_mem (mul_mem hgM m.2) (inv_mem hgM)⟩).1

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace KLoc

variable (H : KLoc h)
include H

theorem JB_le_M3 : h.JB ≤ h.M3 := H.fixedLayer_le_K.trans le_sup_left

theorem D_le_M3 : h.D ≤ h.M3 := h.D_le_JB.trans H.JB_le_M3

theorem rho_mem_inn_of_mem_K {m : ↥h.M3} (hm : (m : X) ∈ h.K) :
    H.rho m ∈ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) := by
  have : m = ⟨(m : X), mem_sup_left hm⟩ := rfl
  rw [this, H.rho_of_mem_K hm]
  exact ⟨_, rfl⟩

theorem map_JB_le_innFix :
    (h.JB.subgroupOf h.M3).map H.rho ≤ Cat8.innFix (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
  rintro _ ⟨m, hm, rfl⟩
  have hmJB : (m : X) ∈ h.JB := hm
  have hmJ : (m : X) ∈ h.J := ((GSLit.fixedLayer_le_inf h.J h.B) hmJB).1
  refine ⟨H.rho_mem_inn_of_mem_K (H.fixedLayer_le_K hmJB), ?_⟩
  show H.rho m ∈ centralizer ({H.rhoA} : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))
  rw [mem_centralizer_singleton_iff, ← H.rho_aM, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (mem_centralizer_singleton_iff.mp (h.J_le hmJ))

theorem commutator_JB_subgroupOf :
    ⁅h.JB.subgroupOf h.M3, h.JB.subgroupOf h.M3⁆ = h.JB.subgroupOf h.M3 := by
  apply map_injective h.M3.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le H.JB_le_M3]
  exact commutator_fixedLayer_eq h.J h.B

theorem map_JB_eq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hJo : CFSec8JOrder)
    (hL0 : CF81L0) :
    (h.JB.subgroupOf h.M3).map H.rho = Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.case8
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hle : (h.JB.subgroupOf h.M3).map H.rho ≤ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
    rw [← H.commutator_JB_subgroupOf, map_commutator]
    exact commutator_mono H.map_JB_le_innFix H.map_JB_le_innFix
  refine eq_of_le_of_card_ge hle ?_
  rw [hL0 _ p f hp hp2 hf hK _ (H.rhoA_admQ hCF1 hCF2 hJo hp hp2 hf hJ)]
  have h1 := card_quotient_dvd_card_map H.rho hker (h.JB.subgroupOf h.M3)
  let e2 : h.JB ≃* h.JB.subgroupOf h.M3 := (subgroupOfEquivOfLe H.JB_le_M3).symm
  let e3 : h.JB ⧸ pPrimeCore 2 h.JB ≃* (h.JB.subgroupOf h.M3) ⧸
      pPrimeCore 2 (h.JB.subgroupOf h.M3) :=
    QuotientGroup.congr (pPrimeCore 2 h.JB) (pPrimeCore 2 (h.JB.subgroupOf h.M3)) e2
      (pPrimeCore_map_iso 2 e2)
  rw [← Nat.card_congr e3.toEquiv, h.card_JB_quotient, hJo _ p f hp hp2 hf hJ] at h1
  exact Nat.le_of_dvd Nat.card_pos h1

theorem map_D_eq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) (hJo : CFSec8JOrder)
    (hL0 : CF81L0) :
    (h.D.subgroupOf h.M3).map H.rho =
      (h.Q.subgroupOf h.M3).map H.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Sec8Case.exists_params h H.case8
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hD2 : IsPGroup 2 h.D := (Six.isPGroup_S h).to_le inf_le_left
  have hle : (h.D.subgroupOf h.M3).map H.rho ≤
      (h.Q.subgroupOf h.M3).map H.rho ⊓ Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA := by
    refine le_inf (map_mono fun m hm => h.sec8_D_le_Q hm) ?_
    rw [← H.map_JB_eq hCF1 hCF2 hJo hL0]
    exact map_mono fun m hm => h.D_le_JB hm
  refine eq_of_le_of_card_ge hle ?_
  have hD2' : IsPGroup 2 (h.D.subgroupOf h.M3) := hD2.comap_subtype
  have hcD : Nat.card ((h.D.subgroupOf h.M3).map H.rho) = Nat.card h.D := by
    rw [Eight.card_map_of_isPGroup hker hD2',
      ← card_map_of_injective h.M3.subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr H.D_le_M3]
  rw [hcD]
  obtain ⟨R, hR⟩ := h.sec8_D_sylow
  set T : Sylow 2 (h.J ⧸ pPrimeCore 2 h.J) := R.mapSurjective (QuotientGroup.mk'_surjective _)
  have hT : Nat.card (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) = Nat.card h.D := by
    have hker' : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥h.J)).ker := by
      rw [QuotientGroup.ker_mk']
      exact (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := ↥h.J))
    rw [Sylow.coe_mapSurjective, Eight.card_map_of_isPGroup hker' R.isPGroup', hR,
      Six.card_subgroupOf_eq, inf_eq_left.mpr inf_le_right]
  have hcL : Nat.card (Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA) =
      Nat.card (h.J ⧸ pPrimeCore 2 h.J) := by
    rw [hL0 _ p f hp hp2 hf hK _ (H.rhoA_admQ hCF1 hCF2 hJo hp hp2 hf hJ),
      hJo _ p f hp hp2 hf hJ]
  have hA2 : IsPGroup 2 (((h.Q.subgroupOf h.M3).map H.rho ⊓
      Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA).subgroupOf
        (Cat8.L0 (h.K ⧸ pPrimeCore 2 h.K) H.rhoA)) :=
    ((h.sec8_isPGroup_Q.comap_subtype.map H.rho).to_le inf_le_left).comap_subtype
  have h1 := card_le_card_sylow_of_card_eq hcL hA2 T
  rw [Six.card_subgroupOf_eq, inf_eq_left.mpr inf_le_right, hT] at h1
  exact h1

end KLoc

end Hyp52

end CFSG.ComponentClassification.GSThmB
