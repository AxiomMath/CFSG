module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Step1
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Fixed
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Perm5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Derived

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed
open CFSG.ComponentClassification.SolMax.FiveCat

theorem fusionOddCore_eq_bot_of_cent {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hSn : S.Normal) (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hcent : centralizer (S : Set G) = ⊥) : Open.fusionOddCore G = ⊥ := by
  refine le_bot_iff.1 (sSup_le ?_)
  rintro N ⟨hN, hodd⟩
  haveI := hN
  haveI := hSn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf S) with hb | ht
  · intro n hn
    rw [Subgroup.mem_bot]
    have hcomm : ∀ s ∈ S, s * n = n * s := by
      intro s hs
      have h1 : s * n * s⁻¹ * n⁻¹ ∈ N := N.mul_mem (hN.conj_mem n hn s) (N.inv_mem hn)
      have h2 : s * (n * s⁻¹ * n⁻¹) ∈ S :=
        S.mul_mem hs (hSn.conj_mem s⁻¹ (S.inv_mem hs) n)
      have h3 : (⟨s * (n * s⁻¹ * n⁻¹), h2⟩ : ↥S) ∈ N.subgroupOf S := by
        rw [Subgroup.mem_subgroupOf]
        have e : s * (n * s⁻¹ * n⁻¹) = s * n * s⁻¹ * n⁻¹ := by group
        show s * (n * s⁻¹ * n⁻¹) ∈ N
        rw [e]
        exact h1
      rw [hb, Subgroup.mem_bot] at h3
      have h4 : s * (n * s⁻¹ * n⁻¹) = 1 := congrArg Subtype.val h3
      have h5 : s * n * s⁻¹ * n⁻¹ = 1 := by rw [← h4]; group
      exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h5)
    have : n ∈ centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      exact hcomm
    rw [hcent, Subgroup.mem_bot] at this
    exact this
  · exfalso
    have hSN : S ≤ N := by
      intro s hs
      have : (⟨s, hs⟩ : ↥S) ∈ N.subgroupOf S := by rw [ht]; exact Subgroup.mem_top _
      exact this
    have hdvd : Nat.card ↥S ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hSN
    have hSodd : Odd (Nat.card ↥S) := Odd.of_dvd_nat hodd hdvd
    have hsolv : Group.IsSolvable ↥S := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hSodd
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 hsolv) a b)

theorem centralizerDerived_eq_alt {G : Type*} [Group G] {t : G}
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    centralizerDerived t = (alternatingGroup (Fin 5)).map (embA ζ) := by
  rw [centralizerDerived_eq_map ζ, alternatingGroup.commutator_perm_eq (by simp)]

theorem derived_equiv_alt_five {G : Type*} [Group G] {t : G}
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    Nonempty (↥(centralizerDerived t) ≃* alternatingGroup (Fin 5)) := by
  rw [centralizerDerived_eq_alt ζ]
  exact ⟨(Subgroup.equivMapOfInjective _ (embA ζ) (embA_injective ζ)).symm⟩

theorem derived_le_of_cent {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hSn : S.Normal) (hS : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    centralizerDerived t ≤ S := by
  have hO : Open.fusionOddCore G = ⊥ := fusionOddCore_eq_bot_of_cent hSn hS hnab hcent
  have htc : t ∉ Subgroup.center G := by
    intro htc
    apply ne_one_of_orderOf_eq_two ht
    have : t ∈ centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x _
      exact Subgroup.mem_center_iff.1 htc x
    rw [hcent, Subgroup.mem_bot] at this
    exact this
  have hset := setting_of_RHyp rhyp_perm5 hO ht ζ htc
  obtain ⟨a, b, hab⟩ := hnab
  have hfix : FixedData G S :=
    ⟨hSn, hS, ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩, hcent⟩
  rw [centralizerDerived_eq_alt ζ]
  exact setting_le_of_fixedData hset hfix

theorem fivePumpOutcome_one {G : Type} [Group G] [Finite G] (hleaf : FivePumpLeaf)
    {S : Subgroup G} (hSn : S.Normal) (hS : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hcat : Blueprint.Catalog ↥S)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2)
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :
    FivePumpOutcome ↥S := by
  haveI := hSn
  exact fivePumpOutcome_of_derived hleaf hS hnab hcat hcent ht
    (derived_le_of_cent hSn hS hnab hcent ht ζ) (derived_equiv_alt_five ζ)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
