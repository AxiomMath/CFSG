module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226SBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L226SComp
public import CFSG.GH74.GLS.Balance.Bender.Final

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace F3L226S

variable {G : Type} [Group G] [Finite G]

theorem lemma226_solvable {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) (hc : z₁ * z₂ = z₂ * z₁)
    {L₁ L₂ : Subgroup G} (hL₁ : IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hL₂ : IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) (hz₂L : z₂ ∈ L₂)
    (hns : ¬ (((pPrimeCore 2 ↥(centralizer ({z₁} : Set G))).map (centralizer {z₁}).subtype ⊔
        GH74.GLS.oPrimeResidualOf 3 L₁).subgroupOf (centralizer {z₁})).IsSubnormal) :
    ∃ K : Subgroup G, IsTwoComponentIn K (centralizer {z₁}) ∧
      GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K ∧
      centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) ∧
      ⁅K, GH74.GLS.oPrimeResidualOf 3 L₁⁆ = K ∧
      ∃ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
        center (↥K ⧸ pPrimeCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₂C : z₂ ∈ centralizer ({z₁} : Set G) := mem_centralizer_singleton_iff.mpr hc.symm
  have hxo : orderOf (⟨z₂, hz₂C⟩ : ↥(centralizer ({z₁} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz₂
  have hx2 : (⟨z₂, hz₂C⟩ : ↥(centralizer ({z₁} : Set G))) ^ 2 = 1 := by
    rw [← hxo, pow_orderOf_eq_one]
  have hz2 : z₂ ^ 2 = 1 := by rw [← hz₂, pow_orderOf_eq_one]
  have hL₂C : L₂ ≤ centralizer ({z₁} : Set G) := hL₂.1.trans inf_le_left
  have hL₂' : IsSolvableTwoComponentIn (L₂.subgroupOf (centralizer {z₁}))
      (centralizer {(⟨z₂, hz₂C⟩ : ↥(centralizer ({z₁} : Set G)))}) := by
    rw [F3L226.centralizer_mk_eq hz₂C]
    exact F3L226.isSolvableTwoComponentIn_subgroupOf hL₂.1 inf_le_left hL₂
  have hxL : (⟨z₂, hz₂C⟩ : ↥(centralizer ({z₁} : Set G))) ∈ L₂.subgroupOf (centralizer {z₁}) :=
    hz₂L
  obtain ⟨e⟩ := F3L221.nonempty_sl23_of_central hL₂' hxL hxo
    fun l hl => mem_centralizer_singleton_iff.mp (hL₂'.1 hl)
  have hV := isSolvTwoCompSL23In_of_isSolvableTwoComponentIn hL₂' e
  rcases GH74.GLS.Balance.solvableL2PrimeBalance_proved ↥(centralizer ({z₁} : Set G))
      ⟨z₂, hz₂C⟩ hxo _ hV with h | ⟨K₀, hK₀, -, hK₀V⟩
  ·
    exfalso
    have ht2 : orderOf (QuotientGroup.mk (⟨z₂, hz₂C⟩ : ↥(centralizer ({z₁} : Set G))) :
        MBar z₁) = 2 := by
      refine orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hx2, QuotientGroup.mk_one]) ?_
      intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      have h2 := eq_one_of_mem_pPrimeCore h1 (n := 1) (by rw [pow_one]; exact hx2)
      rw [h2, orderOf_one] at hxo
      exact absurd hxo (by norm_num)
    have hle : GH74.GLS.oPrimeResidualOf 2 (hatIn z₁ L₂) ≤ pCore 2 (MBar z₁) := by
      refine (oPrimeResidualOf_map_le
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z₁} : Set G))))
        (L₂.subgroupOf (centralizer {z₁}))).trans ?_
      rintro _ ⟨y, hy, rfl⟩
      exact h hy
    have hsn := isSubnormal_of_oPrimeResidualOf_le_pCore ht2
      (F3L226.isSolvableTwoComponentIn_hatIn hz₂ hz₂C hL₂) (mk_mem_hatIn hz₂L hz₂C)
      (F3L226.isSolvableTwoComponentIn_hatIn hz₂ hz₂C hL₁) hle
    exact hns (isSubnormal_of_hatIn (hL₁.1.trans inf_le_left)
      (Subgroup.IsSubnormal.trans (F3L226.hatIn_mono (map_subtype_le _))
        (hatIn_oPrimeResidualOf_normal z₁ L₁).isSubnormal hsn))
  ·
    have hK : IsTwoComponentIn (K₀.map (centralizer ({z₁} : Set G)).subtype) (centralizer {z₁}) :=
      T23.isTwoComponentIn_map_subtype ((isTwoComponent_iff_isPComponent K₀).mpr hK₀)
    have hL₂K : GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K₀.map (centralizer ({z₁} : Set G)).subtype :=
      (oPrimeResidualOf_le_map_subgroupOf hL₂C).trans (map_mono hK₀V)
    have hz₂K : z₂ ∈ K₀.map (centralizer ({z₁} : Set G)).subtype :=
      hL₂K (mem_oPrimeResidualOf_of_pow (x := ⟨z₂, hz₂L⟩) (m := 1)
        (Subtype.ext (by simpa using hz2)))
    obtain ⟨hnorm, hcomm, hnc⟩ := lemma226_of_twoComponent hz₂ hc hL₁ hns hK hz₂K
    exact ⟨_, hK, hL₂K, hnorm, hcomm, hz₂K, hnc⟩

end F3L226S

theorem harris82Lemma226ThreeSolvable_holds : Harris82Lemma226ThreeSolvable := by
  intro G _ _ z₁ z₂ _ hz₂ _ hc L₁ L₂ hL₁ hL₂ hz₂L hns
  exact F3L226S.lemma226_solvable hz₂ hc hL₁ hL₂ hz₂L hns

end CFSG.ComponentClassification.HarrisLit.T1
