module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4F_no_twoU43_cent [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) {s : G}
    (hs6 : InducesTypeSome L s 7 1 6 1) {K : Subgroup G} (hK : IsQuasisimple K) (hKL : K ≤ L)
    (hKs : K ≤ centralizer ({s} : Set G)) (hK43 : IsTwoU43 (K ⧸ oddCore K)) : False := by
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨y, hy, hty⟩ :=
    (sec4I_inducesTypeSome_iff e (Or.inr (Or.inr rfl))).mp hs6
  have hycard : Nat.card (Subgroup.centralizer ({y} : Set (ProjOrth Sec4IQ))) = 24261120 :=
    natCard_centralizer_hasType_six_plus_seven sec4IQ_nondegenerate sec4IQ_finrank hty
  let ρ : ↥L →* ProjOrth Sec4IQ := Sec4IOmega.subtype.comp (sec4ICover e)
  let f : ↥K →* ProjOrth Sec4IQ := ρ.comp (Subgroup.inclusion hKL)
  have hf_apply : ∀ k : ↥K, f k =
      ((e (QuotientGroup.mk (Subgroup.inclusion hKL k)) : Sec4IOmega) :
        ProjOrth Sec4IQ) := by
    intro k
    rfl
  have hfmem : ∀ k : ↥K, f k ∈ Subgroup.centralizer ({y} : Set (ProjOrth Sec4IQ)) := by
    intro k
    have hcomm : ((Subgroup.inclusion hKL k : ↥L) : G) * s =
        s * ((Subgroup.inclusion hKL k : ↥L) : G) := by
      simpa using Subgroup.mem_centralizer_singleton_iff.mp (hKs k.2)
    have hl : ((Subgroup.inclusion hKL k : ↥L) : G) =
        s * (Subgroup.inclusion hKL k : ↥L) * s⁻¹ := by
      rw [← hcomm]
      group
    have h2 := hy.2 (Subgroup.inclusion hKL k) (Subgroup.inclusion hKL k) hl
    have h2' : f k = y * f k * y⁻¹ := by
      rw [hf_apply k]
      exact h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    nth_rewrite 1 [h2']
    group
  let C : Subgroup (ProjOrth Sec4IQ) := Subgroup.centralizer ({y} : Set (ProjOrth Sec4IQ))
  let ρ' : ↥K →* ↥C := f.codRestrict C hfmem
  have hker_le : ρ'.ker ≤ Subgroup.center ↥K := by
    intro k hk
    have hk1 : f k = 1 := by
      have h' : ((ρ' k : ↥C) : ProjOrth Sec4IQ) = 1 := by
        rw [MonoidHom.mem_ker.mp hk]
        rfl
      simpa [ρ', MonoidHom.codRestrict_apply] using h'
    have hk1' : sec4ICover e (Subgroup.inclusion hKL k) = 1 := by
      apply Subtype.ext
      simpa [f, ρ, MonoidHom.comp_apply] using hk1
    have hkker : (Subgroup.inclusion hKL k) ∈ (sec4ICover e).ker :=
      MonoidHom.mem_ker.mpr hk1'
    have hcz : (Subgroup.inclusion hKL k) ∈ Subgroup.center ↥L :=
      (sec4ICover_odd hL e).ker_le_center hkker
    rw [Subgroup.mem_center_iff]
    intro k'
    rw [← Subgroup.inclusion_inj (h := hKL)]
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hcz (Subgroup.inclusion hKL k')
  have hdvd1 : Nat.card (↥K ⧸ Subgroup.center ↥K) ∣ Nat.card (↥K ⧸ ρ'.ker) := by
    simpa only [Subgroup.index_eq_card] using Subgroup.index_dvd_of_le hker_le
  have hiso : Nat.card (↥K ⧸ ρ'.ker) = Nat.card ρ'.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv
  have hdvd2 : Nat.card (↥K ⧸ ρ'.ker) ∣ Nat.card C := by
    rw [hiso]
    exact Subgroup.card_subgroup_dvd_card ρ'.range
  have hdvd : ctrQ K ∣ Nat.card (Subgroup.centralizer ({y} : Set (ProjOrth Sec4IQ))) := by
    unfold ctrQ
    exact hdvd1.trans hdvd2
  rw [ctrQ_of_twoU43 hK hK43, hycard] at hdvd
  exact absurd hdvd (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
