module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5ZClaim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510T

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {Q₁ Q₂ : Subgroup G}

theorem sec5z_conj_cent_le_centralizer (hy : Sec5B59Hyp) (h55 : Asc82Lemma55)
    (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6)
    (h : Sec5Ctx G t L S z) (hnc : ¬ ∃ g : G, g⁻¹ * t * g = t * z) (hQ : Sec510Q G L z Q₁ Q₂)
    {y : G} (hyH : y ∈ conjClassIn (centralizer ({z} : Set G)) t) (hyc : y * t = t * y) :
    y ∈ centralizer ((Q₁ ⊔ Q₂ : Subgroup G) : Set G) := by
  by_cases hyt : y = t
  · rw [hyt]
    exact (sec5p510_t_mem_R h hQ).2
  by_contra hyQ
  obtain ⟨k, hk, hyk⟩ := hyH
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hk
  have htz : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 h.mem_S)).symm
  have hz' : k * z * k⁻¹ = z := by
    rw [hkz]
    group
  have hz'' : k⁻¹ * z * k = z := by
    calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
      _ = k⁻¹ * (k * z) := by rw [hkz]
      _ = z := by group
  have hyz : y * z = z * y := by
    calc y * z = (k * t * k⁻¹) * (k * z * k⁻¹) := by rw [hyk, hz']
      _ = k * (t * z) * k⁻¹ := by group
      _ = k * (z * t) * k⁻¹ := by rw [htz]
      _ = (k * z * k⁻¹) * (k * t * k⁻¹) := by group
      _ = z * y := by rw [hz', hyk]
  obtain ⟨g₀, hg₀⟩ := sec5z_claimZ hy h55 h58d hFB h4 h hnc hQ ⟨k⁻¹, by rw [hyk]; group⟩ hyt hyc
    hyz hyQ
  refine sec5_tz_not_conj_z hy.h36 hy.h37 hy.h52b hy.h53 hy.tab h (g₀ * k) ?_
  calc (g₀ * k)⁻¹ * z * (g₀ * k) = k⁻¹ * (g₀⁻¹ * z * g₀) * k := by group
    _ = k⁻¹ * (y * z) * k := by rw [hg₀]
    _ = k⁻¹ * (k * t * k⁻¹ * z) * k := by rw [hyk]
    _ = t * (k⁻¹ * z * k) := by group
    _ = t * z := by rw [hz'']

theorem sec5z_conj_inter_S_le_R (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6) (h : Sec5Ctx G t L S z)
    (hnc : ¬ ∃ g : G, g⁻¹ * t * g = t * z) (hQ : Sec510Q G L z Q₁ Q₂) {y : G}
    (hyH : y ∈ conjClassIn (centralizer ({z} : Set G)) t) (hyS : y ∈ S) :
    y ∈ sec5p510_R S Q₁ Q₂ :=
  ⟨hyS, sec5z_conj_cent_le_centralizer hy h55 h58d hFB h4 h hnc hQ hyH
    (Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hyS))⟩

theorem sec5z_conj_inter_S_le_T (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d)
    (hFB : Asc82Sec5FactB5z) (h4 : Asc82FactReflCentQ6) (h : Sec5Ctx G t L S z)
    (hnc : ¬ ∃ g : G, g⁻¹ * t * g = t * z) (hQ : Sec510Q G L z Q₁ Q₂) {y : G}
    (hyH : y ∈ conjClassIn (centralizer ({z} : Set G)) t) (hyS : y ∈ S) :
    y ∈ sec5p510_T t z (sec5p510_R S Q₁ Q₂) :=
  Subgroup.subset_closure
    ⟨hyH, sec5z_conj_inter_S_le_R hy h55 h58d hFB h4 h hnc hQ hyH hyS⟩

end CFSG.OddStandard.SmallF3.Omega
