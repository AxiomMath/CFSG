module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem not_two_dvd_index_of_fusion {Rs : Subgroup G} {z : G} (hR : IsPGroup 2 Rs) (hzR : z ∈ Rs)
    (hfus : ∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹)
    (hcent : ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G))) : ¬ 2 ∣ Rs.index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hR.exists_le_sylow
  have hEq : Rs = (P : Subgroup G) := by
    by_contra hne
    have hlt : Rs < (P : Subgroup G) := lt_of_le_of_ne hP hne
    have : Group.IsNilpotent (↥(P : Subgroup G)) := P.isPGroup'.isNilpotent
    have hproper : Rs.subgroupOf (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm hP (fun x hx => ?_)
      have : (⟨x, hx⟩ : ↥(P : Subgroup G)) ∈ Rs.subgroupOf (P : Subgroup G) := htop ▸ mem_top _
      exact this
    obtain ⟨n, hnN, hn⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G)) _ hproper)
    have hnG : ((n : ↥(P : Subgroup G)) : G) ∉ Rs := hn
    have hnorm : ∀ r ∈ Rs, (n : G) * r * (n : G)⁻¹ ∈ Rs := by
      intro r hr
      have := (Subgroup.mem_normalizer_iff.1 hnN ⟨r, hP hr⟩).1 (by exact hr)
      exact this
    obtain ⟨r, hrR, hr⟩ := hfus (n : G) (hnorm z hzR)
    set c : G := r⁻¹ * (n : G) with hc
    have hcP : c ∈ (P : Subgroup G) := mul_mem (inv_mem (hP hrR)) n.2
    have hcz : c ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * z = r⁻¹ * ((n : G) * z * (n : G)⁻¹) * (n : G) := by rw [hc]; group
        _ = r⁻¹ * (r * z * r⁻¹) * (n : G) := by rw [hr]
        _ = z * c := by rw [hc]; group
    have hCR : IsPGroup 2 (Rs.subgroupOf (centralizer ({z} : Set G))) := hR.comap_subtype
    let Sz : Sylow 2 ↥(centralizer ({z} : Set G)) := hCR.toSylow hcent
    have hCP : IsPGroup 2 ((P : Subgroup G).subgroupOf (centralizer ({z} : Set G))) :=
      P.isPGroup'.comap_subtype
    have hle : (Rs.subgroupOf (centralizer ({z} : Set G))) ≤
        (P : Subgroup G).subgroupOf (centralizer ({z} : Set G)) := fun x hx => hP hx
    have heq := Sz.is_maximal' hCP hle
    have hcR : c ∈ Rs := by
      have : (⟨c, hcz⟩ : ↥(centralizer ({z} : Set G))) ∈
          (P : Subgroup G).subgroupOf (centralizer ({z} : Set G)) := hcP
      rw [heq] at this
      exact this
    apply hnG
    have : (n : G) = r * c := by rw [hc]; group
    rw [this]
    exact mul_mem hrR hcR
  rw [hEq]
  exact P.not_dvd_index

theorem false_of_fusion_pair [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz2 : orderOf z = 2) {Rs R : Subgroup G} (hRs : IsPGroup 2 Rs) (hRR : R ≤ Rs)
    (hidx : R.relIndex Rs = 2) (hzRs : z ∈ Rs) (hzR : z ∉ R)
    (hfus : ∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹)
    (hcent : ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G))) : False := by
  have hSidx : ¬ 2 ∣ Rs.index := not_two_dvd_index_of_fusion hRs hzRs hfus hcent
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.exists_conj_mem_complement hnonab hRs hSidx hRR
    hidx hzRs hzR hz2
  have hgR : g⁻¹ * z * g⁻¹⁻¹ ∈ R := by simpa using hg
  obtain ⟨r, hrRs, hr⟩ := hfus g⁻¹ (hRR hgR)
  have hnorm : (R.subgroupOf Rs).Normal := Subgroup.normal_of_index_eq_two hidx
  have hmem : (⟨r * z * r⁻¹, mul_mem (mul_mem hrRs hzRs) (inv_mem hrRs)⟩ : ↥Rs) ∈
      R.subgroupOf Rs := by
    show r * z * r⁻¹ ∈ R
    rw [← hr]
    exact hgR
  have := hnorm.conj_mem _ hmem ⟨r⁻¹, inv_mem hrRs⟩
  apply hzR
  have h2 : r⁻¹ * (r * z * r⁻¹) * r⁻¹⁻¹ ∈ R := this
  simpa [mul_assoc] using h2

end CFSG.EvenSporadicStandard.Fin76b
