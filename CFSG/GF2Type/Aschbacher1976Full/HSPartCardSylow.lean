module

import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Tools
public import CFSG.GF2Type.Aschbacher1976Full.WidthCore

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Card

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]

section Basic

variable {z : G} {w : ℕ} {Z A : Subgroup G}

theorem Fz_le_Hz (z : G) : Fz z ≤ Hz z := Subgroup.map_subtype_le _

theorem le_normalizer_Fz {K : Subgroup G} (hKH : K ≤ Hz z) :
    K ≤ normalizer (Fz z : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · exact fun hf => Width.Fz_conj_mem (hKH ht) hf
  · intro hf
    have h := Width.Fz_conj_mem ((Hz z).inv_mem (hKH ht)) hf
    have e : t⁻¹ * (t * f * t⁻¹) * t⁻¹⁻¹ = f := by group
    rwa [e] at h

theorem mem_Z_of_central (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) {T : Subgroup G} (hFT : Fz z ≤ T) (hTH : T ≤ Hz z) {x : G}
    (hxT : x ∈ T) (hc : ∀ t ∈ T, x * t = t * x) : x ∈ Z := by
  have hxF : x ∈ Fz z := by
    rw [← Width.coreAt_eq_Fz hF2]
    exact Width.selfCent_F hF2 x (hTH hxT) fun q hq =>
      hc q (hFT (by rwa [Width.coreAt_eq_Fz hF2] at hq))
  exact Width.mem_Z_of_comm hD hz hxF fun b hb =>
    hc b (hFT (hD.sup_eq ▸ Subgroup.mem_sup_right hb))

theorem normalizer_le_Hz (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) {T : Subgroup G} (hFT : Fz z ≤ T) (hTH : T ≤ Hz z) :
    normalizer (T : Set G) ≤ Hz z := by
  intro n hn
  have hzT : z ∈ T := hFT (by rw [← hD.sup_eq]; exact Subgroup.mem_sup_left hD.mem_z)
  have hnT : ∀ t, t ∈ T ↔ n * t * n⁻¹ ∈ T := Subgroup.mem_normalizer_iff.mp hn
  have hninv : ∀ t, t ∈ T ↔ n⁻¹ * t * n ∈ T := fun t => by
    have h := Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem hn) t
    rwa [inv_inv] at h
  have hxT : n * z * n⁻¹ ∈ T := (hnT z).mp hzT
  have hxcomm : ∀ t ∈ T, (n * z * n⁻¹) * t = t * (n * z * n⁻¹) := by
    intro t ht
    have h1 : z * (n⁻¹ * t * n) = (n⁻¹ * t * n) * z :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hTH ((hninv t).mp ht))).symm
    calc n * z * n⁻¹ * t = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by rw [h1]
      _ = t * (n * z * n⁻¹) := by group
  have hxZ : n * z * n⁻¹ ∈ Z := mem_Z_of_central hD hz hF2 hFT hTH hxT hxcomm
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hsq : (n * z * n⁻¹) ^ 2 = 1 := by
    rw [conj_pow, Width.z_sq hz, mul_one, mul_inv_cancel]
  have hne : n * z * n⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hfix : n * z * n⁻¹ = z := Width.involution_eq hD hz hxZ hsq hne
  exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)

theorem exists_sylow (hD : Width.Z4Data z w Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    {K : Subgroup G} (hFK : Fz z ≤ K) (hKH : K ≤ Hz z) (hK2 : IsPGroup 2 K) :
    ∃ T : Sylow 2 G, K ≤ (T : Subgroup G) ∧ (T : Subgroup G) ≤ Hz z := by
  obtain ⟨T, hKT, hT⟩ := Set.Finite.exists_le_maximal
    (s := {Q : Subgroup G | IsPGroup 2 Q ∧ K ≤ Q ∧ Q ≤ Hz z}) (Set.toFinite _)
    ⟨hK2, le_rfl, hKH⟩
  obtain ⟨hT2, -, hTH⟩ := hT.1
  have hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → T ≤ Q → Q ≤ Hz z → Q = T :=
    fun Q hQ hTQ hQH => le_antisymm (hT.2 ⟨hQ, hKT.trans hTQ, hQH⟩ hTQ) hTQ
  obtain ⟨S, hS⟩ := CFSG.EvenSmallLie.OmegaEight.Child8.exists_sylow_eq_of_normalizer_le hT2 hmax
    (normalizer_le_Hz hD hz hF2 (hFK.trans hKT) hTH)
  exact ⟨S, by rw [hS]; exact hKT, by rw [hS]; exact hTH⟩

end Basic

end CFSG.GF2Type.Aschbacher1976Full.HS.Card
