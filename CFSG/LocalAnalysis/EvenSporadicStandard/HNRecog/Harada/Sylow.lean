module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.E64Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Rigid
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}

private theorem coordElt_injective {G : Type} [Group G] {ι : Elem2 6 →* G}
    (hι : Function.Injective ι) : Function.Injective (coordElt ι) := by
  intro u v huv
  have h : Multiplicative.ofAdd u = Multiplicative.ofAdd v := hι huv
  simpa using congrArg Multiplicative.toAdd h

theorem harada_prop_2_1 [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hD : HData G t z b z₁ S Eg T T' W0 ι) : 2 ∣ S.index := by
  by_contra hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ∀ n ∈ normalizer (S : Set G), n * t * n⁻¹ = t :=
    fun n hn => HarCoreData.normalizer_fixes_t hD.core hD.z_sq hidx hn
  have hinv : ∀ u ∈ Eg, u ^ 2 = 1 → u ≠ 1 → u ≠ t →
      ∃ e : G, e * u * e⁻¹ = z ∨ e * u * e⁻¹ = t * z := by
    intro u hu hu2 hu1 hut
    obtain ⟨h, _, hh⟩ := hD.inv_E u hu hu2 hu1 hut
    exact ⟨h, hh⟩
  have hP : (IsPGroup.toSylow hD.isPGroup_S hidx : Subgroup G) = S :=
    IsPGroup.toSylow_coe hD.isPGroup_S hidx
  have hfus : ∀ g : G, g⁻¹ * t * g ∈ Eg → g⁻¹ * t * g = t :=
    harCore_S' hD.core (IsPGroup.toSylow hD.isPGroup_S hidx) hP hN hinv
  obtain ⟨g₀, hg₀ne, hg₀comm⟩ := exists_fused_commuting_involution hnonab hD.orderOf_t
  let p : G := g₀ * t * g₀⁻¹
  have hp_ne_t : p ≠ t := hg₀ne
  have hp_comm : p * t = t * p := hg₀comm
  have hp_cent : p ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact hp_comm
  have hp2 : p ^ 2 = 1 := by
    dsimp only [p]
    rw [conj_pow, hD.t_sq]
    group
  have hp_conj : IsConj t p := isConj_iff.mpr ⟨g₀, rfl⟩
  have hp_not_Eg : p ∉ Eg := by
    intro hpE
    have hmem : (g₀⁻¹)⁻¹ * t * g₀⁻¹ ∈ Eg := by simpa [p] using hpE
    have h := hfus g₀⁻¹ hmem
    rw [inv_inv] at h
    exact hp_ne_t h
  obtain ⟨h, _hh_cent, hhq⟩ := hD.inv_outer p hp_cent hp2 hp_not_Eg
  have hq_data : ∃ q : G, (q = b ∨ q = z₁) ∧ IsConj t q := by
    rcases hhq with hb | hz
    · exact ⟨b, Or.inl rfl, hp_conj.trans (isConj_iff.mpr ⟨h, hb⟩)⟩
    · exact ⟨z₁, Or.inr rfl, hp_conj.trans (isConj_iff.mpr ⟨h, hz⟩)⟩
  obtain ⟨q, hq_bz, hq_conj⟩ := hq_data
  have hw_data : ∃ w : V6, lam w = 1 ∧ coordElt ι w = q := by
    rcases hq_bz with rfl | rfl
    · obtain ⟨v, hv, hl, _⟩ := hD.coords_b
      exact ⟨v, hl, hv⟩
    · obtain ⟨v, hv, hl, _⟩ := hD.coords_z₁
      exact ⟨v, hl, hv⟩
  obtain ⟨w, hw_lam, hw_q⟩ := hw_data
  have hq_A : q ∈ ι.range :=
    MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd w, by rw [← hw_q]; rfl⟩
  have hq_conj' : IsConj t (coordElt ι w) := by rw [hw_q]; exact hq_conj
  have hex : ∃ v : V6, lam v = 1 ∧ IsConj t (coordElt ι v) := ⟨w, hw_lam, hq_conj'⟩
  have hker : ∀ v : V6, lam v = 0 → IsConj t (coordElt ι v) → v = tv := by
    intro v hl hv
    have hvEg : coordElt ι v ∈ Eg := (hD.mem_E_iff v).mpr hl
    obtain ⟨c, hc⟩ := isConj_iff.mp hv
    have hmem : (c⁻¹)⁻¹ * t * c⁻¹ ∈ Eg := by rw [inv_inv, hc]; exact hvEg
    have h1 := hfus c⁻¹ hmem
    rw [inv_inv, hc] at h1
    have h2 : coordElt ι v = coordElt ι tv := by rw [h1, hD.ι_tv]
    exact coordElt_injective hD.injective_ι h2
  obtain ⟨n, hn, hnq⟩ := hD.exists_normalizer_conj_t hq_A hq_conj
  obtain ⟨σ, hσ_add, hσ⟩ := exists_perm_of_mem_normalizer hD.injective_ι hn
  have hconj : ∀ x : V6, IsConj t (coordElt ι (σ x)) ↔ IsConj t (coordElt ι x) := by
    intro x
    rw [← hσ x]
    exact isConj_conj_iff t (coordElt ι x) n
  have hfix : σ tv = tv := by
    rcases hD.X_cases_prop21 hker hex with hY | hY | hY
    · exact rigid_Yv2 σ hσ_add (fun x => (hY (σ x)).symm.trans ((hconj x).trans (hY x)))
    · exact rigid_Yv1 σ hσ_add (fun x => (hY (σ x)).symm.trans ((hconj x).trans (hY x)))
    · exact rigid_Yv12 σ hσ_add (fun x => (hY (σ x)).symm.trans ((hconj x).trans (hY x)))
  have hq_t : q = t := by
    calc q = n * t * n⁻¹ := hnq.symm
      _ = n * coordElt ι tv * n⁻¹ := by rw [hD.ι_tv]
      _ = coordElt ι (σ tv) := hσ tv
      _ = coordElt ι tv := by rw [hfix]
      _ = t := hD.ι_tv
  have hwt : coordElt ι w = t := by rw [hw_q, hq_t]
  have hw_tv : w = tv := coordElt_injective hD.injective_ι (by rw [hwt, hD.ι_tv])
  have hlam0 : lam w = 0 := by rw [hw_tv]; simp [lam, tv]
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (hw_lam.symm.trans hlam0)

end CFSG.EvenSporadicStandard.HNRecog.Harada
