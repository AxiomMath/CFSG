module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Growth
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_normalizer_of_conj_le [Finite G] {S : Subgroup G} {e : G}
    (h : ∀ s ∈ S, e * s * e⁻¹ ∈ S) : e ∈ normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using h s hs
  · rw [Subgroup.card_map_of_injective (MulAut.conj e).injective]

theorem sec5_fusion_central [Finite G] {t z : G} {S : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (ht2 : orderOf t = 2) (hz2 : orderOf z = 2)
    (hΩ : omega1 (centerIn S) = zpowers t ⊔ zpowers z)
    (hnt : ∀ g : G, g⁻¹ * z * g ≠ t) (hconj : ∃ h : G, h⁻¹ * z * h = t * z) :
    ∃ d ∈ centralizer ({t} : Set G), d⁻¹ * z * d = t * z := by
  have hSG : IsSylow2Of S ⊤ := sec5_isSylow2Of_top hS ht2 hz2 hΩ hnt hconj
  have htC : t ∈ centerIn S := by
    rw [sec5_mem_centerIn_iff]
    exact ⟨sec4_t_mem_S hS ht2,
      fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hS.1 hy)).symm⟩
  have hzω : z ∈ omega1 (centerIn S) := by
    rw [hΩ]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzC : z ∈ centerIn S :=
    (show omega1 (centerIn S) ≤ centerIn S from
      (Subgroup.closure_le (K := centerIn S)).mpr fun _ hx => hx.1) hzω
  have htz : t * z = z * t :=
    ((sec5_mem_centerIn_iff.mp hzC).2 t ((sec5_mem_centerIn_iff.mp htC).1)).symm
  obtain ⟨h, hh⟩ := hconj
  let Hc : Subgroup G := centralizer ({t * z} : Set G)
  have hSle : S ≤ Hc := by
    intro s hs
    show s ∈ centralizer ({t * z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hts : t * s = s * t := (sec5_mem_centerIn_iff.mp htC).2 s hs
    have hzs : z * s = s * z := (sec5_mem_centerIn_iff.mp hzC).2 s hs
    calc s * (t * z) = (s * t) * z := by group
      _ = (t * s) * z := by rw [← hts]
      _ = t * (s * z) := by group
      _ = t * (z * s) := by rw [← hzs]
      _ = (t * z) * s := by group
  have hSyl : IsSylow2Of S Hc := by
    refine ⟨hSle, hSG.2.1, ?_⟩
    intro h2
    have hdiv : S.relIndex Hc ∣ S.index := Subgroup.relIndex_dvd_index_of_le hSle
    have hodd : ¬ 2 ∣ S.index := by
      rw [← Subgroup.relIndex_top_right (H := S)]
      exact hSG.2.2
    exact hodd (h2.trans hdiv)
  let K : Subgroup G := CFSG.conjugate S h
  have hKp : IsPGroup 2 K := by
    change IsPGroup 2 (S.map (MulAut.conj h⁻¹).toMonoidHom)
    exact hSG.2.1.map _
  have hKle : K ≤ Hc := by
    intro x hx
    show x ∈ centralizer ({t * z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    change x ∈ CFSG.conjugate S h at hx
    rw [mem_conjugate_iff] at hx
    have hcomm : z * (h * x * h⁻¹) = (h * x * h⁻¹) * z :=
      (sec5_mem_centerIn_iff.mp hzC).2 _ hx
    rw [← hh]
    calc x * (h⁻¹ * z * h) = h⁻¹ * ((h * x * h⁻¹) * z) * h := by group
      _ = h⁻¹ * (z * (h * x * h⁻¹)) * h := by rw [← hcomm]
      _ = (h⁻¹ * z * h) * x := by group
  obtain ⟨c, hcHc, hcK⟩ := exists_conj_le_of_isSylow2Of hSyl hKp hKle
  let e : G := c * h⁻¹
  have he : ∀ s ∈ S, e * s * e⁻¹ ∈ S := by
    intro s hs
    have hk : h⁻¹ * s * h ∈ K := by
      change h⁻¹ * s * h ∈ CFSG.conjugate S h
      rw [mem_conjugate_iff]
      have heq : h * (h⁻¹ * s * h) * h⁻¹ = s := by group
      rwa [heq]
    have hcs := hcK (h⁻¹ * s * h) hk
    have heq : e * s * e⁻¹ = c * (h⁻¹ * s * h) * c⁻¹ := by simp only [e]; group
    rw [heq]
    exact hcs
  have he_norm : e ∈ normalizer (S : Set G) := mem_normalizer_of_conj_le he
  let d : G := e⁻¹
  have hd_norm : d ∈ normalizer (S : Set G) := by
    rw [show d = e⁻¹ from rfl]
    exact (normalizer (S : Set G)).inv_mem he_norm
  have hd_z : d⁻¹ * z * d = t * z := by
    rw [show d = e⁻¹ from rfl, inv_inv]
    have hcz : c * (t * z) = (t * z) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hcHc
    calc e * z * e⁻¹ = c * (h⁻¹ * z * h) * c⁻¹ := by simp only [e]; group
      _ = c * (t * z) * c⁻¹ := by rw [hh]
      _ = t * z := by rw [hcz]; group
  have ht22 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hu_omega : d⁻¹ * t * d ∈ omega1 (centerIn S) :=
    sec5_conj_mem_omega1 hd_norm htC ht22
  have hu_mem : d⁻¹ * t * d ∈ zpowers t ⊔ zpowers z := by
    rw [← hΩ]
    exact hu_omega
  have hu_ord : orderOf (d⁻¹ * t * d) = 2 := by rw [orderOf_conjugate_eq, ht2]
  rcases sec5_klein_involutions ht2 hz2 htz hu_mem hu_ord with h | h | h
  · refine ⟨d, ?_, hd_z⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htt : t * d = d * t := by
      calc t * d = d * (d⁻¹ * t * d) := by group
        _ = d * t := by rw [h]
    exact htt.symm
  · exfalso
    have hzd : d * z * d⁻¹ = t := by
      calc d * z * d⁻¹ = d * (d⁻¹ * t * d) * d⁻¹ := by rw [h]
        _ = t := by group
    exact hnt d⁻¹ (by simpa using hzd)
  · exfalso
    have htz_eq : t = z := by
      calc t = d * (d⁻¹ * t * d) * d⁻¹ := by group
        _ = d * (d⁻¹ * z * d) * d⁻¹ := by rw [h, hd_z]
        _ = z := by group
    exact hnt 1 (by simpa using htz_eq.symm)

theorem sec5_tz_not_conj_z [Finite G] (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5) {t : G} {L S : Subgroup G}
    {z : G} (h : Sec5Ctx G t L S z) : ∀ g : G, g⁻¹ * z * g ≠ t * z := by
  intro g hg
  have hΩ : omega1 (centerIn S) = zpowers t ⊔ zpowers z := h53 G t L S z h
  have hnt : ∀ g : G, g⁻¹ * z * g ≠ t := sec5_t_not_conj_z h37 h
  obtain ⟨d, hdC, hdz⟩ :=
    sec5_fusion_central h.sylow h.involution h.pocket.1 hΩ hnt ⟨g, hg⟩
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  have hdL : d ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 h.toSec3SettingLB d hdC
  have hdLinv : d⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem hdL
  have hpock : IsI4PlusIn L (t * z) := by
    have h1 := sec5_isI4PlusIn_conj h.pocket (c := d⁻¹) hdLinv
    rwa [inv_inv, hdz] at h1
  exact tab.tz_not_pocket G L h.toSec5Setting.isOm6Z2 t htZ h.involution z h.pocket hpock

end CFSG.OddStandard.SmallF3.Omega
