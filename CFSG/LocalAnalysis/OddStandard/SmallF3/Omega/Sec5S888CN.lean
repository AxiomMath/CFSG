module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private lemma s888cn_iso_z_eq_neg_one {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {i : Fin 4} (e : ↥(K i) ≃* SL23) :
    e ⟨z, hq.z_mem i⟩ = -1 := by
  have hsq : e ⟨z, hq.z_mem i⟩ * e ⟨z, hq.z_mem i⟩ = 1 := by
    rw [← map_mul]
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) * ⟨z, hq.z_mem i⟩ = 1 :=
      Subtype.ext (by simpa using hq.z_sq)
    rw [hsub, map_one]
  rcases sl23_unique_involution _ hsq with h1 | hneg
  · exfalso
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := e.injective (by rw [h1, map_one])
    exact hq.z_ne (congrArg Subtype.val hsub)
  · exact hneg

private lemma s888cn_comm_mem_zpowers {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {i : Fin 4} {u v : G}
    (hu : u ∈ K i) (hu4 : u ^ 4 = 1) (hv : v ∈ K i) (hv4 : v ^ 4 = 1) :
    u * v * u⁻¹ * v⁻¹ ∈ zpowers z := by
  obtain ⟨e⟩ := hq.iso i
  have hzu : e ⟨z, hq.z_mem i⟩ = -1 := s888cn_iso_z_eq_neg_one hq e
  have hu4' : (e ⟨u, hu⟩) ^ 4 = 1 := by
    have hsub : (⟨u, hu⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hu4)
    rw [← map_pow, hsub, map_one]
  have hv4' : (e ⟨v, hv⟩) ^ 4 = 1 := by
    have hsub : (⟨v, hv⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hv4)
    rw [← map_pow, hsub, map_one]
  have hmap : e (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) =
      e ⟨u, hu⟩ * e ⟨v, hv⟩ * (e ⟨u, hu⟩)⁻¹ * (e ⟨v, hv⟩)⁻¹ := by
    simp only [map_mul, map_inv]
  rcases (sl23_q8_comm_sq (e ⟨u, hu⟩) (e ⟨v, hv⟩) hu4' hv4').1 with hc | hc
  · have hsub : (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ : ↥(K i)) = 1 := by
      apply e.injective
      rw [hmap, hc]
      exact (map_one e).symm
    have hG : u * v * u⁻¹ * v⁻¹ = 1 := by simpa using congrArg Subtype.val hsub
    rw [hG]
    exact (zpowers z).one_mem
  · have hsub : (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ : ↥(K i)) = ⟨z, hq.z_mem i⟩ := by
      apply e.injective
      rw [hmap, hc]
      exact hzu.symm
    have hG : u * v * u⁻¹ * v⁻¹ = z := by simpa using congrArg Subtype.val hsub
    rw [hG]
    exact Subgroup.mem_zpowers z

private lemma s888cn_prod_commutator {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {k l : Fin 4 → G}
    (hk : ∀ i, k i ∈ K i) (hl : ∀ i, l i ∈ K i) :
    Sec5B517Prod k * Sec5B517Prod l * (Sec5B517Prod k)⁻¹ * (Sec5B517Prod l)⁻¹ =
      Sec5B517Prod (fun i => k i * l i * (k i)⁻¹ * (l i)⁻¹) := by
  simp only [sec5b517_prod_inv hq hk, sec5b517_prod_inv hq hl,
    sec5b517_prod_mul hq hk hl,
    sec5b517_prod_mul hq (fun i => (K i).mul_mem (hk i) (hl i))
      (fun i => (K i).inv_mem (hk i)),
    sec5b517_prod_mul hq
      (fun i => (K i).mul_mem ((K i).mul_mem (hk i) (hl i)) ((K i).inv_mem (hk i)))
      (fun i => (K i).inv_mem (hl i))]

private lemma s888cn_conj_zpow {n z ζ : G} (hn : n ∈ centralizer ({z} : Set G))
    (hζ : ζ ∈ zpowers z) : n * ζ * n⁻¹ = ζ := by
  obtain ⟨k, hk⟩ := hζ
  rw [← hk]
  have hcz : Commute n z := Subgroup.mem_centralizer_singleton_iff.mp hn
  exact (hcz.zpow_right k).mul_inv_cancel

theorem centralizerMod_conj_mem (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {n x : G} (hn : n ∈ normalizer (Qsub K₁ K₂ h : Set G))
    (hx : x ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) :
    n * x * n⁻¹ ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) := by
  obtain ⟨hxN, hxz, hxE, hxc⟩ := hx
  have hnz : n ∈ centralizer ({z} : Set G) := sec5b517_normalizer_le h514 c hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (normalizer (Qsub K₁ K₂ h : Set G)).mul_mem
      ((normalizer (Qsub K₁ K₂ h : Set G)).mul_mem hn hxN)
      ((normalizer (Qsub K₁ K₂ h : Set G)).inv_mem hn)
  · exact (centralizer ({z} : Set G)).mul_mem
      ((centralizer ({z} : Set G)).mul_mem hnz hxz)
      ((centralizer ({z} : Set G)).inv_mem hnz)
  · exact (normalizer (Qsub K₁ K₂ h : Set G)).mul_mem
      ((normalizer (Qsub K₁ K₂ h : Set G)).mul_mem hn hxE)
      ((normalizer (Qsub K₁ K₂ h : Set G)).inv_mem hn)
  · intro q hq
    have hq' : n⁻¹ * q * n ∈ Qsub K₁ K₂ h := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) q).mp hq
      simpa using this
    have hkey : (n * x * n⁻¹) * q * (n * x * n⁻¹)⁻¹ * q⁻¹ =
        n * (x * (n⁻¹ * q * n) * x⁻¹ * (n⁻¹ * q * n)⁻¹) * n⁻¹ := by group
    rw [hkey, s888cn_conj_zpow hnz (hxc (n⁻¹ * q * n) hq')]
    exact hxc (n⁻¹ * q * n) hq'

theorem qsub_le_centralizerMod (h514 : Asc82Lemma514) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Qsub K₁ K₂ h ≤
      centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) := by
  intro q hq
  have hquad := sec5b517_quad h514 c
  have hqQ8 : q ∈ Sec5B517Q8 hquad := by
    rwa [sec5b517_Qsub_eq, hquad.core_eq] at hq
  refine ⟨Subgroup.le_normalizer hq, ?_, Subgroup.le_normalizer hq, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hquad.z_comm_all (Sec5B517Q8.le_all hquad hqQ8)).symm
  · intro q' hq'
    have hq'Q8 : q' ∈ Sec5B517Q8 hquad := by
      rwa [sec5b517_Qsub_eq, hquad.core_eq] at hq'
    obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hquad).mp hqQ8
    obtain ⟨l, hl, rfl⟩ := (Sec5B517Q8.mem_iff hquad).mp hq'Q8
    rw [s888cn_prod_commutator hquad (fun i => (hk i).1) (fun i => (hl i).1)]
    simp only [Sec5B517Prod]
    exact (zpowers z).mul_mem ((zpowers z).mul_mem ((zpowers z).mul_mem
      (s888cn_comm_mem_zpowers hquad (hk 0).1 (hk 0).2 (hl 0).1 (hl 0).2)
      (s888cn_comm_mem_zpowers hquad (hk 1).1 (hk 1).2 (hl 1).1 (hl 1).2))
      (s888cn_comm_mem_zpowers hquad (hk 2).1 (hk 2).2 (hl 2).1 (hl 2).2))
      (s888cn_comm_mem_zpowers hquad (hk 3).1 (hk 3).2 (hl 3).1 (hl 3).2)

end CFSG.OddStandard.SmallF3.Omega
