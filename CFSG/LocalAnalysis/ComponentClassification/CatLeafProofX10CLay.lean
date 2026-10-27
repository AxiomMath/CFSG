module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CBal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10A
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Lemma29
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CatLeafProof

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

omit [Finite H] in
theorem map_conj_centralizer_singleton' (g x : H) :
    (centralizer ({x} : Set H)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set H) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hw
    rw [mem_centralizer_singleton_iff]
    change g * w * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * w * g⁻¹)
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hw]
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by change g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
    rw [mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group

omit [Finite H] in
theorem centralizer_mk_eq {F : Subgroup H} {s : H} (hs : s ∈ F) :
    centralizer ({(⟨s, hs⟩ : F)} : Set F) = (centralizer ({s} : Set H)).subgroupOf F := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h2 => congrArg Subtype.val h2, fun h2 => Subtype.ext h2⟩

theorem asigma_comm_az : h.a * d.sigma * (h.a * d.z) = h.a * d.z * (h.a * d.sigma) := by
  have haσ : d.sigma * h.a = h.a * d.sigma := h.toHyp52.comm_a d.sigma_mem_S
  have hzσ : d.sigma * d.z = d.z * d.sigma := mem_centralizer_iff.mp d.z_S d.sigma d.sigma_mem_S
  have hza : d.z * h.a = h.a * d.z := d.z_comm_a
  calc h.a * d.sigma * (h.a * d.z) = h.a * (d.sigma * h.a) * d.z := by group
    _ = h.a * (h.a * d.sigma) * d.z := by rw [haσ]
    _ = h.a * h.a * (d.sigma * d.z) := by group
    _ = h.a * h.a * (d.z * d.sigma) := by rw [hzσ]
    _ = h.a * (h.a * d.z) * d.sigma := by group
    _ = h.a * (d.z * h.a) * d.sigma := by rw [hza]
    _ = h.a * d.z * (h.a * d.sigma) := by group

theorem asigma_involution : h.a * d.sigma * (h.a * d.sigma) = 1 := by
  have haσ : d.sigma * h.a = h.a * d.sigma := h.toHyp52.comm_a d.sigma_mem_S
  calc h.a * d.sigma * (h.a * d.sigma) = h.a * (d.sigma * h.a) * d.sigma := by group
    _ = h.a * (h.a * d.sigma) * d.sigma := by rw [haσ]
    _ = (h.a * h.a) * (d.sigma * d.sigma) := by group
    _ = 1 := by rw [Six.a_mul_a_self h.toHyp52, d.sigma_mul_self, one_mul]

theorem isPComponent_L :
    conjugate h.K (h.x * d.g) ≤ centralizer ({h.a * d.sigma} : Set H) ∧
      IsPComponent 2 ((conjugate h.K (h.x * d.g)).subgroupOf
        (centralizer ({h.a * d.sigma} : Set H))) := by
  set c := h.x * d.g with hc
  have hNB : normalizer (h.B : Set H) = centralizer ({d.b} : Set H) := by
    rw [d.B_eq]
    exact Sol78.normalizer_zpowers_eq_centralizer_of_orderOf_eq_two d.b_ord
  obtain ⟨hKN, hK⟩ := h.isPComponent_K
  rw [hNB] at hKN hK
  have h1 := X10.isPComponent_map_injective (MulAut.conj c⁻¹).toMonoidHom
    (MulAut.conj c⁻¹).injective hKN hK
  have h2 : (centralizer ({d.b} : Set H)).map (MulAut.conj c⁻¹).toMonoidHom =
      centralizer ({h.a * d.sigma} : Set H) := by
    rw [map_conj_centralizer_singleton', inv_inv, d.conj_b]
  rw [h2] at h1
  refine ⟨?_, h1⟩
  rw [conjugate, ← h2]
  exact map_mono hKN

theorem isKGroupCat_F : SectionRank.IsKGroupCat ↥(centralizer ({h.a * d.z} : Set H)) := by
  have haa := Six.a_mul_a_self h.toHyp52
  have haz1 : h.a * d.z ≠ 1 := by
    intro h1
    apply d.z_ne_a
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right haa]
  rcases H₁.kOrSimple with hKG | hs
  · exact hKG.subgroup _
  · refine isKGroupCat_of_ne_top' h.toHyp52.kProper fun htop => ?_
    obtain ⟨u, w, huw⟩ := h.exists_ne_commute_generalizedFitting
    have hZ : (h.a * d.z) ∈ center H := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ centralizer ({h.a * d.z} : Set H) := by rw [htop]; exact mem_top g
      exact mem_centralizer_singleton_iff.mp hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with hb | ht
    · rw [hb, mem_bot] at hZ
      exact haz1 hZ
    · apply huw
      have := mem_center_iff.mp (ht ▸ mem_top (u : H)) (w : H)
      exact Subtype.ext this.symm

theorem asigma_mem_F : h.a * d.sigma ∈ centralizer ({h.a * d.z} : Set H) :=
  mem_centralizer_singleton_iff.mpr asigma_comm_az

theorem azComp_facts (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    {K : Type} [Field K] [Finite K] {J : Subgroup H} (hJ : X10.AzComp K d J) :
    J.subgroupOf (centralizer ({h.a * d.z} : Set H)) ≤
        centralizer ({(⟨h.a * d.sigma, asigma_mem_F⟩ : ↥(centralizer ({h.a * d.z} : Set H)))} :
          Set ↥(centralizer ({h.a * d.z} : Set H))) ∧
      IsPComponent 2 ((J.subgroupOf (centralizer ({h.a * d.z} : Set H))).subgroupOf
        (centralizer ({(⟨h.a * d.sigma, asigma_mem_F⟩ : ↥(centralizer ({h.a * d.z} : Set H)))} :
          Set ↥(centralizer ({h.a * d.z} : Set H))))) ∧
      J.subgroupOf (centralizer ({h.a * d.z} : Set H)) ≤
        pLayer ↥(centralizer ({h.a * d.z} : Set H)) 2 := by
  set F := centralizer ({h.a * d.z} : Set H) with hF
  obtain ⟨hJLF, hJp, -, -⟩ := hJ
  obtain ⟨hLs, hL⟩ := isPComponent_L (d := d)
  have hsch : LBalance.SchreierSections ↥F :=
    schreierSections_of_isKGroupCat hS isKGroupCat_F
  have hs2 : ∃ n : ℕ, (h.a * d.sigma) ^ 2 ^ n = 1 :=
    ⟨1, by rw [pow_one, pow_two]; exact asigma_involution⟩
  obtain ⟨hJA, hJlay⟩ := X10C.le_layerIn_of_pComponent_inf asigma_comm_az hs2 hsch hLs hL hJLF hJp
  have hJs : J ≤ centralizer ({h.a * d.sigma} : Set H) := hJLF.trans (inf_le_left.trans hLs)
  have hJF : J ≤ F := hJLF.trans inf_le_right
  have hC := centralizer_mk_eq (F := F) asigma_mem_F
  refine ⟨?_, ?_, ?_⟩
  · rw [hC]
    exact subgroupOf_mono _ hJs
  · rw [hC, OddStandard.Solomon75.isPComponent_subgroupOf_subgroupOf_iff hJs hJF, inf_comm]
    exact hJA
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hJlay (show (x : H) ∈ J from hx)
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
