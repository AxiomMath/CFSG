module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section LQ4

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem R_sq_mem_centerOf {r : G} (hr : r ∈ thompsonJ S) : r ^ 2 ∈ centerOf (thompsonJ S) := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRU, hUV⟩ := E.RUU hcfg hx hxS
  obtain ⟨hUe, hVe, -⟩ := E.elemU hcfg hx hxS
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (blockU L : Set G) :=
    hVR.trans (E.R_le_normalizer_U hcfg)
  have hUN : blockU L ≤ Subgroup.normalizer (conjR (blockU L) x : Set G) :=
    hUR.trans (E.R_le_normalizer_conjR_U hcfg hx)
  rw [hRU] at hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer hVN).1 hr
  have hu2 : u ^ 2 = 1 := hUe.2 u hu
  have hv2 : v ^ 2 = 1 := hVe.2 v hv
  have h1 : v * u * v⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.1 (hVN hv) u).1 hu
  have h2 : u * v * u⁻¹ ∈ conjR (blockU L) x := (Subgroup.mem_normalizer_iff.1 (hUN hu) v).1 hv
  have e1 : (u * v) ^ 2 = u * (v * u * v⁻¹) * v ^ 2 := by simp only [pow_two]; group
  have e2 : (u * v) ^ 2 = (u * v * u⁻¹) * u ^ 2 * v := by simp only [pow_two]; group
  have hs1 : (u * v) ^ 2 ∈ blockU L := by rw [e1, hv2, mul_one]; exact mul_mem hu h1
  have hs2 : (u * v) ^ 2 ∈ conjR (blockU L) x := by rw [e2, hu2, mul_one]; exact mul_mem h2 hv
  rw [← hUV]
  exact ⟨hs1, hs2⟩

theorem mul_mem_S_of_not_mem_S {x t : G} (hx : x ∈ T) (hxS : x ∉ S) (ht : t ∈ T) (htS : t ∉ S) :
    x * t ∈ S := by
  have := inv_mul_mem_of_relIndex_two (E.idxTS hcfg) (T.inv_mem hx) ht
    (fun h => hxS (by simpa using S.inv_mem h)) htS
  simpa using this

theorem swap_U {x t : G} (hx : x ∈ T) (hxS : x ∉ S) (ht : t ∈ T) (htS : t ∉ S) {y : G}
    (hy : y ∈ blockU L) : t * y * t⁻¹ ∈ conjR (blockU L) x := by
  rw [mem_conjR]
  have hxt : x * t ∈ S := E.mul_mem_S_of_not_mem_S hcfg hx hxS ht htS
  have := (Subgroup.mem_normalizer_iff.1 (E.S_le_normalizer_U hcfg hxt) y).1 hy
  have e : x * t * y * (x * t)⁻¹ = x * (t * y * t⁻¹) * x⁻¹ := by group
  rwa [e] at this

theorem swap_Ux {x t : G} (hx : x ∈ T) (hxS : x ∉ S) (ht : t ∈ T) (htS : t ∉ S) {y : G}
    (hy : y ∈ conjR (blockU L) x) : t * y * t⁻¹ ∈ blockU L := by
  have hy' : x * y * x⁻¹ ∈ blockU L := mem_conjR.1 hy
  have hxi : x⁻¹ ∈ T := T.inv_mem hx
  have hxiS : x⁻¹ ∉ S := fun h => hxS (by simpa using S.inv_mem h)
  have hti := inv_mul_mem_of_relIndex_two (E.idxTS hcfg) (T.inv_mem ht) hxi
    (fun h => htS (by simpa using S.inv_mem h)) hxiS
  have hts : t * x⁻¹ ∈ S := by simpa using hti
  have := (Subgroup.mem_normalizer_iff.1 (E.S_le_normalizer_U hcfg hts) _).1 hy'
  have e : t * x⁻¹ * (x * y * x⁻¹) * (t * x⁻¹)⁻¹ = t * y * t⁻¹ := by group
  rwa [e] at this

theorem inf_R_le_centerOf {x t : G} (hx : x ∈ T) (hxS : x ∉ S) (ht : t ∈ T) (htS : t ∉ S)
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (htV : t ∈ V) :
    V ⊓ thompsonJ S ≤ centerOf (thompsonJ S) := by
  intro y hy
  have hel : IsElemAbelian 2 (V ⊓ thompsonJ S) := IsElemAbelian.mono inf_le_left hV
  obtain ⟨hUe, hVe, hmax⟩ := E.elemU hcfg hx hxS
  obtain ⟨-, hUV⟩ := E.RUU hcfg hx hxS
  have hcomm : t * y * t⁻¹ = y := by
    have := IsElemAbelian.comm hV htV hy.1
    rw [this]; group
  rcases hmax _ inf_le_right hel with hU | hUx
  · have hyU : y ∈ blockU L := hU hy
    have := E.swap_U hcfg hx hxS ht htS hyU
    rw [hcomm] at this
    rw [← hUV]; exact ⟨hyU, this⟩
  · have hyUx : y ∈ conjR (blockU L) x := hUx hy
    have := E.swap_Ux hcfg hx hxS ht htS hyUx
    rw [hcomm] at this
    rw [← hUV]; exact ⟨this, hyUx⟩

theorem exists_conjR_Z_of_mem (hc : centerOf L = ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) {h y : G}
    (hy : y ∈ conjR (thompsonJ S) h) (hy2 : y ^ 2 = 1) :
    ∃ k : G, conjR (lin2Z L (thompsonJ S)) k ≤ conjR (thompsonJ S) h ∧
      y ∈ conjR (lin2Z L (thompsonJ S)) k := by
  have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
    ((lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl).resolve_right fun h => h.1 hc).2
  have hZU : lin2Z L (thompsonJ S) ≤ blockU L := by
    rw [hZR]; exact E.centerOf_R_le_U' hcfg
  obtain ⟨hRU, -⟩ := E.RUU hcfg hx hxS
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  obtain ⟨-, -, hmax⟩ := E.elemU hcfg hx hxS
  have hy0 : h * y * h⁻¹ ∈ thompsonJ S := mem_conjR.1 hy
  have hy02 : (h * y * h⁻¹) ^ 2 = 1 := by
    have : (h * y * h⁻¹) ^ 2 = h * y ^ 2 * h⁻¹ := by simp only [pow_two]; group
    rw [this, hy2]; group
  have hel := isElemAbelian_zpowers_of_sq_eq_one hy02
  have hle : Subgroup.zpowers (h * y * h⁻¹) ≤ thompsonJ S := Subgroup.zpowers_le.2 hy0
  have hZℓ : ∀ ℓ ∈ L, conjR (lin2Z L (thompsonJ S)) ℓ ≤ blockU L := fun ℓ hℓ =>
    calc conjR (lin2Z L (thompsonJ S)) ℓ ≤ conjR (blockU L) ℓ := conjR_mono hZU ℓ
      _ = blockU L := conjR_eq_of_mem_normalizer (E.L_le_normalizer_U hcfg hℓ)
  rcases hmax _ hle hel with hU | hUx
  · have hyU : h * y * h⁻¹ ∈ blockU L := hU (Subgroup.mem_zpowers _)
    obtain ⟨ℓ, hℓ, hℓy⟩ := E.exists_conj_mem_centerOf_R hcfg hyU
    refine ⟨ℓ * h, ?_, ?_⟩
    · rw [← conjR_conjR]
      exact conjR_mono ((hZℓ ℓ hℓ).trans hUR) h
    · rw [mem_conjR, hZR]
      have e : ℓ * h * y * (ℓ * h)⁻¹ = ℓ * (h * y * h⁻¹) * ℓ⁻¹ := by group
      rw [e]; exact hℓy
  · have hyUx : x * (h * y * h⁻¹) * x⁻¹ ∈ blockU L := mem_conjR.1 (hUx (Subgroup.mem_zpowers _))
    obtain ⟨ℓ, hℓ, hℓy⟩ := E.exists_conj_mem_centerOf_R hcfg hyUx
    refine ⟨ℓ * x * h, ?_, ?_⟩
    · rw [← conjR_conjR, ← conjR_conjR]
      refine conjR_mono ?_ h
      exact (conjR_mono (hZℓ ℓ hℓ) x).trans hVR
    · rw [mem_conjR, hZR]
      have e : ℓ * x * h * y * (ℓ * x * h)⁻¹ = ℓ * (x * (h * y * h⁻¹) * x⁻¹) * ℓ⁻¹ := by group
      rw [e]; exact hℓy

end LQ4

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
