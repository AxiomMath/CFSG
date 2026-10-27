module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Hyp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Gen

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

namespace Lin2Hyp0

section Structure

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem S_le_normalizer_U : S ≤ Subgroup.normalizer (blockU L : Set G) := fun s hs => by
  have := hcfg.H_le_normalizer_Q (hcfg.S_le_H hs)
  rwa [← E.UQ hcfg] at this

theorem R_le_normalizer_U : thompsonJ S ≤ Subgroup.normalizer (blockU L : Set G) :=
  (thompsonJ_le_self S).trans (E.S_le_normalizer_U hcfg)

theorem R_le_normalizer_conjR_U {x : G} (hx : x ∈ T) :
    thompsonJ S ≤ Subgroup.normalizer (conjR (blockU L) x : Set G) := by
  intro r hr
  rw [conjR_normalizer, mem_conjR]
  apply E.R_le_normalizer_U hcfg
  exact (Subgroup.mem_normalizer_iff.1 (E.TnR hcfg hx) r).1 hr

theorem R_comm_le_centerOf : ⁅thompsonJ S, thompsonJ S⁆ ≤ centerOf (thompsonJ S) := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRU, hUV⟩ := E.RUU hcfg hx hxS
  obtain ⟨hUe, hVe, -⟩ := E.elemU hcfg hx hxS
  have hUR : blockU L ≤ thompsonJ S := by rw [hRU]; exact le_sup_left
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  have h1 : ⁅thompsonJ S, thompsonJ S⁆ ≤ blockU L :=
    commutator_le_of_sup_commutative hUR hVR (E.R_le_normalizer_U hcfg) hRU
      (fun a ha b hb => IsElemAbelian.comm hVe ha hb)
  have h2 : ⁅thompsonJ S, thompsonJ S⁆ ≤ conjR (blockU L) x :=
    commutator_le_of_sup_commutative hVR hUR (E.R_le_normalizer_conjR_U hcfg hx)
      (by rw [hRU, sup_comm]) (fun a ha b hb => IsElemAbelian.comm hUe ha hb)
  rw [← hUV]
  exact le_inf h1 h2

theorem centerOf_R_le_U' : centerOf (thompsonJ S) ≤ blockU L := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  rw [← (E.RUU hcfg hx hxS).2]
  exact inf_le_left

theorem centerOf_R_isElemAbelian : IsElemAbelian 2 (centerOf (thompsonJ S)) := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hUe, -, -⟩ := E.elemU hcfg hx hxS
  exact IsElemAbelian.mono (E.centerOf_R_le_U' hcfg) hUe

theorem R_pow_four {r : G} (hr : r ∈ thompsonJ S) : r ^ 4 = 1 := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRU, hUV⟩ := E.RUU hcfg hx hxS
  obtain ⟨hUe, hVe, -⟩ := E.elemU hcfg hx hxS
  have hVR : conjR (blockU L) x ≤ thompsonJ S := by rw [hRU]; exact le_sup_right
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (blockU L : Set G) :=
    hVR.trans (E.R_le_normalizer_U hcfg)
  rw [hRU] at hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer hVN).1 hr
  have hv2 : v ^ 2 = 1 := hVe.2 v hv
  have h1 : v * u * v⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.1 (hVN hv) u).1 hu
  have e1 : (u * v) ^ 2 = u * (v * u * v⁻¹) * v ^ 2 := by simp only [pow_two]; group
  have hs1 : (u * v) ^ 2 ∈ blockU L := by
    rw [e1, hv2, mul_one]
    exact mul_mem hu h1
  calc (u * v) ^ 4 = ((u * v) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := hUe.2 _ hs1

end Structure

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
