module

public import Certificates.Data.Kernel.PermCent.A7AiC
public import CFSG.Certificates.Kernel.PermCent.F7CentSound

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.A7Ai CFSG.GH74.GLS.C3.Prop121

theorem exists_allPermsP (σ : Perm (Fin 7)) : ∃ x ∈ allPermsP 7 inferInstance, ev x.1 = σ := by
  have h := mem_allPerms 7 σ
  rw [allPerms_eq 7 inferInstance, List.mem_map] at h
  exact h

theorem ev_c1P : ev c1P = c1 := ev_cOf c1

theorem ev_c2P : ev c2P = c2 := ev_cOf c2

theorem e9_eq : e9 = e9P.map ev := by
  unfold e9 e9P
  simp only [tab_eq, List.map_flatMap, List.map_map, Function.comp_def, ev_mul, ← ev_pow', ev_c1P,
    ev_c2P]

theorem vInv_eq : vInv = vP.map ev := by
  unfold vP
  rw [List.map_map]
  simp only [Function.comp_def, ev_cOf, List.map_id']

theorem cy1_eq : ([1, ev c1P, ev c1P ^ 2] : List (Perm (Fin 7))) = cy1P.map ev := by
  simp only [cy1P, List.map_cons, List.map_nil, ev_one, ← ev_pow']

theorem cy2_eq : ([1, ev c2P, ev c2P ^ 2] : List (Perm (Fin 7))) = cy2P.map ev := by
  simp only [cy2P, List.map_cons, List.map_nil, ev_one, ← ev_pow']

theorem one_mem_e9 : (1 : Perm (Fin 7)) ∈ e9 := by
  unfold e9
  refine List.mem_flatMap.2 ⟨0, List.mem_range.2 (by decide), List.mem_map.2 ⟨0,
    List.mem_range.2 (by decide), ?_⟩⟩
  rw [tab_eq, pow_zero, pow_zero, one_mul]

theorem mem_e9PP {z : CV 7 × CV 7} (hz : z ∈ e9PP) : z.1 ∈ e9P ∧ z.2 = z.1⁻¹ := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
  exact ⟨hw, rfl⟩

theorem a7aiA_of (h : a7aiAF = true) (t : Perm (Fin 7)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hE : ∀ x ∈ e9, ∀ y ∈ e9, (x * t * x⁻¹ * (y * t * y⁻¹)) ^ 16 = 1) : t ∈ vInv := by
  rw [a7aiAF, forceQL_eq, forceCL_eq, a7aiAB, List.all_eq_true] at h
  obtain ⟨x, hx, rfl⟩ := exists_allPermsP t
  have hx' := h x hx
  by_contra hv
  have h1 : powOneC x.1 2 = true := by
    rw [powOneC_eq, decide_eq_true_iff, pow_two]
    apply ev_injective
    rw [ev_mul, ev_one]
    exact ht2
  have h2 : powOneC x.1 1 = false := by
    rw [powOneC_eq, decide_eq_false_iff_not, pow_one]
    intro h0
    apply ht1
    rw [h0, ev_one]
  have h3 : memC x.1.1 vP = false := by
    rw [memC_val, decide_eq_false_iff_not]
    intro hm
    apply hv
    rw [vInv_eq]
    exact List.mem_map_of_mem hm
  have h4 : (e9PP.any fun z => !powOneC (x.1 * (z.1 * x.1 * z.2)) 16) = false := by
    rw [List.any_eq_false]
    intro z hz hc
    rw [Bool.not_eq_true', powOneC_eq, decide_eq_false_iff_not] at hc
    obtain ⟨hz1, hz2⟩ := mem_e9PP hz
    apply hc
    have hw : ev z.1 ∈ e9 := by
      rw [e9_eq]
      exact List.mem_map_of_mem hz1
    have he := hE 1 one_mem_e9 (ev z.1) hw
    rw [one_mul, inv_one, mul_one] at he
    apply ev_injective
    rw [← ev_pow', ev_mul, ev_mul, ev_mul, hz2, ev_inv, ev_one]
    exact he
  rw [h1, h2, h3, h4] at hx'
  exact absurd hx' (by decide)

theorem conj_mem_iff (g a : CV 7) (L : List (CV 7)) :
    ev g * ev a * (ev g)⁻¹ ∈ L.map ev ↔ (L.any fun e => eq22C g a e g) = true := by
  rw [ev_inv', ev_mul', ev_mul', mem_map_ev, List.any_eq_true]
  simp only [← conj_fast, decide_eq_true_iff]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨e, he, h⟩ => h ▸ he⟩

theorem decide_conj_mem (g a : CV 7) (L : List (CV 7))
    [Decidable (ev g * ev a * (ev g)⁻¹ ∈ L.map ev)] :
    decide (ev g * ev a * (ev g)⁻¹ ∈ L.map ev) = L.any fun e => eq22C g a e g := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, conj_mem_iff]

theorem any_e9PP (g a : CV 7) :
    (e9PP.any fun e => eq22C g a e.1 g) = e9P.any fun e => eq22C g a e g := by
  unfold e9PP
  rw [List.any_map]
  rfl

theorem badGB_of (g : CV 7) (h : badG (ev g) = true) : badGB e9PP cy1P cy2P c1P c2P g = true := by
  unfold badG at h
  rw [← ev_c1P, ← ev_c2P] at h
  rw [e9_eq, cy1_eq, cy2_eq, decide_conj_mem, decide_conj_mem, decide_conj_mem,
    decide_conj_mem] at h
  rw [badGB, any_e9PP, any_e9PP]
  exact h

theorem a7aiB_of (h : a7aiBF = true) (g : Perm (Fin 7)) (hg : badG g = true) (t : Perm (Fin 7))
    (ht : t ∈ vInv) (hu : g * t * g⁻¹ ∈ vInv) : (t * (g * t * g⁻¹)) ^ 16 ≠ 1 := by
  rw [a7aiBF, forceQL_eq, forceCL_eq, forceCL_eq, forceC_eq, forceC_eq, forceCL_eq, forceQL_eq,
    a7aiBB, List.all_eq_true] at h
  obtain ⟨x, hx, rfl⟩ := exists_allPermsP g
  have hx' := h x hx
  rw [badGB_of x.1 hg, Bool.not_true, Bool.false_or, List.all_eq_true] at hx'
  rw [vInv_eq] at ht hu
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  rw [ev_inv', ev_mul', ev_mul'] at hu ⊢
  obtain ⟨u', hu', hue⟩ := List.mem_map.1 hu
  have hue' : u' = x.1 * t' * x.1⁻¹ := ev_injective hue
  intro hpow
  have hp : (t', u') ∈ p16P vP := by
    unfold p16P
    rw [List.mem_filter]
    refine ⟨List.mem_flatMap.2 ⟨t', ht', List.mem_map.2 ⟨u', hu', rfl⟩⟩, ?_⟩
    rw [powOneC_eq, decide_eq_true_iff, hue']
    apply ev_injective
    rw [← ev_pow', ev_mul, ev_one]
    exact hpow
  have hc := hx' (t', u') hp
  rw [Bool.not_eq_true', ← conj_fast, decide_eq_false_iff_not] at hc
  exact hc hue'.symm

end CFSG.Certificates.Kernel.PkCV

end
