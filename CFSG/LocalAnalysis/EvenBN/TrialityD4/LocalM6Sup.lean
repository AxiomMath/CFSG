module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Five
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem mem_normalizer_map_conj_of_comm {A : Subgroup G} {g v : G} (hgv : g * v = v * g)
    (hA : g ∈ normalizer (A : Set G)) :
    g ∈ normalizer ((A.map (MulAut.conj v).toMonoidHom : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨g * a * g⁻¹, (mem_normalizer_iff.1 hA a).1 ha, ?_⟩
  show v * (g * a * g⁻¹) * v⁻¹ = g * (v * a * v⁻¹) * g⁻¹
  calc v * (g * a * g⁻¹) * v⁻¹ = (v * g) * a * (v * g)⁻¹ := by group
    _ = (g * v) * a * (g * v)⁻¹ := by rw [hgv]
    _ = g * (v * a * v⁻¹) * g⁻¹ := by group

theorem yamada_5_29_1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hL₆ : yamadaL₆ d t =
      yamadaL₄ d t ⊔ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom) :
    yamadaL₆ d t = yamadaM₆ d t ⊔ zpowers t ∧ t ∉ yamadaM₆ d t ∧
      yamadaM₆ d t =
        yamadaM₄ d t ⊔ (yamadaM₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  obtain ⟨hL₄, -⟩ := h.yamadaL₄_eq_sup d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have hvt : ((d.v : L) : G) * t = t * ((d.v : L) : G) :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.v).2)
  have hvC : ((d.v : L) : G) ∈ normalizer (centralizer (yamadaY₂ d t : Set G) : Set G) :=
    mem_normalizer_centralizer_C8 (v_mem_normalizer_yamadaY₂ (t := t) d)
  have hφt : (MulAut.conj ((d.v : L) : G)).toMonoidHom t = t := by
    show ((d.v : L) : G) * t * ((d.v : L) : G)⁻¹ = t
    rw [hvt, mul_inv_cancel_right]
  have hφz : (zpowers t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = zpowers t := by
    rw [MonoidHom.map_zpowers, hφt]
  have htR₄ : t ∈ yamadaR₄ d t := h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    Common.mem_normalizer_inf (le_normalizer htR₄)
      (mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))
  have htL₄ : t ∈ yamadaL₄ d t := by
    rw [hL₄]
    exact mem_sup_right (mem_zpowers t)
  have hM₄L₄ : yamadaM₄ d t ≤ yamadaL₄ d t := by
    rw [hL₄]
    exact le_sup_left
  have hL₄L₆ : yamadaL₄ d t ≤ yamadaL₆ d t := by
    rw [hL₆]
    exact le_sup_left
  have hM₄C : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G) := inf_le_right
  have hMφC : (yamadaM₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤
      centralizer (yamadaY₂ d t : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.1 hvC m).1 (hM₄C hm)
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G,
      N = yamadaM₄ d t ⊔ (yamadaM₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom :=
    ⟨_, rfl⟩
  have hM₄N : yamadaM₄ d t ≤ N := by
    rw [hN]
    exact le_sup_left
  have hMφN : (yamadaM₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤ N := by
    rw [hN]
    exact le_sup_right
  have hNL₆ : N ≤ yamadaL₆ d t := by
    rw [hN, hL₆]
    exact sup_le (hM₄L₄.trans le_sup_left)
      ((Subgroup.map_mono (f := (MulAut.conj ((d.v : L) : G)).toMonoidHom) hM₄L₄).trans
        le_sup_right)
  have hNC : N ≤ centralizer (yamadaY₂ d t : Set G) := by
    rw [hN]
    exact sup_le hM₄C hMφC
  have htN : t ∈ normalizer (N : Set G) := by
    rw [hN]
    exact Common.mem_normalizer_sup htM₄ (mem_normalizer_map_conj_of_comm hvt.symm htM₄)
  have hL₆N : yamadaL₆ d t = N ⊔ zpowers t := by
    refine le_antisymm ?_ (sup_le hNL₆ ((zpowers_le).2 (hL₄L₆ htL₄)))
    rw [hL₆, hL₄, Subgroup.map_sup, hφz]
    exact sup_le (sup_le (hM₄N.trans le_sup_left) le_sup_right)
      (sup_le (hMφN.trans le_sup_left) le_sup_right)
  have hM₆N : yamadaM₆ d t = N := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
      rw [hL₆N, h.mem_sup_zpowers_iff_of_normalizer htN] at hxL
      rcases hxL with hxN | htx
      · exact hxN
      · exfalso
        have htC : t ∈ centralizer (yamadaY₂ d t : Set G) := by
          have := mul_mem (hNC htx) (inv_mem hxC)
          rwa [mul_inv_cancel_right] at this
        exact t_not_mem_centralizer_yamadaY₂ d h592 htC
    · exact Subgroup.mem_inf.2 ⟨hNL₆ hx, hNC hx⟩
  have htM₆ : t ∉ yamadaM₆ d t := fun ht =>
    t_not_mem_centralizer_yamadaY₂ d h592 (Subgroup.mem_inf.1 ht).2
  refine ⟨?_, htM₆, ?_⟩
  · rw [hM₆N]
    exact hL₆N
  · rw [hM₆N]
    exact hN

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
