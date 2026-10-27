module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54M3b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma conj_comp_toMonoidHom (a b : G) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

private lemma conjSub_conjSub (a b : G) (W : Subgroup G) :
    conjSub a (conjSub b W) = conjSub (a * b) W := by
  simp only [conjSub, Subgroup.map_map, conj_comp_toMonoidHom]

theorem y7n_t_norm_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    conjSub c.s.t (M3 c.s) = M3 c.s := by
  have htY : c.s.t ∈ f4Y c.s :=
    y54_X0_le_Y hH (y54_P_le_X0 hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)))
  apply le_antisymm
  · intro x hx
    rw [conjSub, Subgroup.mem_map] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      y54_M_normal (c := c) hH (y54_M3_cand c hH) c.s.t htY m hm
  · intro m hm
    rw [conjSub, Subgroup.mem_map]
    refine ⟨c.s.t⁻¹ * m * c.s.t, ?_, ?_⟩
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        y54_M_normal (c := c) hH (y54_M3_cand c hH) c.s.t⁻¹ ((f4Y c.s).inv_mem htY) m hm
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem y7n_N_M3_le_N_K (s : Setting3 G L) :
    normalizer (M3 s : Set G) ≤ normalizer (K7 s : Set G) := by
  have hstep : ∀ m ∈ normalizer (M3 s : Set G),
      (K7 s).map (MulAut.conj m) ≤ K7 s := by
    intro m hm
    rw [K7]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hx => ?_
    change conjSub m (conjSub x (JF s ⊔ M3 s)) ≤
      ⨆ x ∈ normalizer (M3 s : Set G), conjSub x (JF s ⊔ M3 s)
    rw [conjSub_conjSub]
    exact le_iSup₂ (f := fun x (_ : x ∈ normalizer (M3 s : Set G)) =>
      conjSub x (JF s ⊔ M3 s)) (m * x) (Subgroup.mul_mem _ hm hx)
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hstep n hn) ?_
  intro k hk
  rw [Subgroup.mem_map]
  refine ⟨n⁻¹ * k * n, ?_, ?_⟩
  · exact hstep n⁻¹ (Subgroup.inv_mem _ hn)
      (Subgroup.mem_map.mpr ⟨k, hk, by
        change (MulAut.conj n⁻¹) k = n⁻¹ * k * n
        rw [MulAut.conj_apply]; group⟩)
  · change (MulAut.conj n) (n⁻¹ * k * n) = k
    rw [MulAut.conj_apply]; group

theorem y7n_P_pgroup {c : Ctx7 G L} (h76 : c.Fact76) : IsPGroup 2 (P7 c.e) :=
  IsPGroup.of_card h76.2.1

theorem y7n_M3_pgroup {c : Ctx7 G L} (h71 : c.Fact71) (h76 : c.Fact76) :
    IsPGroup 2 (M3 c.s) := by
  refine (y7n_P_pgroup h76).to_le ?_
  rw [P7]
  exact h71.2.2.2.1.trans le_sup_left

theorem y7n_g_norm_P {c : Ctx7 G L} (hRT : c.s.R ≠ c.s.T) (h71 : c.Fact71) (h72 : c.Fact72)
    (h75 : c.Fact75) : ∀ x ∈ P7 c.e, c.g * x * c.g⁻¹ ∈ P7 c.e := by
  have hM3M6 : M3 c.s ≤ M6 c.e := h71.2.2.2.1
  have hM3M7 : M3 c.s ≤ M7 c.s := by
    rw [M7]
    exact le_sup_right.trans le_sup_right
  have hconjM6 : ∀ m ∈ M6 c.e, c.g * m * c.g⁻¹ ∈ M6 c.e := by
    intro m hm
    have hc : ⁅c.g, m⁆ ∈ M3 c.s := h72.2.2.2 hRT m hm
    have heq : c.g * m * c.g⁻¹ = ⁅c.g, m⁆ * m := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact (M6 c.e).mul_mem (hM3M6 hc) hm
  have hconjM7 : ∀ m ∈ M7 c.s, c.g * m * c.g⁻¹ ∈ M7 c.s := by
    intro m hm
    have hc : ⁅c.g, m⁆ ∈ M3 c.s := h75.2.2.2 hRT m hm
    have heq : c.g * m * c.g⁻¹ = ⁅c.g, m⁆ * m := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact (M7 c.s).mul_mem (hM3M7 hc) hm
  have hle : conjSub c.g (P7 c.e) ≤ P7 c.e := by
    rw [P7, conjSub, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro m hm
      exact Subgroup.mem_sup_left (by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hconjM6 m hm)
    · rw [Subgroup.map_le_iff_le_comap]
      intro m hm
      exact Subgroup.mem_sup_right (by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hconjM7 m hm)
  intro x hx
  exact hle (Subgroup.mem_map.mpr ⟨x, hx, by rfl⟩)

end CFSG.OddStandard.HigherRank.YamadaG23
