module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MSide
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5BorelSolv
public import CFSG.FeitThompson.OddOrderTheorem
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem frU_ne_bot [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    frU P x ≠ ⊥ := by
  obtain ⟨n, hn, -, -, -, hcard⟩ := fr_layer_sylow hG hl
  intro h
  rw [h, Subgroup.card_bot] at hcard
  have := (Fact.out : p.Prime).one_lt
  have h2 : 1 < p ^ n := Nat.one_lt_pow (by omega) this
  omega

theorem frU_le_M [Fact p.Prime] (hl : FrobLocal p P M x) : frU P x ≤ M :=
  inf_le_left.trans (fr_P_le_M hl)

theorem fr_inf_layer_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    M ⊓ layerOf x ≤ normalizer (frU P x : Set G) := by
  obtain ⟨n, hn, ⟨e⟩, hU, -, -⟩ := fr_layer_sylow hG hl
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  exact CFSG.LocalAnalysis.RankThreeTheoremC.inf_le_normalizer_of_mulEquiv_psl2GF hp2
    (by omega) e hU (fr_normalizer_le hG hl le_rfl (frU_ne_bot hG hl)) hl.not_le

theorem fr_inf_normalizer_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    M ⊓ normalizer ((layerOf x : Subgroup G) : Set G) ≤ normalizer (frU P x : Set G) := by
  obtain ⟨n, hn, ⟨e⟩, hU, -, -⟩ := fr_layer_sylow hG hl
  exact CFSG.LocalAnalysis.RankThreeTheoremC.inf_normalizer_le_normalizer_of_isSylowOf hU
    (frU_le_M hl) (fr_inf_layer_le hG hl)

theorem fr_solvable_inf_normalizer [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    Group.IsSolvable ↥(M ⊓ normalizer ((layerOf x : Subgroup G) : Set G)) := by
  obtain ⟨n, hn, ⟨e⟩, hU, -, -⟩ := fr_layer_sylow hG hl
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  have : Group.IsSolvable (centralizer ((layerOf x : Subgroup G) : Set G)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (fr_centralizer_layer_odd hG hl)
  exact CFSG.LocalAnalysis.RankThreeTheoremC.isSolvable_of_le_normalizer_of_mulEquiv_psl2GF hp2
    (by omega) e hU inf_le_right (fr_inf_normalizer_le hG hl)

theorem frN_normalizer_centralizer_le (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer ((centralizer (H : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ c ∈ centralizer (H : Set G),
      g * c * g⁻¹ ∈ centralizer (H : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    have hh' : g⁻¹ * h * g ∈ (H : Set G) := (mem_normalizer_iff''.mp hg h).mp hh
    have hcomm := hc _ hh'
    calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
      _ = g * c * g⁻¹ * h := by group
  intro g hg
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have h := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using h

theorem frN_normalizer_layer_le (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer ((CFSG.Open.GLBLayer H : Subgroup G) : Set G) := by
  have hmap : ∀ (e : G ≃* G) (K : Subgroup G),
      (CFSG.Open.GLBLayer K).map e.toMonoidHom ≤ CFSG.Open.GLBLayer (K.map e.toMonoidHom) := by
    intro e K
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hL)
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ CFSG.Open.GLBLayer H,
      g * y * g⁻¹ ∈ CFSG.Open.GLBLayer H := by
    intro g hg y hy
    have hK : H.map (MulAut.conj g).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have h := hmap (MulAut.conj g) H ⟨y, hy, rfl⟩
    rwa [hK] at h
  intro g hg
  rw [mem_normalizer_iff]
  exact fun y => ⟨key g hg y, fun hy => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hy⟩

theorem fr_normalizer_sylow_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    normalizer ((P : Subgroup G) : Set G) ≤ normalizer ((layerOf x : Subgroup G) : Set G) := by
  intro g hg
  have hgx : g * x * g⁻¹ ∈ (P : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp hg x).mp hl.point.mem
  have hcl : CFSG.Open.GLBConj g⁻¹ (zpowers x) ≤ (P : Subgroup G) := by
    unfold CFSG.Open.GLBConj
    rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
    simpa using hgx
  have hfix : CFSG.Open.GLBConj g⁻¹ (zpowers x) = zpowers x := hl.weak g⁻¹ hcl
  have hgZ : g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    unfold CFSG.Open.GLBConj at hfix
    simpa using hfix
  exact frN_normalizer_layer_le (centralizer ((zpowers x : Subgroup G) : Set G))
    (frN_normalizer_centralizer_le (zpowers x) hgZ)

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
