module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Amb
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Action

variable {Ω : Type} [Group Ω]

theorem s265e_centerQuotAut_conjAut (S : Subgroup Ω) [S.Normal] {g : Ω}
    (hg : g ∈ Subgroup.normalizer (S : Set Ω)) :
    Y10F.centerQuotAut ↥S (Y10F.conjAut S g hg) = S2019.actQuot S g⁻¹ := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H s =>
    rw [Y10F.centerQuotAut_mk, S2019.actQuot_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by
      rw [Y10F.coe_conjAut, MulAut.conjNormal_apply, inv_inv]))

theorem s265e_mem_centralizer_of_actQuot_eq_one (S : Subgroup Ω) [S.Normal] (hS : ⁅S, S⁆ = S)
    {g : Ω} (hg : S2019.actQuot S g = 1) : g ∈ Subgroup.centralizer (S : Set Ω) := by
  refine S2019.le_centralizer_of_actQuot_eq_one S hS (K := Subgroup.zpowers g) ?_
    (Subgroup.mem_zpowers _)
  intro c hc
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rw [map_zpow, hg, one_zpow]

end Action

section Cfg

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s265e_actRange {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (cfg : QSCfg p S B T x D K) [S.Normal] :
    IsElemAbelian p (B.map (S2019.actQuot S)) ∧ p ^ 3 ≤ Nat.card (B.map (S2019.actQuot S)) := by
  have hp := cfg.prime
  have hSperf : ⁅S, S⁆ = S := S2019.commutator_self_eq_of_isQuasisimple cfg.quasi
  set φ : ↥B →* MulAut (↥S ⧸ Subgroup.center ↥S) := (S2019.actQuot S).comp B.subtype with hφ
  have hrange : φ.range = B.map (S2019.actQuot S) := by
    ext a
    simp [hφ, MonoidHom.mem_range, Subgroup.mem_map]
  refine ⟨CFSG.SectionRank.isElemAbelian_map cfg.elem _, ?_⟩
  rw [← hrange]
  have hker : Nat.card φ.ker ≤ p := by
    have hle : φ.ker.map B.subtype ≤ Subgroup.zpowers x := by
      rintro _ ⟨b, hb, rfl⟩
      have h1 : S2019.actQuot S (b : Ω) = 1 := hb
      have hc : CentMod p S (b : Ω) :=
        centMod_of_mem_centralizer (s265e_mem_centralizer_of_actQuot_eq_one S hSperf h1)
      exact (cfg.centB b b.2).1 hc
    calc Nat.card φ.ker = Nat.card (φ.ker.map B.subtype) :=
          (Subgroup.card_map_of_injective B.subtype_injective).symm
      _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      _ ≤ p := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (cfg.elem.2 x cfg.xB))
  have hmul := Subgroup.card_ker_mul_card_range φ
  have h1 : p * p ^ 3 ≤ p * Nat.card φ.range := by
    calc p * p ^ 3 = p ^ 4 := by ring
      _ ≤ Nat.card B := cfg.big
      _ = Nat.card φ.ker * Nat.card φ.range := hmul.symm
      _ ≤ p * Nat.card φ.range := Nat.mul_le_mul_right _ hker
  exact Nat.le_of_mul_le_mul_left h1 hp.pos

theorem s265e_exists_d0 {p : ℕ} {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (cfg : QSCfg p S B T x D K) :
    ∃ d₀ ∈ B, d₀ ∉ Subgroup.zpowers x ∧ d₀ ∉ Subgroup.centralizer (S : Set Ω) ∧
      IsComponentOf K (S ⊓ Subgroup.centralizer ({d₀} : Set Ω)) := by
  obtain ⟨d₀, hdD, hdx⟩ := S171.exists_y cfg.prime cfg.x1 cfg.std
  have hdB : d₀ ∈ B := cfg.std.1 hdD
  have hLx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen s)
  obtain ⟨-, -, -, -, -, hKcomp, -⟩ := cfg.std
  refine ⟨d₀, hdB, hdx, fun hC => hdx ((cfg.centB d₀ hdB).1 (centMod_of_mem_centralizer hC)), ?_⟩
  rwa [S171.L_cs_eq cfg.prime cfg.x1 cfg.std hdD hdx hLx] at hKcomp

end Cfg

end CFSG.LocalAnalysis.GLTheoremA.S265

end
