module

import CFSG.GroupTheory.PLayer.Transport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {Ω : Type} [Group Ω]

theorem inv_mul_mem_centralizer_of_mk_eq {K : Subgroup Ω} (hperf : Group.IsPerfect ↥K)
    {a b : Ω} (ha : a ∈ Subgroup.normalizer (K : Set Ω))
    (hb : b ∈ Subgroup.normalizer (K : Set Ω))
    (hab : ∀ k k₁ k₂ : ↥K, (k₁ : Ω) = a * k * a⁻¹ → (k₂ : Ω) = b * k * b⁻¹ →
      (k₁ : ↥K ⧸ Subgroup.center ↥K) = (k₂ : ↥K ⧸ Subgroup.center ↥K)) :
    a⁻¹ * b ∈ Subgroup.centralizer (K : Set Ω) := by
  set N := Subgroup.normalizer (K : Set Ω) with hN
  set ψ := CFSG.normalizerToCenterQuotientAut K N le_rfl with hψ
  have hψab : ψ ⟨a, ha⟩ = ψ ⟨b, hb⟩ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have e1 := (CFSG.normalizerConjAutOfMem_comp_mk K N le_rfl ⟨a, ha⟩ k).symm
      have e2 := (CFSG.normalizerConjAutOfMem_comp_mk K N le_rfl ⟨b, hb⟩ k).symm
      rw [QuotientGroup.mk'_apply] at e1 e2
      rw [e1, e2, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
      exact hab k _ _ rfl rfl
  have h1 : ψ (⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [map_mul, map_inv, hψab, inv_mul_cancel]
  exact ((CFSG.normalizerToCenterQuotientAut_eq_one_iff hperf le_rfl _).1 h1).2

theorem eq_mulAut_conj_of_act {K : Subgroup Ω} {R : Type} [Group R]
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) {σ : MulAut R} {y : Ω} (hyK : y ∈ K)
    (hσ : ∀ k k' : ↥K, (k' : Ω) = y * k * y⁻¹ →
      σ (θ (k : ↥K ⧸ Subgroup.center ↥K)) = θ (k' : ↥K ⧸ Subgroup.center ↥K)) :
    σ = MulAut.conj (θ ((⟨y, hyK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)) := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [hσ k (⟨y, hyK⟩ * k * (⟨y, hyK⟩ : ↥K)⁻¹) rfl, MulAut.conj_apply, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]

variable [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem exists_act_nl {p : ℕ} (h : QSNL p S B T x D K) {R : Type} [Group R]
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) :
    ∃ ρ : ↥B →* MulAut R, (∀ b : ↥B, ρ b = 1 ↔ (b : Ω) ∈ D) ∧
      (∀ (b : ↥B) (k k' : ↥K), (k' : Ω) = (b : Ω) * (k : Ω) * (b : Ω)⁻¹ →
        ρ b (θ (k : ↥K ⧸ Subgroup.center ↥K)) = θ (k' : ↥K ⧸ Subgroup.center ↥K)) ∧
      IsElemAbelian p ρ.range ∧ Nat.card B = Nat.card D * Nat.card ρ.range ∧
      ∀ α ∈ ρ.range, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥ := by
  obtain ⟨hDB, -, -, -, -, hKcomp, hDK⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  haveI : Finite R := Finite.of_equiv _ θ.toEquiv
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hBN := S171.B_norm_K h.cfg.elem hSN h.cfg.std
  set φ := CFSG.normalizerToCenterQuotientAut K B hBN with hφ
  set ρ : ↥B →* MulAut R := (MulAut.congr θ).toMonoidHom.comp φ with hρ
  have hρ1 : ∀ b : ↥B, ρ b = 1 ↔ (b : Ω) ∈ D := fun b => by
    rw [hρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulAut.congr θ).injective,
      CFSG.normalizerToCenterQuotientAut_eq_one_iff hperf hBN b, ← hDK]
  have hcomm : ∀ a c : ↥B, a * c = c * a := fun a c => h.cfg.elem.1.is_comm.comm a c
  refine ⟨ρ, hρ1, fun b k k' hk' => ?_, ⟨⟨⟨fun a c => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · have e1 := (CFSG.normalizerConjAutOfMem_comp_mk K B hBN b k).symm
    have hk : CFSG.normalizerConjAutOfMem K B hBN b k = k' := Subtype.ext hk'.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hk] at e1
    change θ (φ b (θ.symm (θ (k : ↥K ⧸ Subgroup.center ↥K)))) = _
    rw [MulEquiv.symm_apply_apply, e1]
  · obtain ⟨_, b, rfl⟩ := a
    obtain ⟨_, c, rfl⟩ := c
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm])
  · rintro _ ⟨b, rfl⟩
    have hb : b ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h.cfg.elem.2 _ b.2)
    rw [← map_pow, hb, map_one]
  · have hX : Nat.card ρ.range = D.relIndex B := by
      rw [hρ, MonoidHom.range_comp, Subgroup.card_map_of_injective
        (f := (MulAut.congr θ).toMonoidHom) (MulAut.congr θ).injective,
        CFSG.card_range_normalizerToCenterQuotientAut hperf hBN, ← hDK]
    have h1 := (Subgroup.relIndex_mul_card (H := D) (K := B)).symm
    rwa [inf_of_le_left hDB, mul_comm, ← hX] at h1
  · rintro _ ⟨b, rfl⟩ hb1
    have hbD : (b : Ω) ∉ D := fun hmem => hb1 ((hρ1 b).2 hmem)
    change GLAPLayer p (fixSubgroup (MulAut.congr θ (φ b))) = ⊥
    rw [CFSG.glaPLayer_fixSubgroup_congr h.cfg.prime θ (φ b),
      (CFSG.glaPLayer_inf_centralizer_eq_bot_iff h.cfg.prime hBN b).1 (h.nl b b.2 hbD),
      Subgroup.map_bot]

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
