module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UTw25

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem exists_mem_inv_mul_mem_centralizer_of_pow (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {g : Ω} {n : ℕ}
    (hgN : g ∈ Subgroup.normalizer (K : Set Ω)) (hg : g ^ 5 ^ n = 1)
    (hgB : ∀ b ∈ B, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set Ω)) :
    ∃ b ∈ B, g⁻¹ * b ∈ Subgroup.centralizer (K : Set Ω) := by
  obtain ⟨-, -, hDcard, -, -, hKcomp, -⟩ := h.cfg.std
  have hperf : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
  obtain ⟨m, F, _, hFd, hpm, -, -, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hF
  have h25 := not_dvd_of_qsnl h hF hFd θ
  obtain ⟨ρ, -, hρk, hX, hBX, hnl⟩ := exists_act_nl h θ
  have hSN : B ≤ Subgroup.normalizer (S : Set Ω) := fun g _ =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  have hBN := S171.B_norm_K h.cfg.elem hSN h.cfg.std
  have hXc : Nat.card ρ.range = 5 ^ 2 := by
    rw [card_eq_of_qsnl h hF, hDcard] at hBX
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5 ^ 2) (hBX.symm.trans (by norm_num))
  set N := Subgroup.normalizer (K : Set Ω)
  set ψ := CFSG.normalizerToCenterQuotientAut K N le_rfl
  set α := MulAut.congr θ (ψ ⟨g, hgN⟩)
  have hαk : ∀ k k' : ↥K, (k' : Ω) = g * k * g⁻¹ →
      α (θ (k : ↥K ⧸ Subgroup.center ↥K)) = θ (k' : ↥K ⧸ Subgroup.center ↥K) := by
    intro k k' hk'
    have e1 := (CFSG.normalizerConjAutOfMem_comp_mk K N le_rfl ⟨g, hgN⟩ k).symm
    have hk : CFSG.normalizerConjAutOfMem K N le_rfl ⟨g, hgN⟩ k = k' := Subtype.ext hk'.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hk] at e1
    change θ (ψ ⟨g, hgN⟩ (θ.symm (θ (k : ↥K ⧸ Subgroup.center ↥K)))) = _
    rw [MulEquiv.symm_apply_apply, e1]
  have hαn : α ^ 5 ^ n = 1 := by
    have hgn : (⟨g, hgN⟩ : ↥N) ^ 5 ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg)
    rw [← map_pow, ← map_pow, hgn, map_one, map_one]
  have hαX : ∀ β ∈ ρ.range, α * β = β * α := by
    rintro _ ⟨b, rfl⟩
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hb := hBN b.2
    have hgk : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgN k).1 k.2
    have hbk : (b : Ω) * k * (b : Ω)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hb k).1 k.2
    have hgbk : g * ((b : Ω) * k * (b : Ω)⁻¹) * g⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 hgN _).1 hbk
    have hbgk : (b : Ω) * (g * k * g⁻¹) * (b : Ω)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 hb _).1 hgk
    have hcomm := Subgroup.mem_centralizer_iff.1 (hgB b b.2) _ hbgk
    have e : g * ((b : Ω) * k * (b : Ω)⁻¹) * g⁻¹ = (b : Ω) * (g * k * g⁻¹) * (b : Ω)⁻¹ := by
      calc g * ((b : Ω) * k * (b : Ω)⁻¹) * g⁻¹
          = g * b * g⁻¹ * (b : Ω)⁻¹ * ((b : Ω) * (g * k * g⁻¹) * (b : Ω)⁻¹) *
              (g * b * g⁻¹ * (b : Ω)⁻¹)⁻¹ := by group
        _ = (b : Ω) * (g * k * g⁻¹) * (b : Ω)⁻¹ := by rw [← hcomm, mul_inv_cancel_right]
    rw [MulAut.mul_apply, MulAut.mul_apply, hρk b k ⟨_, hbk⟩ rfl, hαk ⟨_, hbk⟩ ⟨_, hgbk⟩ rfl,
      hαk k ⟨_, hgk⟩ rfl, hρk b ⟨_, hgk⟩ ⟨_, hbgk⟩ rfl]
    exact congrArg (fun y : ↥K => θ (y : ↥K ⧸ Subgroup.center ↥K)) (Subtype.ext e)
  obtain ⟨b, hb⟩ : α ∈ ρ.range := mem_of_commute_of_pow_eq_one hFd hpm h25 hX hnl hXc hαn hαX
  refine ⟨b, b.2, inv_mul_mem_centralizer_of_mk_eq hperf hgN (hBN b.2)
    fun k k₁ k₂ hk₁ hk₂ => θ.injective ?_⟩
  rw [← hαk k k₁ hk₁, ← hρk b k k₂ hk₂, hb]

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
