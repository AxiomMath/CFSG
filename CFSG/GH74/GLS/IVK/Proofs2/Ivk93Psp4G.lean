module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

section Psp4

theorem ivk93_psp4 (h93 : Ivk93Pair) (hctx : Stage2Ctx G z Kind.psp4 S)
    {H : Subgroup G} (hne : H ≠ ⊤) (hCH : Cen z ≤ H)
    (hs : IsSimpleGroup ↥(generalizedFitting (HBar H)))
    (hn : ∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) (hPerf : PerfInJ H) : FUS H := by
  have hz2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  obtain ⟨q, L₁, L₂, hp⟩ : ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1PSp4 G z S q L₁ L₂ := by
    cases hctx.data with
    | psp4 h => exact h
  obtain ⟨x, hx⟩ := hp.two
  obtain ⟨hzJ, L₁', L₂', hcfg⟩ := exists_cfg hz2 hCH hPerf hp.pair
  have hcen := isCentralInvolution_zbar hctx hCH hzJ
  have hGH := ghList_J hctx hne hs hn
  have hconcl := h93 ↥(generalizedFitting (HBar H)) hs hGH _ hcen q L₁' L₂' hcfg
  obtain ⟨T, hT⟩ := exists_sylow_barIn hctx hCH
  have hTcard : Nat.card ↥(T : Subgroup (HBar H)) = 2 ^ nuQ q * 2 := by
    rw [hT, card_barIn_S hctx hCH]
    exact card_S_psp4 hctx hp
  have hq5 : 5 ≤ q := by
    obtain ⟨m, hm⟩ := hp.pair.odd
    have := hp.pair.gt3
    omega
  have hxH : x ∈ H := hCH (hctx.S_le_Cen hx.x_mem)
  have hxz : ¬ IsConj z x := fun h => hx.x_nonCentral (by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have := isCentralInvolution_of_equiv (MulAut.conj c) hctx.central
    have hx' : (MulAut.conj c) z = x := by
      show c * z * c⁻¹ = x
      exact hc
    rwa [hx'] at this)
  have hJ2 : ∀ (hK : IVK.IsSp4L4U4 ↥(generalizedFitting (HBar H)) q),
      IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q ∧ FUS H := by
    intro hK
    obtain ⟨y, b, hy2, hyz, hcl, hb, hbpsp, hcard⟩ := jm_apply hctx hCH hzJ hp.pair.odd hq5 hK T hT
    have hle : Nat.card ↥((T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H)) ≤
        Nat.card ↥(T : Subgroup (HBar H)) := Subgroup.card_le_of_le inf_le_left
    rw [hcard, hTcard] at hle
    have hb2 : b = 2 := by
      have hpos : 0 < 2 ^ nuQ q := pow_pos (by norm_num) _
      have := Nat.le_of_mul_le_mul_left hle hpos
      rcases hb with rfl | rfl
      · rfl
      · omega
    subst hb2
    have hTJ : (T : Subgroup (HBar H)) ≤ generalizedFitting (HBar H) := by
      have heq : (T : Subgroup (HBar H)) ⊓ generalizedFitting (HBar H) = (T : Subgroup (HBar H)) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hTcard])
      rw [← heq]
      exact inf_le_right
    exact ⟨hbpsp.1 rfl, fus_of_J_two_classes hzmem hxH hz2 hx.x_inv hxz hx.classes T hTJ hzJ hcl⟩
  rcases hconcl with hPsp | ⟨p, f, hp', hp2, hf, hpf, h8, hm⟩ | ⟨p, f, hp', hp2, hf, hpf, h8, hm⟩ |
    ⟨p, f, hp', hp2, hf, hpf, hm⟩
  · exact (hJ2 (Or.inl hPsp)).2
  ·
    exfalso
    have hL : IVK.IsLnEps 4 ↥(generalizedFitting (HBar H)) 1 q := hpf ▸
      CFSG.GH74.GLS.Stage2.Final.isLnEps_psl_of_lieModel hm
    by_cases h4 : q % 4 = 3
    · obtain ⟨hpsp, -⟩ := hJ2 (Or.inr (Or.inl ⟨h4, hL⟩))
      exact (CFSG.GH74.GLS.Stage2.Final.ivk_PSp4_ne_LU _ q hpsp).1 hL
    · have h58 : p ^ f % 8 = 5 := by
        obtain ⟨m, hm'⟩ := hp.pair.odd
        have : q % 8 ≠ 1 := h8
        omega
      exact false_of_J_one_class hctx hCH hPerf hp.pair hx
        (CFSG.GH74.GLS.Stage2.Final.modelOneClass _ p f hp' hp2 (Or.inl ⟨h58, hm⟩))
  ·
    exfalso
    have hU : IVK.IsLnEps 4 ↥(generalizedFitting (HBar H)) (-1) q := hpf ▸
      CFSG.GH74.GLS.Stage2.Final.isLnEps_psu_of_lieModel hm
    by_cases h4 : q % 4 = 1
    · obtain ⟨hpsp, -⟩ := hJ2 (Or.inr (Or.inr ⟨h4, hU⟩))
      exact (CFSG.GH74.GLS.Stage2.Final.ivk_PSp4_ne_LU _ q hpsp).2 hU
    · have h38 : p ^ f % 8 = 3 := by
        obtain ⟨m, hm'⟩ := hp.pair.odd
        have : q % 8 ≠ 7 := h8
        omega
      exact false_of_J_one_class hctx hCH hPerf hp.pair hx
        (CFSG.GH74.GLS.Stage2.Final.modelOneClass _ p f hp' hp2 (Or.inr ⟨h38, hm⟩))
  ·
    exfalso
    exact false_of_J_one_class hctx hCH hPerf hp.pair hx (g2_one_class hp' hp2 hm)

end Psp4

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
