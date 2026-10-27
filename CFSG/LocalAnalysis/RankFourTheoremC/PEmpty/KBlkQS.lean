module

public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

open Subgroup
open scoped commutatorElement

theorem center_specialLinearGroup_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Subgroup.mem_bot]
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h0)
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

noncomputable def specialLinearEquivProjective {F : Type*} [Field F] [CharP F 2] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [QuotientGroup.ker_mk']
        exact center_specialLinearGroup_eq_bot),
      QuotientGroup.mk'_surjective _⟩

theorem benderType_of_sl {K : Type} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (φ : K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    CFSG.GH74.Uniqueness.Bender.BenderType K n 1 1 :=
  .linear n hn (φ.trans specialLinearEquivProjective)

theorem eq_top_of_quasisimple_of_sylow {Y : Type} [Group Y] [Finite Y] (N' : Subgroup Y)
    [N'.Normal] (hq : CFSG.IsQuasisimple (Y ⧸ N')) (hev : 2 ∣ Nat.card (Y ⧸ N'))
    (N0 : Subgroup Y) [N0.Normal] (T : Subgroup Y) (hTN : T ≤ N0) (hNT : N' ≤ T)
    (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) : N0 = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : Y →* Y ⧸ N' := QuotientGroup.mk' N'
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N'
  have hker : π.ker ≤ T := by
    show (QuotientGroup.mk' N').ker ≤ T
    rw [QuotientGroup.ker_mk']
    exact hNT
  set M : Subgroup (Y ⧸ N') := N0.map π with hM
  haveI : M.Normal := Subgroup.Normal.map ‹N0.Normal› π hπ
  have hTbar2 : IsPGroup 2 (T.map π) := hT2.map π
  have hTbarIdx : ¬ 2 ∣ (T.map π).index := by
    rw [Subgroup.index_map_eq T hπ hker]
    exact hTi
  have hTM : T.map π ≤ M := Subgroup.map_mono hTN
  have hperf : commutator (Y ⧸ N') = ⊤ := Group.isPerfect_def.mp hq.1
  set ρ : Y ⧸ N' →* (Y ⧸ N') ⧸ Subgroup.center (Y ⧸ N') :=
    QuotientGroup.mk' (Subgroup.center (Y ⧸ N')) with hρ
  haveI : (M.map ρ).Normal := Subgroup.Normal.map ‹M.Normal› ρ (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup ((Y ⧸ N') ⧸ Subgroup.center (Y ⧸ N')) := hq.2.1
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map ρ) with hbot | htop
    ·
      exfalso
      have hMZ : M ≤ Subgroup.center (Y ⧸ N') := by
        have h1 := (Subgroup.map_le_iff_le_comap).mp hbot.le
        rwa [MonoidHom.comap_bot, hρ, QuotientGroup.ker_mk'] at h1
      have hdvdT : 2 ∣ Nat.card (T.map π) := by
        have h1 := Subgroup.card_mul_index (T.map π)
        have h2 : 2 ∣ Nat.card (T.map π) * (T.map π).index := h1 ▸ hev
        exact ((Nat.Prime.dvd_mul Nat.prime_two).mp h2).resolve_right hTbarIdx
      have hdvdZ : 2 ∣ Nat.card (Subgroup.center (Y ⧸ N')) :=
        hdvdT.trans (Subgroup.card_dvd_of_le (hTM.trans hMZ))
      have hcomm := GL83.not_isMulCommutative_sylow_of_perfect (p := 2) hperf hdvdZ
        (hTbar2.toSylow hTbarIdx)
      apply hcomm
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exact (Subgroup.mem_center_iff.mp (hMZ (hTM a.2)) b).symm
    ·
      have hdec : ∀ k : Y ⧸ N', ∃ m ∈ M, ∃ z ∈ Subgroup.center (Y ⧸ N'), k = m * z := by
        intro k
        have hk : ρ k ∈ M.map ρ := htop ▸ Subgroup.mem_top _
        obtain ⟨m, hmM, hmk⟩ := hk
        refine ⟨m, hmM, m⁻¹ * k, ?_, by group⟩
        have := QuotientGroup.eq.mp hmk
        exact this
      rw [eq_top_iff, ← hperf, _root_.commutator_def, Subgroup.commutator_le]
      intro k₁ _ k₂ _
      obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hdec k₁
      obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hdec k₂
      have hz₁' := Subgroup.mem_center_iff.mp hz₁
      have hz₂' := Subgroup.mem_center_iff.mp hz₂
      have : ⁅m₁ * z₁, m₂ * z₂⁆ = ⁅m₁, m₂⁆ := by
        simp only [commutatorElement_def, mul_inv_rev]
        have e1 : z₁ * m₂ = m₂ * z₁ := (hz₁' m₂).symm
        have e2 : z₂ * m₁⁻¹ = m₁⁻¹ * z₂ := (hz₂' m₁⁻¹).symm
        have e3 : z₁ * z₂ = z₂ * z₁ := (hz₁' z₂).symm
        calc m₁ * z₁ * (m₂ * z₂) * (z₁⁻¹ * m₁⁻¹) * (z₂⁻¹ * m₂⁻¹)
            = m₁ * (z₁ * m₂) * z₂ * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
          _ = m₁ * (m₂ * z₁) * z₂ * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by rw [e1]
          _ = m₁ * m₂ * (z₁ * z₂ * z₁⁻¹) * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
          _ = m₁ * m₂ * z₂ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by rw [e3]; group
          _ = m₁ * m₂ * (z₂ * m₁⁻¹) * z₂⁻¹ * m₂⁻¹ := by group
          _ = m₁ * m₂ * (m₁⁻¹ * z₂) * z₂⁻¹ * m₂⁻¹ := by rw [e2]
          _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
      rw [this, commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
  refine eq_top_iff.mpr fun y _ => ?_
  have hy : π y ∈ M := hMtop ▸ Subgroup.mem_top _
  obtain ⟨n0, hn0, hn0y⟩ := hy
  have hn : n0⁻¹ * y ∈ N' := QuotientGroup.eq.mp hn0y
  have : y = n0 * (n0⁻¹ * y) := by group
  rw [this]
  exact N0.mul_mem hn0 (hTN (hNT hn))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk
