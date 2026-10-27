module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.YData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.ModuleFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section
open scoped Pointwise
variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem Hyp2813.module_conclusions (h : Hyp2813 X K R P) (hS : pCoreOf 2 P ≠ ⊥)
    {ψ : ↥X →* GL32} (hψs : Function.Surjective ψ) (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X)
    {N : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N] {ι : ↥(TT X) → N}
    (hι : IsTBridge X ψ ι) (hN2 : ∀ n : N, n + n = 0)
    {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M] {π : N →+ M}
    (hπs : Function.Surjective π) (hπk : ∀ n, π n = 0 ↔ n ∈ fixSub N ⊤)
    (hπe : ∀ (g : GL32) (n : N), π (g • n) = g • π n) (hM2 : ∀ m : M, m + m = 0)
    (hM0 : ∀ m : M, (∀ g : GL32, g • m = m) → m = 0)
    {D : Subgroup A} {d₀ : A} (hDX : D ≤ X) (hd₀D : d₀ ∈ D) (hd₀3 : orderOf d₀ = 3)
    (hdP : d₀ ∈ P) :
    Nat.card (commSub M (zpowers (ψ ⟨d₀, hDX hd₀D⟩))) ≤ 16 ∧
    Nat.card (fixSub M (Hbar X ψ (pCoreOf 2 P) ⊔ zpowers (ψ ⟨d₀, hDX hd₀D⟩))) ≤ 2 ∧
    ((∃ m ∈ fixSub M (Hbar X ψ (pCoreOf 2 P)), (ψ ⟨d₀, hDX hd₀D⟩) • m ≠ m) →
      fixSub M (Hbar X ψ (pCoreOf 2 P) ⊔ zpowers (ψ ⟨d₀, hDX hd₀D⟩)) = ⊥) := by
  classical
  obtain ⟨t, htT, htT0⟩ := h.exists_TT_not_T0 hS
  have hne : ∃ m : M, m ≠ 0 := by
    refine ⟨π (ι ⟨t, htT⟩), fun h0 => htT0 ?_⟩
    exact (hι.mem_fixSub_top_iff hψs ⟨t, htT⟩).1 ((hπk _).1 h0)
  obtain ⟨A₀, hA₀, hA₀Q⟩ := h.exists_offender hS
  have hA₀S : A₀ ≤ pCoreOf 2 P := hA₀.1
  have hSP : pCoreOf 2 P ≤ P := pCoreOf_le_self P
  have hA₀X : A₀ ≤ X := hA₀S.trans (hSP.trans h.P_le)
  have hNoff := h.offender_N hS hψs hψk hι hA₀
  have hMoff : Nat.card M ≤ Nat.card (Hbar X ψ A₀) * Nat.card (fixSub M (Hbar X ψ A₀)) := by
    have h1 := quot_index_le hπs hπk hπe (Hbar X ψ A₀)
    have hpos : 0 < Nat.card (fixSub N (Hbar X ψ A₀)) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card M * Nat.card (fixSub N (Hbar X ψ A₀))
        ≤ Nat.card N * Nat.card (fixSub M (Hbar X ψ A₀)) := h1
      _ ≤ (Nat.card (Hbar X ψ A₀) * Nat.card (fixSub N (Hbar X ψ A₀))) *
            Nat.card (fixSub M (Hbar X ψ A₀)) := Nat.mul_le_mul_right _ hNoff
      _ = Nat.card (Hbar X ψ A₀) * Nat.card (fixSub M (Hbar X ψ A₀)) *
            Nat.card (fixSub N (Hbar X ψ A₀)) := by ring
  have hS2 : IsPGroup 2 (pCoreOf 2 P) := isPGroup_pCoreOf P
  have hSb2 : IsPGroup 2 (Hbar X ψ (pCoreOf 2 P)) := Hbar_isPGroup X ψ hS2
  have hdbar3 : orderOf (ψ ⟨d₀, hDX hd₀D⟩) = 3 := dbar_order X hψk (hDX hd₀D) hd₀3
  have hnorm : ψ ⟨d₀, hDX hd₀D⟩ ∈ normalizer (Hbar X ψ (pCoreOf 2 P) : Set GL32) :=
    dbar_mem_normalizer X ψ h.P_le hdP
  have hAb0ne : Hbar X ψ A₀ ≠ ⊥ := Hbar_ne_bot X hψk hA₀X hA₀Q
  have hSbne : Hbar X ψ (pCoreOf 2 P) ≠ ⊥ := fun hbot =>
    hAb0ne (le_bot_iff.1 (hbot ▸ Hbar_mono X ψ hA₀S))
  obtain ⟨hcard4, hsq⟩ := two_group_normalized_card hSb2 hSbne hdbar3 hnorm
  obtain ⟨p, hp, hSp⟩ := klein_classification hcard4 hsq
  have hoff := offender_to_Sbar hM2 hM0 hne hcard4 hsq (Hbar_mono X ψ hA₀S) hAb0ne hMoff
  exact ct_final hM2 hM0 hne hp hSp hdbar3 hnorm hoff

end

theorem kFactLemma2813_holds : KFactLemma2813 := by
  intro A _ _ X K R P b hchar hKX hKnorm hKperf hXeq hquot hRX hR2 hRsyl hRP hPX hPidx hnofact D
    hDP hD3 hDi
  have h : Hyp2813 X K R P :=
    ⟨hchar, hKX, hKnorm, hKperf, hXeq, hquot, hRX, hR2, hRsyl, hRP, hPX, hPidx, hnofact⟩
  by_cases hS : pCoreOf 2 P = ⊥
  · have hV : omegaCenter (pCoreOf 2 P) = ⊥ := by
      rw [hS]
      refine bot_unique fun g hg => ?_
      obtain ⟨hgb, -, -⟩ := mem_omegaCenter.1 hg
      exact hgb
    rw [hV]
    refine ⟨?_, ?_, ?_⟩
    · have : (⁅(⊥ : Subgroup A), D⁆ : Subgroup A) = ⊥ := Subgroup.commutator_bot_left D
      rw [this]
      simp
    · intro _ _ v hv
      rw [Subgroup.mem_bot] at hv
      simp [hv]
    · intro _ _ _ _ _ B' _ _ _ _ v hv
      rw [Subgroup.mem_bot] at hv
      simp [hv]
  · obtain ⟨ψ, hψs, hψk⟩ := h.exists_psi
    obtain ⟨N, _, _, _, ι, hι, hN2⟩ := h.exists_Tmod hψs hψk
    obtain ⟨M, _, _, _, π, hπs, hπk, hπe, hM2, hM0⟩ := exists_quot_module hN2
    obtain ⟨d₀, hd₀D, hDgen, hd₀3⟩ := h.D_cyclic hDP hD3 hDi
    have hDX : D ≤ X := hDP.trans hPX
    obtain ⟨hi, hii, hiii⟩ := h.module_conclusions hS hψs hψk hι hN2 hπs hπk hπe hM2 hM0 hDX hd₀D
      hd₀3 (hDP hd₀D)
    refine ⟨h.card_comm_le hψs hψk hι hN2 hπk hπe hDX hd₀D hDgen hd₀3 hi, ?_, ?_⟩
    ·
      intro hY hnotX v hv hvD x hx
      have hex : ∃ z ∈ omegaCenter R, ∃ d ∈ D, z * d ≠ d * z := by
        by_contra hcon
        push Not at hcon
        have hRle : R ≤ centralizer ((omegaCenter R : Subgroup A) : Set A) := fun r hr =>
          Subgroup.mem_centralizer_iff.2 fun z hz => (mem_omegaCenter.1 hz).2.1 r hr
        have hDle : D ≤ centralizer ((omegaCenter R : Subgroup A) : Set A) := fun d hd =>
          Subgroup.mem_centralizer_iff.2 fun z hz => hcon z hz d hd
        have hPle : P ≤ centralizer ((omegaCenter R : Subgroup A) : Set A) := by
          rw [← h.P_eq_sup hDP hD3 hDi]
          exact sup_le hRle hDle
        have hYP : P ≤ X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) :=
          le_inf hPX hPle
        rcases h.maximal_P hYP inf_le_left with hYeq | hYeq
        · exact hY hYeq
        · exact hnotX (hYeq ▸ inf_le_right)
      obtain ⟨z, hz, hzD⟩ := hex
      have hv0 := h.V1_le_T0 hψs hψk hι hN2 hπk hπe hDX hd₀D hDgen hd₀3 hiii hz hzD hv hvD
      exact ((mem_T0_iff X).1 hv0).2 x hx |>.symm
    ·
      intro _ hb hb3 hbK hbx B' hB'le hB'3 hDB' hB'i v hv hvD y hy x hx
      obtain ⟨hyX, hyS, hyD⟩ := h.y_data hDP hD3 hDi hb hb3 hbK hbx hB'le hB'3 hDB' hB'i y hy
      have hc0 := h.comm_mem_T0 hψs hψk hι hN2 hπk hπe hDX hd₀D hDgen hd₀3 hii hyX hyS hyD hv hvD
      exact ((mem_T0_iff X).1 hc0).2 x hx |>.symm

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
