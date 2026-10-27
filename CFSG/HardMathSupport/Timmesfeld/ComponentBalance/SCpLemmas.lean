module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem exists_ne_one_mem_sylow_inf_normal {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] (N : Subgroup M) [N.Normal] (hdvd : p ∣ Nat.card N) (S : Sylow p M) :
    ∃ x ∈ (S : Subgroup M) ⊓ N, x ≠ 1 := by
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hh' : orderOf (h : M) = p := by rw [Subgroup.orderOf_coe]; exact hh
  have hpg : IsPGroup p (Subgroup.zpowers (h : M)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hh', pow_one]
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S Q
  have hmem : (h : M) ∈ ((g • S : Sylow p M) : Subgroup M) := hg ▸ hQ (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  refine ⟨(MulAut.conj g)⁻¹ • (h : M), ⟨hmem, ?_⟩, ?_⟩
  · have h1 := (inferInstance : N.Normal).conj_mem (h : M) h.2 g⁻¹
    simpa [MulAut.inv_apply, MulAut.conj_apply] using h1
  · intro h1
    have h3 : g⁻¹ * (h : M) * g = 1 := by
      simpa [MulAut.inv_apply, MulAut.conj_apply] using h1
    have h2 : (h : M) = 1 := by
      calc (h : M) = g * (g⁻¹ * (h : M) * g) * g⁻¹ := by group
        _ = 1 := by rw [h3]; group
    rw [h2, orderOf_one] at hh'
    exact (Fact.out : p.Prime).one_lt.ne hh'

theorem exists_ne_one_mem_inf_of_isSCp {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {B H : Subgroup X} (hB : IsSCp p ⊤ B) (hBH : B ≤ Subgroup.normalizer (H : Set X))
    (hdvd : p ∣ Nat.card H) : ∃ x ∈ B ⊓ H, x ≠ 1 := by
  set M : Subgroup X := H ⊔ B with hM
  have hHM : H ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMnorm : M ≤ Subgroup.normalizer (H : Set X) :=
    sup_le Subgroup.le_normalizer hBH
  have hN : (H.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).2 hMnorm
  have hdvd' : p ∣ Nat.card (H.subgroupOf M) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv]
  have hBp : IsPGroup p (B.subgroupOf M) := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (Subtype.ext (hB.2.1.2 g.1.1 g.2))
  obtain ⟨S, hS⟩ := hBp.exists_le_sylow
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_mem_sylow_inf_normal (H.subgroupOf M) hdvd' S
  have hSnil : Group.IsNilpotent ↥(S : Subgroup M) := S.isPGroup'.isNilpotent
  set N' : Subgroup ↥(S : Subgroup M) := (H.subgroupOf M).subgroupOf (S : Subgroup M) with hN'
  have hN'n : N'.Normal := hN.subgroupOf _
  have hN'ne : N' ≠ ⊥ := by
    intro hbot
    have hmem : (⟨x, hx.1⟩ : ↥(S : Subgroup M)) ∈ N' := hx.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 (congrArg Subtype.val hmem)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  have hzp : IsPGroup p ↥(S : Subgroup M) := S.isPGroup'
  have hnt : Nontrivial ↥(N' ⊓ Subgroup.center ↥(S : Subgroup M)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hcen
  have hpZ : IsPGroup p ↥(N' ⊓ Subgroup.center ↥(S : Subgroup M)) := hzp.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := hpZ.nontrivial_iff_card.1 hnt
  have hdvdZ : p ∣ Nat.card ↥(N' ⊓ Subgroup.center ↥(S : Subgroup M)) := by
    rw [hn]; exact dvd_pow_self p hn0.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvdZ
  have hwS : orderOf ((w : ↥(S : Subgroup M)) : M) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  set w' : X := (((w : ↥(S : Subgroup M)) : M) : X) with hw'
  have hw'ord : orderOf w' = p := by
    rw [hw', Subgroup.orderOf_coe, hwS]
  have hwH : w' ∈ H := (Subgroup.mem_subgroupOf).1 (w.2.1)
  have hwcent : w' ∈ Subgroup.centralizer (B : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbM : b ∈ M := hBM hb
    have hbS : (⟨b, hbM⟩ : M) ∈ (S : Subgroup M) := hS ((Subgroup.mem_subgroupOf).2 hb)
    have hc := Subgroup.mem_center_iff.1 w.2.2 ⟨⟨b, hbM⟩, hbS⟩
    have := congrArg (fun y : ↥(S : Subgroup M) => ((y : M) : X)) hc
    simpa using this
  have hwB : w' ∈ B := mem_of_mem_centralizer_orderOf_eq_prime hB hwcent hw'ord
  refine ⟨w', ⟨hwB, hwH⟩, ?_⟩
  intro h1
  rw [h1, orderOf_one] at hw'ord
  exact (Fact.out : p.Prime).one_lt.ne hw'ord

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
