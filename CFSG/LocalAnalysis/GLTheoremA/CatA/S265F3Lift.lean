module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Step
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup comm_mem_fixSubgroup
  exists_glaPComponent_map_central)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem ker_chevQuotHom_le_center' {p : ℕ} {S : Subgroup Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) : (chevQuotHom p S).ker ≤ Subgroup.center ↥S := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro s
  have hx' : pQuotHom p S x ∈ Subgroup.center (PQuot p S) := by
    rw [MonoidHom.mem_ker] at hx
    have h : (QuotientGroup.mk' (Subgroup.center (PQuot p S))) (pQuotHom p S x) = 1 := hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hc : pQuotHom p S (s * x * s⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      Subgroup.mem_center_iff.1 hx' (pQuotHom p S s)]
    group
  have hk : s * x * s⁻¹ * x⁻¹ ∈ (pQuotHom p S).ker := hc
  rw [ker_pQuotHom, hcore, Subgroup.mem_bot] at hk
  calc s * x = s * x * s⁻¹ * x⁻¹ * x * s := by group
    _ = x * s := by rw [hk]; group

private theorem comp_ne_bot {G : Type} [Group G] {p : ℕ} {X L : Subgroup G}
    (h : GLAPComponent p X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem glaPLayer_inf_cx_ne_bot_of_fix {p : ℕ} (hp : p.Prime) {S : Subgroup Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) {a c : Ω} (ha : a ∈ Subgroup.normalizer (S : Set Ω))
    (hc : c ∈ Subgroup.normalizer (S : Set Ω))
    (h : GLAPLayer p (fixSubgroup (chevAut p S ⟨a, ha⟩) ⊓ fixSubgroup (chevAut p S ⟨c, hc⟩)) ≠ ⊥) :
    GLAPLayer p (S ⊓ cx a ⊓ cx c) ≠ ⊥ := by
  have hker := ker_chevQuotHom_le_center' hcore
  have hπ : Function.Surjective (chevQuotHom p S) := chevQuotHom_surjective p S
  have hαa : ∀ k, chevQuotHom p S (S.normalizerMonoidHom ⟨a, ha⟩ k) =
      chevAut p S ⟨a, ha⟩ (chevQuotHom p S k) := fun k => (chevAut_chevQuotHom p S _ k).symm
  have hαc : ∀ k, chevQuotHom p S (S.normalizerMonoidHom ⟨c, hc⟩ k) =
      chevAut p S ⟨c, hc⟩ (chevQuotHom p S k) := fun k => (chevAut_chevQuotHom p S _ k).symm
  have hH : fixSubgroup (S.normalizerMonoidHom ⟨a, ha⟩) ⊓ fixSubgroup (S.normalizerMonoidHom ⟨c, hc⟩) =
      (S ⊓ cx a ⊓ cx c).subgroupOf S := by
    ext k
    rw [Subgroup.mem_inf, fixSubgroup_normalizerMonoidHom ha, fixSubgroup_normalizerMonoidHom hc,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf]
    tauto
  obtain ⟨A, hA⟩ : ∃ A, GLAPComponent p
      (fixSubgroup (chevAut p S ⟨a, ha⟩) ⊓ fixSubgroup (chevAut p S ⟨c, hc⟩)) A := by
    by_contra hne
    push Not at hne
    exact h (sSup_eq_bot.2 fun J hJ => absurd hJ (hne J))
  have hAperf := glaPComponent_perfect hA
  have hAH : A ≤ ((S ⊓ cx a ⊓ cx c).subgroupOf S).map (chevQuotHom p S) := by
    rw [← hH]
    conv_lhs => rw [← hAperf]
    rw [Subgroup.commutator_le]
    intro a₁ ha₁ a₂ ha₂
    obtain ⟨k₁, rfl⟩ := hπ a₁
    obtain ⟨k₂, rfl⟩ := hπ a₂
    exact ⟨⁅k₁, k₂⁆, ⟨comm_mem_fixSubgroup _ hker _ _ hαa (hA.1 ha₁).1 (hA.1 ha₂).1,
      comm_mem_fixSubgroup _ hker _ _ hαc (hA.1 ha₁).2 (hA.1 ha₂).2⟩, map_commutatorElement _ _ _⟩
  have hHF : ((S ⊓ cx a ⊓ cx c).subgroupOf S).map (chevQuotHom p S) ≤
      fixSubgroup (chevAut p S ⟨a, ha⟩) ⊓ fixSubgroup (chevAut p S ⟨c, hc⟩) := by
    rw [← hH]
    rintro _ ⟨k, hk, rfl⟩
    have hk' := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show chevAut p S ⟨a, ha⟩ (chevQuotHom p S k) = chevQuotHom p S k
      rw [← hαa, mem_fixSubgroup.1 hk'.1]
    · show chevAut p S ⟨c, hc⟩ (chevQuotHom p S k) = chevQuotHom p S k
      rw [← hαc, mem_fixSubgroup.1 hk'.2]
  have hA' := glaPComponent_of_le hp hA hAH hHF
  obtain ⟨J, hJ, hJA⟩ := exists_glaPComponent_map_central hp (chevQuotHom p S)
    (fun y hy x _ => Subgroup.mem_center_iff.1 (hker hy.2) x) hA'
  have hJΩ := glaPComponent_map hp S.subtype
    (by rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]; exact Nat.coprime_one_right p) hJ
  rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans inf_le_left)] at hJΩ
  intro hbot
  have hle : J.map S.subtype ≤ GLAPLayer p (S ⊓ cx a ⊓ cx c) := le_sSup hJΩ
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective] at hle
  apply comp_ne_bot hA
  rw [← hJA, hle, Subgroup.map_bot]

theorem exists_e3_of_layer {p : ℕ} (hp : p.Prime) {B S : Subgroup Ω} {x b e : Ω}
    (hB : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hSx : S ≤ Subgroup.centralizer ({x} : Set Ω))
    (hb : b ∈ B) (hbx : b ∉ Subgroup.zpowers x) (heB : e ∈ B) (heD : e ∉ Dgrp b x)
    (hne : GLAPLayer p (S ⊓ cx b ⊓ cx e) ≠ ⊥) :
    ∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
      GLAPLayer p (S ⊓ cs E) ≠ ⊥ := by
  haveI := Fact.mk hp
  have hzx : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hxB
  have hDB : Dgrp b x ≤ B := by
    rw [dgrp_eq]
    exact sup_le hzx (Subgroup.zpowers_le.2 hb)
  have hordx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 x hxB) hx1]
  have hordb : Nat.card (Subgroup.zpowers b) = p := by
    have hb1 : b ≠ 1 := fun h => hbx (h ▸ (Subgroup.zpowers x).one_mem)
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 b hb) hb1]
  have hcard : Nat.card ↥(Dgrp b x) = p ^ 2 := by
    rw [dgrp_eq]
    exact s265_card_sup hp hB hzx (by rw [hordx, pow_one]) hb hbx hordb
  have hne' : GLAPLayer p ((S ⊓ Subgroup.centralizer ((Dgrp b x : Subgroup Ω) : Set Ω)) ⊓
      Subgroup.centralizer ({e} : Set Ω)) ≠ ⊥ := by
    rw [inf_cs_dgrp hSx]
    exact hne
  obtain ⟨E, ⟨h1, h2, h3⟩, h4, h5⟩ := s265_stepB_gen hp hB hDB hcard le_rfl (IsSubnormal.refl _)
    heB heD hne'
  exact ⟨E, h1, h2, h3, h4, h5⟩

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
