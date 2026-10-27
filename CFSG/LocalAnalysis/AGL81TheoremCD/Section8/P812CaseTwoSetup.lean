module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Omega
import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.SupCommute
import CFSG.GH74.Generic.BProg.BpGeneral

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

theorem commutator_le_of_le_centralizerSection {X : Type} [Group X] {K Q B : Subgroup X}
    (hB : B ≤ CFSG.GH74.GLS.centralizerSection K Q) : ⁅B, K⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro b hb k hk
  have h := (hB hb).2.2 k hk
  simpa only [commutatorElement_inv] using Q.inv_mem h

theorem le_centralizerSection_of_ne {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {M K L : Subgroup X} (hK : CFSG.GH74.GLS.IsPCompIn p M K)
    (hL : CFSG.GH74.GLS.IsPCompIn p M L) (hne : K ≠ L) :
    K ≤ CFSG.GH74.GLS.centralizerSection L ((CFSG.pPrimeCore p ↥L).map L.subtype) := by
  let Q : Subgroup X := (CFSG.pPrimeCore p ↥L).map L.subtype
  have hneSub : K.subgroupOf M ≠ L.subgroupOf M := by
    intro h
    apply hne
    have hmap := congrArg (Subgroup.map (Subgroup.subtype M)) h
    simpa [Subgroup.map_subgroupOf_eq_of_le hK.1,
      Subgroup.map_subgroupOf_eq_of_le hL.1] using hmap
  obtain ⟨-, hKnormL, hcomm, -⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
      p hp (K.subgroupOf M) (L.subgroupOf M) hK.2 hL.2).2 hneSub
  intro x hx
  let xM : ↥M := ⟨x, hK.1 hx⟩
  have hxMnormL : xM ∈ Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) :=
    hKnormL (Subgroup.mem_subgroupOf.mpr hx)
  have hxNormL : x ∈ Subgroup.normalizer (L : Set X) := by
    have hmem : xM ∈ (Subgroup.normalizer (L : Set X)).subgroupOf M := by
      rw [Subgroup.subgroupOf_normalizer_eq hL.1]
      exact hxMnormL
    exact Subgroup.mem_subgroupOf.mp hmem
  have hxNormQ : x ∈ Subgroup.normalizer (Q : Set X) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pPrimeCore p ↥L) hxNormL
  refine ⟨hxNormL, hxNormQ, ?_⟩
  intro l hl
  let lM : ↥M := ⟨l, hL.1 hl⟩
  have hxSub : xM ∈ K.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (by simpa using hx)
  have hlSub : lM ∈ L.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (by simpa using hl)
  have hcommM : ⁅xM, lM⁆ ∈
      (CFSG.pPrimeCore p ↥(L.subgroupOf M)).map (L.subgroupOf M).subtype := by
    have hmem := hcomm (Subgroup.commutator_mem_commutator hxSub hlSub)
    exact (Subgroup.mem_inf.mp hmem).2
  have hmap : ((CFSG.pPrimeCore p ↥(L.subgroupOf M)).map
      (L.subgroupOf M).subtype).map M.subtype = Q := by
    change (CFSG.GH74.GLS.pPrimeCoreOf p (L.subgroupOf M)).map M.subtype =
      CFSG.GH74.GLS.pPrimeCoreOf p L
    exact CFSG.GH74.Generic.BProg.map_pPrimeCoreOf_subgroupOf p hL.1
  have hval : M.subtype ⁅xM, lM⁆ = ⁅x, l⁆ := by
    rw [map_commutatorElement]
    rfl
  have hQ : ⁅x, l⁆ ∈ Q := by
    rw [← hval, ← hmap]
    exact Subgroup.mem_map_of_mem M.subtype hcommM
  simpa only [commutatorElement_inv] using Q.inv_mem hQ

theorem inf_eq_of_pRank_le_one {X : Type} [Group X] [Finite X] {K A B : Subgroup X}
    (hr : CFSG.Open.pRank 3 K ≤ 1) (hA : CFSG.Open.IsElemAbelian 3 A) (hBA : B ≤ A)
    (hBK : B ≤ K) (hB3 : Nat.card B = 3) : A ⊓ K = B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : CFSG.Open.IsElemAbelian 3 (A ⊓ K) := hA.mono inf_le_left
  have hle : B ≤ A ⊓ K := le_inf hBA hBK
  have h3le : 3 ≤ Nat.card ↥(A ⊓ K) := by
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hB3] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hE.isPGroup
  have hnle : n ≤ 1 :=
    (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) inf_le_right hE hn).trans hr
  have hcard : Nat.card ↥(A ⊓ K) = 3 := by
    rcases n with _ | n
    · exfalso
      rw [hn] at h3le
      norm_num at h3le
    · have hn1 : n + 1 = 1 := by omega
      rw [hn, hn1]
      norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hB3])).symm

theorem eq_one_of_mem_centralizerSection {X : Type} [Group X] {p : ℕ} {L₁ L₂ S : Subgroup X}
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {z : X} (hzS : z ∈ S)
    (hz₁ : z ∈ CFSG.GH74.GLS.centralizerSection L₁ ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (hz₂ : z ∈ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) : z = 1 :=
  hC z hzS (commutator_le_of_le_centralizerSection (Subgroup.zpowers_le.mpr hz₁))
    (commutator_le_of_le_centralizerSection (Subgroup.zpowers_le.mpr hz₂))

theorem closure_eq_of_not_mem_sup {X : Type} [Group X] [Finite X] {A A₁ A₂ : Subgroup X}
    (hA : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (hA₁A : A₁ ≤ A)
    (hA₂A : A₂ ≤ A) (hA₁₂ : Nat.card ↥(A₁ ⊔ A₂) = 9) {a₀ a₁ a₂ : X} (ha₀ : a₀ ∈ A)
    (ha₀' : a₀ ∉ A₁ ⊔ A₂) (ha₁ : Subgroup.zpowers a₁ = A₁)
    (ha₂ : Subgroup.zpowers a₂ = A₂) : Subgroup.closure {a₀, a₁, a₂} = A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup X := A₁ ⊔ A₂
  have hDle : D ≤ A := sup_le hA₁A hA₂A
  have hDcard : Nat.card ↥D = 9 := hA₁₂
  have hnot : a₀ ≠ 1 := fun h => ha₀' (h ▸ D.one_mem)
  have hzcard : Nat.card ↥(Subgroup.zpowers a₀) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hA.2 a₀ ha₀) hnot]
  have hdisj : D ⊓ Subgroup.zpowers a₀ = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(D ⊓ Subgroup.zpowers a₀) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_right : D ⊓ Subgroup.zpowers a₀ ≤ Subgroup.zpowers a₀)
      rwa [hzcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · have heq : D ⊓ Subgroup.zpowers a₀ = Subgroup.zpowers a₀ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hzcard])
      apply ha₀'
      have hmem : a₀ ∈ D ⊓ Subgroup.zpowers a₀ := by
        rw [heq]
        exact Subgroup.mem_zpowers a₀
      exact (Subgroup.mem_inf.mp hmem).1
  have hcomm : ∀ x ∈ D, ∀ y ∈ Subgroup.zpowers a₀, Commute x y := by
    intro x hx y hy
    exact hA.comm (hDle hx) (Subgroup.zpowers_le.mpr ha₀ hy)
  have hcard : Nat.card ↥(D ⊔ Subgroup.zpowers a₀) = 27 := by
    rw [CFSG.card_sup_eq_mul_of_commute D _ hcomm hdisj, hDcard, hzcard]
  have hsup_le : D ⊔ Subgroup.zpowers a₀ ≤ A :=
    sup_le hDle (Subgroup.zpowers_le.mpr ha₀)
  have hsup_eq : D ⊔ Subgroup.zpowers a₀ = A :=
    Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hcard, h27])
  have hgen_le : Subgroup.closure ({a₀, a₁, a₂} : Set X) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact ha₀
    · rw [hx]
      exact hA₁A (ha₁ ▸ Subgroup.mem_zpowers a₁)
    · rw [hx]
      exact hA₂A (ha₂ ▸ Subgroup.mem_zpowers a₂)
  have hA_le : A ≤ Subgroup.closure ({a₀, a₁, a₂} : Set X) := by
    rw [← hsup_eq]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [← ha₁]
      exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · rw [← ha₂]
      exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  exact le_antisymm hgen_le hA_le

namespace P812Hyp

private theorem map_conj_eq_of_mem_normalizer {X : Type} [Group X] [Finite X]
    {A K B : Subgroup X} {g : X} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBA : B ≤ A) (hBK : B ≤ K)
    (hK : CFSG.Open.pRank 3 K ≤ 1) (hgA : g ∈ Subgroup.normalizer (A : Set X))
    (hgK : g ∈ Subgroup.normalizer (K : Set X)) :
    B.map (MulAut.conj g).toMonoidHom = B := by
  have hAg : A.map (MulAut.conj g).toMonoidHom = A :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgA
  have hKg : K.map (MulAut.conj g).toMonoidHom = K :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgK
  have hinf : A ⊓ K = B := inf_eq_of_pRank_le_one hK hA hBA hBK hB3
  have hle : B.map (MulAut.conj g).toMonoidHom ≤ A ⊓ K :=
    le_inf (by rw [← hAg]; exact Subgroup.map_mono hBA)
      (by rw [← hKg]; exact Subgroup.map_mono hBK)
  rw [hinf] at hle
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB3])

private theorem map_conj_component_of_mem (h : P812Hyp G M p L₁ L₂) {g : G} (hgM : g ∈ M) :
    (L₂.map (MulAut.conj g).toMonoidHom ≤ M) ∧
      CFSG.IsPComponent p ((L₂.map (MulAut.conj g).toMonoidHom).subgroupOf M) ∧
      L₂.map (MulAut.conj g).toMonoidHom ≠ L₁ := by
  let L₂g : Subgroup G := CFSG.conjugate L₂ g⁻¹
  have hL₂g_eq : L₂g = L₂.map (MulAut.conj g).toMonoidHom := by
    simp [L₂g, CFSG.conjugate]
  have hMg : M.map (MulAut.conj g).toMonoidHom = M :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer hgM)
  have hL₂g_comp : CFSG.IsPComponent p (L₂g.subgroupOf M) := by
    have hpc := CFSG.ComponentClassification.CatFactsSp4.isPComponent_map_subgroupOf
      p (MulAut.conj g) h.le₂ h.comp₂
    rw [← hL₂g_eq, hMg] at hpc
    exact hpc
  have hL₂g_le_M : L₂g ≤ M := by
    rw [hL₂g_eq, ← hMg]
    exact Subgroup.map_mono h.le₂
  have hgN₁ : g ∈ Subgroup.normalizer (L₁ : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁) hgM
  have hconjL₂g : CFSG.conjugate L₂g g = L₂ := by
    rw [show L₂g = CFSG.conjugate L₂ g⁻¹ from rfl,
      CFSG.LocalCores.conjugate_conjugate, inv_mul_cancel]
    ext x
    simp [CFSG.conjugate, MulAut.conj_apply]
  have hconjL₁ : CFSG.conjugate L₁ g = L₁ := by
    rw [CFSG.conjugate]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.inv_mem _ hgN₁)
  have hne_l1 : L₂g ≠ L₁ := by
    intro hEq
    refine h.ne ?_
    have h2 := congrArg (fun H : Subgroup G => CFSG.conjugate H g) hEq
    rw [hconjL₂g, hconjL₁] at h2
    exact h2.symm
  exact ⟨hL₂g_eq ▸ hL₂g_le_M, hL₂g_eq ▸ hL₂g_comp, hL₂g_eq ▸ hne_l1⟩

private theorem map_conj_eq_of_not_normalizes {X : Type} [Group X] [Finite X]
    {p : ℕ} {M L₁ L₂ S A A₂ : Subgroup X} {g : X}
    (h : P812Hyp X M p L₁ L₂) (hA : CFSG.Open.IsElemAbelian 3 A) (hAS : A ≤ S)
    (hA₂ : A₂ ≤ L₂) (hA₂A : A₂ ≤ A) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hgA : g ∈ Subgroup.normalizer (A : Set X)) (hgM : g ∈ M)
    (hL₂g_ne : L₂.map (MulAut.conj g).toMonoidHom ≠ L₂) :
    A₂.map (MulAut.conj g).toMonoidHom = A₂ := by
  exfalso
  obtain ⟨hL₂g_le_M, hL₂g_comp, hne_l1⟩ := map_conj_component_of_mem h hgM
  have hL₂gC₁ : L₂.map (MulAut.conj g).toMonoidHom ≤
      CFSG.GH74.GLS.centralizerSection L₁ ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :=
    le_centralizerSection_of_ne h.prime ⟨hL₂g_le_M, hL₂g_comp⟩
      ⟨h.le₁, h.comp₁⟩ hne_l1
  have hL₂gC₂ : L₂.map (MulAut.conj g).toMonoidHom ≤
      CFSG.GH74.GLS.centralizerSection L₂ ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :=
    le_centralizerSection_of_ne h.prime ⟨hL₂g_le_M, hL₂g_comp⟩
      ⟨h.le₂, h.comp₂⟩ hL₂g_ne
  have hAg : A.map (MulAut.conj g).toMonoidHom = A :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgA
  have hA₂g_le_A : A₂.map (MulAut.conj g).toMonoidHom ≤ A := by
    rw [← hAg]
    exact Subgroup.map_mono hA₂A
  have hA₂g_le_L₂g : A₂.map (MulAut.conj g).toMonoidHom ≤
      L₂.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hA₂
  have hA₂g_S : A₂.map (MulAut.conj g).toMonoidHom ≤ S :=
    hA₂g_le_A.trans hAS
  have hbot : A₂.map (MulAut.conj g).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_centralizerSection hC
      (hA₂g_S hz) (hL₂gC₁ (hA₂g_le_L₂g hz)) (hL₂gC₂ (hA₂g_le_L₂g hz)))
  have hcardbot : Nat.card ↥(A₂.map (MulAut.conj g).toMonoidHom) = 1 := by
    rw [hbot, Subgroup.card_bot]
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA₂3] at hcardbot
  norm_num at hcardbot

theorem mem_normalizer_of_mem_normalizer (h : P812Hyp G M p L₁ L₂)
    {S A A₁ A₂ : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAS : A ≤ S)
    (hA₁ : A₁ ≤ L₁) (hA₁A : A₁ ≤ A) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂A : A₂ ≤ A) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgM : g ∈ M) :
    g ∈ Subgroup.normalizer (A₁ : Set G) ∧ g ∈ Subgroup.normalizer (A₂ : Set G) := by
  have hgN₁ : g ∈ Subgroup.normalizer (L₁ : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer h.le₁).mp h.normal₁) hgM
  have hA₁g : A₁.map (MulAut.conj g).toMonoidHom = A₁ :=
    map_conj_eq_of_mem_normalizer hA hA₁3 hA₁A hA₁ (le_of_eq h.rank_three₁) hgA hgN₁
  have hA₂g_eq : A₂.map (MulAut.conj g).toMonoidHom = A₂ := by
    by_cases hL₂g : L₂.map (MulAut.conj g).toMonoidHom = L₂
    · exact map_conj_eq_of_mem_normalizer hA hA₂3 hA₂A hA₂ (le_of_eq h.rank_three₂)
        hgA ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr hL₂g)
    · exact map_conj_eq_of_not_normalizes h hA hAS hA₂ hA₂A hA₂3 hC hgA hgM hL₂g
  exact ⟨(Subgroup.mem_normalizer_iff_map_conj_eq).mpr hA₁g,
    (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hA₂g_eq⟩

private theorem exists_outer_mem_of_mem_centralizer_left
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAS : A ≤ S) (hA₁A : A₁ ≤ A)
    (hA₂ : A₂ ≤ L₂) (hA₂A : A₂ ≤ A) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hA₂C₁ : A₂ ≤ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (hA₁C₂ : A₁ ≤ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b)
    {a₀ : G} (ha₀A : a₀ ∈ A)
    (ha₀C₁ : a₀ ∈ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (ha₀A₂ : a₀ ∉ A₂) :
    ∃ a₀ ∈ A, a₀ ∉ A₁ ⊔ A₂ ∧
      a₀ ∈ CFSG.GH74.GLS.centralizerSection L₁
        ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) ∧
      a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
        ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) := by
  let C₁ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₁
    ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
  let C₂ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₂
    ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
  have ha₀C₁' : a₀ ∈ C₁ := ha₀C₁
  have hA₁S : A₁ ≤ S := hA₁A.trans hAS
  have hA₂S : A₂ ≤ S := hA₂A.trans hAS
  have hnot : a₀ ∉ A₁ ⊔ A₂ := by
    intro hmem
    obtain ⟨a₁, ha₁A₁, a₂, ha₂A₂, ha₁₂⟩ := (CFSG.mem_sup_of_commute hcomm).mp hmem
    have ha₁eq : a₁ = a₀ * a₂⁻¹ := by
      rw [← ha₁₂]
      group
    have ha₁C₁ : a₁ ∈ C₁ := by
      rw [ha₁eq]
      exact C₁.mul_mem ha₀C₁' (C₁.inv_mem (hA₂C₁ ha₂A₂))
    have ha₁C₂ : a₁ ∈ C₂ := hA₁C₂ ha₁A₁
    have ha₁1 : a₁ = 1 :=
      eq_one_of_mem_centralizerSection hC (hA₁S ha₁A₁) ha₁C₁ ha₁C₂
    rw [ha₁1, one_mul] at ha₁₂
    rw [ha₁₂] at ha₂A₂
    exact ha₀A₂ ha₂A₂
  have hnotL : a₀ ∉ L₂ ⊔ C₂ := by
    intro hmem
    obtain ⟨a₂, ha₂A₂, ha₂C₂⟩ :=
      h.mem_centralizerSection_of_mem_sup₂ hSch hSM hS3 hA₂ hA₂S hA₂3
        (hAS ha₀A) (hA.2 a₀ ha₀A) hmem
    have hz : a₀ * a₂⁻¹ = 1 :=
      eq_one_of_mem_centralizerSection hC
        (S.mul_mem (hAS ha₀A) (S.inv_mem (hA₂S ha₂A₂)))
        (C₁.mul_mem ha₀C₁' (C₁.inv_mem (hA₂C₁ ha₂A₂))) ha₂C₂
    have heq : a₀ = a₂ := by
      have h := congrArg (fun z => z * a₂) hz
      simpa [mul_assoc] using h
    exact ha₀A₂ (by simpa [heq] using ha₂A₂)
  exact ⟨a₀, ha₀A, hnot, ha₀C₁, hnotL⟩

private theorem exists_outer_mem_of_mem_centralizer_right
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAS : A ≤ S)
    (hA₁ : A₁ ≤ L₁) (hA₁A : A₁ ≤ A) (hA₁3 : Nat.card A₁ = 3) (hA₂A : A₂ ≤ A)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (hA₂C₁ : A₂ ≤ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype))
    (hA₁C₂ : A₁ ≤ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))
    {a₀ : G} (ha₀A : a₀ ∈ A)
    (ha₀C₂ : a₀ ∈ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))
    (ha₀A₁ : a₀ ∉ A₁) :
    ∃ a₀ ∈ A, a₀ ∉ A₁ ⊔ A₂ ∧
      a₀ ∈ CFSG.GH74.GLS.centralizerSection L₂
        ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) ∧
      a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
        ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) := by
  let C₁ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₁
    ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
  let C₂ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₂
    ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
  have hnot : a₀ ∉ A₁ ⊔ A₂ := by
    intro hmem
    rw [sup_comm] at hmem
    obtain ⟨a₂, ha₂A₂, a₁, ha₁A₁, ha₂₁⟩ :=
      (CFSG.mem_sup_of_commute (fun a ha b hb =>
        hA.comm (hA₂A ha) (hA₁A hb))).mp hmem
    have ha₂eq : a₂ = a₀ * a₁⁻¹ := by
      rw [← ha₂₁]
      group
    have ha₂C₂ : a₂ ∈ C₂ := by
      rw [ha₂eq]
      exact C₂.mul_mem ha₀C₂ (C₂.inv_mem (hA₁C₂ ha₁A₁))
    have ha₂C₁ : a₂ ∈ C₁ := hA₂C₁ ha₂A₂
    have ha₂1 : a₂ = 1 :=
      eq_one_of_mem_centralizerSection hC ((hA₂A.trans hAS) ha₂A₂) ha₂C₁ ha₂C₂
    rw [ha₂1, one_mul] at ha₂₁
    rw [ha₂₁] at ha₁A₁
    exact ha₀A₁ ha₁A₁
  have hnotL : a₀ ∉ L₁ ⊔ C₁ := by
    intro hmem
    obtain ⟨a₁, ha₁A₁, ha₁C₁⟩ :=
      h.mem_centralizerSection_of_mem_sup₁ hSch hSM hS3 hA₁ (hA₁A.trans hAS) hA₁3
        (hAS ha₀A) (hA.2 a₀ ha₀A) hmem
    have hz : a₀ * a₁⁻¹ = 1 :=
      eq_one_of_mem_centralizerSection hC
        (S.mul_mem (hAS ha₀A) (S.inv_mem ((hA₁A.trans hAS) ha₁A₁)))
        ha₁C₁
        (C₂.mul_mem ha₀C₂ (C₂.inv_mem (hA₁C₂ ha₁A₁)))
    have heq : a₀ = a₁ := by
      have h := congrArg (fun z => z * a₁) hz
      simpa [mul_assoc] using h
    exact ha₀A₁ (by simpa [heq] using ha₁A₁)
  exact ⟨a₀, ha₀A, hnot, ha₀C₂, hnotL⟩

private theorem not_mem_sup_centralizerSection_of_outer
    (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAS : A ≤ S)
    (hA₁ : A₁ ≤ L₁) (hA₁A : A₁ ≤ A) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂A : A₂ ≤ A) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    (h₁ : A ⊓ CFSG.GH74.GLS.centralizerSection L₁
        ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) ≤ A₂)
    (h₂ : A ⊓ CFSG.GH74.GLS.centralizerSection L₂
        ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) ≤ A₁)
    {x : G} (hxA : x ∈ A) (hx : x ∉ A₁ ⊔ A₂) :
    x ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
        ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) ∧
      x ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
        ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) := by
  let C₁ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₁
    ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
  let C₂ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₂
    ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
  have hle₁ : A ⊓ C₁ ≤ A₂ := h₁
  have hle₂ : A ⊓ C₂ ≤ A₁ := h₂
  have hA₁S : A₁ ≤ S := hA₁A.trans hAS
  have hA₂S : A₂ ≤ S := hA₂A.trans hAS
  refine ⟨?_, ?_⟩
  · intro hxL
    obtain ⟨a₁, ha₁A₁, ha₁C₁⟩ :=
      h.mem_centralizerSection_of_mem_sup₁ hSch hSM hS3 hA₁ hA₁S hA₁3
        (hAS hxA) (hA.2 x hxA) hxL
    have hmemA : x * a₁⁻¹ ∈ A :=
      A.mul_mem hxA (A.inv_mem (hA₁A ha₁A₁))
    have hmemA₂ : x * a₁⁻¹ ∈ A₂ := hle₁ ⟨hmemA, ha₁C₁⟩
    have hsup : x ∈ A₂ ⊔ A₁ := by
      simpa [mul_assoc] using Subgroup.mul_mem_sup hmemA₂ ha₁A₁
    rw [sup_comm] at hsup
    exact hx hsup
  · intro hxL
    obtain ⟨a₂, ha₂A₂, ha₂C₂⟩ :=
      h.mem_centralizerSection_of_mem_sup₂ hSch hSM hS3 hA₂ hA₂S hA₂3
        (hAS hxA) (hA.2 x hxA) hxL
    have hmemA : x * a₂⁻¹ ∈ A :=
      A.mul_mem hxA (A.inv_mem (hA₂A ha₂A₂))
    have hmemA₁ : x * a₂⁻¹ ∈ A₁ := hle₂ ⟨hmemA, ha₂C₂⟩
    have hsup : x ∈ A₁ ⊔ A₂ := by
      simpa [mul_assoc] using Subgroup.mul_mem_sup hmemA₁ ha₂A₂
    exact hx hsup

theorem exists_outer_mem (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAS : A ≤ S)
    (hA₁ : A₁ ≤ L₁) (hA₁A : A₁ ≤ A) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂A : A₂ ≤ A) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {x : G} (hxA : x ∈ A) (hx : x ∉ A₁ ⊔ A₂) :
    ∃ a₀ ∈ A, a₀ ∉ A₁ ⊔ A₂ ∧
      ((a₀ ∈ CFSG.GH74.GLS.centralizerSection L₁
          ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) ∧
          a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
            ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)) ∨
        (a₀ ∈ CFSG.GH74.GLS.centralizerSection L₂
            ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) ∧
          a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
            ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)) ∨
        (a₀ ∉ L₁ ⊔ CFSG.GH74.GLS.centralizerSection L₁
            ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) ∧
          a₀ ∉ L₂ ⊔ CFSG.GH74.GLS.centralizerSection L₂
            ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype))) := by
  have hA₂C₁ : A₂ ≤ CFSG.GH74.GLS.centralizerSection L₁
      ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype) :=
    hA₂.trans (le_centralizerSection_of_ne h.prime ⟨h.le₂, h.comp₂⟩
      ⟨h.le₁, h.comp₁⟩ h.ne.symm)
  have hA₁C₂ : A₁ ≤ CFSG.GH74.GLS.centralizerSection L₂
      ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype) :=
    hA₁.trans (le_centralizerSection_of_ne h.prime ⟨h.le₁, h.comp₁⟩
      ⟨h.le₂, h.comp₂⟩ h.ne)
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, Commute a b := fun a ha b hb =>
    hA.comm (hA₁A ha) (hA₂A hb)
  let C₁ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₁
    ((CFSG.pPrimeCore p ↥L₁).map L₁.subtype)
  let C₂ : Subgroup G := CFSG.GH74.GLS.centralizerSection L₂
    ((CFSG.pPrimeCore p ↥L₂).map L₂.subtype)
  by_cases h₁ : ∃ a₀ ∈ A, a₀ ∈ C₁ ∧ a₀ ∉ A₂
  · obtain ⟨a₀, ha₀A, ha₀C₁, ha₀A₂⟩ := h₁
    obtain ⟨b₀, hb₀A, hnot, hb₀C₁, hnotL⟩ :=
      exists_outer_mem_of_mem_centralizer_left h hSch hSM hS3 hA hAS hA₁A hA₂ hA₂A hA₂3
        hC hA₂C₁ hA₁C₂ hcomm ha₀A ha₀C₁ ha₀A₂
    exact ⟨b₀, hb₀A, hnot, Or.inl ⟨hb₀C₁, hnotL⟩⟩
  · by_cases h₂ : ∃ a₀ ∈ A, a₀ ∈ C₂ ∧ a₀ ∉ A₁
    · obtain ⟨a₀, ha₀A, ha₀C₂, ha₀A₁⟩ := h₂
      obtain ⟨b₀, hb₀A, hnot, hb₀C₂, hnotL⟩ :=
        exists_outer_mem_of_mem_centralizer_right h hSch hSM hS3 hA hAS hA₁ hA₁A hA₁3
          hA₂A hC hA₂C₁ hA₁C₂ ha₀A ha₀C₂ ha₀A₁
      exact ⟨b₀, hb₀A, hnot, Or.inr (Or.inl ⟨hb₀C₂, hnotL⟩)⟩
    · push Not at h₁ h₂
      have hle₁ : A ⊓ C₁ ≤ A₂ := fun a ha => h₁ a ha.1 ha.2
      have hle₂ : A ⊓ C₂ ≤ A₁ := fun a ha => h₂ a ha.1 ha.2
      obtain ⟨hnotL₁, hnotL₂⟩ :=
        not_mem_sup_centralizerSection_of_outer h hSch hSM hS3 hA hAS hA₁ hA₁A hA₁3
          hA₂ hA₂A hA₂3 hC hle₁ hle₂ hxA hx
      exact ⟨x, hxA, hx, Or.inr (Or.inr ⟨hnotL₁, hnotL₂⟩)⟩

theorem card_sup_eq_nine (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {S A₁ A₂ : Subgroup G} (hS3 : IsPGroup 3 S)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3) :
    Nat.card ↥(A₁ ⊔ A₂) = 9 := by
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    h.commute_of_isPGroup hSch hS3 ⟨hA₁S ha, hA₁ ha⟩ ⟨hA₂S hb, hA₂ hb⟩
  have hbot : A₁ ⊓ A₂ = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(A₁ ⊓ A₂) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : A₁ ⊓ A₂ ≤ A₁)
      rwa [hA₁3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · have heq : A₁ ⊓ A₂ = A₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hA₁3])
      have hleA₂ : A₁ ≤ A₂ := by
        rw [← heq]
        exact inf_le_right
      exact h.not_le_two hSch hA₁ hA₁3 (hleA₂.trans hA₂)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hcomm).1
  rw [hbot, hA₁3, hA₂3] at hcard
  simpa using hcard

end P812Hyp

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
