module

public import CFSG.CGT.Foote82.EF2
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hp ▸ hcomm)

private theorem map_conj_eq_self {M : Subgroup G} {ℓ : G} (hℓ : ℓ ∈ M) :
    M.map (MulAut.conj ℓ).toMonoidHom = M := by
  ext x
  refine ⟨?_, fun hx => ⟨ℓ⁻¹ * x * ℓ, mul_mem (mul_mem (inv_mem hℓ) hx) hℓ, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hℓ hy) (inv_mem hℓ)
  · show ℓ * (ℓ⁻¹ * x * ℓ) * ℓ⁻¹ = x
    group

theorem le_of_isFooteBlock_of_conj {M L₁ L K : Subgroup G} (hL₁ : IsFooteBlock M L₁)
    (hLM : L ≤ M) (hLq : CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hKperf : ⁅K, K⁆ = K) (hK2 : ¬ IsPGroup 2 K) (hKL₁ : K ≤ L₁) (hKL : K ≤ L)
    (hgen : L ≤ Subgroup.closure {g | ∃ ℓ ∈ L, ∃ k ∈ K, g = ℓ * k * ℓ⁻¹}) : L ≤ L₁ := by
  have hcent : ∀ ℓ ∈ L, L₁.map (MulAut.conj ℓ).toMonoidHom ≠ L₁ →
      L₁.map (MulAut.conj ℓ).toMonoidHom ≤ Subgroup.centralizer (L₁ : Set G) := by
    intro ℓ hℓ hne
    have hblock : IsFooteBlock M (L₁.map (MulAut.conj ℓ).toMonoidHom) := by
      simpa only [map_conj_eq_self (hLM hℓ)] using isFooteBlock_map hL₁ (MulAut.conj ℓ)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (blocks_commute hblock hL₁ hne)
  have hfix : ∀ ℓ ∈ L, L₁.map (MulAut.conj ℓ).toMonoidHom = L₁ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ℓ₀, hℓ₀, hne⟩ := hcon
    have hLA : L ≤ (L ⊓ L₁) ⊔ (L ⊓ Subgroup.centralizer (L₁ : Set G)) := by
      refine hgen.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨ℓ, hℓ, k, hk, rfl⟩
      have hkℓ : ℓ * k * ℓ⁻¹ ∈ L := mul_mem (mul_mem hℓ (hKL hk)) (inv_mem hℓ)
      have hkP : ℓ * k * ℓ⁻¹ ∈ L₁.map (MulAut.conj ℓ).toMonoidHom := ⟨k, hKL₁ hk, rfl⟩
      by_cases h : L₁.map (MulAut.conj ℓ).toMonoidHom = L₁
      · rw [h] at hkP
        exact Subgroup.mem_sup_left ⟨hkℓ, hkP⟩
      · exact Subgroup.mem_sup_right ⟨hkℓ, hcent ℓ hℓ h hkP⟩
    have hA'cent : L ⊓ Subgroup.centralizer (L₁ : Set G) ≤
        Subgroup.centralizer ((L ⊓ L₁ : Subgroup G) : Set G) :=
      fun y hy => Subgroup.centralizer_le (fun a ha => ha.2) hy.2
    have hnorm : L ≤ Subgroup.normalizer ((L ⊓ L₁ : Subgroup G) : Set G) :=
      hLA.trans (sup_le Subgroup.le_normalizer
        (hA'cent.trans (Subgroup.centralizer_le_normalizer _)))
    let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    have hKnc : ¬ (K.subgroupOf L).map π ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro hKc
      refine hK2 ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype |>.to_le ?_)
      rw [← hKperf, Subgroup.commutator_le]
      intro a ha b hb
      refine ⟨⁅(⟨a, hKL ha⟩ : ↥L), ⟨b, hKL hb⟩⁆, ?_, rfl⟩
      have h1 : π ⁅(⟨a, hKL ha⟩ : ↥L), ⟨b, hKL hb⟩⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1
          (hKc ⟨⟨a, hKL ha⟩, ha, rfl⟩) _).symm)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hAA' : ∀ a ∈ L ⊓ L₁, ∀ y ∈ L ⊓ Subgroup.centralizer (L₁ : Set G), a * y = y * a :=
      fun a ha y hy => Subgroup.mem_centralizer_iff.1 hy.2 a ha.2
    have hĀ : (((L ⊓ L₁).subgroupOf L).map π).Normal := by
      haveI : ((L ⊓ L₁).subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hnorm
      exact this.map π (QuotientGroup.mk'_surjective _)
    rcases normal_eq_top_or_le_center hLq hĀ with htop | hcen
    ·
      have hA'c : ∀ y : ↥L, (y : G) ∈ L ⊓ Subgroup.centralizer (L₁ : Set G) →
          π y ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
        intro y hy
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨a, ha, rfl⟩ : q ∈ ((L ⊓ L₁).subgroupOf L).map π := by
          rw [htop]
          exact Subgroup.mem_top q
        rw [← map_mul, ← map_mul]
        exact congrArg π (Subtype.ext (hAA' (a : G) (Subgroup.mem_subgroupOf.1 ha) (y : G) hy))
      refine hKnc ?_
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
      let ℓ' : ↥L := ⟨ℓ₀, hℓ₀⟩
      have hy : ((ℓ' * k * ℓ'⁻¹ : ↥L) : G) ∈ L ⊓ Subgroup.centralizer (L₁ : Set G) :=
        ⟨(ℓ' * k * ℓ'⁻¹).2, hcent ℓ₀ hℓ₀ hne ⟨k, hKL₁ hk', rfl⟩⟩
      have e : π k = (π ℓ')⁻¹ * π (ℓ' * k * ℓ'⁻¹) * (π ℓ')⁻¹⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [e]
      exact (inferInstance : (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).Normal).conj_mem _
        (hA'c _ hy) _
    ·
      refine hKnc ((Subgroup.map_mono fun x hx => ?_).trans hcen)
      exact Subgroup.mem_subgroupOf.2
        ⟨hKL (Subgroup.mem_subgroupOf.1 hx), hKL₁ (Subgroup.mem_subgroupOf.1 hx)⟩
  refine hgen.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨ℓ, hℓ, k, hk, rfl⟩
  have hmem : ℓ * k * ℓ⁻¹ ∈ L₁.map (MulAut.conj ℓ).toMonoidHom := ⟨k, hKL₁ hk, rfl⟩
  rwa [hfix ℓ hℓ] at hmem

theorem exists_isSylowTwoOf_normalized {C P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) :
    ∃ R : Subgroup G, IsSylowTwoOf R C ∧ P ≤ Subgroup.normalizer (R : Set G) := by
  obtain ⟨S, hS⟩ := CFSG.ComponentClassification.TwoActionInvariantSylow.subgroup C P hP hPC
  refine ⟨(S : Subgroup C).map C.subtype,
    ⟨Subgroup.map_subtype_le _, S.isPGroup'.map C.subtype, ?_⟩, hS⟩
  have hsub : ((S : Subgroup C).map C.subtype).subgroupOf C = (S : Subgroup C) :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [hsub]
  exact Sylow.not_dvd_index S

end CFSG.CGT.Foote82
