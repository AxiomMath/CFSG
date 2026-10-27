module

public import CFSG.ClassicalInvolution.SmallCases.NDBCRes
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyEdge
import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnConj

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.Dichotomy (involutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace Cover

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem eq_of_modOdd_eq {J J' : Subgroup G} {w : G} (hJ : IsClassicalMember p f J w)
    (hJ' : IsClassicalMember p f J' w) (h : modOdd w J = modOdd w J') : J = J' := by
  have hsup := sup_involutionOddCore_eq_of_modOdd_eq (isSubnormal_le hJ.subnormal)
    (isSubnormal_le hJ'.subnormal) h
  have hc := isCanonical_of_isClassicalMember hJ
  have hc' := isCanonical_of_isClassicalMember hJ'
  unfold IsCanonical at hc hc'
  rw [← hc, hsup, hc']

theorem modOdd_le_of_forall_exists {L₁ L₂ : Subgroup G} {w : G}
    (h₂ : L₂ ≤ Subgroup.centralizer ({w} : Set G))
    (h : ∀ x ∈ L₁, ∃ k ∈ L₂, k⁻¹ * x ∈ componentClassificationOddCore G) :
    modOdd w L₁ ≤ modOdd w L₂ := by
  rintro _ ⟨⟨x, hxC⟩, hx, rfl⟩
  obtain ⟨k, hk, hko⟩ := h x hx
  have hkC := h₂ hk
  refine ⟨⟨k, hkC⟩, hk, ?_⟩
  have hS : componentClassificationOddCore G ⊓ Subgroup.centralizer ({w} : Set G) ≤
      oddCoreIn (Subgroup.centralizer ({w} : Set G)) := by
    refine le_oddCoreIn_of_normalizes inf_le_right ?_ ?_
    · intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨(componentClassificationOddCore_normal G).conj_mem y hy1 c,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hy2) (Subgroup.inv_mem _ hc)⟩
      · rintro ⟨hy1, hy2⟩
        have e : y = c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ := by group
        refine ⟨?_, ?_⟩
        · rw [e]
          exact (componentClassificationOddCore_normal G).conj_mem _ hy1 c⁻¹
        · rw [e]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hy2)
            (Subgroup.inv_mem _ (Subgroup.inv_mem _ hc))
    · have hdvd := Subgroup.card_dvd_of_le
        (inf_le_left : componentClassificationOddCore G ⊓ Subgroup.centralizer ({w} : Set G) ≤ _)
      exact Odd.of_dvd_nat (OddCore.odd_card G) hdvd
  obtain ⟨y, hy, hyeq⟩ := hS ⟨hko, Subgroup.mul_mem _ (Subgroup.inv_mem _ hkC) hxC⟩
  have h1 : (⟨k, hkC⟩ : ↥(Subgroup.centralizer ({w} : Set G)))⁻¹ * ⟨x, hxC⟩ = y :=
    Subtype.ext hyeq.symm
  rw [oddQuotMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, h1]
  exact hy

theorem exactCore_eq_of_modOdd_eq {N N' : Subgroup G} {l c : G}
    (hN : IsClassicalMember p f N l) (hN' : IsClassicalMember p f N' l)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcN : c ∈ trivialOnQuot N)
    (hcN' : c ∈ trivialOnQuot N')
    (h : modOdd c (exactCore c N) = modOdd c (exactCore c N')) :
    exactCore c N = exactCore c N' := by
  have hle := exactCore_le_centralizer c N
  have hle' := exactCore_le_centralizer c N'
  have h1 := isClassicalMember_exactCore_subgroupOf hN hc2 hcN hle le_rfl
  have h2 := isClassicalMember_exactCore_subgroupOf hN' hc2 hcN' hle' le_rfl
  have key : (exactCore c N).subgroupOf (Subgroup.centralizer ({c} : Set G)) =
      (exactCore c N').subgroupOf (Subgroup.centralizer ({c} : Set G)) := by
    refine eq_of_modOdd_eq h1 h2 (le_antisymm ?_ ?_)
    · refine modOdd_le_of_forall_exists (isSubnormal_le h2.subnormal) fun x hx => ?_
      obtain ⟨k, hk, hkx⟩ : oddQuotMk c x ∈ modOdd c (exactCore c N') := h ▸ ⟨x, hx, rfl⟩
      refine ⟨k, hk, ?_⟩
      rw [oddQuotMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hkx
      exact QuotientGroup.eq.mp hkx
    · refine modOdd_le_of_forall_exists (isSubnormal_le h1.subnormal) fun x hx => ?_
      obtain ⟨k, hk, hkx⟩ : oddQuotMk c x ∈ modOdd c (exactCore c N) := h.symm ▸ ⟨x, hx, rfl⟩
      refine ⟨k, hk, ?_⟩
      rw [oddQuotMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hkx
      exact QuotientGroup.eq.mp hkx
  have e := Subgroup.subgroupOf_inj.mp key
  rwa [inf_of_le_left hle, inf_of_le_left hle'] at e

theorem modOdd_eq_exactCore {N : Subgroup G} {l c : G} (hN : IsClassicalMember p f N l)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcN : c ∈ trivialOnQuot N) :
    modOdd l N = modOdd l (exactCore c N) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨x, hxC⟩, hx, rfl⟩
    obtain ⟨i, hi, n, hn, rfl⟩ := exactCore_cover hN hc2 hcN x hx
    have hnO : n ∈ oddCoreIn (Subgroup.centralizer ({l} : Set G)) :=
      oddCoreIn_le_of_isSubnormal hN.subnormal hn
    have hiC : i ∈ Subgroup.centralizer ({l} : Set G) :=
      isSubnormal_le hN.subnormal (exactCore_le_left c N hi)
    obtain ⟨n', hn', hn'eq⟩ := hnO
    refine ⟨⟨i, hiC⟩, hi, ?_⟩
    have e : (⟨i * n, hxC⟩ : ↥(Subgroup.centralizer ({l} : Set G))) = ⟨i, hiC⟩ * n' :=
      Subtype.ext (by show i * n = i * (n' : G); rw [← hn'eq]; rfl)
    rw [e, map_mul, oddQuotMk_eq_one_iff.mpr hn', mul_one]
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, exactCore_le_left c N hy, rfl⟩

theorem eq_of_modOdd_exactCore_eq {N N' : Subgroup G} {l c : G}
    (hN : IsClassicalMember p f N l) (hN' : IsClassicalMember p f N' l)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hcN : c ∈ trivialOnQuot N)
    (hcN' : c ∈ trivialOnQuot N')
    (h : modOdd c (exactCore c N) = modOdd c (exactCore c N')) : N = N' := by
  refine eq_of_modOdd_eq hN hN' ?_
  rw [modOdd_eq_exactCore hN hc2 hcN, modOdd_eq_exactCore hN' hc2 hcN',
    exactCore_eq_of_modOdd_eq hN hN' hc2 hcN hcN' h]

end Twins

end Cover

end CFSG.ClassicalInvolution.NDB
