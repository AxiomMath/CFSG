module

public import CFSG.ClassicalInvolution.Uniform.UInduction
public import CFSG.ClassicalInvolution.Uniform.UOmega4
public import CFSG.ClassicalInvolution.Asc77.WP2Stand
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups commutatorElement

section HypOmega

variable {G : Type} [Group G]

structure HypOmegaModU (t : MemberType) (Ω : Set (Subgroup G)) : Prop where
  conjInvariant : ConjInvariant Ω
  classical : ∀ L ∈ Ω, ∃ z : G, IsClassicalMemberU t L z
  omega4 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J)
  omega5 : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
    (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
      v ∈ Subgroup.normalizer (K : Set G)

theorem hypOmegaModU_iff_hypOmegaMod {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} : HypOmegaModU (.sl2 p f) Ω ↔ HypOmegaMod p f Ω := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  refine ⟨fun h => ⟨h.conjInvariant, fun L hL => ?_, h.omega4, h.omega5⟩,
    fun h => ⟨h.conjInvariant, fun L hL => ?_, h.omega4, h.omega5⟩⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, hz.toGeneric hq⟩
  · obtain ⟨z, hz⟩ := h.classical L hL
    exact ⟨z, IsClassicalMemberU.ofGeneric hp2 hf hz⟩

variable {t : MemberType} [Finite G] {K₀ : Subgroup G} {z₀ : G}

theorem hypOmegaModU_conjClass (hc : t.Cert) (h₀ : IsClassicalMemberU t K₀ z₀)
    (hint : IsIntrinsicU t K₀ z₀)
    (h5 : AscHypOmega.Omega5At (Generic.CoreAssembly.conjClass K₀) K₀ z₀) :
    HypOmegaModU t (Generic.CoreAssembly.conjClass K₀) where
  conjInvariant := conjInvariant_conjClass K₀
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, h₀.conj g⟩
  omega4 K hK J hJ hne := omega4_of_memberU hc h₀ hint hK hJ hne
  omega5 := omega5_of_omega5AtU hc h₀ h5

end HypOmega

section Induction

theorem CITBelowAllT.toAll {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (h : CITBelowAllT p n) :
    CITBelowAll p n :=
  fun e he => (citBelowT_iff_citBelowU hp2 he n).mp (h e (by omega))

theorem citBelowAllT_iff_citBelowAll {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (n : ℕ) : CITBelowAllT p n ↔ CITBelowAll p n := by
  refine ⟨fun h => h.toAll hp2, fun h e he => ?_⟩
  have hp : 5 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    by_contra hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd (Fact.out : Nat.Prime 4) (by norm_num)
  have h5 : 5 ≤ p ^ e := by
    have he0 : e ≠ 0 := by rintro rfl; simp at he
    exact hp.trans (Nat.le_self_pow he0 p)
  exact (citBelowT_iff_citBelowU hp2 h5 n).mpr (h e h5)

theorem citBelowAllT_three_iff (n : ℕ) :
    CITBelowAllT 3 n ↔ CITBelowAll 3 n ∧ Q3.CIT3Below n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨fun h => ⟨h.toAll (by norm_num), ?_⟩, fun ⟨h, h3⟩ e he => ?_⟩
  · exact (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mp (h 1 (by norm_num))
  · by_cases h1 : e = 1
    · subst h1
      exact (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr h3
    · have he0 : e ≠ 0 := by rintro rfl; simp at he
      have h2 : 2 ≤ e := by omega
      have h5 : 5 ≤ 3 ^ e := by
        calc 5 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) h2
      exact (citBelowT_iff_citBelowU (by norm_num) h5 n).mpr (h e h5)

end Induction

section Stand

variable (p f : ℕ) [Fact p.Prime]

@[expose] def IH8U (n : ℕ) : Prop :=
  5 ≤ p ^ f → IH8 p f n

@[expose] def IH8AllU (n : ℕ) : Prop :=
  ∀ e : ℕ, 3 ≤ p ^ e → IH8U p e n

variable {p f}

theorem ih8AllU_iff_ih8All (n : ℕ) : IH8AllU p n ↔ IH8All p n :=
  ⟨fun h e he => h e (by omega) he, fun h e _ he => h e he⟩

variable (p f) in
structure AscStandU {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  odd : p ≠ 2
  three : 3 ≤ p ^ f
  hyp : HypOmegaModU (.sl2 p f) Ω
  below : CITBelowAllT p (Nat.card G)
  ih : IH8AllU p (Nat.card G)
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}

theorem AscStandU.toAscStand (h : AscStandU p f Ω K) (hq : 5 ≤ p ^ f) : AscStand p f Ω K where
  odd := h.odd
  five := hq
  hyp := (hypOmegaModU_iff_hypOmegaMod h.odd hq).mp h.hyp
  below := h.below.toAll h.odd
  ih := (ih8AllU_iff_ih8All _).mp h.ih
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen

theorem AscStandU.of_ascStand (hp3 : p ≠ 3) (h : AscStand p f Ω K) : AscStandU p f Ω K where
  odd := h.odd
  three := by have := h.five; omega
  hyp := (hypOmegaModU_iff_hypOmegaMod h.odd h.five).mpr h.hyp
  below := (citBelowAllT_iff_citBelowAll h.odd hp3 _).mpr h.below
  ih := (ih8AllU_iff_ih8All _).mpr h.ih
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen

end Stand

end CFSG.ClassicalInvolution.Uniform
