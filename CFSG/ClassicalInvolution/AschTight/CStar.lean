module

public import CFSG.ClassicalInvolution.AschTight.E3ModAut
public import CFSG.ClassicalInvolution.AschTight.E3OddGen

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.GorensteinWalter

section Defs

variable {G : Type} [Group G]

@[expose] def cStar (K : Subgroup G) : Subgroup G :=
  ((oddCoreQuotientAut K).comp (normalizerConj K)).ker.map (Subgroup.normalizer (K : Set G)).subtype

theorem cStar_le_normalizer (K : Subgroup G) : cStar K ≤ Subgroup.normalizer (K : Set G) :=
  Subgroup.map_subtype_le _

theorem mem_cStar_iff {K : Subgroup G} {g : G} :
    g ∈ cStar K ↔ ∃ hg : g ∈ Subgroup.normalizer (K : Set G),
      ∀ k : K, (normalizerConj K ⟨g, hg⟩ k)⁻¹ * k ∈ classicalInvolutionOddCore K := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n.2, fun k => ?_⟩
    have h1 := congrArg (fun α : MulAut (K ⧸ classicalInvolutionOddCore K) =>
      α (QuotientGroup.mk k)) (MonoidHom.mem_ker.mp hn)
    simp only [MonoidHom.coe_comp, Function.comp_apply, oddCoreQuotientAut_mk,
      MulAut.one_apply] at h1
    exact QuotientGroup.eq.mp h1
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      simp only [MonoidHom.coe_comp, Function.comp_apply, oddCoreQuotientAut_mk,
        MulAut.one_apply]
      exact QuotientGroup.eq.mpr (h k)

theorem centralizer_le_cStar (K : Subgroup G) :
    Subgroup.centralizer (K : Set G) ≤ cStar K := by
  have hconj : ∀ c ∈ Subgroup.centralizer (K : Set G), ∀ k ∈ K, c * k * c⁻¹ = k := by
    intro c hc k hk
    calc c * k * c⁻¹ = k * c * c⁻¹ := by rw [Subgroup.mem_centralizer_iff.mp hc k hk]
      _ = k := by group
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      rw [hconj g hg k hk]
      exact hk
    · intro hk
      have e : k = g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ := by group
      rw [e, hconj g⁻¹ (Subgroup.inv_mem _ hg) _ hk]
      exact hk
  refine mem_cStar_iff.mpr ⟨hgN, fun k => ?_⟩
  have hk : normalizerConj K ⟨g, hgN⟩ k = k :=
    Subtype.ext (by rw [normalizerConj_apply_coe]; exact hconj g hg k k.2)
  rw [hk, inv_mul_cancel]
  exact Subgroup.one_mem _

@[expose] def CStarTwoRankOne (K : Subgroup G) : Prop :=
  ∀ a ∈ cStar K, ∀ b ∈ cStar K, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b

@[expose] def NormalizerQuotientTwoGeneratedStar (K : Subgroup G) : Prop :=
  ∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.normalizer (K : Set G) →
    ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) ⊔ (P ⊓ cStar K) = P

end Defs

section E3Star

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

omit [Finite G] in
theorem normalizerQuotientTwoGeneratedStar_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (hf : Odd f) : NormalizerQuotientTwoGeneratedStar K := by
  classical
  intro P hP hPN
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.pos.ne'
  have hF : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, Nat.Prime.odd_of_ne_two Fact.out hp2, hf.pos, hFcard⟩
  have h3 : 3 < Nat.card (GaloisField p f) := by omega
  set Ψ := normalizerToPGammaL2Mod (G := G) e hFcard hF h3 with hΨ
  let P' : Subgroup (Subgroup.normalizer (K : Set G)) := P.subgroupOf (Subgroup.normalizer K)
  have hP' : IsPGroup 2 P' := hP.comap_subtype
  obtain ⟨a, b, hab⟩ :=
    exists_closure_pair_eq_of_isPGroup_pGammaL2 Fact.out hFcard hF hf (hP'.map Ψ)
  have ha : a ∈ P'.map Ψ := hab ▸ Subgroup.subset_closure (by simp)
  have hb : b ∈ P'.map Ψ := hab ▸ Subgroup.subset_closure (by simp)
  obtain ⟨a', ha'P, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b', hb'P, rfl⟩ := Subgroup.mem_map.mp hb
  have hclP : Subgroup.closure ({(a' : G), (b' : G)} : Set G) ≤ P := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_subgroupOf.mp ha'P
    · exact Subgroup.mem_subgroupOf.mp hb'P
  refine ⟨{(a' : G), (b' : G)}, Finset.card_le_two, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_pair]
    exact sup_le hclP inf_le_left
  · intro x hxP
    rw [Finset.coe_pair]
    let x' : Subgroup.normalizer (K : Set G) := ⟨x, hPN hxP⟩
    have hx' : Ψ x' ∈ P'.map Ψ := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP)
    rw [← hab, ← Set.image_singleton, ← Set.image_insert_eq, ← MonoidHom.map_closure] at hx'
    obtain ⟨y', hy', hyx⟩ := Subgroup.mem_map.mp hx'
    have hy : (y' : G) ∈ Subgroup.closure ({(a' : G), (b' : G)} : Set G) := by
      have h := Subgroup.mem_map_of_mem (Subgroup.normalizer (K : Set G)).subtype hy'
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at h
      exact h
    have hker : Ψ (y'⁻¹ * x') = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
    have hc : (y' : G)⁻¹ * x ∈ cStar K :=
      ⟨y'⁻¹ * x', oddCoreQuotientAut_eq_one_of_normalizerToPGammaL2Mod_eq_one e hFcard hF h3 hker,
        rfl⟩
    have hyP : (y' : G) ∈ P := hclP hy
    have hx : x = y' * ((y' : G)⁻¹ * x) := by group
    rw [hx]
    exact Subgroup.mul_mem_sup hy ⟨P.mul_mem (P.inv_mem hyP) hxP, hc⟩

variable (p f) in
@[expose] def TightE2Star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z → CStarTwoRankOne K

variable (p f) in
@[expose] def TightE3Star : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z → NormalizerQuotientTwoGeneratedStar K

theorem tightE3Star_of_odd (hf : Odd f) : TightE3Star p f := by
  intro G _ _ _ K z ht
  exact normalizerQuotientTwoGeneratedStar_of_isClassicalMember ht.branch.odd ht.branch.five
    ht.branch.member hf

end E3Star

end CFSG.ClassicalInvolution.Disconnected.AschTight
