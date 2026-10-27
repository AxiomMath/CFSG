module

public import CFSG.CGT.Timmesfeld75.Sec3Twelve
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.CGT.Timmesfeld75.L2AutInvolCard
public import CFSG.CGT.Timmesfeld75.Sec5FiveBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem swap_inner_or_field [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {S S' : Subgroup G} (hS : Sec3 S S') (hSiso : Sec3Iso S S') (hSg : Sec3Global S)
    (hSi : Sec3IsoGlobal S) {x : G} (hxx : x * x = 1) (hx : conjSubgroup x S = S')
    (hxD : x ∈ classD S) :
    (Nat.card S = 16 ∧ Nat.card (normIn S S') = 4) ∨
      ∃ h ∈ S ⊔ S', ∃ t ∈ conjSubgroup h S,
        ∀ y ∈ S ⊔ S', y⁻¹ * ((x * t) * y * (x * t)⁻¹) ∈ cfgM S S' := by
  obtain ⟨hN, f, hf, hiso⟩ := hSiso
  have := hN
  have hpair := hS.isL2Pair_quotient hf hiso
  have hSS' : conjSubgroup x S' = S := by
    rw [← hx, conjSubgroup_conjSubgroup, hxx, conjSubgroup_one]
  have hxX : x ∈ Subgroup.normalizer ((S ⊔ S' : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup, hx, hSS', sup_comm]
  have hxM : x ∈ Subgroup.normalizer ((cfgM S S' : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj, hx, hSS']
    show normIn S' S ⊔ normIn S S' = normIn S S' ⊔ normIn S' S
    exact sup_comm _ _
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := S ⊔ S') (N := cfgM S S') hxX hxM
  have hφφ := quotient_conj_equiv_involutive hxX hxx φ hφ
  rcases hpair.autInvol_inner_or_field_card φ hφφ with
    ⟨g, hgg, hg⟩ | ⟨F, iF, finF, charF, e, σ, hcard, hσ, hσe⟩
  ·
    right
    obtain ⟨k, hk⟩ := hpair.exists_conj_mem_of_mul_self_eq_one hgg
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective k
    have hk' : g ∈ ((conjSubgroup (k₀ : G) S).subgroupOf (S ⊔ S')).map
        (QuotientGroup.mk' ((cfgM S S').subgroupOf (S ⊔ S'))) := by
      have h1 : conjSubgroup (QuotientGroup.mk' ((cfgM S S').subgroupOf (S ⊔ S')) k₀)
          ((S.subgroupOf (S ⊔ S')).map (QuotientGroup.mk' ((cfgM S S').subgroupOf (S ⊔ S')))) =
          ((conjSubgroup (k₀ : G) S).subgroupOf (S ⊔ S')).map
            (QuotientGroup.mk' ((cfgM S S').subgroupOf (S ⊔ S'))) := by
        rw [← map_conjSubgroup, conjSubgroup_subgroupOf]
      rw [← h1]
      exact hk
    obtain ⟨t', ht', rfl⟩ := hk'
    refine ⟨(k₀ : G), k₀.2, (t' : G), Subgroup.mem_subgroupOf.1 ht', fun y hy => ?_⟩
    have hg' : ∀ w : ↥(S ⊔ S') ⧸ (cfgM S S').subgroupOf (S ⊔ S'),
        φ w = QuotientGroup.mk t' * w * (QuotientGroup.mk t')⁻¹ := hg
    have hxt : ∀ z : ↥(S ⊔ S'), x * (z : G) * x⁻¹ ∈ S ⊔ S' := fun z =>
      (Subgroup.mem_normalizer_iff.1 hxX z).1 z.2
    have hmem : (t' : G) * y * (t' : G)⁻¹ ∈ S ⊔ S' :=
      (S ⊔ S').mul_mem ((S ⊔ S').mul_mem t'.2 hy) ((S ⊔ S').inv_mem t'.2)
    set z : ↥(S ⊔ S') := ⟨(t' : G) * y * (t' : G)⁻¹, hmem⟩ with hz
    have hxz : x * (z : G) * x⁻¹ ∈ S ⊔ S' := hxt z
    have h1 : φ (QuotientGroup.mk z) = QuotientGroup.mk ⟨x * (z : G) * x⁻¹, hxz⟩ := hφ z
    have h2 : (QuotientGroup.mk z : ↥(S ⊔ S') ⧸ (cfgM S S').subgroupOf (S ⊔ S')) =
        (QuotientGroup.mk t') * QuotientGroup.mk ⟨y, hy⟩ * (QuotientGroup.mk t')⁻¹ := rfl
    have h3 : (QuotientGroup.mk ⟨x * (z : G) * x⁻¹, hxz⟩ :
        ↥(S ⊔ S') ⧸ (cfgM S S').subgroupOf (S ⊔ S')) = QuotientGroup.mk ⟨y, hy⟩ := by
      rw [← h1, hg', h2]
      have hgg' : (QuotientGroup.mk t' : ↥(S ⊔ S') ⧸ (cfgM S S').subgroupOf (S ⊔ S')) *
          QuotientGroup.mk t' = 1 := hgg
      calc _ = ((QuotientGroup.mk t') * QuotientGroup.mk t') * QuotientGroup.mk ⟨y, hy⟩ *
            ((QuotientGroup.mk t') * QuotientGroup.mk t')⁻¹ := by group
        _ = _ := by rw [hgg']; group
    have h4 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h3.symm)
    have e : (x * (t' : G)) * y * (x * (t' : G))⁻¹ = x * ((t' : G) * y * (t' : G)⁻¹) * x⁻¹ := by
      group
    rw [e]
    exact h4
  ·
    left
    have hxXc : ∀ y ∈ S ⊔ S', x * y * x⁻¹ ∈ S ⊔ S' := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hxX y).1 hy
    have hind : InducesFieldAut (S ⊔ S') (cfgM S S') x e σ :=
      ⟨hxXc, fun y => by rw [← hφ y]; exact hσe (QuotientGroup.mk y)⟩
    obtain ⟨hS16, hF4⟩ :=
      lemma312 G hnab S S' hS.cfg.wc hSg hSi hS x hxD hN F iF finF charF e σ hσ hind
    refine ⟨hS16, ?_⟩
    have h1 := hS.card_eq_mul hf hiso
    have h2f : 2 ^ f = 4 := hcard.symm.trans hF4
    rw [hS16, h2f] at h1
    omega

end CFSG.CGT.Timmesfeld75
