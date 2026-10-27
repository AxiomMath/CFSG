module

public import CFSG.LocalAnalysis.SteinbergBXGMSEvenPairAffinePlane
public import CFSG.Adapters.FrobeniusKernel

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open scoped Pointwise

section Frobenius

theorem exists_regular_normal_frobeniusKernel {Ω : Type} [Finite Ω]
    {N : Subgroup (Equiv.Perm Ω)} (htrans : ∀ β γ : Ω, ∃ x ∈ N, x β = γ) {α : Ω}
    (hα : ∃ x ∈ N, x ≠ 1 ∧ x α = α)
    (hfrob : ∀ x ∈ N, x ≠ 1 → ∀ β γ : Ω, x β = β → x γ = γ → β = γ) :
    ∃ K : Subgroup (Equiv.Perm Ω), K ≤ N ∧ (K.subgroupOf N).Normal ∧
      (∀ x ∈ N, x ∈ K ↔ x = 1 ∨ ∀ β : Ω, x β ≠ β) ∧
      (∀ β γ : Ω, ∃! k : K, (k : Equiv.Perm Ω) β = γ) ∧
      (∀ x ∈ N, ∃ k ∈ K, ∃ y ∈ N, y α = α ∧ x = k * y) ∧
      Nat.card K = Nat.card Ω := by
  classical
  set H : Subgroup N := MulAction.stabilizer N α with hHdef
  have hmemH : ∀ x : N, x ∈ H ↔ (x : Equiv.Perm Ω) α = α := fun x => by
    rw [hHdef, MulAction.mem_stabilizer_iff, MulAction.subgroup_smul_def, Equiv.Perm.smul_def]
  have hconj : ∀ g x : N, x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H := fun g x => by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  have hconjfix : ∀ g x : N, x ∈ MulAut.conj g • H ↔
      (x : Equiv.Perm Ω) ((g : Equiv.Perm Ω) α) = (g : Equiv.Perm Ω) α := by
    intro g x
    rw [hconj, hmemH]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    constructor
    · intro h1
      have h2 := congrArg (g : Equiv.Perm Ω) h1
      rwa [GMSAffine.perm_apply_inv] at h2
    · intro h1
      rw [h1, GMSAffine.perm_inv_apply]
  obtain ⟨x₀, hx₀, hx₀1, hx₀α⟩ := hα
  have hH1 : H ≠ ⊥ := by
    intro hb
    have : (⟨x₀, hx₀⟩ : N) ∈ H := (hmemH _).mpr hx₀α
    rw [hb, mem_bot] at this
    exact hx₀1 (congrArg Subtype.val this)
  obtain ⟨β₀, hβ₀⟩ : ∃ β : Ω, β ≠ α := by
    by_contra hall
    push Not at hall
    exact hx₀1 (Equiv.ext fun γ => by rw [hall γ, hx₀α]; rfl)
  have hHG : H ≠ ⊤ := by
    intro ht
    obtain ⟨x, hx, hxβ⟩ := htrans α β₀
    have : (⟨x, hx⟩ : N) ∈ H := ht ▸ mem_top _
    exact hβ₀ (hxβ ▸ ((hmemH _).mp this))
  have hfrob' : ∀ g : N, g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxg⟩ := mem_inf.mp hx
    rw [hconjfix] at hxg
    rw [hmemH] at hxH hg
    rw [mem_bot]
    by_contra hx1
    exact hg (hfrob x x.2 (fun h1 => hx1 (Subtype.ext h1)) α _ hxH hxg).symm
  obtain ⟨K, hKset, hKn, hKH, -, -⟩ := CFSG.Adapters.frobenius_kernel H hH1 hHG hfrob'
  have hKmem : ∀ x : N, x ∈ K ↔ x = 1 ∨ ∀ β : Ω, (x : Equiv.Perm Ω) β ≠ β := by
    intro x
    rw [← SetLike.mem_coe, hKset]
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_univ, true_and,
      Set.mem_iUnion, SetLike.mem_coe, not_exists]
    refine or_congr Iff.rfl ⟨fun hx β hxβ => ?_, fun hx g hxg => ?_⟩
    · obtain ⟨g, hg, hgβ⟩ := htrans α β
      exact hx ⟨g, hg⟩ ((hconjfix _ _).2 (by rw [hgβ]; exact hxβ))
    · exact hx _ ((hconjfix _ _).1 hxg)
  have hKfree : ∀ k : N, k ∈ K → ∀ β : Ω, (k : Equiv.Perm Ω) β = β → k = 1 := by
    intro k hk β hkβ
    rcases (hKmem k).1 hk with h1 | h1
    · exact h1
    · exact absurd hkβ (h1 β)
  have hKα : ∀ γ : Ω, ∃ k ∈ K, (k : Equiv.Perm Ω) α = γ := by
    intro γ
    obtain ⟨x, hx, hxγ⟩ := htrans α γ
    obtain ⟨k, hk, y, hy, hxky⟩ := hKH ⟨x, hx⟩
    refine ⟨k, hk, ?_⟩
    have h2 := congrArg (fun z : N => (z : Equiv.Perm Ω) α) hxky
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, (hmemH y).mp hy] at h2
    rw [← h2, hxγ]
  have hKeq : (K.map N.subtype).subgroupOf N = K :=
    comap_map_eq_self_of_injective N.subtype_injective K
  have hmemK : ∀ x (hx : x ∈ N), x ∈ K.map N.subtype ↔ (⟨x, hx⟩ : N) ∈ K := by
    intro x hx
    rw [← mem_subgroupOf (H := K.map N.subtype) (K := N) (h := ⟨x, hx⟩), hKeq]
  have hreg : ∀ β γ : Ω, ∃! k : K.map N.subtype, (k : Equiv.Perm Ω) β = γ := by
    intro β γ
    obtain ⟨k₁, hk₁, hk₁α⟩ := hKα β
    obtain ⟨k₂, hk₂, hk₂α⟩ := hKα γ
    refine ⟨⟨((k₂ * k₁⁻¹ : N) : Equiv.Perm Ω), ⟨_, mul_mem hk₂ (inv_mem hk₁), rfl⟩⟩, ?_, ?_⟩
    · change ((k₂ : Equiv.Perm Ω) * (k₁ : Equiv.Perm Ω)⁻¹) β = γ
      rw [← hk₁α, ← hk₂α, Equiv.Perm.mul_apply, GMSAffine.perm_inv_apply]
    · rintro ⟨_, ⟨k, hk, rfl⟩⟩ hkβ
      have hkβ' : (k : Equiv.Perm Ω) β = γ := hkβ
      have h1 : k₂⁻¹ * k * k₁ = 1 := by
        refine hKfree _ (mul_mem (mul_mem (inv_mem hk₂) hk) hk₁) α ?_
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hk₁α, hkβ', ← hk₂α,
          GMSAffine.perm_inv_apply]
      have h2 : k = k₂ * k₁⁻¹ := by
        calc k = k₂ * (k₂⁻¹ * k * k₁) * k₁⁻¹ := by group
          _ = k₂ * k₁⁻¹ := by rw [h1, mul_one]
      subst h2
      rfl
  refine ⟨K.map N.subtype, map_subtype_le K, by rw [hKeq]; exact hKn, ?_, hreg, ?_, ?_⟩
  · intro x hx
    rw [hmemK x hx, hKmem]
    exact or_congr ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩ Iff.rfl
  · intro x hx
    obtain ⟨k, hk, y, hy, hxky⟩ := hKH ⟨x, hx⟩
    exact ⟨k, ⟨k, hk, rfl⟩, y, y.2, (hmemH y).mp hy, congrArg Subtype.val hxky⟩
  · refine Nat.card_congr (Equiv.ofBijective (fun k : K.map N.subtype => (k : Equiv.Perm Ω) α)
      ⟨fun k k' hkk' => ?_, fun γ => ?_⟩)
    · obtain ⟨c, -, hc⟩ := hreg α ((k : Equiv.Perm Ω) α)
      exact (hc k rfl).trans (hc k' hkk'.symm).symm
    · obtain ⟨k, hk, -⟩ := hreg α γ
      exact ⟨k, hk⟩

end Frobenius

section GMS

variable {D : Type} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_pairStabilizer_structure [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) :
    (∀ x ∈ gmsPermStabilizer U R, ∃ t ∈ gmsSingerPermImage X U R,
      ∃ b ∈ gmsPairStabilizer U R β, x = t * b) ∧
    gmsSingerPermImage X U R ⊓ gmsPairStabilizer U R β = ⊥ ∧
    Nat.card (gmsPairStabilizer U R β) = Nat.card (gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) ∧
    IsCyclic (gmsPairStabilizer U R β) ∧ Nat.card (gmsPairStabilizer U R β) ∣ n := by
  classical
  have hTle := GMSDichotomy.gmsSingerPermImage_le h (X := X)
  have hBH : gmsPairStabilizer U R β ≤ gmsPermStabilizer U R := inf_le_left
  have hBβ : ∀ b ∈ gmsPairStabilizer U R β, b β = β := fun b hb => by
    have h1 := (mem_inf.1 hb).2
    rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h1
  have hdec : ∀ x ∈ gmsPermStabilizer U R, ∃ t ∈ gmsSingerPermImage X U R,
      ∃ b ∈ gmsPairStabilizer U R β, x = t * b := by
    intro x hx
    have hxR := (GMSDichotomy.mem_gmsPermStabilizer.1 hx).2
    have hxβ : ((x β : gmsRootConjugates (U ⊔ R) R) : Subgroup D) ≠ R := by
      intro h1
      apply hβ
      have h2 : x β = ⟨R, gms_R_mem⟩ := Subtype.ext h1
      rw [← hxR] at h2
      exact congrArg Subtype.val (x.injective h2)
    obtain ⟨t, ht, htβ⟩ := GMSDichotomy.exists_mem_gmsSingerPermImage_apply_eq h h3 hβ hxβ
    refine ⟨t, ht, t⁻¹ * x, mem_inf.2 ⟨mul_mem (inv_mem (hTle ht)) hx, ?_⟩, by group⟩
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply, ← htβ,
      GMSAffine.perm_inv_apply]
  have hTB : gmsSingerPermImage X U R ⊓ gmsPairStabilizer U R β = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [mem_bot]
    exact GMSDichotomy.eq_one_of_mem_gmsSingerPermImage h h3 (mem_inf.1 hb).1 hβ
      (hBβ b (mem_inf.1 hb).2)
  have hTn := GMSDichotomy.gmsSingerPermImage_normal h (X := X)
  obtain ⟨-, -, -, -, -, -, hHTcyc, hHTdvd, -⟩ :=
    gms_normal_root_action_dichotomy_branch_completion h h3 (X := X)
  set φ : gmsPairStabilizer U R β →* gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hBH) with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf] at hb
    have h1 : (b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) ∈
        gmsSingerPermImage X U R ⊓ gmsPairStabilizer U R β := mem_inf.2 ⟨hb, b.2⟩
    rw [hTB, mem_bot] at h1
    exact (mem_bot).2 (Subtype.ext h1)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨t, ht, b, hb, hxtb⟩ := hdec x x.2
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [mem_subgroupOf]
    have h1 : ((Subgroup.inclusion hBH ⟨b, hb⟩)⁻¹ * x : gmsPermStabilizer U R).1 =
        b⁻¹ * t * b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hxtb, mul_assoc]
    rw [h1]
    have h2 := hTn.conj_mem ⟨t, hTle ht⟩ (mem_subgroupOf.2 ht) ⟨b, hBH hb⟩⁻¹
    rw [mem_subgroupOf] at h2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h2
  have hcard : Nat.card (gmsPairStabilizer U R β) = Nat.card (gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
  have := hHTcyc
  exact ⟨hdec, hTB, hcard, isCyclic_of_injective φ hφinj, hcard ▸ hHTdvd⟩

theorem gmsPairStabilizer_eq_bot_iff [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) :
    (gmsPairStabilizer U R β = ⊥ ↔ gmsPermStabilizer U R = gmsSingerPermImage X U R) ∧
    (gmsPairStabilizer U R β = ⊥ ↔ Nat.card (gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 1) := by
  obtain ⟨hdec, -, hcard, -, -⟩ := gms_pairStabilizer_structure h h3 β hβ (X := X)
  have hTle := GMSDichotomy.gmsSingerPermImage_le h (X := X)
  have h1 : gmsPairStabilizer U R β = ⊥ ↔ gmsPermStabilizer U R = gmsSingerPermImage X U R := by
    constructor
    · intro hd
      refine le_antisymm (fun x hx => ?_) hTle
      obtain ⟨t, ht, b, hb, rfl⟩ := hdec x hx
      rw [hd, mem_bot] at hb
      rw [hb, mul_one]
      exact ht
    · intro hHT
      rw [eq_bot_iff]
      intro b hb
      rw [mem_bot]
      have hbH : b ∈ gmsPermStabilizer U R := (mem_inf.1 hb).1
      have hbβ : b β = β := by
        have h1 := (mem_inf.1 hb).2
        rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h1
      rw [hHT] at hbH
      exact GMSDichotomy.eq_one_of_mem_gmsSingerPermImage h h3 hbH hβ hbβ
  exact ⟨h1, by rw [← hcard, Subgroup.card_eq_one]⟩

theorem gms_frobenius_of_pairStabilizer_eq_bot [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) (hd : gmsPairStabilizer U R β = ⊥) :
    (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ≠ 1 →
      ∀ Q Z : gmsRootConjugates (U ⊔ R) R, σ Q = Q → σ Z = Z → Q = Z) ∧
    ∀ β' : gmsRootConjugates (U ⊔ R) R, (β' : Subgroup D) ≠ R →
      gmsPairStabilizer U R β' = ⊥ := by
  obtain ⟨-, -, -, -, h2tr, -⟩ := gms_normal_root_partition_and_two_transitivity h h3
  have hβR : β ≠ ⟨R, gms_R_mem⟩ := fun h1 => hβ (congrArg Subtype.val h1)
  have hfrob : ∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ≠ 1 →
      ∀ Q Z : gmsRootConjugates (U ⊔ R) R, σ Q = Q → σ Z = Z → Q = Z := by
    intro σ hσ hσ1 Q Z hQ hZ
    by_contra hQZ
    obtain ⟨τ, hτ, hτQ, hτZ⟩ := h2tr Q Z ⟨R, gms_R_mem⟩ β hQZ hβR.symm
    have hb : τ * σ * τ⁻¹ ∈ gmsPairStabilizer U R β := by
      refine mem_inf.2 ⟨GMSDichotomy.mem_gmsPermStabilizer.2
        ⟨mul_mem (mul_mem hτ hσ) (inv_mem hτ), ?_⟩, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hτQ, GMSAffine.perm_inv_apply, hQ]
      · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply, ← hτZ, GMSAffine.perm_inv_apply, hZ]
    rw [hd, mem_bot] at hb
    apply hσ1
    calc σ = τ⁻¹ * (τ * σ * τ⁻¹) * τ := by group
      _ = 1 := by rw [hb, mul_one, inv_mul_cancel]
  refine ⟨hfrob, fun β' hβ' => ?_⟩
  rw [eq_bot_iff]
  intro b hb
  rw [mem_bot]
  by_contra hb1
  have hbH := GMSDichotomy.mem_gmsPermStabilizer.1 (mem_inf.1 hb).1
  have hbβ' : b β' = β' := by
    have h1 := (mem_inf.1 hb).2
    rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h1
  exact hβ' (congrArg Subtype.val (hfrob b hbH.1 hb1 _ β' hbH.2 hbβ')).symm

theorem gms_normal_root_trivial_pair_completion [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (β : gmsRootConjugates (U ⊔ R) R) (hβ : (β : Subgroup D) ≠ R)
    (hd : gmsPairStabilizer U R β = ⊥) :
    3 ≤ n ∧ (gmsRootConjugates (U ⊔ R) R).ncard = 2 ^ n ∧
    (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ≠ 1 →
      ∀ Q Z : gmsRootConjugates (U ⊔ R) R, σ Q = Q → σ Z = Z → Q = Z) ∧
    (∀ β' : gmsRootConjugates (U ⊔ R) R, (β' : Subgroup D) ≠ R →
      gmsPairStabilizer U R β' = ⊥) ∧
    gmsPermStabilizer U R = gmsSingerPermImage X U R ∧
    Nat.card (gmsRootConjugateAction (U ⊔ R) R).range = 2 ^ n * (2 ^ n - 1) ∧
    ∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      E ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) ∧
      (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
        σ ∈ E ↔ σ = 1 ∨ ∀ Q : gmsRootConjugates (U ⊔ R) R, σ Q ≠ Q) ∧
      (∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ ∈ E ↔ σ = 1 ∨ orderOf σ = 2) ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ n ∧
      E ⊓ gmsSingerPermImage X U R = ⊥ ∧
      E ⊔ gmsSingerPermImage X U R = (gmsRootConjugateAction (U ⊔ R) R).range ∧
      ((E ⊔ gmsSingerPermImage X U R).subgroupOf
        (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      Nat.card (E ⊔ gmsSingerPermImage X U R : Subgroup _) = 2 ^ n * (2 ^ n - 1) ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ E ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
      (∀ f ∈ E ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
        f Q = Q → f Z = Z → Q = Z) ∧
      (E.comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤ E.comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥(E.comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf (E.comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        E) := by
  classical
  obtain ⟨-, hΔcard, -, -, h2tr, -⟩ := gms_normal_root_partition_and_two_transitivity h h3
  obtain ⟨hfrob, hB⟩ := gms_frobenius_of_pairStabilizer_eq_bot h h3 β hβ hd
  have hHT := ((gmsPairStabilizer_eq_bot_iff (X := X) h h3 β hβ).1).1 hd
  obtain ⟨-, -, hTcard, hTle, -, -, -, -, haff, -⟩ :=
    gms_normal_root_action_dichotomy_branch_completion h h3
  have hn3 : 3 ≤ n := h.1
  have h8 : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have htrans : ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
      ∃ x ∈ (gmsRootConjugateAction (U ⊔ R) R).range, x Q = Z := by
    intro Q Z
    by_cases hQZ : Q = Z
    · exact ⟨1, one_mem _, by rw [hQZ]; rfl⟩
    · obtain ⟨σ, hσ, hσQ, -⟩ := h2tr Q Z Z Q hQZ (Ne.symm hQZ)
      exact ⟨σ, hσ, hσQ⟩
  have hα : ∃ x ∈ (gmsRootConjugateAction (U ⊔ R) R).range, x ≠ 1 ∧
      x ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ := by
    have hT1 : gmsSingerPermImage X U R ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hTcard]
      omega
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT1
    have htH := GMSDichotomy.mem_gmsPermStabilizer.1 (hTle ht)
    exact ⟨t, htH.1, fun h1 => ht1 (Subtype.ext h1), htH.2⟩
  obtain ⟨E, hEN, hEn, hEmem, hreg, hEdec, -⟩ :=
    exists_regular_normal_frobeniusKernel htrans hα hfrob
  obtain ⟨hEel, hEcard, hFN, hFn, hFcard, hFtrans, hFfrob⟩ := haff E hEN hEn hreg
  have hNF : E ⊔ gmsSingerPermImage X U R = (gmsRootConjugateAction (U ⊔ R) R).range := by
    refine le_antisymm hFN (fun x hx => ?_)
    obtain ⟨k, hk, y, hy, hyR, rfl⟩ := hEdec x hx
    have hyH : y ∈ gmsPermStabilizer U R := GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hy, hyR⟩
    rw [hHT] at hyH
    exact mul_mem (mem_sup_left hk) (mem_sup_right hyH)
  have hET : E ⊓ gmsSingerPermImage X U R = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨haE, haT⟩ := mem_inf.1 ha
    have haR := (GMSDichotomy.mem_gmsPermStabilizer.1 (hTle haT)).2
    rw [mem_bot]
    rcases (hEmem a (hEN haE)).1 haE with h1 | h1
    · exact h1
    · exact absurd haR (h1 _)
  have hinv : ∀ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
      σ ∈ E ↔ σ = 1 ∨ orderOf σ = 2 := by
    intro σ hσ
    constructor
    · intro hσE
      have hsq : σ ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian σ hσE
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hsq) with h1 | h1
      · exact Or.inl (orderOf_eq_one_iff.1 h1)
      · exact Or.inr h1
    · rintro (rfl | h2)
      · exact one_mem E
      · refine (hEmem σ hσ).2 (Or.inr fun Q hQ => ?_)
        obtain ⟨τ, hτ, hτQ⟩ := htrans ⟨R, gms_R_mem⟩ Q
        have hc : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ gmsSingerPermImage X U R := by
          rw [← hHT]
          refine GMSDichotomy.mem_gmsPermStabilizer.2
            ⟨mul_mem (mul_mem (inv_mem hτ) hσ) (inv_mem (inv_mem hτ)), ?_⟩
          rw [inv_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτQ, hQ, ← hτQ,
            GMSAffine.perm_inv_apply]
        have hdvd := (gmsSingerPermImage X U R).orderOf_dvd_natCard hc
        rw [GMSAffine.orderOf_conj_eq, h2, hTcard] at hdvd
        omega
  have hcomapN : (E.comap (gmsRootConjugateAction (U ⊔ R) R)).Normal := by
    constructor
    intro l hl g
    rw [mem_comap] at hl ⊢
    have h1 := hEn.conj_mem ⟨_, hEN hl⟩ (mem_subgroupOf.2 hl) ⟨_, ⟨g, rfl⟩⟩
    rw [mem_subgroupOf] at h1
    rw [map_mul, map_mul, map_inv]
    exact h1
  have hKE : gmsRootKernel (U ⊔ R) R ≤ E.comap (gmsRootConjugateAction (U ⊔ R) R) := by
    intro l hl
    rw [← ker_gmsRootConjugateAction, MonoidHom.mem_ker] at hl
    rw [mem_comap, hl]
    exact one_mem E
  have hquot : Nonempty (↥(E.comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
      (gmsRootKernel (U ⊔ R) R).subgroupOf (E.comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        E) := by
    set φ : E.comap (gmsRootConjugateAction (U ⊔ R) R) →* E :=
      ((gmsRootConjugateAction (U ⊔ R) R).comp
        (E.comap (gmsRootConjugateAction (U ⊔ R) R)).subtype).codRestrict E (fun x => x.2)
      with hφ
    have hφsurj : Function.Surjective φ := by
      rintro ⟨e, he⟩
      obtain ⟨l, hl⟩ := hEN he
      exact ⟨⟨l, by rw [mem_comap, hl]; exact he⟩, Subtype.ext hl⟩
    have hφker : φ.ker = (gmsRootKernel (U ⊔ R) R).subgroupOf
        (E.comap (gmsRootConjugateAction (U ⊔ R) R)) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, ← ker_gmsRootConjugateAction, MonoidHom.mem_ker]
      exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)⟩
  refine ⟨hn3, hΔcard, hfrob, hB, hHT, by rw [← hNF]; exact hFcard, E, hEN, hEn, hreg, hEmem,
    hinv, hEel, hEcard, hET, hNF, hFn, hFcard, hFtrans, hFfrob, hcomapN, hKE, hquot⟩

end GMS

end CFSG.SeitzReduction.RankOne
