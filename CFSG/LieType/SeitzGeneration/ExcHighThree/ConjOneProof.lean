module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Assemble
public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjMain

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

section Proof


@[expose] def E6InnerIsotropic : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 1 →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRNative .E6 K E₀ →
      ∀ x ∈ E₀.comap (e6Isogeny K), ∀ y ∈ E₀.comap (e6Isogeny K), x * y = y * x

theorem normalizesRNative_of_matrix {K : Type} [Field K] [Finite K]
    (E₀ : Subgroup (adjointGroup Tag.E6 K)) (R : Subgroup (ModGL Tag.E6 K))
    (hRC : R ≤ adjointGroup Tag.E6 K) (hR1 : R ≠ ⊥) (hRp : IsPGroup (ringChar K) R)
    (hRn : ∀ x ∈ E₀, ∀ z ∈ R, (x : ModGL Tag.E6 K) * z * (x : ModGL Tag.E6 K)⁻¹ ∈ R) :
    NormalizesRNative .E6 K E₀ := by
  classical
  refine ⟨R.subgroupOf (adjointGroup Tag.E6 K), ?_, ?_, ?_⟩
  · intro h
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have h0 : (⟨r, hRC hr⟩ : adjointGroup Tag.E6 K) ∈ R.subgroupOf (adjointGroup Tag.E6 K) := hr
    rw [h] at h0
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 h0))
  · exact hRp.comap_of_injective (adjointGroup Tag.E6 K).subtype
      (adjointGroup Tag.E6 K).subtype_injective
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hRn x hx _ hr
    · intro hr
      have hr' : (x : ModGL Tag.E6 K) * (r : ModGL Tag.E6 K) * (x : ModGL Tag.E6 K)⁻¹ ∈ R := hr
      have h1 := hRn x⁻¹ (inv_mem hx) _ hr'
      rw [Subgroup.mem_subgroupOf]
      have e : ((x⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * ((x : ModGL Tag.E6 K) *
          (r : ModGL Tag.E6 K) * (x : ModGL Tag.E6 K)⁻¹) *
          ((x⁻¹ : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)⁻¹ = (r : ModGL Tag.E6 K) := by
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rwa [e] at h1

theorem normalizesRNative_of_rElement {K : Type} [Field K] [Finite K]
    (E₀ : Subgroup (adjointGroup Tag.E6 K)) {u : ModGL Tag.E6 K}
    (hu : u ∈ adjointGroup Tag.E6 K) (hu1 : u ≠ 1) (hup : ∃ n : ℕ, u ^ (ringChar K ^ n) = 1)
    (hcomm : ∀ x ∈ E₀, Commute u (x : ModGL Tag.E6 K)) : NormalizesRNative .E6 K E₀ := by
  obtain ⟨n, hn⟩ := hup
  refine normalizesRNative_of_matrix E₀ (Subgroup.zpowers u) ?_ ?_ ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact hu
  · intro h
    exact hu1 (Subgroup.zpowers_eq_bot.1 h)
  · intro g
    refine ⟨n, Subtype.ext ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  · intro x hx z hz
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc : Commute (u ^ m) (x : ModGL Tag.E6 K) := (hcomm x hx).zpow_left m
    rw [← hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers u m

theorem mem_fixE6_of_graphFixed6 {K : Type} [Field K] (y : adjointGroup Tag.E6 K)
    (h : (y : ModGL Tag.E6 K) ∈ graphFixed6 K) : y ∈ fixE6 K := by
  unfold fixE6
  refine Subgroup.mem_subgroupOf.2 ?_
  have e := twistedFixedGroup_id_eq (k := K) TwistTag.E6
  exact e ▸ h

theorem conjOne_of_innerIsotropic (hIso : E6InnerIsotropic) : ConjOne := by
  intro K _ _ hq E₀ hexp hcard hn
  classical
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h3 : ¬ 3 ∣ Nat.card K := by omega
  have hK3 : ringChar K ≠ 3 := by
    intro h
    apply h3
    obtain ⟨e, he, hcardK⟩ := card_eq_pow_ringChar K
    rw [hcardK, h]
    exact dvd_pow_self 3 (by omega)
  have hab := hIso K hq E₀ hexp hcard hn
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
    e6IsotropicToral_of_planeToralLang e6PlaneToralLang_proved K h3 E₀ hexp hcard hab
  set A : Subgroup (ModGL Tag.E6 K) := E₀.map (adjointGroup Tag.E6 K).subtype with hAdef
  have hAle : A ≤ adjointGroup Tag.E6 K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAcard : Nat.card A = 3 ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective (adjointGroup Tag.E6 K).subtype_injective, hcard]
  have hAexp : ∀ y ∈ A, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (hexp x hx)
    simpa using this
  have hAnorm : A ≤ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) :=
    hAle.trans Subgroup.le_normalizer
  let D : LangGLData Tag.E6 K A :=
    ⟨w, Fr, hFr, g0, hg0C, hg0, 1, one_mem _, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using hin y hy⟩
  have hc1 : D.c = 1 := rfl
  have hAmem : ∀ x ∈ E₀, (x : ModGL Tag.E6 K) ∈ A := fun x hx => ⟨x, hx, rfl⟩
  have hnt : Nontrivial A := by
    haveI : Fintype A := Fintype.ofFinite A
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hAcard]
    norm_num
  obtain ⟨x₁, hx₁⟩ := exists_ne (1 : A)
  have hx₁1 : (x₁ : ModGL Tag.E6 K) ≠ 1 := fun h => hx₁ (Subtype.ext h)
  have hx₁3 := hAexp x₁ x₁.2
  obtain ⟨x₂, hx₂, hx₂n⟩ := exists_mem_not_mem_zpowers A hAcard x₁.2 hx₁3 hx₁1
  have hgen : Subgroup.closure ({(x₁ : ModGL Tag.E6 K), x₂} : Set (ModGL Tag.E6 K)) = A :=
    closure_pair_eq_of_not_mem A hAcard x₁.2 hx₂ hx₁3 hx₁1 hx₂n
  obtain ⟨ω, hω⟩ := exists_primCubeRoot K hK3
  have hω3 : ω ^ 3 = 1 := Units.ext (by simpa using hω.pow_eq_one)
  obtain ⟨a₁, ha₁, k₁, hk₁⟩ := langGL_diag_exponent D ω hω x₁.2 hx₁3
  obtain ⟨a₂, ha₂, k₂, hk₂⟩ := langGL_diag_exponent D ω hω hx₂ (hAexp x₂ hx₂)
  obtain rfl : a₁ = fun i => ω ^ k₁ i := funext hk₁
  obtain rfl : a₂ = fun i => ω ^ k₂ i := funext hk₂
  have hreg : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ¬ ((3 : ℤ) ∣ ∑ i, α i * (k₁ i : ℤ) ∧ (3 : ℤ) ∣ ∑ i, α i * (k₂ i : ℤ)) := by
    rintro α hα ⟨h1, h2⟩
    obtain ⟨u, hu, hu1, hup, hcomm⟩ := kill_root_gl_E6 K hK3 A D α hα
      (langGL_kills_of_pair D ω hω3 hgen k₁ k₂ ha₁ ha₂ hα h1 h2)
    exact hn (normalizesRNative_of_rElement E₀ hu hu1 hup fun x hx => hcomm _ (hAmem x hx))
  have hnf : ∀ l : Fin Tag.E6.rank → ℤ, l ≠ 0 →
      ¬ ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (D.w • v) i = ∑ i, l i * v i := by
    intro l hl hlfix
    obtain ⟨R, hRad, hR1, hRp, hRn⟩ :=
      exists_normalized_rGroup_of_fixed hK3 hAnorm D l hl hlfix
    exact hn (normalizesRNative_of_matrix E₀ R hRad hR1 hRp fun x hx z hz =>
      hRn _ (hAmem x hx) z hz)
  obtain ⟨g, hg, hgA⟩ := exists_inn_conj_into_graphFixed hq hAle D hc1 ω hω hgen x₁.2 hx₂ k₁ k₂
    ha₁ ha₂ hreg hnf
  refine ⟨⟨g, hg⟩, fun x hx => ?_⟩
  rw [range_embE6F4]
  have hmem := hgA _ (hAmem x hx)
  exact mem_fixE6_of_graphFixed6 (⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹) hmem

end Proof

end CFSG.LieType.SeitzGeneration.ExcHighThree
