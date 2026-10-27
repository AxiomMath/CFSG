module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.ConjOneProof
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6Reduction
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Purity
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootF4

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

set_option linter.unusedSectionVars true

section Plane


theorem conjOne_of_isotropic_plane (K : Type) [Field K] [Finite K] (hq : Nat.card K % 3 = 1)
    (E₀ : Subgroup (adjointGroup .E6 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hn : ¬ NormalizesRNative .E6 K E₀)
    (hab : ∀ x ∈ E₀.comap (e6Isogeny K), ∀ y ∈ E₀.comap (e6Isogeny K), x * y = y * x) :
    ∃ g : adjointGroup .E6 K, ∀ x ∈ E₀, g * x * g⁻¹ ∈ (embE6F4 K).range := by
  classical
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have h3 : ¬ 3 ∣ Nat.card K := by omega
  have hK3 : ringChar K ≠ 3 := by
    intro h
    apply h3
    obtain ⟨e, he, hcardK⟩ := card_eq_pow_ringChar K
    rw [hcardK, h]
    exact dvd_pow_self 3 (by omega)
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

theorem f4ThreeNative_one_of_pilot : F4ThreeNative 1 :=
  f4ThreeNative_of_pilot (Or.inl rfl)
    (langToralOrParabolic_of_langToralPlane
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three)
    langPlaneKillsRoot_F4 (f4RegularPure_one_of_pure f4PureSplit_holds) (f4RegularSolvable 1)
    (fun h => absurd h (by decide))

theorem planeCl_e6_of_isotropic (K : Type) [Field K] [Finite K] (hq : Nat.card K % 3 = 1)
    (E₀ : Subgroup (adjointGroup .E6 K)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1) (hcard : Nat.card E₀ = 3 ^ 2)
    (hn : ¬ NormalizesRNative .E6 K E₀)
    (hab : ∀ x ∈ E₀.comap (e6Isogeny K), ∀ y ∈ E₀.comap (e6Isogeny K), x * y = y * x) :
    planeCl E₀ = ⊤ := by
  obtain ⟨g, hg⟩ := conjOne_of_isotropic_plane K hq E₀ hexp hcard hn hab
  set E₁ : Subgroup (adjointGroup .E6 K) := E₀.map (MulAut.conj g).toMonoidHom with hE₁def
  have hE₁le : E₁ ≤ (embE6F4 K).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hι := embE6F4_injective K
  set E₃ : Subgroup (adjointGroup .F4 K) := E₁.comap (embE6F4 K) with hE₃def
  have hE₃map : E₃.map (embE6F4 K) = E₁ := Subgroup.map_comap_eq_self hE₁le
  have hcardE₁ : Nat.card E₁ = 3 ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map (embE6F4 K)) = Nat.card E₃ :=
      Subgroup.card_map_of_injective hι
    rw [← h1, hE₃map, hcardE₁]
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    have hmem : (embE6F4 K) x ∈ E₀.map (MulAut.conj g).toMonoidHom := hx
    obtain ⟨y, hy, hyx⟩ := hmem
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hnF : ¬ NormalizesRNative .F4 K E₃ :=
    not_normalizesRIn_comap_of_map (embE6F4 K) hι g hn E₃ hE₃map
  obtain ⟨e, he, he1, hcl⟩ :=
    hClose_one_of_purity_emb (hReg_of_NR langPlaneKillsRoot_F4) f4PureSplit_holds K hq E₃ hexp₃
      hcardE₃ hnF
  exact planeCl_eq_top_of_embedded_high (r := ringChar K)
    (fun E₃ h1 h2 h3 => f4ThreeNative_one_of_pilot K hq E₃ h1 h2 h3) hexp hcard hn g (embE6F4 K) E₃
    hι hE₃map he he1 hcl

end Plane

end CFSG.LieType.SeitzGeneration.ExcHighThree
