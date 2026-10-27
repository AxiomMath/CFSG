module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4One
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Purity

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


@[expose] def TwHighPlaneContained_two : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (k : Type) [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c),
    Nat.card K = q ^ 2 → (∀ c : K, σ c = c ^ q) → Nat.card k = q → q % 3 = 2 → 3 ≤ q →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ →
      ∃ g : twistedE6RootGroup K σ,
        E₀.map (MulAut.conj g).toMonoidHom ≤
          ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range

@[expose] def TwistedZClosing_two : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] (σ : K ≃+* K)
    (hσ : ∀ c : K, σ c = c ^ Nat.card k) (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c),
    Nat.card K = Nat.card k ^ 2 → Nat.card k % 3 = 2 → 3 ≤ Nat.card k →
    ∀ (D₁ : LangLevi TwClass.f4Six.tag k TwClass.f4Six.w) (ω : D₁.Lˣ), orderOf ω = 3 →
    ∀ z : adjointGroup TwClass.f4Six.tag k,
      baseChangeGL (algebraMap k D₁.L) (z : ModGL TwClass.f4Six.tag k) =
        D₁.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
          TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹ →
      z ≠ 1 →
      Subgroup.closure
        ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range :
            Set (twistedE6RootGroup K σ)) ∪
          (Subgroup.centralizer
            ({((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom) z} :
              Set (twistedE6RootGroup K σ)) : Set (twistedE6RootGroup K σ))) = ⊤

@[expose] def TwE6HighInF4_at_two : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 2 ^ 2 → (∀ c, σ c = c ^ 2) →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
      ¬ NormalizesRIn (ringChar K) E₀ →
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (g : twistedE6RootGroup K σ)
        (ι : adjointGroup .F4 k →* twistedE6RootGroup K σ) (E₃ : Subgroup (adjointGroup .F4 k)),
        Nat.card k = 2 ∧ ringChar k = ringChar K ∧ Function.Injective ι ∧
        E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom ∧
        ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((ι.range : Set (twistedE6RootGroup K σ)) ∪
          (Subgroup.centralizer ({ι e} : Set (twistedE6RootGroup K σ)) :
            Set (twistedE6RootGroup K σ))) = ⊤

theorem exists_conj_twisted_z_mem (hNR : LangPlaneKillsRoot .F4)
    (k : Type) [Field k] [Finite k] (hq : Nat.card k % 3 = 2) (h3 : 3 ≤ Nat.card k)
    (D₁ : LangLevi TwClass.f4Six.tag k TwClass.f4Six.w) (ω : D₁.Lˣ) (hω : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag k)
    (hz : baseChangeGL (algebraMap k D₁.L) (z : ModGL TwClass.f4Six.tag k) =
      D₁.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
        TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹)
    (E₃ : Subgroup (adjointGroup .F4 k)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1) (hcard : Nat.card E₃ = 3 ^ 2)
    (hn : ¬ NormalizesRIn (ringChar k) E₃) :
    ∃ g : adjointGroup .F4 k, z ∈ E₃.map (MulAut.conj g).toMonoidHom := by
  have hn3 : ¬ 3 ∣ Nat.card k := by omega
  have hLT : LangToralOrParabolic .F4 := langToralOrParabolic_of_langToralPlane
    CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three
  rcases hLT k hn3 E₃ hexp hcard with hD | hnorm
  · let D : LangPlaneData .F4 k E₃ := hD.some
    have hkills : ∀ α, IsRoot .F4 α → ¬ D.Kills α := by
      intro α hα hk
      obtain ⟨u, hu1, hun, hcomm⟩ := hNR k E₃ D α hα hk
      exact hn (normalizesRNative_of_unip ⟨u, hu1, hun, hcomm⟩)
    have hE : ∃ e ∈ E₃, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : E₃ = ⊥ := (Subgroup.eq_bot_iff_forall E₃).2 hcon
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    obtain ⟨e, he, he1⟩ := hE
    obtain ⟨g, hg⟩ := f4PureTwisted_holds k hq h3 D₁ ω hω z hz E₃ hexp hcard D hkills e he he1
    exact ⟨g, e, he, hg⟩
  · exact absurd hnorm hn

theorem twE6HighInF4_two_of (hNR : LangPlaneKillsRoot .F4)
    (hQ2 : TwE6HighInF4_at_two) (hCont : TwHighPlaneContained_two) (hZ : TwistedZClosing_two) :
    TwE6HighInF4 2 := by
  intro q K _ _ σ hK hσ hq E₀ hexp hcard hn
  by_cases h2 : q = 2
  · subst h2
    exact hQ2 K σ hK hσ E₀ hexp hcard hn
  have hq2 : 2 ≤ q := by omega
  have hq5 : 3 ≤ q := by omega
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ := exists_fixed_subfield q K σ hK hσ hq2
  have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hkq]; exact hσ c
  have hq' : Nat.card k % 3 = 2 := by rw [hkq]; exact hq
  have h3 : 3 ≤ Nat.card k := by rw [hkq]; exact hq5
  obtain ⟨g₀, hg₀⟩ := hCont q K σ k hfix hK hσ hkq hq hq5 E₀ hexp hcard hn
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set E₃ : Subgroup (adjointGroup .F4 k) := (E₀.map (MulAut.conj g₀).toMonoidHom).comap ι with hE₃def
  have hE₃ : E₃.map ι = E₀.map (MulAut.conj g₀).toMonoidHom := Subgroup.map_comap_eq_self hg₀
  have hexp₃ : ∀ x ∈ E₃, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
    apply hι
    rw [map_pow, map_one, ← hyx, ← map_pow, hexp y hy, map_one]
  have hcardE₃ : Nat.card E₃ = 3 ^ 2 := by
    have h1 : Nat.card (E₃.map ι) = Nat.card E₃ := Subgroup.card_map_of_injective hι
    have h2 : Nat.card (E₀.map (MulAut.conj g₀).toMonoidHom) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (MulAut.conj g₀).injective
    rw [← h1, hE₃, h2, hcard]
  have hn3 : ¬ NormalizesRIn (ringChar k) E₃ := by
    rw [hkchar]
    exact not_normalizesRIn_of_map hn g₀ ι E₃ hι hE₃
  obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag k TwClass.f4Six.w (TwClass.w_theta TwClass.f4Six)
  have hnd : ¬ 3 ∣ Nat.card k := by omega
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi k hnd D₁
  obtain ⟨z, hzbc, hz1, -, -⟩ := f4TwistedFrame_of k hq' h3 D₁ ω hω
  obtain ⟨g₁, hg₁⟩ := exists_conj_twisted_z_mem hNR k hq' h3 D₁ ω hω z hzbc E₃ hexp₃ hcardE₃ hn3
  have hKk : Nat.card K = Nat.card k ^ 2 := by rw [hK, hkq]
  have hcl := hZ k K σ hσk hfix hKk hq' h3 D₁ ω hω z hzbc hz1
  refine ⟨k, inferInstance, inferInstance, ι g₁ * g₀, ι, E₃.map (MulAut.conj g₁).toMonoidHom, hkq, hkchar,
    hι, ?_, z, hg₁, hz1, hcl⟩
  rw [Subgroup.map_map]
  have hc1 : ι.comp (MulAut.conj g₁).toMonoidHom = ((MulAut.conj (ι g₁)).toMonoidHom).comp ι := by
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  rw [hc1, ← Subgroup.map_map, hE₃, Subgroup.map_map]
  have hc2 : ((MulAut.conj (ι g₁)).toMonoidHom).comp (MulAut.conj g₀).toMonoidHom =
      (MulAut.conj (ι g₁ * g₀)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hc2]

end CFSG.LieType.SeitzGeneration.ExcHighThree
