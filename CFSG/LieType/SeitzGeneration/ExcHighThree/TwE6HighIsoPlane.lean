module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZHolds
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Two
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwContTwo
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6Reduction
public import CFSG.LieType.SeitzGeneration.ExcHighThree.RegularSolvable
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootF4

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars true

section Plane


theorem twE6HighInF4_plane_two {q : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hq : q % 3 = 2)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar K) E₀)
    (hiso : TwIsoLift K σ E₀) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (g : twistedE6RootGroup K σ)
      (ι : adjointGroup .F4 k →* twistedE6RootGroup K σ) (E₃ : Subgroup (adjointGroup .F4 k)),
      Nat.card k = q ∧ ringChar k = ringChar K ∧ Function.Injective ι ∧
      E₃.map ι = E₀.map (MulAut.conj g).toMonoidHom ∧
      ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure ((ι.range : Set (twistedE6RootGroup K σ)) ∪
        (Subgroup.centralizer ({ι e} : Set (twistedE6RootGroup K σ)) :
          Set (twistedE6RootGroup K σ))) = ⊤ := by
  have hq2 : 2 ≤ q := by omega
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ := exists_fixed_subfield q K σ hK hσ hq2
  obtain ⟨g₀, hg₀⟩ := tw_plane_contained_of_isoLift σ hfix hK hσ hkq hq E₀ hexp hcard hn hiso
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set E₃ : Subgroup (adjointGroup .F4 k) := (E₀.map (MulAut.conj g₀).toMonoidHom).comap ι
    with hE₃def
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
  by_cases h2 : q = 2
  · subst h2
    obtain ⟨e, he, he1, hcl⟩ := TwE6Two.twCloseAtTwo_holds K σ k hfix hK hσ hkq E₃ hexp₃ hcardE₃
    exact ⟨k, inferInstance, inferInstance, g₀, ι, E₃, hkq, hkchar, hι, hE₃, e, he, he1, hcl⟩
  · have hq5 : 3 ≤ q := by omega
    have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hkq]; exact hσ c
    have hq' : Nat.card k % 3 = 2 := by rw [hkq]; exact hq
    have h3 : 3 ≤ Nat.card k := by rw [hkq]; exact hq5
    have hn3 : ¬ NormalizesRIn (ringChar k) E₃ := by
      rw [hkchar]
      exact not_normalizesRIn_of_map hn g₀ ι E₃ hι hE₃
    obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag k TwClass.f4Six.w
      (TwClass.w_theta TwClass.f4Six)
    have hnd : ¬ 3 ∣ Nat.card k := by omega
    obtain ⟨ω, hω⟩ := exists_cube_root_langLevi k hnd D₁
    obtain ⟨z, hzbc, hz1, -, -⟩ := f4TwistedFrame_of k hq' h3 D₁ ω hω
    obtain ⟨g₁, hg₁⟩ := exists_conj_twisted_z_mem langPlaneKillsRoot_F4 k hq' h3 D₁ ω hω z hzbc E₃
      hexp₃ hcardE₃ hn3
    have hKk : Nat.card K = Nat.card k ^ 2 := by rw [hK, hkq]
    have hcl := twistedZClosing_two_holds k K σ hσk hfix hKk hq' h3 D₁ ω hω z hzbc hz1
    refine ⟨k, inferInstance, inferInstance, ι g₁ * g₀, ι, E₃.map (MulAut.conj g₁).toMonoidHom,
      hkq, hkchar, hι, ?_, z, hg₁, hz1, hcl⟩
    rw [Subgroup.map_map]
    have hc1 : ι.comp (MulAut.conj g₁).toMonoidHom =
        ((MulAut.conj (ι g₁)).toMonoidHom).comp ι := by
      ext x
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [hc1, ← Subgroup.map_map, hE₃, Subgroup.map_map]
    have hc2 : ((MulAut.conj (ι g₁)).toMonoidHom).comp (MulAut.conj g₀).toMonoidHom =
        (MulAut.conj (ι g₁ * g₀)).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hc2]

theorem f4ThreeNative_two_of_pilot : F4ThreeNative 2 :=
  f4ThreeNative_of_pilot (Or.inr rfl)
    (langToralOrParabolic_of_langToralPlane
      CFSG.HardMathSupport.Timmesfeld.Torality.langToralPlane_F4_three)
    langPlaneKillsRoot_F4 (f4RegularPure_two_of_pure f4PureTwisted_holds) (f4RegularSolvable 2)
    (fun _ => F4Two.f4ThreeTwo_holds)

theorem planeCl_twE6_of_isoLift {q : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hq : q % 3 = 2)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar K) E₀)
    (hiso : TwIsoLift K σ E₀) : planeCl E₀ = ⊤ := by
  obtain ⟨k, _, _, g, ι, E₃, hk, hr, hι, hE₃, e, he, he1, hgen⟩ :=
    twE6HighInF4_plane_two σ hK hσ hq E₀ hexp hcard hn hiso
  exact planeCl_eq_top_of_embedded_high (r := ringChar K)
    (fun E₃ h1 h2 h3 => f4ThreeNative_two_of_pilot k (by rw [hk]; exact hq) E₃ h1 h2
      (by rw [NormalizesRNative, hr]; exact h3))
    hexp hcard hn g ι E₃ hι hE₃ he he1 hgen

end Plane

end CFSG.LieType.SeitzGeneration.ExcHighThree
