module

public import CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwContTwo
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZUni
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.HoldsTw

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.HardMathSupport.Lang.AnisoE6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem twE6UniClose_two
    {k K : Type} [Field k] [Finite k] [Field K]
    [Finite K] [Algebra k K] (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hkchar : ringChar k = ringChar K) (hK : Nat.card K = Nat.card k ^ 2)
    (hq : Nat.card k % 3 = 2) (h3 : 3 ≤ Nat.card k)
    (E₃ : Subgroup (adjointGroup .F4 k)) (hexp : ∀ x ∈ E₃, x ^ 3 = 1)
    (hcard : Nat.card E₃ = 3 ^ 2) (hnF : ¬ NormalizesRNative .F4 k E₃)
    (D₁ : LangLevi TwClass.f4Six.tag k TwClass.f4Six.w) (ω : D₁.Lˣ) (hω : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag k)
    (hzbc : baseChangeGL (algebraMap k D₁.L) (z : ModGL TwClass.f4Six.tag k) =
      D₁.g * rootDiagUnit TwClass.f4Six.tag (Pi.mulSingle (⟨1, by decide⟩ : Fin
        TwClass.f4Six.tag.rank) ω) * D₁.g⁻¹)
    (hz1 : z ≠ 1) (g₁ : adjointGroup .F4 k)
    (hz : z ∈ E₃.map (MulAut.conj g₁).toMonoidHom) :
    Subgroup.closure {x : twistedE6RootGroup K σ | ∃ y ∈ (E₃.map (MulAut.conj g₁).toMonoidHom).map
        ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom), y ≠ 1 ∧ Commute x y ∧
      ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} = ⊤ := by
  classical
  set ι : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
    (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    (phiG_injective σ hfix).comp (e6FixedF4EquivAll k).symm.injective
  set H := Subgroup.closure {x : twistedE6RootGroup K σ |
      ∃ y ∈ (E₃.map (MulAut.conj g₁).toMonoidHom).map ι,
        y ≠ 1 ∧ Commute x y ∧ ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} with hH
  have hnd : ¬ 3 ∣ Nat.card k := by omega
  have hF := f4ThreeUniNative_of_three_le k h3 hnd E₃ hexp hcard hnF
  rw [hkchar] at hF
  have hrange : ι.range ≤ H := by
    have h1 := map_le_uniClosure (ι.comp (MulAut.conj g₁).toMonoidHom)
      (hι.comp (MulAut.conj g₁).injective) E₃ hF
    rw [← Subgroup.map_map] at h1
    refine le_trans ?_ h1
    rintro _ ⟨y, rfl⟩
    exact ⟨g₁⁻¹ * y * g₁, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hιz1 : ι z ≠ 1 := fun h => hz1 (hι (h.trans (map_one ι).symm))
  have hιzE : ι z ∈ (E₃.map (MulAut.conj g₁).toMonoidHom).map ι := ⟨z, hz, rfl⟩
  have htop := twistedZUniClosing_two k K σ hσ hfix hK hq h3 D₁ ω hω z hzbc hz1
  change Subgroup.closure ((ι.range : Set (twistedE6RootGroup K σ)) ∪
    {x : twistedE6RootGroup K σ | Commute x (ι z) ∧
      ∃ n : ℕ, x ^ (ringChar K ^ n) = 1}) = ⊤ at htop
  have hle : Subgroup.closure ((ι.range : Set (twistedE6RootGroup K σ)) ∪
      {x : twistedE6RootGroup K σ | Commute x (ι z) ∧
        ∃ n : ℕ, x ^ (ringChar K ^ n) = 1}) ≤ H := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact hrange hx
    · exact Subgroup.subset_closure ⟨ι z, hιzE, hιz1, hx.1, hx.2⟩
  exact top_le_iff.1 (htop ▸ hle)

theorem twE6ThreeUniNative_two
    (q : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hq : q % 3 = 2)
    (hq3 : 3 ≤ q) (E₀ : Subgroup (twistedE6RootGroup K σ)) (hexp : ∀ x ∈ E₀, x ^ 3 = 1)
    (hcard : Nat.card E₀ = 3 ^ 2) (hn : ¬ NormalizesRIn (ringChar K) E₀) :
    Subgroup.closure {x | ∃ y ∈ E₀, y ≠ 1 ∧ Commute x y ∧
      ∃ n : ℕ, x ^ (ringChar K ^ n) = 1} = ⊤ := by
  have hq2 : 2 ≤ q := by omega
  obtain ⟨k, hkF, hkfin, hkalg, hkq, hkchar, hfix⟩ := exists_fixed_subfield q K σ hK hσ hq2
  have hσk : ∀ c : K, σ c = c ^ Nat.card k := fun c => by rw [hkq]; exact hσ c
  have hK' : Nat.card K = (Nat.card k) ^ 2 := by rw [hkq]; exact hK
  have hq' : Nat.card k % 3 = 2 := by rw [hkq]; exact hq
  have h3 : 3 ≤ Nat.card k := by rw [hkq]; exact hq3
  have hCont : TwHighPlaneContained_two :=
    twHighPlaneContained_two_of_frame
      (twE6HeisFrameNormalizesR_of_fixedElt twE6HeisFrameFixedElt_holds)
  obtain ⟨g₀, hg₀⟩ := hCont q K σ k hfix hK hσ hkq hq hq3 E₀ hexp hcard hn
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
  have hn3 : ¬ NormalizesRIn (ringChar k) E₃ := by
    rw [hkchar]
    exact not_normalizesRIn_of_map hn g₀ ι E₃ hι hE₃
  obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag k TwClass.f4Six.w (TwClass.w_theta TwClass.f4Six)
  have hnd : ¬ 3 ∣ Nat.card k := by omega
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi k hnd D₁
  obtain ⟨z, hzbc, hz1, -, -⟩ := f4TwistedFrame_of k hq' h3 D₁ ω hω
  obtain ⟨g₁, hg₁⟩ := exists_conj_twisted_z_mem langPlaneKillsRoot_F4 k hq' h3 D₁ ω hω z hzbc E₃
    hexp₃ hcardE₃ hn3
  have hcl := twE6UniClose_two σ hσk hfix hkchar hK' hq' h3 E₃ hexp₃ hcardE₃ hn3
    D₁ ω hω z hzbc hz1 g₁ hg₁
  have hE : (E₃.map (MulAut.conj g₁).toMonoidHom).map ι =
      E₀.map (MulAut.conj (ι g₁ * g₀)).toMonoidHom := by
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
  refine uniClosure_eq_top_of_conj (ι g₁ * g₀) ?_
  rw [← hE]
  exact hcl

theorem uniSeitzPlanes_twE6_inner_three_two :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.card % 3 = 2 ∧ q.card ≠ 2) ∧
      ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, ⟨q, hq, hmod, hne2⟩, hn⟩
  obtain rfl : d = .twistedE6 q := hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have hchK : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq3 : 3 ≤ q.card := by
    rcases Nat.lt_or_ge q.card 3 with h | h
    · rw [Nat.mod_eq_of_lt h] at hmod
      exact absurd hmod hne2
    · exact h
  have hqmod : (q.p ^ q.exponent) % 3 = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hmod
  have hq3' : 3 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq3
  have h := uniPlaneGen_of_native_uniClosure (p := 3) (r := ringChar K) e
    (conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)))
    (fun E₀ h1 h2 h3 => twE6ThreeUniNative_two (q.p ^ q.exponent) K σ hK hσ hqmod hq3'
      E₀ h1 h2
      (fun ⟨R, hR1, hRp, hRn⟩ => h3 ⟨R, hR1, hRp, fun g hg =>
        (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩))
    hE hc hin ?_
  · rw [hring] at h
    simpa using h
  · rintro ⟨R, hR1, hRp, hRn⟩
    refine hn ⟨R, hR1, ?_, hRn⟩
    show IsPGroup (TauCeti.LieTypeIndex.twistedE6 q).characteristic R
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6, ← hring]
    exact hRp

section


theorem twE6ThreeOpenInner_holds : TwE6ThreeOpenInner :=
  uniSeitzPlanes_twE6_inner_three_two

theorem seitzCoverFamExcRest2Rest_of_diag (hD : TwE6ThreeOpenDiag) :
    QuasiHigh5.SeitzCoverFamExcRest2Rest :=
  seitzCoverFamExcRest2Rest_of_open (twE6ThreeOpenPlanes_of twE6ThreeOpenInner_holds hD)

end

end CFSG.LieType.SeitzGeneration.QuasiHigh5E6Cover
