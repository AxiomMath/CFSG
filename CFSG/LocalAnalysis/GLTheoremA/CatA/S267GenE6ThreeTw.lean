module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.E6ThreePlaneComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (TwistedE6DiagIsotropic)

section Transport


theorem exists_langTransport_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq4 : 4 ≤ ℓ ^ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {w : WeylGroup TwistTag.E6.tag}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    (J : Subgroup (twistedE6RootGroup K σ)) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 3)
      (J' : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))), 4 ≤ S.D.q ∧
      S.D.torus = twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      (∀ x : ↥(twistedE6InndiagGL K σ), IsComponentOf J (fixSubgroup (twistedE6InndiagConj K σ x)) →
        IsComponentOf J' (S.Γ ⊓ Subgroup.centralizer
          {g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0})) ∧
      (∀ x : ↥(twistedE6InndiagGL K σ), (∀ c ∈ J, twistedE6InndiagConj K σ x c = c) →
        ∀ y ∈ J', Commute (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0) y) := by
  obtain ⟨S, hq, hTor, hΓ⟩ := exists_langSetup_twE6 hℓ hℓ3 hf hq4 hK σ hσ hFr hg0C hg0
  set L := AlgebraicClosure K with hL
  set ι : ↥(twistedE6RootGroup K σ) →* ModGL TwistTag.E6.tag L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype) with hιdef
  have hι : ∀ c : ↥(twistedE6RootGroup K σ),
      ι c = g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL TwistTag.E6.tag K) * g0 := fun c => by
    change (MulAut.conj g0⁻¹) _ = _
    rw [MulAut.conj_apply, inv_inv]
    rfl
  have hιinj : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)
  have hrange : ι.range = S.Γ := by
    rw [hΓ, hιdef, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
  have hβ : ∀ (x : ↥(twistedE6InndiagGL K σ)) (c : ↥(twistedE6RootGroup K σ)),
      ι (twistedE6InndiagConj K σ x c) =
        (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * g0) * ι c *
          (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * g0)⁻¹ := by
    intro x c
    rw [hι, hι, twistedE6InndiagConj_apply, map_mul, map_mul, map_inv]
    group
  refine ⟨S, J.map ι, hq, hTor, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← hrange]
    exact isComponentOf_map_of_embedding ι hιinj _ _ (hβ x) hx
  · exact commute_of_fixed_of_embedding ι _ _ (hβ x) hx

end Transport

section Plane


theorem twE6Three_not_common_component_of_le_inndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq2 : ℓ ^ f ≠ 2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (J : Subgroup (twistedE6RootGroup K σ)) :
    ¬ ∀ x ∈ E, x ≠ 1 → IsComponentOf J (fixSubgroup x) := by
  classical
  intro hall
  set L := AlgebraicClosure K with hL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq4 : 4 ≤ ℓ ^ f :=
    four_le_of_not_three_dvd (le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)) h3 hq2
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  haveI : Finite K₁ := hK₁
  have hJfix : ∀ x ∈ E, ∀ c ∈ J, x c = c := fun x hx c hc => by
    by_cases hx1 : x = 1
    · rw [hx1, MulAut.one_apply]
    · exact (mem_fixSubgroup).1 ((hall x hx hx1).1 hc)
  by_cases hiso : TwistedE6DiagIsotropic K σ K₁ E
  ·
    have hEr : E ≤ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj]
      exact hd
    set E₀ : Subgroup ↥(twistedE6InndiagGL K σ) := E.comap (twistedE6InndiagConj K σ) with hE₀
    have hmap : E₀.map (twistedE6InndiagConj K σ) = E := Subgroup.map_comap_eq_self hEr
    have hexp : ∀ x ∈ E₀, x ^ 3 = 1 := fun x hx =>
      hinj (by rw [map_pow, map_one]; exact hE.2 _ hx)
    have hcard₀ : Nat.card E₀ = 3 ^ 2 := by
      rw [← Subgroup.card_map_of_injective hinj, hmap]
      exact hcard
    have hC₁ : ∀ x ∈ E₀, baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) ∈
        adjointGroup Tag.E6 K₁ := fun x _ =>
      map_twistedE6InndiagGL_le σ _ hroot (Subgroup.mem_map_of_mem _ x.2)
    obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hin⟩ :=
      twistedE6IsotropicToralInndiag_of_planeToralLang twistedE6PlaneToralLang_proved ℓ f hℓ hℓ3
        hf K hK σ hσ K₁ E₀ hexp hcard₀ hC₁ hiso
    obtain ⟨S, J', hq, hTor, hcomp, -⟩ :=
      exists_langTransport_twE6 hℓ hℓ3 hf hq4 hK σ hσ hFr hg0C hg0 J
    let θ : ↥(twistedE6InndiagGL K σ) →* ModGL TwistTag.E6.tag L :=
      (MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K L)).comp (twistedE6InndiagGL K σ).subtype)
    have hθ : ∀ x, θ x = g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) * g0 :=
      fun x => by simp [θ, MulAut.conj_apply]
    have hθinj : Function.Injective θ :=
      (MulAut.conj g0⁻¹).injective.comp
        ((baseChangeGL_injective _).comp Subtype.val_injective)
    have hD₁T : E₀.map θ ≤ S.D.torus := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hin x hx
      rw [hTor, hθ, ← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
      exact hy
    have hD₁exp : ∀ z ∈ E₀.map θ, z ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one]
    have hD₁card : Nat.card (E₀.map θ) = 3 ^ 2 := by
      rw [Subgroup.card_map_of_injective hθinj, hcard₀]
    refine false_of_common_component_of_le_torus_E6 S hq hD₁T hD₁exp hD₁card (J := J') ?_
    rintro _ ⟨x, hx, rfl⟩ hx1
    have hx1' : twistedE6InndiagConj K σ x ≠ 1 := fun h => hx1 (by
      rw [hinj (h.trans (map_one _).symm)]
      exact map_one θ)
    rw [hθ]
    exact hcomp x (hall _ hx hx1')
  ·
    obtain ⟨F⟩ := exists_twE6HeisenbergFrame ℓ f hℓ hℓ3 hf hK σ hσ K₁ hroot E
      hE.isElementaryAbelian hcard hd hiso
    obtain ⟨S, J', hq, hTor, hcomp, hcomm⟩ :=
      exists_langTransport_twE6 hℓ hℓ3 hf hq4 hK σ hσ F.hFr F.hg0C F.hg0 J
    have ha1 : rootDiagUnit TwistTag.E6.tag F.a ≠ 1 := by
      intro h1
      apply F.hsh
      have : F.a = 1 :=
        CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
      rw [this]
      simp [rootChar]
    have hg₁1 : twistedE6InndiagConj K σ F.g₁ ≠ 1 := by
      intro h
      have hg1 : F.g₁ = 1 := hinj (h.trans (map_one _).symm)
      apply ha1
      rw [← F.hg₁, hg1]
      simp
    have hJ' := hcomp F.g₁ (hall _ F.hE₁ hg₁1)
    rw [F.hg₁] at hJ'
    have hc := hcomm F.g₂ (hJfix _ F.hE₂)
    rw [F.hg₂] at hc
    exact false_of_heisenberg_component_E6 S hq F.ha3 (hTor ▸ F.hT) ha1 F.hw F.hsh F.hu hJ' hc

end Plane

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
