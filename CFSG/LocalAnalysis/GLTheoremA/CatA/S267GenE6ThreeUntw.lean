module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenE6ThreeLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.E6ThreePlaneComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic)

section Transport


theorem exists_langTransport_e6 {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    (hK4 : 4 ≤ Nat.card K) {w : WeylGroup Tag.E6}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (J : Subgroup (adjointGroup Tag.E6 K)) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 3)
      (J' : Subgroup (ModGL Tag.E6 (AlgebraicClosure K))), 4 ≤ S.D.q ∧
      S.D.torus = twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
        (Units.map (entrywiseHom Fr)) ∧
      (∀ x : ↥(e6InndiagGL K), IsComponentOf J (fixSubgroup (e6InndiagConj K x)) →
        IsComponentOf J' (S.Γ ⊓ Subgroup.centralizer
          {g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E6 K) * g0})) ∧
      (∀ x : ↥(e6InndiagGL K), (∀ c ∈ J, e6InndiagConj K x c = c) →
        ∀ y ∈ J', Commute (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL Tag.E6 K) * g0) y) := by
  obtain ⟨S, hq, hTor, hΓ⟩ := exists_langSetup_e6 hK3 hK4 hFr hg0C hg0
  set L := AlgebraicClosure K with hL
  set ι : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E6 K).subtype) with hιdef
  have hι : ∀ c : ↥(adjointGroup Tag.E6 K),
      ι c = g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL Tag.E6 K) * g0 := fun c => by
    change (MulAut.conj g0⁻¹) _ = _
    rw [MulAut.conj_apply, inv_inv]
    rfl
  have hιinj : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp Subtype.val_injective)
  have hrange : ι.range = S.Γ := by
    rw [hΓ, hιdef, MonoidHom.range_comp]
  have hβ : ∀ (x : ↥(e6InndiagGL K)) (c : ↥(adjointGroup Tag.E6 K)),
      ι (e6InndiagConj K x c) =
        (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E6 K) * g0) * ι c *
          (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E6 K) * g0)⁻¹ := by
    intro x c
    rw [hι, hι, e6InndiagConj_apply, map_mul, map_mul, map_inv]
    group
  refine ⟨S, J.map ι, hq, hTor, fun x hx => ?_, fun x hx => ?_⟩
  · rw [← hrange]
    exact isComponentOf_map_of_embedding ι hιinj _ _ (hβ x) hx
  · exact commute_of_fixed_of_embedding ι _ _ (hβ x) hx

end Transport

section Plane


theorem e6Three_not_common_component_of_le_inndiag {K : Type} [Field K] [Finite K]
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hd : E ≤ e6Inndiag K) (J : Subgroup (adjointGroup Tag.E6 K)) :
    ¬ ∀ x ∈ E, x ≠ 1 → IsComponentOf J (fixSubgroup x) := by
  classical
  intro hall
  set L := AlgebraicClosure K with hL
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  haveI : Finite K₁ := hK₁
  have hinj := e6InndiagConj_injective K hK4
  have h3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar K hK3
  have hJfix : ∀ x ∈ E, ∀ c ∈ J, x c = c := fun x hx c hc => by
    by_cases hx1 : x = 1
    · rw [hx1, MulAut.one_apply]
    · exact (mem_fixSubgroup).1 ((hall x hx hx1).1 hc)
  by_cases hiso : E6DiagIsotropic K K₁ E
  ·
    have hEr : E ≤ (e6InndiagConj K).range := by
      rw [range_e6InndiagConj]
      exact hd
    set E₀ : Subgroup ↥(e6InndiagGL K) := E.comap (e6InndiagConj K) with hE₀
    have hmap : E₀.map (e6InndiagConj K) = E := Subgroup.map_comap_eq_self hEr
    have hexp : ∀ x ∈ E₀, x ^ 3 = 1 := fun x hx =>
      hinj (by rw [map_pow, map_one]; exact hE.2 _ hx)
    have hcard₀ : Nat.card E₀ = 3 ^ 2 := by
      rw [← Subgroup.card_map_of_injective hinj, hmap]
      exact hcard
    have hC₁ : ∀ x ∈ E₀, baseChangeGL (algebraMap K K₁) (x : ModGL Tag.E6 K) ∈
        adjointGroup Tag.E6 K₁ := fun x _ =>
      map_e6InndiagGL_le _ hroot (Subgroup.mem_map_of_mem _ x.2)
    obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hin⟩ := e6IsotropicToralInndiag_of_planeToralLang
      e6PlaneToralLang_proved K h3 K₁ E₀ hexp hcard₀ hC₁ (fun x y hx hy => hiso x y hx hy)
    obtain ⟨S, J', hq, hTor, hcomp, -⟩ := exists_langTransport_e6 h3 hK4 hFr hg0C hg0 J
    let θ : ↥(e6InndiagGL K) →* ModGL Tag.E6 L :=
      (MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K L)).comp (e6InndiagGL K).subtype)
    have hθ : ∀ x, θ x = g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL Tag.E6 K) * g0 :=
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
    have hx1' : e6InndiagConj K x ≠ 1 := fun h => hx1 (by
      rw [hinj (h.trans (map_one _).symm), map_one])
    rw [hθ]
    exact hcomp x (hall _ hx hx1')
  ·
    obtain ⟨F⟩ := exists_e6HeisenbergFrame hK3 hK4 K₁ hroot E hE.isElementaryAbelian hcard hd hiso
    obtain ⟨S, J', hq, hTor, hcomp, hcomm⟩ := exists_langTransport_e6 h3 hK4 F.hFr F.hg0C F.hg0 J
    have ha1 : rootDiagUnit Tag.E6 F.a ≠ 1 := by
      intro h1
      apply F.hsh
      have : F.a = 1 :=
        CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
      rw [this]
      simp [rootChar]
    have hg₁1 : e6InndiagConj K F.g₁ ≠ 1 := by
      intro h
      apply ha1
      rw [← F.hg₁, hinj (h.trans (map_one _).symm)]
      simp
    have hJ' := hcomp F.g₁ (hall _ F.hE₁ hg₁1)
    rw [F.hg₁] at hJ'
    have hc := hcomm F.g₂ (hJfix _ F.hE₂)
    rw [F.hg₂] at hc
    exact false_of_heisenberg_component_E6 S hq F.ha3 (hTor ▸ F.hT) ha1 F.hw F.hsh F.hu hJ' hc

end Plane

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
