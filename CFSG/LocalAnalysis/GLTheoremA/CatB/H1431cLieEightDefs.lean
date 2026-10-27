module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def LieSEightAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 → KD264Lie.fieldSize d.1 = 8 →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ ξ : MulAut Y, ξ ^ 3 = 1 → ξ ≠ 1 →
        inducedAut ξ ∈ innAutDerived (Y ⧸ Subgroup.center Y) →
        ∀ J : Subgroup Y,
          GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ξ) J →
          catalogIs (PSimple 3 J) S8.L84.isSp48 →
          (∃ τ : MulAut Y, τ ^ 3 = 1 ∧ Commute τ ξ ∧ ¬ InnerOnMod 3 J τ ∧ RkTau τ) →
          isSp68 (.lie d)

theorem lieSEight_of_at (h : LieSEightAt fun _ => True) : LieSEight :=
  fun Y _ _ hY hcore hRk d hc hf he ξ h3 h1 hin J hJ hT hτ =>
    h Y hY hcore hRk d trivial hc hf he ξ h3 h1 hin J hJ hT hτ

@[expose] def LieSEightNoAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ → RkY Y →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 → KD264Lie.fieldSize d.1 = 8 →
      Nonempty (Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut (Y ⧸ Subgroup.center Y), α ∈ innAutDerived (Y ⧸ Subgroup.center Y) →
        α ^ 3 = 1 → α ≠ 1 → ¬ CompOfType (Y ⧸ Subgroup.center Y) α S8.L84.isSp48

theorem lieSEight_image_component {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y)
    {ξ : MulAut Y} {J : Subgroup Y}
    (hJ : GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ξ) J)
    (hT : catalogIs (PSimple 3 J) S8.L84.isSp48) :
    CompOfType (Y ⧸ Subgroup.center Y) (inducedAut ξ) S8.L84.isSp48 := by
  obtain ⟨J', hJ', ψ, hψs, hψk⟩ := component_to_simple_explicit hJ
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ
  have hq' : CFSG.Open.IsQuasisimple (PQuot 3 J') :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isQuasisimple_quotient_of_glaPComponent hJ'
  haveI : Nontrivial (PQuot 3 J') := by
    have := hq'.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J' ⧸ Subgroup.center (PQuot 3 J'))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  obtain ⟨eP⟩ := CFSG.LocalAnalysis.GLTheoremA.psimple_equiv_of_central_surj hq ψ hψs hψk
  obtain ⟨i', hi', ⟨f⟩⟩ := hT
  exact ⟨J', hJ', i', hi', ⟨eP.symm.trans f⟩⟩

theorem lieSEightAt_of_noAt {P : TauCeti.LieTypeIndex → Prop} (h : LieSEightNoAt P) :
    LieSEightAt P := by
  rintro Y _ _ hY hcore hRk d hd hc hf he ξ h3 h1 hin J hJ hT -
  have hβ3 : inducedAut ξ ^ 3 = 1 := by
    rw [show inducedAut ξ = CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot Y ξ from rfl,
      ← map_pow, h3, map_one]
  have hβ1 : inducedAut ξ ≠ 1 := fun h' => h1 (eq_one_of_inducedAut_eq_one hY.1 h')
  exact (h Y hY hcore hRk d hd hc hf he _ hin hβ3 hβ1
    (lieSEight_image_component hY hJ hT)).elim

@[expose] def LieSEightOther : TauCeti.LieTypeIndex → Prop
  | .C _ _ | .G2 _ | .trialityD4 _ | .suzuki _ | .reeG2 _ | .tits => True
  | _ => False

theorem lieSEightAt_of_families
    (hA : LieSEightAt fun d => ∃ n q, d = .A n q)
    (htA : LieSEightAt fun d => ∃ n q, d = .twistedA n q)
    (hB : LieSEightAt fun d => ∃ n q, d = .B n q)
    (hD : LieSEightAt fun d => ∃ n q, d = .D n q)
    (htD : LieSEightAt fun d => ∃ n q, d = .twistedD n q)
    (hE : LieSEightAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q)
    (hF4 : LieSEightAt fun d => ∃ q, d = .F4 q)
    (htE6 : LieSEightAt fun d => ∃ q, d = .twistedE6 q)
    (hR : LieSEightAt fun d => ∃ m, d = .reeF4 m)
    (hO : LieSEightAt LieSEightOther) : LieSEightAt fun _ => True := by
  rintro Y _ _ hY hcore hRk ⟨d, hv⟩ - hc hf he ξ h3 h1 hin J hJ hT hτ
  cases d with
  | A n q => exact hA Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | twistedA n q => exact htA Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | B n q => exact hB Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | D n q => exact hD Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | twistedD n q => exact htD Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | E6 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inl rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | E7 q =>
    exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inr (Or.inl rfl)⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | E8 q =>
    exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inr (Or.inr rfl)⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | F4 q => exact hF4 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | twistedE6 q => exact htE6 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | reeF4 m => exact hR Y hY hcore hRk ⟨_, hv⟩ ⟨m, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  | C n q => exact hO Y hY hcore hRk ⟨_, hv⟩ trivial hc hf he ξ h3 h1 hin J hJ hT hτ
  | G2 q => exact hO Y hY hcore hRk ⟨_, hv⟩ trivial hc hf he ξ h3 h1 hin J hJ hT hτ
  | trialityD4 q => exact hO Y hY hcore hRk ⟨_, hv⟩ trivial hc hf he ξ h3 h1 hin J hJ hT hτ
  | suzuki m => exact hO Y hY hcore hRk ⟨_, hv⟩ trivial hc hf he ξ h3 h1 hin J hJ hT hτ
  | reeG2 m => exact hO Y hY hcore hRk ⟨_, hv⟩ trivial hc hf he ξ h3 h1 hin J hJ hT hτ
  | tits => exact hO Y hY hcore hRk ⟨_, hv⟩ trivial hc hf he ξ h3 h1 hin J hJ hT hτ

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
