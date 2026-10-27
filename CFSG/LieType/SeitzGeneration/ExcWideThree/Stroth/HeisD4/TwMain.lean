module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.TwTheta
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.TwField
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.TwLift

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6


section Core

variable {L : Type} [Field L] [IsAlgClosed L]

theorem conj_twFrobE6_c0 (Fr : L →+* L) (s : WeylGroup Tag.E6) (h g : ModGL Tag.E6 L) :
    canonicalRep (coxeterSystem Tag.E6) L s *
      twFrobE6 ((canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ * h⁻¹ *
        canonicalRep (coxeterSystem Tag.E6) L twNeg *
        twistHomE6 Fr (canonicalRep (coxeterSystem Tag.E6) L s) *
        (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹ *
        canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr
        ((canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ * g *
          canonicalRep (coxeterSystem Tag.E6) L s) *
      (canonicalRep (coxeterSystem Tag.E6) L s)⁻¹ =
    (h⁻¹ * twTheta L) * Units.map (entrywiseHom Fr) g * (h⁻¹ * twTheta L)⁻¹ := by
  rw [twFrobE6_apply, map_mul, map_mul, map_inv, twistHomE6_apply Fr g]
  have hP : diagramMapE6 L = tw6P L := rfl
  rw [hP]
  simp only [twTheta]
  group

theorem twD_exists_x {K₀ : Type} [Field K₀] [Finite K₀] [Algebra K₀ L] [IsAlgClosure K₀ L]
    (hK3 : ringChar K₀ ≠ 3) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K₀)
    {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (hD : HeisClassD a w) :
    ∃ c₀ ∈ heisM a, ∀ y' : ModGL Tag.E6 L,
      y' ∈ Subgroup.normalizer (heisM a : Set (ModGL Tag.E6 L)) →
      (∃ m ∈ heisM a, y' = m * canonicalRep (coxeterSystem Tag.E6) L w) → y' ^ 3 = 1 →
      twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr y' = y' →
      ∃ x ∈ heisM a, x ≠ 1 ∧ x ^ ringChar K₀ = 1 ∧
        twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr x = x ∧ Commute x y' := by
  classical
  obtain ⟨s, hs, hw₀, hsh₀⟩ := stdPosition hD
  obtain ⟨h, hh, hΘ⟩ := twTheta_conj_on_Q (L := L)
  set ns := canonicalRep (coxeterSystem Tag.E6) L s with hns
  set c₀ := ns⁻¹ * h⁻¹ * canonicalRep (coxeterSystem Tag.E6) L twNeg *
    twistHomE6 Fr ns * (canonicalRep (coxeterSystem Tag.E6) L twNeg)⁻¹ with hc₀
  refine ⟨c₀, twC0_mem_heisM hs hh Fr, ?_⟩
  intro y' hyN ⟨m0, hm0, hy'm0⟩ hy'3 hFy'
  have hconj := map_conj_heisM (L := L) hs
  have hFrs : Function.Surjective Fr := fun c => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.card_pos (α := K₀))
    exact ⟨z, by rw [hFr, hz]⟩
  have hΦ : ∀ g : ModGL Tag.E6 L,
      ns * twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr (ns⁻¹ * g * ns) *
        ns⁻¹ = (h⁻¹ * twTheta L) * Units.map (entrywiseHom Fr) g * (h⁻¹ * twTheta L)⁻¹ := by
    intro g
    have := conj_twFrobE6_c0 Fr s h g
    exact this
  have hΦQ : ∀ x ∈ subsystemGroup Tag.E6 L d4Support,
      (h⁻¹ * twTheta L) * Units.map (entrywiseHom Fr) x * (h⁻¹ * twTheta L)⁻¹ =
        Units.map (entrywiseHom Fr) x := by
    intro x hx
    have h1 := hΘ _ (units_map_mem_subsystem Fr hx)
    calc (h⁻¹ * twTheta L) * Units.map (entrywiseHom Fr) x * (h⁻¹ * twTheta L)⁻¹
        = h⁻¹ * (twTheta L * Units.map (entrywiseHom Fr) x * (twTheta L)⁻¹) * h := by group
      _ = Units.map (entrywiseHom Fr) x := by rw [h1]; group
  set y'' := ns * y' * ns⁻¹ with hy''
  have hy''Φ : (h⁻¹ * twTheta L) * Units.map (entrywiseHom Fr) y'' * (h⁻¹ * twTheta L)⁻¹ = y'' := by
    rw [← hΦ y'']
    have e : ns⁻¹ * y'' * ns = y' := by rw [hy'']; group
    rw [e]
    change ns * twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr y' * ns⁻¹ = y''
    rw [hFy']
  have hy''3 : y'' ^ 3 = 1 := by
    have := conj_pow (a := ns) (b := y') (i := 3)
    rw [hy'', this, hy'3]
    group
  set g := ns * canonicalRep (coxeterSystem Tag.E6) L w * ns⁻¹ with hg
  have hm''mem : ns * m0 * ns⁻¹ ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support := by
    rw [← hconj]
    exact ⟨m0, hm0, rfl⟩
  have hy''eq : y'' = (ns * m0 * ns⁻¹) * g := by
    rw [hy'', hy'm0, hg]
    group
  have hgmono : g ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup' s)
      (canonicalRep_mem_monomialSubgroup' w)) (inv_mem (canonicalRep_mem_monomialSubgroup' s))
  have hgmaps : MapsRootLines g (s * w * s⁻¹) :=
    ((mapsRootLines_canonicalRep s).mul (mapsRootLines_canonicalRep w)).mul
      (mapsRootLines_canonicalRep s).inv
  obtain ⟨ε, hε, m, hm, hgeq⟩ := mono_decomp hgmono hgmaps hw₀ hsh₀
  have hmm : (ns * m0 * ns⁻¹) * m ∈ torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support :=
    mul_mem hm''mem hm
  have hy''β : y'' = ((ns * m0 * ns⁻¹) * m) * d4TrialityRep L ^ ε := by
    rw [hy''eq, hgeq]
    group
  have hnormQ : ∀ x ∈ subsystemGroup Tag.E6 L d4Support,
      y'' * x * y''⁻¹ ∈ subsystemGroup Tag.E6 L d4Support := by
    intro x hx
    obtain ⟨h', hh', -⟩ := d4Res_conj_y hmm ε ⟨x, hx⟩
    rw [← hy''β] at hh'
    rw [← hh']
    exact h'.2
  have hcomm : ∀ x ∈ subsystemGroup Tag.E6 L d4Support,
      Units.map (entrywiseHom Fr) (y'' * x * y''⁻¹) =
        y'' * Units.map (entrywiseHom Fr) x * y''⁻¹ := by
    intro x hx
    have h1 := hΦQ _ (hnormQ x hx)
    have h2 := hΦQ x hx
    rw [← h1]
    set Φ₂ : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
      (MulAut.conj (h⁻¹ * twTheta L)).toMonoidHom.comp (Units.map (entrywiseHom Fr)) with hΦ₂
    have e : ∀ z, Φ₂ z = (h⁻¹ * twTheta L) * Units.map (entrywiseHom Fr) z *
        (h⁻¹ * twTheta L)⁻¹ := fun z => rfl
    have hΦy : Φ₂ y'' = y'' := by rw [e]; exact hy''Φ
    calc Φ₂ (y'' * x * y''⁻¹) = Φ₂ y'' * Φ₂ x * (Φ₂ y'')⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = y'' * Units.map (entrywiseHom Fr) x * y''⁻¹ := by rw [hΦy, e x, h2]
  obtain ⟨x'', hxQ, hx1, hxℓ, hxF, hxc⟩ := exists_fixed_ell_std_tw (K := K₀) hK3 Fr hFr hε hmm hy''β
    hy''3 hcomm
  have hxM : ns⁻¹ * x'' * ns ∈ heisM a := by
    refine mem_heisM_of_conj_mem hs ?_
    have e : ns * (ns⁻¹ * x'' * ns) * ns⁻¹ = x'' := by group
    rw [e]
    exact Subgroup.mem_sup_right hxQ
  refine ⟨ns⁻¹ * x'' * ns, hxM, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hx1
    have : x'' = ns * (ns⁻¹ * x'' * ns) * ns⁻¹ := by group
    rw [this, h1]
    group
  · have := conj_pow (a := ns⁻¹) (b := x'') (i := ringChar K₀)
    rw [inv_inv] at this
    rw [this, hxℓ]
    group
  · have h1 := hΦ x''
    rw [hΦQ x'' hxQ, hxF] at h1
    have h2 : ns⁻¹ * (ns * twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr
        (ns⁻¹ * x'' * ns) * ns⁻¹) * ns = ns⁻¹ * x'' * ns := by rw [h1]
    calc twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr (ns⁻¹ * x'' * ns)
        = ns⁻¹ * (ns * twFrobE6 (c₀ * canonicalRep (coxeterSystem Tag.E6) L twNeg) Fr
            (ns⁻¹ * x'' * ns) * ns⁻¹) * ns := by group
      _ = ns⁻¹ * x'' * ns := h2
  · have h2 : y'' * x'' = x'' * y'' := hxc
    rw [hy''] at h2
    show (ns⁻¹ * x'' * ns) * y' = y' * (ns⁻¹ * x'' * ns)
    calc (ns⁻¹ * x'' * ns) * y' = ns⁻¹ * (x'' * (ns * y' * ns⁻¹)) * ns := by group
      _ = ns⁻¹ * ((ns * y' * ns⁻¹) * x'') * ns := by rw [← h2]
      _ = y' * (ns⁻¹ * x'' * ns) := by group

end Core

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4


theorem twE6HeisFrameFixedEltD_holds : TwE6HeisFrameFixedEltD := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ E hE hEab hcard F hD
  classical
  obtain ⟨K₀, _, _, _, hK₀alg, hK₀card, hK₀char⟩ := exists_fixedField_data hℓ hf hK σ hσ
  have hK3 : ringChar K₀ ≠ 3 := by rw [hK₀char]; exact hℓ3
  have hFr : ∀ c, F.Fr c = c ^ Nat.card K₀ := fun c => by rw [F.hFr c, hK₀card]
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  refine twFrame_exists_fixedElt_of_exists_x hℓ hℓ3 hf hK σ hσ hEab F ?_
  obtain ⟨c₀, hc₀, hx⟩ := twD_exists_x (K₀ := K₀) hK3 F.Fr hFr hD
  refine ⟨c₀, hc₀, fun y' hyN hym hy3 hFy' => ?_⟩
  obtain ⟨x, hxM, hx1, hxℓ, hxF, hxc⟩ := hx y' hyN hym hy3 hFy'
  exact ⟨x, hxM, hx1, by rw [← hK₀char]; exact hxℓ, hxF, hxc⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree
