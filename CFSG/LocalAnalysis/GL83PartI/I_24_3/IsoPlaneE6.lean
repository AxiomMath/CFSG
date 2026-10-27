module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.IsoPlane
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6IsoPlaneLarge
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6IsoPlaneLarge
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TorusLower
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwRank

public section

namespace GL83.I243

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars true

section E6


theorem Cfg.false_of_e6 {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {B K : Subgroup X}
    {z : X} (h : Cfg 3 R B K z) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.E6 q).Valid} (hq : q.card % 3 = 1)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Cat ⟨.E6 q, hv⟩)
    (hZ : 3 ∣ Nat.card (Subgroup.center ↥K)) : False := by
  obtain ⟨F, _, _, hFq, -, ⟨e'⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hF3 : 3 ∣ Nat.card F - 1 := by
    rw [hFq]
    omega
  set π : ↥K →* ↥(adjointGroup Tag.E6 F) := e'.toMonoidHom.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))) with hπ
  have hπs : Function.Surjective π :=
    e'.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center ↥K := by
    intro x
    simp [hπ, QuotientGroup.eq_one_iff]
  have h6 := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.six_le_pRank_of_cover_E6 hF3 π hπs hker hZ
  exact h.false_of_largePlane e (h.pow_le_card_of_le_pRank (k := 5) (by omega))
    (fun Ē hĒ hc => exists_planeGen_of_large_E6 hv hq hĒ hc)

end E6

section TwE6


theorem Cfg.false_of_twE6 {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {B K : Subgroup X}
    {z : X} (h : Cfg 3 R B K z) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid} (hq : q.card % 3 = 2)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Cat ⟨.twistedE6 q, hv⟩)
    (hZ : 3 ∣ Nat.card (Subgroup.center ↥K)) : False := by
  classical
  obtain ⟨F, _, σ, hF, hσ, ⟨e'⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hF]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP F q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul])
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact hσ x
  have h3 : 3 ∣ q.p ^ q.exponent + 1 := by
    rw [← TauCeti.PrimePower.card_def]
    omega
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect TwistTag.E6 q.prime_p
    q.exponent_pos F hF σ.toRingHom hσ''
  let e2 : ↥(twistedE6RootGroup F σ) ≃*
      ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ.toRingHom) :=
    (MulEquiv.subgroupCongr hΓ).symm
  set π : ↥K →* ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ.toRingHom) :=
    e2.toMonoidHom.comp (e'.toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)))) with hπ
  have hπs : Function.Surjective π :=
    e2.surjective.comp (e'.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center ↥K := by
    intro x
    change e2 (e' (e (QuotientGroup.mk x))) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
  haveI : Finite ↥(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twDerived σ.toRingHom) :=
    Subtype.finite
  have h6 := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.six_le_pRank_of_cover_twE6 σ.toRingHom
    q.exponent_pos h3 hF hσ'' π hπs hker hZ
  exact h.false_of_largePlane e (h.pow_le_card_of_le_pRank (k := 5) (by omega))
    (fun Ē hĒ hc => exists_planeGen_of_large_twE6 hv hq hĒ hc)

end TwE6

end GL83.I243
