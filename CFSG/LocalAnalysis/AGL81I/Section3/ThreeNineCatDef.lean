module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatCross
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.ListDefs
public import CFSG.LieType.DefCharRankFour
import CFSG.RankThree.PartOne.S11c.OuterInner
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open TauCeti
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaOver)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_centralizing_of_pRank_le_one {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {K E : Subgroup X} (hKn : K.Normal) (hZ : Subgroup.center ↥K = ⊥)
    (hout : ¬ p ∣ Nat.card (Outer ↥K)) (hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 1)
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    ∃ x ∈ E, x ≠ 1 ∧ ∀ c ∈ K, x * c = c * x := by
  have : K.Normal := hKn
  let ρ : ↥E →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp E.subtype
  have hρp : ∀ x : ↥E, ρ x ^ p = 1 := fun x => by
    rw [← map_pow]
    have hx : x ^ p = 1 := Subtype.ext (hE.2 x x.2)
    rw [hx, map_one]
  have hinn : ∀ x : ↥E, ρ x ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := fun x =>
    CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer hp hout (ρ x) (hρp x)
  have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    intro a b hab
    have h1 : ∀ x : ↥K, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
      simpa using DFunLike.congr_fun hab x
    have hmem : b⁻¹ * a ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [← h1 g]
        _ = b⁻¹ * a * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  let σ : ↥E →* ↥K :=
    ((MonoidHom.ofInjective hinj).symm : ↥(MulAut.conj : ↥K →* MulAut ↥K).range →* ↥K).comp
      (ρ.codRestrict _ hinn)
  have hσρ : ∀ x : ↥E, MulAut.conj (σ x) = ρ x := fun x =>
    MonoidHom.apply_ofInjective_symm hinj ⟨ρ x, hinn x⟩
  by_cases hσ : Function.Injective σ
  · exfalso
    have hcard : Nat.card σ.range = p ^ 2 := by
      rw [← hEc]
      exact (Nat.card_congr (MonoidHom.ofInjective hσ).toEquiv).symm
    have hel : IsElemAbelian p σ.range := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
      · obtain ⟨a, x, rfl⟩ := a
        obtain ⟨b, y, rfl⟩ := b
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← map_mul, ← map_mul, hE.1.is_comm.comm x y]
      · obtain ⟨x, rfl⟩ := ha
        have hx : x ^ p = 1 := Subtype.ext (hE.2 x x.2)
        rw [← map_pow, hx, map_one]
    have := CFSG.SectionRank.le_pRank hp.one_lt (le_top : σ.range ≤ ⊤) hel hcard
    omega
  · rw [injective_iff_map_eq_one] at hσ
    push Not at hσ
    obtain ⟨x, hx, hx1⟩ := hσ
    refine ⟨x, x.2, fun h => hx1 (Subtype.ext h), fun c hc => ?_⟩
    have hρx : ρ x = 1 := by rw [← hσρ x, hx, map_one]
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hρx ⟨c, hc⟩)
    change (x : X) * c * (x : X)⁻¹ = c at h1
    calc (x : X) * c = (x : X) * c * (x : X)⁻¹ * x := by group
      _ = c * x := by rw [h1]

theorem lieDef_rank_three_cases (hexc : CFSG.LieType.DefCharRankFourExc)
    (hG2 : CFSG.TauCetiBridge.UntwistedBridge .G2 LieTypeIndex.G2)
    {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {d : ValidLieTypeIndex} (hpd : p = d.1.characteristic) (e : K ≃* (CFSGIndex.lie d).Group)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3) :
    (∃ q : PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 1 q) ∨
      StatedClassicalModel K .PSL 2 p 2 ∨ StatedClassicalModel K .PSL 2 p 3 ∨
      IsPSLType 3 (ZMod p) K ∨ StatedClassicalModel K .PSU 3 p 1 ∨
      StatedClassicalModel K .PSp 2 p 1 ∨ CFSG.Blueprint.ChevalleyExceptionalModel K .G2 p 1 := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    obtain rfl : p = q.p := by simpa using hpd
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
    rcases hcases with ⟨-, ⟨hn, hr⟩ | ⟨hn, hr⟩ | hr⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
    · obtain rfl : r = 1 := by omega
      rcases (show q.exponent = 1 ∨ q.exponent = 2 ∨ q.exponent = 3 by omega) with h1 | h2 | h3
      · exact Or.inl ⟨q, rfl, h1, rfl⟩
      · rw [h2] at hm
        exact Or.inr (Or.inl hm)
      · rw [h3] at hm
        exact Or.inr (Or.inr (Or.inl hm))
    · obtain rfl : r = 2 := by omega
      have h1 : q.exponent = 1 := by omega
      rw [h1] at hm
      have : NeZero q.p := ⟨q.prime_p.ne_zero⟩
      have hcard : Nat.card (ZMod q.p) = q.p ^ 1 := by rw [pow_one, Nat.card_zmod]
      obtain ⟨φ⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod q.p) 3 q.p 1 one_pos
        hcard hm
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ⟩)))
    · omega
    · cases ht
    · cases ht
    · omega
  | twistedA r q =>
    obtain rfl : p = q.p := by simpa using hpd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
    rcases hcases with ⟨ht, -⟩ | ⟨-, ⟨hn, hr⟩ | hr⟩ | ⟨ht, -⟩ | hr
    · cases ht
    · obtain rfl : r = 2 := by omega
      have h1 : q.exponent = 1 := by omega
      rw [h1] at hm
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
    · omega
    · cases ht
    · omega
  | B r q =>
    obtain rfl : p = q.p := by simpa using hpd
    have hr2 : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
      rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, ⟨hn, hr⟩ | hr⟩ | hr
      · cases ht
      · cases ht
      · have h1 : q.exponent = 1 := by omega
        rw [h1] at hm
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))
      · omega
      · omega
    · exfalso
      have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e
      obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
      rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
      · cases ht
      · cases ht
      · cases ht
      · omega
  | C r q =>
    exfalso
    obtain rfl : p = q.p := by simpa using hpd
    have hr3 : 3 ≤ r := hrange.1
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
    rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, ⟨hn, hr⟩ | hr⟩ | hr
    · cases ht
    · cases ht
    · omega
    · omega
    · omega
  | D r q =>
    exfalso
    obtain rfl : p = q.p := by simpa using hpd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
    rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
    · cases ht
    · cases ht
    · cases ht
    · omega
  | twistedD r q =>
    exfalso
    obtain rfl : p = q.p := by simpa using hpd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
    obtain ⟨-, hf, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
    rcases hcases with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
    · cases ht
    · cases ht
    · cases ht
    · omega
  | E6 q =>
    exfalso
    have := hexc K ⟨.E6 q, hv⟩ ⟨e⟩ p hp hp2 hpd (Or.inl ⟨q, rfl⟩)
    omega
  | E7 q =>
    exfalso
    have := hexc K ⟨.E7 q, hv⟩ ⟨e⟩ p hp hp2 hpd (Or.inr (Or.inl ⟨q, rfl⟩))
    omega
  | E8 q =>
    exfalso
    have := hexc K ⟨.E8 q, hv⟩ ⟨e⟩ p hp hp2 hpd (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))
    omega
  | F4 q =>
    exfalso
    have := hexc K ⟨.F4 q, hv⟩ ⟨e⟩ p hp hp2 hpd (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))
    omega
  | twistedE6 q =>
    exfalso
    have := hexc K ⟨.twistedE6 q, hv⟩ ⟨e⟩ p hp hp2 hpd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))
    omega
  | trialityD4 q =>
    exfalso
    have := hexc K ⟨.trialityD4 q, hv⟩ ⟨e⟩ p hp hp2 hpd
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))
    omega
  | G2 q =>
    obtain rfl : p = q.p := by simpa using hpd
    rcases (show q.exponent = 1 ∨ 2 ≤ q.exponent by have := q.exponent_pos; omega) with h1 | h2
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
      have hmod := CFSG.TauCetiBridge.untwistedModel_of_bridge hG2 q hv hp2 e
      rw [h1] at hmod
      exact ⟨⟨hp, le_rfl, rfl, by rw [pow_one]; omega⟩, hmod⟩
    · exfalso
      have := hexc K ⟨.G2 q, hv⟩ ⟨e⟩ q.p hp hp2 hpd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl, h2⟩))))))
      omega
  | suzuki m =>
    exfalso
    have : p = 2 := by simpa using hpd
    omega
  | reeG2 m =>
    exfalso
    have : p = 3 := by simpa using hpd
    omega
  | reeF4 m =>
    exfalso
    have : p = 2 := by simpa using hpd
    omega
  | tits =>
    exfalso
    have : p = 2 := by simpa using hpd
    omega

theorem lieDef_of_catalogue24_12_five_of_exc (hPC : GL83.I243.PCoverList)
    (hexc : CFSG.LieType.DefCharRankFourExc)
    (hG2 : CFSG.TauCetiBridge.UntwistedBridge .G2 LieTypeIndex.G2) {X : Type} [Group X]
    [Finite X] {K E : Subgroup X} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hKq : CFSG.IsQuasisimple ↥K) (hOp : CFSG.pPrimeCore p ↥K = ⊥) (hKn : K.Normal)
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver 1 p E K)
    {d : TauCeti.ValidLieTypeIndex} (hpd : p = d.1.characteristic)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.StatedClassicalModel ↥K .PSL 2 p 2 ∨ CFSG.Open.StatedClassicalModel ↥K .PSL 2 p 3 ∨
      IsPSLType 3 (ZMod p) ↥K ∨ CFSG.Open.StatedClassicalModel ↥K .PSU 3 p 1 ∨
      CFSG.Open.StatedClassicalModel ↥K .PSp 2 p 1 ∨
      CFSG.Blueprint.ChevalleyExceptionalModel ↥K .G2 p 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : K.Normal := hKn
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hZp : IsPGroup p (Subgroup.center ↥K) :=
      CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥K) inferInstance inferInstance hOp
    by_contra hne
    have hdvd : p ∣ Nat.card (Subgroup.center ↥K) :=
      hZp.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
    rcases hPC ↥K ⟨Group.isPerfect_def.mp hKq.1, hKq.2.1⟩ p hp hp2 hdvd
      (CFSGIndex.lie d) ⟨e⟩ with ⟨d', hd', hne', -, -⟩ | ⟨h3, -⟩
    · have := CFSGIndex.lie.inj hd'
      subst this
      exact hne' hpd
    · omega
  let eK : ↥K ≃* (CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  have hrkK : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 3 := by
    rw [CFSG.AGLEmbeddingD2.pRank_top_subgroup_eq hp]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left).trans hrk
  rcases lieDef_rank_three_cases hexc hG2 hp hp5 hpd eK hrkK with ⟨q, hqp, hq1, hd1⟩ | h
  ·
    exfalso
    apply hΓ
    have hsmall : CFSG.AGLEmbeddingD2.IsD2LieCharSmall p d.1 :=
      ⟨q, hqp, Or.inl ⟨by omega, hd1⟩⟩
    have hout := CFSG.AGLEmbeddingD2.kFactLieCharOut ↥K d ⟨eK⟩ p hp hp2 hsmall
    have hr1 := CFSG.AGLEmbeddingD2.kFactLinTwoPrimeRank ↥K d ⟨eK⟩ p hp hp2 ⟨q, hqp, hq1, hd1⟩
    obtain ⟨x, hxE, hx1, hxc⟩ := exists_centralizing_of_pRank_le_one hp hKn hZ hout hr1 hE hEc
    intro c hcK
    exact mem_gammaOver_of_commute hp hxE hx1 (hE.2 x hxE) hcK (hxc c hcK)
  · exact h

theorem lieDef_of_catalogue24_12_five
    (hPC : GL83.I243.PCoverList) {X : Type} [Group X]
    [Finite X] {K E : Subgroup X} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hKq : CFSG.IsQuasisimple ↥K) (hOp : CFSG.pPrimeCore p ↥K = ⊥) (hKn : K.Normal)
    (hE : CFSG.Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3)
    (hΓ : ¬ K ≤ CFSG.LocalAnalysis.AGL81TheoremCD.Section12.gammaOver 1 p E K)
    {d : TauCeti.ValidLieTypeIndex} (hpd : p = d.1.characteristic)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.StatedClassicalModel ↥K .PSL 2 p 2 ∨ CFSG.Open.StatedClassicalModel ↥K .PSL 2 p 3 ∨
      IsPSLType 3 (ZMod p) ↥K ∨ CFSG.Open.StatedClassicalModel ↥K .PSU 3 p 1 ∨
      CFSG.Open.StatedClassicalModel ↥K .PSp 2 p 1 ∨
      CFSG.Blueprint.ChevalleyExceptionalModel ↥K .G2 p 1 :=
  lieDef_of_catalogue24_12_five_of_exc hPC CFSG.LieType.defCharRankFourExc
    CFSG.TauCetiBridge.chevalleyBridges.g2 hp hp5 hKq hOp hKn hE hEc hrk hΓ hpd e

end CFSG.LocalAnalysis.AGL81I.Section3
