module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Amb
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Ree
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwG2
import CFSG.LieType.SeitzGeneration.ExtSeitzBridge
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.Ree

@[expose] def S2019ExcCoreIdx : TauCeti.LieTypeIndex → Prop
  | .G2 _ | .trialityD4 _ | .F4 _ | .E6 _ | .twistedE6 _ | .E7 _ | .E8 _ => True
  | _ => False

@[expose] def S2019FactExceptionalLie : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D J : Subgroup Ω), S.Normal →
      CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
      catalogIs (PSimple p S) (onLie fun d => d.characteristic = q ∧ S2019ExcCoreIdx d) →
      IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
      S2019Omega p S B D J

section ReeG2


private theorem false_of_pRank_le_one (hI : GL83.I_7_13_1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1) {A : Subgroup (MulAut S)}
    (hA : CFSG.Open.IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) : False := by
  have h3' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) :=
    H248.three_le_pRank_of_card hp hA h3
  have h2' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ 2 :=
    (hI p hp hp2 S hS hnab hcat hrk).2
  omega

private theorem exists_noncomm_of_elemAbelian_cube {p : ℕ} (hp : p.Prime)
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S) {A : Subgroup (MulAut S)}
    (hA : CFSG.Open.IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ a b : S, a * b ≠ b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ^ 2 ≤ Nat.card A :=
    (Nat.pow_le_pow_right hp.pos (by norm_num : 2 ≤ 3)).trans h3
  obtain ⟨E, hEcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card (G := ↥A) hp hA.isPGroup
      (by simpa using hp2)
  have hE : CFSG.Open.IsElemAbelian p (E.map A.subtype) :=
    hA.mono (Subgroup.map_subtype_le E)
  refine CFSG.LieType.SeitzGeneration.exists_noncommuting_of_isElementaryAbelian_aut
    (E := E.map A.subtype) hE.isElementaryAbelian ?_
  rw [Subgroup.card_map_of_injective A.subtype_injective, hEcard]

private theorem false_of_pRank_le_one_of_mulEquiv (hI : GL83.I_7_13_1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S Γ : Type} [Group S] [Finite S] [Group Γ] [Finite Γ]
    (hΓ : IsSimpleGroup Γ) (hrkΓ : CFSG.Open.pRank p (⊤ : Subgroup Γ) ≤ 1) (e : S ≃* Γ)
    (hcat : CFSG.Open.IsCatalogGroup S) {A : Subgroup (MulAut S)}
    (hAel : CFSG.Open.IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  have hS : IsSimpleGroup S := e.isSimpleGroup
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).le.trans hrkΓ
  exact false_of_pRank_le_one hI hp hp2 hS
    (exists_noncomm_of_elemAbelian_cube hp hS hAel hA3) hcat hrk hAel hA3

theorem false_of_reeG2_aut (hI : GL83.I_7_13_1) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    (hm : 1 ≤ m) {S : Type} [Group S] [Finite S] {hv : (TauCeti.LieTypeIndex.reeG2 m).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group)
    (hcat : CFSG.Open.IsCatalogGroup S) {A : Subgroup (MulAut S)}
    (hAel : CFSG.Open.IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) : False := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega
  haveI : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    inferInstanceAs (CharP (GaloisField 3 (2 * m + 1)) 3)
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  obtain ⟨ψ⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.nonempty_reeGamma_equiv hv
      (K := GaloisField 3 (2 * m + 1)) hK
  have hsimple : IsSimpleGroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) :=
    (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hm
      (GaloisField 3 (2 * m + 1)) hK).2.1
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(ReeTag.G2.reeGamma
      (GaloisField 3 (2 * m + 1)) m)) ≤ 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_le_one_reeGamma_G2
      m hm (GaloisField 3 (2 * m + 1)) hK hp hp5
  exact (false_of_pRank_le_one_of_mulEquiv hI hp (by omega) hsimple hrank (e.trans ψ) hcat
    hAel hA3).elim

theorem s2019FactExceptional_of_lie (h : S2019FactExceptionalLie) : S2019FactExceptional := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  obtain ⟨i, hi, e⟩ := hcat
  cases i with
  | cyclic r hr => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨d, hv⟩ := d
    obtain ⟨hchar, hncl⟩ := hi
    have hcore : ∀ (_ : S2019ExcCoreIdx d), S2019Omega p S B D J := fun hc =>
      h p q hp hp2 hq hq2 hqp Ω S B D J hSn hSq hSp
        ⟨TauCeti.CFSGIndex.lie ⟨d, hv⟩, ⟨hchar, hc⟩, e⟩ hBel hSB hrank
    cases d with
    | A n Q => exact absurd trivial hncl
    | twistedA n Q => exact absurd trivial hncl
    | B n Q => exact absurd trivial hncl
    | C n Q => exact absurd trivial hncl
    | D n Q => exact absurd trivial hncl
    | twistedD n Q => exact absurd trivial hncl
    | E6 Q => exact hcore trivial
    | E7 Q => exact hcore trivial
    | E8 Q => exact hcore trivial
    | F4 Q => exact hcore trivial
    | G2 Q => exact hcore trivial
    | twistedE6 Q => exact hcore trivial
    | trialityD4 Q => exact hcore trivial
    | suzuki m => exact absurd hchar.symm (by simpa using hq2)
    | reeF4 m => exact absurd hchar.symm (by simpa using hq2)
    | tits => exact absurd hchar.symm (by simpa using hq2)
    | reeG2 m =>
      intro hC hDB hCD hrel hD hJ hBJ hcm T hTS hT2 hJT
      exfalso
      have hq3 : q = 3 := by simpa using hchar.symm
      have hp3 : p ≠ 3 := fun hp3 => hqp (hq3.trans hp3.symm)
      have hm : 1 ≤ m := by
        have hr := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
        simpa using (TauCeti.LieTypeIndex.inStandardRange_iff _).mp hr
      let eS : PQuot p S ≃* ↥S :=
        (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
      let eSS : PSimple p S ≃* (↥S ⧸ Subgroup.center ↥S) :=
        QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
      obtain ⟨e₀⟩ := e
      obtain ⟨A, hA, hcard⟩ := exists_elemAbelian_aut_rank_ge_three hp hSn hSq hSp hBel hCD hrel hD
      exact false_of_reeG2_aut GL83.I713.i_7_13_1_holds hp hp2 hp3 hm (eSS.symm.trans e₀)
        ⟨TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩, ⟨eSS.symm.trans e₀⟩⟩ hA hcard

end ReeG2

end CFSG.LocalAnalysis.GLTheoremA.S2019

end
