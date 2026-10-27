module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116c
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSmallTypes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz5

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (ExcIndex IsSixIndex IsTwoPow Bal207Index IsL2EightIndex
  IsF4EightIndex IsD4FourIndex FourIndex Gen2318Index Bal209TwoIndex IsTwistedE6FourIndex Seitz2310CubeSimple)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple onLie ambiguousChev)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open GL83.CompFam

set_option linter.unusedSectionVars false

@[expose] def Input23_19ExcRes : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) →
      p ^ (CFSG.Open.pRank p B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex p d.1 → d.1 ≠ .tits → d.1 ≠ .suzuki 2 → ¬ IsL2EightIndex d.1 →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (Subgroup.center ↥K ≠ ⊥ ∨ B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∨
          IsD2SeitzException p d.1) →
        K ≤ GLBCore p 2 B

@[expose] def Rank3CuResExcRes : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → ∀ {U : Subgroup G}, IsU1312 p B M D L0 d U →
      ∀ u ∈ U, u ≠ 1 →
        CFSG.Open.pRank 3 B < CFSG.Open.pRank 3 (⊤ : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) →
        ∀ Kc : Subgroup G, GLAPComponent 3 (Cg u) Kc → Prop1310a5b.Good2319 (barOf 3 Kc) →
          B ≤ Subgroup.normalizer (Kc : Set G) →
          CFSG.Open.pRank 3 B < 2 + CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 Kc))) →
          CFSG.Open.pRank 3 (barX 3 (Cg u) B ⊓
            Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
              Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u)))) ≤ 1 →
          ¬ IsPiGroup 3 (barOf 3 Kc) →
          IsStronglyLocallyOneBalanced 3 B u Kc →
          ((∃ n : ℕ, 9 ≤ n ∧ n % 3 ≠ 2 ∧ IsAltType n (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc))) ∨
            ∃ i : TauCeti.ValidLieTypeIndex,
              Nonempty (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc) ≃* (TauCeti.CFSGIndex.lie i).Group) ∧
              i.1.characteristic ≠ 3 ∧
              ExcIndex 3 i.1 ∧ i.1 ≠ .tits ∧ ¬ IsL2EightIndex i.1 ∧
              (IsSixIndex i.1 → ¬ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
                (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range) ∧
              (Subgroup.center (barOf 3 Kc) ≠ ⊥ ∨
                barX 3 (Cg u) B ⊓
                  Subgroup.centralizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
                    Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) = ⊥ ∨
                IsD2SeitzException 3 i.1)) →
          Kc ≤ M

theorem characteristic_eq_two_of_excIndex {p : ℕ} {d : TauCeti.LieTypeIndex} (h : ExcIndex p d) :
    d.characteristic = 2 := by
  by_contra hc
  cases d <;> simp_all [ExcIndex, Bal207Index, IsL2EightIndex, Gen2318Index, Bal209TwoIndex,
    IsTwistedE6FourIndex, IsSixIndex, IsF4EightIndex, IsD4FourIndex, FourIndex, IsTwoPow]

theorem eq_three_or_five_of_excIndex_tits {p : ℕ} (h : ExcIndex p .tits) : p = 3 ∨ p = 5 := by
  rcases h with h | ⟨h, -⟩
  · exact h
  · exact Or.inl h

theorem eq_five_of_excIndex_suzuki {p m : ℕ} (h : ExcIndex p (.suzuki m)) : p = 5 := by
  rcases h with h | ⟨-, h⟩
  · simp only [Bal207Index] at h
    exact h.1
  · simp [IsL2EightIndex, Gen2318Index, Bal209TwoIndex, IsTwistedE6FourIndex, IsSixIndex, IsF4EightIndex,
      IsD4FourIndex, FourIndex] at h

theorem eq_three_of_excIndex_A {p r : ℕ} {q : TauCeti.PrimePower} (h : ExcIndex p (.A r q)) : p = 3 := by
  rcases h with h | ⟨h, -⟩
  · simp [Bal207Index] at h
  · exact h

theorem autIm_mono {Y : Type} [Group Y] {E B : Subgroup Y} (h : E ≤ B) (K : Subgroup Y) :
    InputsSeitz3.autIm E K ≤ InputsSeitz3.autIm B K := by
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hn)), rfl⟩

theorem pRank_mulAut_le_quot {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (K ⧸ Subgroup.center K))) :=
  CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (quotientCenterAut' K)
    (quotientCenterAut'_injective hperf)

section Dispatch


theorem pRank_three_mulAut_le_two_of_tits
    {S : Type} [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 2 := by
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hE
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have h1 : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at hlt
    exact absurd hlt (not_lt.2 h1)
  obtain ⟨D, hD⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 3 ∣ Nat.card E by rw [hk]; exact pow_dvd_pow 3 hk3)
  set φ : MulAut S →* MulAut (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := (MulAut.congr e).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.congr e).injective
  have hDel : IsElemAbelian 3 ((D.map E.subtype).map φ) :=
    CFSG.SectionRank.isElemAbelian_map (elem_mono hE (Subgroup.map_subtype_le D)) φ
  refine CFSG.HardMathSupport.Timmesfeld.CrossChar.titsNoElemAbelian27 hv _ hDel ?_
  rw [Subgroup.card_map_of_injective hφ, Subgroup.card_map_of_injective E.subtype_injective, hD]
  norm_num

theorem pRank_five_mulAut_le_two_of_suzuki
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .suzuki 2) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (MulAut S)) ≤ 2 := by
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  have hX : CFSG.Blueprint.LieModel S .twistedB2 0 2 (2 * 2 + 1) :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
        (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_lie (t := .twistedB2) (p := 2)
          (f := 2 * 2 + 1) ⟨Nat.prime_two, by omega, rfl, rfl, ⟨2, rfl⟩, by omega⟩ ⟨.suzuki 2, hv⟩
          ⟨rfl, rfl⟩))
  have hS : CFSG.Blueprint.SuzukiModel S 2 (2 * 2 + 1) := (CFSG.Blueprint.LieModel.suzukiModel hX).2
  have hZ : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple hs hnab
  refine (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer Nat.prime_five hZ).trans ?_
  have h1 : CFSG.Open.pRank 5 (⊤ : Subgroup S) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki hS Nat.prime_five (by norm_num)
  haveI hcyc : IsCyclic (Outer S) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 _ hS).1.1
  have h2 : CFSG.Open.pRank 5 (⊤ : Subgroup (Outer S)) ≤ 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_le_one_of_isCyclic Nat.prime_five inferInstance
  omega

theorem pRank_mulAut_le_two_of_small {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    {p : ℕ} (d : TauCeti.ValidLieTypeIndex) (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hexc : ExcIndex p d.1) (hd : d.1 = .tits ∨ d.1 = .suzuki 2 ∨ IsL2EightIndex d.1) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hs : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.exists_noncomm_quot hq
  rcases hd with hd | hd | hd
  · rw [hd] at hexc
    rcases eq_three_or_five_of_excIndex_tits hexc with rfl | rfl
    · exact (pRank_mulAut_le_quot Nat.prime_three hq.1).trans (pRank_three_mulAut_le_two_of_tits d hd e)
    · exact InputsSeitz3.pRank_five_mulAut_le_two_of_tits hq.1 d hd e
  · rw [hd] at hexc
    obtain rfl := eq_five_of_excIndex_suzuki hexc
    exact (pRank_mulAut_le_quot Nat.prime_five hq.1).trans
      (pRank_five_mulAut_le_two_of_suzuki hs hnab d hd e)
  · obtain ⟨q, hdq, hq3⟩ := hd.exists
    rw [hdq] at hexc
    obtain rfl := eq_three_of_excIndex_A hexc
    exact (pRank_mulAut_le_quot Nat.prime_three hq.1).trans
      (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_two_of_l28
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple hs hnab)
        ⟨q, hdq, hq3.1, hq3.2⟩ e)

theorem le_glbCore_of_index (h2 : KFactSeitzRankTwo) (h3 : Seitz2310CubeSimple)
    (hR : InputsSeitz3.SeitzQuasiHigh) (hRes : Input23_19ExcRes) {X : Type} [Group X] [Finite X]
    (hKX : CFSG.Open.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hrk : CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (haut : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)))
    (hsmall : p ^ (CFSG.Open.pRank p B - 2) * Nat.card (cen B K) < Nat.card (stab B K))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) : K ≤ GLBCore p 2 B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3le : p ^ 3 * Nat.card (cen B K) ≤ Nat.card (stab B K) :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))).trans
      (InputsSeitz3.pow_succ_mul_le hp hB hsmall)
  have hL34 : ¬ (p = 3 ∧ IsLThreeFour (↥K ⧸ Subgroup.center ↥K)) := by
    rintro ⟨rfl, h⟩
    have h1 := InputsSeitz3.pRank_mulAut_le_two_of_l34 hK.2.2.1 h
    omega
  by_cases hgood : ¬ ExcIndex p d.1
  · obtain ⟨E, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hB h3le
    have hEB : E ≤ B := hEN.trans inf_le_left
    have hENK : E ≤ Subgroup.normalizer (K : Set X) := hEN.trans inf_le_right
    have hEel : IsElemAbelian p E := elem_mono hB hEB
    have hgen := InputsSeitz3.seitzHyperGamma_eq_top_of_seitz h2 h3 hR hp hp2 hK.2.2 d ⟨e⟩ hpd hL34
      (InputsSeitz3.isElemAbelian_autIm hEel K)
      (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
      (Or.inl hgood)
    exact InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
      (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen)
  have hexc : ExcIndex p d.1 := not_not.1 hgood
  by_cases hsix : IsSixIndex d.1 ∧ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range
  · obtain ⟨E, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hB h3le
    have hEB : E ≤ B := hEN.trans inf_le_left
    have hENK : E ≤ Subgroup.normalizer (K : Set X) := hEN.trans inf_le_right
    have hEel : IsElemAbelian p E := elem_mono hB hEB
    have hgen := InputsSeitz3.seitzHyperGamma_eq_top_of_seitz h2 h3 hR hp hp2 hK.2.2 d ⟨e⟩ hpd hL34
      (InputsSeitz3.isElemAbelian_autIm hEel K)
      (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num))
      (Or.inr ⟨hsix.1, (autIm_mono hEB K).trans hsix.2⟩)
    exact InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
      (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen)
  by_cases hroute : Subgroup.center ↥K = ⊥ ∧ cen B K ≠ ⊥ ∧ ¬ IsD2SeitzException p d.1
  · obtain ⟨hZ, hC1, hnd⟩ := hroute
    obtain ⟨E₂, hE₂N, hE₂C, hE₂card⟩ := InputsSeitz3.exists_faithful hp hB (k := 2)
      ((Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by norm_num))).trans h3le)
    have hE₂B : E₂ ≤ B := hE₂N.trans inf_le_left
    have hE₂NK : E₂ ≤ Subgroup.normalizer (K : Set X) := hE₂N.trans inf_le_right
    have hE₂el : IsElemAbelian p E₂ := elem_mono hB hE₂B
    have hgen := InputsSeitz3.seitzHyperGamma_eq_top_of_plane h2 hp hp2 hZ d e hpd hnd
      (InputsSeitz3.isElemAbelian_autIm hE₂el K) (by rw [InputsSeitz3.card_autIm hE₂NK hE₂C, hE₂card])
    have hE₂cen : E₂ ⊓ cen B K = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ (inf_le_right : cen B K ≤ _)).trans hE₂C.le)
    exact InputsSeitz3.le_glbCore_of_centGenI_central hp hB hE₂B inf_le_left inf_le_right hE₂cen hC1
      hE₂card.ge (InputsSeitz3.le_centGenI_of_autIm hE₂NK hE₂C hgen)
  have hsm : ¬ (d.1 = .tits ∨ d.1 = .suzuki 2 ∨ IsL2EightIndex d.1) := fun h => by
    have h1 := pRank_mulAut_le_two_of_small hK.2.2 d e hexc h
    omega
  refine hRes X hKX p hp hp2 hcore B hB hB4 hrk K hK haut hsmall d ⟨e⟩ hexc
    (fun h => hsm (Or.inl h)) (fun h => hsm (Or.inr (Or.inl h))) (fun h => hsm (Or.inr (Or.inr h)))
    (fun h6 hin => hsix ⟨h6, hin⟩) ?_
  by_cases hZ : Subgroup.center ↥K = ⊥
  · by_cases hC1 : cen B K = ⊥
    · exact Or.inr (Or.inl hC1)
    · exact Or.inr (Or.inr (by by_contra hnd; exact hroute ⟨hZ, hC1, hnd⟩))
  · exact Or.inl hZ

theorem input23_19ChevCore_of_res (h2 : KFactSeitzRankTwo)
    (h3 : Seitz2310CubeSimple) (hR : InputsSeitz3.SeitzQuasiHigh) (hRes : Input23_19ExcRes) :
    InputsSeitz.Input23_19ChevCore := by
  intro X _ _ hKX p hp hp2 hcore B hB hB4 hrk K hK hch haut
  haveI : Fact p.Prime := ⟨hp⟩
  have hBcard : Nat.card B = p ^ CFSG.Open.pRank p B := GL83.PiGen.card_eq_pow_pRank hB
  by_cases hsmall : Nat.card (stab B K) ≤ p ^ (CFSG.Open.pRank p B - 2) * Nat.card (cen B K)
  · exact InputsSeitz.le_glbCore_of_card_stab_le hp hB hK 2 (CFSG.Open.pRank p B - 2) (by omega)
      (by rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega)) hsmall
  push Not at hsmall
  have hdisp : ∀ (d : TauCeti.ValidLieTypeIndex),
      (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) → p ≠ d.1.characteristic →
        K ≤ GLBCore p 2 B := fun d e hpd =>
    le_glbCore_of_index h2 h3 hR hRes hKX hp hp2 hcore hB hB4 hrk hK haut hsmall d e hpd
  obtain ⟨q, -, hqp, hc⟩ := hch
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  rcases hc with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact hi.elim
    · have hdq : d.1.characteristic = q := hi
      exact hdisp d e (fun h => hqp (hdq.symm.trans h.symm))
    · exact hi.elim
  · rcases i with ⟨r, hr⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact InputsSeitz.le_glbCore_of_alt hp hp2 hB hB4 hrk hK ⟨e⟩
    · by_cases hpd : p = d.1.characteristic
      swap
      · exact hdisp d e hpd
      exfalso
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k q' =>
        rcases k with _ | _ | k
        · simp [ambiguousChev] at hi
        · have hi' : (q'.card = 7 ∧ q = 2) ∨ (q'.card = 8 ∧ q = 3) := by
            simpa [ambiguousChev] using hi
          rcases hi' with ⟨h7, -⟩ | ⟨h8, -⟩
          ·
            have hq7 : q'.p = 7 :=
              Claims1116c.p_eq_of_card_eq (k := 1) (by norm_num) (by rw [h7]; norm_num)
            have hp7 : p = 7 := by rw [hpd]; simpa using hq7
            subst hp7
            have h1 := Claims1116c.pRank_aut_le_one hp hperf e
              (dvd_of_eq (Claims1116c.card_mulAut_L27 (q' := q') (hv := hv) h7 (MulEquiv.refl _)))
              (by norm_num)
            omega
          ·
            have hq2 : q'.p = 2 :=
              Claims1116c.p_eq_of_card_eq (k := 3) Nat.prime_two (by rw [h8]; norm_num)
            exact hp2 (by rw [hpd]; simpa using hq2)
        · simp [ambiguousChev] at hi
      | twistedA k q' =>
        rcases k with _ | _ | _ | _ | k
        · simp [ambiguousChev] at hi
        · simp [ambiguousChev] at hi
        ·
          have hi' : q'.card = 3 ∧ q = 2 := by simpa [ambiguousChev] using hi
          have hq3 : q'.p = 3 :=
            Claims1116c.p_eq_of_card_eq (k := 1) Nat.prime_three (by rw [hi'.1]; norm_num)
          have hp3 : p = 3 := by rw [hpd]; simpa using hq3
          subst hp3
          have hexp : q'.exponent = 1 := by
            have h1 : 3 ^ q'.exponent = 3 ^ 1 := by
              rw [← hq3, ← TauCeti.PrimePower.card_def, hi'.1, hq3, pow_one]
            exact Nat.pow_right_injective (by norm_num) h1
          have h1 := (pRank_mulAut_le_quot Nat.prime_three hperf).trans
            (CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_two_of_unitaryThree
              CFSG.AGLEmbedding.kFactUnitaryAutElemRank ⟨q', hq3, rfl⟩ (by simp [hexp]) e)
          omega
        ·
          have hi' : q'.card = 2 ∧ q = 3 := by simpa [ambiguousChev] using hi
          have hq2 : q'.p = 2 :=
            Claims1116c.p_eq_of_card_eq (k := 1) Nat.prime_two (by rw [hi'.1]; norm_num)
          exact hp2 (by rw [hpd]; simpa using hq2)
        · simp [ambiguousChev] at hi
      | _ => simp [ambiguousChev] at hi
    · exact hi.elim

theorem input23_19ChevExc_of_res (h2 : KFactSeitzRankTwo)
    (h3 : Seitz2310CubeSimple) (hR : InputsSeitz3.SeitzQuasiHigh) (hRes : Input23_19ExcRes) :
    InputsSeitz3.Input23_19ChevExc :=
  InputsSeitz3.input23_19ChevExc_of_core (input23_19ChevCore_of_res h2 h3 hR hRes)

end Dispatch

theorem input23_19ExcRes_of_chevExc (h : InputsSeitz3.Input23_19ChevExc) : Input23_19ExcRes := by
  intro X _ _ hKX p hp hp2 hcore B hB hB4 hrk K hK haut hsmall d hd hexc htits _ _ _ hrest
  have hd2 : d.1.characteristic = 2 := characteristic_eq_two_of_excIndex hexc
  obtain ⟨e⟩ := hd
  refine h X hKX p hp hp2 hcore B hB hB4 hrk K hK
    ⟨2, Nat.prime_two, Ne.symm hp2, Or.inl ⟨.lie d, hd2, ⟨e⟩⟩⟩ haut hsmall d ⟨e⟩
    (Or.inr ⟨hexc, fun h' => htits h'.2, hrest⟩)

theorem rank3CuResExcRes_of_exc (h : InputsSeitz3.Rank3CuResExc) : Rank3CuResExcRes := by
  intro G _ _ m p B M E A D T R L0 d hc h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  refine h hc h139b hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal ?_
  rcases htype with ⟨n, -, -, hA⟩ | ⟨i, hi, hi3, hexc, -, -, -, hrest⟩
  · exact Or.inl ⟨n, hA⟩
  · exact Or.inr ⟨i, hi, hi3, hexc, hrest⟩

section Rank3


theorem rank3CuResExc_of_res (h2 : KFactSeitzRankTwo) (h3 : Seitz2310CubeSimple)
    (hR : InputsSeitz3.SeitzQuasiHigh) (hX : Rank3CuResExcRes) : InputsSeitz3.Rank3CuResExc := by
  intro G _ _ m p B M E A D T R L0 d h h139b U hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal htype
  have h139b' := h139b
  obtain ⟨hp3, -⟩ := h139b
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hB4 : 4 ≤ CFSG.Open.pRank 3 B := Claims1310.pRank_B_eq h ▸ h.standing.four_le
  rcases htype with ⟨n, hA⟩ | ⟨i, ⟨e⟩, hi3, hexc, hrest⟩
  ·
    have hq := Lemma1313.isQuasisimple_barOf_of_pComp hKc
    have hn5 : 5 ≤ n := SchurFacts.five_le_of_isAltType hq hA
    have hPi : ¬ (n % 3 = 2 ∨ n = 7) := by
      intro hn
      apply hpi
      obtain ⟨eA⟩ := hA
      refine ⟨hq, glaPPrimeCore_quotient_eq_bot hp, ?_⟩
      rcases hn with hn | rfl
      · obtain ⟨k, rfl⟩ : ∃ k, n = k * 3 + 2 := ⟨n / 3, by omega⟩
        exact Or.inl ⟨k, ⟨eA⟩⟩
      · exact Or.inr (Or.inr ⟨rfl, ⟨eA⟩⟩)
    have hn6 : n ≠ 6 := by
      rintro rfl
      obtain ⟨eA⟩ := hA
      have h1 := InputsSeitz.pRank_aut_le_two_of_alt6 hp (by norm_num) hq.1 eA
      omega
    exact hX h h139b' hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      (Or.inl ⟨n, by omega, fun h => hPi (Or.inl h), hA⟩)
  have hsm : ¬ (i.1 = .tits ∨ i.1 = .suzuki 2 ∨ IsL2EightIndex i.1) := fun hs => by
    have h1 := pRank_mulAut_le_two_of_small (Lemma1313.isQuasisimple_barOf_of_pComp hKc) i e hexc hs
    omega
  by_cases hsix : IsSixIndex i.1 ∧ InputsSeitz3.autIm (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) ≤
      (MulAut.conj : ↥(barX 3 (Cg u) Kc) →* MulAut ↥(barX 3 (Cg u) Kc)).range
  swap
  · exact hX h h139b' hU u hu hu1 hlt Kc hKc hgood hN haut hcen hpi hbal
      (Or.inr ⟨i, ⟨e⟩, hi3, hexc, fun h' => hsm (Or.inl h'), fun h' => hsm (Or.inr (Or.inr h')),
        fun h6 hin => hsix ⟨h6, hin⟩, hrest⟩)
  have hBel : IsElemAbelian 3 B := h.bOne.1.1
  have huB : u ∈ B := hU.1.1 hu
  have hBC : B ≤ Cg u := Prop1310a5b.le_cg_of_mem hBel huB
  have hnorm : ∀ E' : Subgroup G, E' ≤ B → 2 ≤ CFSG.Open.pRank 3 E' →
      Subgroup.normalizer (E' : Set G) ≤ M :=
    fun E' hE' hr => (normalizer_le_glbCore hE' hr).trans h.uniq.clause_d
  have hcore : GLAPPrimeCoreOf 3 (Cg u) ≤ M := le_sup_left.trans (h.uniq.clause_a u huB hu1)
  have hpi3 : 3 ≠ i.1.characteristic := fun h => hi3 h.symm
  have eK : barOf 3 Kc ≃* ↥(barX 3 (Cg u) Kc) := quotEquivBarX hp hKc.1 hKc.2.1
  have hqK : CFSG.Open.IsQuasisimple ↥(barX 3 (Cg u) Kc) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv eK.symm (Lemma1313.isQuasisimple_barOf_of_pComp hKc)
  have eZ : ↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc) ≃*
      (TauCeti.CFSGIndex.lie i).Group :=
    (Lemma1315b.centerQuotEquiv eK.symm).trans e
  have hBtel : IsElemAbelian 3 (barX 3 (Cg u) B) := isElemAbelian_barX hBel
  have hBtrk : CFSG.Open.pRank 3 (barX 3 (Cg u) B) = CFSG.Open.pRank 3 B :=
    rank_barX_of_isPGroup hp (CFSG.Open.IsElemAbelian.isPGroup hBel) hBC
  have hBtN : barX 3 (Cg u) B ≤
      Subgroup.normalizer ((barX 3 (Cg u) Kc : Subgroup (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :
        Set (↥(Cg u) ⧸ GLAPPrimeCore 3 ↥(Cg u))) :=
    barX_le_normalizer hN
  have hstab : stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc) = barX 3 (Cg u) B := inf_eq_left.2 hBtN
  have hcen3 : Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 := by
    obtain ⟨c, hc⟩ : ∃ c, Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) = 3 ^ c :=
      GL83.CompFam.exists_card_eq_pow (elem_mono hBtel inf_le_left)
    have hcr : c ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl (elem_mono hBtel inf_le_left) hc).trans hcen
    rw [hc]
    calc 3 ^ c ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcr
      _ = 3 := by norm_num
  have h3le : 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤
      Nat.card (stab (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) := by
    rw [hstab, GL83.PiGen.card_eq_pow_pRank hBtel, hBtrk]
    calc 3 ^ 3 * Nat.card (cen (barX 3 (Cg u) B) (barX 3 (Cg u) Kc)) ≤ 3 ^ 3 * 3 :=
          Nat.mul_le_mul_left _ hcen3
      _ = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 B := Nat.pow_le_pow_right (by norm_num) hB4
  have hL34b : ¬ IsLThreeFour (barOf 3 Kc ⧸ Subgroup.center (barOf 3 Kc)) := fun h => by
    have h1 := InputsSeitz3.pRank_mulAut_le_two_of_l34 (Lemma1313.isQuasisimple_barOf_of_pComp hKc).1 h
    omega
  have hL34 : ¬ (3 = 3 ∧
      IsLThreeFour (↥(barX 3 (Cg u) Kc) ⧸ Subgroup.center ↥(barX 3 (Cg u) Kc))) :=
    fun h => hL34b (InputsSeitz3.isLThreeFour_congr (Lemma1315b.centerQuotEquiv eK) h.2)
  obtain ⟨Ee, hEN, hEC, hEcard⟩ := InputsSeitz3.exists_faithful hp hBtel h3le
  have hEB : Ee ≤ barX 3 (Cg u) B := hEN.trans inf_le_left
  have hENK := hEN.trans inf_le_right
  have hEel : IsElemAbelian 3 Ee := elem_mono hBtel hEB
  have hgen := InputsSeitz3.seitzHyperGamma_eq_top_of_seitz h2 h3 hR hp (by norm_num) hqK i ⟨eZ⟩ hpi3 hL34
    (InputsSeitz3.isElemAbelian_autIm hEel _)
    (by rw [InputsSeitz3.card_autIm hENK hEC, hEcard]; norm_num)
    (Or.inr ⟨hsix.1, (autIm_mono hEB _).trans hsix.2⟩)
  exact Prop1310a5b.comp_le_M_of_gamma hBel huB hnorm hcore hKc
    (InputsSeitz3.le_glbCore_of_centGenI hp hEB hEel hEcard.ge
      (InputsSeitz3.le_centGenI_of_autIm hENK hEC hgen))

end Rank3

section Holds


theorem input23_19ChevCore_of_res_cube (h3 : Seitz2310CubeSimple)
    (hR : InputsSeitz3.SeitzQuasiHigh) (hRes : Input23_19ExcRes) : InputsSeitz.Input23_19ChevCore :=
  input23_19ChevCore_of_res CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds h3 hR hRes

theorem input23_19ChevExc_of_res_cube (h3 : Seitz2310CubeSimple)
    (hR : InputsSeitz3.SeitzQuasiHigh) (hRes : Input23_19ExcRes) : InputsSeitz3.Input23_19ChevExc :=
  input23_19ChevExc_of_res CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds h3 hR hRes

theorem rank3CuRes_of_res_cube (h3 : Seitz2310CubeSimple) (hR : InputsSeitz3.SeitzQuasiHigh)
    (hX : Rank3CuResExcRes) : Claims1310.Rank3CuRes :=
  InputsSeitz3.rank3CuRes_of_seitz CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds h3 hR
    (rank3CuResExc_of_res CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds h3 hR hX)

end Holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz5

end
