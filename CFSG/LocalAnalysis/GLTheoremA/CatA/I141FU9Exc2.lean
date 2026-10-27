module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9LemRed
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoE
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoRat
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem excU9_le_mul_sub_one {Q a k : ℕ} (hQ : 2 ≤ Q) (hk : 1 ≤ k) : a ≤ a * (Q ^ k - 1) := by
  have h1 : 2 ≤ Q ^ k := le_trans hQ (Nat.le_self_pow (by omega) Q)
  exact Nat.le_mul_of_pos_right a (by omega)

private theorem excU9_two_le_card (q : TauCeti.PrimePower) : 2 ≤ q.card := by
  rw [TauCeti.PrimePower.card_def]
  exact le_trans q.prime_p.two_le (Nat.le_self_pow (by have := q.exponent_pos; omega) q.p)

theorem excU9_order_cases {d : TauCeti.ValidLieTypeIndex} (hd : I141F.u9FamExc (.lie d)) :
    17971200 < lieOrderFormula d.1 ∨ lieOrderFormula d.1 = 4245696 := by
  obtain ⟨e, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases e with
  | E7 q =>
    left
    have hQ := excU9_two_le_card q
    set Q := q.card
    show 17971200 < CFSG.Open.orderE7 Q
    unfold CFSG.Open.orderE7
    have hN : Q ^ 63 ≤ Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) *
        (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      exact excU9_le_mul_sub_one hQ (by norm_num)
    have h63 : 2 ^ 63 ≤ Q ^ 63 := Nat.pow_le_pow_left hQ 63
    have hg : Nat.gcd 2 (Q - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hg0 : 0 < Nat.gcd 2 (Q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hdiv : (Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) *
        (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)) / 2 ≤
        (Q ^ 63 * (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 10 - 1) *
        (Q ^ 8 - 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1)) / Nat.gcd 2 (Q - 1) :=
      Nat.div_le_div_left hg hg0
    refine lt_of_lt_of_le ?_ hdiv
    rw [Nat.lt_div_iff_mul_lt (by norm_num)]
    have : (17971200 : ℕ) * 2 < 2 ^ 63 := by norm_num
    omega
  | E8 q =>
    left
    have hQ := excU9_two_le_card q
    set Q := q.card
    show 17971200 < CFSG.Open.orderE8 Q
    unfold CFSG.Open.orderE8
    have hN : Q ^ 120 ≤ Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) * (Q ^ 18 - 1) *
        (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1) := by
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      exact excU9_le_mul_sub_one hQ (by norm_num)
    have h120 : 2 ^ 120 ≤ Q ^ 120 := Nat.pow_le_pow_left hQ 120
    have : (17971200 : ℕ) < 2 ^ 120 := by norm_num
    omega
  | F4 q =>
    left
    have hQ := excU9_two_le_card q
    set Q := q.card
    show 17971200 < CFSG.Open.orderF4 Q
    unfold CFSG.Open.orderF4
    have hN : Q ^ 24 * (Q ^ 12 - 1) ≤ Q ^ 24 * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 6 - 1) *
        (Q ^ 2 - 1) := by
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      refine le_trans ?_ (excU9_le_mul_sub_one hQ (by norm_num))
      exact excU9_le_mul_sub_one hQ (by norm_num)
    have h24 : 2 ^ 24 ≤ Q ^ 24 := Nat.pow_le_pow_left hQ 24
    have h12 : 2 ^ 12 - 1 ≤ Q ^ 12 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hQ 12) 1
    have hm : 2 ^ 24 * (2 ^ 12 - 1) ≤ Q ^ 24 * (Q ^ 12 - 1) := Nat.mul_le_mul h24 h12
    have : (17971200 : ℕ) < 2 ^ 24 * (2 ^ 12 - 1) := by norm_num
    omega
  | G2 q =>
    have hQ3 : 3 ≤ q.card := hr
    set Q := q.card
    show 17971200 < CFSG.Open.orderG2 Q ∨ CFSG.Open.orderG2 Q = 4245696
    by_cases h3 : Q = 3
    · right
      rw [h3]
      decide
    · left
      have hQ : 4 ≤ Q := by omega
      unfold CFSG.Open.orderG2
      have h6 : 4 ^ 6 ≤ Q ^ 6 := Nat.pow_le_pow_left hQ 6
      have h6' : 4 ^ 6 - 1 ≤ Q ^ 6 - 1 := Nat.sub_le_sub_right h6 1
      have h2 : 4 ^ 2 - 1 ≤ Q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hQ 2) 1
      have hm : 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1) ≤ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h6 h6') h2
      have : (17971200 : ℕ) < 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1) := by norm_num
      omega
  | trialityD4 q =>
    left
    have hQ := excU9_two_le_card q
    set Q := q.card
    show 17971200 < CFSG.Open.orderTrialityD4 Q
    unfold CFSG.Open.orderTrialityD4
    have h12 : 2 ^ 12 ≤ Q ^ 12 := Nat.pow_le_pow_left hQ 12
    have h8 : 2 ^ 8 + 2 ^ 4 + 1 ≤ Q ^ 8 + Q ^ 4 + 1 :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.pow_le_pow_left hQ 8) (Nat.pow_le_pow_left hQ 4)) 1
    have h6 : 2 ^ 6 - 1 ≤ Q ^ 6 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hQ 6) 1
    have h2 : 2 ^ 2 - 1 ≤ Q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hQ 2) 1
    have hm : 2 ^ 12 * (2 ^ 8 + 2 ^ 4 + 1) * (2 ^ 6 - 1) * (2 ^ 2 - 1) ≤
        Q ^ 12 * (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h12 h8) h6) h2
    have : (17971200 : ℕ) < 2 ^ 12 * (2 ^ 8 + 2 ^ 4 + 1) * (2 ^ 6 - 1) * (2 ^ 2 - 1) := by norm_num
    omega
  | _ => simp [I141F.u9FamExc, onLie] at hd

theorem excU9_order_ne {d : TauCeti.ValidLieTypeIndex} (hd : I141F.u9FamExc (.lie d)) :
    lieOrderFormula d.1 ≠ 5515776 := by
  rcases excU9_order_cases hd with h | h <;> omega

section U38Model


theorem excU9_u38_model {Y : Type} [Group Y] (hU : catalogIs Y S9.isU3eight) :
    CFSG.Blueprint.LieModel Y .PSU 3 2 3 ∧ Nat.card Y = 5515776 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hU
  cases i with
  | lie d =>
    obtain ⟨idx, hv⟩ := d
    cases idx with
    | twistedA r q =>
      by_cases hr : r = 2
      · subst hr
        simp only [S9.isU3eight, onLie] at hi
        obtain ⟨hp2, hexp⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 3)
          Nat.prime_two (by norm_num) (by simpa using hi)
        have hM := CFSG.Models.lieModel_twistedA 2 q hv e
        have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = 2 :=
          (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hp2
        have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 3 :=
          (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hexp
        rw [hc, hf] at hM
        have hB : CFSG.Blueprint.LieModel Y .PSU 3 2 3 :=
          CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by simp [CFSG.Blueprint.classicalTags]) hM
        obtain ⟨hfin, -, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput Y _ _ _ _
          (CFSG.Blueprint.LieModel.admissible hB) hB
        haveI := hfin
        have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
          ⟨.twistedA 2 q, hv⟩ Y ⟨e⟩
        refine ⟨hB, ?_⟩
        rw [hcard]
        show CFSG.Open.orderTwistedA 2 q.card = 5515776
        rw [hi]
        decide
      · exact absurd hi (by simp [S9.isU3eight, onLie, hr])
    | _ => exact absurd hi (by simp [S9.isU3eight, onLie])
  | _ => exact absurd hi (by simp [S9.isU3eight, onLie])

end U38Model

end CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex

namespace CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section RatE78


theorem excU9_orbit_one {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  refine componentOrbitLength_eq_one ?_ fun γ hγ => ?_
  · exact (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  · rw [hρ γ (hΨ.isRoot γ hγ)]
    exact hΨ.neg_mem γ hγ

theorem excU9_inner_big_dvd {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard) :
    2 ^ 13 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  haveI : CharP L 2 := CFSG.StandardType.ExcThreeAtTwo.charP_two_of_langSetup_q_eq_two S hq2
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  obtain ⟨D⟩ := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.nonempty_innerData S hT i hk
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isPerfect_componentRootSpan_of_big hτ D
    (by omega)
  obtain ⟨g, hg, hgk⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.exists_surjective_central_of_perfect D hperf
  have hdvd := CFSG.StandardType.ExcThreeAtTwo.pow_card_dvd_centerQuotient_of_uniEmbed
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.uniEmbed_holds (rootCharHom a) i (fixSubfield D.σ) g
    hg hgk hperf
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN : 13 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := by omega
  obtain ⟨k, hk1, hkc⟩ := CFSG.StandardType.LayerExcThree.exists_card_eq_two_pow (fixSubfield D.σ)
  rw [hkc, ← pow_mul] at hdvd
  refine dvd_trans (Nat.pow_dvd_pow 2 ?_) hdvd
  calc 13 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := hN
    _ ≤ k * (posRoots (componentRoots (rootCharHom a) i)).ncard := Nat.le_mul_of_pos_left _ hk1

theorem excU9_rat_notU38 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) (hq2 : S.D.q = 2) (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hU : catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) S9.isU3eight) : False := by
  classical
  haveI : CharP L 2 := CFSG.StandardType.ExcThreeAtTwo.charP_two_of_langSetup_q_eq_two S hq2
  obtain ⟨hX3, hXcard⟩ := excU9_u38_model hU
  have htd : ∀ (t : StatedLieTag) (n f : ℕ),
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) t n 2 f →
        t = .PSU ∧ n = 3 ∧ f = 3 := fun t n f h =>
    CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet _ 3 t n f hX3 h.admissible h
  have h13 : ¬ 2 ^ 13 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
    rw [hXcard]
    decide
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit τ a ^ 3 = 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  have horb := excU9_orbit_one S hρ i
  have hτ4 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h <;> simp [h]
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · obtain ⟨ν, f, -, -, hfeq, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model S Nat.prime_three
        hT hap h1 i hA hqs
    rw [horb, pow_one, hq2, ringChar.eq L 2] at hfeq
    have hf : f = 1 := by
      have h2 : (2 : ℕ) ^ f = 2 ^ 1 := by rw [hfeq, pow_one]
      exact Nat.pow_right_injective le_rfl h2
    rw [ringChar.eq L 2] at hmodel
    rcases hmodel with hPSL | hPSU
    · obtain ⟨h, -, -⟩ := htd .PSL ν f (.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSL⟩)
      exact absurd h (by decide)
    · obtain ⟨-, -, h⟩ := htd .PSU ν f (.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩)
      omega
  · rcases hτ with rfl | rfl
    · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
        exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S
          Nat.prime_three h3L hTp i
      have hshape := e7_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD | hE
      · exact hA hA'
      · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
          by_contra hlt
          have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
          exact CFSG.StandardType.ExcThreeAtTwo.not_d4Shape_of_three_E7 S h3L hTp i
            ⟨hr4, by rw [hD.2, hr4]⟩
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact h13 (excU9_inner_big_dvd S hq2 hT i hτ4 hinner h26)
        · obtain ⟨m, e, -, hlie⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_twoD_highG
              Nat.prime_three S hT hap h1 i hr5 hD.2 hinner (fun _ _ => True)
              (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
          rw [ringChar.eq L 2] at hlie
          obtain ⟨h, -, -⟩ := htd _ _ _ hlie
          exact absurd h (by decide)
      · have hr7 : compRank (componentRoots (rootCharHom a) i) ≤ 7 := by
          have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
          rwa [show Tag.E7.rank = 7 from rfl] at hle
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hE.2]
          have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
              compRank (componentRoots (rootCharHom a) i) = 7 := by omega
          rcases hc with h6 | h7
          · rw [h6]
            norm_num [eRootCount]
          · rw [h7]
            norm_num [eRootCount]
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact h13 (excU9_inner_big_dvd S hq2 hT i hτ4 hinner h26)
        · obtain ⟨f, -, -, hlie⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_outer_E7 S
              Nat.prime_three h3L hT hTp i hE.1 hE.2 hinner
          rw [ringChar.eq L 2] at hlie
          obtain ⟨h, -, -⟩ := htd _ _ _ hlie
          exact absurd h (by decide)
    · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
        exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S
          Nat.prime_three h3L hTp i
      have hshape := e8_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD | hE
      · exact hA hA'
      · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
          by_contra hlt
          have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
          exact CFSG.StandardType.ExcThreeAtTwo.not_d4Shape_of_three_E8 S h3L hTp i
            ⟨hr4, by rw [hD.2, hr4]⟩
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact h13 (excU9_inner_big_dvd S hq2 hT i hτ4 hinner h26)
        · obtain ⟨m, e, -, hlie⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_twoD_highG
              Nat.prime_three S hT hap h1 i hr5 hD.2 hinner (fun _ _ => True)
              (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
          rw [ringChar.eq L 2] at hlie
          obtain ⟨h, -, -⟩ := htd _ _ _ hlie
          exact absurd h (by decide)
      · have hr8 : compRank (componentRoots (rootCharHom a) i) ≤ 8 := by
          have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
          rwa [show Tag.E8.rank = 8 from rfl] at hle
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hE.2]
          have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
              compRank (componentRoots (rootCharHom a) i) = 7 ∨
              compRank (componentRoots (rootCharHom a) i) = 8 := by omega
          rcases hc with h6 | h7 | h8
          · rw [h6]
            norm_num [eRootCount]
          · rw [h7]
            norm_num [eRootCount]
          · rw [h8]
            norm_num [eRootCount]
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact h13 (excU9_inner_big_dvd S hq2 hT i hτ4 hinner h26)
        · obtain ⟨f, -, -, hlie⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.lieModel_rationalComponent_of_outer_E8 S
              Nat.prime_three h3L hT hTp i hE.1 hE.2 hinner
          rw [ringChar.eq L 2] at hlie
          obtain ⟨h, -, -⟩ := htd _ _ _ hlie
          exact absurd h (by decide)

end RatE78

section AdjE78


open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

private theorem excU9_commutator_eq_self {X G : Type*} [Group X] [Group G] {M : Subgroup G}
    (e : X ≃* ↥M) (hX : commutator X = ⊤) : ⁅M, M⁆ = M := by
  have hM : commutator ↥M = ⊤ := by
    rw [_root_.commutator_def] at hX ⊢
    rw [← Subgroup.map_top_of_surjective (e : X →* ↥M) e.surjective, ← Subgroup.map_commutator, hX]
  have htop : (⊤ : Subgroup ↥M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc ⁅M, M⁆ = ⁅(⊤ : Subgroup ↥M).map M.subtype, (⊤ : Subgroup ↥M).map M.subtype⁆ := by
        rw [htop]
    _ = (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ : Subgroup ↥M).map M.subtype :=
        (Subgroup.map_commutator _ _ _).symm
    _ = M := by
        rw [← _root_.commutator_def, hM, htop]

private theorem excU9_map_conj_eq {G : Type*} [Group G] {M : Subgroup G} {v : G}
    (hv : ∀ m ∈ M, v * m * v⁻¹ ∈ M) (hv' : ∀ m ∈ M, v⁻¹ * m * v⁻¹⁻¹ ∈ M) :
    M.map (MulAut.conj v).toMonoidHom = M := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hv m hm
  · intro hy
    refine ⟨v⁻¹ * y * v⁻¹⁻¹, hv' y hy, ?_⟩
    show v * (v⁻¹ * y * v⁻¹⁻¹) * v⁻¹ = y
    group

theorem excU9_adjoint_notU38_of_model {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) [CharP (AlgebraicClosure K) 2] {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (htorL : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit τ a ∈ torusGroup τ (AlgebraicClosure K))
    (hmon : MonomialToralAt τ 3)
    (hLang : ∀ a : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer τ (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer τ (AlgebraicClosure K) a, z⁻¹ * frobTwistGL τ
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀) z = c)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 1)) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)
    {M : Subgroup (ModGL τ (AlgebraicClosure K))} (e : ↥(adjointGroup τ K) ≃* ↥M)
    (hMW : M ≤ twModel (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)
      (iterateFrobenius (AlgebraicClosure K) 2 1))
    (hnorm : ∀ u ∈ twModel (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)
      (iterateFrobenius (AlgebraicClosure K) 2 1), ∀ m ∈ M, u * m * u⁻¹ ∈ M)
    (hΓM : ⁅twModel (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)
        (iterateFrobenius (AlgebraicClosure K) 2 1),
      twModel (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)
        (iterateFrobenius (AlgebraicClosure K) 2 1)⁆ = M)
    {s : ↥(adjointGroup τ K)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {J : Subgroup ↥(adjointGroup τ K)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K))))
    (hU : catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isU3eight) : False := by
  classical
  set L := AlgebraicClosure K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  set n := canonicalRep (coxeterSystem τ) L w₀ with hn
  set W := twModel n (iterateFrobenius L 2 1) with hW
  haveI hWfin : Finite W := finite_twModel hg0C hg0
  have hFr2 : ∀ c : L, iterateFrobenius L 2 1 c = c ^ 2 := iterateFrobenius_two_one
  set s' : ModGL τ L := (e s : ModGL τ L) with hs'
  have hs'W : s' ∈ W := hMW (e s).2
  have hs'3 : s' ^ 3 = 1 := by
    rw [hs', ← Subgroup.coe_pow, ← map_pow, hs3, map_one, Subgroup.coe_one]
  obtain ⟨ω, hω, -⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_orderOf_eq_of_dvd_add_one K
    (L := L) (N := 3) (by rw [hK])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨v, hvW, x, hvx⟩ := exists_conj_dV_twModel
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K 2)
    hmon hw₀ hLang hω hs'W hs'3
  set D : LangDatum τ L := LangDatum.ofFrobenius (iterateFrobenius L 2 1) 2 hFr2 w₀ hg0C hg0 with hD
  have hDmodel : D.model = W := rfl
  set ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (MulAut.conj (g0 * v)).toMonoidHom.comp (M.subtype.comp e.toMonoidHom) with hι₀def
  have hι₀ : Function.Injective ι₀ :=
    (MulAut.conj (g0 * v)).injective.comp (M.subtype_injective.comp e.injective)
  have hrange₀ : (M.subtype.comp e.toMonoidHom).range = M := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    have h1 : ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom = M.map (MulAut.conj v).toMonoidHom := by
      rw [hι₀def, MonoidHom.range_comp, hrange₀, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun y => ?_
      show g0⁻¹ * ((g0 * v) * y * (g0 * v)⁻¹) * g0⁻¹⁻¹ = v * y * v⁻¹
      group
    rw [h1, excU9_map_conj_eq (fun m hm => hnorm v hvW m hm)
      (fun m hm => hnorm v⁻¹ (inv_mem hvW) m hm)]
    exact hΓM
  set u : ModGL τ L := g0 * dV ω x * g0⁻¹ with hu
  have hβ : ∀ c, ι₀ (MulAut.conj s c) = u * ι₀ c * u⁻¹ := by
    intro c
    have hc : (e (MulAut.conj s c) : ModGL τ L) = s' * (e c : ModGL τ L) * s'⁻¹ := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
    show (g0 * v) * (e (MulAut.conj s c) : ModGL τ L) * (g0 * v)⁻¹ =
      u * ((g0 * v) * (e c : ModGL τ L) * (g0 * v)⁻¹) * u⁻¹
    rw [hc, hu, ← hvx]
    group
  have hdT : dV ω x ∈ D.torus := by
    refine (mem_twistedTorus_of_neg htorL hw₀ hFr2).2 ⟨torV ω x, rfl, fun i => ?_⟩
    show (ω ^ (x i).val) ^ (2 + 1) = 1
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have hmem : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := ⟨dV ω x, hdT, rfl⟩
  have hup : u ^ 3 = 1 := by
    rw [hu, conj_pow, dV_pow_three hω3 x, mul_one, mul_inv_cancel]
  have hu1 : u ≠ 1 := by
    intro h
    apply hs1
    have hd1 : dV ω x = 1 := by
      have : dV ω x = g0⁻¹ * u * g0 := by rw [hu]; group
      rw [this, h]
      group
    have h's : s' = 1 := by
      have : s' = v⁻¹ * (v * s' * v⁻¹) * v := by group
      rw [this, hvx, hd1]
      group
    apply e.injective
    rw [map_one]
    exact Subtype.ext h's
  have hDq : D.q = 2 ^ 1 := rfl
  obtain ⟨S, a, ι, hSD, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_toral_datum_of_prime
      (ℓ := 2) (f := 1) Nat.prime_two le_rfl D hDq (p₀ := 5) Nat.prime_five (by norm_num)
      (Or.inl le_rfl) (p := 3) (hDmodel ▸ hWfin) ι₀ hι₀ hΓ (MulAut.conj s) hβ hmem hup hu1
  have hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ := by
    intro γ hγ
    have hFD : FrobRootMap D S.ρ := hSD ▸ S.frob
    rw [frobRootMap_ofFrobenius_apply (by norm_num) hFr2 hg0C hg0 hFD hγ, hw₀]
  have hq2 : S.D.q = 2 := by rw [hSD]; rfl
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three (by rw [ringChar.eq L 2]; norm_num)
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S
    Nat.prime_three h3L (fun h' => absurd h' (by rcases hτ with h | h <;> simp [h])) hT hap h1
  have hfix : fixSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K)) := by
    ext y
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, eq_comm]
  rw [← hfix] at hJ
  obtain ⟨i, hq, hJR⟩ := components_of_langSetup S Nat.prime_three ι hinj hrange (MulAut.conj s)
    hconj hT hap h1 hTame hJ
  have hU' : catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) S9.isU3eight := by
    obtain ⟨idx, hidx, ⟨f⟩⟩ := hU
    let εJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
    exact ⟨idx, hidx, ⟨(QuotientGroup.congr _ _ εJ (Subgroup.map_center_eq εJ)).symm.trans f⟩⟩
  exact excU9_rat_notU38 hτ S hq2 hρ hT hap h1 i hq hU'

private theorem excU9_conj_sq {τ : Tag} {L : Type} [Field L] {w₀ : WeylGroup τ}
    (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) {a : Fin τ.rank → Lˣ} (ha3 : ∀ i, a i ^ 3 = 1) :
    canonicalRep (coxeterSystem τ) L w₀ * rootDiagUnit τ a *
      (canonicalRep (coxeterSystem τ) L w₀)⁻¹ = rootDiagUnit τ a ^ 2 := by
  rw [canonicalRep_conj_rootDiagUnit_of_neg hw₀]
  have hd3 : rootDiagUnit τ a ^ 3 = 1 := by
    have h1 : rootDiagUnit τ (a ^ 3) = rootDiagUnit τ a ^ 3 := map_pow (rootDiagUnitHom τ L) a 3
    rw [← h1, show a ^ 3 = 1 from funext ha3, rootDiagUnit_one]
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hd3])

theorem excU9_adjoint_E8_notU38 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {s : ↥(adjointGroup Tag.E8 K)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {J : Subgroup ↥(adjointGroup Tag.E8 K)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set ↥(adjointGroup Tag.E8 K))))
    (hU : catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isU3eight) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E8 K e8Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  have hMW := langModel_le_twModel Tag.E8 K (AlgebraicClosure K) hFr hg0C hg0
  haveI : Finite (twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) := finite_twModel hg0C hg0
  have hWM := le_langModel_E8_of_le_twModel K (AlgebraicClosure K) hFr hg0C hg0 (P :=
    twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) le_rfl
  have hEq := le_antisymm hMW hWM
  have hcomm := excU9_commutator_eq_self (langModelEquiv Tag.E8 K (AlgebraicClosure K) g0)
    (CFSG.LieType.Chevalley.single_edge_perfect Tag.E8 K (by simp))
  have hLang : ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E8
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
            e8Neg) z = c := fun a ha3 c hc =>
    CFSG.HardMathSupport.Timmesfeld.Steinberg.toral_centralizer_Lang_E8_three 2 (AlgebraicClosure K)
      (by norm_num) a ha3 1 le_rfl (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (excU9_conj_sq e8Neg_smul ha3) c hc
  exact excU9_adjoint_notU38_of_model (Or.inr rfl) hK e8Neg_smul rootDiagUnit_mem_torusGroup_E8
    (monomialToralAt_three_of_block a2BlockToral_E8) hLang hg0C hg0
    (langModelEquiv Tag.E8 K (AlgebraicClosure K) g0) hMW
    (fun u hu m hm => hWM (mul_mem (mul_mem hu (hMW hm)) (inv_mem hu)))
    (by rw [← hEq]; exact hcomm) hs3 hs1 hJ hU

theorem excU9_adjoint_E7_notU38 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {s : ↥(adjointGroup Tag.E7 K)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {J : Subgroup ↥(adjointGroup Tag.E7 K)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set ↥(adjointGroup Tag.E7 K))))
    (hU : catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isU3eight) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E7 K e7Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  set W := twModel (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) e7Neg)
    (iterateFrobenius (AlgebraicClosure K) 2 1) with hW
  set M := e7Model K (AlgebraicClosure K) g0 with hM
  have hMW : M ≤ W := e7Model_le_twModel K (AlgebraicClosure K) hFr hg0C hg0
  have : Finite W := finite_twModel hg0C hg0
  have hd : M.relIndex W ∣ 2 := by
    set X := W.map (MulAut.conj g0).toMonoidHom with hX
    have : Finite X := Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap W)
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective W)
    have hXF := map_conj_twModel hg0C hg0
    have hdesc := (finite_fixed_subgroup_rational_perfect 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (iterateFrobenius (AlgebraicClosure K) 2 1) hFr X (fun x hx => by
        rw [hX, hXF] at hx
        exact hx.1) (fun x hx => by
        rw [hX, hXF] at hx
        exact hx.2)).1
    have hcomp : (MulAut.conj g0).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have hMX : M.map (MulAut.conj g0).toMonoidHom =
        (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
      rw [hM, e7Model, Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g0).toMonoidHom) _ _
      (MulAut.conj g0).injective, hMX]
    exact hdesc
  obtain ⟨hnorm, -⟩ := normal_of_relIndex_dvd_two hMW hd
  have hsq : ∀ g ∈ W, g * g ∈ M := by
    intro g hg
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · have htop := Subgroup.index_eq_one.1 h1
      have : (⟨g * g, mul_mem hg hg⟩ : W) ∈ M.subgroupOf W := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    · exact Subgroup.mem_subgroupOf.1 (Subgroup.mul_self_mem_of_index_two h2 ⟨g, hg⟩)
  have hcomm := excU9_commutator_eq_self (e7ModelEquiv K (AlgebraicClosure K) g0)
    (CFSG.LieType.Chevalley.single_edge_perfect Tag.E7 K (by simp))
  have hΓM : ⁅W, W⁆ = M := by
    refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => ?_) ?_
    · have e : ⁅x, y⁆ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem (mul_mem (hsq x hx) (hsq _ (mul_mem (inv_mem hx) hy))) (hsq _ (inv_mem hy))
    · calc M = ⁅M, M⁆ := hcomm.symm
        _ ≤ ⁅W, W⁆ := Subgroup.commutator_mono hMW hMW
  have hLang : ∀ a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E7
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K)
            e7Neg) z = c := fun a ha3 c hc =>
    CFSG.HardMathSupport.Timmesfeld.Steinberg.toral_centralizer_Lang_E7_three 2 (AlgebraicClosure K)
      (by norm_num) a ha3 1 le_rfl (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (excU9_conj_sq e7Neg_smul ha3) c hc
  exact excU9_adjoint_notU38_of_model (Or.inl rfl) hK e7Neg_smul rootDiagUnit_mem_torusGroup_E7
    (monomialToralAt_three_of_block a2BlockToral_E7) hLang hg0C hg0
    (e7ModelEquiv K (AlgebraicClosure K) g0) hMW hnorm hΓM hs3 hs1 hJ hU

end AdjE78

section Catalogue


open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem excU9_noU38_of_adjoint {S C : Type} [Group S] [Group C] (φ : S ≃* C)
    (hinner : ∀ α : MulAut C, α ∈ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut C)
    (hZ : Subgroup.center C = ⊥)
    (hadj : ∀ s : C, s ^ 3 = 1 → s ≠ 1 → ∀ J : Subgroup C,
      CFSG.Open.IsComponentOf J (Subgroup.centralizer ({s} : Set C)) →
        ¬ catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isU3eight)
    {β : MulAut S} (hβ3 : β ^ 3 = 1) (hβ1 : β ≠ 1) {L : Subgroup S}
    (hL : CFSG.Open.IsComponentOf L (fixSubgroup β)) :
    ¬ catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU3eight := by
  intro hU
  obtain ⟨s, hs⟩ := hinner (MulAut.congr φ β)
  have hconjinj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut C => φ g) (MonoidHom.mem_ker.1 hc)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * c = c * g * c⁻¹ * c := by rw [h]
      _ = c * g := by group
  have hs3 : s ^ 3 = 1 := by
    apply hconjinj
    rw [map_pow, hs, ← map_pow, hβ3, map_one, map_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hβ1
    apply (MulAut.congr φ).injective
    rw [← hs, map_one, map_one]
  have hfix : fixSubgroup (MulAut.congr φ β) = Subgroup.centralizer ({s} : Set C) := by
    rw [← hs]
    ext y
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, eq_comm]
  have hL' : CFSG.Open.IsComponentOf (L.map (φ : S →* C)) (Subgroup.centralizer ({s} : Set C)) := by
    rw [← hfix, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr φ β]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map φ hL
  apply hadj s hs3 hs1 _ hL'
  obtain ⟨i, hi, ⟨f⟩⟩ := hU
  let ε : ↥L ≃* ↥(L.map (φ : S →* C)) := L.equivMapOfInjective (φ : S →* C) φ.injective
  exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ ε (Subgroup.map_center_eq ε)).symm.trans f⟩⟩

theorem e78TwoNoU38_holds :
    ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      (d.1 = .E7 q ∨ d.1 = .E8 q) → q.card = 2 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 →
          ∀ L : Subgroup S, CFSG.Open.IsComponentOf L
              (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) →
            ¬ catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU3eight := by
  intro S _ _ d q hd hq2 ⟨eS⟩ β hβ3 hβ1 L hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hKq : Nat.card (GaloisField 2 1) = q.card := by rw [hK, hq2]
  obtain ⟨idx, hv⟩ := d
  rcases hd with h7 | h8
  · change idx = .E7 q at h7
    subst h7
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv (GaloisField 2 1) hKq
    let φ : S ≃* ↥(adjointGroup Tag.E7 (GaloisField 2 1)) :=
      eS.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq
        CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot))
    exact excU9_noU38_of_adjoint φ
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.mem_innerAut_of_card_two hK (Or.inl rfl))
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
      (fun s hs3 hs1 J hJ hU => excU9_adjoint_E7_notU38 hK hs3 hs1 hJ hU) hβ3 hβ1 hL
  · change idx = .E8 q at h8
    subst h8
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv (GaloisField 2 1) hKq
    let φ : S ≃* ↥(adjointGroup Tag.E8 (GaloisField 2 1)) :=
      eS.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq
        CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot))
    exact excU9_noU38_of_adjoint φ
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.mem_innerAut_of_card_two hK (Or.inr rfl))
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
      (fun s hs3 hs1 J hJ hU => excU9_adjoint_E8_notU38 hK hs3 hs1 hJ hU) hβ3 hβ1 hL

end Catalogue

end CFSG.LocalAnalysis.GLTheoremA.I141FU9Ex

end