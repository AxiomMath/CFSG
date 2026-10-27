module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs103
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxClaim
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

namespace CatSingle

variable {G : Type} [Group G] [Finite G]

theorem single_core (T : Tables112) (TL : TableL2) (TT : Tables112Types) (TM : Tables112More)
    (h183 : Input18_3_4) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    {X E J : Subgroup G} {z : G} (hXK : CFSG.Open.IsKGroup ↥X) (hzE : z ∈ E) (hEX : E ≤ X)
    (hEel : IsElemAbelian 3 E) (hr : 3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card E)
    (hJ : GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) J)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    (∃ K : Subgroup G, GLAPComponent 3 X K ∧ J ≤ K ∧ E ≤ Subgroup.normalizer (K : Set G)) ∨
      ∃ L₁ : Subgroup G, GLAPComponent 3 X L₁ ∧ ¬ E ≤ Subgroup.normalizer (L₁ : Set G) ∧
        Nonempty (PQuot 3 J ≃* PSimple 3 L₁) := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hZX : Subgroup.zpowers z ≤ X := Subgroup.zpowers_le.2 (hEX hzE)
  have hZE : Subgroup.zpowers z ≤ E := Subgroup.zpowers_le.2 hzE
  have hZel : IsElemAbelian 3 (Subgroup.zpowers z) := isElemAbelian_mono hEel hZE
  obtain ⟨𝒞, hC1, hC2, hC3, hC4⟩ := h183 G X hXK 3 hp (Subgroup.zpowers z) hZX hZel J hJ
  have hJW : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [hC2]
    exact le_iSup₂_of_le 1 (GLAPLayer 3 X).one_mem (by rw [gLBConj_one])
  by_cases hA : ∃ L₀ ∈ 𝒞, z ∈ Subgroup.normalizer (L₀ : Set G)
  · obtain ⟨L₀, hL₀, hzL₀⟩ := hA
    have hall : ∀ L ∈ 𝒞, L = L₀ := by
      intro L hL
      obtain ⟨e, he, hLe⟩ := hC4 L₀ hL₀ L hL
      have he' : e ∈ Subgroup.normalizer (L₀ : Set G) := (Subgroup.zpowers_le.2 hzL₀) he
      rw [← hLe, mem_normalizer_iff_gLBConj_eq.1 he']
    have hW : (⨆ L ∈ 𝒞, L) = L₀ :=
      le_antisymm (iSup₂_le fun L hL => (hall L hL).le) (le_iSup₂_of_le L₀ hL₀ le_rfl)
    refine Or.inl ⟨L₀, hC1 L₀ hL₀, hW ▸ hJW, ?_⟩
    rw [← hW, hC2, ← closureIn_eq_iSup_gLBConj]
    exact L62.le_normalizer_closureIn_of_le hEJ
      (fun g hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer (hEX hg)))
  · push Not at hA
    obtain ⟨L₁, hL₁mem⟩ : ∃ L₁, L₁ ∈ 𝒞 := by
      by_contra hne
      push Not at hne
      have : (⨆ L ∈ 𝒞, L) = ⊥ := by
        simp only [iSup_eq_bot]
        intro L hL
        exact absurd hL (hne L)
      exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (this ▸ hJW))
    have hL₁ : GLAPComponent 3 X L₁ := hC1 L₁ hL₁mem
    have hzn : z ∉ Subgroup.normalizer (L₁ : Set G) := hA L₁ hL₁mem
    have hnE : ¬ E ≤ Subgroup.normalizer (L₁ : Set G) := fun h => hzn (h hzE)
    have hr' : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 E :=
      CFSG.AGLEmbedding.le_pRank_of_pow_le_card hp le_rfl hEel hr
    obtain ⟨hcomp, ⟨e⟩⟩ := i112c_layer_G T TL TT TM hsimple hKP hEel hEX hr' hL₁ hnE hzE hzn
    have hbX : bClosure E L₁ ≤ X := by
      refine iSup₂_le fun b hb => ?_
      rw [← mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hEX hb))]
      exact gLBConj_mono hL₁.1
    have hWb : (⨆ L ∈ 𝒞, L) ≤ bClosure E L₁ := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨e', he', hLe⟩ := hC4 L₁ hL₁mem L hL
      rw [← hLe]
      exact le_iSup₂_of_le e' (hZE he') le_rfl
    have hcz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
        Subgroup.centralizer ({z} : Set G) := S3.centralizer_zpowers z
    have hJle : J ≤ bClosure E L₁ ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine le_inf (hJW.trans hWb) ?_
      rw [← hcz]
      exact hJ.1.trans inf_le_right
    have hHle : bClosure E L₁ ⊓ Subgroup.centralizer ({z} : Set G) ≤
        X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      inf_le_inf hbX (by rw [hcz])
    have hJH : GLAPComponent 3 (bClosure E L₁ ⊓ Subgroup.centralizer ({z} : Set G)) J :=
      glaPComponent_of_le hp hJ hJle hHle
    have hJeq : J = GLAPLayer 3 (bClosure E L₁ ⊓ Subgroup.centralizer ({z} : Set G)) :=
      Lemma53Ns.glaPComponent_eq_of_le hp hJH hcomp (le_sSup hJH)
    subst hJeq
    exact Or.inr ⟨L₁, hL₁, hnE, ⟨e.trans (QuotientGroup.congr _ _
      (quotEquivBarX hp hL₁.1 hL₁.2.1) (Subgroup.map_center_eq _)).symm⟩⟩

theorem quot_center_equiv {Q S : Type} [Group Q] [Group S] [IsSimpleGroup S]
    (hQ : Nontrivial (Q ⧸ Subgroup.center Q)) (e : Q ≃* S) :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* S) := by
  haveI : IsSimpleGroup Q := e.isSimpleGroup
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h1 | h1
    · exact h1
    · exfalso
      haveI : Subsingleton (Q ⧸ Subgroup.center Q) := by
        rw [h1]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton (Q ⧸ Subgroup.center Q) ‹_›
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

open CatDistinct in
theorem card_isU3eight (hb : OrderBridge) {S : Type} [Group S] [Finite S]
    (h : catalogIs S S9.isU3eight) : Nat.card S = 5515776 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isU3eight, onLie] at hi
  | alternating n hn => simp [S9.isU3eight, onLie] at hi
  | sporadic s => simp [S9.isU3eight, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | r <;> simp [S9.isU3eight, onLie] at hi
      rw [hb ⟨.twistedA 2 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 2 q.card = 5515776
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isU3eight, onLie] at hi

open CatDistinct in
theorem card_isSp6two (hb : OrderBridge) {S : Type} [Group S] [Finite S]
    (h : catalogIs S S9.isSp6two) : Nat.card S = 1451520 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S9.isSp6two, onLie] at hi
  | alternating n hn => simp [S9.isSp6two, onLie] at hi
  | sporadic s => simp [S9.isSp6two, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | B r q =>
      rcases r with _ | _ | _ | _ | r <;> simp [S9.isSp6two, onLie] at hi
      rw [hb ⟨.B 3 q, hv⟩ S ⟨e⟩]
      show orderBC 3 q.card = 1451520
      rw [(TauCeti.PrimePower.card_def q).trans hi]
      decide
    | _ => simp [S9.isSp6two, onLie] at hi

theorem lie_A (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] (n : ℕ)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderA n q.card :=
  hb ⟨TauCeti.LieTypeIndex.A n q, hv⟩ S ⟨φ⟩

theorem lie_twistedA (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S] (n : ℕ)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderTwistedA n q.card :=
  hb ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩ S ⟨φ⟩

theorem orderA2 {Q : ℕ} (hQ : Q % 3 = 1) :
    CFSG.Open.orderA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) / 3 := by
  have hg : Nat.gcd 3 (Q - 1) = 3 := Nat.gcd_eq_left (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (Q ^ i - 1) = (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num)]
  unfold CFSG.Open.orderA
  simp only [show 2 * (2 + 1) / 2 = 3 from rfl, show 2 + 1 = 3 from rfl, hg, hprod]

theorem orderTwistedA2 {Q : ℕ} (hQ : Q % 3 = 2) :
    CFSG.Open.orderTwistedA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) / 3 := by
  have hg : Nat.gcd 3 (Q + 1) = 3 := Nat.gcd_eq_left (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (if Even i then Q ^ i - 1 else Q ^ i + 1) =
      (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num),
      if_pos (by decide), if_neg (by decide)]
  unfold CFSG.Open.orderTwistedA
  simp only [show 2 * (2 + 1) / 2 = 3 from rfl, show 2 + 1 = 3 from rfl, hg, hprod]

theorem bound_A {Q : ℕ} (hQ : 19 ≤ Q) : 1100000000 ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) / 3 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : 6859 ≤ Q ^ 3 := by
    calc 6859 = 19 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h2 : 360 ≤ Q ^ 2 - 1 := by
    have : 361 ≤ Q ^ 2 := by
      calc 361 = 19 ^ 2 := by norm_num
        _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    omega
  have h3 : 6858 ≤ Q ^ 3 - 1 := by omega
  calc 1100000000 * 3 ≤ 6859 * (360 * 6858) := by norm_num
    _ ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

theorem bound_T {Q : ℕ} (hQ : 19 ≤ Q) : 1100000000 ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) / 3 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have h1 : 6859 ≤ Q ^ 3 := by
    calc 6859 = 19 ^ 3 := by norm_num
      _ ≤ Q ^ 3 := Nat.pow_le_pow_left hQ 3
  have h2 : 360 ≤ Q ^ 2 - 1 := by
    have : 361 ≤ Q ^ 2 := by
      calc 361 = 19 ^ 2 := by norm_num
        _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    omega
  have h3 : 6860 ≤ Q ^ 3 + 1 := by omega
  calc 1100000000 * 3 ≤ 6859 * (360 * 6860) := by norm_num
    _ ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

@[expose] def IsTarget (N : ℕ) : Prop := N = 5515776 ∨ N = 25920 ∨ N = 13685760 ∨ N = 1451520

theorem IsTarget.lt {N : ℕ} (hN : IsTarget N) : N < 1100000000 := by
  rcases hN with rfl | rfl | rfl | rfl <;> norm_num

theorem orderA2_ne {Q : ℕ} (hQ : Q % 9 = 4 ∨ Q % 9 = 7) {N : ℕ} (hN : IsTarget N) :
    CFSG.Open.orderA 2 Q ≠ N := by
  by_cases hQ19 : 19 ≤ Q
  · intro h
    have hb := bound_A hQ19
    rw [orderA2 (by omega)] at h
    have hN' : 1100000000 ≤ N := h ▸ hb
    exact absurd hN.lt (not_lt.2 hN')
  · push Not at hQ19
    interval_cases Q <;> first | omega | (rcases hN with rfl | rfl | rfl | rfl <;> decide)

theorem orderTwistedA2_ne {Q : ℕ} (hQ : Q % 9 = 2 ∨ Q % 9 = 5) (hQ3 : 3 ≤ Q) {N : ℕ}
    (hN : IsTarget N) : CFSG.Open.orderTwistedA 2 Q ≠ N := by
  by_cases hQ19 : 19 ≤ Q
  · intro h
    have hb := bound_T hQ19
    rw [orderTwistedA2 (by omega)] at h
    have hN' : 1100000000 ≤ N := h ▸ hb
    exact absurd hN.lt (not_lt.2 hN')
  · push Not at hQ19
    interval_cases Q <;> first | omega | (rcases hN with rfl | rfl | rfl | rfl <;> decide)

theorem L2_ne (n : ℕ) (hn : n % 2 = 1) (hn1 : 1 < n) {N : ℕ} (hN : IsTarget N) :
    2 ^ n * (4 ^ n - 1) ≠ N := by
  intro h
  have hn30 : n ≤ 30 := by
    by_contra hc
    push Not at hc
    have h2 : 2 ^ 31 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 16 ≤ 4 ^ n := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 3 ≤ 4 ^ n - 1 := by omega
    have hbig : 2 ^ 31 * 3 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h2 h3
    rw [h] at hbig
    rcases hN with rfl | rfl | rfl | rfl <;> norm_num at hbig
  interval_cases n <;> first | omega | (rcases hN with rfl | rfl | rfl | rfl <;> norm_num at h)

open CatDistinct in
theorem card_of_excIndex (hb : OrderBridge)
    (hm22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520)
    {S : Type} [Group S] [Finite S] (i : TauCeti.CFSGIndex) (φ : S ≃* i.Group) (h : excIndex i) :
    Nat.card S = 360 ∨ Nat.card S = 2520 ∨ Nat.card S = 443520 ∨
      (∃ Q : ℕ, (Q % 9 = 4 ∨ Q % 9 = 7) ∧ Nat.card S = CFSG.Open.orderA 2 Q) ∨
      (∃ Q : ℕ, (Q % 9 = 2 ∨ Q % 9 = 5) ∧ 3 ≤ Q ∧ Nat.card S = CFSG.Open.orderTwistedA 2 Q) := by
  cases i with
  | cyclic p hp => exact h.elim
  | alternating n hn =>
    rcases h with h | h
    · have hn6 : n = 6 := h
      subst hn6
      left
      rw [card_alternating_of_iso hn φ]
      decide
    · have hn7 : n = 7 := h
      subst hn7
      right; left
      rw [card_alternating_of_iso hn φ]
      decide
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M22 := h
    subst hs
    right; right; left
    rw [Nat.card_congr φ.toEquiv]
    exact hm22
  | lie j =>
    rcases j with ⟨d, hv⟩
    cases d with
    | A n q =>
      rcases n with _ | _ | _ | n
      · exact h.elim
      · exact h.elim
      · have hq : q.card % 9 = 4 ∨ q.card % 9 = 7 := h
        right; right; right; left
        exact ⟨q.card, hq, lie_A hb 2 q hv φ⟩
      · exact h.elim
    | twistedA n q =>
      rcases n with _ | _ | _ | n
      · exact h.elim
      · exact h.elim
      · have hq : q.card % 9 = 2 ∨ q.card % 9 = 5 := h
        have hq3 : 3 ≤ q.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
        right; right; right; right
        exact ⟨q.card, hq, hq3, lie_twistedA hb 2 q hv φ⟩
      · exact h.elim
    | _ => exact h.elim

theorem exc_ne {x : ℕ}
    (hA : x = 360 ∨ x = 2520 ∨ x = 443520 ∨
      (∃ Q : ℕ, (Q % 9 = 4 ∨ Q % 9 = 7) ∧ x = CFSG.Open.orderA 2 Q) ∨
      (∃ Q : ℕ, (Q % 9 = 2 ∨ Q % 9 = 5) ∧ 3 ≤ Q ∧ x = CFSG.Open.orderTwistedA 2 Q))
    (hB : IsTarget x) : False := by
  rcases hA with h | h | h | ⟨Q, hQ, h⟩ | ⟨Q, hQ, hQ3, h⟩
  · rcases hB with h' | h' | h' | h' <;> omega
  · rcases hB with h' | h' | h' | h' <;> omega
  · rcases hB with h' | h' | h' | h' <;> omega
  · exact orderA2_ne hQ hB h.symm
  · exact orderTwistedA2_ne hQ hQ3 hB h.symm

theorem not_types (hb : CatDistinct.OrderBridge)
    (hm22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520)
    {X L₁ : Subgroup G} (hL : GLAPComponent 3 X L₁)
    (htype : IsLTwoOddPow (barOf 3 L₁) ∨ IsHatSix (barOf 3 L₁) ∨ IsHatSeven (barOf 3 L₁) ∨
      IsHatMTwentyTwo (barOf 3 L₁) ∨ IsSLThreeExc (barOf 3 L₁) ∨ IsSUThreeExc (barOf 3 L₁) ∨
      IsSUThreeTwoPow (barOf 3 L₁))
    {N : ℕ} (hN : IsTarget N) (hcard : Nat.card (PSimple 3 L₁) = N) : False := by
  have hQ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  rcases htype with h2 | h2
  · obtain ⟨n, hn2, hn1, hcardL2⟩ := card_of_isLTwoOddPow h2
    have hcen : Subgroup.center (barOf 3 L₁) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      exact Lemma26Ns.central_eq_one_of_isLTwoOddPow h2 z (fun w => Subgroup.mem_center_iff.1 hz w)
    have hc1 : Nat.card ↥(Subgroup.center (barOf 3 L₁)) = 1 := by rw [hcen, Subgroup.card_bot]
    have h1 := Subgroup.card_mul_index (Subgroup.center (barOf 3 L₁))
    rw [hc1, one_mul] at h1
    have hPS : Nat.card (PSimple 3 L₁) = Nat.card (barOf 3 L₁) := h1
    rw [hPS, hcardL2] at hcard
    exact L2_ne n hn2 hn1 hN hcard
  · obtain ⟨-, ⟨i, hi, ⟨ψ⟩⟩⟩ := isExcShape_of_types hQ h2
    have hA := card_of_excIndex hb hm22 i ψ hi
    rw [hcard] at hA
    exact exc_ne hA hN

theorem single_of_card (T : Tables112) (TL : TableL2) (TT : Tables112Types) (TM : Tables112More)
    (h183 : Input18_3_4) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    (hb : CatDistinct.OrderBridge)
    (hm22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520)
    {Q : TauCeti.CFSGIndex → Prop}
    (hQ : ∀ (S : Type) [Group S] [Finite S], catalogIs S Q → IsTarget (Nat.card S))
    {X E J : Subgroup G} {z : G} (hXK : CFSG.Open.IsKGroup ↥X) (hzE : z ∈ E) (hEX : E ≤ X)
    (hEel : IsElemAbelian 3 E) (hr : 3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card E)
    (hJ : GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) J)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) (hJQ : catalogIs (PSimple 3 J) Q) :
    ∃ K : Subgroup G, GLAPComponent 3 X K ∧ J ≤ K ∧ E ≤ Subgroup.normalizer (K : Set G) := by
  rcases single_core T TL TT TM h183 hsimple hKP hXK hzE hEX hEel hr hJ hEJ with
    h | ⟨L₁, hL₁, hnE, ⟨e⟩⟩
  · exact h
  · exfalso
    have hr' : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 E :=
      CFSG.AGLEmbedding.le_pRank_of_pow_le_card Nat.prime_three le_rfl hEel hr
    obtain ⟨-, -, -, htype⟩ := i112c_types T TL TT hsimple hKP Nat.prime_three (by norm_num) hEel
      hEX hr' hL₁ hnE
    have hQJ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
    have hQL := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL₁
    haveI : IsSimpleGroup (PSimple 3 L₁) := hQL.2
    haveI : IsSimpleGroup (PSimple 3 J) := hQJ.2
    obtain ⟨f⟩ := quot_center_equiv (inferInstance : Nontrivial (PSimple 3 J)) e
    have hcard : Nat.card (PSimple 3 L₁) = Nat.card (PSimple 3 J) :=
      (Nat.card_congr f.toEquiv).symm
    exact not_types hb hm22 hL₁ htype (hQ _ hJQ) hcard

end CatSingle

open CatSingle in
theorem i112SingleU38At_of_tables {G : Type} [Group G] [Finite G] (T : Tables112) (TL : TableL2)
    (TT : Tables112Types) (TM : Tables112More) (h183 : Input18_3_4) (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) (hb : CatDistinct.OrderBridge)
    (hm22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520) :
    I112SingleU38At G := by
  intro X z E J hXK hzE hEX hEel hr hJ hEJ hU
  refine single_of_card T TL TT TM h183 hsimple hKP hb hm22 (Q := S9.isU3eight)
    (fun S _ _ h => Or.inl (card_isU3eight hb h)) hXK hzE hEX hEel hr hJ hEJ hU

open CatSingle in
theorem i112SingleStdAt_of_tables {G : Type} [Group G] [Finite G] (T : Tables112) (TL : TableL2)
    (TT : Tables112Types) (TM : Tables112More) (h183 : Input18_3_4) (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) (hb : CatDistinct.OrderBridge)
    (hm22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520) :
    I112SingleStdAt G := by
  intro X z E J hXK hzE hEX hEel hr hJ hEJ hStd
  refine single_of_card T TL TT TM h183 hsimple hKP hb hm22
    (Q := fun i => S9.isU4two i ∨ S9.isU5two i ∨ S9.isSp6two i) (fun S _ _ h => ?_)
    hXK hzE hEX hEel hr hJ hEJ hStd
  obtain ⟨i, hi | hi | hi, ⟨e⟩⟩ := h
  · exact Or.inr (Or.inl (CatDistinct.card_isU4two hb ⟨i, hi, ⟨e⟩⟩))
  · exact Or.inr (Or.inr (Or.inl (CatDistinct.card_isU5two hb ⟨i, hi, ⟨e⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (card_isSp6two hb ⟨i, hi, ⟨e⟩⟩)))

end CFSG.LocalAnalysis.GLTheoremA
