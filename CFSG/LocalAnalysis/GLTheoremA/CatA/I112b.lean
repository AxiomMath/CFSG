module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112CtxExt
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MHolds
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FNotL2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section


variable {G : Type} [Group G] [Finite G]

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

variable {G : Type} [Group G] [Finite G]

private theorem i112b_card_le_three_of_isL2
    {L : Subgroup G} (hL2 : IsLTwoOddPow (barOf 3 L))
    {W : Subgroup G} (hWL : W ≤ L) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL2' : IsL2TwoPowOdd (barOf 3 L) := isL2TwoPowOdd_of_isLTwoOddPow hL2
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hW
  have hWsub : Nat.card ↥(W.subgroupOf L) = 3 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv, hk]
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
  have hdisj : Disjoint (W.subgroupOf L) (GLAPPrimeCore 3 ↥L) := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hWsub]
    exact Nat.Coprime.pow_left k hcop
  let f : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)
  let g : ↥W →* barOf 3 L := f.comp (Subgroup.inclusion hWL)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hmem : (Subgroup.inclusion hWL w : ↥L) ∈ GLAPPrimeCore 3 ↥L :=
      (QuotientGroup.eq_one_iff _).1 hw
    have hmemW : (Subgroup.inclusion hWL w : ↥L) ∈ W.subgroupOf L :=
      Subgroup.mem_subgroupOf.2 w.2
    have hinf : W.subgroupOf L ⊓ GLAPPrimeCore 3 ↥L = ⊥ := disjoint_iff.1 hdisj
    have h1 : (Subgroup.inclusion hWL w : ↥L) = 1 := by
      have hmem' : (Subgroup.inclusion hWL w : ↥L) ∈ W.subgroupOf L ⊓ GLAPPrimeCore 3 ↥L := ⟨hmemW, hmem⟩
      rw [hinf] at hmem'
      exact Subgroup.mem_bot.1 hmem'
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have hpR : CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) ≤ 1 :=
    pRank_three_le_one_of_isL2TwoPowOdd hL2'
  have hcomm : ∀ a b : ↥W, a * b = b * a := fun a b => Subtype.ext (isElemAbelian_commute hW a.2 b.2)
  have hpow : ∀ a : ↥W, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hW.2 a a.2)
  have hk1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (barOf 3 L)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hk g hg le_top
  calc Nat.card W = 3 ^ k := hk
    _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (hk1.trans hpR)
    _ = 3 := by norm_num

private theorem i112b_card_le_nine_of_max
    {L : Subgroup G}
    (hmax : ∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
      (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R)
    {W : Subgroup G} (hWL : W ≤ L) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW3 : IsPGroup 3 ↥W := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hW.2 g.1 g.2)⟩
  obtain ⟨S, hSmem, hSmax⟩ := Set.Finite.exists_maximal
    (s := {S : Subgroup G | S ≤ L ∧ IsPGroup 3 ↥S ∧ W ≤ S}) (Set.toFinite _) ⟨W, hWL, hW3, le_rfl⟩
  obtain ⟨hSL, hS3, hWS⟩ := hSmem
  have hmaxS : ∀ S' : Subgroup G, S' ≤ L → IsPGroup 3 ↥S' → S ≤ S' → S' = S := fun S' h1 h2 h3 =>
    le_antisymm (hSmax ⟨h1, h2, hWS.trans h3⟩ h3) h3
  obtain ⟨⟨r, hr, s, hs, hrs⟩, hcard, -⟩ := hmax S hSL hS3 hmaxS
  have hdvd : Nat.card W ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hWS
    rw [hcard] at this
    exact this
  obtain ⟨i, hi, hWi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  by_contra hgt
  have hi3 : i = 3 := by
    by_contra hne
    have : i ≤ 2 := by omega
    have : Nat.card W ≤ 3 ^ 2 := by
      rw [hWi]
      exact Nat.pow_le_pow_right (by norm_num) this
    exact hgt this
  have hWS' : W = S := Subgroup.eq_of_le_of_card_ge hWS (by rw [hcard, hWi, hi3]; norm_num)
  have hr' : r ∈ W := by rw [hWS']; exact hr
  have hs' : s ∈ W := by rw [hWS']; exact hs
  exact hrs (isElemAbelian_commute hW hr' hs')

private theorem i112b_card_le_nine
    {L : Subgroup G}
    (hcase : IsLTwoOddPow (barOf 3 L) ∨
      (∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
        (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R))
    {W : Subgroup G} (hWL : W ≤ L) (hW : IsElemAbelian 3 W) : Nat.card W ≤ 3 ^ 2 := by
  rcases hcase with h | h
  · exact (i112b_card_le_three_of_isL2 h hWL hW).trans (by norm_num)
  · exact i112b_card_le_nine_of_max h hWL hW

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L89

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem i112NormAt_holds
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) (p : ℕ) :
    I112NormAt G p := by
  unfold I112NormAt
  intro hp hp2 X B L hXK hB hBX hL hE
  obtain ⟨E, hEL, hE', hE3⟩ := hE
  by_contra hnL
  have hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B := glaTwoLocalRank_le_pRank_of_isBmax hp hB X
  obtain ⟨-, h3, -, -, hcase⟩ := i112c_ext tables112_holds tableL2_unconditional tables112Types_holds
    tables112More_holds hsimple hKP hp hp2 hB.1 hBX hr hL hnL
  subst h3
  have hcase' : IsLTwoOddPow (barOf 3 L) ∨
      (∀ R : Subgroup G, R ≤ L → IsPGroup 3 ↥R →
        (∀ S : Subgroup G, S ≤ L → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R) := by
    rcases hcase with h | ⟨-, -, hR⟩
    · exact Or.inl h
    · exact Or.inr fun R h1 h2 h3 => (hR R h1 h2 h3).1
  have hle := i112b_card_le_nine hcase' hEL hE'
  have h33 : (3 : ℕ) ^ 3 ≤ 3 ^ 2 := hE3.trans hle
  norm_num at h33

end CFSG.LocalAnalysis.GLTheoremA.S8.L89

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

private theorem i112b_card_A6
    : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  omega

private theorem i112b_card_A7
    : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  have hp : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  omega

private theorem i112b_card_A9
    : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 9)
  have hp : Nat.card (Equiv.Perm (Fin 9)) = 362880 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  omega

private theorem i112b_card_J3
    {S : Type} [Group S]
    (φ : S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group) :
    Nat.card S = 50232960 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group TauCeti.SporadicName.J3
  calc Nat.card S = Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J3).Group :=
        Nat.card_congr φ.toEquiv
    _ = Nat.card (Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.J3) :=
        Nat.card_congr e.symm.toEquiv
    _ = 50232960 := CFSG.Sporadic.J3.card_J3

private theorem i112b_card_M22
    {S : Type} [Group S]
    (φ : S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group) :
    Nat.card S = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group TauCeti.SporadicName.M22
  calc Nat.card S = Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group :=
        Nat.card_congr φ.toEquiv
    _ = Nat.card (Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.M22) :=
        Nat.card_congr e.symm.toEquiv
    _ = 443520 := CFSG.Sporadic.Mathieu.card_M22

private theorem i112b_lie_A
    {S : Type} [Group S] [Finite S] (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderA n q.card :=
  lieOrderBridge_holds ⟨TauCeti.LieTypeIndex.A n q, hv⟩ S ⟨φ⟩

private theorem i112b_lie_twistedA
    {S : Type} [Group S] [Finite S] (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderTwistedA n q.card :=
  lieOrderBridge_holds ⟨TauCeti.LieTypeIndex.twistedA n q, hv⟩ S ⟨φ⟩

private theorem i112b_lie_B
    {S : Type} [Group S] [Finite S] (n : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n q).Valid)
    (φ : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group) :
    Nat.card S = CFSG.Open.orderBC n q.card :=
  lieOrderBridge_holds ⟨TauCeti.LieTypeIndex.B n q, hv⟩ S ⟨φ⟩

private theorem i112b_orderA2
    {Q : ℕ} (hQ : Q % 3 = 1) :
    CFSG.Open.orderA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) / 3 := by
  have hg : Nat.gcd 3 (Q - 1) = 3 := Nat.gcd_eq_left (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (Q ^ i - 1) = (Q ^ 2 - 1) * (Q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num)]
  unfold CFSG.Open.orderA
  simp only [show 2 * (2 + 1) / 2 = 3 from rfl, show 2 + 1 = 3 from rfl, hg, hprod]

private theorem i112b_orderTwistedA2
    {Q : ℕ} (hQ : Q % 3 = 2) :
    CFSG.Open.orderTwistedA 2 Q = Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) / 3 := by
  have hg : Nat.gcd 3 (Q + 1) = 3 := Nat.gcd_eq_left (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 3, (if Even i then Q ^ i - 1 else Q ^ i + 1) =
      (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num),
      if_pos (by decide), if_neg (by decide)]
  unfold CFSG.Open.orderTwistedA
  simp only [show 2 * (2 + 1) / 2 = 3 from rfl, show 2 + 1 = 3 from rfl, hg, hprod]

private theorem i112b_bound_A
    {Q : ℕ} (hQ : 19 ≤ Q) :
    1100000000 ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) / 3 := by
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
    _ ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

private theorem i112b_bound_T
    {Q : ℕ} (hQ : 19 ≤ Q) :
    1100000000 ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) / 3 := by
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
    _ ≤ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

private theorem i112b_orderA2_ne
    {Q : ℕ} (hQ : Q % 9 = 4 ∨ Q % 9 = 7) (N : ℕ)
    (hN : N = 181440 ∨ N = 50232960 ∨ N = 1451520 ∨ N = 193709880 ∨ N = 1056706560) :
    CFSG.Open.orderA 2 Q ≠ N := by
  by_cases hQ19 : 19 ≤ Q
  · intro h
    have hb := i112b_bound_A hQ19
    rw [i112b_orderA2 (by omega)] at h
    have hN' : 1100000000 ≤ N := h ▸ hb
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hN'
  · push Not at hQ19
    interval_cases Q <;> first | omega | (rcases hN with rfl | rfl | rfl | rfl | rfl <;> decide)

private theorem i112b_orderTwistedA2_ne
    {Q : ℕ} (hQ : Q % 9 = 2 ∨ Q % 9 = 5) (hQ3 : 3 ≤ Q) (N : ℕ)
    (hN : N = 181440 ∨ N = 50232960 ∨ N = 1451520 ∨ N = 193709880 ∨ N = 1056706560) :
    CFSG.Open.orderTwistedA 2 Q ≠ N := by
  by_cases hQ19 : 19 ≤ Q
  · intro h
    have hb := i112b_bound_T hQ19
    rw [i112b_orderTwistedA2 (by omega)] at h
    have hN' : 1100000000 ≤ N := h ▸ hb
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hN'
  · push Not at hQ19
    interval_cases Q <;> first | omega | (rcases hN with rfl | rfl | rfl | rfl | rfl <;> decide)

private theorem i112b_L2_ne
    (n : ℕ) (hn : n % 2 = 1) (hn1 : 1 < n) (N : ℕ)
    (hN : N = 181440 ∨ N = 50232960 ∨ N = 1451520 ∨ N = 193709880 ∨ N = 1056706560) :
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
    rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at hbig
  interval_cases n <;> first | omega | (rcases hN with rfl | rfl | rfl | rfl | rfl <;> norm_num at h)

private theorem i112b_card_of_excIndex
    {S : Type} [Group S] [Finite S] (i : TauCeti.CFSGIndex)
    (φ : S ≃* i.Group) (h : excIndex i) :
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
      rw [Nat.card_congr φ.toEquiv, i112b_card_A6]
    · have hn7 : n = 7 := h
      subst hn7
      right; left
      rw [Nat.card_congr φ.toEquiv, i112b_card_A7]
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M22 := h
    subst hs
    right; right; left
    exact i112b_card_M22 φ
  | lie j =>
    rcases j with ⟨d, hv⟩
    cases d with
    | A n q =>
      rcases n with _ | _ | _ | n
      · exact h.elim
      · exact h.elim
      · have hq : q.card % 9 = 4 ∨ q.card % 9 = 7 := h
        right; right; right; left
        exact ⟨q.card, hq, i112b_lie_A 2 q hv φ⟩
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
        exact ⟨q.card, hq, hq3, i112b_lie_twistedA 2 q hv φ⟩
      · exact h.elim
    | _ => exact h.elim

private theorem i112b_card_of_isType1430
    {S : Type} [Group S] [Finite S] (i : TauCeti.CFSGIndex)
    (φ : S ≃* i.Group) (h : S8.L84.isType1430 i) :
    Nat.card S = 181440 ∨ Nat.card S = 50232960 ∨ Nat.card S = 1451520 ∨
      Nat.card S = 193709880 ∨ Nat.card S = 1056706560 := by
  cases i with
  | cyclic p hp => rcases h with h | h | h <;> first | exact h.elim | cases h
  | alternating n hn =>
    rcases h with h | h | h
    · have hn9 : n = 9 := h
      subst hn9
      left
      rw [Nat.card_congr φ.toEquiv, i112b_card_A9]
    · cases h
    · exact h.elim
  | sporadic s =>
    rcases h with h | h | h
    · exact h.elim
    · have hs : s = TauCeti.SporadicName.J3 := by injection h
      subst hs
      right; left
      exact i112b_card_J3 φ
    · exact h.elim
  | lie j =>
    rcases h with h | h | h
    · cases h
    · cases h
    · rcases j with ⟨d, hv⟩
      cases d with
      | B n q =>
        rcases n with _ | _ | _ | _ | n
        · exact h.elim
        · exact h.elim
        · have hq : q.card = 8 := h
          right; right; right; right
          rw [i112b_lie_B _ q hv φ, hq]
          decide
        · have hq : q.card = 2 := h
          right; right; left
          rw [i112b_lie_B _ q hv φ, hq]
          decide
        · exact h.elim
      | A n q =>
        rcases n with _ | _ | n
        · exact h.elim
        · have hq : q.card = 729 := h
          right; right; right; left
          rw [i112b_lie_A _ q hv φ, hq]
          decide
        · exact h.elim
      | _ => exact h.elim

private theorem i112b_card_isA6
    {S : Type} [Group S] [Finite S] (i : TauCeti.CFSGIndex)
    (φ : S ≃* i.Group) (h : S8.isA6 i) : Nat.card S = 360 := by
  cases i with
  | cyclic p hp => rcases h with h | h <;> exact h.elim
  | alternating n hn =>
    rcases h with h | h
    · have hn6 : n = 6 := h
      subst hn6
      rw [Nat.card_congr φ.toEquiv, i112b_card_A6]
    · exact h.elim
  | sporadic s => rcases h with h | h <;> exact h.elim
  | lie j =>
    rcases h with h | h
    · exact h.elim
    · rcases j with ⟨d, hv⟩
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact h.elim
        · have h9 : q.card = 9 := h
          rw [i112b_lie_A _ q hv φ, h9]
          decide
        · exact h.elim
      | _ => exact h.elim

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

private theorem i112b_L2_ne360
    (n : ℕ) (hn : n % 2 = 1) (hn1 : 1 < n) :
    2 ^ n * (4 ^ n - 1) ≠ 360 := by
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
    norm_num at hbig
  interval_cases n <;> first | omega | norm_num at h

private theorem i112b_L2_ne_list
    (n : ℕ) (hn : n % 2 = 1) (hn1 : 1 < n)
    (h : 2 ^ n * (4 ^ n - 1) = 181440 ∨ 2 ^ n * (4 ^ n - 1) = 50232960 ∨
      2 ^ n * (4 ^ n - 1) = 1451520 ∨ 2 ^ n * (4 ^ n - 1) = 193709880 ∨
      2 ^ n * (4 ^ n - 1) = 1056706560) : False := by
  rcases h with h | h | h | h | h
  · exact i112b_L2_ne n hn hn1 181440 (Or.inl rfl) h
  · exact i112b_L2_ne n hn hn1 50232960 (Or.inr (Or.inl rfl)) h
  · exact i112b_L2_ne n hn hn1 1451520 (Or.inr (Or.inr (Or.inl rfl))) h
  · exact i112b_L2_ne n hn hn1 193709880 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
  · exact i112b_L2_ne n hn hn1 1056706560 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h

private theorem i112b_exc_ne_1430
    (x : ℕ)
    (hA : x = 360 ∨ x = 2520 ∨ x = 443520 ∨
      (∃ Q : ℕ, (Q % 9 = 4 ∨ Q % 9 = 7) ∧ x = CFSG.Open.orderA 2 Q) ∨
      (∃ Q : ℕ, (Q % 9 = 2 ∨ Q % 9 = 5) ∧ 3 ≤ Q ∧ x = CFSG.Open.orderTwistedA 2 Q))
    (hB : x = 181440 ∨ x = 50232960 ∨ x = 1451520 ∨ x = 193709880 ∨ x = 1056706560) : False := by
  rcases hA with h | h | h | ⟨Q, hQ, h⟩ | ⟨Q, hQ, hQ3, h⟩
  · rcases hB with h' | h' | h' | h' | h' <;> omega
  · rcases hB with h' | h' | h' | h' | h' <;> omega
  · rcases hB with h' | h' | h' | h' | h' <;> omega
  · exact i112b_orderA2_ne hQ x hB h.symm
  · exact i112b_orderTwistedA2_ne hQ hQ3 x hB h.symm

private theorem i112b_twoLocalRank_le_of_bound
    {X B : Subgroup G} (hB : IsElemAbelian 3 B)
    (hW : ∀ W U : Subgroup G, W ≤ X → IsElemAbelian 3 W → U ≤ X → U ≠ ⊥ → IsPGroup 2 U →
      W ≤ Subgroup.normalizer (U : Set G) → Nat.card W ≤ Nat.card B) :
    GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hB
  have hBm : m ≤ CFSG.Open.pRank 3 B := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hB hm
  refine le_trans ?_ hBm
  unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
  refine csSup_le' ?_
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E hEH hE
  have hPG1 : P.map X.subtype ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective P X.subtype_injective).1 h)
  have hPG2 : IsPGroup 2 (P.map X.subtype) := hP2.map X.subtype
  have hle := Subgroup.le_normalizer_map (H := P) X.subtype
  have hE' : IsElemAbelian 3 (E.map X.subtype) := CFSG.SectionRank.isElemAbelian_map hE X.subtype
  have hcard : Nat.card ↥(E.map X.subtype) = Nat.card ↥E :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hEX : E.map X.subtype ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPX : P.map X.subtype ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hEN : E.map X.subtype ≤ Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) :=
    (Subgroup.map_mono hEH).trans hle
  have hb := hW (E.map X.subtype) (P.map X.subtype) hEX hE' hPX hPG1 hPG2 hEN
  rw [hcard, hm] at hb
  exact hb

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA

variable {G : Type} [Group G] [Finite G]

theorem i112At_holds
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) : I112At G := by
  unfold I112At
  intro X B L₁ hXK hBX hB hW hL hnB
  have hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B := i112b_twoLocalRank_le_of_bound hB hW
  obtain ⟨-, -, -, -, -, htype⟩ := i112c_full tables112_holds tableL2_unconditional tables112Types_holds
    hsimple hKP Nat.prime_three (by norm_num) hB hBX hr hL hnB
  obtain ⟨-, -, -, -, hcase⟩ := i112c_ext tables112_holds tableL2_unconditional tables112Types_holds
    tables112More_holds hsimple hKP Nat.prime_three (by norm_num) hB hBX hr hL hnB
  have hcase' : IsLTwoOddPow (barOf 3 L₁) ∨
      (∀ R : Subgroup G, R ≤ L₁ → IsPGroup 3 ↥R →
        (∀ S : Subgroup G, S ≤ L₁ → IsPGroup 3 ↥S → R ≤ S → S = R) → IsThreeOnePlusTwo R) := by
    rcases hcase with h | ⟨-, -, hR⟩
    · exact Or.inl h
    · exact Or.inr fun R h1 h2 h3 => (hR R h1 h2 h3).1
  have hQ := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  refine ⟨?_, ?_, fun W hWL hW' => i112b_card_le_nine hcase' hWL hW', ?_⟩
  ·
    rintro ⟨⟨i, hi, ⟨φ⟩⟩, hz⟩
    rcases htype with h2 | h2
    · obtain ⟨n, hn2, hn1, hcardL2⟩ := card_of_isLTwoOddPow h2
      have h1 := Subgroup.card_mul_index (Subgroup.center (barOf 3 L₁))
      rw [hz, one_mul] at h1
      have hPS : Nat.card (PSimple 3 L₁) = Nat.card (barOf 3 L₁) := h1
      have h360 := i112b_card_isA6 i φ hi
      rw [hPS, hcardL2] at h360
      exact i112b_L2_ne360 n hn2 hn1 h360
    · have hex := isExcShape_of_types hQ h2
      have := hex.1
      exact absurd (hz.symm.trans this) (by norm_num)
  ·
    rintro ⟨j, hj, ⟨φ⟩⟩
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
      have hN := i112b_card_of_isType1430 j φ hj
      rw [hPS, hcardL2] at hN
      exact i112b_L2_ne_list n hn2 hn1 hN
    · obtain ⟨-, ⟨i, hi, ⟨ψ⟩⟩⟩ := isExcShape_of_types hQ h2
      have hA := i112b_card_of_excIndex i ψ hi
      have hB := i112b_card_of_isType1430 j φ hj
      exact i112b_exc_ne_1430 _ hA hB
  ·
    intro b hb hbn J hJ
    obtain ⟨hcomp, ⟨e⟩⟩ := i112c_layer_G tables112_holds tableL2_unconditional tables112Types_holds
      tables112More_holds hsimple hKP hB hBX hr hL hnB hb hbn
    rw [closureIn_eq_bClosure] at hJ
    have hJeq : J = GLAPLayer 3 (bClosure B L₁ ⊓ Subgroup.centralizer ({b} : Set G)) :=
      Lemma53Ns.glaPComponent_eq_of_le Nat.prime_three hJ hcomp (le_sSup hJ)
    subst hJeq
    exact ⟨e.trans (QuotientGroup.congr _ _ (quotEquivBarX Nat.prime_three hL.1 hL.2.1)
      (Subgroup.map_center_eq _)).symm⟩

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
