module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Block
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4Edge
public import CFSG.ClassicalInvolution.Q3.TL4SepTwoD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
open scoped commutatorElement

structure QFam {Y : Type} [Group Y] (Φ : Set (Subgroup Y)) (Q : Subgroup Y) : Prop where
  hyp : TypeRHyp Φ
  normal : Q.Normal
  two : IsPGroup 2 Q
  isPGroup : ∀ L ∈ Φ, IsPGroup 2 L
  inv_mem : ∀ L ∈ Φ, ∀ u : Y, IsUniqueInvolution L u → u ∈ Q
  notEmpty : ∀ L ∈ Φ, ¬ AEmpty Φ L

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {Q : Subgroup Y}

theorem isPGroup_of_inv_mem (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    {L : Subgroup Y} (hL : L ∈ Φ) {u : Y} (hu : IsUniqueInvolution L u) (hQn : Q.Normal)
    (hQ2 : IsPGroup 2 Q) (huQ : u ∈ Q) : IsPGroup 2 L :=
  isPGroup_of_oddCent hΦ.hyp hL hu (TC.oddCoreImg_centralizer_eq_bot hO hQn hQ2 huQ)
    (hΦ.twoGroup L hL)

theorem natCard_sylow_eq_eight (hΦ : TypeRHyp Φ) :
    ∀ L ∈ Φ, ∀ P : Subgroup Y, IsSylow2In P L → Nat.card ↥P = 8 := by
  intro L hL P hP
  obtain ⟨e⟩ := hΦ.sylow L hL P hP
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem not_aEmpty_of_mem_twinSet (hΦ : TypeRHyp Φ) {K : Subgroup Y} (hK : K ∈ Φ)
    (hA : ¬ AEmpty Φ K) {J : Subgroup Y} (hJ : J ∈ twinSet Φ K) : ¬ AEmpty Φ J := by
  obtain ⟨J₀, zK, zJ₀, hv⟩ := not_aEmpty_iff.mp hA
  obtain ⟨Ks, d⟩ :=
    FrameTwins.exists_of_aviol hΦ.hyp hΦ.twoGroup (natCard_sylow_eq_eight hΦ) hK hv
  have hJ' : J ∈ ({K, Ks} : Set (Subgroup Y)) := by
    rw [← d.twins]
    exact hJ
  rcases hJ' with rfl | rfl
  · exact hA
  · obtain ⟨J', hv'⟩ := d.isAInv_twin ⟨J₀, hv⟩
    exact not_aEmpty_iff.mpr ⟨J', _, _, hv'⟩

theorem QFam.of_twinOrbits (hΦ : TypeRHyp Φ) (hO : classicalInvolutionOddCore Y = ⊥)
    {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) (htw : TwinOrbits Φ K) {z : Y}
    (hz : IsUniqueInvolution K z) (hQn : Q.Normal) (hQ2 : IsPGroup 2 Q) (hzQ : z ∈ Q) :
    QFam Φ Q := by
  have hc := hΦ.hyp.conjInvariant
  have hinv : ∀ L ∈ Φ, ∀ u : Y, IsUniqueInvolution L u → u ∈ Q := by
    intro L hL u hu
    obtain ⟨g, J, hJ, rfl⟩ := htw L hL
    have hzJ : IsUniqueInvolution J z := isUniqueInvolution_of_mem_twinSet hz hJ
    rw [← (hzJ.conj g).eq hu]
    exact hQn.conj_mem z hzQ g
  refine ⟨hΦ, hQn, hQ2, fun L hL => ?_, hinv, fun L hL => ?_⟩
  · obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hL
    exact isPGroup_of_inv_mem hΦ hO hL hu hQn hQ2 (hinv L hL u hu)
  · obtain ⟨g, J, hJ, rfl⟩ := htw L hL
    obtain ⟨J', zJ, zJ', hv⟩ := not_aEmpty_iff.mp (not_aEmpty_of_mem_twinSet hΦ hK hA hJ)
    exact not_aEmpty_iff.mpr ⟨_, _, _, hv.conj hc g⟩

namespace QFam

variable (h : QFam Φ Q)
include h

theorem hypGen : HypOmegaGen Φ := h.hyp.hyp

theorem mem_RSet {L : Subgroup Y} (hL : L ∈ Φ) : L ∈ RSet Φ :=
  TC.mem_RSet_of_isPGroup hL (h.isPGroup L hL)

theorem oddCoreOf_eq_bot {L : Subgroup Y} (hL : L ∈ Φ) : oddCoreOf L = ⊥ :=
  TL4.oddCoreOf_eq_bot_of_isPGroup (h.isPGroup L hL)

theorem isSylow2In_self {L : Subgroup Y} (hL : L ∈ Φ) : IsSylow2In L L :=
  ⟨le_rfl, h.isPGroup L hL, fun _ hV _ hLV => le_antisymm hV hLV⟩

theorem natCard_eq_eight {L : Subgroup Y} (hL : L ∈ Φ) : Nat.card L = 8 :=
  natCard_sylow_eq_eight h.hyp L hL L (h.isSylow2In_self hL)

theorem mem_omegaNbr_iff {K J : Subgroup Y} :
    J ∈ omegaNbr Φ K ↔ J ∈ Φ ∧ J ≠ K ∧ J ≤ Subgroup.normalizer (K : Set Y) :=
  TC.mem_omegaNbr_iff h.hypGen h.isPGroup

theorem commutes_of_le_isPGroup {L M P : Subgroup Y} (hL : L ∈ Φ) (hM : M ∈ Φ) (hLM : L ≠ M)
    (hP : IsPGroup 2 P) (hLP : L ≤ P) (hMP : M ≤ P) : Commutes L M := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  exact Q3CP.l67Gen Y Φ h.hypGen S L (h.mem_RSet hL) M (h.mem_RSet hM) (hLP.trans hS)
    (hMP.trans hS) hLM

theorem commutes_of_mem_omegaNbr {K J : Subgroup Y} (hK : K ∈ Φ) (hJ : J ∈ omegaNbr Φ K) :
    Commutes K J := by
  obtain ⟨hJΦ, hJK, hJN⟩ := h.mem_omegaNbr_iff.mp hJ
  exact TL4.commutes_of_le_normalizer h.hypGen (h.mem_RSet hK) (h.mem_RSet hJΦ)
    (h.isPGroup K hK) (h.isPGroup J hJΦ) (Ne.symm hJK) hJN

theorem mem_omegaNbr_of_commutes {K J : Subgroup Y} (hJ : J ∈ Φ) (hJK : J ≠ K)
    (hc : Commutes J K) : J ∈ omegaNbr Φ K :=
  h.mem_omegaNbr_iff.mpr ⟨hJ, hJK, AscL62.le_normalizer_of_commutes hc⟩

end QFam

omit [Finite Y] in
theorem commutes_symm {A B : Subgroup Y} (h : Commutes A B) : Commutes B A :=
  fun x hx y hy => (h y hy x hx).symm

theorem mem_omegaOfSet_of_mem_omegaNbr (hΦ : HypOmegaGen Φ) {K L : Subgroup Y} {z : Y}
    (hz : IsUniqueInvolution K z) (hL : L ∈ omegaNbr Φ K) (hLt : L ∉ twinSet Φ K) :
    L ∈ omegaOfSet Φ (twinSet Φ K) := by
  refine ⟨hL.1, fun N hN => ?_⟩
  exact TwinExitPf4.omegaNbr_of_twin hΦ hN.1 hz (isUniqueInvolution_of_mem_twinSet hz hN) hL
    (fun e => hLt (e ▸ hN))

omit [Finite Y] in
theorem eq_one_of_pow_two_pow {X : Subgroup Y} (hX : Odd (Nat.card X)) {x : Y} (hx : x ∈ X)
    {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x = 1 := by
  have hodd : Odd (orderOf x) := hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

namespace QFam

variable (h : QFam Φ Q)
include h

theorem le_centralizer_inv_of_odd {M X : Subgroup Y} (hM : M ∈ Φ) {w : Y}
    (hw : IsUniqueInvolution M w) (hX : Odd (Nat.card X))
    (hMX : M ≤ Subgroup.normalizer (X : Set Y)) : ∀ x ∈ X, w * x = x * w := by
  intro x hx
  have hwQ : w ∈ Q := h.inv_mem M hM w hw
  have hc : w * x * w⁻¹ * x⁻¹ = 1 := by
    have hcX : w * x * w⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMX hw.mem) x).mp hx) (X.inv_mem hx)
    have hcQ : w * x * w⁻¹ * x⁻¹ ∈ Q := by
      have := Q.mul_mem hwQ (h.normal.conj_mem w⁻¹ (Q.inv_mem hwQ) x)
      rwa [show w * (x * w⁻¹ * x⁻¹) = w * x * w⁻¹ * x⁻¹ by group] at this
    exact TC.eq_one_of_mem_odd_of_mem_isPGroup hX h.two hcX hcQ
  calc w * x = (w * x * w⁻¹ * x⁻¹) * (x * w) := by group
    _ = x * w := by rw [hc, one_mul]

theorem le_centralizer_of_odd {M X : Subgroup Y} (hM : M ∈ Φ) (hX : Odd (Nat.card X))
    (hMX : M ≤ Subgroup.normalizer (X : Set Y)) : M ≤ Subgroup.centralizer (X : Set Y) := by
  have hΦ := h.hypGen
  obtain ⟨w, hw⟩ := Sec6Gen.exists_uniqueInvolution hΦ hM
  have hwX := h.le_centralizer_inv_of_odd hM hw hX hMX
  have hM2 := h.isPGroup M hM
  intro m hm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hdX : x * m * x⁻¹ * m⁻¹ ∈ X := by
    have := X.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hMX hm) x⁻¹).mp (X.inv_mem hx))
    rwa [show x * (m * x⁻¹ * m⁻¹) = x * m * x⁻¹ * m⁻¹ by group] at this
  have hxw : x * w * x⁻¹ = w := by
    rw [← hwX x hx]
    group
  have hwx : IsUniqueInvolution (conjSub x M) w := by
    have := hw.conj x
    rwa [hxw] at this
  have hd : x * m * x⁻¹ * m⁻¹ = 1 := by
    by_cases hMx : conjSub x M = M
    ·
      have hdM : x * m * x⁻¹ * m⁻¹ ∈ M := by
        have hxm : x * m * x⁻¹ ∈ M := by
          rw [← hMx]
          exact conj_mem_conjSub hm
        exact M.mul_mem hxm (M.inv_mem hm)
      exact TC.eq_one_of_mem_odd_of_mem_isPGroup hX hM2 hdX hdM
    ·
      have hMxΦ : conjSub x M ∈ Φ := hΦ.conjInvariant x M hM
      obtain ⟨hle, hcomm⟩ := hΦ.omega4 M hM (conjSub x M) hMxΦ (Ne.symm hMx)
      have hwI : w ∈ M ⊓ conjSub x M := ⟨hw.mem, hwx.mem⟩
      have h2 : 2 ∣ Nat.card ↥(M ⊓ conjSub x M) := by
        have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw.sq) hw.ne_one
        rw [← hwo, ← Subgroup.orderOf_mk w hwI]
        exact orderOf_dvd_natCard _
      have hv1 : padicValNat 2 (Nat.card ↥(M ⊓ conjSub x M)) = 1 := by
        have hpos : 0 < Nat.card ↥(M ⊓ conjSub x M) := Nat.card_pos
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have : 1 ≤ padicValNat 2 (Nat.card ↥(M ⊓ conjSub x M)) :=
          one_le_padicValNat_of_dvd hpos.ne' h2
        omega
      have hc := hcomm hv1
      rw [h.oddCoreOf_eq_bot hM, bot_inf_eq, le_bot_iff,
        Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
      have hxm : x * m * x⁻¹ ∈ conjSub x M := conj_mem_conjSub hm
      have hcm : Commute (x * m * x⁻¹) m⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp (hc (M.inv_mem hm))) _ hxm
      have hm8 : m ^ (2 ^ 3) = 1 := by
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h.natCard_eq_eight hM]
        exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard M hm)
      have hd8 : (x * m * x⁻¹ * m⁻¹) ^ (2 ^ 3) = 1 := by
        rw [hcm.mul_pow, conj_pow, inv_pow, hm8, inv_one, mul_one, mul_one, mul_inv_cancel]
      exact eq_one_of_pow_two_pow hX hdX hd8
  calc x * m = (x * m * x⁻¹ * m⁻¹) * (m * x) := by group
    _ = m * x := by rw [hd, one_mul]

theorem commutes_of_le_of_not_mem_aStar (hb : Thm3A.Thm3RBelowG (Nat.card Y))
    {X L J M : Subgroup Y} {zL zJ : Y} (hX : X ≠ ⊤) (hL : L ∈ Φ) (hLX : L ≤ X) (hJX : J ≤ X)
    (hv : AViol Φ L J zL zJ) (hM : M ∈ Φ) (hMX : M ≤ X) (hMB : M ∉ aStar Φ L) :
    Commutes L M := by
  have hc := comm_of_le_of_aViol h.hyp hb hX hL hLX hJX hv hM hMX hMB
  rw [h.oddCoreOf_eq_bot hM, h.oddCoreOf_eq_bot hL, bot_sup_eq, inf_idem] at hc
  have hN : Odd (Nat.card ↥(oddCoreOf X)) := oddCoreOf_odd_natCard X
  have hnorm : ∀ A : Subgroup Y, A ≤ X →
      A ≤ Subgroup.normalizer ((oddCoreOf X : Subgroup Y) : Set Y) := fun A hA x hx =>
    mem_normalizer_of_conjSub_eq
      (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer (hA hx)))
  have hLC := h.le_centralizer_of_odd hL hN (hnorm L hLX)
  intro l hl m hm
  have hn : m * l * m⁻¹ * l⁻¹ ∈ oddCoreOf X := hc (Subgroup.commutator_mem_commutator hm hl)
  have hnl : Commute (m * l * m⁻¹ * l⁻¹) l :=
    (Subgroup.mem_centralizer_iff.mp (hLC hl)) _ hn
  have hl8 : l ^ (2 ^ 3) = 1 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h.natCard_eq_eight hL]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard L hl)
  have hn8 : (m * l * m⁻¹ * l⁻¹) ^ (2 ^ 3) = 1 := by
    have e : (m * l * m⁻¹ * l⁻¹) * l = m * l * m⁻¹ := by group
    have h1 : ((m * l * m⁻¹ * l⁻¹) * l) ^ (2 ^ 3) = 1 := by
      rw [e, conj_pow, hl8, mul_one, mul_inv_cancel]
    rwa [hnl.mul_pow, hl8, mul_one] at h1
  have hn1 := eq_one_of_pow_two_pow hN hn hn8
  calc l * m = (m * l * m⁻¹ * l⁻¹)⁻¹ * (m * l) := by group
    _ = m * l := by rw [hn1, inv_one, one_mul]

end QFam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
