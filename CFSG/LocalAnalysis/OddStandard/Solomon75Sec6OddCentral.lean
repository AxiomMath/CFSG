module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6CtrlDefs
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Equiv

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section OddCentral

variable {X : Type} [Group X] [Finite X]

private theorem l66_isPCompIn {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsPCompIn 2 H J := by
  rcases h with ⟨⟨u, -, -, hpc, -⟩, -⟩ | ⟨⟨hpc, -⟩, -⟩
  · exact hpc
  · exact hpc

private theorem l66_isTwoGenQuasi {n : ℕ} {H J : Subgroup X} (h : Sec6KComp X n H J) :
    IsTwoGenQuasi ↥J :=
  (isTwoGenQuasi_subgroupOf_iff (l66_isPCompIn h).1).1
    (isPComponent_two_iff.1 (l66_isPCompIn h).2).2

private theorem l66_sq_eq_one {g : X} (hg : orderOf g = 2) : g ^ 2 = 1 := by
  rw [← hg]
  exact pow_orderOf_eq_one g

private theorem l66_mem_oTwoPrimeOf {A : Subgroup X} {x : X} (hx : x ∈ A) (h2 : x ^ 2 = 1) :
    x ∈ oTwoPrimeOf A :=
  mem_oTwoPrimeOf hx 1 (by simpa using h2)

private theorem l66_exists_involution {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) :
    ∃ v ∈ L, orderOf v = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥L := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := primeResidual_eq_bot_of_coprime_card (G := ↥L) 2 hcop
    rw [hq.1] at h1
    have hnt : Nontrivial ↥L := by
      by_contra hnot
      rw [not_nontrivial_iff_subsingleton] at hnot
      obtain ⟨a, b, hab⟩ := hq.2.2.2
      exact hab (Subsingleton.elim (a * b) (b * a))
    exact top_ne_bot h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

private theorem l66_le_of_normalizes {L A : Subgroup X} (hq : IsTwoGenQuasi ↥L)
    (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) (hLA : L ≤ normalizer (A : Set X)) {v : X}
    (hvL : v ∈ L) (hv : orderOf v = 2) (hvA : v ∈ A) : L ≤ A := by
  haveI hn : (A.subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h1 := (Subgroup.mem_normalizer_iff.1 (hLA g.2) x).1 hx
    simpa using h1
  have hv' : orderOf (⟨v, hvL⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hv
  have htop := eq_top_of_normal_of_involution hq hZ (A := A.subgroupOf L) (s := ⟨v, hvL⟩)
    (by rw [Subgroup.mem_subgroupOf]; exact hvA) hv'
  intro x hx
  have : (⟨x, hx⟩ : ↥L) ∈ A.subgroupOf L := by
    rw [htop]
    exact Subgroup.mem_top _
  exact this

private theorem l66_mem_normalizer_of_map_le {V : Subgroup X} {b : X}
    (h : V.map (MulAut.conj b).toMonoidHom ≤ V) : b ∈ normalizer (V : Set X) :=
  mem_normalizer_of_map_conj_eq (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]))

private theorem l66_mem_normalizer_oTwoPrimeOf {A : Subgroup X} {g : X}
    (hg : g ∈ normalizer (A : Set X)) : g ∈ normalizer (oTwoPrimeOf A : Set X) := by
  apply l66_mem_normalizer_of_map_le
  have := map_oTwoPrimeOf_le A (MulAut.conj g).toMonoidHom
  rwa [map_conj_eq_of_mem_normalizer hg] at this

private theorem l66_oddCoreOf_le_of_normal {K C : Subgroup X} (hKC : K ≤ C)
    (hn : C ≤ normalizer (K : Set X)) : oddCoreOf K ≤ oddCoreOf C :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le K).trans hKC)
    (fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (hn hc)) (odd_card_oddCoreOf K)

private theorem l66_oddCoreOf_eq_bot {H F : Subgroup X} (hF : IsPCompIn 2 H F)
    (hH : oddCoreOf H = ⊥) : oddCoreOf F = ⊥ := by
  have h : oddCoreOf F ≤ oddCoreOf H :=
    pPrimeCoreOf_le_oddCoreOf hF.1 (isPComponent_two_iff.1 hF.2).1
  rw [hH] at h
  exact le_bot_iff.1 h

private theorem l66_K_le (n : ℕ) (t : X) : Sec6K X n (cen t) ≤ cen t :=
  sSup_le fun _ hL => (l66_isPCompIn hL).1

private theorem l66_M_le_K (n : ℕ) (H : Subgroup X) : Sec6M X n H ≤ Sec6K X n H := by
  rw [sec6K_eq]
  exact le_sup_right

private theorem l66_center_quot_eq_bot
    {n : ℕ} {H L : Subgroup X} (hL : Sec6MComp X n H L) :
    center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ :=
  mcLLyCenterFree _ hL.1.2.1

private theorem l66_M_le_base (n : ℕ) (t : X) : Sec6M X n (cen t) ≤ Sec6Base X n t := by
  unfold Sec6Base
  exact le_sup_left

private theorem l66_core_bot {n : ℕ} {t b : X} (h65 : Sec6L65 X n t)
    (hb : b ∈ Sec6M X n (cen t)) (hb2 : orderOf b = 2) : oddCoreOf (cen b) = ⊥ :=
  h65 b (l66_M_le_base n t hb) hb2

private abbrev L66HU (X : Type) [Group X] (n : ℕ) (t : X) : Prop :=
  ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
    Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x

private theorem l66_piece_mem {n : ℕ} {t x : X} (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) (hx : x ∈ Sec6M X n (cen t)) (hx2 : orderOf x = 2) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) : Sec6KComp X n (cen x) (sec6Piece L x) := by
  obtain ⟨F, hF, hPF⟩ := hC.land x (Subgroup.mem_sup_left hx) hx2 L (Or.inr hL)
  have hFeq := hU x hx hx2 L F hL hF hPF
  rw [l66_oddCoreOf_eq_bot (l66_isPCompIn hF) (l66_core_bot h65 hx hx2), bot_sup_eq] at hFeq
  rwa [← hFeq]

private theorem l66_pPrimeCore_eq_bot {L : Subgroup X} (hL : oddCoreOf L = ⊥) :
    pPrimeCore 2 ↥L = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hL

private theorem l66_eq_one_of_central {L : Subgroup X} (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥)
    (hO : oddCoreOf L = ⊥) {z : X} (hzL : z ∈ L) (hz : ∀ l ∈ L, l * z = z * l) : z = 1 := by
  let π : ↥L →* ↥L ⧸ pPrimeCore 2 ↥L := QuotientGroup.mk' _
  have hc : π ⟨z, hzL⟩ ∈ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz l l.2)
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : (⟨z, hzL⟩ : ↥L) ∈ π.ker := hc
  rw [QuotientGroup.ker_mk', l66_pPrimeCore_eq_bot hO, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

private theorem l66_mem_normalizer_centralizer {F : Subgroup X} {g : X}
    (hg : g ∈ normalizer (F : Set X)) : g ∈ normalizer (centralizer (F : Set X) : Set X) := by
  have key : ∀ g ∈ normalizer (F : Set X), ∀ c ∈ centralizer (F : Set X),
      g * c * g⁻¹ ∈ centralizer (F : Set X) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro f hf
    have hf' : g⁻¹ * f * g ∈ F := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) f).1 hf
      simpa using this
    have h1 := hc _ hf'
    calc f * (g * c * g⁻¹) = g * ((g⁻¹ * f * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * f * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * f := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun h => ?_⟩
  have h2 := key g⁻¹ (inv_mem hg) _ h
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h2

private theorem l66_isElemAbelian_pair {a b : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : a * b = b * a) : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({a, b} : Set X)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set X)) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]; exact hab
      · rw [Set.mem_singleton_iff.mp hx]; exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.mp hy]; exact hb
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure ({a, b} : Set X)) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [(show Commute y z from hc).mul_pow, hy, hz, one_mul]
  | inv y hy' hy => rw [inv_pow, hy, inv_one]

private theorem l66_cen_le_normalizer_W (n : ℕ) (t : X) :
    cen t ≤ normalizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
  fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (Sec6M_cen_normal n t hc)

private theorem l66_M_le_cen (n : ℕ) (t : X) : Sec6M X n (cen t) ≤ cen t :=
  (l66_M_le_K n (cen t)).trans (l66_K_le n t)

private theorem l66_cW_comm {n : ℕ} {t e : X} (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) (he : e ∈ Sec6M X n (cen t)) (he2 : orderOf e = 2) {L : Subgroup X}
    (hL : Sec6MComp X n (cen t) L) {c p : X} (hc : c ∈ oddCoreOf (Sec6M X n (cen t)))
    (hce : c ∈ cen e) (hp : p ∈ sec6Piece L e) : c * p = p * c := by
  have hPL : sec6Piece L e ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPt : sec6Piece L e ≤ cen t := hPL.trans (l66_isPCompIn (Or.inr hL)).1
  have hWO : oddCoreOf (Sec6M X n (cen t)) ≤ oddCoreOf (cen t) :=
    l66_oddCoreOf_le_of_normal (l66_M_le_cen n t) (Sec6M_cen_normal n t)
  have hcL : c ∈ normalizer (L : Set X) :=
    pPrimeCoreOf_le_normalizer_of_isPCompIn (l66_isPCompIn (Or.inr hL)) (hWO hc)
  have hcP : c ∈ normalizer (sec6Piece L e : Set X) :=
    l66_mem_normalizer_oTwoPrimeOf (mem_normalizer_inf hcL (Subgroup.le_normalizer hce))
  have hpW : p ∈ normalizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
    l66_cen_le_normalizer_W n t (hPt hp)
  have hcomP : ⁅c, p⁆ ∈ sec6Piece L e := by
    rw [commutatorElement_def]
    exact (sec6Piece L e).mul_mem ((Subgroup.mem_normalizer_iff.1 hcP p).1 hp)
      ((sec6Piece L e).inv_mem hp)
  have hcomW : ⁅c, p⁆ ∈ oddCoreOf (Sec6M X n (cen t)) := by
    have h1 : ⁅c, p⁆ = c * (p * c⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h1]
    exact (oddCoreOf (Sec6M X n (cen t))).mul_mem hc
      ((Subgroup.mem_normalizer_iff.1 hpW c⁻¹).1 ((oddCoreOf (Sec6M X n (cen t))).inv_mem hc))
  have hPO : oddCoreOf (sec6Piece L e) = ⊥ :=
    l66_oddCoreOf_eq_bot (l66_isPCompIn (l66_piece_mem hC hU h65 he he2 hL))
      (l66_core_bot h65 he he2)
  have hle : sec6Piece L e ⊓ oddCoreOf (Sec6M X n (cen t)) ≤ oddCoreOf (sec6Piece L e) :=
    le_oddCoreOf_of_normalized inf_le_left
      (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
        (l66_cen_le_normalizer_W n t (hPt hg)))
      ((odd_card_oddCoreOf _).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  have h := hle ⟨hcomP, hcomW⟩
  rw [hPO, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.1 h

private theorem l66_W_le_cen
    {n : ℕ} {t : X} (hS : Sec6Setting X n t) (hC : Sec6CtrlAt X n t) (hU : L66HU X n t)
    (h65 : Sec6L65 X n t) {L : Subgroup X} (hL : Sec6MComp X n (cen t) L) {x : X} (hxL : x ∈ L)
    (hx2 : orderOf x = 2) : oddCoreOf (Sec6M X n (cen t)) ≤ cen x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ Sec6M X n (cen t) := le_sSup (s := {M | Sec6MComp X n (cen t) M}) hL
  have hxM := hLM hxL
  have hPmem := l66_piece_mem hC hU h65 hxM hx2 hL
  have hPO : oddCoreOf (sec6Piece L x) = ⊥ :=
    l66_oddCoreOf_eq_bot (l66_isPCompIn hPmem) (l66_core_bot h65 hxM hx2)
  have hPL : sec6Piece L x ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hPx : sec6Piece L x ≤ cen x := (oTwoPrimeOf_le _).trans inf_le_right
  have hxP : x ∈ sec6Piece L x :=
    l66_mem_oTwoPrimeOf ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ (l66_sq_eq_one hx2)
  have hPn : IsDoubleCoverOfAlt ↥(sec6Piece L x) n := by
    rcases hPmem with hA | hM
    · exact isDoubleCoverOfAlt_congr' ((QuotientGroup.quotientMulEquivOfEq
        (l66_pPrimeCore_eq_bot hPO)).trans QuotientGroup.quotientBot) hA.2
    · exfalso
      have h1 := l66_eq_one_of_central (l66_center_quot_eq_bot hM) hPO hxP
        fun p hp => Subgroup.mem_centralizer_singleton_iff.1 (hPx hp)
      rw [h1, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
  obtain ⟨u, hu2, hunc⟩ : ∃ u : ↥(sec6Piece L x), u ^ 2 = 1 ∧ u ∉ center ↥(sec6Piece L x) := by
    rcases hS.deg with h8 | h11
    · rw [h8] at hPn
      exact GH74.GLS.Stage12.McLRec.coverFacts_eight.exists_noncentral _ hPn
    · rw [h11] at hPn
      exact Sporadic.Recognition.LyonsSims.coverFacts_eleven.exists_noncentral _ hPn
  have hu1 : (u : X) ≠ 1 := fun h => hunc (by rw [show u = 1 from Subtype.ext h]; exact one_mem _)
  have hux' : (u : X) ≠ x := by
    intro h
    apply hunc
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [h]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hPx g.2)
  have hu2' : (u : X) ^ 2 = 1 := by
    have := congrArg Subtype.val hu2
    simpa using this
  have hux : (u : X) * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 (hPx u.2)
  have hEab := l66_isElemAbelian_pair (l66_sq_eq_one hx2) hu2' hux.symm
  have hEcard : 2 ^ 2 ≤ Nat.card (Subgroup.closure ({x, (u : X)} : Set X)) := by
    obtain ⟨V, hVE, -, hV4⟩ :=
      LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hx2
        (orderOf_eq_prime hu2' hu1) hux.symm (Ne.symm hux')
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV4]
    exact Subgroup.card_le_of_le hVE
  have hEM : Subgroup.closure ({x, (u : X)} : Set X) ≤ Sec6M X n (cen t) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact hxM
    · rw [Set.mem_singleton_iff.mp h]
      exact hLM (hPL u.2)
  have hEx : Subgroup.closure ({x, (u : X)} : Set X) ≤ cen x := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · rw [Set.mem_singleton_iff.mp h]
      exact hPx u.2
  have hEN : Subgroup.closure ({x, (u : X)} : Set X) ≤
      normalizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
    hEM.trans ((l66_M_le_cen n t).trans (l66_cen_le_normalizer_W n t))
  have hcop : Nat.Coprime 2 (Nat.card (oddCoreOf (Sec6M X n (cen t)))) :=
    Nat.coprime_two_left.2 (odd_card_oddCoreOf _)
  rw [← SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hEab hEcard
    hEN hcop]
  refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
  have hao : orderOf a = 2 := orderOf_eq_prime (hEab.2 a haE) ha1
  have hxPa : x ∈ sec6Piece L a :=
    l66_mem_oTwoPrimeOf ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_singleton_iff.1 (hEx haE)).symm⟩ (l66_sq_eq_one hx2)
  intro c hc
  exact Subgroup.mem_centralizer_singleton_iff.2
    (l66_cW_comm hC hU h65 (hEM haE) hao hL hc.1 hc.2 hxPa)

private theorem l66_M_le_centralizer_W
    {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hC : Sec6CtrlAt X n t) (hU : L66HU X n t) (h65 : Sec6L65 X n t) :
    Sec6M X n (cen t) ≤ centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) := by
  refine sSup_le fun L hL => ?_
  have hq := l66_isTwoGenQuasi (Or.inr hL)
  have hLN : L ≤ normalizer (centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) : Set X) :=
    fun g hg => l66_mem_normalizer_centralizer
      (l66_cen_le_normalizer_W n t ((l66_isPCompIn (Or.inr hL)).1 hg))
  obtain ⟨v, hvL, hv2⟩ := l66_exists_involution hq
  have hvC : v ∈ centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (l66_W_le_cen hS hC hU h65 hL hvL hv2 hw)
  exact l66_le_of_normalizes hq (l66_center_quot_eq_bot hL) hLN hvL hv2 hvC

theorem sec6_M_le_centralizer_oddCoreOf
    {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hC : Sec6CtrlAt X n t)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
      Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x)
    (h65 : Sec6L65 X n t) :
    Sec6M X n (cen t) ≤ centralizer (oddCoreOf (Sec6M X n (cen t)) : Set X) :=
  l66_M_le_centralizer_W hS hC hU h65

theorem sec6_oddCoreOf_K_le_centralizer
    {n : ℕ} {t : X} (hS : Sec6Setting X n t)
    (hC : Sec6CtrlAt X n t)
    (hU : ∀ x ∈ Sec6M X n (cen t), orderOf x = 2 → ∀ L F : Subgroup X, Sec6MComp X n (cen t) L →
      Sec6KComp X n (cen x) F → sec6Piece L x ≤ F → F = oddCoreOf F ⊔ sec6Piece L x)
    (h65 : Sec6L65 X n t) :
    K0 X n (cen t) = ⊥ →
      oddCoreOf (Sec6K X n (cen t)) ≤ centralizer (Sec6K X n (cen t) : Set X) := by
  intro hA
  have hKM : Sec6K X n (cen t) = Sec6M X n (cen t) := by rw [sec6K_eq, hA, bot_sup_eq]
  rw [hKM]
  exact Subgroup.le_centralizer_iff.mp (sec6_M_le_centralizer_oddCoreOf hS hC hU h65)

end OddCentral

end CFSG.OddStandard.Solomon75
