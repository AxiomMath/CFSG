module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
import CFSG.LieType.Steinberg.CentralExt.GriessClassical
import CFSG.Adapters.TauCetiLieModels
import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26h.Decode
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
import CFSG.Quasithin.Background.B1MoreElevenD
import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OddCentre
import CFSG.RankThree.PartOne.KF.ClsPOmegaPlus
import CFSG.RankThree.PartOne.KF.ClsPOmegaMinus
import CFSG.GH74.GLS.LU.Local.Core
public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

@[expose] noncomputable def excJMap (p : ℕ) {X J : Subgroup Ω} (hJX : J ≤ X) : ↥J →* PSimple p X :=
  ((QuotientGroup.mk' (Subgroup.center (PQuot p X))).comp
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).comp (Subgroup.inclusion hJX)

section


private theorem center_pQuot_eq_bot_of_type167J_aux1 {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
    (h : catalogIs S (isLnA n 2)) : Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 4 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨m, F, _, _, hm, hF, ⟨e'⟩⟩ := exists_psl_of_isLnEps (S := S) ⟨i, hi, ⟨e⟩⟩
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨-, ⟨eP⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_five_le
      (k := F) (n := m + 1) (by omega)
    have h1 : Nat.card (CFSG.Open.griessHopfMultiplier S) = 1 := by
      rw [Nat.card_congr
          (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e').toEquiv,
        Nat.card_congr eP.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
        Fintype.card_eq_nat_card, hF]
      simp
    rw [h1]
    exact one_dvd 4
  all_goals omega

private theorem center_pQuot_eq_bot_of_type167J_aux2 {S : Type} [Group S] {n : ℕ} (hn : 4 ≤ n)
    (h : catalogIs S (isOmMA n 2)) : Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 4 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | ⟨h3, -⟩
  · cases i with
    | cyclic _ _ => simp [isOmM, onLie] at hi
    | alternating _ _ => simp [isOmM, onLie] at hi
    | sporadic _ => simp [isOmM, onLie] at hi
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedD r qq =>
        obtain ⟨hr, hq⟩ : r = n ∧ qq.card = 2 := hi
        have hcard : qq.p ^ qq.exponent = 2 ^ 1 := by
          rw [← TauCeti.PrimePower.card_def, hq]
          norm_num
        obtain ⟨hq2, hq1⟩ :=
          Nat.Prime.pow_inj' qq.prime_p Nat.prime_two qq.exponent_pos.ne' (by norm_num) hcard
        have hm := CFSG.Models.lieModel_twistedD r qq hv e
        rw [hq2, hq1] at hm
        rcases hm.2 with hcl | ⟨h0, -⟩
        · obtain ⟨-, ⟨eP⟩⟩ :=
            CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row hcl
          have hM := CFSG.RankThree.PartOne.KFU.card_multiplier_pOmegaMinus
            (n := r) (f := 1) (by norm_num) (by omega)
          rw [Nat.card_congr eP.toEquiv, hM]
          exact one_dvd 4
        · omega
      | _ => simp [isOmM, onLie] at hi
  · omega

private theorem center_pQuot_eq_bot_of_type167J_aux3_omP {S : Type} [Group S] {n k : ℕ}
    (hk : 1 ≤ k) (hn : 3 ≤ n) (hnk : k = 1 → 5 ≤ n) (h : catalogIs S (isOmP n (2 ^ k))) :
    Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 4 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => simp [isOmP, onLie] at hi
  | alternating _ _ => simp [isOmP, onLie] at hi
  | sporadic _ => simp [isOmP, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r qq =>
      obtain ⟨hr, hq⟩ : r = n ∧ qq.card = 2 ^ k := hi
      have hcard : qq.p ^ qq.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hq]
      obtain ⟨hq2, hq1⟩ :=
        Nat.Prime.pow_inj' qq.prime_p Nat.prime_two qq.exponent_pos.ne' (by omega) hcard
      have hm := CFSG.Models.lieModel_D r qq hv e
      rw [hq2, hq1] at hm
      rcases hm.2 with hcl | ⟨h0, -⟩
      · have hq' : 3 ≤ (2 : ℕ) ^ k ∨ ((2 : ℕ) ^ k = 2 ∧ 5 ≤ r) := by
          rcases Nat.eq_or_lt_of_le hk with hk1 | hk2
          · right
            exact ⟨by rw [← hk1]; norm_num, by rw [hr]; exact hnk (by omega)⟩
          · left
            have h2 : 2 ≤ k := by omega
            calc 3 ≤ 2 ^ 2 := by norm_num
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2
        obtain ⟨-, ⟨eP⟩⟩ :=
          CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row hcl hq'
        have hM := CFSG.RankThree.PartOne.KFU.card_multiplier_pOmegaPlus
          (n := r) (f := k) hk
        rw [Nat.card_congr eP.toEquiv]
        exact hM
      · omega
    | _ => simp [isOmP, onLie] at hi

private theorem center_pQuot_eq_bot_of_type167J_aux3_l4 {S : Type} [Group S] {k : ℕ}
    (hk2 : 2 ≤ k) (h : catalogIs S (isLnA 4 (2 ^ k))) :
    Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 4 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  · obtain ⟨m, F, _, _, hm, hF, ⟨e'⟩⟩ := exists_psl_of_isLnEps (S := S) ⟨i, hi, ⟨e⟩⟩
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨-, ⟨eP⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
      (k := F) (n := m + 1) (by omega) (by
        rw [Fintype.card_eq_nat_card, hF]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2) (by omega)
    have h1 : Nat.card (CFSG.Open.griessHopfMultiplier S) = 1 := by
      rw [Nat.card_congr
          (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e').toEquiv,
        Nat.card_congr eP.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
        hm, Fintype.card_eq_nat_card, hF]
      have hodd : Odd (2 ^ k - 1) :=
        Nat.Even.sub_odd Nat.one_le_two_pow
          (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))) odd_one
      have hco : Nat.Coprime 4 (2 ^ k - 1) := by
        have h4 := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
        simpa using h4
      exact Nat.coprime_iff_gcd_eq_one.mp hco
    rw [h1]
    exact one_dvd 4
  · omega
  · omega
  · omega
  · have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    rw [h] at h4
    omega

private theorem center_pQuot_eq_bot_of_type167J_aux3 {S : Type} [Group S] {n k : ℕ} (hk : 1 ≤ k)
    (hn : 3 ≤ n) (hnk : k = 1 → 5 ≤ n) (h : catalogIs S (isOmPA n (2 ^ k))) :
    Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 4 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | ⟨hn3, hi⟩
  · exact center_pQuot_eq_bot_of_type167J_aux3_omP hk hn hnk ⟨i, hi, ⟨e⟩⟩
  · have hk2 : 2 ≤ k := by
      by_contra hlt
      exact absurd (hnk (by omega)) (by omega)
    exact center_pQuot_eq_bot_of_type167J_aux3_l4 hk2 ⟨i, hi, ⟨e⟩⟩

theorem center_pQuot_eq_bot_of_type167J {p : ℕ} {C J : Subgroup Ω} (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : GLAPComponent p C J) (h : Type167J p J) : Subgroup.center (PQuot p J) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hpg := CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' hp J
  have hodd : Odd (Nat.card (Subgroup.center (PQuot p J))) := by
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  refine CFSG.SectionRank.QTK.Insp443.center_eq_bot_of_card_multiplier_dvd_four
    (CFSG.Quasithin.B1Red.isQuasisimple_of_open hq) hodd (MulEquiv.refl _) ?_
  rcases h with ⟨rfl, n, hn, h5, hc⟩ | ⟨rfl, n, hn, h6, hc⟩ |
    ⟨n, k, hn, h3, hnk, hk, hdvd, hc⟩
  · exact center_pQuot_eq_bot_of_type167J_aux1 h5 hc
  · exact center_pQuot_eq_bot_of_type167J_aux2 (by omega) hc
  · exact center_pQuot_eq_bot_of_type167J_aux3 hk h3 hnk hc

end

private theorem exists_fixed_element_aux1 {p : ℕ} {X : Subgroup Ω}
    (hnt : Nontrivial (PSimple p X)) : GLAPPrimeCore p ↥X ≠ ⊤ := by
  intro htop
  have hsub : Subsingleton (PQuot p X) := by
    show Subsingleton (↥X ⧸ GLAPPrimeCore p ↥X)
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  have hsub2 : Subsingleton (PSimple p X) :=
    (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p X))).subsingleton
  exact (not_subsingleton_iff_nontrivial.2 hnt) hsub2

private theorem exists_fixed_element_aux2 {p : ℕ} {X : Subgroup Ω} {x l : Ω}
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hl : l ∈ X)
    (hlx : ∀ y ∈ X, (l⁻¹ * y * l)⁻¹ * (x⁻¹ * y * x) ∈ GLAPPrimeCoreOf p X) :
    CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥X)) := by
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (X : Set Ω) := Subgroup.inv_mem _ hxN
  have hbar_inv : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x⁻¹, hxN'⟩ =
      MulAut.conj ((QuotientGroup.mk (⟨l, hl⟩ : ↥X))⁻¹) :=
    (barAut_inv_eq_conj_iff hxN' hl).2 hlx
  have hsub : (⟨x⁻¹, hxN'⟩ : ↥(Subgroup.normalizer (X : Set Ω))) = (⟨x, hxN⟩)⁻¹ :=
    Subtype.ext rfl
  have h2 : (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩)⁻¹ =
      (MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥X)))⁻¹ := by
    rw [← map_inv, ← hsub, hbar_inv, map_inv]
  exact inv_inj.1 h2

private theorem exists_fixed_element_aux3 {p : ℕ} {X : Subgroup Ω} {x : Ω}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hOZ : GLAPPrimeCore p ↥X ≤ Subgroup.center ↥X)
    (hcm : x ∈ centModSubgroup p X) : x ∈ cs X := by
  have hJeq : ⁅X, X⁆ = X := by
    rw [← Subgroup.map_subtype_commutator X, hX.1, Subgroup.map_top, X.range_subtype]
  have hconjX : ∀ j ∈ X, x * j * x⁻¹ = j := by
    refine CFSG.GH74.GLS.LU.Local.centralizes_of_perfect_mod_center (J := X) (x := x) hJeq ?_
    intro j hj
    have hoj : ⁅j, x⁆ ∈ GLAPPrimeCoreOf p X := hcm.2 j hj
    have hcinv : (⁅j, x⁆)⁻¹ ∈ GLAPPrimeCoreOf p X := (GLAPPrimeCoreOf p X).inv_mem hoj
    have hcX : (⁅j, x⁆)⁻¹ ∈ X := Subgroup.map_subtype_le (GLAPPrimeCore p ↥X) hcinv
    have hco : (⟨(⁅j, x⁆)⁻¹, hcX⟩ : ↥X) ∈ GLAPPrimeCore p ↥X :=
      (chev_mem_glaPPrimeCoreOf_iff hcX).1 hcinv
    have hcent := hOZ hco
    refine ⟨(⁅j, x⁆)⁻¹, hcX, ?_, ?_⟩
    · intro g hg
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcent ⟨g, hg⟩)).symm
    · rw [commutatorElement_def]
      group
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := hconjX y hy
  have hxy : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h]
  exact hxy.symm

private theorem exists_fixed_element_aux4 {p : ℕ} {X : Subgroup Ω} {x : Ω} {a : PQuot p X}
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : x ^ p = 1)
    (hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ = MulAut.conj a) :
    ((QuotientGroup.mk' (Subgroup.center (PQuot p X)) a) : PSimple p X) ^ p = 1 := by
  have hNxp : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (X : Set Ω))) ^ p = 1 := by
    ext
    simpa using hxp
  have hbarp : (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩) ^ p = 1 := by
    rw [← map_pow, hNxp, map_one]
  have hconjp : (MulAut.conj a) ^ p = 1 := by rw [← hbar]; exact hbarp
  have hconjp2 : MulAut.conj (a ^ p) = 1 := by
    rw [map_pow]
    exact hconjp
  have hcenter : a ^ p ∈ Subgroup.center (PQuot p X) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have hq := congrArg (fun φ : MulAut (PQuot p X) => φ q) hconjp2
    simp only [MulAut.conj_apply, MulAut.one_apply] at hq
    have h2 : a ^ p * q = q * a ^ p := by
      calc a ^ p * q = (a ^ p * q * (a ^ p)⁻¹) * a ^ p := by group
        _ = q * a ^ p := by rw [hq]
    exact h2.symm
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (a ^ p)).2 hcenter

private theorem exists_fixed_element_aux5 {p : ℕ} {X J : Subgroup Ω} {x : Ω} {a : PQuot p X}
    (hJX : J ≤ X) (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxJ : x ∈ cs J)
    (hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ = MulAut.conj a) :
    ∀ j : ↥J, (QuotientGroup.mk' (Subgroup.center (PQuot p X)) a) * excJMap p hJX j =
      excJMap p hJX j * (QuotientGroup.mk' (Subgroup.center (PQuot p X)) a) := by
  intro j
  set b : PQuot p X := QuotientGroup.mk (Subgroup.inclusion hJX j) with hb
  have hcomm : a * b = b * a := by
    have hxJc : x * (j : Ω) * x⁻¹ = (j : Ω) := by
      rw [← Subgroup.mem_centralizer_iff.1 hxJ (j : Ω) j.2, mul_inv_cancel_right]
    have hb' : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ b = b := by
      change CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩
          (QuotientGroup.mk (Subgroup.inclusion hJX j)) = QuotientGroup.mk (Subgroup.inclusion hJX j)
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
      congr 1
      apply Subtype.ext
      rw [chev_coe_normalizerMonoidHom]
      simpa using hxJc
    have hconjb : MulAut.conj a b = b := by
      rw [← hbar]
      exact hb'
    rw [MulAut.conj_apply] at hconjb
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [hconjb]
  change (QuotientGroup.mk' (Subgroup.center (PQuot p X))) a *
      (QuotientGroup.mk' (Subgroup.center (PQuot p X))) b =
    (QuotientGroup.mk' (Subgroup.center (PQuot p X))) b *
      (QuotientGroup.mk' (Subgroup.center (PQuot p X))) a
  rw [← map_mul, hcomm, ← map_mul]

private theorem exists_fixed_element_aux6 {p : ℕ} {X : Subgroup Ω} {x : Ω} {a : PQuot p X}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hxN : x ∈ Subgroup.normalizer (X : Set Ω))
    (hxX : x ∉ cs X) (hOZ : GLAPPrimeCore p ↥X ≤ Subgroup.center ↥X)
    (hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ = MulAut.conj a) :
    (QuotientGroup.mk' (Subgroup.center (PQuot p X)) a) ≠ 1 := by
  intro hs1
  have haZ : a ∈ Subgroup.center (PQuot p X) :=
    (QuotientGroup.eq_one_iff a).1 hs1
  have hconj_a_one : MulAut.conj a = 1 := by
    ext q
    rw [MulAut.conj_apply, MulAut.one_apply]
    have h := Subgroup.mem_center_iff.1 haZ q
    rw [← h, mul_inv_cancel_right]
  have hbar1 : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ = 1 := by
    rw [hbar]
    exact hconj_a_one
  have hcm : x ∈ centModSubgroup p X :=
    (centMod_iff).1 ((chev_barAut_eq_one_iff_centMod hxN).1 hbar1)
  exact hxX (exists_fixed_element_aux3 hX hOZ hcm)

theorem exists_fixed_element {p : ℕ} {X J : Subgroup Ω} {x : Ω} (hp : p.Prime)
    (hX : CFSG.Open.IsQuasisimple ↥X) (hnt : Nontrivial (PSimple p X)) (hJX : J ≤ X)
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hxp : x ^ p = 1) (hxX : x ∉ cs X)
    (hxJ : x ∈ cs J) (hinner : InducesInnerMod p X x) :
    ∃ s : PSimple p X, s ≠ 1 ∧ s ^ p = 1 ∧ ∀ j : ↥J, s * excJMap p hJX j = excJMap p hJX j * s := by
  obtain ⟨l, hl, hlx⟩ := hinner
  have hOne : GLAPPrimeCore p ↥X ≠ ⊤ := exists_fixed_element_aux1 hnt
  have hOZ : GLAPPrimeCore p ↥X ≤ Subgroup.center ↥X :=
    le_center_of_normal_of_isQuasisimple hX (GLAPPrimeCore.normal p ↥X) hOne
  set a : PQuot p X := QuotientGroup.mk (⟨l, hl⟩ : ↥X) with ha
  have hbar : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p X ⟨x, hxN⟩ =
      MulAut.conj a := exists_fixed_element_aux2 hxN hl hlx
  set s : PSimple p X := QuotientGroup.mk' (Subgroup.center (PQuot p X)) a with hs
  have hsne : s ≠ 1 := by
    rw [hs]
    exact exists_fixed_element_aux6 hX hxN hxX hOZ hbar
  have hsp : s ^ p = 1 := by
    rw [hs]
    exact exists_fixed_element_aux4 hxN hxp hbar
  exact ⟨s, hsne, hsp, fun j => by
    rw [hs]
    exact exists_fixed_element_aux5 hJX hxN hxJ hbar j⟩

theorem ker_excJMap_le {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hZ : Subgroup.center (PQuot p J) = ⊥) : (excJMap p hJX).ker ≤ GLAPPrimeCore p ↥J := by
  letI : Fact p.Prime := ⟨hp⟩
  intro j hj
  rw [MonoidHom.mem_ker] at hj
  have hqX : (QuotientGroup.mk (Subgroup.inclusion hJX j) : PQuot p X) ∈
      Subgroup.center (PQuot p X) :=
    (QuotientGroup.eq_one_iff _).mp hj
  have hmemX : ∀ y : ↥J, Subgroup.inclusion hJX ⁅j, y⁆ ∈ GLAPPrimeCore p ↥X := by
    intro y
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X))
        (⁅Subgroup.inclusion hJX j, Subgroup.inclusion hJX y⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hqX _).symm
    have h2 : ⁅Subgroup.inclusion hJX j, Subgroup.inclusion hJX y⁆ ∈ GLAPPrimeCore p ↥X :=
      (QuotientGroup.eq_one_iff _).mp h1
    simpa only [map_commutatorElement] using h2
  have hKle : (GLAPPrimeCore p ↥X).comap (Subgroup.inclusion hJX) ≤ GLAPPrimeCore p ↥J := by
    change _ ≤ CFSG.pPrimeCore p ↥J
    exact le_sSup
      ⟨((GLAPPrimeCore.normal p ↥X).comap (Subgroup.inclusion hJX)),
        ((CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X)).coprime_dvd_right
          (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hJX)))⟩
  have hcenterJ : (QuotientGroup.mk j : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) g
    have h1 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥J)) ⁅j, y⁆ : PQuot p J) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hKle (by rw [Subgroup.mem_comap]; exact hmemX y))
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hzero : (QuotientGroup.mk j : PQuot p J) = 1 := by
    simpa [hZ] using hcenterJ
  exact (QuotientGroup.eq_one_iff j).mp hzero

private theorem exists_lift_elemAbelian_aux1 {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hZ : Subgroup.center (PQuot p J) = ⊥) {E : Subgroup (PSimple p J)} (hE : IsElemAbelian p E) :
    ∃ S : Subgroup ↥J, IsElemAbelian p S ∧ Nat.card S = Nat.card E ∧
      Disjoint S (GLAPPrimeCore p ↥J) := by
  letI : Fact p.Prime := ⟨hp⟩
  let e : PSimple p J ≃* PQuot p J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let E' : Subgroup (PQuot p J) := E.map e.toMonoidHom
  have hE' : IsElemAbelian p E' := IsElemAbelian.map hE e.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective e.injective
  have hNcop : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥J) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥J))
  obtain ⟨S, -, hSelem, hScard⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_lift (GLAPPrimeCore p ↥J) hNcop hE'
  refine ⟨S, hSelem, hScard.trans hcardE', ?_⟩
  have hSp : IsPGroup p ↥S := isPGroup_of_isElemAbelian hSelem
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hSp
  have hcop : Nat.Coprime (Nat.card S) (Nat.card (GLAPPrimeCore p ↥J)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hNcop)
  exact Subgroup.disjoint_of_coprime_natCard hcop

private theorem exists_lift_elemAbelian_aux2 {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hZ : Subgroup.center (PQuot p J) = ⊥) {S : Subgroup ↥J}
    (hdisj : Disjoint S (GLAPPrimeCore p ↥J)) :
    Nat.card (S.map (excJMap p hJX)) = Nat.card S := by
  letI : Fact p.Prime := ⟨hp⟩
  let φ : ↥S →* PSimple p X := (excJMap p hJX).comp S.subtype
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hker : (a.1)⁻¹ * b.1 ∈ (excJMap p hJX).ker := by
      rw [MonoidHom.mem_ker]
      have h1 : φ (a⁻¹ * b) = 1 := by
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      simpa [φ] using h1
    have hmem : (a.1)⁻¹ * b.1 ∈ S ⊓ (excJMap p hJX).ker :=
      ⟨S.mul_mem (S.inv_mem a.2) b.2, hker⟩
    have hbot : (a.1)⁻¹ * b.1 ∈ (⊥ : Subgroup ↥J) :=
      Disjoint.le_bot (Disjoint.mono_right (ker_excJMap_le hp hJX hZ) hdisj) hmem
    exact Subtype.ext (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot))
  have hrange : S.map (excJMap p hJX) = φ.range := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm

private theorem exists_lift_elemAbelian_aux3 {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hZ : Subgroup.center (PQuot p J) = ⊥) {S : Subgroup ↥J}
    (hdisj : Disjoint S (GLAPPrimeCore p ↥J)) :
    ∀ f ∈ S.map (excJMap p hJX),
      (∀ j : ↥J, f * excJMap p hJX j = excJMap p hJX j * f) → f = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rintro f hf hcomm
  rw [Subgroup.mem_map] at hf
  obtain ⟨x, hxS, rfl⟩ := hf
  have hxN : x ∈ GLAPPrimeCore p ↥J := by
    have hcentral : (QuotientGroup.mk x : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) g
      have hker : ⁅x, y⁆ ∈ (excJMap p hJX).ker := by
        rw [MonoidHom.mem_ker]
        have h1 : (excJMap p hJX) ⁅x, y⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm y)
        exact h1
      have h1 : ((QuotientGroup.mk' (GLAPPrimeCore p ↥J)) ⁅x, y⁆ : PQuot p J) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (ker_excJMap_le hp hJX hZ hker)
      rw [map_commutatorElement] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hzero : (QuotientGroup.mk x : PQuot p J) = 1 := by
      simpa [hZ] using hcentral
    exact (QuotientGroup.eq_one_iff x).mp hzero
  have hx1 : x = 1 :=
    Subgroup.mem_bot.mp (Disjoint.le_bot hdisj ⟨hxS, hxN⟩)
  rw [hx1, map_one]

theorem exists_lift_elemAbelian {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hZ : Subgroup.center (PQuot p J) = ⊥) {E : Subgroup (PSimple p J)} (hE : IsElemAbelian p E) :
    ∃ F₀ : Subgroup (PSimple p X), IsElemAbelian p F₀ ∧ Nat.card F₀ = Nat.card E ∧
      F₀ ≤ (excJMap p hJX).range ∧
      ∀ f ∈ F₀, (∀ j : ↥J, f * excJMap p hJX j = excJMap p hJX j * f) → f = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSelem, hScard, hdisj⟩ := exists_lift_elemAbelian_aux1 hp hJX hZ hE
  refine ⟨S.map (excJMap p hJX), IsElemAbelian.map hSelem (excJMap p hJX),
    (exists_lift_elemAbelian_aux2 hp hJX hZ hdisj).trans hScard, ?_,
    exists_lift_elemAbelian_aux3 hp hJX hZ hdisj⟩
  rintro x ⟨s, -, rfl⟩
  exact ⟨s, rfl⟩

theorem exists_elemAbelian_pumpup {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hZ : Subgroup.center (PQuot p J) = ⊥) {s : PSimple p X} (hs1 : s ≠ 1) (hsp : s ^ p = 1)
    (hsc : ∀ j : ↥J, s * excJMap p hJX j = excJMap p hJX j * s) {E : Subgroup (PSimple p J)}
    (hE : IsElemAbelian p E) :
    ∃ F : Subgroup (PSimple p X), IsElemAbelian p F ∧ Nat.card F = p * Nat.card E := by
  obtain ⟨F₀, hF₀, hcard, hrange, hfree⟩ := exists_lift_elemAbelian hp hJX hZ hE
  have hsF : s ∉ F₀ := fun h => hs1 (hfree s h hsc)
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p F₀ := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hF₀.2 g g.2⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hcomm : ∀ e ∈ F₀, e * s = s * e := by
    intro e he
    obtain ⟨j, rfl⟩ := hrange he
    exact (hsc j).symm
  obtain ⟨hab, hc⟩ := isElemAbelian_sup_zpowers_of_card hp hF₀ hk hsp hsF hcomm
  refine ⟨F₀ ⊔ Subgroup.zpowers s, hab, ?_⟩
  rw [hc, pow_succ, ← hk, hcard, mul_comm]

end CFSG.LocalAnalysis.GLTheoremA.I167

end
