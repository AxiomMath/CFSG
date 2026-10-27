module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Local
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26SCON
public import CFSG.HardMathSupport.Solomon.Coordinator.ONGroup
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.ON25Local
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import Certificates.Data.ExceptionalSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem exists_conj_of_pow_three {X : Type*} [Group X]
    (hidx : (MulAut.conj : X →* MulAut X).range.index ∣ 2) {x : MulAut X} (hx : x ^ 3 = 1) :
    ∃ g : X, MulAut.conj g = x := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
  · have : (MulAut.conj : X →* MulAut X).range = ⊤ := Subgroup.index_eq_one.1 h1
    have hx' : x ∈ (MulAut.conj : X →* MulAut X).range := this ▸ Subgroup.mem_top x
    obtain ⟨g, hg⟩ := hx'
    exact ⟨g, hg⟩
  · haveI : (MulAut.conj : X →* MulAut X).range.Normal := Subgroup.normal_of_index_eq_two h2
    have hx2 : x ^ 2 ∈ (MulAut.conj : X →* MulAut X).range := by
      have := Subgroup.pow_index_mem (MulAut.conj : X →* MulAut X).range x
      rwa [h2] at this
    have : x = (x ^ 2)⁻¹ := by
      have h3 : x ^ 2 * x = 1 := by rw [← pow_succ]; exact hx
      exact (eq_inv_of_mul_eq_one_right h3)
    have hx' : x ∈ (MulAut.conj : X →* MulAut X).range := by
      rw [this]; exact Subgroup.inv_mem _ hx2
    obtain ⟨g, hg⟩ := hx'
    exact ⟨g, hg⟩

section


theorem gfr2spor_exists_q {Y : Type} [Group Y] [Finite Y] (f : Y ≃* PON.Group) :
    ∃ q : GM →* Y, Function.Surjective q ∧ q.ker = zpowers zG := by
  let q : GM →* Y := f.symm.toMonoidHom.comp (piON.comp modelEquiv.symm.toMonoidHom)
  have hq : Function.Surjective q :=
    f.symm.surjective.comp (piON_surjective.comp modelEquiv.symm.surjective)
  have hkerq : q.ker = zpowers zG := by
    ext g
    rw [MonoidHom.mem_ker]
    show f.symm (piON (modelEquiv.symm g)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, ker_piON, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← modelEquiv_zF, ← map_zpow, hk, MulEquiv.apply_symm_apply]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk, ← modelEquiv_zF, ← map_zpow, MulEquiv.symm_apply_apply]
  exact ⟨q, hq, hkerq⟩

theorem onSimpleNoPumpup_of_inputs (hOut : ONOuterTwo) (hOG : UniquenessMaximal.InputONGroup) :
    ONSimpleNoPumpup := by
  intro Y _ _ hq hKg hcore hZ1 ⟨e⟩ x hxo J₁ hJ₁ hty
  have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  have hcardY : Nat.card Y = orderON := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    rw [hZ1, mul_one, Nat.card_congr e.toEquiv, hOG.2] at h1
    exact h1
  rcases gfr2_type_dvd hOG hty with ⟨-, hd⟩ | ⟨hSix, hd⟩
  · rw [hcardY] at hd
    have := Nat.le_of_dvd (by unfold orderON; norm_num) hd
    unfold orderON at this
    omega
  · have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    obtain ⟨g, hg⟩ := exists_conj_of_pow_three (hOut Y hq.1 ⟨e⟩) hx3
    have hg3 : g ^ 3 = 1 := by
      have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg, hx3]
      have h2 := CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof.conj_eq_one_iff.1 h1
      rwa [hbot, Subgroup.mem_bot] at h2
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one] at hg
      rw [← hg, orderOf_one] at hxo
      omega
    obtain ⟨b0⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
        (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b0
    have f : Y ≃* PON.Group :=
      ((((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans
        (e.trans b'.symm)).trans nonempty_equiv_PON.some)
    obtain ⟨q, hqs, hker⟩ := gfr2spor_exists_q f
    obtain ⟨a, ha⟩ := hqs g
    have ha3 : a ^ 3 = 1 := by
      have h1 : q (a ^ 3) = 1 := by rw [map_pow, ha, hg3]
      have h2 : a ^ 3 ∈ zpowers zG := by rw [← hker]; exact h1
      have h3 : (a ^ 3) ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h2
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        have : zG ^ ((3 : ℕ) : ℤ) = 1 := by
          rw [zpow_natCast]
          exact relG.xcube
        rw [this, one_zpow]
      refine CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one (MulEquiv.refl GM) (k := 2) ?_
      rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h3
    have haz : a ∉ zpowers zG := by
      intro h
      apply hg1
      rw [← ha]
      have : a ∈ q.ker := by rw [hker]; exact h
      exact this
    obtain ⟨n, hC, -⟩ := gfr1_exists_conj ha3 haz
    set K : Subgroup GM := K0G.map (MulAut.conj n).toMonoidHom with hK
    have hKC : K ≤ centralizer ({a} : Set GM) := by rw [hC]; exact le_sup_right
    have hKa : ∀ k ∈ K, a * k = k * a := fun k hk =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)).symm
    have hcommK : ⁅centralizer ({a} : Set GM), centralizer ({a} : Set GM)⁆ ≤ K := by
      rw [hC]; exact gfr1_commutator_le hKa
    set Jh : Subgroup GM := J₁.comap q with hJh
    have hzc : ∀ w ∈ q.ker, w ∈ Subgroup.center GM := by
      intro w hw
      rw [hker, ← center_GM] at hw
      exact hw
    have hJc : ∀ m ∈ Jh, ∃ c ∈ Subgroup.center GM, a * m * a⁻¹ = c * m := by
      intro m hm
      have hmJ : q m ∈ J₁ := hm
      have hfix : x (q m) = q m := hJ₁.1 hmJ
      rw [← hg, MulAut.conj_apply, ← ha] at hfix
      refine ⟨a * m * a⁻¹ * m⁻¹, hzc _ ?_, by group⟩
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hfix]
      group
    have hH : ⁅Jh, Jh⁆ ≤ centralizer ({a} : Set GM) := by
      refine Subgroup.commutator_le.2 fun m₁ h₁ m₂ h₂ => ?_
      obtain ⟨c₁, hc₁, e₁⟩ := hJc m₁ h₁
      obtain ⟨c₂, hc₂, e₂⟩ := hJc m₂ h₂
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hφ : a * ⁅m₁, m₂⁆ * a⁻¹ = ⁅m₁, m₂⁆ := by
        have h := map_commutatorElement (MulAut.conj a) m₁ m₂
        simp only [MulAut.conj_apply] at h
        rw [h, e₁, e₂, show c₁ * m₁ = m₁ * c₁ from (Subgroup.mem_center_iff.1 hc₁ m₁).symm,
          show c₂ * m₂ = m₂ * c₂ from (Subgroup.mem_center_iff.1 hc₂ m₂).symm]
        exact commutatorElement_mul_mul'
          (Commute.symm (Subgroup.mem_center_iff.1 hc₁ m₂))
          (Commute.symm (Subgroup.mem_center_iff.1 hc₁ c₂))
          (Commute.symm (Subgroup.mem_center_iff.1 hc₂ m₁))
      calc ⁅m₁, m₂⁆ * a = (a * ⁅m₁, m₂⁆ * a⁻¹) * a := by rw [hφ]
        _ = a * ⁅m₁, m₂⁆ := by group
    have hmapJ : Jh.map q = J₁ := Subgroup.map_comap_eq_self_of_surjective hqs J₁
    have hperf : ⁅J₁, J₁⁆ = J₁ := glaPComponent_perfect hJ₁
    have hq1 : (⁅Jh, Jh⁆).map q = J₁ := by
      rw [Subgroup.map_commutator, hmapJ, hperf]
    have hq2 : (⁅⁅Jh, Jh⁆, ⁅Jh, Jh⁆⁆).map q = J₁ := by
      rw [Subgroup.map_commutator, hq1, hperf]
    have hle : ⁅⁅Jh, Jh⁆, ⁅Jh, Jh⁆⁆ ≤ K :=
      (Subgroup.commutator_mono hH hH).trans hcommK
    have hJK : J₁ ≤ K.map q := hq2 ▸ Subgroup.map_mono hle
    let φ : ↥K →* Y := q.comp K.subtype
    have hφr : φ.range = K.map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkr := Subgroup.card_ker_mul_card_range φ
    rw [hφr, on25_card_K n] at hkr
    have hzK : (⟨zG, on25_z_mem_K n⟩ : ↥K) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      show q zG = 1
      have : zG ∈ q.ker := by rw [hker]; exact mem_zpowers zG
      exact this
    have h3 : 3 ≤ Nat.card φ.ker := by
      have hle : zpowers (⟨zG, on25_z_mem_K n⟩ : ↥K) ≤ φ.ker := zpowers_le.2 hzK
      have h := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, ← Subgroup.orderOf_coe] at h
      have h' : orderOf zG = 3 := orderOf_eq_prime relG.xcube relG.x1
      exact h' ▸ h
    have hpos : 0 < Nat.card (K.map q) := Nat.card_pos
    have hc360 : Nat.card (K.map q) ≤ 360 := by nlinarith
    have hdJ : Nat.card J₁ ∣ Nat.card (K.map q) := Subgroup.card_dvd_of_le hJK
    have hJle : Nat.card J₁ ≤ 360 := (Nat.le_of_dvd hpos hdJ).trans hc360
    have hbar : Nat.card (barOf 3 J₁) ∣ Nat.card J₁ := Subgroup.card_quotient_dvd_card _
    rw [gfr2_card_isHatSix hSix] at hbar
    have := Nat.le_of_dvd Nat.card_pos hbar
    omega

theorem onSimpleNoPumpup_holds :
    ONSimpleNoPumpup :=
  onSimpleNoPumpup_of_inputs onOuterTwo_holds inputONGroup_holds

end

end CFSG.HardMathSupport.Solomon.Coordinator
