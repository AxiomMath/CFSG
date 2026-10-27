module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426SporKleinU
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Spor
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card
public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import Certificates.Certificate10140
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426SporCore

public section

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426SporMathieu

theorem nonempty_quot_equiv_of_isogeny {Q T : Type} [Group Q] [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) (π : Q →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Q) : Nonempty (Q ⧸ Subgroup.center Q ≃* T) := by
  have hZ : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnc
  have hcen : Subgroup.center Q ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have : π z ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := hπ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz q]
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have heq : π.ker = Subgroup.center Q := le_antisymm hker hcen
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)⟩

theorem inner_of_outer {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hout : Nat.card (Outer S) ≤ 2) :
    ∀ α : MulAut S, α ^ 3 = 1 → ∃ x : S, α = MulAut.conj x := fun α hα => by
  obtain ⟨x, hx, -⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hZ hout α hα
  exact ⟨x, hx.symm⟩

theorem le_of_three_pow_dvd {k m n : ℕ} (hm : ¬ 3 ∣ m) (h : 3 ^ n ∣ 3 ^ k * m) : n ≤ k := by
  have h0 : 3 ^ k * m ≠ 0 := by
    have : m ≠ 0 := fun e => hm (e ▸ dvd_zero 3)
    positivity
  have := (Nat.prime_three.pow_dvd_iff_le_factorization h0).1 h
  rwa [CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul k hm] at this

theorem card_le_nine_M22 (H : Subgroup ↥NativeSporadic.M22)
    (hH : IsElemAbelian 3 H) : Nat.card H ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hH).exists_card_eq
  have hc : Nat.card ↥NativeSporadic.M22 = 3 ^ 2 * 49280 := CFSG.Sporadic.Mathieu.card_M22
  have hd : 3 ^ m ∣ 3 ^ 2 * 49280 := by
    rw [← hm, ← hc]; exact Subgroup.card_subgroup_dvd_card H
  have hm2 := le_of_three_pow_dvd (by norm_num) hd
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 9 := by norm_num

theorem card_le_nine_M12 (H : Subgroup ↥NativeSporadic.M12)
    (hH : IsElemAbelian 3 H) : Nat.card H ≤ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hH).exists_card_eq
  have hc : Nat.card (↥NativeSporadic.M12) = 3 ^ 3 * 3520 := CFSG.Sporadic.Mathieu.card_M12
  have hd : 3 ^ m ∣ 3 ^ 3 * 3520 := by
    rw [← hm, ← hc]; exact Subgroup.card_subgroup_dvd_card H
  have hm3 := le_of_three_pow_dvd (by norm_num) hd
  have hfac : (Nat.card (↥NativeSporadic.M12)).factorization 3 = 3 := by
    rw [hc, CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  rcases (show m ≤ 2 ∨ m = 3 by omega) with h2 | rfl
  · rw [hm]
    calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 9 := by norm_num
  · exfalso
    set P0 : Subgroup (↥NativeSporadic.M12) := CFSG.RankThree.PartTwo.Toolkit.M12.P0
    have hP0 : Nat.card P0 = 3 ^ (Nat.card (↥NativeSporadic.M12)).factorization 3 := by
      rw [hfac]; exact CFSG.RankThree.PartTwo.Toolkit.M12.card_P0
    have hH' : Nat.card H = 3 ^ (Nat.card (↥NativeSporadic.M12)).factorization 3 := by rw [hfac, hm]
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥NativeSporadic.M12) (Sylow.ofCard H hH')
      (Sylow.ofCard P0 hP0)
    have hmem : ∀ p ∈ P0, ∃ q ∈ H, g * q * g⁻¹ = p := by
      intro p hp
      have hp' : p ∈ ((g • Sylow.ofCard H hH' : Sylow 3 _) : Subgroup (↥NativeSporadic.M12)) := by
        rw [hg]; exact hp
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hp'
      obtain ⟨q, hq, hqp⟩ := hp'
      exact ⟨q, hq, by rw [← hqp, MulAut.smul_def, MulAut.conj_apply]⟩
    apply CFSG.RankThree.PartTwo.Toolkit.M12.not_comm_P0
    refine ⟨⟨fun a c => Subtype.ext ?_⟩⟩
    obtain ⟨q, hq, hqa⟩ := hmem a.1 a.2
    obtain ⟨r, hr, hrc⟩ := hmem c.1 c.2
    have hqr : q * r = r * q := congrArg Subtype.val (hH.1.is_comm.comm ⟨q, hq⟩ ⟨r, hr⟩)
    show (a : ↥NativeSporadic.M12) * (c : ↥NativeSporadic.M12) = (c : ↥NativeSporadic.M12) * a
    rw [← hqa, ← hrc]
    calc g * q * g⁻¹ * (g * r * g⁻¹) = g * (q * r) * g⁻¹ := by group
      _ = g * (r * q) * g⁻¹ := by rw [hqr]
      _ = g * r * g⁻¹ * (g * q * g⁻¹) := by group

theorem kleinData_M22 :
    ∃ x y t1 t2 : ↥NativeSporadic.M22, KD1426SporKlein.KleinData x y t1 t2 := by
  have h := Certificates.certificate10140
  unfold KD1426M22.m22KleinOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩ := h
  have hmem : ∀ w, CFSG.Sporadic.Schreier.evalCodes KD1426M22.m22S w ∈ NativeSporadic.M22 :=
    fun w => CFSG.Sporadic.Schreier.evalCodes_mem _ (fun g hg => by
      simp only [KD1426M22.m22S, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (CFSG.Sporadic.Mathieu.m22a).2
      · exact (CFSG.Sporadic.Mathieu.m22b).2) w
  set x := CFSG.Sporadic.Schreier.evalCodes KD1426M22.m22S KD1426M22.xW
  set y := CFSG.Sporadic.Schreier.evalCodes KD1426M22.m22S KD1426M22.yW
  set t1 := CFSG.Sporadic.Schreier.evalCodes KD1426M22.m22S KD1426M22.t1W
  set t2 := CFSG.Sporadic.Schreier.evalCodes KD1426M22.m22S KD1426M22.t2W
  set x' : ↥NativeSporadic.M22 := ⟨x, hmem _⟩
  set y' : ↥NativeSporadic.M22 := ⟨y, hmem _⟩
  set u1 : ↥NativeSporadic.M22 := ⟨t1, hmem _⟩
  set u2 : ↥NativeSporadic.M22 := ⟨t2, hmem _⟩
  have ne : ∀ {a c : ↥NativeSporadic.M22}, (a : Equiv.Perm (Fin 22)) ≠ c → a ≠ c :=
    fun h e => h (congrArg Subtype.val e)
  refine ⟨x', y', u1, u2, ⟨?_, ne h2, ?_, ne h4, ne h5, ne h6, Subtype.ext h7, ?_, ?_, ne h10,
    ne h11, ne h12, Subtype.ext h13, Subtype.ext h14, Subtype.ext h15, ?_, ?_⟩⟩
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h1)
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h8)
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h9)
  · exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; exact h16)
  · exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]; exact h17)

theorem concl_of_core {Y : Type} [Group Y] [Finite Y] {K B : Subgroup Y} {S : Type} [Group S]
    {s : TauCeti.SporadicName} (hs : s = .M12 ∨ s = .M22)
    (b : S ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h : Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
      Nonempty (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ≃* S) ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer
          ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
      T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ IsElemAbelian 2 T ∧
      Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥) :
    KD1426Concl K B := by
  obtain ⟨hBc, A, T, hAB, hAel, hAc, hcomp, ⟨eP⟩, hcent, hTle, hTel, hTc, hBn, hcomm, hcore⟩ := h
  exact ⟨hBc, A, T, hAB, hAel, hAc, hcomp, ⟨TauCeti.CFSGIndex.sporadic s, hs, ⟨eP.trans b⟩⟩,
    hcent, hTle, hTel, hTc, hBn, hcomm, hcore⟩

theorem kd1426SporS_of
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : SporadicOrdersTable)
    (hsimple : ∀ s : TauCeti.SporadicName, s ≠ .M → Finite (Carrier s) ∧ IsSimpleGroup (Carrier s)) :
    KD1426SporS := by
  intro s hs Y _ _ K B hKn hq hcat hcore hlev hB hKB hcard hmax hC hH hM
  obtain ⟨π, hπ, hker, -⟩ := hcat
  have hsM : s ≠ .M := by rcases hs with rfl | rfl <;> decide
  obtain ⟨hfin, hsimp⟩ := hsimple s hsM
  have b : Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group := (hbr s).some
  have hcS : Nat.card (Carrier s) = sporOrd s := (Nat.card_congr b.toEquiv).trans (hOrd s)
  have hnp : ¬ (Nat.card (Carrier s)).Prime := by
    rw [hcS]; rcases hs with rfl | rfl <;> (simp only [sporOrd]; norm_num)
  have hnc := CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_not_comm_of_simple_not_prime hnp
  have hZ : Subgroup.center (Carrier s) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnc
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := b.symm.isSimpleGroup
  have hncT : ∃ a c : (TauCeti.CFSGIndex.sporadic s).Group, a * c ≠ c * a := by
    obtain ⟨u1, u2, hu⟩ := hnc
    exact ⟨b u1, b u2, fun e => hu (b.injective (by rw [map_mul, map_mul, e]))⟩
  obtain ⟨eK⟩ := nonempty_quot_equiv_of_isogeny hncT π hπ hker
  have hout := hOut (Carrier s) hsimp hnc s ⟨b⟩
  have hInn := inner_of_outer hZ hout
  rcases hs with rfl | rfl
  ·
    set eK' : ↥K ⧸ Subgroup.center ↥K ≃* ↥NativeSporadic.M12 := eK.trans b.symm
    have hZ' : Subgroup.center ↥NativeSporadic.M12 = ⊥ := hZ
    have hInn' : ∀ α : MulAut ↥NativeSporadic.M12, α ^ 3 = 1 → ∃ x, α = MulAut.conj x := hInn
    refine concl_of_core (Or.inl rfl) b (KD1426SporCore.kd1426_core K B hKn hq eK' hInn' hZ'
      card_le_nine_M12 hcore hB hcard hH ?_)
    intro h9r
    set ψ := KD1426SporCore.psiB K hKn eK' hInn' hZ' B hB.2 with hψ
    set π' := KD1426SporCore.piK K eK' with hπ'
    obtain ⟨U, hUK, hU1, hU2, hBU⟩ := hM ⟨TauCeti.CFSGIndex.sporadic .M12, rfl, ⟨eK⟩⟩
    have hZp : IsPGroup 3 ↥(Subgroup.center ↥K) :=
      KD264Z.isPGroup_center_of_pPrimeCore Nat.prime_three hcore
    set Ub : Subgroup ↥NativeSporadic.M12 := (U.subgroupOf K).map π' with hUb
    refine KD1426SporKlein.klein_of_U ψ.range (KD1426Common.isElemAbelian_range hB ψ) h9r Ub ?_
      ?_ ?_ ?_
    ·
      intro hbot
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_bot]
      have huK := hUK hu
      have h1 : π' ⟨u, huK⟩ = 1 := by
        have : π' ⟨u, huK⟩ ∈ Ub := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hu)
        rwa [hbot, Subgroup.mem_bot] at this
      have hcen := (KD1426SporCore.piK_eq_one_iff K eK' _).1 h1
      obtain ⟨n2, hn2⟩ := hU2 ⟨u, hu⟩
      obtain ⟨n3, hn3⟩ := hZp ⟨⟨u, huK⟩, hcen⟩
      have e2 : u ^ 2 ^ n2 = 1 := by simpa using congrArg Subtype.val hn2
      have e3 : u ^ 3 ^ n3 = 1 := by
        have h' := congrArg (fun x : ↥(Subgroup.center ↥K) => ((x : ↥K) : Y)) hn3
        simpa using h'
      have hd : orderOf u ∣ Nat.gcd (2 ^ n2) (3 ^ n3) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e3)
      have hg : Nat.gcd (2 ^ n2) (3 ^ n3) = 1 := Nat.Coprime.pow _ _ (by norm_num)
      rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
      exact hd
    ·
      rintro ⟨y, hy⟩
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨n, hn⟩ := hU2 ⟨(u : Y), Subgroup.mem_subgroupOf.1 hu⟩
      refine ⟨n, Subtype.ext ?_⟩
      have hu1 : u ^ 2 ^ n = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← map_pow, hu1, map_one]
    ·
      intro d hd y hy
      obtain ⟨⟨bb, hbb⟩, rfl⟩ := MonoidHom.mem_range.1 hd
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
      have heq := KD1426SporCore.psiFun_equiv K hKn eK' hInn' bb (hB.2 bb hbb) u
      rw [hψ, KD1426SporCore.psiB_apply, ← heq]
      refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
      rw [KD264Inner.conjKequiv_apply]
      exact (Subgroup.mem_normalizer_iff.1 (hBU hbb) u).1 (Subgroup.mem_subgroupOf.1 hu)
    ·
      intro t ht1 ht2 hall
      have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
      have hct := CFSG.Sporadic.Schreier.card_centralizer_involution_of_mulEquiv_M12
        (Y := ↥NativeSporadic.M12) (MulEquiv.refl _) hto
      have hle : ψ.range ≤ Subgroup.centralizer ({t} : Set ↥NativeSporadic.M12) := fun d hd =>
        Subgroup.mem_centralizer_singleton_iff.2 (hall d hd)
      have h9 : 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set ↥NativeSporadic.M12)) := by
        rw [← h9r]; exact Subgroup.card_dvd_of_le hle
      rcases hct with h | h <;> rw [h] at h9 <;> norm_num at h9
  ·
    set eK' : ↥K ⧸ Subgroup.center ↥K ≃* ↥NativeSporadic.M22 := eK.trans b.symm
    have hZ' : Subgroup.center ↥NativeSporadic.M22 = ⊥ := hZ
    have hInn' : ∀ α : MulAut ↥NativeSporadic.M22, α ^ 3 = 1 → ∃ x, α = MulAut.conj x := hInn
    obtain ⟨x, y, t1, t2, hd⟩ := kleinData_M22
    have hfac : (Nat.card ↥NativeSporadic.M22).factorization 3 = 2 := by
      rw [CFSG.Sporadic.Mathieu.card_M22, show (443520 : ℕ) = 3 ^ 2 * 49280 by norm_num,
        CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
    exact concl_of_core (Or.inr rfl) b (KD1426SporCore.kd1426_core K B hKn hq eK' hInn' hZ'
      card_le_nine_M22 hcore hB hcard hH fun h9r => KD1426SporKlein.klein_of_sylow hfac hd _ h9r)

section Closed


theorem kd1426SporS_holds : KD1426SporS :=
  kd1426SporS_of CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group sporadicOrdersTable_holds
    CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M

end Closed

end CFSG.LocalAnalysis.GLTheoremA.KD1426SporMathieu
