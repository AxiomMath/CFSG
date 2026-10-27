module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped MatrixGroups

namespace Lemma123

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}

theorem exists_le_isElemAbelian_card_pow {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] {D : Subgroup X}
    (hD : IsElemAbelian p D) {k k' : ℕ} (hk : k' ≤ k) (hcard : Nat.card D = p ^ k) :
    ∃ D' ≤ D, IsElemAbelian p D' ∧ Nat.card D' = p ^ k' := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) p (n := k')
    (hcard ▸ Nat.pow_dvd_pow p hk)
  refine ⟨K.map D.subtype, Subgroup.map_subtype_le _, CFSG.Open.IsElemAbelian.mono hD
    (Subgroup.map_subtype_le _), ?_⟩
  rw [Subgroup.card_map_of_injective D.subtype_injective, hK]

theorem isLocallyOTwoBalanced_of_le {p k k' : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkk : k ≤ k')
    {K : Type*} [Group K] {A : Subgroup (MulAut K)} (h : IsLocallyOTwoBalanced p k A) :
    IsLocallyOTwoBalanced p k' A := by
  intro D hD H hH hN
  obtain ⟨hDA, hDel, hDcard⟩ := hD
  obtain ⟨D', hD'D, hD'el, hD'card⟩ := exists_le_isElemAbelian_card_pow hp hDel hkk hDcard
  have h0 := h D' ⟨hD'D.trans hDA, hD'el, hD'card⟩ H hH (hD'D.trans hN)
  exact le_bot_iff.1 ((localDeltaTwoIn_anti hD'D).trans h0.le)

theorem not_isLocallyOTwoBalanced_two {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) {D B' L : Subgroup G}
    (hDB : D ≤ B') (h : ¬ IsCompLocallyOTwoBalanced p r D L) :
    ¬ IsLocallyOTwoBalanced p 2 (autBar p B' L) := by
  intro h2
  apply h
  exact isLocallyOTwoBalanced_mono (autBar_mono hDB) (isLocallyOTwoBalanced_of_le hp (by norm_num) hr h2)

@[expose] def Input19_17_2 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (s : TauCeti.SporadicName) (Y : Type) [Group Y] [Finite Y],
    CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ → IsSporType s (Y ⧸ Subgroup.center Y) →
    (¬ IsLocallyOTwoBalancedWrtP p 2 Y ∨ ¬ IsWeaklyLocallyOTwoBalancedWrtP p 1 Y) →
      (p = 5 ∧ s = TauCeti.SporadicName.Fi22) ∨
        (p = 3 ∧ (s = TauCeti.SporadicName.M12 ∨ s = TauCeti.SporadicName.M22 ∨ s = TauCeti.SporadicName.J2))

@[expose] def Input23_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G) (s : TauCeti.SporadicName),
    GLAPComponent 3 X K → B ≤ X → IsElemAbelian 3 B → B ≤ Subgroup.normalizer (K : Set G) →
    (∀ x ∈ B, x ∈ centBar 3 ⊤ K → x = 1) → 2 ≤ CFSG.Open.pRank 3 B →
    (s = TauCeti.SporadicName.M12 ∨ s = TauCeti.SporadicName.M22 ∨ s = TauCeti.SporadicName.J2) →
    IsSporType s (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) →
    (¬ IsLocallyOTwoBalanced 3 2 (autBar 3 B K) ∨ ¬ IsWeaklyLocallyOTwoBalanced 3 1 (autBar 3 B K)) →
      barX 3 X K ≤ barX 3 X (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
        GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set G)))

@[expose] def InputSchurFi22 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 5 Y = ⊥ →
    IsSporType TauCeti.SporadicName.Fi22 (Y ⧸ Subgroup.center Y) → Subgroup.center Y = ⊥

theorem case_spor (h112 : Prop112Statement) (h117 : Prop117_cex_falseStatement)
    (hI191img : Input19_1_O2_img) (h122 : Lemma122_i_iiStatement)
    (hI1917 : Input19_17_2) (hI2324 : Input23_24) (hSchur : InputSchurFi22)
    {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r) {s : TauCeti.SporadicName}
    (hs : IsSporType s (barOf p K ⧸ Subgroup.center (barOf p K))) : False := by
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have ha : a ∈ A := P.cex.ha.1
  have ha1 : a ≠ 1 := P.cex.ha.2
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := lemma122_ii_of_cex P.cex
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hK
  have hcore : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBel : IsElemAbelian p (autBar p (E ⊓ A) K) := isElemAbelian_autBar (isElemAbelian_inter hSec)
  have hunbal : ¬ IsLocallyOTwoBalanced p 2 (autBar p (E ⊓ A) K) ∨
      ¬ IsWeaklyLocallyOTwoBalanced p 1 (autBar p (E ⊓ A) K) := by
    by_cases hr1 : r = 1
    · exact Or.inr (weak_nonbal hI191img h122 P hr1)
    · exact Or.inl (not_isLocallyOTwoBalanced_two hp (by have := P.hr; omega) P.hDA P.hbal)
  have hunbalP : ¬ IsLocallyOTwoBalancedWrtP p 2 (barOf p K) ∨
      ¬ IsWeaklyLocallyOTwoBalancedWrtP p 1 (barOf p K) := by
    rcases hunbal with h | h
    · exact Or.inl fun hb => h (hb _ hBel)
    · exact Or.inr fun hb => h (hb _ hBel)
  rcases hI1917 p hp hp2 s (barOf p K) hq hcore hs hunbalP with ⟨hp5, rfl⟩ | ⟨hp3, hs3⟩
  ·
    subst hp5
    have hz : Subgroup.center (barOf 5 K) = ⊥ := hSchur (barOf 5 K) hq hcore hs
    have hSp : IsSporType TauCeti.SporadicName.Fi22 (barOf 5 K) :=
      l119_isSporType_congr _ (Prop1116Design.mulEquivQuotCenterOfEqBot hz).symm hs
    rcases prop117_of_cex_false h117 hSec ha ha1 P.hK (Or.inr (Or.inl ⟨rfl, hSp⟩)) with hKM | hD
    · exact P.hKM hKM
    · exact hnotD hD
  ·
    subst hp3
    have hgen := hI2324 G (Cg a) K (E ⊓ A) s P.hK (inter_le_cg P.cex) (isElemAbelian_inter hSec)
      P.hA0norm P.hA0faith hSec.pair.1.2.2 hs3 hs hunbal
    have hle : barX 3 (Cg a) K ≤ barX 3 (Cg a) M :=
      hgen.trans (barX_mono 3 (iSup_le_of_cov1 hp h112 hSec ha ha1 hnotD P.hK))
    exact P.hKM (le_M_of_barX_le P.hK.1 hle ((prop111_of_prop112 h112) hSec ha ha1))

@[expose] def Input19_20_1 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsChevSimple 2 (Y ⧸ Subgroup.center Y) → ∀ R : Subgroup (MulAut Y), IsPGroup p ↥R →
      pCoreOf 2 (innerAut Y ⊓ Subgroup.centralizer (R : Set (MulAut Y))) = ⊥

@[expose] def Input7_12_2 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsChevSimple 2 (Y ⧸ Subgroup.center Y) → ∀ W B' : Subgroup (MulAut Y), IsPGroup 2 ↥W → IsPGroup p ↥B' →
      B' ≤ Subgroup.normalizer (W : Set (MulAut Y)) → ⁅W, B'⁆ ≤ innerAut Y

theorem mem_normalizer_inf' {Y : Type*} [Group Y] {A B : Subgroup Y} {k : Y}
    (hA : k ∈ Subgroup.normalizer (A : Set Y)) (hB : k ∈ Subgroup.normalizer (B : Set Y)) :
    k ∈ Subgroup.normalizer ((A ⊓ B : Subgroup Y) : Set Y) := by
  refine Subgroup.mem_normalizer_iff.2 fun x => ?_
  exact and_congr (Subgroup.mem_normalizer_iff.1 hA x) (Subgroup.mem_normalizer_iff.1 hB x)

theorem mem_normalizer_localDeltaTwoIn {Y : Type*} [Group Y] {H D : Subgroup Y} {x : Y}
    (hxH : x ∈ Subgroup.normalizer (H : Set Y)) (hxD : ∀ d ∈ D, x * d = d * x) :
    x ∈ Subgroup.normalizer ((localDeltaTwoIn H D : Subgroup Y) : Set Y) := by
  have key : ∀ x : Y, x ∈ Subgroup.normalizer (H : Set Y) → (∀ d ∈ D, x * d = d * x) →
      ∀ y ∈ localDeltaTwoIn H D, x * y * x⁻¹ ∈ localDeltaTwoIn H D := by
    intro x hxH hxD y hy
    unfold localDeltaTwoIn at hy ⊢
    simp only [Subgroup.mem_iInf] at hy ⊢
    intro d hd hd1
    have hyd := hy d hd hd1
    have hxC : x ∈ Subgroup.centralizer ({d} : Set Y) :=
      Subgroup.mem_centralizer_iff.2 fun z hz => by
        obtain rfl := Set.mem_singleton_iff.1 hz
        exact (hxD z hd).symm
    have hxd : x ∈ Subgroup.normalizer ((H ⊓ Subgroup.centralizer ({d} : Set Y) : Subgroup Y) : Set Y) :=
      mem_normalizer_inf' hxH (Subgroup.le_normalizer hxC)
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxd) y).1 hyd
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hxH hxD y, fun hy => ?_⟩
  have hxH' := (Subgroup.normalizer (H : Set Y)).inv_mem hxH
  have hxD' : ∀ d ∈ D, x⁻¹ * d = d * x⁻¹ := fun d hd => (Commute.inv_left (hxD d hd)).eq
  have := key x⁻¹ hxH' hxD' _ hy
  simpa [mul_assoc] using this

theorem chev2_weak (hI1920 : Input19_20_1) (hI712 : Input7_12_2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hY : IsChevSimple 2 (Y ⧸ Subgroup.center Y)) : IsWeaklyLocallyOTwoBalancedWrtP p 1 Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro A hA D hD H hH hAH
  obtain ⟨hDA, hDel, hDcard⟩ := hD
  have hnt : D ≠ ⊥ := by
    intro hD0
    rw [hD0, Subgroup.card_bot] at hDcard
    have : 1 < p ^ 1 := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hnt
  have hdD : (d : MulAut Y) ∈ D := d.2
  have hdp : (d : MulAut Y) ^ p = 1 := hDel.2 d hdD
  have hd1' : (d : MulAut Y) ≠ 1 := fun e => hd1 (Subtype.ext e)
  set Δ : Subgroup (MulAut Y) := localDeltaTwoIn H D with hΔ
  set Q : Subgroup (MulAut Y) :=
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({(d : MulAut Y)} : Set (MulAut Y))) with hQ
  have hΔQ : Δ ≤ Q := (iInf_le _ (d : MulAut Y)).trans ((iInf_le _ hdD).trans (iInf_le _ hd1'))
  have hΔ2 : IsPGroup 2 ↥Δ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hΔQ
  have hAN : A ≤ Subgroup.normalizer (Δ : Set (MulAut Y)) := fun x hx =>
    mem_normalizer_localDeltaTwoIn (hAH hx) fun e he => CFSG.Open.IsElemAbelian.comm hA hx (hDA he)
  have h1 : ⁅Δ, A⁆ ≤ innerAut Y :=
    hI712 p hp hp2 Y hq hY Δ A hΔ2 (CFSG.Open.IsElemAbelian.isPGroup hA) hAN
  have h2 : ⁅Δ, A⁆ ≤ Δ := by
    refine Subgroup.commutator_le.2 fun x hx a ha => ?_
    have h3 := (Subgroup.mem_normalizer_iff.1 (hAN ha) x⁻¹).1 (Δ.inv_mem hx)
    simpa [commutatorElement_def, mul_assoc] using Δ.mul_mem hx h3
  have hRp : IsPGroup p ↥(Subgroup.zpowers (d : MulAut Y)) := l119_isPGroup_zpowers hdp
  have h20 := hI1920 p hp hp2 Y hq hY _ hRp
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h20
  have hQI : Q ⊓ innerAut Y ≤ pCoreOf 2 (innerAut Y ⊓ Subgroup.centralizer ({(d : MulAut Y)} : Set (MulAut Y))) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact le_inf inf_le_right
        ((inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans inf_le_right)
    · intro x hx
      have hxH : x ∈ H ⊓ Subgroup.centralizer ({(d : MulAut Y)} : Set (MulAut Y)) :=
        Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
      exact mem_normalizer_inf'
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hxH))
        (Subgroup.le_normalizer (Subgroup.mem_inf.1 hx).1)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  rw [h20] at hQI
  refine eq_bot_iff.2 fun x hx => ?_
  exact hQI (Subgroup.mem_inf.2 ⟨hΔQ (h2 hx), h1 hx⟩)

theorem exists_barAut_ne_one {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r) :
    ∃ t ∈ TD p M a D, ∃ hN : t ∈ Subgroup.normalizer (K : Set G), barAut p K ⟨t, hN⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hp : p.Prime := P.cex.standing.prime
  apply P.hTDK
  refine Subgroup.commutator_le.2 fun k hk t ht => ?_
  have hb := hcon t ht (P.hTDnorm ht)
  have hkinv : k⁻¹ ∈ K := K.inv_mem hk
  have hq : (barAut p K ⟨t, P.hTDnorm ht⟩) (QuotientGroup.mk (⟨k⁻¹, hkinv⟩ : ↥K)) =
      QuotientGroup.mk (⟨k⁻¹, hkinv⟩ : ↥K) := by
    rw [hb]; rfl
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hq
  have hmem := QuotientGroup.eq.1 hq
  have hzval : ((((K.normalizerMonoidHom ⟨t, P.hTDnorm ht⟩ ⟨k⁻¹, hkinv⟩)⁻¹ * ⟨k⁻¹, hkinv⟩ : ↥K)) : G) =
      t * k * t⁻¹ * k⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨t, P.hTDnorm ht⟩ ⟨k⁻¹, hkinv⟩]
    simp [mul_assoc]
  have hmemG : t * k * t⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf p K := Subgroup.mem_map.2 ⟨_, hmem, hzval⟩
  have hmemG' : (t * k * t⁻¹ * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p (Cg a) :=
    (GLAPPrimeCoreOf p (Cg a)).inv_mem (glaPPrimeCoreOf_le_of_isSubnormal hp P.hK.2.1 hmemG)
  simpa [commutatorElement_def, mul_assoc] using hmemG'

theorem barAut_of_mem {p : ℕ} {L : Subgroup G} {l : G} (hl : l ∈ L)
    (hlN : l ∈ Subgroup.normalizer (L : Set G)) :
    barAut p L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : barOf p L) := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk]
    show (QuotientGroup.mk (L.normalizerMonoidHom ⟨l, hlN⟩ x) : barOf p L) = _
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem inducesInner_of_autBar_le_innerAut {p : ℕ} {B' K : Subgroup G}
    (hBN : B' ≤ Subgroup.normalizer (K : Set G)) (h : autBar p B' K ≤ innerAut (barOf p K)) :
    ∀ x ∈ B', InducesInner p K x := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBN hx
  have hmem : barAut p K ⟨x, hxN⟩ ∈ autBar p B' K :=
    ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx, hxN⟩), rfl⟩
  obtain ⟨κ, hκ⟩ := h hmem
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective κ
  have hkN : (k' : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k'.2
  refine ⟨k', k'.2, mem_centBar_iff.2 ⟨Subgroup.mem_top _, ?_, ?_⟩⟩
  · exact (Subgroup.normalizer (K : Set G)).mul_mem ((Subgroup.normalizer (K : Set G)).inv_mem hkN) hxN
  · have e : (⟨(k' : G)⁻¹ * x, (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).inv_mem hkN) hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        (⟨(k' : G), hkN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ * ⟨x, hxN⟩ := rfl
    rw [e, map_mul, map_inv, ← hκ, barAut_of_mem k'.2 hkN]
    exact inv_mul_cancel _

theorem eq_of_mem_zpowers_of_orderOf_two {Y : Type*} [Group Y] {u g : Y} (hu : orderOf u = 2)
    (hg : g ∈ Subgroup.zpowers u) (hne : g ≠ 1) : g = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h2 : u ^ k = u ^ (k % 2) := by
    have := zpow_mod_orderOf u k
    rw [hu] at this
    exact_mod_cast this.symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h2, h] at hne
    simp at hne
  · rw [h2, h]
    simp

@[expose] def Input19_16_two : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → IsChevSimple 2 (Y ⧸ Subgroup.center Y) →
    ∀ (k : ℕ) (B' : Subgroup (MulAut Y)), 2 ≤ k → IsElemAbelian p B' → Nat.card B' = p ^ k →
      ¬ IsLocallyOTwoBalanced p k B' →
        p = 3 ∧ IsLThreeFour (Y ⧸ Subgroup.center Y) ∧ k = 2 ∧ B' ≤ innerAut Y ∧
        ∀ H : Subgroup (MulAut Y), innerAut Y ≤ H → localDeltaTwoIn H B' ≠ ⊥ →
          ∃ u : MulAut Y, IsUnitaryAut u ∧ localDeltaTwoIn H B' = Subgroup.zpowers u

theorem case_chev2_one (hI191img : Input19_1_O2_img) (h122 : Lemma122_i_iiStatement)
    (hI1920 : Input19_20_1) (hI712 : Input7_12_2) {K D : Subgroup G} {r : ℕ}
    (P : Prep123 G m p B M E A a K D r) (hr1 : r = 1)
    (hchev : IsChevSimple 2 (barOf p K ⧸ Subgroup.center (barOf p K))) : False := by
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hK
  have hBel : IsElemAbelian p (autBar p (E ⊓ A) K) := isElemAbelian_autBar (isElemAbelian_inter hSec)
  exact weak_nonbal hI191img h122 P hr1 (chev2_weak hI1920 hI712 hp hp2 hq hchev _ hBel)

theorem case_chev2_ge2 (h122 : Lemma122_i_iiStatement) (hI191img : Input19_1_O2_img)
    (hI1916 : Input19_16_two) (hI7L : Input7_L34)
    {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r) (hr : 2 ≤ r)
    (hchev : IsChevSimple 2 (barOf p K ⧸ Subgroup.center (barOf p K))) :
    p = 3 ∧ IsLThreeFour (barOf p K ⧸ Subgroup.center (barOf p K)) ∧
      Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner p (E ⊓ A) K ∧
      ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
        ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut p K ⟨u, hu⟩) := by
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := P.cex.standing.simple
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hK
  have hcore : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hDel : IsElemAbelian p D := CFSG.Open.IsElemAbelian.mono (isElemAbelian_inter hSec) P.hDA
  have hXtop : Cg a ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top P.cex.standing.nonabelian P.cex.ha.2
  have hDX : IsEkIn p r (Cg a) D := ⟨P.hDA.trans (inter_le_cg P.cex), hDel, P.hDcard⟩
  have hDt : IsEkIn p r ⊤ (autBar p D K) := Lemma136c.l136c_isEkIn_autBar hDX P.hDnorm P.hDfaith
  obtain ⟨hp3, hL34, hr2, hDinn, hunit⟩ :=
    hI1916 p hp hp2 (barOf p K) hq hcore hchev r (autBar p D K) hr hDt.2.1 hDt.2.2 P.hbal
  have hTDle : TD p M a D ≤ localDeltaTwoIn (Cg a) D := TD_le_delta h122 P.cex P.hDA
  have hKΔ : ¬ ⁅K, localDeltaTwoIn (Cg a) D⁆ ≤ GLAPPrimeCoreOf p (Cg a) :=
    fun hΔ => P.hTDK (le_trans (Subgroup.commutator_mono le_rfl hTDle) hΔ)
  have himg := hI191img G P.cex.standing.kProper p hp hp2 r P.hr (Cg a) D hXtop hDX K P.hK hKΔ
  obtain ⟨t, ht, htN, htne⟩ := exists_barAut_ne_one P
  have htΔ : barAut p K ⟨t, htN⟩ ∈ DeltaImage p (Cg a) D K :=
    ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 (hTDle ht), rfl⟩
  have hne : localDeltaTwoIn (innerAut (barOf p K) ⊔ DeltaImage p (Cg a) D K) (autBar p D K) ≠ ⊥ := by
    intro h0
    have := himg htΔ
    rw [h0] at this
    exact htne (Subgroup.mem_bot.1 this)
  obtain ⟨u, hu, hΔu⟩ := hunit _ le_sup_left hne
  have htu : barAut p K ⟨t, htN⟩ = u :=
    eq_of_mem_zpowers_of_orderOf_two hu.1 (hΔu ▸ himg htΔ) htne
  subst hp3
  have hA0el : IsElemAbelian 3 (E ⊓ A) := isElemAbelian_inter hSec
  have hcardA : Nat.card (E ⊓ A : Subgroup G) = 3 ^ CFSG.Open.pRank 3 (E ⊓ A) := card_eq_pow_pRank hp hA0el
  have hA0X : IsEkIn 3 (CFSG.Open.pRank 3 (E ⊓ A)) (Cg a) (E ⊓ A) :=
    ⟨inter_le_cg P.cex, hA0el, hcardA⟩
  have hA0t : IsEkIn 3 (CFSG.Open.pRank 3 (E ⊓ A)) ⊤ (autBar 3 (E ⊓ A) K) :=
    Lemma136c.l136c_isEkIn_autBar hA0X P.hA0norm (by
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨hxA, hxN, hxb⟩ := mem_centBar_iff.1 hx
      exact Subgroup.mem_bot.2 (P.hA0faith x hxA (mem_centBar_iff.2 ⟨Subgroup.mem_top _, hxN, hxb⟩)))
  have hrk : CFSG.Open.pRank 3 (E ⊓ A) ≤ 2 := by
    have h1 := hI7L (barOf 3 K) hq hL34 hcore (autBar 3 (E ⊓ A) K) (isElemAbelian_autBar hA0el)
    have h2 : CFSG.Open.pRank 3 (E ⊓ A) ≤ CFSG.Open.pRank 3 (autBar 3 (E ⊓ A) K) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hA0t.2.1 hA0t.2.2
    exact h2.trans h1
  have hcard9 : Nat.card (E ⊓ A : Subgroup G) = 9 := by
    have h1 : 3 ^ 2 ≤ Nat.card (E ⊓ A : Subgroup G) := sq_le_card_inter hSec
    have h2 : Nat.card (E ⊓ A : Subgroup G) ≤ 3 ^ 2 := by
      rw [hcardA]; exact Nat.pow_le_pow_right (by norm_num) hrk
    omega
  have hDeq : D = E ⊓ A := by
    refine Subgroup.eq_of_le_of_card_ge P.hDA ?_
    rw [hcard9, P.hDcard, hr2]
    norm_num
  subst hDeq
  refine ⟨rfl, hL34, hcard9, ⟨P.hA0norm, P.hA0faith, inducesInner_of_autBar_le_innerAut P.hA0norm hDinn⟩,
    t, ht, htN, ?_⟩
  rw [htu]
  exact hu

@[expose] def Input19_7_3 : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → ∀ (Y : Type) [Group Y] [Finite Y],
    CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ → IsChevSimple q (Y ⧸ Subgroup.center Y) →
    ∀ (k : ℕ) (B' : Subgroup (MulAut Y)), 2 ≤ k → IsElemAbelian p B' → Nat.card B' = p ^ k →
      ¬ IsLocallyOTwoBalanced p k B' →
        k = 2 ∧ ∃ n : ℕ,
          (IsLpType p (q ^ n) (Y ⧸ Subgroup.center Y) ∧ p ∣ q ^ n - 1 ∧ Prop1116Design.HeisenbergImageL p (q ^ n) B') ∨
          (IsUpType p (q ^ n) (Y ⧸ Subgroup.center Y) ∧ p ∣ q ^ n + 1 ∧ Prop1116Design.HeisenbergImageU p (q ^ n) B')

@[expose] def Input19_18 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 13 Y = ⊥ →
    (Prop1116Design.IsLieOverField 3 Y ∨ IsLpType 3 (3 ^ 13) Y) →
      IsWeaklyLocallyOTwoBalancedWrtP 13 1 Y

@[expose] def Input27_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p q n : ℕ) (X K B W : Subgroup G),
    p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → GLAPComponent p X K → B ≤ X → IsElemAbelian p B →
    Nat.card B = p ^ 2 → B ≤ Subgroup.normalizer (K : Set G) → (∀ x ∈ B, x ∈ centBar p ⊤ K → x = 1) →
    ((IsLpType p (q ^ n) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ q ^ n - 1 ∧
        Prop1116Design.HeisenbergImageL p (q ^ n) (autBar p B K)) ∨
      (IsUpType p (q ^ n) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ q ^ n + 1 ∧
        Prop1116Design.HeisenbergImageU p (q ^ n) (autBar p B K))) →
    IsPGroup 2 ↥W → ∀ (hWK : W ≤ Subgroup.normalizer (K : Set G)), B ≤ Subgroup.normalizer (W : Set G) →
    (∀ b ∈ B, b ≠ 1 → GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (W : Set G)) →
    ∀ (w : G) (hw : w ∈ W), barAut p K ⟨w, hWK hw⟩ = 1

theorem case_chev_odd (h112 : Prop112Statement) (h1116 : Prop1116StrongStatement)
    (hI191img : Input19_1_O2_img) (h122 : Lemma122_i_iiStatement) (hI1918 : Input19_18)
    (hI197 : Input19_7_3) (hI272 : Input27_2)
    {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hchev : IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K))) : False := by
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := P.cex.standing.simple
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have ha : a ∈ A := P.cex.ha.1
  have ha1 : a ≠ 1 := P.cex.ha.2
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := lemma122_ii_of_cex P.cex
  have hqs : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hK
  have hcore : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBel : IsElemAbelian p (autBar p (E ⊓ A) K) := isElemAbelian_autBar (isElemAbelian_inter hSec)
  have hDel : IsElemAbelian p D := CFSG.Open.IsElemAbelian.mono (isElemAbelian_inter hSec) P.hDA
  have hXtop : Cg a ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top P.cex.standing.nonabelian P.cex.ha.2
  have hDX : IsEkIn p r (Cg a) D := ⟨P.hDA.trans (inter_le_cg P.cex), hDel, P.hDcard⟩
  have hDt : IsEkIn p r ⊤ (autBar p D K) := Lemma136c.l136c_isEkIn_autBar hDX P.hDnorm P.hDfaith
  obtain ⟨B₀, n, hB₀A, hB₀N, hB₀F, hB₀el, hB₀card, hHeis⟩ : ∃ (B₀ : Subgroup G) (n : ℕ),
      B₀ ≤ E ⊓ A ∧ B₀ ≤ Subgroup.normalizer (K : Set G) ∧ (∀ x ∈ B₀, x ∈ centBar p ⊤ K → x = 1) ∧
      IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ((IsLpType p (q ^ n) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ q ^ n - 1 ∧
          Prop1116Design.HeisenbergImageL p (q ^ n) (autBar p B₀ K)) ∨
        (IsUpType p (q ^ n) (barOf p K ⧸ Subgroup.center (barOf p K)) ∧ p ∣ q ^ n + 1 ∧
          Prop1116Design.HeisenbergImageU p (q ^ n) (autBar p B₀ K))) := by
    by_cases hr1 : r = 1
    ·
      rcases h1116 hSec ha ha1 P.hK ⟨hq, hq2, hqp⟩ hchev with hKM | hD | hIii | hIv
      · exact absurd hKM P.hKM
      · exact absurd hD hnotD
      · obtain ⟨⟨n, hn⟩, hN, hcard, hfaith⟩ := hIii
        exact ⟨E ⊓ A, n, le_rfl, hN, hfaith, isElemAbelian_inter hSec, hcard, hn⟩
      · exfalso
        obtain ⟨hp13, -, hform⟩ := hIv
        subst hp13
        exact weak_nonbal hI191img h122 P hr1 (hI1918 (barOf 13 K) hqs hcore hform.symm _ hBel)
    ·
      have hr2 : 2 ≤ r := by have := P.hr; omega
      obtain ⟨hk2, n, hn⟩ := hI197 p q hp hp2 hq hq2 hqp (barOf p K) hqs hcore hchev r (autBar p D K)
        hr2 hDt.2.1 hDt.2.2 P.hbal
      refine ⟨D, n, P.hDA, P.hDnorm, ?_, hDel, by rw [P.hDcard, hk2], hn⟩
      intro x hx hxc
      obtain ⟨-, hxN, hxb⟩ := mem_centBar_iff.1 hxc
      have : x ∈ centBar p D K := mem_centBar_iff.2 ⟨hx, hxN, hxb⟩
      rw [P.hDfaith] at this
      exact Subgroup.mem_bot.1 this
  set W : Subgroup G := Tof p M a ⊓ Subgroup.normalizer (K : Set G) with hW
  have hW2 : IsPGroup 2 ↥W := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hBW : B₀ ≤ Subgroup.normalizer (W : Set G) := fun x hx =>
    mem_normalizer_inf' (inter_le_normalizer_tof P.cex (hB₀A hx)) (Subgroup.le_normalizer (hB₀N hx))
  have hJW : ∀ b ∈ B₀, b ≠ 1 → GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (W : Set G) := by
    intro b hb hb1 y hy
    have hyM : y ∈ M := cov1 hp h112 hSec ha ha1 hnotD P.hK (hB₀A hb) hb1 hy
    have hyKC : y ∈ K ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _ hy
    have hyK : y ∈ K := (Subgroup.mem_inf.1 hyKC).1
    have hyC : y ∈ Cg a := P.hK.1 hyK
    exact mem_normalizer_inf' (mem_normalizer_tof hyM hyC)
      (Subgroup.le_normalizer (Subgroup.le_normalizer hyK))
  have hzero := hI272 G p q n (Cg a) K B₀ W hp hp2 hq hq2 hqp P.hK (hB₀A.trans (inter_le_cg P.cex)) hB₀el
    hB₀card hB₀N hB₀F hHeis hW2 inf_le_right hBW hJW
  obtain ⟨t, ht, htN, htne⟩ := exists_barAut_ne_one P
  exact htne (hzero t ⟨ht.1, htN⟩)

end Lemma123

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
