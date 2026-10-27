module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123a
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SporadicGammaPairs
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Mod
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03J4
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HSAux.ThreeCent
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HeAux.ThreeCheck
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Ru
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3M24
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporMathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveCo3
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveJ2
public import CFSG.LargeExtraspecial.S97RQuasi
public import CFSG.RankThree.Native.SuzFiveCentralizers

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceFromYS

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn SporadicP2Table B3SporRestPair)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut localDeltaIn)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (OPrimeCoreTrivialAt SporadicOPrimeHolds SporadicOneParts)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges SporadicOnePair)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo (OPrimeCoreLeTwoAt LocalTwoBalanceSporadicGtFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Bridge

theorem localDeltaTwoIn_le_localDeltaIn {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (H D : Subgroup M) : localDeltaTwoIn H D ≤ localDeltaIn p H D := by
  unfold localDeltaTwoIn localDeltaIn
  exact iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ =>
    Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem isLocallyOTwoBalancedWrtP_of_abs {k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsLocallyBalancedAbs p k K) : IsLocallyOTwoBalancedWrtP p k K := by
  intro A _ D hD H hH hDH
  exact le_bot_iff.1 ((localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans
    (h D hD.2.1 hD.2.2 H hH hDH).le)

theorem isWeaklyLocallyOTwoBalancedWrtP_of_abs (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsLocallyBalancedAbs p 1 K) : IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  intro A _ D hD H hH hAH
  have h0 : localDeltaTwoIn H D = ⊥ := le_bot_iff.1 ((localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans
    (h D hD.2.1 hD.2.2 H hH (hD.1.trans hAH)).le)
  rw [h0, Subgroup.commutator_bot_left]

theorem isWeaklyLocallyOTwoBalancedWrtP_congr {K' : Type} [Group K'] [Finite K'] {k : ℕ} (e : K ≃* K') :
    IsWeaklyLocallyOTwoBalancedWrtP p k K ↔ IsWeaklyLocallyOTwoBalancedWrtP p k K' :=
  ⟨Inputs123a.isWeaklyLocallyOTwoBalancedWrtP_of_map (MulAut.congr e.symm).toMonoidHom
      (MulAut.congr e.symm).injective (Inputs123a.innerAut_le_map_congr e.symm),
    Inputs123a.isWeaklyLocallyOTwoBalancedWrtP_of_map (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective (Inputs123a.innerAut_le_map_congr e)⟩

end Bridge

section Weak

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem isWeaklyLocallyOTwoBalancedWrtP_of_card_le_two (hp : p.Prime)
    (h : ∀ x : MulAut K, orderOf x = p → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
      x ∈ Subgroup.normalizer (H : Set (MulAut K)) →
        Nat.card (pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))) ≤ 2) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro A hA D hD H hH hAH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hDc
    exact hp.one_lt.ne hDc
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdo : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1'
  have hDeq : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
      (by rw [Nat.card_zpowers, hdo, hDc, pow_one])).symm
  have hcard := h d hdo H hH (hAH (hDA hdD))
  rw [← Inputs123a.localDeltaTwoIn_zpowers hp hdo H, ← hDeq] at hcard
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer ((localDeltaTwoIn H D : Subgroup (MulAut K)) :
      Set (MulAut K)) := fun a ha =>
    Lemma123.mem_normalizer_localDeltaTwoIn (hAH ha) fun e he =>
      CFSG.Open.IsElemAbelian.comm hA ha (hDA he)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro t ht a ha
  rw [Subgroup.mem_bot, commutatorElement_def]
  by_cases ht1 : t = 1
  · rw [ht1]
    group
  have hat : a * t * a⁻¹ ∈ localDeltaTwoIn H D := (Subgroup.mem_normalizer_iff.1 (hAN a ha) t).1 ht
  have hat1 : a * t * a⁻¹ ≠ 1 := fun h1 => ht1 (by
    have h2 := congrArg (fun z => a⁻¹ * z * a) h1
    simpa [mul_assoc] using h2)
  have heq : (⟨a * t * a⁻¹, hat⟩ : ↥(localDeltaTwoIn H D)) = ⟨t, ht⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.eq_of_ne_one_of_card_le_two hcard
      (fun e => hat1 (congrArg Subtype.val e)) (fun e => ht1 (congrArg Subtype.val e))
  have heq' : a * t * a⁻¹ = t := congrArg Subtype.val heq
  calc t * a * t⁻¹ * a⁻¹ = t * (a * t * a⁻¹)⁻¹ := by group
    _ = 1 := by rw [heq', mul_inv_cancel]

theorem isWeaklyLocallyOTwoBalancedWrtP_of_card_le
    (h : ∀ A : Subgroup (MulAut K), IsElemAbelian p A → Nat.card A ≤ p) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  intro A hA D hD H _ _
  obtain ⟨hDA, -, hDc⟩ := hD
  have hAD : D = A := Subgroup.eq_of_le_of_card_ge hDA (by rw [hDc, pow_one]; exact h A hA)
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro t ht a ha
  have ha' : a ∈ D := hAD ▸ ha
  rw [Subgroup.mem_bot, commutatorElement_def]
  by_cases ha1 : a = 1
  · rw [ha1]
    group
  have hle : localDeltaTwoIn H D ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer ({a} : Set (MulAut K))) :=
    (iInf_le _ a).trans ((iInf_le _ ha').trans (iInf_le _ ha1))
  have hta : t * a = a * t :=
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hle ht)).2
  rw [hta]
  group

theorem mem_innerAut_of_pow_prime (hp : p.Prime) (hp2 : p ≠ 2) (hout : Nat.card (Outer K) ≤ 2)
    {x : MulAut K} (hx : x ^ p = 1) : x ∈ innerAut K := by
  let q : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
  have hsq : (q x) ^ 2 = 1 := by
    have hc : (q x) ^ Nat.card (Outer K) = 1 := pow_card_eq_one'
    have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
    interval_cases hn : Nat.card (Outer K)
    · rw [pow_one] at hc
      rw [hc, one_pow]
    · exact hc
  have h3 : (q x) ^ p = 1 := by rw [← map_pow, hx, map_one]
  have h4 : orderOf (q x) ∣ Nat.gcd p 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hsq)
  have hg : Nat.gcd p 2 = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact (QuotientGroup.eq_one_iff x).1 h4

theorem card_le_of_not_sq_dvd (hp : p.Prime) (hp2 : p ≠ 2) (hout : Nat.card (Outer K) ≤ 2)
    (hsq : ¬ p ^ 2 ∣ Nat.card K) (A : Subgroup (MulAut K)) (hA : IsElemAbelian p A) :
    Nat.card A ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAI : A ≤ innerAut K := fun a ha => mem_innerAut_of_pow_prime hp hp2 hout (hA.2 a ha)
  have h2 : Nat.card (innerAut K) ∣ Nat.card K := by
    have e := Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : K →* MulAut K)).toEquiv
    show Nat.card (MulAut.conj : K →* MulAut K).range ∣ Nat.card K
    rw [← e]
    exact Subgroup.card_quotient_dvd_card _
  have hdvd : Nat.card A ∣ Nat.card K := (Subgroup.card_dvd_of_le hAI).trans h2
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
  rw [hn] at hdvd ⊢
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp only [pow_zero]
      exact hp.one_lt.le
    · rw [pow_one]
  · exact absurd ((pow_dvd_pow p h).trans hdvd) hsq

theorem inf_innerAut_le_map (hp : p.Prime) (hψ : Function.Injective (MulAut.conj : K →* MulAut K)) (s : K)
    {H : Subgroup (MulAut K)} (hH : innerAut K ≤ H) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))) ⊓ innerAut K ≤
      (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))).map (MulAut.conj : K →* MulAut K) := by
  set A : Subgroup (MulAut K) := H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K)) with hA
  set B : Subgroup (MulAut K) :=
    innerAut K ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K)) with hB
  have hBA : B ≤ A := inf_le_inf hH le_rfl
  have hNA : GLAPPrimeCoreOf p A ≤ A := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le A
  have hOB : (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))).map (MulAut.conj : K →* MulAut K) =
      GLAPPrimeCoreOf p B := by
    have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
      (MulAut.conj : K →* MulAut K) hψ (Subgroup.centralizer ({s} : Set K))
    have hc := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective
      (MulAut.conj : K →* MulAut K) hψ ⊤ s
    rw [top_inf_eq] at hc
    have hrange : (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) = innerAut K :=
      (MonoidHom.range_eq_map _).symm
    rw [hrange] at hc
    rw [hc] at hmap
    exact hmap
  rw [hOB]
  refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal
    (fun y hy => ⟨hy.2, (hNA hy.1).2⟩) ?_ ?_
  · intro g hg y hy
    refine ⟨CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem g (hBA hg) y hy.1, ?_⟩
    exact (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K).conj_mem y hy.2 g
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp A)

theorem isWeaklyLocallyOTwoBalancedWrtP_of_oPrime (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center K = ⊥) (hout : Nat.card (Outer K) ≤ 2) (h1 : OPrimeCoreTrivialAt p K) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  refine isWeaklyLocallyOTwoBalancedWrtP_of_card_le_two hp fun x hx H hH _ => ?_
  have hψ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
  obtain ⟨s, rfl⟩ := mem_innerAut_of_pow_prime hp hp2 hout (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hs : orderOf s = p := by rw [← hx, orderOf_injective _ hψ s]
  set N := GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))) with hNdef
  have hN : N ⊓ innerAut K = ⊥ := by
    have h0 := inf_innerAut_le_map hp hψ s hH
    rw [h1 s hs, Subgroup.map_bot] at h0
    exact le_bot_iff.1 h0
  have hcardN : Nat.card N ≤ 2 := by
    let q : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
    have hinj : Function.Injective (fun n : N => q n) := by
      intro a b hab
      have hab' : (a : MulAut K)⁻¹ * b ∈ inner K := QuotientGroup.eq.1 hab
      have hmem : (a : MulAut K)⁻¹ * b ∈ N ⊓ innerAut K := ⟨N.mul_mem (N.inv_mem a.2) b.2, hab'⟩
      rw [hN, Subgroup.mem_bot] at hmem
      exact Subtype.ext (inv_mul_eq_one.1 hmem)
    exact (Nat.card_le_card_of_injective _ hinj).trans hout
  exact (Subgroup.card_le_of_le (Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _)).trans hcardN

theorem isWeaklyLocallyOTwoBalancedWrtP_of_leTwo (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center K = ⊥) (hinn : innerAut K = ⊤) (h2 : OPrimeCoreLeTwoAt p K) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  refine isWeaklyLocallyOTwoBalancedWrtP_of_card_le_two hp fun x hx H hH _ => ?_
  have hψ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
  have hxI : x ∈ innerAut K := hinn ▸ Subgroup.mem_top x
  obtain ⟨s, rfl⟩ := hxI
  have hs : orderOf s = p := by rw [← hx, orderOf_injective _ hψ s]
  have hle := inf_innerAut_le_map hp hψ s hH
  rw [hinn, inf_top_eq] at hle
  have hmap : Nat.card ((GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))).map
      (MulAut.conj : K →* MulAut K)) ≤ 2 := by
    rw [Subgroup.card_map_of_injective hψ]
    exact h2 s hs
  have hcardN : Nat.card (GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K)))) ≤ 2 :=
    (Subgroup.card_le_of_le hle).trans hmap
  exact (Subgroup.card_le_of_le (Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _)).trans hcardN

theorem commute_of_card_lt {G : Type*} [Group G] {T : Subgroup G} [Finite T] {p : ℕ} (hp : p.Prime)
    (hT : Nat.card T < p) {a : G} (ha : a ^ p = 1) (haN : a ∈ Subgroup.normalizer (T : Set G)) {t : G}
    (ht : t ∈ T) : a * t = t * a := by
  by_contra hne
  have hfix : ∀ m : ℕ, 0 < m → m < p → a ^ m * t * (a ^ m)⁻¹ ≠ t := by
    intro m hm0 hmp heq
    apply hne
    have hcop : Nat.Coprime m p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hm0 hmp))
    obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have han : (a ^ m) ^ n = a := by
      rw [← pow_mul, ← Nat.mod_add_div (m * n) p, hn, pow_add, pow_mul, ha, one_pow, mul_one, pow_one]
    have hc : Commute (a ^ m) t := by
      show a ^ m * t = t * a ^ m
      calc a ^ m * t = (a ^ m * t * (a ^ m)⁻¹) * a ^ m := by group
        _ = t * a ^ m := by rw [heq]
    rw [← han]
    exact (hc.pow_left n).eq
  have hmem : ∀ k : ℕ, a ^ k * t * (a ^ k)⁻¹ ∈ T := fun k =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (T : Set G)).pow_mem haN k) t).1 ht
  have key : ∀ i j : ℕ, i < j → j < p → a ^ i * t * (a ^ i)⁻¹ ≠ a ^ j * t * (a ^ j)⁻¹ := by
    intro i j hij hjp heq
    apply hfix (j - i) (by omega) (by omega)
    have hj : a ^ j = a ^ i * a ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj] at heq
    calc a ^ (j - i) * t * (a ^ (j - i))⁻¹
        = (a ^ i)⁻¹ * (a ^ i * a ^ (j - i) * t * (a ^ i * a ^ (j - i))⁻¹) * a ^ i := by group
      _ = (a ^ i)⁻¹ * (a ^ i * t * (a ^ i)⁻¹) * a ^ i := by rw [← heq]
      _ = t := by group
  let f : Fin p → ↥T := fun k => ⟨a ^ (k : ℕ) * t * (a ^ (k : ℕ))⁻¹, hmem k⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hij' : a ^ (i : ℕ) * t * (a ^ (i : ℕ))⁻¹ = a ^ (j : ℕ) * t * (a ^ (j : ℕ))⁻¹ :=
      congrArg Subtype.val hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
    · exact absurd hij' (key _ _ h j.2)
    · exact Fin.ext h
    · exact absurd hij'.symm (key _ _ h i.2)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

theorem isWeaklyLocallyOTwoBalancedWrtP_of_card_lt (hp : p.Prime)
    (h : ∀ x : MulAut K, orderOf x = p → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
      x ∈ Subgroup.normalizer (H : Set (MulAut K)) →
        Nat.card (pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K)))) < p) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro A hA D hD H hH hAH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hDc
    exact hp.one_lt.ne hDc
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdo : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1'
  have hDeq : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
      (by rw [Nat.card_zpowers, hdo, hDc, pow_one])).symm
  have hcard := h d hdo H hH (hAH (hDA hdD))
  rw [← Inputs123a.localDeltaTwoIn_zpowers hp hdo H, ← hDeq] at hcard
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro t ht a ha
  rw [Subgroup.mem_bot, commutatorElement_def]
  have hta := commute_of_card_lt hp hcard (hA.2 a ha)
    (Lemma123.mem_normalizer_localDeltaTwoIn (hAH ha) fun e he =>
      CFSG.Open.IsElemAbelian.comm hA ha (hDA he)) ht
  calc t * a * t⁻¹ * a⁻¹ = (a * t) * t⁻¹ * a⁻¹ := by rw [hta]
    _ = 1 := by group

theorem card_le_card_inf_innerAut_mul_two (hout : Nat.card (Outer K) ≤ 2) (N : Subgroup (MulAut K)) :
    Nat.card N ≤ Nat.card (N ⊓ innerAut K : Subgroup (MulAut K)) * 2 := by
  let q : ↥N →* Outer K := (QuotientGroup.mk' (inner K)).comp N.subtype
  have hker : Nat.card q.ker = Nat.card (N ⊓ innerAut K : Subgroup (MulAut K)) := by
    have e : q.ker = (innerAut K).subgroupOf N := by
      ext n
      simp only [MonoidHom.mem_ker, q, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [e, ← Subgroup.inf_subgroupOf_right, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : Nat.card q.range ≤ 2 :=
    (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hout
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv, hker] at h1
  rw [h1, mul_comm]
  exact Nat.mul_le_mul_left _ hrange

theorem isWeaklyLocallyOTwoBalancedWrtP_of_leTwo_out (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcen : Subgroup.center K = ⊥) (hout : Nat.card (Outer K) ≤ 2) (h2 : OPrimeCoreLeTwoAt p K) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  have hp2 : p ≠ 2 := by omega
  refine isWeaklyLocallyOTwoBalancedWrtP_of_card_lt hp fun x hx H hH _ => ?_
  have hψ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
  obtain ⟨s, rfl⟩ := mem_innerAut_of_pow_prime hp hp2 hout (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hs : orderOf s = p := by rw [← hx, orderOf_injective _ hψ s]
  set N := GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))) with hNdef
  have hmap : Nat.card ((GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set K))).map
      (MulAut.conj : K →* MulAut K)) ≤ 2 := by
    rw [Subgroup.card_map_of_injective hψ]
    exact h2 s hs
  have hinf : Nat.card (N ⊓ innerAut K : Subgroup (MulAut K)) ≤ 2 :=
    (Subgroup.card_le_of_le (inf_innerAut_le_map hp hψ s hH)).trans hmap
  have hN : Nat.card N ≤ 4 := (card_le_card_inf_innerAut_mul_two hout N).trans (by omega)
  have h2N := (Subgroup.card_le_of_le (Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2
    (H ⊓ Subgroup.centralizer ({MulAut.conj s} : Set (MulAut K))))).trans hN
  omega

end Weak

section Sporadic

@[expose] def IsExc1917 (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (p = 5 ∧ name = .Fi22) ∨ (p = 3 ∧ (name = .M12 ∨ name = .M22 ∨ name = .J2))

instance (name : TauCeti.SporadicName) (p : ℕ) : Decidable (IsExc1917 name p) := by
  unfold IsExc1917
  infer_instance

@[expose] def ExtraOPrimePair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (p = 3 ∧ (name = .M11 ∨ name = .M23 ∨ name = .M24 ∨ name = .HS ∨ name = .He ∨ name = .Ru)) ∨
  (p = 5 ∧ (name = .J2 ∨ name = .HS ∨ name = .McL ∨ name = .He ∨ name = .Ru ∨ name = .Co2 ∨
    name = .Co3 ∨ name = .Fi23 ∨ name = .Fi24Prime ∨ name = .Th)) ∨
  (p = 7 ∧ (name = .Co1 ∨ name = .Fi24Prime ∨ name = .Th ∨ name = .ONan ∨ name = .He)) ∨
  (p = 11 ∧ (name = .M ∨ name = .J4)) ∨ (p = 13 ∧ name = .M)

instance (name : TauCeti.SporadicName) (p : ℕ) : Decidable (ExtraOPrimePair name p) := by
  unfold ExtraOPrimePair
  infer_instance

theorem restPair_cases {name : TauCeti.SporadicName} {p : ℕ} (h : B3SporRestPair name p) :
    IsExc1917 name p ∨ ExtraOPrimePair name p ∨ (name = .B ∧ p = 7) ∨ (name = .J4 ∧ p = 3) ∨
      (name = .Suz ∧ p = 5) := by
  unfold B3SporRestPair at h
  rcases h with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ <;>
    (try simp only [Finset.mem_insert, Finset.mem_singleton] at hn) <;>
    (try rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    decide

theorem centralizer_eq_of_zpowers_eq {G : Type*} [Group G] {a b : G}
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  have e : ∀ c : G, Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := fun c => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [e a, e b, h]

theorem map_conj_centralizer {G : Type*} [Group G] (c x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    calc c * z * c⁻¹ * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by group
      _ = c * (x * z) * c⁻¹ := by rw [hz]
      _ = c * x * c⁻¹ * (c * z * c⁻¹) := by group
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, by group⟩
    calc c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * y) * c := by rw [hy]
      _ = x * (c⁻¹ * y * c) := by group

theorem sporadicOPrimeHolds_HS_three :
    SporadicOPrimeHolds .HS 3 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv
    (e.trans CFSG.Sporadic.Schreier.hsPermEquiv)
    (CFSG.HardMathSupport.Solomon.Coordinator.i19s_oPrimeCoreTrivialAt_of_perm _
      CFSG.HardMathSupport.Dickson.LocalTwoBalance.HSAux.gLAPPrimeCoreOf_hs_three)

theorem sporadicOPrimeHolds_He_three :
    SporadicOPrimeHolds .He 3 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv
    (e.trans CFSG.Sporadic.HeldB.heEquivP)
    (CFSG.HardMathSupport.Solomon.Coordinator.i19s_oPrimeCoreTrivialAt_of_perm _ fun x hx hxo =>
      (CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux.heS3_centralizers x hx hxo).1)

theorem oPrimeCoreTrivialAt_M24_three :
    OPrimeCoreTrivialAt 3 ↥CFSG.Blueprint.NativeSporadic.M24 :=
  CFSG.HardMathSupport.Solomon.Coordinator.i19s_oPrimeCoreTrivialAt_of_perm _
    (CFSG.HardMathSupport.Solomon.Coordinator.B3S3.i19s_check_sound
      CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m24S3Data
      CFSG.HardMathSupport.Solomon.Coordinator.rep_m24A CFSG.HardMathSupport.Solomon.Coordinator.rep_m24B
      (by decide) Certificates.certificate13512)

theorem sporadicOPrimeHolds_M24_three : SporadicOPrimeHolds .M24 3 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv e
    oPrimeCoreTrivialAt_M24_three

theorem oPrimeCoreTrivialAt_ruP_three :
    OPrimeCoreTrivialAt 3 ↥CFSG.Sporadic.RuSchreier.ruP := by
  intro r hr
  obtain ⟨c, hc⟩ := CFSG.EvenSporadicStandard.RuStd.S2.exists_conj_ruThree r hr
  rw [centralizer_eq_of_zpowers_eq hc.symm, ← map_conj_centralizer,
    ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 3 _
      (MulAut.conj c).injective,
    CFSG.HardMathSupport.Solomon.Coordinator.ruThree_oPrime.2, Subgroup.map_bot]

theorem sporadicOPrimeHolds_Ru_three :
    SporadicOPrimeHolds .Ru 3 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv
    (e.trans CFSG.Sporadic.RuSchreier.ruEquivP) oPrimeCoreTrivialAt_ruP_three

theorem oPrimeCoreTrivialAt_co3P_five :
    OPrimeCoreTrivialAt 5 ↥CFSG.Sporadic.Schreier.Co3.co3P := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec0, hrec25, -⟩ :=
    CFSG.RankThree.Native.R3E_Co3_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrimeCoreTrivialAt_of_sub _
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrime_of_lines Nat.prime_five hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl)
      CFSG.RankThree.Native.co3FiveLine (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines)
      fun j => ?_)
  obtain ⟨hjP, hjconj⟩ := htrans j
  have hr : CFSG.RankThree.Native.co3FiveRecordOf j = 0 ∨ CFSG.RankThree.Native.co3FiveRecordOf j = 25 := by
    by_cases h : (j : ℕ) = 25
    · exact Or.inr ((hrec25 j).2 h)
    · exact Or.inl ((hrec0 j).2 h)
  rw [← hjconj]
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrime_inf_conj
    (fun r hr q hq => CFSG.Sporadic.Schreier.Co3.co3P.mul_mem
      (CFSG.Sporadic.Schreier.Co3.co3P.mul_mem hr hq) (CFSG.Sporadic.Schreier.Co3.co3P.inv_mem hr)) hjP
    (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_co3FiveRecord_eq_bot _ hr)

theorem sporadicOPrimeHolds_Co3_five :
    SporadicOPrimeHolds .Co3 5 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv
    (e.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv) oPrimeCoreTrivialAt_co3P_five

theorem oPrimeCoreTrivialAt_j2P_five :
    OPrimeCoreTrivialAt 5 ↥CFSG.Sporadic.Schreier.j2P := by
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlines, -⟩, -⟩ :=
    CFSG.RankThree.PartOne.R3E_J2_full_five_centralizer_structure
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := CFSG.Sporadic.SmallOddCore.j2_autModel
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrimeCoreTrivialAt_of_sub _
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrime_of_lines Nat.prime_five hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl)
      CFSG.RankThree.PartOne.j2FiveLine (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines)
      fun j => CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five
        hM.le hM.conj_mem (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_j2FiveC_eq_bot j))

theorem sporadicOPrimeHolds_J2_five :
    SporadicOPrimeHolds .J2 5 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv
    (e.trans CFSG.Sporadic.Schreier.j2PermEquiv) oPrimeCoreTrivialAt_j2P_five

theorem oPrimeCoreTrivialAt_heP_five :
    OPrimeCoreTrivialAt 5 ↥CFSG.Sporadic.HeldB.heP := by
  obtain ⟨⟨hQP, hQsyl, -, -⟩, ⟨hlines, -⟩, htrans, hrec, -⟩ :=
    CFSG.RankThree.PartOne.R3E_He_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hM := CFSG.RankThree.PartOne.heAutModel
  refine CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrimeCoreTrivialAt_of_sub _
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrime_of_lines Nat.prime_five hQP
      (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl)
      CFSG.RankThree.PartOne.heFiveLine (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines)
      fun j => ?_)
  obtain ⟨hjR, hjconj⟩ := htrans j
  rw [← hjconj, hrec j]
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_oPrime_inf_conj hM.conj_mem hjR
    (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_eq_bot_of_ambient Nat.prime_five hM.le
      hM.conj_mem CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_heFiveRecord_eq_bot)

theorem sporadicOPrimeHolds_He_five :
    SporadicOPrimeHolds .He 5 :=
  fun _ _ _ _ ⟨e⟩ => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv
    (e.trans CFSG.Sporadic.HeldB.heEquivP) oPrimeCoreTrivialAt_heP_five

theorem card_glaPPrimeCoreOf_three_le_two {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥C) (hz : Nat.card (Subgroup.center ↥C) = 6) (h3 : 3 ∣ Nat.card C) :
    Nat.card (GLAPPrimeCoreOf 3 C) ≤ 2 := by
  set N := GLAPPrimeCoreOf 3 C with hNdef
  have hNC : N ≤ C := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf Nat.prime_three C
  have hcardN : Nat.card (N.subgroupOf C) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
  haveI hN : (N.subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem (g : G) g.2 (x : G) hx
  have hne : N.subgroupOf C ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top] at hcardN
    rw [← hcardN] at hcop
    exact absurd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop) (not_not.2 h3)
  have hle := CFSG.LargeExtraspecial.S9.le_center_of_normal_of_ne_top hq.1.commutator_eq_top hq.2.1 hne
  have hdvd : Nat.card N ∣ 3 * 2 := by
    rw [← hcardN, show (3 : ℕ) * 2 = 6 by norm_num, ← hz]
    exact Subgroup.card_dvd_of_le hle
  exact Nat.le_of_dvd (by norm_num) (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd)

theorem oPrimeCoreLeTwoAt_J_three :
    OPrimeCoreLeTwoAt 3 ↥CFSG.Sporadic.J4.J := by
  intro s hs
  have hs3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    norm_num at hs
  obtain ⟨g, hg⟩ := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_conj_cE_of_orderThree s hs3 hs1
  obtain ⟨hq, hz, -⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_cE_quasisimple CFSG.Sporadic.J4.j4Facts
  have hC : Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.J4.J) =
      (Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    have hs' : g⁻¹ * CFSG.Quasithin.J4M2.cE * g⁻¹⁻¹ = s := by rw [← hg]; group
    rw [map_conj_centralizer, hs']
  have hcE : orderOf CFSG.Quasithin.J4M2.cE = 3 := by
    rw [← hg, ← hs]
    exact (MulAut.conj g).orderOf_eq s
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J)) := by
    have hmem : CFSG.Quasithin.J4M2.cE ∈ Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J) :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    have := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} :
      Set ↥CFSG.Sporadic.J4.J)))
    rwa [Subgroup.orderOf_mk, hcE] at this
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective 3
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    (Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} : Set ↥CFSG.Sporadic.J4.J))
  have key := card_glaPPrimeCoreOf_three_le_two hq hz h3
  calc Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.J4.J)))
      = Nat.card ((GLAPPrimeCoreOf 3 (Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} :
          Set ↥CFSG.Sporadic.J4.J))).map (MulAut.conj g⁻¹).toMonoidHom) := by rw [hC, hmap]
    _ = Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({CFSG.Quasithin.J4M2.cE} :
          Set ↥CFSG.Sporadic.J4.J))) := Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    _ ≤ 2 := key

set_option maxRecDepth 100000 in
theorem oPrimeCoreLeTwoAt_J4_three :
    OPrimeCoreLeTwoAt 3 (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.OPrimeCoreLeTwoAt.of_mulEquiv (K' := ↥CFSG.Sporadic.J4.J)
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ys03_seedEquivJ4 oPrimeCoreLeTwoAt_J_three

theorem card_core_le_of_lines {G : Type*} [Group G] [Finite G] {p c : ℕ} (hp : p.Prime) {P Q : Subgroup G}
    (hQP : Q ≤ P) (hQ : Nat.card Q = p ^ (Nat.card P).factorization p) {ι : Type*} (line : ι → G)
    (hlines : ∀ H : Subgroup G, H ≤ Q → Nat.card H = p → ∃ j, H = Subgroup.zpowers (line j))
    (hline : ∀ j, Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({line j} : Set G) ⊓ P)) ≤ c) :
    ∀ y ∈ P, orderOf y = p →
      Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({y} : Set G) ⊓ P)) ≤ c := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro y hyP hyo
  obtain ⟨g, hgP, hgQ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full hQP hQ hyP hyo
  set t := g⁻¹ * y * g with htdef
  have hto : orderOf t = p := by
    have := (MulAut.conj g⁻¹ : G ≃* G).orderOf_eq y
    simpa [MulAut.conj_apply, htdef, hyo] using this
  obtain ⟨j, hj⟩ := hlines (Subgroup.zpowers t) ((Subgroup.zpowers_le).2 hgQ)
    (by rw [Nat.card_zpowers, hto])
  have ht : Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({t} : Set G) ⊓ P)) ≤ c := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers hj]
    exact hline j
  have hy : y = g * t * g⁻¹ := by rw [htdef]; group
  have hk : ∀ q ∈ P, g * q * g⁻¹ ∈ P := fun q hq => P.mul_mem (P.mul_mem hgP hq) (P.inv_mem hgP)
  have hk' : ∀ q ∈ P, g⁻¹ * q * g ∈ P := fun q hq => P.mul_mem (P.mul_mem (P.inv_mem hgP) hq) hgP
  have hmap := CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (Subgroup.centralizer ({t} : Set G) ⊓ P)
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_conj_centralizer_inf hk hk' t, ← hy] at hmap
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact ht

theorem oPrimeCoreLeTwoAt_of_sub {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Subgroup G)
    (h : ∀ x ∈ P, orderOf x = p →
      Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P)) ≤ 2) :
    OPrimeCoreLeTwoAt p ↥P := by
  intro x hx
  have h1 := h x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype P x,
    ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p P.subtype
      P.subtype_injective, Subgroup.card_map_of_injective P.subtype_injective] at h1
  exact h1

theorem card_core_inf_le_two_of_ambient {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P R : Subgroup G} (hPR : P ≤ R) (hR : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P) {x : G} {K : Subgroup G}
    (hK : GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ R) ≤ K) (hKcard : Nat.card K = 2 * p) :
    Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P)) ≤ 2 := by
  have hOK := (CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_le_of_ambient hp hPR hR x).trans hK
  have hdvd : Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G) ⊓ P)) ∣ 2 * p :=
    hKcard ▸ Subgroup.card_dvd_of_le hOK
  have hcop := CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp
    (Subgroup.centralizer ({x} : Set G) ⊓ P)
  exact Nat.le_of_dvd (by norm_num) (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd)

theorem card_suzLine_core_le_two
    (i : Fin 6) :
    Nat.card (GLAPPrimeCoreOf 5 (Subgroup.centralizer ({CFSG.RankThree.Native.suzFiveLine i} :
      Set (Equiv.Perm (Fin 1782))) ⊓ CFSG.Sporadic.SuzOddCore.suzM)) ≤ 2 := by
  obtain ⟨-, -, hrec, hgood, hbad⟩ := CFSG.RankThree.Native.R3E_Suz_full_five_centralizer_structures
  obtain ⟨hCeq, hDs, hDnab, -⟩ := hrec i
  have hR : ∀ r ∈ CFSG.Sporadic.SuzOddCore.suzT, ∀ q ∈ CFSG.Sporadic.SuzOddCore.suzM,
      r * q * r⁻¹ ∈ CFSG.Sporadic.SuzOddCore.suzM := fun r hr q hq =>
    CFSG.Sporadic.SuzOddCore.suzT_conj_mem_suzM hr hq
  have hD : (⁅CFSG.RankThree.Native.suzFiveC i, CFSG.RankThree.Native.suzFiveC i⁆ :
      Subgroup (Equiv.Perm (Fin 1782))) = CFSG.RankThree.Native.suzFiveD i := rfl
  have hamb := CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_inf_le_of_ambient Nat.prime_five
    CFSG.Sporadic.SuzOddCore.suzM_le_suzT hR (CFSG.RankThree.Native.suzFiveLine i)
  by_cases hg : i.val = 0 ∨ i.val = 3 ∨ i.val = 4
  · obtain ⟨-, hDcard, hcentEq, hcard5⟩ := hgood i hg
    have hcore : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({CFSG.RankThree.Native.suzFiveLine i} :
        Set (Equiv.Perm (Fin 1782))) ⊓ CFSG.Sporadic.SuzOddCore.suzT) = ⊥ := by
      rw [← hCeq]
      exact CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_eq_bot_of_record_derived Nat.prime_five
        hDs hDnab (by rw [hD, hDcard]; norm_num)
        (IsPGroup.of_card (n := 1) (by rw [pow_one, hD, hcentEq]; exact hcard5))
    rw [hcore, le_bot_iff] at hamb
    rw [hamb, Subgroup.card_bot]
    norm_num
  · have hb : i.val = 1 ∨ i.val = 2 ∨ i.val = 5 := by
      have := i.2
      omega
    obtain ⟨-, hDcard, hcard10⟩ := hbad i hb
    have hle := CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_le_inf_centralizer (p := 5)
      Nat.prime_five (CFSG.HardMathSupport.Solomon.Coordinator.commutator_self_le'
        (CFSG.RankThree.Native.suzFiveC i))
      (fun g hg d hd => CFSG.HardMathSupport.Solomon.Coordinator.commutator_self_conj_mem hg hd)
      (CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_simple_subgroup hDs hDnab)
      (by rw [hD, hDcard]; norm_num)
    rw [hCeq] at hle
    exact card_core_inf_le_two_of_ambient Nat.prime_five CFSG.Sporadic.SuzOddCore.suzM_le_suzT hR hle
      (by rw [← hCeq, inf_comm, hD, hcard10])

theorem oPrimeCoreLeTwoAt_suzM_five :
    OPrimeCoreLeTwoAt 5 ↥CFSG.Sporadic.SuzOddCore.suzM := by
  obtain ⟨⟨hQP, -, -, -, hQsyl⟩, ⟨hlines, -⟩, -⟩ :=
    CFSG.RankThree.Native.R3E_Suz_full_five_centralizer_structures
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact oPrimeCoreLeTwoAt_of_sub _ (card_core_le_of_lines Nat.prime_five hQP
    (CFSG.HardMathSupport.Solomon.Coordinator.card_eq_of_sylow_subgroupOf hQP hQsyl)
    CFSG.RankThree.Native.suzFiveLine (CFSG.HardMathSupport.Solomon.Coordinator.lines_of_eq hlines)
    card_suzLine_core_le_two)

noncomputable def suzEquivM' :
    @MulEquiv CFSG.Blueprint.NativeSporadic.Suz ↥CFSG.Sporadic.SuzOddCore.suzM MulOneClass.toMul
      MulOneClass.toMul :=
  CFSG.Sporadic.SuzOddCore.suzEquivM

set_option maxRecDepth 100000 in
theorem oPrimeCoreLeTwoAt_Suz_five :
    OPrimeCoreLeTwoAt 5 (CFSG.Blueprint.NativeSporadic.Carrier .Suz) :=
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.OPrimeCoreLeTwoAt.of_mulEquiv
    (K' := ↥CFSG.Sporadic.SuzOddCore.suzM) suzEquivM' oPrimeCoreLeTwoAt_suzM_five

structure SporadicFacts : Prop where
  ys03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive
  ys04 : LocalTwoBalanceSporadicGtFive
  outer : SporadicOuterLeTwo
  bridges : SporadicBridges
  table : SporadicP2Table
  one : SporadicOneParts
  M11_three : SporadicOPrimeHolds .M11 3
  M23_three : SporadicOPrimeHolds .M23 3
  M24_three : SporadicOPrimeHolds .M24 3
  HS_three : SporadicOPrimeHolds .HS 3
  He_three : SporadicOPrimeHolds .He 3
  Ru_three : SporadicOPrimeHolds .Ru 3
  J2_five : SporadicOPrimeHolds .J2 5
  HS_five : SporadicOPrimeHolds .HS 5
  McL_five : SporadicOPrimeHolds .McL 5
  He_five : SporadicOPrimeHolds .He 5
  Ru_five : SporadicOPrimeHolds .Ru 5
  Co2_five : SporadicOPrimeHolds .Co2 5
  Co3_five : SporadicOPrimeHolds .Co3 5
  Fi23_five : SporadicOPrimeHolds .Fi23 5
  Fi24Prime_five : SporadicOPrimeHolds .Fi24Prime 5
  Th_five : SporadicOPrimeHolds .Th 5
  Co1_seven : SporadicOPrimeHolds .Co1 7
  Fi24Prime_seven : SporadicOPrimeHolds .Fi24Prime 7
  Th_seven : SporadicOPrimeHolds .Th 7
  ONan_seven : SporadicOPrimeHolds .ONan 7
  He_seven : SporadicOPrimeHolds .He 7
  M_eleven : SporadicOPrimeHolds .M 11
  J4_eleven : SporadicOPrimeHolds .J4 11
  M_thirteen : SporadicOPrimeHolds .M 13
  B_seven : OPrimeCoreLeTwoAt 7 (CFSG.Blueprint.NativeSporadic.Carrier .B)
  B_inner : innerAut (CFSG.Blueprint.NativeSporadic.Carrier .B) = ⊤
  J4_three : OPrimeCoreLeTwoAt 3 (CFSG.Blueprint.NativeSporadic.Carrier .J4)
  J4_inner : innerAut (CFSG.Blueprint.NativeSporadic.Carrier .J4) = ⊤
  Suz_five : OPrimeCoreLeTwoAt 5 (CFSG.Blueprint.NativeSporadic.Carrier .Suz)

theorem SporadicFacts.extra (F : SporadicFacts) {name : TauCeti.SporadicName} {p : ℕ}
    (h : ExtraOPrimePair name p) : SporadicOPrimeHolds name p := by
  unfold ExtraOPrimePair at h
  rcases h with ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  exacts [F.M11_three, F.M23_three, F.M24_three, F.HS_three, F.He_three, F.Ru_three, F.J2_five, F.HS_five,
    F.McL_five, F.He_five, F.Ru_five, F.Co2_five, F.Co3_five, F.Fi23_five, F.Fi24Prime_five, F.Th_five,
    F.Co1_seven, F.Fi24Prime_seven, F.Th_seven, F.ONan_seven, F.He_seven, F.M_eleven, F.J4_eleven,
    F.M_thirteen]

variable {S : Type} [Group S] [Finite S]

theorem three_or_five_or_gt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ p = 5 ∨ 5 < p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  omega

theorem isLocallyOTwoBalancedWrtP_two_spor (F : SporadicFacts) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {name : TauCeti.SporadicName} (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hs : IsSporType name S) (hexc : ¬ (p = 5 ∧ name = .Fi22)) : IsLocallyOTwoBalancedWrtP p 2 S := by
  refine isLocallyOTwoBalancedWrtP_of_abs hp hp2 ?_
  rcases three_or_five_or_gt hp hp2 with rfl | rfl | h5
  · exact F.ys03.sporadicThree name S hS hnab hs
  · exact F.ys03.sporadicFive name (fun h => hexc ⟨rfl, h⟩) S hS hnab hs
  · exact F.ys04 S hS hnab name hs p hp h5

theorem isWeaklyLocallyOTwoBalancedWrtP_one_spor (F : SporadicFacts) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {name : TauCeti.SporadicName} (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hs : IsSporType name S) (hexc : ¬ IsExc1917 name p) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 S := by
  haveI := hS
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := F.outer S hS hnab name hs
  by_cases hsq : p ^ 2 ∣ Nat.card S
  · have hsq' : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group := by
      rwa [← Nat.card_congr hs.some.toEquiv]
    have he : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier name) :=
      ⟨hs.some.trans (F.bridges name).some.symm⟩
    rcases F.table name p hp hp2 hsq' with h1 | h2
    · exact isWeaklyLocallyOTwoBalancedWrtP_of_oPrime hp hp2 hcen hout ((F.one.holds name p h1).1 S he)
    · rcases restPair_cases h2 with hE | hX | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hE hexc
      · exact isWeaklyLocallyOTwoBalancedWrtP_of_oPrime hp hp2 hcen hout (F.extra hX S he)
      · exact isWeaklyLocallyOTwoBalancedWrtP_of_leTwo hp hp2 hcen
          (CFSG.HardMathSupport.Timmesfeld.LocalTwo.innerAut_eq_top_of_mulEquiv he.some F.B_inner)
          (CFSG.HardMathSupport.Timmesfeld.LocalTwo.OPrimeCoreLeTwoAt.of_mulEquiv he.some F.B_seven)
      · exact isWeaklyLocallyOTwoBalancedWrtP_of_leTwo hp hp2 hcen
          (CFSG.HardMathSupport.Timmesfeld.LocalTwo.innerAut_eq_top_of_mulEquiv he.some F.J4_inner)
          (CFSG.HardMathSupport.Timmesfeld.LocalTwo.OPrimeCoreLeTwoAt.of_mulEquiv he.some F.J4_three)
      · exact isWeaklyLocallyOTwoBalancedWrtP_of_leTwo_out Nat.prime_five le_rfl hcen hout
          (CFSG.HardMathSupport.Timmesfeld.LocalTwo.OPrimeCoreLeTwoAt.of_mulEquiv he.some F.Suz_five)
  · exact isWeaklyLocallyOTwoBalancedWrtP_of_card_le fun A hA => card_le_of_not_sq_dvd hp hp2 hout hsq A hA

theorem input19_17_2_simple (F : SporadicFacts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {name : TauCeti.SporadicName} (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hs : IsSporType name S)
    (hnb : ¬ IsLocallyOTwoBalancedWrtP p 2 S ∨ ¬ IsWeaklyLocallyOTwoBalancedWrtP p 1 S) :
    IsExc1917 name p := by
  by_contra hexc
  have hexc5 : ¬ (p = 5 ∧ name = .Fi22) := fun h => hexc (Or.inl h)
  rcases hnb with h | h
  · exact h (isLocallyOTwoBalancedWrtP_two_spor F hp hp2 hS hnab hs hexc5)
  · exact h (isWeaklyLocallyOTwoBalancedWrtP_one_spor F hp hp2 hS hnab hs hexc)

theorem input19_17_2_of_facts (F : SporadicFacts) : Lemma123.Input19_17_2 := by
  intro p hp hp2 s Y _ _ hq _ hs hnb
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  refine input19_17_2_simple F hp hp2 hq.2 (Prop1116Design.not_isCommutative_barQuot Y hq) hs ?_
  rcases hnb with h | h
  · exact Or.inl fun h2 => h (Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hq.1 h2)
  · exact Or.inr fun h2 => h (Inputs123a.isWeaklyLocallyOTwoBalancedWrtP_of_quot hq.1 h2)

theorem innerAut_carrier_J4_eq_top :
    innerAut (CFSG.Blueprint.NativeSporadic.Carrier .J4) = ⊤ :=
  Subgroup.index_eq_one.mp CFSG.AGLEmbedding.card_outer_J4

theorem not_prime_sporOrd (s : TauCeti.SporadicName) :
    ¬ (CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s).Prime := by
  intro h
  have h2 : 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s := by
    cases s <;> decide
  have hne : CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s ≠ 2 := by
    cases s <;> decide
  rcases h.eq_one_or_self_of_dvd 2 h2 with h1 | h1
  · omega
  · exact hne h1.symm

theorem input19_17_2S_of_facts (F : SporadicFacts)
    (hsimp : ∀ s : TauCeti.SporadicName, IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group)
    (hord : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable) : Inputs123a.Input19_17_2S := by
  intro p hp hp2 s S _ _ hs hnb
  obtain ⟨e⟩ := hs
  haveI := hsimp s
  haveI : IsSimpleGroup S := e.isSimpleGroup
  have hnab : ∃ a b : S, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    haveI : IsMulCommutative S := ⟨⟨hc⟩⟩
    have hpr : (Nat.card S).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    rw [Nat.card_congr e.toEquiv, hord s] at hpr
    exact not_prime_sporOrd s hpr
  exact input19_17_2_simple F hp hp2 inferInstance hnab ⟨e⟩ hnb

end Sporadic

section Seitz

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple ambiguousChev onLie catalogIs)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo (IsLpEpsIndex LocalTwoBalanceCrossCharGtFive)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (LocalThreeBalanceCrossChar)

theorem characteristic_of_ambiguous {r : ℕ} (hr : r ≠ 2) (idx : TauCeti.ValidLieTypeIndex)
    (h : ambiguousChev r (TauCeti.CFSGIndex.lie idx)) : idx.1.characteristic = 2 := by
  have key : ∀ q' : TauCeti.PrimePower, q'.card = 8 ∨ q'.card = 2 → q'.p = 2 := by
    intro q' hq'
    have hdvd : q'.p ∣ 2 ^ 3 := by
      rcases hq' with h8 | h2
      · rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h8, TauCeti.PrimePower.card_def]
        exact dvd_pow_self _ q'.exponent_pos.ne'
      · have h1 : q'.p ∣ 2 := by
          rw [← h2, TauCeti.PrimePower.card_def]
          exact dvd_pow_self _ q'.exponent_pos.ne'
        exact h1.trans (by norm_num)
    exact (Nat.prime_dvd_prime_iff_eq q'.prime_p Nat.prime_two).1 (q'.prime_p.dvd_of_dvd_pow hdvd)
  simp only [ambiguousChev] at h
  split at h
  · rename_i q' heq
    rcases h with ⟨-, h2⟩ | ⟨h8, -⟩
    · exact absurd h2 hr
    · rw [heq, TauCeti.LieTypeIndex.characteristic_A]
      exact key q' (Or.inl h8)
  · exact absurd h.2 hr
  · rename_i q' heq
    rw [heq, TauCeti.LieTypeIndex.characteristic_twistedA]
    exact key q' (Or.inr h.1)
  · exact h.elim

theorem chevSimple_cases {p q : ℕ} (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q ≠ p) {S : Type} [Group S]
    (h : IsChevSimple q S) :
    (∃ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) ∧
        idx.1.characteristic ≠ p) ∨
      (q = 5 ∧ Nonempty (S ≃* ↥(alternatingGroup (Fin 5)))) ∨
        (q = 3 ∧ Nonempty (S ≃* ↥(alternatingGroup (Fin 6)))) := by
  rcases h with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
  · cases i with
    | lie idx => exact Or.inl ⟨idx, he, by simp only [onLie] at hi; rw [hi]; exact hqp⟩
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | lie idx =>
      refine Or.inl ⟨idx, he, ?_⟩
      rw [characteristic_of_ambiguous hq2 idx hi]
      exact Ne.symm hp2
    | alternating n hn =>
      simp only [ambiguousChev] at hi
      rcases hi with ⟨rfl, h2 | h5⟩ | ⟨rfl, h2 | h3⟩ | ⟨-, h2⟩
      · exact absurd h2 hq2
      · exact Or.inr (Or.inl ⟨h5, he⟩)
      · exact absurd h2 hq2
      · exact Or.inr (Or.inr ⟨h3, he⟩)
      · exact absurd h2 hq2
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

theorem card_dvd_card_mulAut_of_quot {Y : Type} [Group Y] [Finite Y] (hY : commutator Y = ⊤) {T : Type}
    [Group T] (e : (Y ⧸ Subgroup.center Y) ≃* T) (B : Subgroup (MulAut Y)) :
    Nat.card B ∣ Nat.card (MulAut T) := by
  have hf : Function.Injective ((MulAut.congr e).toMonoidHom.comp (Lemma123.autQ Y)) :=
    (MulAut.congr e).injective.comp (Lemma123.autQ_injective hY)
  rw [← Subgroup.card_map_of_injective hf]
  haveI : Finite (MulAut T) := Finite.of_equiv _ (MulAut.congr e).toEquiv
  exact Subgroup.card_subgroup_dvd_card _

theorem card_mulAut_alt5 : Nat.card (MulAut ↥(alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num) (by norm_num))),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem not_sq_dvd_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 2 ∣ 120 ∧ (p ≠ 3 → ¬ p ^ 2 ∣ 1440) := by
  constructor
  · intro h
    have hle : p ^ 2 ≤ 120 := Nat.le_of_dvd (by norm_num) h
    have hp10 : p ≤ 10 := by nlinarith
    interval_cases p <;> revert hp hp2 h <;> decide
  · intro hp3 h
    have hle : p ^ 2 ≤ 1440 := Nat.le_of_dvd (by norm_num) h
    have hp37 : p ≤ 37 := by nlinarith
    interval_cases p <;> revert hp hp2 hp3 h <;> decide

theorem false_of_alt_quot {Y : Type} [Group Y] [Finite Y] (hY : commutator Y = ⊤) {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 2 ≤ k) (B : Subgroup (MulAut Y)) (hB : Nat.card B = p ^ k)
    (h : Nonempty ((Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin 5))) ∨
      (p ≠ 3 ∧ Nonempty ((Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin 6))))) : False := by
  have hsq : ∀ m : ℕ, p ^ k ∣ m → p ^ 2 ∣ m := fun m hm => (pow_dvd_pow p hk).trans hm
  rcases h with h | ⟨hp3, h⟩
  · obtain ⟨e⟩ := h
    have h1 := card_dvd_card_mulAut_of_quot hY e B
    rw [hB, card_mulAut_alt5] at h1
    exact (not_sq_dvd_alt hp hp2).1 (hsq _ h1)
  · obtain ⟨e⟩ := h
    have h1 := card_dvd_card_mulAut_of_quot hY e B
    rw [hB, CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at h1
    exact (not_sq_dvd_alt hp hp2).2 hp3 (hsq _ h1)

@[expose] def Input19_7_3Lp : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → ∀ (Y : Type) [Group Y] [Finite Y],
    CFSG.Open.IsQuasisimple Y → GLAPPrimeCore p Y = ⊥ → IsChevSimple q (Y ⧸ Subgroup.center Y) →
    (∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ B' : Subgroup (MulAut Y), IsElemAbelian p B' → Nat.card B' = p ^ 2 →
      ¬ IsLocallyOTwoBalanced p 2 B' →
        ∃ n : ℕ,
          (IsLpType p (q ^ n) (Y ⧸ Subgroup.center Y) ∧ p ∣ q ^ n - 1 ∧
            Prop1116Design.HeisenbergImageL p (q ^ n) B') ∨
          (IsUpType p (q ^ n) (Y ⧸ Subgroup.center Y) ∧ p ∣ q ^ n + 1 ∧
            Prop1116Design.HeisenbergImageU p (q ^ n) B')

theorem input19_7_3Lp_of_input19_7_3 (h : Lemma123.Input19_7_3) : Input19_7_3Lp :=
  fun p q hp hp2 hq hq2 hqp Y _ _ hY hO hchev _ B' hB'el hB'c hnb =>
    (h p q hp hp2 hq hq2 hqp Y hY hO hchev 2 B' le_rfl hB'el hB'c hnb).2

theorem input19_7_3_of_ys (h02 : LocalThreeBalanceCrossChar)
    (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive) (h04 : LocalTwoBalanceCrossCharGtFive)
    (hLp : Input19_7_3Lp) : Lemma123.Input19_7_3 := by
  intro p q hp hp2 hq hq2 hqp Y _ _ hY hO hchev k B' hk hB'el hB'c hnb
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hnab := Prop1116Design.not_isCommutative_barQuot Y hY
  have htr : ∀ k' : ℕ, IsLocallyOTwoBalancedWrtP p k' (Y ⧸ Subgroup.center Y) →
      IsLocallyOTwoBalanced p k' B' := fun k' h =>
    Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hY.1 h B' hB'el
  rcases chevSimple_cases hp2 hq2 hqp hchev with ⟨idx, he, hch⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩
  · have hk2 : k = 2 := by
      by_contra hk2
      have h3 : IsLocallyOTwoBalancedWrtP p 3 (Y ⧸ Subgroup.center Y) :=
        isLocallyOTwoBalancedWrtP_of_abs hp hp2 (h02 _ hY.2 hnab idx he p hp hp2 hch)
      exact hnb (Lemma123.isLocallyOTwoBalanced_of_le hp (by norm_num) (by omega) (htr 3 h3))
    subst hk2
    refine ⟨rfl, ?_⟩
    by_cases hL : ∃ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx').Group)
    · exact hLp p q hp hp2 hq hq2 hqp Y hY hO hchev hL B' hB'el hB'c hnb
    · exfalso
      have hL' : ∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
          IsEmpty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx').Group) :=
        fun idx' h => not_nonempty_iff.1 fun hn => hL ⟨idx', h, hn⟩
      have h2 : IsLocallyBalancedAbs p 2 (Y ⧸ Subgroup.center Y) := by
        rcases three_or_five_or_gt hp hp2 with rfl | rfl | h5
        · exact h03.crossCharThree _ hY.2 hnab idx he hch hL'
        · exact h03.crossCharFive _ hY.2 hnab idx he hch hL'
        · exact h04 _ hY.2 hnab idx he p hp h5 hch hL'
      exact hnb (htr 2 (isLocallyOTwoBalancedWrtP_of_abs hp hp2 h2))
  · exact (false_of_alt_quot hY.1 hp hp2 hk B' hB'c (Or.inl he)).elim
  · exact (false_of_alt_quot hY.1 hp hp2 hk B' hB'c (Or.inr ⟨Ne.symm hqp, he⟩)).elim

end Seitz

section ChevTwo

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple ambiguousChev onLie catalogIs)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo (IsLpEpsIndex LocalTwoBalanceCrossCharGtFive
  LocalTwoBalanceDefCharGtFive)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (LocalThreeBalanceCrossChar)
open CFSG.HardMathSupport.Solomon.Coordinator (LocalTwoBalanceDefCharThree LocalTwoBalanceDefCharFive)

theorem lie_balance (h02 : LocalThreeBalanceCrossChar)
    (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive) (h04 : LocalTwoBalanceCrossCharGtFive)
    (hd3 : LocalTwoBalanceDefCharThree) (hd5 : LocalTwoBalanceDefCharFive) (hd7 : LocalTwoBalanceDefCharGtFive)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) :
    (idx.1.characteristic ≠ p → IsLocallyOTwoBalancedWrtP p 3 S) ∧
      ((idx.1.characteristic = p ∨ ∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
          IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx').Group)) → IsLocallyOTwoBalancedWrtP p 2 S) := by
  refine ⟨fun hch => isLocallyOTwoBalancedWrtP_of_abs hp hp2 (h02 S hS hnab idx he p hp hp2 hch), ?_⟩
  rintro (hch | hL)
  · refine isLocallyOTwoBalancedWrtP_of_abs hp hp2 ?_
    rcases three_or_five_or_gt hp hp2 with rfl | rfl | h5
    · exact hd3 S hS hnab idx he hch
    · exact hd5 S hS hnab idx he hch
    · exact hd7 S hS hnab idx he p hp h5 hch
  · by_cases hch : idx.1.characteristic = p
    · refine isLocallyOTwoBalancedWrtP_of_abs hp hp2 ?_
      rcases three_or_five_or_gt hp hp2 with rfl | rfl | h5
      · exact hd3 S hS hnab idx he hch
      · exact hd5 S hS hnab idx he hch
      · exact hd7 S hS hnab idx he p hp h5 hch
    · refine isLocallyOTwoBalancedWrtP_of_abs hp hp2 ?_
      rcases three_or_five_or_gt hp hp2 with rfl | rfl | h5
      · exact h03.crossCharThree S hS hnab idx he hch hL
      · exact h03.crossCharFive S hS hnab idx he hch hL
      · exact h04 S hS hnab idx he p hp h5 hch hL

theorem chevSimple_two_cases {S : Type} [Group S] (h : IsChevSimple 2 S) :
    (∃ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) ∨
      Nonempty (S ≃* ↥(alternatingGroup (Fin 5))) ∨ Nonempty (S ≃* ↥(alternatingGroup (Fin 6))) ∨
        Nonempty (S ≃* ↥(alternatingGroup (Fin 8))) := by
  rcases h with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
  · cases i with
    | lie idx => exact Or.inl ⟨idx, he⟩
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | lie idx => exact Or.inl ⟨idx, he⟩
    | alternating n hn =>
      simp only [ambiguousChev] at hi
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl he))
      · exact Or.inr (Or.inr (Or.inr he))
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

theorem card_mulAut_alt8 : Nat.card (MulAut ↥(alternatingGroup (Fin 8))) = 40320 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num))),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem eq_three_of_pow_dvd_alt8 {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 2 ≤ k) (h : p ^ k ∣ 40320) :
    p = 3 ∧ k = 2 := by
  have h2 : p ^ 2 ∣ 40320 := (pow_dvd_pow p hk).trans h
  have hdvd : p ∣ 2 ^ 7 * 3 ^ 2 * 5 * 7 := (dvd_pow_self p two_ne_zero).trans (by norm_num at h2 ⊢; exact h2)
  have hp3 : p = 3 := by
    have hpr := fun q (hq : q.Prime) (h : p ∣ q) => (Nat.prime_dvd_prime_iff_eq hp hq).1 h
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h7
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h5
      · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h3
        · exact absurd (hpr 2 Nat.prime_two (hp.dvd_of_dvd_pow h1)) hp2
        · exact hpr 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)
      · obtain rfl := hpr 5 Nat.prime_five h5
        norm_num at h2
    · obtain rfl := hpr 7 (by norm_num) h7
      norm_num at h2
  subst hp3
  refine ⟨rfl, ?_⟩
  by_contra hk2
  have h3 : 3 ^ 3 ∣ 40320 := (pow_dvd_pow 3 (by omega : 3 ≤ k)).trans h
  norm_num at h3

theorem exists_fix_ne_two_four {D : Subgroup (Equiv.Perm (Fin 8))} (hD : IsElemAbelian 3 D)
    (hc : Nat.card D = 9) :
    ∃ σ ∈ D, σ ≠ 1 ∧ Fintype.card {i // σ i = i} ≠ 2 ∧ Fintype.card {i // σ i = i} ≠ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  have hcardfix : ∀ σ : ↥D, Fintype.card (MulAction.fixedBy (Fin 8) σ) =
      Fintype.card {i // (σ : Equiv.Perm (Fin 8)) i = i} :=
    fun σ => Fintype.card_congr (Equiv.subtypeEquivRight fun i => Iff.rfl)
  have hfix : ∀ σ : ↥D, σ ≠ 1 → Fintype.card (MulAction.fixedBy (Fin 8) σ) = 2 := by
    intro σ hσ1
    have hσ1' : (σ : Equiv.Perm (Fin 8)) ≠ 1 := fun h => hσ1 (Subtype.ext h)
    have hmod := CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts3.card_fix_modEq
      (σ : Equiv.Perm (Fin 8)) (hD.2 σ σ.2)
    rw [Nat.card_eq_fintype_card] at hmod
    rw [hcardfix]
    by_contra h2
    have h4 := hcon σ σ.2 hσ1' h2
    rw [h4] at hmod
    exact absurd hmod (by decide)
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group ↥D (Fin 8)
  have hcD : Fintype.card ↥D = 9 := by rw [← Nat.card_eq_fintype_card, hc]
  rw [hcD, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (1 : ↥D))] at hB
  have h1 : Fintype.card (MulAction.fixedBy (Fin 8) (1 : ↥D)) = 8 := by
    rw [hcardfix]
    simp
  have hrest : ∑ σ ∈ Finset.univ \ {(1 : ↥D)}, Fintype.card (MulAction.fixedBy (Fin 8) σ) = 16 := by
    rw [Finset.sum_congr rfl fun σ hσ => hfix σ (by simpa using hσ), Finset.sum_const, smul_eq_mul,
      Finset.card_sdiff, Finset.card_univ, hcD]
    simp
  rw [h1, hrest] at hB
  omega

theorem input19_8_A8_holds : IsLocallyOTwoBalancedWrtP 3 2 ↥(alternatingGroup (Fin 8)) := by
  classical
  let Φ : Equiv.Perm (Fin 8) ≃* MulAut ↥(alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num))
  intro A _ D hD H hH _
  obtain ⟨-, hDel, hDc⟩ := hD
  have hD'el : IsElemAbelian 3 (D.map Φ.symm.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hDel Φ.symm.toMonoidHom
  have hD'c : Nat.card (D.map Φ.symm.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective Φ.symm.injective, hDc]
    norm_num
  obtain ⟨σ, hσD', hσ1, hfix2, hfix4⟩ := exists_fix_ne_two_four hD'el hD'c
  obtain ⟨d, hdD, hdσ⟩ := hσD'
  have hσ : σ = Φ.symm d := hdσ.symm
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hσ1
    rw [hσ, map_one]
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hDel.2 d hdD, map_one]
  set H' : Subgroup (Equiv.Perm (Fin 8)) := H.map Φ.symm.toMonoidHom with hH'
  have hAH' : alternatingGroup (Fin 8) ≤ H' := by
    intro a ha
    refine ⟨Φ a, hH ⟨⟨a, ha⟩, ?_⟩, by simp⟩
    ext x
    simp [Φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have h0 := Inputs123a.pCoreOf_eq_bot_of_card_fix Nat.prime_three (by norm_num) hσ3 hAH' hfix2 hfix4
  have hHH : H'.map Φ.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨Φ.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hmap : (H' ⊓ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))).map Φ.toMonoidHom =
      H ⊓ Subgroup.centralizer ({d} : Set (MulAut ↥(alternatingGroup (Fin 8)))) := by
    rw [Inputs123a.map_inf_centralizer Φ.toMonoidHom Φ.injective, hHH]
    simp [hσ]
  have hle : localDeltaTwoIn H D ≤
      pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut ↥(alternatingGroup (Fin 8))))) :=
    (iInf_le _ d).trans ((iInf_le _ hdD).trans (iInf_le _ hd1))
  rw [← hmap, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 Φ, h0, Subgroup.map_bot] at hle
  exact le_bot_iff.1 hle

@[expose] def Input19_16_twoLp : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → IsChevSimple 2 (Y ⧸ Subgroup.center Y) →
    (∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx.1 ∧
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
    ∀ B' : Subgroup (MulAut Y), IsElemAbelian p B' → Nat.card B' = p ^ 2 →
      ¬ IsLocallyOTwoBalanced p 2 B' →
        p = 3 ∧ IsLThreeFour (Y ⧸ Subgroup.center Y) ∧ B' ≤ innerAut Y ∧
        ∀ H : Subgroup (MulAut Y), innerAut Y ≤ H → localDeltaTwoIn H B' ≠ ⊥ →
          ∃ u : MulAut Y, IsUnitaryAut u ∧ localDeltaTwoIn H B' = Subgroup.zpowers u

theorem input19_16_twoLp_of_input19_16_two (h : Lemma123.Input19_16_two) : Input19_16_twoLp := by
  intro p hp hp2 Y _ _ hY hO hchev _ B' hB'el hB'c hnb
  obtain ⟨hp3, hL, -, hinn, hu⟩ := h p hp hp2 Y hY hO hchev 2 B' le_rfl hB'el hB'c hnb
  exact ⟨hp3, hL, hinn, hu⟩

theorem input19_16_two_of_ys (h02 : LocalThreeBalanceCrossChar)
    (h03 : CFSG.Yardstones.M67c2c3e09a6b.LocalTwoBalanceThreeFive) (h04 : LocalTwoBalanceCrossCharGtFive)
    (hd3 : LocalTwoBalanceDefCharThree) (hd5 : LocalTwoBalanceDefCharFive) (hd7 : LocalTwoBalanceDefCharGtFive)
    (hLp : Input19_16_twoLp) : Lemma123.Input19_16_two := by
  intro p hp hp2 Y _ _ hY hO hchev k B' hk hB'el hB'c hnb
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
  have hnab := Prop1116Design.not_isCommutative_barQuot Y hY
  have hbal : ∀ k' : ℕ, 1 ≤ k' → k' ≤ k → IsLocallyOTwoBalancedWrtP p k' (Y ⧸ Subgroup.center Y) → False :=
    fun k' h1 hk' h => hnb (Lemma123.isLocallyOTwoBalanced_of_le hp h1 hk'
      (Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hY.1 h B' hB'el))
  rcases chevSimple_two_cases hchev with ⟨idx, he⟩ | he | he | he
  · obtain ⟨h3, h2⟩ := lie_balance h02 h03 h04 hd3 hd5 hd7 hp hp2 hY.2 hnab idx he
    by_cases hch : idx.1.characteristic = p
    · exact (hbal 2 (by norm_num) hk (h2 (Or.inl hch))).elim
    · have hk2 : k = 2 := by
        by_contra hk2
        exact hbal 3 (by norm_num) (by omega) (h3 hch)
      subst hk2
      by_cases hL : ∃ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 ∧
          Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie idx').Group)
      · obtain ⟨hp3, hL34, hinn, hunit⟩ := hLp p hp hp2 Y hY hO hchev hL B' hB'el hB'c hnb
        exact ⟨hp3, hL34, rfl, hinn, hunit⟩
      · exfalso
        refine hbal 2 (by norm_num) le_rfl (h2 (Or.inr fun idx' h => not_nonempty_iff.1 fun hn => hL ⟨idx', h, hn⟩))
  · exact (false_of_alt_quot hY.1 hp hp2 hk B' hB'c (Or.inl he)).elim
  · by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨e⟩ := he
      exact (hbal 1 le_rfl (by omega)
        ((Inputs123a.isLocallyOTwoBalancedWrtP_congr e).2 Inputs123a.balanced_alt6_three)).elim
    · exact (false_of_alt_quot hY.1 hp hp2 hk B' hB'c (Or.inr ⟨hp3, he⟩)).elim
  · obtain ⟨e⟩ := he
    have h1 := card_dvd_card_mulAut_of_quot hY.1 e B'
    rw [hB'c, card_mulAut_alt8] at h1
    obtain ⟨rfl, rfl⟩ := eq_three_of_pow_dvd_alt8 hp hp2 hk h1
    exact (hbal 2 (by norm_num) le_rfl
      ((Inputs123a.isLocallyOTwoBalancedWrtP_congr e).2 input19_8_A8_holds)).elim

end ChevTwo

section ChevThree

@[expose] def Input7_1Chev3 : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    Prop1116Design.IsLieOverField 3 S → ∀ x : MulAut S, x ^ p = 1 → x ∈ innerAut S

@[expose] def Input19_18Inner : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    Prop1116Design.IsLieOverField 3 S → ∀ x y : MulAut S, x ∈ innerAut S → y ∈ innerAut S →
      orderOf x = p → y ^ p = 1 → x * y = y * x →
        ∀ t ∈ pCoreOf 2 (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))), y * t = t * y

@[expose] def Input19_18b : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsLpType 3 (3 ^ 13) S → IsWeaklyLocallyOTwoBalancedWrtP 13 1 S

theorem input19_18b_of_input19_18S (h : Inputs123a.Input19_18S) : Input19_18b :=
  fun S _ _ hL => h 13 (by norm_num) (by norm_num) S (Or.inr ⟨rfl, hL⟩)

theorem conj_pow_eq {G : Type*} [Group G] {a t c : G} (hc : a * t * a⁻¹ = c * t) (hac : a * c = c * a)
    (n : ℕ) : a ^ n * t * (a ^ n)⁻¹ = c ^ n * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcn : a * c ^ n = c ^ n * a := (Commute.pow_right (hac : Commute a c) n).eq
    calc a ^ (n + 1) * t * (a ^ (n + 1))⁻¹ = a * (a ^ n * t * (a ^ n)⁻¹) * a⁻¹ := by group
      _ = a * (c ^ n * t) * a⁻¹ := by rw [ih]
      _ = (a * c ^ n) * t * a⁻¹ := by group
      _ = c ^ n * (a * t * a⁻¹) := by rw [hcn]; group
      _ = c ^ (n + 1) * t := by rw [hc]; group

theorem isWeaklyLocallyOTwoBalancedWrtP_of_inner {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hinn : ∀ x : MulAut K, x ^ p = 1 → x ∈ innerAut K)
    (hcomm : ∀ x y : MulAut K, x ∈ innerAut K → y ∈ innerAut K → orderOf x = p → y ^ p = 1 → x * y = y * x →
      ∀ t ∈ pCoreOf 2 (innerAut K ⊓ Subgroup.centralizer ({x} : Set (MulAut K))), y * t = t * y) :
    IsWeaklyLocallyOTwoBalancedWrtP p 1 K := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A hA D hD H hH hAH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hDc
    exact hp.one_lt.ne hDc
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdo : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1'
  have hDeq : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
      (by rw [Nat.card_zpowers, hdo, hDc, pow_one])).symm
  have hT : localDeltaTwoIn H D = pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut K))) := by
    rw [hDeq, Inputs123a.localDeltaTwoIn_zpowers hp hdo]
  have hdI : d ∈ innerAut K := hinn d (hDel.2 d hdD)
  have hInnN : (innerAut K).Normal := Lemma123.innerAut_normal K
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer ((localDeltaTwoIn H D : Subgroup (MulAut K)) :
      Set (MulAut K)) := fun a ha =>
    Lemma123.mem_normalizer_localDeltaTwoIn (hAH ha) fun e he =>
      CFSG.Open.IsElemAbelian.comm hA ha (hDA he)
  have hT0 : localDeltaTwoIn H D ⊓ innerAut K ≤
      pCoreOf 2 (innerAut K ⊓ Subgroup.centralizer ({d} : Set (MulAut K))) := by
    rw [hT]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact le_inf inf_le_right ((inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans inf_le_right)
    · intro g hg
      have hgH : g ∈ H ⊓ Subgroup.centralizer ({d} : Set (MulAut K)) :=
        Subgroup.mem_inf.2 ⟨hH (Subgroup.mem_inf.1 hg).1, (Subgroup.mem_inf.1 hg).2⟩
      exact Lemma123.mem_normalizer_inf'
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer hgH))
        (Subgroup.le_normalizer (Subgroup.mem_inf.1 hg).1)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hT2 : IsPGroup 2 ↥(localDeltaTwoIn H D) := by
    rw [hT]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro t ht a ha
  rw [Subgroup.mem_bot, commutatorElement_def]
  have hap : a ^ p = 1 := hA.2 a ha
  have haI : a ∈ innerAut K := hinn a hap
  have had : d * a = a * d := CFSG.Open.IsElemAbelian.comm hA (hDA hdD) ha
  set c := a * t * a⁻¹ * t⁻¹ with hcdef
  have hcT : c ∈ localDeltaTwoIn H D :=
    (localDeltaTwoIn H D).mul_mem ((Subgroup.mem_normalizer_iff.1 (hAN a ha) t).1 ht)
      ((localDeltaTwoIn H D).inv_mem ht)
  have hcI : c ∈ innerAut K := by
    have h1 : t * a⁻¹ * t⁻¹ ∈ innerAut K := hInnN.conj_mem _ ((innerAut K).inv_mem haI) t
    have h2 := (innerAut K).mul_mem haI h1
    rw [hcdef]
    simpa [mul_assoc] using h2
  have hac : a * c = c * a := hcomm d a hdI haI hdo hap had c (hT0 ⟨hcT, hcI⟩)
  have hconj : a * t * a⁻¹ = c * t := by rw [hcdef]; group
  have hpow := conj_pow_eq hconj hac p
  rw [hap, one_mul, inv_one, mul_one] at hpow
  have hcp : c ^ p = 1 := by
    have h1 := congrArg (· * t⁻¹) hpow
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h1
    exact h1.symm
  obtain ⟨m, hm⟩ := hT2 ⟨c, hcT⟩
  have hcm : c ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime p (2 ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hc1 : c = 1 := orderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_of_pow_eq_one hcm))
  have hat : a * t = t * a := by
    have h1 : a * t * a⁻¹ * t⁻¹ = 1 := hc1
    calc a * t = (a * t * a⁻¹ * t⁻¹) * (t * a) := by group
      _ = t * a := by rw [h1, one_mul]
  calc t * a * t⁻¹ * a⁻¹ = (a * t) * t⁻¹ * a⁻¹ := by rw [hat]
    _ = 1 := by group

theorem input19_18S_of (hOut : Input7_1Chev3) (hInner : Input19_18Inner) (hb : Input19_18b) :
    Inputs123a.Input19_18S := by
  intro p hp hp3 S _ _ hS
  rcases hS with ⟨hsimp, hlie⟩ | ⟨rfl, hL⟩
  · exact isWeaklyLocallyOTwoBalancedWrtP_of_inner hp (by omega) (hOut p hp hp3 S hsimp hlie)
      (hInner p hp hp3 S hsimp hlie)
  · exact hb S hL

end ChevThree

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceFromYS
