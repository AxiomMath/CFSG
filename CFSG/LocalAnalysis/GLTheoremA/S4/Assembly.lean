module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma42
public import CFSG.LocalAnalysis.GLTheoremA.S4.CycMax
public import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def Lemma43At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L →
    ¬ B ≤ Subgroup.normalizer (L : Set G) →
    ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G),
      Relation.ReflTransGen (PumpRel p) (B, x, L) (B', x', L') ∧
      B' ≤ Subgroup.normalizer (L' : Set G) ∧ IsGB p B' L'

@[expose] def Lemma47At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ t t' : Triple G, PumpRel p t t' →
    ¬ nGen t.1 (closureIn t.2.2 t.1) ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({t.2.1} : Set G)) →
    ¬ nGen t'.1 (closureIn t'.2.2 t'.1) ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({t'.2.1} : Set G))

@[expose] def Lemma49At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ t t' : Triple G, PumpRel p t t' →
    min 4 (fullCoverLevel p (PQuot p t.2.2)) ≤
      min 4 (fullCoverLevel p (PQuot p t'.2.2)) ∧
      (IsGStar p t.1 t.2.2 → IsGStar p t'.1 t'.2.2)

variable {G : Type} [Group G] [Finite G]

private theorem dvd_card_pQuot_of_glaPComponent {p : ℕ} (hp : p.Prime) {X H : Subgroup G}
    (hH : GLAPComponent p X H) : p ∣ Nat.card (PQuot p H) := by
  by_contra hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (PQuot p H) := isQuasisimple_nontrivial
    (isQuasisimple_pQuot_of_glaPComponent hp hH)
  have hKc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥H)) := CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card ↥H = Nat.card (PQuot p H) * Nat.card (GLAPPrimeCore p ↥H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥H)) := by
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd) hKc
  have htop : (⊤ : Subgroup ↥H) ≤ GLAPPrimeCore p ↥H := le_sSup ⟨inferInstance, hcop⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : PQuot p H)
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  exact hx ((QuotientGroup.eq_one_iff h).2 (htop (Subgroup.mem_top h)))

private theorem exists_pow_eq_one_noncomm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X K : Subgroup G}
    (hK : GLAPComponent p X K) : ∃ w ∈ K, w ^ p = 1 ∧ ∃ k ∈ K, k * w ≠ w * k := by
  haveI : Fact p.Prime := ⟨hp⟩
  let π : ↥K →* PQuot p K := QuotientGroup.mk' (GLAPPrimeCore p ↥K)
  have hKc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨yb, hyord, hycen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      (isQuasisimple_pQuot_of_glaPComponent hp hK) hp hp2 (dvd_card_pQuot_of_glaPComponent hp hK)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hpy : π y ^ p = 1 := by
    have h := pow_orderOf_eq_one (π y)
    have hyord' : orderOf (π y) = p := hyord
    rwa [hyord'] at h
  obtain ⟨a, m, hm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  set v : ↥K := y ^ m with hv
  have hπv : π v = π y ^ m := by rw [hv, map_pow]
  have hvK : v ^ p ∈ GLAPPrimeCore p ↥K := by
    have : π (v ^ p) = 1 := by
      rw [map_pow, hπv, ← pow_mul, mul_comm, pow_mul, hpy, one_pow]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hpow : (v ^ p) ^ (p ^ a) = 1 := by
    have h1 : y ^ (p ^ a * m) = 1 := hkm ▸ pow_orderOf_eq_one y
    calc (v ^ p) ^ (p ^ a) = (y ^ (p ^ a * m)) ^ p := by
          rw [hv, ← pow_mul, ← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [h1, one_pow]
  have hv1 : v ^ p = 1 := by
    have h1 : orderOf (v ^ p) ∣ p ^ a := orderOf_dvd_of_pow_eq_one hpow
    have h2 : orderOf (v ^ p) ∣ Nat.card (GLAPPrimeCore p ↥K) :=
      Subgroup.orderOf_dvd_natCard _ hvK
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hKc)] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  refine ⟨(v : G), v.2, ?_, ?_⟩
  · exact_mod_cast hv1
  by_contra hcon
  push Not at hcon
  have hvcomm : ∀ k : ↥K, k * v = v * k := fun k => Subtype.ext (hcon (k : G) k.2)
  have hπvc : π v ∈ Subgroup.center (PQuot p K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥K) q
    show π k * π v = π v * π k
    rw [← map_mul, ← map_mul, hvcomm k]
  rw [hπv] at hπvc
  obtain ⟨s, t, hst⟩ := Nat.Coprime.isCoprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have e : (1 : ℤ) = (p : ℤ) * s + (m : ℤ) * t := by linarith [hst]
  have hfin : π y = (π y ^ m) ^ t := by
    calc π y = π y ^ (1 : ℤ) := (zpow_one _).symm
      _ = π y ^ ((p : ℤ) * s + (m : ℤ) * t) := by rw [← e]
      _ = (π y ^ m) ^ t := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hpy, one_zpow, one_mul]
  have hyc : π y ∈ Subgroup.center (PQuot p K) := by
    rw [hfin]
    exact Subgroup.zpow_mem _ hπvc t
  exact hycen hyc

theorem le_normalizer_of_cycModSylow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B L : Subgroup G}
    {x : G} (hS : IsSTriple p B x L) (hcyc : CycModSylow p L) :
    B ≤ Subgroup.normalizer (L : Set G) := by
  intro b hbB
  by_contra hbN
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hBC : B ≤ Subgroup.centralizer ({x} : Set G) := isElemAbelian_le_centralizer hS.1.1 hxB
  have hLc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := hS.2.2
  have hbN' : b ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (hBC hbB)
  have hKc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) (GLBConj b L) := by
    have h := glaPComponent_gLBConj hLc b
    rwa [mem_normalizer_iff_gLBConj_eq.1 hbN'] at h
  have hKL : GLBConj b L ≠ L := fun h => hbN (mem_normalizer_iff_gLBConj_eq.2 h)
  have hKCm : GLBConj b L ≤ centModSubgroup p L := le_centModSubgroup_of_ne hp hKc hLc hKL
  have hxL : x ∈ centModSubgroup p L :=
    centMod_iff.1 (centMod_of_mem_centralizer (IsSTriple.mem_centralizer hS))
  obtain ⟨w, hwK, hwp, k, hkK, hkw⟩ := exists_pow_eq_one_noncomm hp hp2 hKc
  have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.1 (hKc.1 hkK)
  have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hKc.1 hwK)
  have hwnx : w ∉ Subgroup.zpowers x := by
    intro hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact hkw (hkx.zpow_right n).eq
  obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hwx hwp hxp hx1 hwnx
  have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x ≤ centModSubgroup p L :=
    sup_le (Subgroup.zpowers_le.2 (hKCm hwK)) (Subgroup.zpowers_le.2 hxL)
  have hcycS : IsCyclic (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) :=
    hcyc (Subgroup.zpowers w ⊔ Subgroup.zpowers x) (fun g hg => centMod_iff.2 (hle hg))
      (isPGroup_of_isElemAbelian hE)
  have hdiv : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) ≤ p :=
    card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
  rw [hcard] at hdiv
  have h2 := hp.two_le
  nlinarith

theorem tripleLevel_le_five' (p : ℕ) (B L : Subgroup G) : tripleLevel p B L ≤ 5 := by
  classical
  unfold tripleLevel
  by_cases h : IsGStar p B L
  · rw [if_pos h]
  · rw [if_neg h]
    exact (Nat.min_le_left 4 _).trans (by norm_num)

theorem tripleLevel_le_dLevel {p : ℕ} {B L : Subgroup G} {x : G} (hS : IsSTriple p B x L) :
    tripleLevel p B L ≤ dLevel G p :=
  le_csSup ⟨5, by
    rintro j ⟨B', x', L', -, rfl⟩
    exact tripleLevel_le_five' p B' L'⟩ ⟨B, x, L, hS, rfl⟩

theorem kLevel_le_four (p : ℕ) (S : Type) [Group S] : kLevel p S ≤ 4 := by
  unfold kLevel
  split_ifs <;> omega

theorem tripleLevel_le_of_pumpRel {p : ℕ} (h49 : Lemma49At G p) {t t' : Triple G}
    (hrel : PumpRel p t t') : tripleLevel p t.1 t.2.2 ≤ tripleLevel p t'.1 t'.2.2 := by
  obtain ⟨hk, hg⟩ := h49 t t' hrel
  unfold tripleLevel
  by_cases h : IsGStar p t.1 t.2.2
  · rw [if_pos h, if_pos (hg h)]
  · rw [if_neg h]
    split_ifs
    · exact (Nat.min_le_left 4 _).trans (by norm_num)
    · exact hk

theorem isS0_of_reflTransGen {p : ℕ} (h49 : Lemma49At G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') (ht : IsS0 p t.1 t.2.1 t.2.2) :
    IsS0 p t'.1 t'.2.1 t'.2.2 := by
  induction h with
  | refl => exact ht
  | @tail u u' _ hstep ih =>
    refine ⟨hstep.2.1, le_antisymm (tripleLevel_le_dLevel hstep.2.1) ?_⟩
    rw [← ih.2]
    exact tripleLevel_le_of_pumpRel h49 hstep

theorem lemma410 {p : ℕ} (hc : S4Ctx G p) (h49 : Lemma49At G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') :
    (IsS0 p t.1 t.2.1 t.2.2 → IsS0 p t'.1 t'.2.1 t'.2.2) ∧
      (IsS0Max p t.1 t.2.1 t.2.2 → IsS0Max p t'.1 t'.2.1 t'.2.2) := by
  refine ⟨isS0_of_reflTransGen h49 h, fun ht => ?_⟩
  obtain ⟨-, hmax', hN⟩ := lemma41_max hc h ht.2.1
  exact ⟨isS0_of_reflTransGen h49 h ht.1, hmax', hN ht.2.2⟩

theorem exists_isS0Max_reflTransGen {p : ℕ} (hc : S4Ctx G p) (h43 : Lemma43At G p)
    (h49 : Lemma49At G p) {B L : Subgroup G} {x : G} (ht : IsS0 p B x L) :
    ∃ (B' : Subgroup G) (x' : G) (L' : Subgroup G), IsS0Max p B' x' L' ∧
      Relation.ReflTransGen (PumpRel p) (B, x, L) (B', x', L') := by
  obtain ⟨t', ht', hmax⟩ := exists_isSMax_reflTransGen hc (t := (B, x, L)) ht.1
  by_cases hN : t'.1 ≤ Subgroup.normalizer (t'.2.2 : Set G)
  · exact ⟨t'.1, t'.2.1, t'.2.2, ⟨isS0_of_reflTransGen h49 ht' ht, hmax, hN⟩, ht'⟩
  · obtain ⟨B'', x'', L'', h', hN'', -⟩ := h43 t'.1 t'.2.1 t'.2.2 hmax.1 hN
    have hall := ht'.trans h'
    exact ⟨B'', x'', L'', ⟨isS0_of_reflTransGen h49 hall ht,
      (lemma41_max hc h' hmax).2.1, hN''⟩, hall⟩

theorem lemma412 {p : ℕ} (h43 : Lemma43At G p) (hd : dLevel G p ≤ 4) {B L : Subgroup G} {x : G}
    (hS : IsSTriple p B x L) : B ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hN
  obtain ⟨B', x', L', h', hN', hGB⟩ := h43 B x L hS hN
  have hS' : IsSTriple p B' x' L' := by
    rcases Relation.ReflTransGen.cases_tail h' with heq | ⟨u, -, hstep⟩
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hS
    · exact hstep.2.1
  have hGS : IsGStar p B' L' := by
    obtain ⟨E, hEB, hE, hEc, -, hEL⟩ := hGB
    exact ⟨E, hEB, hE, hEc, by rwa [closureIn_eq_self hN']⟩
  have h5 : tripleLevel p B' L' = 5 := by
    unfold tripleLevel
    rw [if_pos hGS]
  have := tripleLevel_le_dLevel hS'
  omega

theorem stage4Order_of {p : ℕ} (hc : S4Ctx G p) (hp2 : p ≠ 2) (h43 : Lemma43At G p)
    (h47 : Lemma47At G p) (h49 : Lemma49At G p) : Stage4Order G p := by
  refine ⟨fun t t' h => lemma41_card hc h.2.2,
    fun t t' h hmax => lemma41_max hc h.2.2 hmax,
    fun B x L ht => ?_,
    fun B x L hS hcyc => isSMax_of_cycModSylow hc.prime hS hcyc,
    fun B x L ht hcyc => ⟨ht, isSMax_of_cycModSylow hc.prime ht.1 hcyc,
      le_normalizer_of_cycModSylow hc.prime hp2 ht.1 hcyc⟩,
    fun t t' h => ?_, fun t t' h => lemma410 hc h49 h.2.2,
    fun hd B x L hS => lemma412 h43 hd hS⟩
  · obtain ⟨nextB, nextX, nextL, hmax, hchain⟩ :=
      exists_isS0Max_reflTransGen hc h43 h49 ht
    exact ⟨nextB, nextX, nextL, hmax, pumpLe_of_reflTransGen ht.1 hchain⟩
  · obtain ⟨hstart, hfinish, hchain⟩ := h
    clear hstart hfinish
    induction hchain with
    | refl => exact id
    | tail _ hstep ih => exact fun hn => h47 _ _ hstep (ih hn)

end CFSG.LocalAnalysis.GLTheoremA
