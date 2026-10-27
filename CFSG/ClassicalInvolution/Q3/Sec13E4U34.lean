module

public import CFSG.ClassicalInvolution.Q3.Sec13E4Shult
public import CFSG.Goldschmidt.Steps.G76U34

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace U34

private theorem mem_normalizer_of_conj_mem {M : Type*} [Group M] [Finite M] {H : Subgroup M}
    {g : M} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set M) := by
  have hS : H.map (MulAut.conj g).toMonoidHom = H := by
    refine Subgroup.eq_of_le_of_card_ge ?_
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← hS] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
  have : x = y := by
    have := congrArg (fun z => g⁻¹ * z * g) hyx
    simpa [mul_assoc] using this.symm
  rw [this]
  exact hy

private theorem exists_pow_sq_eq {M : Type*} [Group M] {y : M} (hy : Odd (orderOf y)) :
    ∃ j : ℕ, (y ^ 2) ^ j = y := by
  obtain ⟨j, hj⟩ := hy
  refine ⟨j + 1, ?_⟩
  rw [← pow_mul]
  have h1 : y ^ (2 * (j + 1)) = y ^ orderOf y * y := by
    rw [hj, ← pow_succ]
    congr 1
  rw [h1, pow_orderOf_eq_one, one_mul]

private theorem exists_odd_lift {M N : Type*} [Group M] [Finite M] [Group N] (f : M →* N)
    (hf : Function.Surjective f) {x : N} (hx : Odd (orderOf x)) :
    ∃ y : M, f y = x ∧ Odd (orderOf y) := by
  obtain ⟨y₀, rfl⟩ := hf x
  have : Finite N := Finite.of_surjective f hf
  set n := orderOf y₀ with hn
  have hnpos : 0 < n := orderOf_pos y₀
  set a := n.factorization 2 with ha
  set d := n / 2 ^ a with hd
  have hnd : 2 ^ a * d = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hdodd : Odd d := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hnpos.ne')
  set m := orderOf (f y₀) with hm
  have hmpos : 0 < m := orderOf_pos _
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hx)
  have ht1 : (2 ^ a) ^ m.totient ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
  have htdvd : 2 ^ a ∣ (2 ^ a) ^ m.totient :=
    dvd_pow_self _ (Nat.totient_pos.mpr hmpos).ne'
  obtain ⟨u, hu⟩ := htdvd
  refine ⟨y₀ ^ ((2 ^ a) ^ m.totient), ?_, ?_⟩
  · rw [map_pow]
    have : (f y₀) ^ ((2 ^ a) ^ m.totient) = (f y₀) ^ 1 := pow_eq_pow_iff_modEq.mpr ht1
    simpa using this
  · refine Odd.of_dvd_nat hdodd ?_
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (2 ^ a) ^ m.totient * d = n * u := by rw [hu, ← hnd]; ring
    have h2 : y₀ ^ n = 1 := pow_orderOf_eq_one y₀
    rw [← pow_mul, h1, pow_mul, h2, one_pow]

private theorem exists_odd_part {L : Type*} [Group L] [Finite L] (P : Sylow 2 L) {r : L}
    (hr : r ∈ Subgroup.normalizer ((P : Subgroup L) : Set L)) :
    ∃ y : L, y ∈ Subgroup.zpowers r ∧ Odd (orderOf y) ∧
      r ∈ Subgroup.zpowers y ⊔ (P : Subgroup L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := orderOf r with hn
  have hnpos : 0 < n := orderOf_pos r
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hm
  have hnm : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hmodd : Odd m := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hnpos.ne')
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hmodd)
  have hrN : Subgroup.zpowers r ≤ Subgroup.normalizer ((P : Subgroup L) : Set L) :=
    Subgroup.zpowers_le.mpr hr
  have hs : r ^ m ∈ (P : Subgroup L) := by
    have hsN : Subgroup.zpowers (r ^ m) ≤ Subgroup.normalizer ((P : Subgroup L) : Set L) :=
      Subgroup.zpowers_le.mpr (hrN (Subgroup.pow_mem _ (Subgroup.mem_zpowers r) m))
    have hs2 : (r ^ m) ^ (2 ^ a) = 1 := by
      rw [← pow_mul, mul_comm, hnm]
      exact pow_orderOf_eq_one r
    have hzp : IsPGroup 2 (Subgroup.zpowers (r ^ m)) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hs2)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hsup : IsPGroup 2 ↥((P : Subgroup L) ⊔ Subgroup.zpowers (r ^ m)) :=
      P.isPGroup'.to_sup_of_normal_left' hzp hsN
    have heq := P.is_maximal' hsup le_sup_left
    have : r ^ m ∈ (P : Subgroup L) ⊔ Subgroup.zpowers (r ^ m) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rwa [heq] at this
  refine ⟨r ^ (2 ^ a), Subgroup.pow_mem _ (Subgroup.mem_zpowers r) _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (Nat.ordProj_dvd _ _)]
    exact hmodd
  · have hg := Nat.gcd_eq_gcd_ab (2 ^ a) m
    rw [hcop.gcd_eq_one] at hg
    have hrr : r = (r ^ (2 ^ a)) ^ Nat.gcdA (2 ^ a) m * (r ^ m) ^ Nat.gcdB (2 ^ a) m := by
      rw [← zpow_natCast, ← zpow_natCast r m, ← zpow_mul, ← zpow_mul, ← zpow_add]
      have : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
        rw [← hg]; rfl
      rw [this, zpow_one]
    have hmem : (r ^ (2 ^ a)) ^ Nat.gcdA (2 ^ a) m * (r ^ m) ^ Nat.gcdB (2 ^ a) m ∈
        Subgroup.zpowers (r ^ (2 ^ a)) ⊔ (P : Subgroup L) :=
      Subgroup.mul_mem _
        (Subgroup.zpow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
        (Subgroup.zpow_mem _ (Subgroup.mem_sup_right hs) _)
    rwa [← hrr] at hmem

private theorem le_normalizer_commutator_left {M : Type*} [Group M] [Finite M]
    (A B : Subgroup M) : A ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup M) : Set M) := by
  intro c hc
  apply mem_normalizer_of_conj_mem
  intro x hx
  have h1 : ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show c * ⁅a, b⁆ * c⁻¹ ∈ ⁅A, B⁆
    have : c * ⁅a, b⁆ * c⁻¹ = ⁅c * a, b⁆ * ⁅c, b⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (A.mul_mem hc ha) hb)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hc hb))
  exact h1 hx

private theorem le_normalizer_commutator_right {M : Type*} [Group M] [Finite M]
    (A B : Subgroup M) : B ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup M) : Set M) := by
  rw [Subgroup.commutator_comm]
  exact le_normalizer_commutator_left B A

private theorem psu34_odd_part
    {L : Type} [Group L] [Finite L] (e : L ≃* PSU3 2 2) (P : Sylow 2 L) {E : Subgroup L}
    (hEP : E ≤ (P : Subgroup L)) (hE4 : Nat.card E = 4) (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hΩ : ∀ x ∈ (P : Subgroup L), x ^ 2 = 1 → x ∈ E) :
    E = (P : Subgroup L) ⊓ Subgroup.centralizer ((P : Subgroup L) : Set L) ∧
      ∃ y : L, Odd (orderOf y) ∧ y ∈ Subgroup.normalizer ((P : Subgroup L) : Set L) ∧
        (∀ z ∈ E, y * z = z * y) ∧
        ⁅(P : Subgroup L), Subgroup.zpowers y⁆ = (P : Subgroup L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup L := by
    have := CFSG.ShultStronglyClosedTI.unitaryCover_native_simple 2 le_rfl
    exact e.isSimpleGroup
  have hnab : ¬ IsMulCommutative L := by
    intro hc
    have hp : (Nat.card L).Prime := Group.is_simple_iff_prime_card.1 hsimple
    have hdvd : Nat.card E ∣ Nat.card L := Subgroup.card_subgroup_dvd_card E
    rw [hE4] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · omega
    · rw [← h] at hp; norm_num at hp
  have hZ : Subgroup.center L = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun ht =>
      hnab (Subgroup.center_eq_top_iff.1 ht)
  let eZ : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hLq : CFSG.Open.IsQuasisimple L :=
    ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun hb =>
        hnab ((commutator_eq_bot_iff L).1 hb), eZ.isSimpleGroup⟩
  obtain ⟨hc64, hcZ4, hcomm, -, r, hrN, hrC, hX⟩ :=
    CFSG.Goldschmidt.G76.psu34_sylow_facts CFSG.Goldschmidt.G32 hLq (eZ.trans e)
      (fun z hz k _ => by rw [hZ, Subgroup.mem_bot] at hz; exact hz) P
  set PP : Subgroup L := (P : Subgroup L) with hPP
  set ZP := PP ⊓ Subgroup.centralizer (PP : Set L) with hZP
  have hrP : ∀ x ∈ PP, r * x * r⁻¹ ∈ PP := fun x hx => (Subgroup.mem_normalizer_iff.mp hrN x).mp hx
  have hEN : PP ≤ Subgroup.normalizer (E : Set L) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    intro x hx
    refine hΩ _ (PP.mul_mem (PP.mul_mem hg (hEP hx)) (PP.inv_mem hg)) ?_
    calc (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hE2 x hx]; group
  have hrEN : r ∈ Subgroup.normalizer (E : Set L) := by
    apply mem_normalizer_of_conj_mem
    intro x hx
    refine hΩ _ (hrP x (hEP hx)) ?_
    calc (r * x * r⁻¹) ^ 2 = r * x ^ 2 * r⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hE2 x hx]; group
  have hEZ : E = ZP := by
    rcases hX E hEP hEN hrEN with h | h
    · exact Subgroup.eq_of_le_of_card_ge h (by rw [hcZ4, hE4])
    · exfalso
      rw [h, hc64] at hE4
      omega
  obtain ⟨y, hyr, hyodd, hry⟩ := exists_odd_part P hrN
  have hyN : y ∈ Subgroup.normalizer (PP : Set L) := (Subgroup.zpowers_le.mpr hrN) hyr
  have hzyN : Subgroup.zpowers y ≤ Subgroup.normalizer (PP : Set L) :=
    Subgroup.zpowers_le.mpr hyN
  refine ⟨hEZ, y, hyodd, hyN, ?_, ?_⟩
  · intro z hz
    rw [hEZ] at hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyr
    exact ((show Commute r z from hrC z hz).zpow_left j).eq
  · set X := ⁅PP, Subgroup.zpowers y⁆ with hXdef
    have hXP : X ≤ PP := by
      rw [hXdef, Subgroup.commutator_le]
      intro p hp g hg
      rw [commutatorElement_def]
      have h1 : g * p⁻¹ * g⁻¹ ∈ PP :=
        (Subgroup.mem_normalizer_iff.mp (hzyN hg) p⁻¹).mp (PP.inv_mem hp)
      have := PP.mul_mem hp h1
      simpa [mul_assoc] using this
    have hPX : PP ≤ Subgroup.normalizer (X : Set L) := le_normalizer_commutator_left _ _
    have hyX : Subgroup.zpowers y ≤ Subgroup.normalizer (X : Set L) :=
      le_normalizer_commutator_right _ _
    have hrX : r ∈ Subgroup.normalizer (X : Set L) := (sup_le hyX hPX) hry
    rcases hX X hXP hPX hrX with h1X | h1X
    · exfalso
      have hZPle : ZP ≤ PP := inf_le_left
      obtain ⟨p, hpP, hpZ⟩ : ∃ p ∈ PP, p ∉ ZP := by
        by_contra hall
        push Not at hall
        have := Subgroup.card_le_of_le (H := PP) (K := ZP) (fun p hp => hall p hp)
        rw [hc64, hcZ4] at this
        omega
      set Y := ZP ⊔ Subgroup.zpowers p with hYdef
      have hYP : Y ≤ PP := sup_le hZPle (Subgroup.zpowers_le.mpr hpP)
      have hZY : ZP ≤ Y := le_sup_left
      have hPY : PP ≤ Subgroup.normalizer (Y : Set L) := by
        intro g hg
        apply mem_normalizer_of_conj_mem
        intro x hx
        have h1 : ⁅g, x⁆ ∈ ZP := hcomm ▸ Subgroup.commutator_mem_commutator hg (hYP hx)
        have : g * x * g⁻¹ = ⁅g, x⁆ * x := by simp only [commutatorElement_def]; group
        rw [this]
        exact Y.mul_mem (hZY h1) hx
      have hyY : y ∈ Subgroup.normalizer (Y : Set L) := by
        apply mem_normalizer_of_conj_mem
        intro x hx
        have h1 : ⁅x, y⁆ ∈ ZP :=
          h1X (Subgroup.commutator_mem_commutator (hYP hx) (Subgroup.mem_zpowers y))
        have : y * x * y⁻¹ = ⁅x, y⁆⁻¹ * x := by simp only [commutatorElement_def]; group
        rw [this]
        exact Y.mul_mem (Y.inv_mem (hZY h1)) hx
      have hrY : r ∈ Subgroup.normalizer (Y : Set L) :=
        (sup_le (Subgroup.zpowers_le.mpr hyY) hPY) hry
      rcases hX Y hYP hPY hrY with h2 | h2
      · exact hpZ (h2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers p)))
      · have hpN : Subgroup.zpowers p ≤ Subgroup.normalizer (ZP : Set L) := by
          rw [Subgroup.zpowers_le]
          apply mem_normalizer_of_conj_mem
          intro x hx
          have h3 := Subgroup.mem_centralizer_iff.mp hx.2 p hpP
          rw [h3, mul_inv_cancel_right]
          exact hx
        have hdec := Subgroup.coe_mul_of_right_le_normalizer_left ZP (Subgroup.zpowers p) hpN
        have habel : ∀ a ∈ PP, ∀ b ∈ PP, a * b = b * a := by
          intro a ha b hb
          have ha' : a ∈ ((ZP ⊔ Subgroup.zpowers p : Subgroup L) : Set L) := by
            rw [← hYdef, h2]; exact ha
          have hb' : b ∈ ((ZP ⊔ Subgroup.zpowers p : Subgroup L) : Set L) := by
            rw [← hYdef, h2]; exact hb
          rw [hdec] at ha' hb'
          obtain ⟨z₁, hz₁, c, hc, rfl⟩ := Set.mem_mul.mp ha'
          obtain ⟨z₂, hz₂, d, hd, rfl⟩ := Set.mem_mul.mp hb'
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
          have hz1c : ∀ g ∈ PP, Commute z₁ g := fun g hg =>
            (Subgroup.mem_centralizer_iff.mp hz₁.2 g hg).symm
          have hz2c : ∀ g ∈ PP, Commute z₂ g := fun g hg =>
            (Subgroup.mem_centralizer_iff.mp hz₂.2 g hg).symm
          have hpi : p ^ i ∈ PP := Subgroup.zpow_mem _ hpP i
          have hpj : p ^ j ∈ PP := Subgroup.zpow_mem _ hpP j
          exact (Commute.mul_left (hz1c _ (PP.mul_mem hz₂.1 hpj))
            (Commute.mul_right (hz2c _ hpi).symm (Commute.zpow_zpow_self p i j))).eq
        have hbot : ⁅PP, PP⁆ = ⊥ := by
          rw [eq_bot_iff, Subgroup.commutator_le]
          intro a ha b hb
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact habel a ha b hb
        rw [hcomm] at hbot
        have : Nat.card ZP = 1 := by rw [hbot]; exact Subgroup.card_bot
        omega
    · exact h1X

private theorem mul_self_eq_one_of_card_le_two {M : Type*} [Group M] [Finite M] {H : Subgroup M}
    (hH : Nat.card H ≤ 2) {c : M} (hc : c ∈ H) : c * c = 1 := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hdvd : orderOf (⟨c, hc⟩ : H) ∣ 2 := by
    have h1 : orderOf (⟨c, hc⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
    have h2 : Nat.card H = 1 ∨ Nat.card H = 2 := by omega
    rcases h2 with h2 | h2
    · rw [h2] at h1
      exact h1.trans (one_dvd _)
    · rw [h2] at h1
      exact h1
  have h4 : (⟨c, hc⟩ : H) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have h5 := congrArg Subtype.val h4
  simpa [pow_two] using h5

end U34

namespace E4Hyp

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
include h

theorem false_of_asymmetric {K J : Subgroup G} (hp : Paired Ω K J) {q : G}
    (hq : q ∈ pCore 2 G) (hqK : q ∈ Subgroup.normalizer (K : Set G))
    (hqJ : ∀ y ∈ J, q * y = y * q) {k : G} (hk : k ∈ K)
    (hqk : ∀ x ∈ K, q * x * q⁻¹ = k * x * k⁻¹) {x : G} (hx : x ∈ K) (hxk : k * x ≠ x * k) :
    False := by
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨L, hL, hLK, hLJ⟩ := h.exists_third hp
  obtain ⟨w, hw⟩ := h.exists_uniqueInvolution hL
  obtain ⟨L', hpL⟩ := h.exists_partner hL
  obtain ⟨w', hw'⟩ := h.exists_uniqueInvolution hpL.2.1
  have hww' : w = w' := h.inv_eq hpL hw hw'
  have hswap : conjSub w K = J := h.swap hp hL hLK hLJ hw
  have hqL : conjSub q L ≤ L ⊔ pCore 2 G := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 : l * q⁻¹ * l⁻¹ ∈ pCore 2 G := (inferInstance : (pCore 2 G).Normal).conj_mem q⁻¹
      ((pCore 2 G).inv_mem hq) l
    have h2 : q * (l * q⁻¹ * l⁻¹) ∈ L ⊔ pCore 2 G :=
      Subgroup.mem_sup_right ((pCore 2 G).mul_mem hq h1)
    have h3 : (MulAut.conj q).toMonoidHom l = (q * (l * q⁻¹ * l⁻¹)) * l := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [h3]
    exact Subgroup.mul_mem _ h2 (Subgroup.mem_sup_left hl)
  have hqw : q * w * q⁻¹ = w := by
    rcases h.eq_or_eq_of_le_sup hpL (h.thmD.hyp.conjInvariant q L hL) hqL with h1 | h1
    · exact hw.conj_eq h1
    · have h2 := hw.conj q
      rw [h1] at h2
      calc q * w * q⁻¹ = w' := h2.eq hw'
        _ = w := hww'.symm
  have hqw' : q * w⁻¹ * q⁻¹ = w⁻¹ := by
    calc q * w⁻¹ * q⁻¹ = (q * w * q⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [hqw]
  have hy : w * x * w⁻¹ ∈ J := hswap ▸ conj_mem_conjSub hx
  have h1 := hqJ _ hy
  have h3 : q * (w * x * w⁻¹) * q⁻¹ = w * (q * x * q⁻¹) * w⁻¹ := by
    calc q * (w * x * w⁻¹) * q⁻¹ = (q * w * q⁻¹) * (q * x * q⁻¹) * (q * w⁻¹ * q⁻¹) := by group
      _ = w * (q * x * q⁻¹) * w⁻¹ := by rw [hqw, hqw']
  have h4 : q * (w * x * w⁻¹) * q⁻¹ = w * x * w⁻¹ := by
    rw [h1]; group
  rw [h3, hqk x hx] at h4
  apply hxk
  have h5 : k * x * k⁻¹ = x := mul_left_cancel (mul_right_cancel h4)
  calc k * x = (k * x * k⁻¹) * k := by group
    _ = x * k := by rw [h5]

private theorem u34_conjSub_eq_or_eq {K J S : Subgroup G} (hp : Paired Ω K J) (hS : IsPGroup 2 S)
    (hKS : K ≤ S) (hJS : J ≤ S) {g : G} (hg : ∀ s ∈ S, g * s * g⁻¹ ∈ S) {M : Subgroup G}
    (hM : M = K ∨ M = J) : conjSub g M = K ∨ conjSub g M = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := hS.exists_le_sylow
  have hMΩ : M ∈ Ω := by
    rcases hM with rfl | rfl
    exacts [hp.1, hp.2.1]
  have hMS : M ≤ S := by
    rcases hM with rfl | rfl
    exacts [hKS, hJS]
  have hle : conjSub g M ≤ S := by
    rintro _ ⟨m, hm, rfl⟩
    exact hg m (hMS hm)
  have hΩ' := h.thmD.hyp.conjInvariant g M hMΩ
  exact h.eq_or_eq_of_paired hp (hKS.trans hS') (hJS.trans hS') hΩ'
    (h.two_lt_card_inf_of_le hΩ' (hle.trans hS'))

private theorem u34_conjSub_eq_of_odd {K J S : Subgroup G} (hp : Paired Ω K J)
    (hS : IsPGroup 2 S) (hKS : K ≤ S) (hJS : J ≤ S) {y : G} (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S)
    (hodd : Odd (orderOf y)) : conjSub y K = K ∧ conjSub y J = J := by
  have hK' := h.u34_conjSub_eq_or_eq hp hS hKS hJS hy (Or.inl rfl)
  have hJ' := h.u34_conjSub_eq_or_eq hp hS hKS hJS hy (Or.inr rfl)
  have hKJ : K ≠ J := hp.2.2.1
  have hK1 : conjSub y K = K := by
    rcases hK' with h1 | h1
    · exact h1
    · exfalso
      have h2 : conjSub y J = K := by
        rcases hJ' with h3 | h3
        · exact h3
        · exact absurd (conjSub_injective y (h1.trans h3.symm)) hKJ
      have h3 : conjSub (y ^ 2) K = K := by
        rw [pow_two, conjSub_mul, h1, h2]
      have h4 : ∀ i : ℕ, conjSub ((y ^ 2) ^ i) K = K := by
        intro i
        induction i with
        | zero => simp
        | succ i ih => rw [pow_succ, conjSub_mul, h3, ih]
      obtain ⟨j, hj⟩ := U34.exists_pow_sq_eq hodd
      have h5 := h4 j
      rw [hj, h1] at h5
      exact hKJ h5.symm
  refine ⟨hK1, ?_⟩
  rcases hJ' with h1 | h1
  · exact absurd (conjSub_injective y (h1.trans hK1.symm)) hKJ.symm
  · exact h1

private theorem u34_centralizes_of_odd {M : Subgroup G} (hM : M ∈ Ω) {y : G}
    (hodd : Odd (orderOf y)) (hyM : conjSub y M = M)
    (hc : ∀ m ∈ M, y * m * y⁻¹ * m⁻¹ ∈ pCore 2 G) : ∀ m ∈ M, y * m = m * y := by
  obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hM
  have hcard := h.card_inf_pCore_le hM
  have hyz : y * z * y⁻¹ = z := hz.conj_eq hyM
  have hsq : ∀ m ∈ M, y * (y * m * y⁻¹) * y⁻¹ = m := by
    intro m hm
    have hym : y * m * y⁻¹ ∈ M := by
      have := conj_mem_conjSub (n := y) hm
      rwa [hyM] at this
    have hcM : y * m * y⁻¹ * m⁻¹ ∈ M := M.mul_mem hym (M.inv_mem hm)
    have hc2 : (y * m * y⁻¹ * m⁻¹) * (y * m * y⁻¹ * m⁻¹) = 1 :=
      U34.mul_self_eq_one_of_card_le_two hcard (show _ ∈ M ⊓ pCore 2 G from ⟨hcM, hc m hm⟩)
    rcases hz.unique _ hcM hc2 with h1 | h1
    · have h2 : y * m * y⁻¹ = m := by
        calc y * m * y⁻¹ = (y * m * y⁻¹ * m⁻¹) * m := by group
          _ = m := by rw [h1, one_mul]
      rw [h2, h2]
    · have h2 : y * m * y⁻¹ = z * m := by
        calc y * m * y⁻¹ = (y * m * y⁻¹ * m⁻¹) * m := by group
          _ = z * m := by rw [h1]
      rw [h2]
      calc y * (z * m) * y⁻¹ = (y * z * y⁻¹) * (y * m * y⁻¹) := by group
        _ = z * (z * m) := by rw [hyz, h2]
        _ = (z * z) * m := by group
        _ = m := by rw [hz.sq, one_mul]
  intro m hm
  have hcomm2 : Commute (y ^ 2) m := by
    show y ^ 2 * m = m * y ^ 2
    calc y ^ 2 * m = (y * (y * m * y⁻¹) * y⁻¹) * y ^ 2 := by simp only [pow_two]; group
      _ = m * y ^ 2 := by rw [hsq m hm]
  obtain ⟨j, hj⟩ := U34.exists_pow_sq_eq hodd
  have := hcomm2.pow_left j
  rw [hj] at this
  exact this.eq

theorem not_psu34
    {K : Subgroup G} (hK : K ∈ Ω) : ¬ Nonempty (G ⧸ pCore 2 G ≃* PSU3 2 2) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨-, Pb, hPb, hΩb⟩ := h.quot_cases hK
  obtain ⟨J, hp⟩ := h.exists_partner hK
  set π := QuotientGroup.mk' (pCore 2 G) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hidx : ¬ 2 ∣ Pb.index := by
    have h1 : (Pb.subgroupOf ⊤).index = Pb.index := Subgroup.relIndex_top_right Pb
    rw [← h1]
    exact hPb.2.2
  let P : Sylow 2 (G ⧸ pCore 2 G) := hPb.2.1.toSylow hidx
  have hbJ : bar J = bar K := (h.bar_eq_of_paired hp).symm
  obtain ⟨-, yb, hybodd, hybN, hybc, hybX⟩ := U34.psu34_odd_part e P (E := bar K) hΩb.1
    (h.card_bar hK) (h.isElemAbelian_bar hK).2 hΩb.2
  obtain ⟨y, hyπ, hyodd⟩ := U34.exists_odd_lift π hπs hybodd
  set S : Subgroup G := Pb.comap π with hSdef
  have hSp : IsPGroup 2 S := by
    refine IsPGroup.comap_of_ker_isPGroup hPb.2.1 π ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hKS : K ≤ S := fun x hx => hΩb.1 ⟨x, hx, rfl⟩
  have hJS : J ≤ S := by
    intro x hx
    have h1 : π x ∈ bar J := ⟨x, hx, rfl⟩
    rw [hbJ] at h1
    exact hΩb.1 h1
  have hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro s hs
    show π (y * s * y⁻¹) ∈ Pb
    rw [map_mul, map_mul, map_inv, hyπ]
    exact (Subgroup.mem_normalizer_iff.mp hybN (π s)).mp hs
  obtain ⟨hyK, hyJ⟩ := h.u34_conjSub_eq_of_odd hp hSp hKS hJS hyS hyodd
  have hcen : ∀ m : G, π m ∈ bar K → y * m * y⁻¹ * m⁻¹ ∈ pCore 2 G := by
    intro m hm
    have h2 : π (y * m * y⁻¹ * m⁻¹) = 1 := by
      rw [← commutatorElement_def, map_commutatorElement, hyπ]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hybc _ hm)
    exact (QuotientGroup.eq_one_iff _).mp h2
  have hyK' : ∀ m ∈ K, y * m = m * y :=
    h.u34_centralizes_of_odd hK hyodd hyK (fun m hm => hcen m ⟨m, hm, rfl⟩)
  have hyJ' : ∀ m ∈ J, y * m = m * y := by
    refine h.u34_centralizes_of_odd hp.2.1 hyodd hyJ (fun m hm => hcen m ?_)
    have h1 : π m ∈ bar J := ⟨m, hm, rfl⟩
    rwa [hbJ] at h1
  set D : Subgroup G := Subgroup.centralizer (K : Set G) ⊓ Subgroup.centralizer (J : Set G)
    with hD
  have hyD : y ∈ D :=
    ⟨Subgroup.mem_centralizer_iff.mpr fun m hm => (hyK' m hm).symm,
      Subgroup.mem_centralizer_iff.mpr fun m hm => (hyJ' m hm).symm⟩
  have hperm : ∀ s ∈ S, ∀ m : G, (m ∈ K ∨ m ∈ J) → (s⁻¹ * m * s ∈ K ∨ s⁻¹ * m * s ∈ J) := by
    intro s hs m hm
    have hsinv : ∀ t ∈ S, s⁻¹ * t * s⁻¹⁻¹ ∈ S := by
      intro t ht
      rw [inv_inv]
      exact S.mul_mem (S.mul_mem (S.inv_mem hs) ht) hs
    rcases hm with hm | hm
    · have hmem : s⁻¹ * m * s ∈ conjSub s⁻¹ K := by
        have := conj_mem_conjSub (n := s⁻¹) hm
        rwa [inv_inv] at this
      rcases h.u34_conjSub_eq_or_eq hp hSp hKS hJS hsinv (Or.inl rfl) with h1 | h1
      · left; rwa [h1] at hmem
      · right; rwa [h1] at hmem
    · have hmem : s⁻¹ * m * s ∈ conjSub s⁻¹ J := by
        have := conj_mem_conjSub (n := s⁻¹) hm
        rwa [inv_inv] at this
      rcases h.u34_conjSub_eq_or_eq hp hSp hKS hJS hsinv (Or.inr rfl) with h1 | h1
      · left; rwa [h1] at hmem
      · right; rwa [h1] at hmem
  have hSD : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D := by
    intro s hs d hd
    have key : ∀ m : G, (m ∈ K ∨ m ∈ J) → m * (s * d * s⁻¹) = (s * d * s⁻¹) * m := by
      intro m hm
      have hdm : (s⁻¹ * m * s) * d = d * (s⁻¹ * m * s) := by
        rcases hperm s hs m hm with h1 | h1
        · exact Subgroup.mem_centralizer_iff.mp hd.1 _ h1
        · exact Subgroup.mem_centralizer_iff.mp hd.2 _ h1
      calc m * (s * d * s⁻¹) = s * ((s⁻¹ * m * s) * d) * s⁻¹ := by group
        _ = s * (d * (s⁻¹ * m * s)) * s⁻¹ := by rw [hdm]
        _ = (s * d * s⁻¹) * m := by group
    exact ⟨Subgroup.mem_centralizer_iff.mpr fun m hm => key m (Or.inl hm),
      Subgroup.mem_centralizer_iff.mpr fun m hm => key m (Or.inr hm)⟩
  have hCD : ⁅S, Subgroup.zpowers y⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro s hs g hg
    have hgD : g ∈ D := Subgroup.zpowers_le.mpr hyD hg
    rw [commutatorElement_def]
    exact D.mul_mem (hSD s hs g hgD) (D.inv_mem hgD)
  have hCmap : (⁅S, Subgroup.zpowers y⁆).map π = Pb := by
    rw [Subgroup.map_commutator, hSdef, Subgroup.map_comap_eq_self_of_surjective hπs,
      MonoidHom.map_zpowers, hyπ]
    exact hybX
  obtain ⟨k, hk, x, hx, hkx⟩ := h.nonabelian hK
  have hπk : π k ∈ (⁅S, Subgroup.zpowers y⁆).map π := by
    rw [hCmap]
    exact hΩb.1 ⟨k, hk, rfl⟩
  obtain ⟨c, hcC, hck⟩ := hπk
  have hcD : c ∈ D := hCD hcC
  have hcK : ∀ m ∈ K, m * c = c * m := fun m hm => Subgroup.mem_centralizer_iff.mp hcD.1 m hm
  have hcJ : ∀ m ∈ J, m * c = c * m := fun m hm => Subgroup.mem_centralizer_iff.mp hcD.2 m hm
  have hqk : ∀ x ∈ K, (c⁻¹ * k) * x * (c⁻¹ * k)⁻¹ = k * x * k⁻¹ := by
    intro x hx
    have hkxk : k * x * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
    have h1 := hcK _ hkxk
    calc c⁻¹ * k * x * (c⁻¹ * k)⁻¹ = c⁻¹ * ((k * x * k⁻¹) * c) := by group
      _ = c⁻¹ * (c * (k * x * k⁻¹)) := by rw [h1]
      _ = k * x * k⁻¹ := by group
  refine h.false_of_asymmetric hp (q := c⁻¹ * k) ?_ ?_ ?_ hk hqk hx hkx
  · apply (QuotientGroup.eq_one_iff _).mp
    show π (c⁻¹ * k) = 1
    rw [map_mul, map_inv, hck, inv_mul_cancel]
  · apply U34.mem_normalizer_of_conj_mem
    intro x hx
    rw [hqk x hx]
    exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
  · intro y' hy'
    have h1 : k * y' = y' * k := hp.2.2.2 k hk y' hy'
    have h2 : y' * c⁻¹ = c⁻¹ * y' := ((show Commute y' c from hcJ y' hy').inv_right).eq
    calc c⁻¹ * k * y' = c⁻¹ * (k * y') := by group
      _ = c⁻¹ * (y' * k) := by rw [h1]
      _ = (c⁻¹ * y') * k := by group
      _ = (y' * c⁻¹) * k := by rw [h2]
      _ = y' * (c⁻¹ * k) := by group

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
