module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Group
import CFSG.HardMathSupport.Dickson.Bal207.SzNorm
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Field

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

theorem le_normalizer_of_burnside {Y : Type*} [Group Y] [Finite Y] {T D : Subgroup Y}
    {p a c d e : ℕ} [hpp : Fact p.Prime] [hdp : Fact d.Prime] (hY : Nat.card Y = p ^ a * c)
    (hcp : ¬ p ∣ c) (hTc : Nat.card T = p ^ a) (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hNT : Subgroup.normalizer (T : Set Y) ≤ T) (hDc : Nat.card D = d) (hdp' : d ≠ p)
    (hdc : c = d * e) (hde : ¬ d ∣ e) (he : ∀ n, n ∣ e → n ≡ 1 [MOD d] → n = 1) :
    T ≤ Subgroup.normalizer (D : Set Y) := by
  let P : Sylow p Y := Sylow.ofCard T (by
    rw [hTc]
    exact CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization hY hcp)
  have hPT : (P : Subgroup Y) = T := Sylow.coe_ofCard _ _
  have hP : Subgroup.normalizer (P : Set Y) ≤ Subgroup.centralizer (P : Set Y) := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer (T : Set Y) := by
      have : ((P : Subgroup Y) : Set Y) = (T : Set Y) := by rw [hPT]
      rw [← this]
      exact hn
    have hnT : n ∈ T := hNT hn'
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htT : t ∈ T := by
      have : t ∈ (P : Subgroup Y) := ht
      rwa [hPT] at this
    exact hTcomm t htT n hnT
  set M : Subgroup Y := (MonoidHom.transferSylow P hP).ker with hMdef
  have hcomp : Subgroup.IsComplement' M P := MonoidHom.ker_transferSylow_isComplement' P hP
  have hpa : 0 < p ^ a := pow_pos hpp.out.pos a
  have hMcard : Nat.card M = c := by
    have h := hcomp.card_mul_card
    rw [hY, hPT, hTc, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left hpa h
  have hMn : M.Normal := MonoidHom.normal_ker _
  have hDM : D ≤ M := by
    intro x hx
    have hxd : x ^ d = 1 := by
      have := pow_card_eq_one' (G := D) (x := ⟨x, hx⟩)
      rw [hDc] at this
      exact congrArg Subtype.val this
    have hq : Nat.card (Y ⧸ M) = p ^ a := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup M
      rw [hY, hMcard] at h
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0] at hMcard
          exact absurd hMcard (Nat.card_pos (α := M)).ne'
        · exact h0
      exact (Nat.eq_of_mul_eq_mul_right hc0 h).symm
    have h1 : orderOf (QuotientGroup.mk x : Y ⧸ M) ∣ d :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hxd, QuotientGroup.mk_one])
    have h2 : orderOf (QuotientGroup.mk x : Y ⧸ M) ∣ p ^ a := hq ▸ orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk x : Y ⧸ M) = 1 := by
      rcases (Nat.dvd_prime hdp.out).1 h1 with h4 | h4
      · exact h4
      · exfalso
        rw [h4] at h2
        exact hdp' ((Nat.prime_dvd_prime_iff_eq hdp.out hpp.out).mp
          (hdp.out.dvd_of_dvd_pow h2))
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hvd : d ^ 1 = d ^ (Nat.card M).factorization d := by
    rw [hMcard]
    exact CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (by rw [pow_one]; exact hdc)
      hde
  have hsub : ∀ H : Subgroup Y, H ≤ M → Nat.card H = d →
      Nat.card (H.subgroupOf M) = d ^ (Nat.card M).factorization d := by
    intro H hHM hHc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv, hHc, ← hvd, pow_one]
  let S : Sylow d M := Sylow.ofCard (D.subgroupOf M) (hsub D hDM hDc)
  have hS1 : Nat.card (Sylow d M) = 1 := by
    have hmod := card_sylow_modEq_one (p := d) (G := M)
    have hdvd := Sylow.card_dvd_index S
    have hidx : (S : Subgroup M).index = e := by
      have h := (S : Subgroup M).card_mul_index
      rw [Sylow.coe_ofCard, hsub D hDM hDc, ← hvd, pow_one, hMcard, hdc] at h
      exact Nat.eq_of_mul_eq_mul_left hdp.out.pos h
    rw [hidx] at hdvd
    exact he _ hdvd hmod
  have hsing : Subsingleton (Sylow d M) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    omega
  intro t _
  rw [Subgroup.mem_normalizer_iff]
  have hD' : ∀ x ∈ D, t * x * t⁻¹ ∈ D := by
    set D' : Subgroup Y := D.map (MulAut.conj t).toMonoidHom
    have hD'M : D' ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      exact hMn.conj_mem x (hDM hx) t
    have hD'c : Nat.card D' = d := by
      rw [← hDc]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj t).toMonoidHom
        (MulAut.conj t).injective).toEquiv).symm
    let S' : Sylow d M := Sylow.ofCard (D'.subgroupOf M) (hsub D' hD'M hD'c)
    have hSS : S' = S := Subsingleton.elim _ _
    have hsg : D'.subgroupOf M = D.subgroupOf M := by
      have h := congrArg (fun Q : Sylow d M => (Q : Subgroup M)) hSS
      simpa [S, S'] using h
    have hDD : D' = D := by
      have h1 := Subgroup.subgroupOf_inj.mp hsg
      rwa [inf_eq_left.mpr hD'M, inf_eq_left.mpr hDM] at h1
    intro x hx
    have : t * x * t⁻¹ ∈ D' := ⟨x, hx, rfl⟩
    rwa [hDD] at this
  intro x
  constructor
  · exact hD' x
  · intro hx
    by_contra hxD
    have hle : D.map (MulAut.conj t).toMonoidHom ≤ D := by
      rintro _ ⟨y, hy, rfl⟩
      exact hD' y hy
    have heq : D.map (MulAut.conj t).toMonoidHom = D :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [← Nat.card_congr (Subgroup.equivMapOfInjective D (MulAut.conj t).toMonoidHom
          (MulAut.conj t).injective).toEquiv])
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : t * y * t⁻¹ = t * x * t⁻¹ := hyx
      simpa using h1
    exact hxD (this ▸ hy)

theorem sz32_index_cases_41 {m : ℕ} (hd : m ∣ 31744) (hm : m ≡ 1 [MOD 41]) :
    m = 1 ∨ m = 124 := by
  have h : (31744 : ℕ) = 2 ^ 10 * 31 := by norm_num
  rw [h] at hd
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 hd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ha
  have key : ∀ i ≤ 10, ∀ b ∈ ({1, 31} : Finset ℕ), 2 ^ i * b ≡ 1 [MOD 41] →
      2 ^ i * b = 1 ∨ 2 ^ i * b = 124 := by decide +kernel
  refine key i hi b ?_ hm
  rcases (Nat.dvd_prime (by norm_num)).1 hb with rfl | rfl <;> simp

theorem sz32_index_cases_31 {m : ℕ} (hd : m ∣ 41984) (hm : m ≡ 1 [MOD 31]) :
    m = 1 ∨ m = 32 ∨ m = 1024 := by
  have h : (41984 : ℕ) = 2 ^ 10 * 41 := by norm_num
  rw [h] at hd
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 hd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ha
  have key : ∀ i ≤ 10, ∀ b ∈ ({1, 41} : Finset ℕ), 2 ^ i * b ≡ 1 [MOD 31] →
      2 ^ i * b = 1 ∨ 2 ^ i * b = 32 ∨ 2 ^ i * b = 1024 := by decide +kernel
  refine key i hi b ?_ hm
  rcases (Nat.dvd_prime (by norm_num)).1 hb with rfl | rfl <;> simp

section Sz

open CFSG.AGLEmbedding.KFactProofs.Sz32Local (Sz32Data)

theorem sz32Data_of_suzukiModel
    {K : Type} [Group K] [Finite K]
    (hM : CFSG.Blueprint.SuzukiModel K 2 5) (T : Sylow 5 K) : Sz32Data K (T : Subgroup K) := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hM
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  obtain rfl : a = 2 := by omega
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hSz : CFSG.RankThree.PartOne.K159.SzAbs.SzSylow K :=
    CFSG.RankThree.PartOne.K159.SzAbs.SzSylow.of_mulEquiv eF
      (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_model hF')
  let ε : K ≃* CFSG.Blueprint.suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv
      (CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'))
  have hcard : Nat.card (T : Subgroup K) = 25 := by
    rw [Sylow.card_eq_multiplicity, hSz.card,
      CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  exact ⟨hSz.card, hcard, hSz.cyclic T,
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T⟩

theorem sz32_false_of_index
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.Blueprint.SuzukiModel K 2 5) (T : Sylow 5 K) {Y D : Subgroup K} {c d e : ℕ}
    [hdp : Fact d.Prime] (hTY : (T : Subgroup K) ≤ Y) (hDY : D ≤ Y) (hYc : Nat.card Y = 25 * c)
    (hc5 : ¬ 5 ∣ c) (hDc : Nat.card D = d) (hd5 : d ≠ 5) (hdc : c = d * e) (hde : ¬ d ∣ e)
    (he : ∀ n, n ∣ e → n ≡ 1 [MOD d] → n = 1)
    (hN : ∀ n i : ℕ, n ∣ 100 → 25 ∣ n → n * i = 25 * c → i ≡ 1 [MOD 5] → n = 25) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hD := sz32Data_of_suzukiModel hK T
  set TY : Subgroup ↥Y := (T : Subgroup K).subgroupOf Y with hTYdef
  set DY : Subgroup ↥Y := D.subgroupOf Y with hDYdef
  have hTYc : Nat.card TY = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hD.card_eq]
  have hDYc : Nat.card DY = d := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDY).toEquiv, hDc]
  have hTcomm : ∀ x ∈ TY, ∀ y ∈ TY, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hD.commute _ hx _ hy)
  have hNT : Subgroup.normalizer (TY : Set ↥Y) ≤ TY := by
    have hv : (5 : ℕ) ^ 2 = 5 ^ (Nat.card ↥Y).factorization 5 :=
      CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (by rw [hYc]; norm_num) hc5
    let P' : Sylow 5 ↥Y := Sylow.ofCard TY (by rw [hTYc, ← hv]; norm_num)
    have hcount : (Subgroup.normalizer (TY : Set ↥Y)).index ≡ 1 [MOD 5] := by
      have h := card_sylow_modEq_one (p := 5) (G := ↥Y)
      rw [Sylow.card_eq_index_normalizer P'] at h
      exact h
    have hmul := (Subgroup.normalizer (TY : Set ↥Y)).card_mul_index
    rw [hYc] at hmul
    have hTN : TY ≤ Subgroup.normalizer (TY : Set ↥Y) := Subgroup.le_normalizer
    have h25 : 25 ∣ Nat.card (Subgroup.normalizer (TY : Set ↥Y)) := by
      have := Subgroup.card_dvd_of_le hTN
      rwa [hTYc] at this
    have h100 : Nat.card (Subgroup.normalizer (TY : Set ↥Y)) ∣ 100 := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTY, ← hD.card_normalizer]
      have h1 := (Nat.card_congr (Subgroup.equivMapOfInjective
        ((Subgroup.normalizer ((T : Subgroup K) : Set K)).subgroupOf Y) Y.subtype
        Y.subtype_injective).toEquiv).symm
      rw [Subgroup.subgroupOf_map_subtype] at h1
      rw [← h1]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h25eq := hN _ _ h100 h25 hmul hcount
    exact (Subgroup.eq_of_le_of_card_ge hTN (by rw [h25eq, hTYc])).ge
  have hle := le_normalizer_of_burnside (T := TY) (D := DY) (p := 5) (a := 2) (c := c) (e := e)
    (by rw [hYc]; norm_num) hc5 (by rw [hTYc]; norm_num) hTcomm hNT hDYc hd5 hdc hde he
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T : Subgroup K)) 5
    (by rw [hD.card_eq]; norm_num)
  have hk5 : (k : K) ^ 5 = 1 := by
    have h1 : k ^ 5 = 1 := by
      have := pow_orderOf_eq_one k
      rwa [hk] at this
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hk1 : (k : K) ≠ 1 := by
    intro h1
    have : k = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hk
    norm_num at hk
  have hkN : (k : K) ∈ Subgroup.normalizer (D : Set K) := by
    have h1 : (⟨(k : K), hTY k.2⟩ : ↥Y) ∈ Subgroup.normalizer (DY : Set ↥Y) := hle k.2
    rw [← Subgroup.subgroupOf_normalizer_eq hDY] at h1
    exact h1
  have hcop : Nat.Coprime 5 (Nat.card D) := by
    rw [hDc]
    exact (Nat.coprime_primes Nat.prime_five hdp.out).mpr hd5.symm
  have hbot := CFSG.HardMathSupport.Dickson.Bal207.bal207SzNorm K hK (k : K) hk5 hk1 D hcop hkN
  rw [hbot, Subgroup.card_bot] at hDc
  exact hdp.out.one_lt.ne hDc

theorem threeNineFiveSz_holds :
    ThreeNineFiveSz := by
  intro X _ _ K E D X₁ d h hK
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  obtain ⟨Q, hEQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup h.elem).exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 5 ((Q : Subgroup X) ⊓ K) K := by
    have hQ : CFSG.ABGLocalTools.IsSylowOf 5 (Q : Subgroup X) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, Q.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact Q.not_dvd_index
    exact hQ.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  let T : Sylow 5 ↥K := Sylow.ofCard (((Q : Subgroup X) ⊓ K).subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hQsyl.card_eq)
  have hD := sz32Data_of_suzukiModel hK T
  have hcardK : Nat.card ↥K = 32537600 := hD.card_group
  have hsimple : IsSimpleGroup ↥K := by
    obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hK
    have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  have hZ : Subgroup.center ↥K = ⊥ := hD.center_eq_bot
  have hout : ¬ d ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) := by
    have h5 := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥K 2 5
      hK).1.2.1
    intro hd
    exact h.d_ne ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp (hd.trans h5))
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hout
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  have hDinf : D ⊓ K = D := inf_eq_left.mpr hDK
  rw [hDinf] at hDsylK
  have hDcard := hDsylK.card_eq
  rw [hcardK] at hDcard
  have hdK : d ∣ 32537600 := by
    by_contra hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero] at hDcard
    exact h.D_ne_bot (Subgroup.card_eq_one.mp hDcard)
  have hd3141 : d = 31 ∨ d = 41 := by
    have hfac : (32537600 : ℕ) = 2 ^ 10 * 5 ^ 2 * 31 * 41 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  have hDd : Nat.card D = d := by
    rw [hDcard]
    rcases hd3141 with rfl | rfl
    · have h1 : (31 : ℕ) ^ (32537600 : ℕ).factorization 31 = 31 ^ 1 :=
        (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 31) (a := 1)
          (k := 1049600) (by norm_num) (by norm_num)).symm
      rw [h1, pow_one]
    · have h1 : (41 : ℕ) ^ (32537600 : ℕ).factorization 41 = 41 ^ 1 :=
        (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 41) (a := 1)
          (k := 793600) (by norm_num) (by norm_num)).symm
      rw [h1, pow_one]
  set Y : Subgroup ↥K := X₁.subgroupOf K with hYdef
  have hYtop : Y ≠ ⊤ := by
    intro htop
    apply h.not_K_le
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ Y := htop ▸ Subgroup.mem_top _
    exact this
  have hi1 : Y.index ≠ 1 := fun h1 => hYtop (Subgroup.index_eq_one.mp h1)
  have hTY : (T : Subgroup ↥K) ≤ Y := fun x hx => h.inf_K_le Q.isPGroup' hEQ hx
  have hDY : D.subgroupOf K ≤ Y := fun x hx => h.D_le hx
  have hDKc : Nat.card (D.subgroupOf K) = d := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDd]
  let SD : Sylow d ↥K := Sylow.ofCard (D.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDcard, hcardK])
  have hN : Subgroup.normalizer ((SD : Subgroup ↥K) : Set ↥K) ≤ Y := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
    rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
    exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩
  have hmod := index_modEq_one_of_normalizer_le SD hN
  have hidx := Y.card_mul_index
  rw [hcardK] at hidx
  have h25 : 25 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hTY
    rwa [hD.card_eq] at this
  have hdY : d ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hDY
    rwa [hDKc] at this
  rcases hd3141 with rfl | rfl
  ·
    obtain ⟨q, hq⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 25 31) h25 hdY
    have hqi : q * Y.index = 41984 := by
      have h1 : 25 * 31 * (q * Y.index) = 32537600 := by rw [← hidx, hq]; ring
      omega
    rcases sz32_index_cases_31 (Dvd.intro_left q hqi) hmod with h1 | h32 | h1024
    · exact hi1 h1
    ·
      have hcore : Y.normalCore = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with h0 | h0
        · exact h0
        · exact absurd (top_le_iff.mp (h0.symm.le.trans Y.normalCore_le)) hYtop
      have hdvd := Y.index_normalCore_dvd_factorial_index
      rw [hcore, Subgroup.index_bot, hcardK, h32] at hdvd
      have h41 : 41 ∣ Nat.factorial 32 := (by norm_num : 41 ∣ 32537600).trans hdvd
      exact absurd ((Nat.Prime.dvd_factorial (by norm_num)).mp h41) (by norm_num)
    ·
      rw [h1024] at hqi
      refine sz32_false_of_index hK T (c := 1271) (e := 41) hTY hDY (by rw [hq]; omega)
        (by norm_num) hDKc (by norm_num) (by norm_num) (by norm_num) ?_ ?_
      · intro n hn hm
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 41)).1 hn with rfl | rfl
        · rfl
        · exact absurd hm (by decide)
      · intro n i hn h25' hni hi
        obtain ⟨j, rfl⟩ := h25'
        have hj : j ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 25)
          (by rw [show (25 : ℕ) * 4 = 100 by norm_num]; exact hn)
        have hj4 : j ≤ 4 := Nat.le_of_dvd (by norm_num) hj
        unfold Nat.ModEq at hi
        interval_cases j <;> omega
  ·
    obtain ⟨q, hq⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 25 41) h25 hdY
    have hqi : q * Y.index = 31744 := by
      have h1 : 25 * 41 * (q * Y.index) = 32537600 := by rw [← hidx, hq]; ring
      omega
    rcases sz32_index_cases_41 (Dvd.intro_left q hqi) hmod with h1 | h124
    · exact hi1 h1
    · rw [h124] at hqi
      refine sz32_false_of_index hK T (c := 10496) (e := 256) hTY hDY (by rw [hq]; omega)
        (by norm_num) hDKc (by norm_num) (by norm_num) (by norm_num) ?_ ?_
      · intro n hn hm
        have hn' : n ∣ 2 ^ 8 := hn
        obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn'
        have key : ∀ i ≤ 8, 2 ^ i ≡ 1 [MOD 41] → 2 ^ i = 1 := by decide +kernel
        exact key i hi hm
      · intro n i hn h25' hni hi
        obtain ⟨j, rfl⟩ := h25'
        have hj : j ∣ 4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 25)
          (by rw [show (25 : ℕ) * 4 = 100 by norm_num]; exact hn)
        have hj4 : j ≤ 4 := Nat.le_of_dvd (by norm_num) hj
        unfold Nat.ModEq at hi
        interval_cases j <;> omega

end Sz

end CFSG.LocalAnalysis.AGL81I.Section3
