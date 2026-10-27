module

public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.GLS.Th2.L83

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def actOn {K X : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    {B : Subgroup G} (hBX : B ≤ X) : ↥B →* MulAut (kBar K) :=
  (Back.actHom hKX).comp (Subgroup.inclusion hBX)

@[expose] def fixFam {K X : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) {B : Subgroup G}
    (hBX : B ≤ X) (E : Subgroup G) : Set (Subgroup G) :=
  {F | ∃ (u : G) (hu : u ∈ B), orderOf u = 2 ∧ actOn hKX hBX ⟨u, hu⟩ ≠ 1 ∧ F = zpowers u ⊔ E}

theorem fixBar_gen_of_gamma {K X B E : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hBX : B ≤ X) (hEX : E ≤ X)
    (hEtriv : ∀ (e : G) (he : e ∈ E), Back.actHom hKX ⟨e, hEX he⟩ = 1)
    (hBE : ∀ p ∈ B, ∀ e ∈ E, p * e = e * p)
    (hgam : Bk.gammaAut (kBar K) (actOn hKX hBX).range = ⊤)
    (hinv : ∀ w ∈ (actOn hKX hBX).range, orderOf w = 2 →
      ∃ (u : G) (hu : u ∈ B), orderOf u = 2 ∧ actOn hKX hBX ⟨u, hu⟩ = w) :
    ⨆ F ∈ fixFam hKX hBX E, fixBar hKX F = ⊤ := by
  have hle : (⊤ : Subgroup (kBar K)) ≤ ⨆ F ∈ fixFam hKX hBX E, fixBar hKX F := by
    rw [← hgam]
    refine iSup_le fun w => iSup_le fun hw => iSup_le fun hord => ?_
    obtain ⟨u, hu, hu2, rfl⟩ := hinv w hw hord
    have hne : actOn hKX hBX ⟨u, hu⟩ ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      omega
    refine le_iSup₂_of_le (zpowers u ⊔ E) ⟨u, hu, hu2, hne, rfl⟩ ?_
    intro z hz
    have hz' : actOn hKX hBX ⟨u, hu⟩ z = z := hz
    rw [mem_fixBar_iff]
    intro f hf
    have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
      exact (Commute.zpow_left (hBE u hu b hb) m).eq
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm hf
    have haB : a ∈ B := zpowers_le.2 hu ha
    have haX := hBX haB
    have hbX := hEX hb
    have hfeq : f = ⟨a, haX⟩ * ⟨b, hbX⟩ := Subtype.ext hab
    have hb1 : Back.actHom hKX ⟨b, hbX⟩ = 1 := hEtriv b hb
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    have hfix : (actOn hKX hBX ⟨u, hu⟩ ^ m) z = z := by
      have hmem : actOn hKX hBX ⟨u, hu⟩ ∈ MulAction.stabilizer (MulAut (kBar K)) z := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hz'
      have := (MulAction.stabilizer (MulAut (kBar K)) z).zpow_mem hmem m
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    have hua : Back.actHom hKX ⟨u ^ m, haX⟩ = actOn hKX hBX ⟨u, hu⟩ ^ m := by
      have : (⟨u ^ m, haX⟩ : ↥X) = (⟨u, hBX hu⟩ : ↥X) ^ m := Subtype.ext (by simp)
      rw [this, map_zpow]; rfl
    rw [hfeq, map_mul, hb1, mul_one, hua]
    exact hfix
  exact top_le_iff.1 hle

variable [Finite G]

theorem card_sylow_eq_two_pow {K P : Subgroup G} (hP : IsSylowOf 2 P K) :
    Nat.card ↥P = 2 ^ (Nat.card (kBar K)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥K)) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have h0 : Nat.card ↥(pPrimeCore 2 ↥K) ≠ 0 := Nat.card_pos.ne'
  have h1 : Nat.card (kBar K) ≠ 0 := Nat.card_pos.ne'
  rw [hP.card_eq, hK, Nat.factorization_mul h1 h0, Finsupp.add_apply,
    Back.Setup91.factorization_two_of_odd hodd, add_zero]

omit [Finite G] in
theorem conj_injective_of_centerless {K : Subgroup G} (hcen : CenterlessBar K) :
    Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) := by
  intro a b h
  have h1 : MulAut.conj (a⁻¹ * b) = (1 : MulAut (kBar K)) := by
    rw [map_mul, map_inv, h]; simp
  have : a⁻¹ * b = 1 := hcen _ (fun c => by
    have := congrArg (fun φ : MulAut (kBar K) => φ c) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc (a⁻¹ * b) * c = (a⁻¹ * b) * c * (a⁻¹ * b)⁻¹ * (a⁻¹ * b) := by group
      _ = c * (a⁻¹ * b) := by rw [this])
  exact (inv_mul_eq_one.1 this)

theorem eq_five_of_ordA_one_eq_sixty {m : ℕ} (hodd : Odd m) (h : CFSG.Open.ordA 1 m = 60) : m = 5 := by
  unfold CFSG.Open.ordA at h
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton] at h
  rcases Nat.lt_or_ge m 10 with hm | hm
  · have hodd' : m % 2 = 1 := Nat.odd_iff.1 hodd
    interval_cases m <;> simp_all
  · exfalso
    have hg : 0 < Nat.gcd 2 (m - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle : Nat.gcd 2 (m - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hX : 2 * (60 + 1) ≤ m * (m ^ 2 - 1) := by
      have h1 : 10 * 99 ≤ m * (m ^ 2 - 1) := by
        have h2 : 99 ≤ m ^ 2 - 1 := by
          have : 10 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
          omega
        exact Nat.mul_le_mul hm h2
      omega
    have := Th2.lt_div_aux hg hle hX
    rw [h] at this
    exact lt_irrefl _ this

theorem fixBar_gen_L2 {K X P E : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hP : IsSylowOf 2 P K) (hPX : P ≤ X) (hcen : CenterlessBar K)
    (hEtriv : ∀ e ∈ E, ∀ k ∈ K, ⁅k, e⁆ ∈ pPrimeCoreOf 2 K) (hEX : E ≤ X)
    (hPE : ∀ p ∈ P, ∀ e ∈ E, p * e = e * p) (hP2 : 2 ≤ pRank 2 ↥P)
    (hL2 : ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Odd (p ^ f) ∧ p ^ f ≠ 5 ∧ LieModel (kBar K) .PSL 2 p f)
    (h6 : Bk.B_ivk_6) :
    ⨆ F ∈ fixFam hKX hPX E, fixBar hKX F = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj := conj_injective_of_centerless hcen
  let ι : ↥P →* MulAut (kBar K) := actOn hKX hPX
  have hιapply : ∀ (p : G) (hp : p ∈ P), ι ⟨p, hp⟩ =
      MulAut.conj (QuotientGroup.mk (⟨p, hP.le hp⟩ : ↥K) : kBar K) := fun p hp =>
    Back.actHom_of_mem hKX (hP.le hp) (hPX hp)
  have hbot := Back.Setup91.inf_pPrimeCoreOf_eq_bot K hP.isPGroup
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker, show p = ⟨p.1, p.2⟩ from rfl, hιapply p.1 p.2] at hp
    have h1 : (QuotientGroup.mk (⟨p.1, hP.le p.2⟩ : ↥K) : kBar K) = 1 :=
      hconj (by rw [map_one]; exact hp)
    have h2 : (⟨p.1, hP.le p.2⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : p.1 ∈ P ⊓ pPrimeCoreOf 2 K :=
      ⟨p.2, Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hP.le p.2, h2⟩⟩
    rw [hbot, Subgroup.mem_bot] at h3
    rw [Subgroup.mem_bot]
    exact Subtype.ext h3
  let eW : ↥P ≃* ↥ι.range := MonoidHom.ofInjective hιinj
  have hW2 : IsPGroup 2 ↥ι.range := hP.isPGroup.of_equiv eW
  have hWrk : 2 ≤ CFSG.pRank 2 ↥ι.range := by
    rw [← CFSG.RankThree.PartOne.Quotient36.pRank_congr_mulEquiv one_lt_two eW]
    exact hP2
  have hWcard : Nat.card ↥ι.range = Nat.card ↥P := (Nat.card_congr eW.toEquiv).symm
  obtain ⟨p, f, hp, hf, hodd, h5, hmodel⟩ := hL2
  have hLodd : HasL2Model (kBar K) Odd := ⟨p, f, hp, hf, hodd, hmodel⟩
  have hcardK : Nat.card (kBar K) = CFSG.Open.ordA 1 (p ^ f) := by
    simpa using CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hmodel
  have hgam : Bk.gammaAut (kBar K) ι.range = ⊤ := by
    by_contra hne
    obtain ⟨hq, ⟨-, hW4⟩, -⟩ := h6 (kBar K) ι.range (Or.inl hLodd) hW2 hWrk hne
    obtain ⟨q₀, hq₀, p', f', hp', hf', hpq, hmodel'⟩ := hq hLodd
    have hcardK' : Nat.card (kBar K) = CFSG.Open.ordA 1 q₀ := by
      rw [← hpq]
      simpa using CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hmodel'
    have hPcard := card_sylow_eq_two_pow hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    rcases hq₀ with rfl | rfl | rfl
    · have : CFSG.Open.ordA 1 (p ^ f) = 60 := by rw [← hcardK, hcardK']; decide
      exact h5 (eq_five_of_ordA_one_eq_sixty hodd this)
    · have h168 : Nat.card (kBar K) = 168 := by rw [hcardK']; decide
      have : (168 : ℕ).factorization 2 = 3 := by
        have h : (168 : ℕ) = 2 ^ 3 * 21 := by norm_num
        rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
          Back.Setup91.factorization_two_of_odd (by decide : Odd 21)]
      rw [h168, this] at hPcard
      omega
    · have h360 : Nat.card (kBar K) = 360 := by rw [hcardK']; decide
      have : (360 : ℕ).factorization 2 = 3 := by
        have h : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
        rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
          Back.Setup91.factorization_two_of_odd (by decide : Odd 45)]
      rw [h360, this] at hPcard
      omega
  have hinv : ∀ w ∈ ι.range, orderOf w = 2 →
      ∃ (u : G) (hu : u ∈ P), orderOf u = 2 ∧ ι ⟨u, hu⟩ = w := by
    intro w hw hord
    obtain ⟨⟨u, hu⟩, rfl⟩ := hw
    have hord' : orderOf (QuotientGroup.mk (⟨u, hP.le hu⟩ : ↥K) : kBar K) = 2 := by
      rw [← orderOf_injective _ hconj, ← hιapply u hu]
      exact hord
    have hsq : (QuotientGroup.mk (⟨u, hP.le hu⟩ : ↥K) : kBar K) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (QuotientGroup.mk (⟨u, hP.le hu⟩ : ↥K) : kBar K)
      rwa [hord'] at this
    have hu2 : u ^ 2 = 1 := by
      have h1 : (⟨u, hP.le hu⟩ : ↥K) ^ 2 ∈ pPrimeCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact hsq
      have h2 : u ^ 2 ∈ P ⊓ pPrimeCoreOf 2 K :=
        ⟨P.pow_mem hu 2, Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.pow_mem (hP.le hu) 2, h1⟩⟩
      rw [hbot, Subgroup.mem_bot] at h2
      exact h2
    have hu1 : u ≠ 1 := by
      intro h1
      subst h1
      have : (QuotientGroup.mk (⟨1, hP.le hu⟩ : ↥K) : kBar K) = 1 := by
        rw [QuotientGroup.eq_one_iff]; exact (pPrimeCore 2 ↥K).one_mem
      rw [this, orderOf_one] at hord'
      omega
    exact ⟨u, hu, orderOf_eq_prime hu2 hu1, rfl⟩
  exact fixBar_gen_of_gamma hKX hPX hEX
    (fun e he => (Back.actHom_eq_one_iff_commutator_mem hKX ⟨e, hEX he⟩).2 (hEtriv e he))
    hPE hgam hinv

theorem l83_L2_core {x y : G} {K T S M : Subgroup G} (h : Th2Std x y K T S)
    (hcen : CenterlessBar K) (hP : RankTwoShape (T ⊓ K))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hL2 : ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Odd (p ^ f) ∧ p ^ f ≠ 5 ∧ LieModel (kBar K) .PSL 2 p f)
    (h6 : Bk.B_ivk_6) {E : Subgroup G} (hE : E ≤ T ⊓ CxK x K)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE2 : 2 ≤ pRank 2 ↥E)
    (hN : ∀ U : Subgroup G, IsFourSub (T ⊓ K) U → ∀ F : Subgroup G, F ≤ U ⊔ E →
      3 ≤ pRank 2 ↥F → normalizer (F : Set G) ≤ M) : K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPQ := h.commDisj hcen
  have hPX : T ⊓ K ≤ centralizer ({x} : Set G) := inf_le_left.trans h.T_le_C
  have hEX : E ≤ centralizer ({x} : Set G) := hE.trans (inf_le_left.trans h.T_le_C)
  have hEQ : E ≤ T ⊓ CxK x K := hE
  obtain ⟨U₀, hU₀⟩ := exists_isFourSub_of_rankTwoShape hP
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := by
    have := C3.Layer1.Back.pRank_mono' hU₀.1
    rw [pRank_of_isFourSub hU₀] at this
    exact this
  have hrkU : ∀ U : Subgroup G, IsFourSub (T ⊓ K) U →
      CFSG.IsElementaryAbelian 2 ↥(U ⊔ E) ∧ pRank 2 ↥(U ⊔ E) = 2 + pRank 2 ↥E := fun U hU =>
    ⟨hPQ.isElementaryAbelian_sup' hU.2.1 hEel hU.1 hEQ, by
      rw [hPQ.pRank_sup hU.2.1 hEel hU.1 hEQ, pRank_of_isFourSub hU]⟩
  have hO : pPrimeCoreOf 2 K ≤ M := by
    obtain ⟨hAel, hArk⟩ := hrkU U₀ hU₀
    exact pPrimeCoreOf_le_of_normalizers hKN 3 hAel (sup_le (hU₀.1.trans hPX) hEX) (by omega)
      (fun F hFA hFr => hN U₀ hU₀ F hFA hFr)
  have hfam : ∀ F : Subgroup G, F ∈ fixFam hKN hPX E →
      ∃ U : Subgroup G, IsFourSub (T ⊓ K) U ∧ F ≤ U ⊔ E ∧ 3 ≤ pRank 2 ↥F := by
    rintro F ⟨u, hu, hu2, -, rfl⟩
    have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers u) :=
      isElementaryAbelian_zpowers_of_orderOf_two hu2
    obtain ⟨U, hUz, hU⟩ := hP.2.1 (zpowers u) (zpowers_le.2 hu) hzel
    refine ⟨U, hU, sup_le_sup_right hUz E, ?_⟩
    have hcd : CommDisj (zpowers u) E :=
      ⟨fun a ha b hb => hPQ.comm a (zpowers_le.2 hu ha) b (hE hb), eq_bot_iff.2 fun z hz =>
        Subgroup.mem_bot.2 (hPQ.eq_one_of_mem (zpowers_le.2 hu hz.1) (hE hz.2))⟩
    rw [hcd.pRank_sup hzel hEel le_rfl le_rfl, pRank_zpowers_of_orderOf_two hu2]
    omega
  refine K_le_of_cover hKN (fixFam hKN hPX E) ?_ ?_ hO ?_
  · intro F hF
    obtain ⟨U, hU, hFU, -⟩ := hfam F hF
    have hUE := (hrkU U hU).1
    exact ⟨hFU.trans (sup_le (hU.1.trans hPX) hEX),
      (CFSG.IsElementaryAbelian.isPGroup 2 ↥(U ⊔ E)).to_le hFU⟩
  · intro F hF
    obtain ⟨U, hU, hFU, hr⟩ := hfam F hF
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (F : Set G)).trans
      (hN U hU F hFU hr))
  · exact fixBar_gen_L2 hKN h.sylow_P hPX hcen (fun e he k hk => (hEQ he).2.2.2.2 k hk) hEX
      (fun p hp e he => hPQ.comm p hp e (hEQ he)) hP2 hL2 h6

end CFSG.GH74.GLS.Th2.L83
