module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.ClassicalInvolution.SubnormalCommutator
public import CFSG.HardMathSupport.Solomon.Proving.KZeroLe
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement Pointwise

namespace S8.L84

variable {G : Type} [Group G] [Finite G]

theorem rank_cond {p : ℕ} (hp : p.Prime) {B : Subgroup G} (hB : GLAIsBmax p B) (X : Subgroup G) :
    ∀ W U : Subgroup G, W ≤ X → IsElemAbelian p W → U ≤ X → U ≠ ⊥ → IsPGroup 2 U →
      W ≤ Subgroup.normalizer (U : Set G) → Nat.card W ≤ Nat.card B := by
  intro W U _ hW _ hU hU2 hWU
  rw [hB.2.1]
  exact card_le_pow_glaTwoLocalRank hp hW hU hU2 hWU

theorem mem_normalizer_inf {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hH hK ⊢
  rw [gLBConj_inf, hH, hK]

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hH hK ⊢
  unfold GLBConj at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_centralizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.centralizer (H : Set G))
    (hK : g ∈ Subgroup.centralizer (K : Set G)) :
    g ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hle : H ⊔ K ≤ cx g := by
    refine sup_le (fun h hh => ?_) (fun k hk => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hH h hh)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hK k hk)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem centralizer_sup_zpowers (H : Subgroup G) (x : G) :
    Subgroup.centralizer ((H ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ cx x := by
  apply le_antisymm
  · refine le_inf (Subgroup.centralizer_le (le_sup_left : H ≤ H ⊔ Subgroup.zpowers x)) ?_
    have h := Subgroup.centralizer_le (le_sup_right : Subgroup.zpowers x ≤ H ⊔ Subgroup.zpowers x)
    rw [S3.centralizer_zpowers x] at h
    exact h
  · rintro g ⟨hgH, hgx⟩
    refine mem_centralizer_sup hgH ?_
    rw [S3.centralizer_zpowers x]
    exact hgx

theorem normalizer_le_normalizer_centralizer (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [gLBConj_centralizer, hg]

theorem centMod_of_comm {p : ℕ} {L : Subgroup G} {g : G} (h : L ≤ cx g) : CentMod p L g := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hc : y * g = g * y := Subgroup.mem_centralizer_singleton_iff.1 (h hy)
      have : g * y * g⁻¹ = y := by rw [← hc]; group
      rw [this]; exact hy
    · intro hy
      have hc : (g * y * g⁻¹) * g = g * (g * y * g⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.1 (h hy)
      have : y = g * y * g⁻¹ := by
        have h2 : g * y = g * (g * y * g⁻¹) := by
          calc g * y = (g * y * g⁻¹) * g := by group
            _ = g * (g * y * g⁻¹) := hc
        exact mul_left_cancel h2
      rw [this]; exact hy
  · have hle : L ≤ Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) := by
      rw [S3.centralizer_zpowers g]; exact h
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).2 hle]
    exact bot_le

theorem mem_normalizer_of_uniq {p : ℕ} {Y I : Subgroup G} (hI : GLAPComponent p Y I)
    (huniq : ∀ J : Subgroup G, GLAPComponent p Y J → J = I) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) : g ∈ Subgroup.normalizer (I : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  have h1 := glaPComponent_gLBConj hI g
  rw [mem_normalizer_iff_gLBConj_eq.1 hg] at h1
  exact huniq _ h1

theorem catalogIs_pQuot_of_center {p : ℕ} {J : Subgroup G} {Q : TauCeti.CFSGIndex → Prop}
    (hZ : Nat.card (Subgroup.center (PQuot p J)) = 1) (h : catalogIs (PSimple p J) Q) :
    catalogIs (PQuot p J) Q := by
  have hbot : Subgroup.center (PQuot p J) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  have e : PSimple p J ≃* PQuot p J :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  exact (catalogIs_congr e).1 h

theorem inf_cx_mul_pow {L : Subgroup G} {x : G} (hL : L ≤ cx x) (d : G) (i : ℕ) :
    L ⊓ cx (d * x ^ i) = L ⊓ cx d := by
  ext l
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    have hx : l * x = x * l := (Subgroup.mem_centralizer_singleton_iff.1 (hL hl))
    have hxi : l * x ^ i = x ^ i * l := (Commute.pow_right hx i).eq
    have : l * d * x ^ i = d * l * x ^ i := by
      calc l * d * x ^ i = l * (d * x ^ i) := by group
        _ = d * x ^ i * l := h
        _ = d * (x ^ i * l) := by group
        _ = d * (l * x ^ i) := by rw [hxi]
        _ = d * l * x ^ i := by group
    exact mul_right_cancel this
  · rintro ⟨hl, h⟩
    refine ⟨hl, ?_⟩
    have hx : l * x = x * l := (Subgroup.mem_centralizer_singleton_iff.1 (hL hl))
    have hxi : l * x ^ i = x ^ i * l := (Commute.pow_right hx i).eq
    calc l * (d * x ^ i) = l * d * x ^ i := by group
      _ = d * l * x ^ i := by rw [h]
      _ = d * (l * x ^ i) := by group
      _ = d * (x ^ i * l) := by rw [hxi]
      _ = d * x ^ i * l := by group

theorem centralizer_eq_inf {D : Subgroup G} {a d : G} (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    (haD : a ∈ D) (ha1 : a ≠ 1) (hdD : d ∈ D) (hd : d ∉ Subgroup.zpowers a) :
    Subgroup.centralizer (D : Set G) = cx a ⊓ cx d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hao : orderOf a = 3 := orderOf_eq_prime (hD.2 a haD) ha1
  set M : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers d with hM
  have hMD : M ≤ D := sup_le ((Subgroup.zpowers_le).2 haD) ((Subgroup.zpowers_le).2 hdD)
  have hgt : 3 < Nat.card M := by
    by_contra hle
    push Not at hle
    have h1 : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hao]
    have heq : Subgroup.zpowers a = M :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h1]; exact hle)
    exact hd (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have hdvd : Nat.card M ∣ 3 ^ 2 := hDc ▸ Subgroup.card_dvd_of_le hMD
  obtain ⟨k, hk, hkM⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk2 : k = 2 := by
    interval_cases k <;> simp_all
  have hMeq : M = D := Subgroup.eq_of_le_of_card_ge hMD (by rw [hDc, hkM, hk2])
  rw [← hMeq, hM, centralizer_sup_zpowers (Subgroup.zpowers a) d, S3.centralizer_zpowers a]


theorem mem_core_of_centMod {p : ℕ} {J : Subgroup G} (hZ : Nat.card (Subgroup.center (PQuot p J)) = 1)
    {g : G} (hgJ : g ∈ J) (hg : CentMod p J g) : g ∈ GLAPPrimeCoreOf p J := by
  have hbot : Subgroup.center (PQuot p J) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  have hcen : (QuotientGroup.mk (⟨g, hgJ⟩ : ↥J) : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective z
    have hc : ⁅l⁻¹, g⁆ ∈ GLAPPrimeCoreOf p J :=
      hg.2 (Subgroup.commutator_mem_commutator (J.inv_mem hl) (Subgroup.mem_zpowers g))
    obtain ⟨c, hcO, hceq⟩ := hc
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hc' : (⟨l, hl⟩ * ⟨g, hgJ⟩ : ↥J)⁻¹ * (⟨g, hgJ⟩ * ⟨l, hl⟩) =
        (⟨g, hgJ⟩ : ↥J)⁻¹ * c * ⟨g, hgJ⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have : (c : G) = l⁻¹ * g * l⁻¹⁻¹ * g⁻¹ := by rw [← commutatorElement_def]; exact hceq
      rw [this]
      group
    rw [hc']
    have h := (GLAPPrimeCore.normal p ↥J).conj_mem c hcO (⟨g, hgJ⟩ : ↥J)⁻¹
    rwa [inv_inv] at h
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  exact ⟨⟨g, hgJ⟩, hcen, rfl⟩

theorem eq_one_of_mem_core {p : ℕ} (hp : p.Prime) {J : Subgroup G} {g : G}
    (hg : g ∈ GLAPPrimeCoreOf p J) (hgp : g ^ p = 1) : g = 1 := by
  have hcop := i183_coprime_card_glaPPrimeCoreOf hp J
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have h2 : orderOf g ∣ Nat.card (GLAPPrimeCoreOf p J) := Subgroup.orderOf_dvd_natCard _ hg
  have h3 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact orderOf_eq_one_iff.1 h3


theorem isPGroup_zpowers_of_pow {p : ℕ} (hp : p.Prime) {g : G} (hg : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1
    (show orderOf g ∣ p ^ 1 by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem glaPLayer_eq_of_uniq {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L)
    (huniq : ∀ J : Subgroup G, GLAPComponent p X J → J = L) : GLAPLayer p X = L := by
  unfold GLAPLayer
  apply le_antisymm
  · exact sSup_le fun J hJ => (huniq J hJ).le
  · exact le_sSup hL


theorem commutator_le_of_normalizes {H K : Subgroup G} (hKH : K ≤ Subgroup.normalizer (H : Set G)) :
    ⁅H, K⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro h hh k hk
  rw [commutatorElement_def]
  have : k * h⁻¹ * k⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 (hKH hk) h⁻¹).1 (H.inv_mem hh)
  have h2 := H.mul_mem hh this
  simpa [mul_assoc] using h2

theorem mem_normalizer_commutator {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hH hK ⊢
  unfold GLBConj at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

theorem exists_inv_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hG : IsCharTwoType G) {B F : Subgroup G}
    (hB : GLAIsBmax p B) (hFB : F ≤ B) (hF : ¬ IsCyclic F) :
    ∃ A R : Subgroup G, A ≤ F ∧ Nat.card A * p = Nat.card F ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧
      R ≤ Subgroup.centralizer (A : Set G) ∧ B ≤ Subgroup.normalizer (R : Set G) ∧ ⁅R, F⁆ = R := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hU1, hU2, hBU⟩ := hB.2.2
  set S : Set (Subgroup G) := {T | U ≤ T ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G)} with hS
  obtain ⟨T, ⟨hUT, hT2, hBT⟩, hTmax⟩ :=
    (Set.toFinite S).exists_maximal ⟨U, le_rfl, hU2, hBU⟩
  have hT1 : T ≠ ⊥ := fun h => hU1 (eq_bot_iff.2 (h ▸ hUT))
  have hmax : ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) → T ≤ T' →
      T' = T := fun T' hT'2 hBT' hTT' => le_antisymm (hTmax ⟨hUT.trans hTT', hT'2, hBT'⟩ hTT') hTT'
  have hF1 : F ≠ ⊥ := by
    intro h
    apply hF
    rw [h]
    infer_instance
  have hB1 : B ≠ ⊥ := fun h => hF1 (eq_bot_iff.2 (h ▸ hFB))
  obtain ⟨-, h2⟩ := GL83.I_33_1_proved G hG p hp hp2 B T hB1 hB.1 hT2 hBT (Or.inl ⟨hT1, hmax⟩)
  obtain ⟨⟨A₁, -, -, hA₁F, -, hidx, -, hne, -⟩, -⟩ := h2 F hF1 hFB hF
  have hFe : IsElemAbelian p F := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB.1 hFB
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (A₁ : Set G) with hQ
  have hFC : ∀ f ∈ F, f ∈ Subgroup.normalizer
      ((Subgroup.centralizer (A₁ : Set G) : Subgroup G) : Set G) := by
    intro f hf
    apply Subgroup.le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hFe (hA₁F ha) hf
  have hFQ : F ≤ Subgroup.normalizer (Q : Set G) := fun f hf =>
    mem_normalizer_inf (hBT (hFB hf)) (hFC f hf)
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := by
    intro b hb
    refine mem_normalizer_inf (hBT hb) (Subgroup.le_normalizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hB.1 (hFB (hA₁F ha)) hb
  have hBF : B ≤ Subgroup.normalizer (F : Set G) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact isElemAbelian_commute hB.1 (hFB hf) hb
  have hRQ : ⁅Q, F⁆ ≤ Q := commutator_le_of_normalizes hFQ
  have hQ2 : IsPGroup 2 Q := hT2.to_le inf_le_left
  have hcop : Nat.Coprime (Nat.card F) (Nat.card Q) := by
    obtain ⟨m, hm⟩ := (isPGroup_of_isElemAbelian hFe).exists_card_eq
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hm, hk]
    exact Nat.Coprime.pow m k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hRR : ⁅⁅Q, F⁆, F⁆ = ⁅Q, F⁆ := le_antisymm
    (commutator_le_of_normalizes fun f hf => mem_normalizer_commutator (hFQ hf) (Subgroup.le_normalizer hf))
    (CFSG.ClassicalInvolution.commutator_le_commutator_commutator_of_coprime Q F hFQ hcop)
  have hcardA : Nat.card A₁ * p = Nat.card F := by
    have h := Subgroup.card_mul_index (A₁.subgroupOf F)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁F).toEquiv] at h
    exact h
  refine ⟨A₁, ⁅Q, F⁆, hA₁F, hcardA, hQ2.to_le hRQ, ?_, hRQ.trans inf_le_right,
    fun b hb => mem_normalizer_commutator (hBQ hb) (hBF hb), hRR⟩
  rw [Subgroup.commutator_comm]
  exact hne

theorem lift_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    {W' T' : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)} (hW' : IsElemAbelian p W') (hT' : IsPGroup 2 T')
    (hT'1 : T' ≠ ⊥) (hWT : W' ≤ Subgroup.normalizer (T' : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :
    ∃ W U : Subgroup G, W ≤ X ∧ IsElemAbelian p W ∧ Nat.card W = Nat.card W' ∧ U ≤ X ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ W ≤ Subgroup.normalizer (U : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N₀ : Subgroup ↥X := GLAPPrimeCore p ↥X with hN₀
  have hN : ¬ p ∣ Nat.card N₀ :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X))
  obtain ⟨S, hSel, hSmap, hScard⟩ := exists_elemAbelian_lift N₀ hN hW'
  set T₁ : Subgroup ↥X := T'.comap (QuotientGroup.mk' N₀) with hT₁
  have hT₁card : Nat.card T₁ = Nat.card N₀ * Nat.card T' :=
    QuotientGroup.card_preimage_mk N₀ (T' : Set (↥X ⧸ N₀))
  obtain ⟨k, hk⟩ := hT'.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hT'1 (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
  have hT₁cop : Nat.Coprime p (Nat.card T₁) := by
    rw [hT₁card, hk]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hN)
      (Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have h2T₁ : 2 ∣ Nat.card T₁ := by
    rw [hT₁card, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hST : S ≤ Subgroup.normalizer (T₁ : Set ↥X) := by
    intro s hs
    have hsW' : QuotientGroup.mk' N₀ s ∈ W' := by
      rw [← hSmap]
      exact Subgroup.mem_map_of_mem _ hs
    have hnorm := Subgroup.mem_normalizer_iff.1 (hWT hsW')
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have := hnorm (QuotientGroup.mk' N₀ t)
    simpa [hT₁, Subgroup.mem_comap, map_mul, map_inv] using this
  obtain ⟨U', -, hU'2, hU'ne, hSU', -⟩ :=
    S3.exists_invariant_sylow hp Nat.prime_two hSel.isPGroup hST hT₁cop h2T₁
  refine ⟨S.map X.subtype, U'.map X.subtype, Subgroup.map_subtype_le _, hSel.map _, ?_,
    Subgroup.map_subtype_le _, ?_, hU'2.map _, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hScard]
  · intro h
    exact hU'ne ((Subgroup.map_eq_bot_iff_of_injective U' X.subtype_injective).1 h)
  · intro w hw
    obtain ⟨s, hs, rfl⟩ := hw
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨s * u * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSU' hs) u).1 hu, by simp⟩
    · rintro ⟨u, hu, hy⟩
      refine ⟨s⁻¹ * u * s, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hSU' (S.inv_mem hs)) u).1 hu
        simpa using this
      · have h1 : (u : G) = (s : G) * y * (s : G)⁻¹ := hy
        simp only [map_mul, map_inv, Subgroup.subtype_apply]
        rw [h1]
        group

theorem pQuot_conj (p : ℕ) (g : G) (J : Subgroup G) : Nonempty (PQuot p (GLBConj g J) ≃* PQuot p J) :=
  ⟨(conjQuotEquiv p g J).symm⟩

theorem isTypeWithCenter_congr {p : ℕ} {J J' : Subgroup G} (h : Nonempty (PQuot p J ≃* PQuot p J'))
    {Q : TauCeti.CFSGIndex → Prop} {z : ℕ} : IsTypeWithCenter p J Q z ↔ IsTypeWithCenter p J' Q z := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := nonempty_pSimple_congr e
  unfold IsTypeWithCenter
  rw [card_center_pQuot_congr e, catalogIs_congr f]

theorem isTypeWithCenter_conj {p : ℕ} {J : Subgroup G} (g : G) {Q : TauCeti.CFSGIndex → Prop} {z : ℕ}
    (h : IsTypeWithCenter p J Q z) : IsTypeWithCenter p (GLBConj g J) Q z :=
  (isTypeWithCenter_congr (pQuot_conj p g J)).2 h

theorem catalogIs_pSimple_conj {p : ℕ} {J : Subgroup G} (g : G) {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs (PSimple p J) Q) : catalogIs (PSimple p (GLBConj g J)) Q := by
  obtain ⟨e⟩ := pQuot_conj p g J
  obtain ⟨f⟩ := nonempty_pSimple_congr e
  exact (catalogIs_congr f).2 h

theorem eq_bot_of_perfect_of_isPGroup {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    {R : Subgroup Q} (hR : IsPGroup p R) (hperf : ⁅R, R⁆ = R) : R = ⊥ := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries R).1 hR.isNilpotent
  have h : ∀ k, R.lowerCentralSeries k = R := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, hperf]
  rw [← h n, hn]

theorem not_le_oPrimePOf {p : ℕ} (hp : p.Prime) {Y J M : Subgroup G} (hM : GLAPComponent p Y M)
    (hMJ : M ≤ J) (hMO : M ≤ CFSG.HardMathSupport.Solomon.LocalBalance.oPrimePOf p J) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥J) with hπ
  set Mb : Subgroup (PQuot p J) := (M.subgroupOf J).map π with hMb
  have hMbP : Mb ≤ CFSG.pCore p (PQuot p J) := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨m', hm', hmeq⟩ := hMO (Subgroup.mem_subgroupOf.1 hm)
    have : m' = m := Subtype.ext hmeq
    subst this
    exact hm'
  have hperf : ⁅Mb, Mb⁆ = Mb := by
    have hMp := glaPComponent_perfect hM
    have h1 : ⁅M.subgroupOf J, M.subgroupOf J⁆ = M.subgroupOf J := by
      apply Subgroup.map_injective J.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMJ, hMp]
    rw [hMb, ← Subgroup.map_commutator, h1]
  have hbot : Mb = ⊥ := eq_bot_of_perfect_of_isPGroup (CFSG.pCore_isPGroup.to_le hMbP) hperf
  have hMc : M ≤ GLAPPrimeCoreOf p J := by
    intro m hm
    have hmb : π ⟨m, hMJ hm⟩ ∈ Mb := ⟨⟨m, hMJ hm⟩, hm, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmb
    exact ⟨_, hmb, rfl⟩
  have hcop : p.Coprime (Nat.card M) :=
    (i183_coprime_card_glaPPrimeCoreOf hp J).coprime_dvd_right (Subgroup.card_dvd_of_le hMc)
  have htop : GLAPPrimeCore p ↥M = ⊤ := by
    refine le_antisymm le_top (le_sSup ⟨inferInstance, ?_⟩)
    rwa [Subgroup.card_top]
  haveI := isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hM)
  obtain ⟨u, v, huv⟩ := exists_pair_ne (PQuot p M)
  apply huv
  induction u using QuotientGroup.induction_on with
  | H u =>
    induction v using QuotientGroup.induction_on with
    | H v =>
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _

theorem oPrimePOf_le_core {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K)
    (hZ : Nat.card (Subgroup.center (PQuot p K)) = 1) :
    CFSG.HardMathSupport.Solomon.LocalBalance.oPrimePOf p K ≤ GLAPPrimeCoreOf p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI := isQuasisimple_nontrivial hq
  have hbotZ : Subgroup.center (PQuot p K) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  have hPne : CFSG.pCore p (PQuot p K) ≠ ⊤ := by
    intro htop
    have hperf : ⁅(⊤ : Subgroup (PQuot p K)), ⊤⁆ = ⊤ := hq.1
    have h1 := eq_bot_of_perfect_of_isPGroup (htop ▸ CFSG.pCore_isPGroup) hperf
    exact (bot_ne_top h1.symm)
  have hPZ : CFSG.pCore p (PQuot p K) ≤ Subgroup.center (PQuot p K) :=
    le_center_of_normal_of_isQuasisimple hq CFSG.pCore_normal hPne
  rw [hbotZ] at hPZ
  rintro _ ⟨k, hk, rfl⟩
  have hk' : QuotientGroup.mk' (GLAPPrimeCore p ↥K) k ∈ CFSG.pCore p (PQuot p K) := hk
  have hk1 := hPZ hk'
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact ⟨k, hk1, rfl⟩

theorem B_inv_of_contains {X Y B J M : Subgroup G} (hJ : GLAPComponent 3 X J) (hBX : B ≤ X)
    (hM : GLAPComponent 3 Y M) (hMJ : M ≤ J) (hBM : B ≤ Subgroup.normalizer (M : Set G)) :
    B ≤ Subgroup.normalizer (J : Set G) := by
  intro b hb
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hJb : GLAPComponent 3 X (GLBConj b J) := by
    have h1 := glaPComponent_gLBConj hJ b
    rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBX hb))] at h1
  have hint := CFSG.HardMathSupport.Solomon.LocalBalance.inf_le_oPrimePOf_of_ne Nat.prime_three hJ hJb
    (Ne.symm hne)
  have hMb : M ≤ GLBConj b J := by
    rw [← mem_normalizer_iff_gLBConj_eq.1 (hBM hb)]
    unfold GLBConj
    exact Subgroup.map_mono hMJ
  exact not_le_oPrimePOf Nat.prime_three hM hMJ ((le_inf hMJ hMb).trans hint)

theorem inf_core_le_core {p : ℕ} (hp : p.Prime) {I J : Subgroup G} (hIJ : I ≤ J) :
    I ⊓ GLAPPrimeCoreOf p J ≤ GLAPPrimeCoreOf p I := by
  set O := GLAPPrimeCoreOf p J with hO
  have hIO : I ≤ Subgroup.normalizer (O : Set G) := hIJ.trans (le_normalizer_glaPPrimeCoreOf p J)
  set N : Subgroup ↥I := (I ⊓ O).subgroupOf I with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨I.mul_mem (I.mul_mem g.2 hn.1) (I.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (hIO g.2) n).1 hn.2
  have hNc : Nat.Coprime p (Nat.card N) := by
    have h1 : Nat.card N = Nat.card (I ⊓ O : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (i183_coprime_card_glaPPrimeCoreOf hp J)
  have hle : N ≤ GLAPPrimeCore p ↥I := le_sSup ⟨hNn, hNc⟩
  intro y hy
  exact ⟨⟨y, hy.1⟩, hle ((Subgroup.mem_subgroupOf).2 hy), rfl⟩

theorem cover_of_card {p : ℕ} (hp : p.Prime) {I J : Subgroup G} (hIJ : I ≤ J)
    (hcard : Nat.card (PQuot p J) ≤ Nat.card (PQuot p I)) : J ≤ I ⊔ GLAPPrimeCoreOf p J := by
  set O := GLAPPrimeCoreOf p J with hO
  have hOJ : O ≤ J := Subgroup.map_subtype_le _
  have hIO : I ≤ Subgroup.normalizer (O : Set G) := hIJ.trans (le_normalizer_glaPPrimeCoreOf p J)
  have hJq : Nat.card J = Nat.card (PQuot p J) * Nat.card (GLAPPrimeCore p ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hIq : Nat.card I = Nat.card (PQuot p I) * Nat.card (GLAPPrimeCore p ↥I) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hOc : Nat.card O = Nat.card (GLAPPrimeCore p ↥J) :=
    Subgroup.card_map_of_injective J.subtype_injective
  have hOIc : Nat.card (GLAPPrimeCoreOf p I) = Nat.card (GLAPPrimeCore p ↥I) :=
    Subgroup.card_map_of_injective I.subtype_injective
  have hIOc : Nat.card (O ⊓ I : Subgroup G) ≤ Nat.card (GLAPPrimeCore p ↥I) := by
    rw [← hOIc, inf_comm]
    exact Subgroup.card_le_of_le (inf_core_le_core hp hIJ)
  have hsup := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hIO
  have hpos : 0 < Nat.card (O ⊓ I : Subgroup G) := Nat.card_pos
  have hle : I ⊔ O ≤ J := sup_le hIJ hOJ
  have hge : Nat.card J ≤ Nat.card (I ⊔ O : Subgroup G) := by
    rw [sup_comm, hJq, ← hOc]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [hsup, hIq]
    calc Nat.card (PQuot p J) * Nat.card O * Nat.card (O ⊓ I : Subgroup G)
        ≤ Nat.card (PQuot p I) * Nat.card O * Nat.card (GLAPPrimeCore p ↥I) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hcard) hIOc
      _ = Nat.card O * (Nat.card (PQuot p I) * Nat.card (GLAPPrimeCore p ↥I)) := by ring
  rw [Subgroup.eq_of_le_of_card_ge hle hge]

theorem pSimple_of_iso {p : ℕ} (hp : p.Prime) {X J K : Subgroup G} (hK : GLAPComponent p X K)
    (h : Nonempty (PQuot p J ≃* PSimple p K)) : Nonempty (PSimple p J ≃* PSimple p K) := by
  obtain ⟨e⟩ := h
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hsimple : IsSimpleGroup (PSimple p K) := hq.2
  obtain ⟨u, v, huv⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hZ : Subgroup.center (PSimple p K) = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (PSimple p K)) with h | h
    · exact h
    · exfalso
      apply huv
      have hu : u ∈ Subgroup.center (PSimple p K) := h ▸ Subgroup.mem_top u
      exact ((Subgroup.mem_center_iff.1 hu) v).symm
  have hmap : (Subgroup.center (PQuot p J)).map (e : PQuot p J →* PSimple p K) =
      Subgroup.center (PSimple p K) := Subgroup.map_center_eq e
  rw [hZ] at hmap
  have hZJ : Subgroup.center (PQuot p J) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot).trans e⟩

theorem exists_comp_of_sub (hlb : LBalanceAt G 3) {X P I : Subgroup G} (hX : CFSG.Open.IsKGroup ↥(X ⊔ P))
    (hP : IsPGroup 3 P) (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hI : GLAPComponent 3 (X ⊓ Subgroup.centralizer (P : Set G)) I) :
    ∃ Q : Subgroup G, GLAPComponent 3 X Q := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set X' := X ⊔ P with hX'
  have hXX' : X ≤ X' := le_sup_left
  have hPX' : P ≤ X' := le_sup_right
  have hX'N : X' ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hPX
  have hCle : X ⊓ Subgroup.centralizer (P : Set G) ≤ X' ⊓ Subgroup.centralizer (P : Set G) :=
    inf_le_inf_right _ hXX'
  have hnormC : X' ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.normalizer ((X ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf (hX'N hg.1) (Subgroup.le_normalizer hg.2)
  have hn : ((X ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
      (X' ⊓ Subgroup.centralizer (P : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCle).2 hnormC
  have hsub : IsSubnormal (X ⊓ Subgroup.centralizer (P : Set G)) (X' ⊓ Subgroup.centralizer (P : Set G)) :=
    IsSubnormal.step hCle hn (IsSubnormal.refl _)
  have hI' : GLAPComponent 3 (X' ⊓ Subgroup.centralizer (P : Set G)) I :=
    glaPComponent_of_isSubnormal' hp3 hsub hI
  have hne1 : GLAPLayer 3 (X' ⊓ Subgroup.centralizer (P : Set G)) ≠ ⊥ :=
    (S3.glaPLayer_ne_bot_iff hp3).2 ⟨I, hI'⟩
  have hle := hlb X' P hX hPX' hP
  have hne2 : GLAPLayer 3 X' ≠ ⊥ := fun h => hne1 (le_bot_iff.1 (h ▸ hle))
  obtain ⟨Q, hQ⟩ := (S3.glaPLayer_ne_bot_iff hp3).1 hne2
  have hnX : (X.subgroupOf X').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXX').2 hX'N
  have hQX : Q ≤ X :=
    CFSG.HardMathSupport.Solomon.Proving.glaPComponent_le_of_normal_sup_pGroup hp3 hXX' hnX hPX' hP
      le_rfl hQ
  exact ⟨Q, glaPComponent_of_le hp3 hQ hQX hXX'⟩


theorem single_of_family {X J₀ : Subgroup G} {𝒞 : Set (Subgroup G)}
    (hsup : (⨆ K ∈ 𝒞, K) = ⨆ g ∈ GLAPLayer 3 X, GLBConj g J₀) (hJ₀ : J₀ ≠ ⊥)
    (hall : ∀ K₁ ∈ 𝒞, ∀ K₂ ∈ 𝒞, K₁ = K₂) : ∃ J ∈ 𝒞, J₀ ≤ J := by
  have hle : J₀ ≤ ⨆ K ∈ 𝒞, K := by
    rw [hsup]
    have h1 : GLBConj 1 J₀ = J₀ := gLBConj_one J₀
    calc J₀ = GLBConj 1 J₀ := h1.symm
      _ ≤ ⨆ g ∈ GLAPLayer 3 X, GLBConj g J₀ :=
        le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 X) => GLBConj g J₀) 1 (GLAPLayer 3 X).one_mem
  by_cases hne : 𝒞.Nonempty
  · obtain ⟨J, hJ⟩ := hne
    refine ⟨J, hJ, hle.trans ?_⟩
    exact iSup₂_le fun K hK => (hall K hK J hJ).le
  · exfalso
    apply hJ₀
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [eq_bot_iff]
    refine hle.trans ?_
    rw [hne]
    simp

theorem three_members {E : Subgroup G} (hE : IsElemAbelian 3 E) {𝒞 : Set (Subgroup G)}
    (hstab : ∀ K ∈ 𝒞, ∀ e ∈ E, GLBConj e K ∈ 𝒞)
    (htr : ∀ K ∈ 𝒞, ∀ K' ∈ 𝒞, ∃ e ∈ E, GLBConj e K = K')
    {K₁ K₂ : Subgroup G} (h1 : K₁ ∈ 𝒞) (h2 : K₂ ∈ 𝒞) (hne : K₁ ≠ K₂) :
    ∃ e ∈ E, GLBConj e K₁ ∈ 𝒞 ∧ GLBConj e (GLBConj e K₁) ∈ 𝒞 ∧ K₁ ≠ GLBConj e K₁ ∧
      K₁ ≠ GLBConj e (GLBConj e K₁) ∧ GLBConj e K₁ ≠ GLBConj e (GLBConj e K₁) := by
  obtain ⟨e, he, hK₂⟩ := htr K₁ h1 K₂ h2
  have hne1 : K₁ ≠ GLBConj e K₁ := hK₂ ▸ hne
  have he3 : e * (e * e) = 1 := by
    rw [← pow_three]
    exact hE.2 e he
  refine ⟨e, he, hstab _ h1 e he, hstab _ (hstab _ h1 e he) e he, hne1, ?_, ?_⟩
  · intro h
    apply hne1
    have h' : GLBConj e K₁ = GLBConj e (GLBConj e (GLBConj e K₁)) := by rw [← h]
    rw [h', gLBConj_gLBConj, gLBConj_gLBConj, he3, gLBConj_one]
  · intro h
    apply hne1
    have h' := congrArg (GLBConj e⁻¹) h
    rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at h'

theorem card_three_comp_sup {Q : Type*} [Group Q] [Finite Q] {J₁ J₂ J₃ D : Subgroup Q}
    (h12 : ⁅J₁, J₂⁆ = ⊥) (h13 : ⁅J₁, J₃⁆ = ⊥) (h23 : ⁅J₂, J₃⁆ = ⊥) {y₁ y₂ y₃ : Q}
    (hy₁ : y₁ ∈ J₁) (hy₂ : y₂ ∈ J₂) (hy₃ : y₃ ∈ J₃) (ho₁ : orderOf y₁ = 3) (ho₂ : orderOf y₂ = 3)
    (ho₃ : orderOf y₃ = 3) (hz₁ : ∃ z ∈ J₁, z * y₁ ≠ y₁ * z) (hz₂ : ∃ z ∈ J₂, z * y₂ ≠ y₂ * z)
    (hz₃ : ∃ z ∈ J₃, z * y₃ ≠ y₃ * z) (hD : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    (hDZ : D ≤ Subgroup.center Q) :
    IsElemAbelian 3 (Subgroup.closure {y₁, y₂, y₃} ⊔ D) ∧
      Nat.card (Subgroup.closure {y₁, y₂, y₃} ⊔ D : Subgroup Q) = 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have cJ : ∀ {H K : Subgroup Q}, ⁅H, K⁆ = ⊥ → ∀ a ∈ H, ∀ b ∈ K, a * b = b * a := by
    intro H K h a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha) b hb).symm
  have c12 := cJ h12
  have c13 := cJ h13
  have c23 := cJ h23
  have hy3 : ∀ {y : Q}, orderOf y = 3 → y ^ 3 = 1 := fun {y} h => by
    have := pow_orderOf_eq_one y
    rwa [h] at this
  have K : ∀ {J : Subgroup Q} {y : Q}, orderOf y = 3 → (∃ z ∈ J, z * y ≠ y * z) →
      ∀ g ∈ Subgroup.zpowers y, (∀ z ∈ J, z * g = g * z) → g = 1 := by
    intro J y hy hz g hg hcg
    by_contra hg1
    obtain ⟨z, hzJ, hzy⟩ := hz
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3 hy, one_zpow]
    have hog : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    have hle : Subgroup.zpowers g ≤ Subgroup.zpowers y := Subgroup.zpowers_le.2 hg
    have heq : Subgroup.zpowers g = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hog, hy])
    have hyg : y ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyg
    apply hzy
    rw [← hk]
    exact ((show Commute z g from hcg z hzJ).zpow_right k).eq
  set A₁ := Subgroup.zpowers y₁ with hA₁
  set A₂ := Subgroup.zpowers y₂ with hA₂
  set A₃ := Subgroup.zpowers y₃ with hA₃
  have hA₁J : A₁ ≤ J₁ := Subgroup.zpowers_le.2 hy₁
  have hA₂J : A₂ ≤ J₂ := Subgroup.zpowers_le.2 hy₂
  have hA₃J : A₃ ≤ J₃ := Subgroup.zpowers_le.2 hy₃
  have hcA₁ : Nat.card A₁ = 3 := by rw [hA₁, Nat.card_zpowers, ho₁]
  have hcA₂ : Nat.card A₂ = 3 := by rw [hA₂, Nat.card_zpowers, ho₂]
  have hcA₃ : Nat.card A₃ = 3 := by rw [hA₃, Nat.card_zpowers, ho₃]
  have hel₁ : IsElemAbelian 3 A₁ := CFSG.Open.isElemAbelian_zpowers (hy3 ho₁)
  have hel₂ : IsElemAbelian 3 A₂ := CFSG.Open.isElemAbelian_zpowers (hy3 ho₂)
  have hel₃ : IsElemAbelian 3 A₃ := CFSG.Open.isElemAbelian_zpowers (hy3 ho₃)
  have cA12 : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb => c12 a (hA₁J ha) b (hA₂J hb)
  set S12 := A₁ ⊔ A₂ with hS12
  have hel12 : IsElemAbelian 3 S12 := IsElemAbelian.sup_of_commute hel₁ hel₂ cA12
  have d1 : A₁ ⊓ A₂ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact K ho₁ hz₁ g hg.1 (fun z hz => c12 z hz g (hA₂J hg.2))
  have hnorm12 : A₂ ≤ Subgroup.normalizer (A₁ : Set Q) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer (A₁ : Set Q))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact cA12 a ha b hb
  have card12 : Nat.card S12 = 9 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnorm12
    rw [d1, Subgroup.card_bot, mul_one, hcA₁, hcA₂] at h
    omega
  have hS12J₃ : ∀ s ∈ S12, ∀ z ∈ J₃, z * s = s * z := by
    have hle : S12 ≤ Subgroup.centralizer (J₃ : Set Q) := by
      refine sup_le ?_ ?_
      · exact hA₁J.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h13)
      · exact hA₂J.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h23)
    intro s hs z hz
    exact Subgroup.mem_centralizer_iff.1 (hle hs) z hz
  have d2 : S12 ⊓ A₃ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact K ho₃ hz₃ g hg.2 (fun z hz => hS12J₃ g hg.1 z hz)
  have hnorm3 : A₃ ≤ Subgroup.normalizer (S12 : Set Q) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer (S12 : Set Q))
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hS12J₃ a ha b (hA₃J hb)).symm
  have card123 : Nat.card (S12 ⊔ A₃ : Subgroup Q) = 27 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnorm3
    rw [d2, Subgroup.card_bot, mul_one, card12, hcA₃] at h
    omega
  have hel123 : IsElemAbelian 3 (S12 ⊔ A₃) :=
    IsElemAbelian.sup_of_commute hel12 hel₃ (fun a ha b hb => (hS12J₃ a ha b (hA₃J hb)).symm)
  have hW₀ : Subgroup.closure {y₁, y₂, y₃} = S12 ⊔ A₃ := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
      · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
      · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  have hD1 : ∀ d ∈ D, ∀ z : Q, z * d = d * z := fun d hd z => Subgroup.mem_center_iff.1 (hDZ hd) z
  have hS12A₃ : S12 ≤ Subgroup.centralizer (A₃ : Set Q) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact hS12J₃ s hs c (hA₃J hc)
  have hA₁A₂ : A₁ ≤ Subgroup.centralizer (A₂ : Set Q) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (cA12 a ha b hb).symm
  have d3 : (S12 ⊔ A₃) ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨hgW, hgD⟩ := hg
    have hmem : g ∈ ((S12 : Set Q) * (A₃ : Set Q)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S12 A₃
        (hS12A₃.trans (Subgroup.centralizer_le_normalizer _))]
      exact hgW
    obtain ⟨s, hs, c, hc, hsc⟩ := Set.mem_mul.1 hmem
    have hmem2 : s ∈ ((A₁ : Set Q) * (A₂ : Set Q)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A₁ A₂
        (hA₁A₂.trans (Subgroup.centralizer_le_normalizer _))]
      exact hs
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hmem2
    have hg : g = a * b * c := by rw [← hsc, ← hab]
    have hcg : ∀ z : Q, Commute z g := fun z => hD1 g hgD z
    have ha1 : a = 1 := by
      have hae : a = g * c⁻¹ * b⁻¹ := by rw [hg]; group
      refine K ho₁ hz₁ a ha (fun z hz => ?_)
      have h1 : Commute z c⁻¹ := (show Commute z c from c13 z hz c (hA₃J hc)).inv_right
      have h2 : Commute z b⁻¹ := (show Commute z b from c12 z hz b (hA₂J hb)).inv_right
      have h3 : Commute z a := by rw [hae]; exact (((hcg z).mul_right h1).mul_right h2)
      exact h3.eq
    have hb1 : b = 1 := by
      have hbe : b = g * c⁻¹ := by rw [hg, ha1]; group
      refine K ho₂ hz₂ b hb (fun z hz => ?_)
      have h1 : Commute z c⁻¹ := (show Commute z c from c23 z hz c (hA₃J hc)).inv_right
      have h3 : Commute z b := by rw [hbe]; exact ((hcg z).mul_right h1)
      exact h3.eq
    have hc1 : c = 1 := by
      have hce : c = g := by rw [hg, ha1, hb1]; group
      exact K ho₃ hz₃ c hc (fun z hz => by rw [hce]; exact (hcg z).eq)
    rw [hg, ha1, hb1, hc1]
    group
  have hnormD : D ≤ Subgroup.normalizer ((S12 ⊔ A₃ : Subgroup Q) : Set Q) :=
    (hDZ.trans (Subgroup.center_le_centralizer _)).trans (Subgroup.centralizer_le_normalizer _)
  have card5 : Nat.card ((S12 ⊔ A₃) ⊔ D : Subgroup Q) = 3 ^ 5 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnormD
    rw [d3, Subgroup.card_bot, mul_one, card123, hDc] at h
    omega
  rw [hW₀]
  exact ⟨IsElemAbelian.sup_of_commute hel123 hD (fun a ha d hd => hD1 d hd a), card5⟩

theorem pump_normalizes {B Q Y' M : Subgroup G} (hY'B : Y' ≤ B)
    (hconj : ∀ q ∈ Q, B ≤ Subgroup.normalizer ((GLBConj q M : Subgroup G) : Set G))
    (hQ : Q ≤ ⁅Q, Y'⁆) (hY' : ∀ y ∈ Y', CentMod 3 M y) :
    Q ≤ Subgroup.normalizer (M : Set G) ∧ ∀ q ∈ Q, CentMod 3 M q := by
  have hN : Q ≤ Subgroup.normalizer (M : Set G) :=
    S3.normalizes_of_comm (fun q hq => (hY'B.trans (hconj q hq))) hQ
  have hA : Y' ≤ centModSubgroup 3 M := fun y hy => centMod_iff.1 (hY' y hy)
  have hC := S3.le_centModSubgroup_of_comm hA hN hQ
  exact ⟨hN, fun q hq => centMod_iff.2 (hC hq)⟩

theorem le_normalizer_sup_core {p : ℕ} (hp : p.Prime) {X M Q Y'' : Subgroup G} (hM : GLAPComponent p X M)
    (hQX : Q ≤ X) (hQc : ∀ q ∈ Q, CentMod p M q) (hY''X : Y'' ≤ X)
    (hY''Q : Y'' ≤ Subgroup.normalizer (Q : Set G)) :
    M ⊔ Y'' ≤ Subgroup.normalizer ((Q ⊔ GLAPPrimeCoreOf p X : Subgroup G) : Set G) := by
  have hOX : X ≤ Subgroup.normalizer (GLAPPrimeCoreOf p X : Set G) := le_normalizer_glaPPrimeCoreOf p X
  have hOM : GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p X := glaPPrimeCoreOf_le_of_isSubnormal hp hM.2.1
  refine sup_le ?_ ?_
  · intro m hm
    rw [mem_normalizer_iff_gLBConj_eq]
    have hmX : m ∈ X := hM.1 hm
    have hle : GLBConj m (Q ⊔ GLAPPrimeCoreOf p X) ≤ Q ⊔ GLAPPrimeCoreOf p X := by
      have hO := mem_normalizer_iff_gLBConj_eq.1 (hOX hmX)
      unfold GLBConj at hO ⊢
      rw [Subgroup.map_sup, hO]
      refine sup_le ?_ le_sup_right
      rintro _ ⟨q, hq, rfl⟩
      have hc : ⁅m⁻¹, q⁆ ∈ GLAPPrimeCoreOf p X :=
        hOM ((hQc q hq).2 (Subgroup.commutator_mem_commutator (M.inv_mem hm) (Subgroup.mem_zpowers q)))
      have heq : (MulAut.conj m⁻¹).toMonoidHom q = ⁅m⁻¹, q⁆ * q := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hq)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    unfold GLBConj
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
  · intro y hy
    exact mem_normalizer_sup (hY''Q hy) (hOX (hY''X hy))

theorem pump_contra {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X Q W : Subgroup G} (hQX : Q ≤ X)
    (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) (hW : IsElemAbelian p W)
    (hWN : W ≤ Subgroup.normalizer ((Q ⊔ GLAPPrimeCoreOf p X : Subgroup G) : Set G)) :
    Nat.card W ≤ p ^ GLATwoLocalRank p G := by
  set O := GLAPPrimeCoreOf p X with hO
  set N : Subgroup G := Q ⊔ O with hN
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) := hQX.trans (le_normalizer_glaPPrimeCoreOf p X)
  have hprod := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hQO
  have hNeq : Nat.card N = Nat.card (O ⊔ Q : Subgroup G) := by rw [hN, sup_comm]
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hcopO : p.Coprime (Nat.card O) := i183_coprime_card_glaPPrimeCoreOf hp X
  have hcop2 : p.Coprime (Nat.card Q) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdvd : Nat.card N ∣ Nat.card O * Nat.card Q := by
    rw [hNeq, ← hprod]
    exact dvd_mul_right _ _
  have hcopN : p.Coprime (Nat.card N) := Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right hcopO hcop2)
  have h2Q : 2 ∣ Nat.card Q := by
    rw [hk]
    rcases k with _ | k
    · exfalso
      apply hQ1
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have h2N : 2 ∣ Nat.card N := h2Q.trans (Subgroup.card_dvd_of_le le_sup_left)
  obtain ⟨S, -, hS2, hSne, hWS, -⟩ := S3.exists_invariant_sylow hp Nat.prime_two
    (isPGroup_of_isElemAbelian hW) hWN hcopN h2N
  exact card_le_pow_glaTwoLocalRank hp hW hSne hS2 hWS

theorem exists_pSubgroup_relIndex {p : ℕ} (hp : p.Prime) {C N : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) {k : ℕ} (hk : p ^ k ∣ C.relIndex N) :
    ∃ Q : Subgroup G, Q ≤ N ∧ IsPGroup p Q ∧ p ^ k ∣ C.relIndex Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C' : Subgroup ↥N := C.subgroupOf N with hC'
  haveI hC'n : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).2 hNC
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := ↥N)
  refine ⟨(P : Subgroup ↥N).map N.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map N.subtype, ?_⟩
  rw [← Subgroup.relIndex_comap]
  change p ^ k ∣ C'.relIndex P
  rw [← Subgroup.relIndex_sup_right]
  have h1 : C'.relIndex ((P : Subgroup ↥N) ⊔ C') * ((P : Subgroup ↥N) ⊔ C').index = C'.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have h2 : ((P : Subgroup ↥N) ⊔ C').index ∣ (P : Subgroup ↥N).index := Subgroup.index_dvd_of_le le_sup_left
  have h3 : ¬ p ∣ (P : Subgroup ↥N).index := P.not_dvd_index
  have hcop : Nat.Coprime (p ^ k) ((P : Subgroup ↥N) ⊔ C').index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => h3 (h.trans h2))
  have h4 : p ^ k ∣ C'.relIndex ((P : Subgroup ↥N) ⊔ C') * ((P : Subgroup ↥N) ⊔ C').index := by
    rw [h1]
    exact hk
  exact hcop.dvd_of_dvd_mul_right h4

@[expose] def conjOrbit (N : Subgroup G) (y : G) : Set G := {z | ∃ g ∈ N, g * y * g⁻¹ = z}

theorem three_dvd_orbit {A : Subgroup G} {x : G}
    (h3 : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ cx x → (∃ k : ℕ, g ^ (3 ^ k) = 1) →
      g ∈ Subgroup.centralizer (A : Set G))
    {n : G} (hnN : n ∈ Subgroup.normalizer (A : Set G)) (hn3 : ∃ k : ℕ, n ^ (3 ^ k) = 1)
    (hnA : n ∉ Subgroup.centralizer (A : Set G)) :
    3 ∣ (conjOrbit (Subgroup.normalizer (A : Set G)) x).ncard := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (A : Set G) with hN
  set O := conjOrbit N x with hO
  obtain ⟨k, hk⟩ := hn3
  have hZ3 : IsPGroup 3 (Subgroup.zpowers n) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hZN : Subgroup.zpowers n ≤ N := (Subgroup.zpowers_le).2 hnN
  have hmem : ∀ z ∈ Subgroup.zpowers n, ∀ y ∈ O, z * y * z⁻¹ ∈ O := by
    rintro z hz y ⟨g, hg, rfl⟩
    exact ⟨z * g, N.mul_mem (hZN hz) hg, by group⟩
  letI : MulAction (Subgroup.zpowers n) O :=
    { smul := fun z y => ⟨(z : G) * y * (z : G)⁻¹, hmem z z.2 y y.2⟩
      one_smul := fun y => Subtype.ext (show ((1 : Subgroup.zpowers n) : G) * (y : G) *
          ((1 : Subgroup.zpowers n) : G)⁻¹ = (y : G) by simp)
      mul_smul := fun z w y => Subtype.ext (show ((z * w : Subgroup.zpowers n) : G) * (y : G) *
          ((z * w : Subgroup.zpowers n) : G)⁻¹ =
            (z : G) * ((w : G) * (y : G) * (w : G)⁻¹) * (z : G)⁻¹ by
          simp only [Subgroup.coe_mul]; group) }
  by_contra hndvd
  have hcard : ¬ 3 ∣ Nat.card O := by rwa [Nat.card_coe_set_eq]
  obtain ⟨y, hy⟩ := hZ3.nonempty_fixed_point_of_prime_not_dvd_card O hcard
  obtain ⟨g, hgN, hgy⟩ := y.2
  have hfix : n * (y : G) * n⁻¹ = y :=
    congrArg Subtype.val (MulAction.mem_fixedPoints.1 hy ⟨n, Subgroup.mem_zpowers n⟩)
  rw [← hgy] at hfix
  have hcx : g⁻¹ * n * g ∈ cx x := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * n * g * x = g⁻¹ * (n * (g * x * g⁻¹) * n⁻¹) * (n * g) := by group
      _ = g⁻¹ * (g * x * g⁻¹) * (n * g) := by rw [hfix]
      _ = x * (g⁻¹ * n * g) := by group
  have hN' : g⁻¹ * n * g ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hgN) hnN) hgN
  have h3' : ∃ k : ℕ, (g⁻¹ * n * g) ^ (3 ^ k) = 1 := by
    refine ⟨k, ?_⟩
    have h := conj_pow (a := g⁻¹) (b := n) (i := 3 ^ k)
    rw [inv_inv] at h
    rw [h, hk]
    group
  have hC := h3 _ hN' hcx h3'
  apply hnA
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : g⁻¹ * b * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (N.inv_mem hgN) b).1 hb
    rwa [inv_inv] at this
  have hcomm := Subgroup.mem_centralizer_iff.1 hC _ hb'
  calc b * n = g * ((g⁻¹ * b * g) * (g⁻¹ * n * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * n * g) * (g⁻¹ * b * g)) * g⁻¹ := by rw [hcomm]
    _ = n * b := by group

open Classical in
theorem ncard_inter_block {S Bk : Set G} (hB : Bk.ncard = 80) (hfull : (S ∩ Bk).Nonempty → Bk ⊆ S) :
    (S ∩ Bk).ncard = if Bk ⊆ S then 80 else 0 := by
  by_cases h : Bk ⊆ S
  · rw [if_pos h, Set.inter_eq_right.2 h, hB]
  · rw [if_neg h]
    have : S ∩ Bk = ∅ := by
      by_contra hne
      exact h (hfull (Set.nonempty_iff_ne_empty.2 hne))
    rw [this, Set.ncard_empty]

open Classical in
theorem ncard_inter_singleton (S : Set G) (a : G) : (S ∩ {a}).ncard = if a ∈ S then 1 else 0 := by
  by_cases h : a ∈ S
  · rw [if_pos h, Set.inter_eq_right.2 (Set.singleton_subset_iff.2 h), Set.ncard_singleton]
  · rw [if_neg h]
    have : S ∩ {a} = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hy rfl
      exact h hy
    rw [this, Set.ncard_empty]

theorem ncard_union_five {S Q₁ Q₂ Q₃ Q₄ Q₅ : Set G} (h12 : Disjoint Q₁ Q₂) (h13 : Disjoint Q₁ Q₃)
    (h14 : Disjoint Q₁ Q₄) (h15 : Disjoint Q₁ Q₅) (h23 : Disjoint Q₂ Q₃) (h24 : Disjoint Q₂ Q₄)
    (h25 : Disjoint Q₂ Q₅) (h34 : Disjoint Q₃ Q₄) (h35 : Disjoint Q₃ Q₅) (h45 : Disjoint Q₄ Q₅)
    (hcov : S ⊆ Q₁ ∪ Q₂ ∪ Q₃ ∪ Q₄ ∪ Q₅) :
    S.ncard = (S ∩ Q₁).ncard + (S ∩ Q₂).ncard + (S ∩ Q₃).ncard + (S ∩ Q₄).ncard + (S ∩ Q₅).ncard := by
  have hS : S = (S ∩ Q₁) ∪ (S ∩ Q₂) ∪ (S ∩ Q₃) ∪ (S ∩ Q₄) ∪ (S ∩ Q₅) := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hy
      have := hcov hy
      simp only [Set.mem_union] at this
      tauto
    · intro hy
      tauto
  have d12 : Disjoint (S ∩ Q₁) (S ∩ Q₂) := h12.mono Set.inter_subset_right Set.inter_subset_right
  have d13 : Disjoint (S ∩ Q₁) (S ∩ Q₃) := h13.mono Set.inter_subset_right Set.inter_subset_right
  have d14 : Disjoint (S ∩ Q₁) (S ∩ Q₄) := h14.mono Set.inter_subset_right Set.inter_subset_right
  have d15 : Disjoint (S ∩ Q₁) (S ∩ Q₅) := h15.mono Set.inter_subset_right Set.inter_subset_right
  have d23 : Disjoint (S ∩ Q₂) (S ∩ Q₃) := h23.mono Set.inter_subset_right Set.inter_subset_right
  have d24 : Disjoint (S ∩ Q₂) (S ∩ Q₄) := h24.mono Set.inter_subset_right Set.inter_subset_right
  have d25 : Disjoint (S ∩ Q₂) (S ∩ Q₅) := h25.mono Set.inter_subset_right Set.inter_subset_right
  have d34 : Disjoint (S ∩ Q₃) (S ∩ Q₄) := h34.mono Set.inter_subset_right Set.inter_subset_right
  have d35 : Disjoint (S ∩ Q₃) (S ∩ Q₅) := h35.mono Set.inter_subset_right Set.inter_subset_right
  have d45 : Disjoint (S ∩ Q₄) (S ∩ Q₅) := h45.mono Set.inter_subset_right Set.inter_subset_right
  conv_lhs => rw [hS]
  rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
      ⟨d15, d25⟩, d35⟩, d45⟩) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨d14, d24⟩, d34⟩)
      (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨d13, d23⟩) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq d12 (Set.toFinite _) (Set.toFinite _)]

open Classical in
theorem card_inv_set {A H : Subgroup G} {x : G} (hA : IsElemAbelian 3 A) (hHA : H ≤ A)
    (hH : Nat.card H = 3 ^ 4) (hxA : x ∈ A) (hxH : x ∉ H) (hAHx : A ≤ H ⊔ Subgroup.zpowers x)
    (hU : ∀ h ∈ H, h ≠ 1 → ∀ h' ∈ H, h' ≠ 1 → ∃ u ∈ Subgroup.normalizer (A : Set G),
      u ∈ cx x ∧ u ∈ Subgroup.normalizer (H : Set G) ∧ u * h * u⁻¹ = h')
    (S : Set G) (hSA : S ⊆ (A : Set G)) (hS1 : (1 : G) ∉ S)
    (hSinv : ∀ u ∈ Subgroup.normalizer (A : Set G), u ∈ cx x → u ∈ Subgroup.normalizer (H : Set G) →
      ∀ s ∈ S, u * s * u⁻¹ ∈ S) :
    ∃ m : ℕ, m ≤ 3 ∧
      S.ncard = (if x ∈ S then 1 else 0) + (if x⁻¹ ∈ S then 1 else 0) + 80 * m := by
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxxx : x * x * x = 1 := by simpa [pow_succ] using hx3
  have hx2 : x * x = x⁻¹ := eq_inv_of_mul_eq_one_left hxxx
  have hxinvH : x⁻¹ ∉ H := fun h => hxH (by simpa using H.inv_mem h)
  have hxinv : x⁻¹ ≠ x := by
    intro h
    have h' : x * x = x := by rw [hx2, h]
    exact hx1 (mul_eq_left.1 h')
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => isElemAbelian_commute hA ha hb
  obtain ⟨Hs, hHs⟩ : ∃ Hs : Set G, Hs = (H : Set G) \ {1} := ⟨_, rfl⟩
  obtain ⟨B3, hB3⟩ : ∃ B : Set G, B = (fun h => x * h) '' Hs := ⟨_, rfl⟩
  obtain ⟨B5, hB5⟩ : ∃ B : Set G, B = (fun h => x⁻¹ * h) '' Hs := ⟨_, rfl⟩
  have hmemHs : ∀ h, h ∈ Hs ↔ h ∈ H ∧ h ≠ 1 := fun h => by simp [hHs]
  have hmem3 : ∀ a, a ∈ B3 ↔ ∃ h ∈ H, h ≠ 1 ∧ x * h = a := fun a => by
    rw [hB3]; constructor
    · rintro ⟨h, hh, hha⟩
      exact ⟨h, ((hmemHs h).1 hh).1, ((hmemHs h).1 hh).2, hha⟩
    · rintro ⟨h, hh, hh1, hha⟩
      exact ⟨h, (hmemHs h).2 ⟨hh, hh1⟩, hha⟩
  have hmem5 : ∀ a, a ∈ B5 ↔ ∃ h ∈ H, h ≠ 1 ∧ x⁻¹ * h = a := fun a => by
    rw [hB5]; constructor
    · rintro ⟨h, hh, hha⟩
      exact ⟨h, ((hmemHs h).1 hh).1, ((hmemHs h).1 hh).2, hha⟩
    · rintro ⟨h, hh, hh1, hha⟩
      exact ⟨h, (hmemHs h).2 ⟨hh, hh1⟩, hha⟩
  have hc1 : ∀ h ∈ H, x * h ∉ H := fun h hh hxh => hxH (by simpa using H.mul_mem hxh (H.inv_mem hh))
  have hc2 : ∀ h ∈ H, x⁻¹ * h ∉ H := fun h hh hxh => hxinvH (by simpa using H.mul_mem hxh (H.inv_mem hh))
  have hc12 : ∀ h ∈ H, ∀ h' ∈ H, x * h ≠ x⁻¹ * h' := by
    intro h hh h' hh' heq
    apply hxinvH
    have h1 : x⁻¹ * h = h' := by
      calc x⁻¹ * h = (x * x) * h := by rw [hx2]
        _ = x * (x * h) := by rw [mul_assoc]
        _ = x * (x⁻¹ * h') := by rw [heq]
        _ = h' := by group
    have : x⁻¹ = h' * h⁻¹ := by rw [← h1]; group
    rw [this]
    exact H.mul_mem hh' (H.inv_mem hh)
  have h12 : Disjoint Hs {x} := by
    rw [Set.disjoint_left]
    intro a ha hb
    have : a = x := hb
    rw [this] at ha
    exact hxH ((hmemHs _).1 ha).1
  have h13 : Disjoint Hs B3 := by
    rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨h, hh, -, hha⟩ := (hmem3 a).1 hb
    exact hc1 h hh (hha ▸ ((hmemHs _).1 ha).1)
  have h14 : Disjoint Hs {x⁻¹} := by
    rw [Set.disjoint_left]
    intro a ha hb
    have : a = x⁻¹ := hb
    rw [this] at ha
    exact hxinvH ((hmemHs _).1 ha).1
  have h15 : Disjoint Hs B5 := by
    rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨h, hh, -, hha⟩ := (hmem5 a).1 hb
    exact hc2 h hh (hha ▸ ((hmemHs _).1 ha).1)
  have h23 : Disjoint ({x} : Set G) B3 := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hax : a = x := ha
    obtain ⟨h, hh, hh1, hha⟩ := (hmem3 a).1 hb
    apply hh1
    have h1 : x * h = x * 1 := by rw [mul_one, hha, hax]
    exact mul_left_cancel h1
  have h24 : Disjoint ({x} : Set G) {x⁻¹} := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hax : a = x := ha
    have hbx : a = x⁻¹ := hb
    exact hxinv (hbx.symm.trans hax)
  have h25 : Disjoint ({x} : Set G) B5 := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hax : a = x := ha
    obtain ⟨h, hh, hh1, hha⟩ := (hmem5 a).1 hb
    apply hxinvH
    have : h = x⁻¹ := by
      calc h = x * (x⁻¹ * h) := by group
        _ = x * x := by rw [hha, hax]
        _ = x⁻¹ := hx2
    rw [← this]
    exact hh
  have h34 : Disjoint B3 {x⁻¹} := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hbx : a = x⁻¹ := hb
    obtain ⟨h, hh, hh1, hha⟩ := (hmem3 a).1 ha
    apply hxH
    have : h = x := by
      calc h = x⁻¹ * (x * h) := by group
        _ = x⁻¹ * x⁻¹ := by rw [hha, hbx]
        _ = x := by rw [← mul_inv_rev, hx2, inv_inv]
    rw [← this]
    exact hh
  have h35 : Disjoint B3 B5 := by
    rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨h, hh, hh1, hha⟩ := (hmem3 a).1 ha
    obtain ⟨h', hh', hh1', hha'⟩ := (hmem5 a).1 hb
    exact hc12 h hh h' hh' (hha.trans hha'.symm)
  have h45 : Disjoint ({x⁻¹} : Set G) B5 := by
    rw [Set.disjoint_left]
    intro a ha hb
    have hax : a = x⁻¹ := ha
    obtain ⟨h, hh, hh1, hha⟩ := (hmem5 a).1 hb
    apply hh1
    have h1 : x⁻¹ * h = x⁻¹ * 1 := by rw [mul_one, hha, hax]
    exact mul_left_cancel h1
  have hHcard : (H : Set G).ncard = 81 := by
    have h1 : (H : Set G).ncard = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm
    rw [h1, hH]
    norm_num
  have hHs80 : Hs.ncard = 80 := by
    rw [hHs, Set.ncard_diff_singleton_of_mem H.one_mem, hHcard]
  have hB3_80 : B3.ncard = 80 := by
    rw [hB3, Set.ncard_image_of_injective _ (mul_right_injective x), hHs80]
  have hB5_80 : B5.ncard = 80 := by
    rw [hB5, Set.ncard_image_of_injective _ (mul_right_injective x⁻¹), hHs80]
  have hHn : H ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((show Commute x h from hcomm x hxA h (hHA hh)).zpow_left k).eq
  have hcov : S ⊆ Hs ∪ {x} ∪ B3 ∪ {x⁻¹} ∪ B5 := by
    intro s hs
    have hsA' := hSA hs
    have hs1 : s ≠ 1 := fun h => hS1 (h ▸ hs)
    have hsm : s ∈ ((H : Set G) * (Subgroup.zpowers x : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right H (Subgroup.zpowers x) hHn]
      exact hAHx hsA'
    obtain ⟨h, hh, z, hz, hhz⟩ := Set.mem_mul.1 hsm
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hk : x ^ k = x ^ (k % 3) := zpow_eq_zpow_emod k (by simpa using hx3)
    have hxh : x * h = h * x := (hcomm x hxA h (hHA hh))
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1' | h2
    · rw [hk, h0, zpow_zero, mul_one] at hhz
      subst hhz
      exact Or.inl (Or.inl (Or.inl (Or.inl ((hmemHs h).2 ⟨hh, hs1⟩))))
    · rw [hk, h1', zpow_one] at hhz
      by_cases hh1 : h = 1
      · rw [hh1, one_mul] at hhz
        subst hhz
        exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
      · have : s = x * h := by rw [← hhz, hxh]
        exact Or.inl (Or.inl (Or.inr ((hmem3 s).2 ⟨h, hh, hh1, this.symm⟩)))
    · rw [hk, h2] at hhz
      have hz2 : x ^ (2 : ℤ) = x⁻¹ := by rw [zpow_two, hx2]
      rw [hz2] at hhz
      have hxih : x⁻¹ * h = h * x⁻¹ := (show Commute x⁻¹ h from (show Commute x h from hxh).inv_left).eq
      by_cases hh1 : h = 1
      · rw [hh1, one_mul] at hhz
        subst hhz
        exact Or.inl (Or.inr rfl)
      · have : s = x⁻¹ * h := by rw [← hhz, hxih]
        exact Or.inr ((hmem5 s).2 ⟨h, hh, hh1, this.symm⟩)
  have hfull1 : (S ∩ Hs).Nonempty → Hs ⊆ S := by
    rintro ⟨s, hsS, hsHs⟩ t ht
    obtain ⟨u, hu, hux, huH, hust⟩ := hU s ((hmemHs s).1 hsHs).1 ((hmemHs s).1 hsHs).2 t
      ((hmemHs t).1 ht).1 ((hmemHs t).1 ht).2
    rw [← hust]
    exact hSinv u hu hux huH s hsS
  have hfull3 : (S ∩ B3).Nonempty → B3 ⊆ S := by
    rintro ⟨s, hsS, hsB⟩ t ht
    obtain ⟨h₀, hh₀, hh₀1, rfl⟩ := (hmem3 s).1 hsB
    obtain ⟨h₁, hh₁, hh₁1, rfl⟩ := (hmem3 t).1 ht
    obtain ⟨u, hu, hux, huH, hust⟩ := hU h₀ hh₀ hh₀1 h₁ hh₁ hh₁1
    have hux' : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 hux
    have : u * (x * h₀) * u⁻¹ = x * h₁ := by
      calc u * (x * h₀) * u⁻¹ = (u * x) * h₀ * u⁻¹ := by group
        _ = x * u * h₀ * u⁻¹ := by rw [hux']
        _ = x * (u * h₀ * u⁻¹) := by group
        _ = x * h₁ := by rw [hust]
    rw [← this]
    exact hSinv u hu hux huH _ hsS
  have hfull5 : (S ∩ B5).Nonempty → B5 ⊆ S := by
    rintro ⟨s, hsS, hsB⟩ t ht
    obtain ⟨h₀, hh₀, hh₀1, rfl⟩ := (hmem5 s).1 hsB
    obtain ⟨h₁, hh₁, hh₁1, rfl⟩ := (hmem5 t).1 ht
    obtain ⟨u, hu, hux, huH, hust⟩ := hU h₀ hh₀ hh₀1 h₁ hh₁ hh₁1
    have hux' : u * x⁻¹ = x⁻¹ * u := (show Commute u x from Subgroup.mem_centralizer_singleton_iff.1 hux).inv_right.eq
    have : u * (x⁻¹ * h₀) * u⁻¹ = x⁻¹ * h₁ := by
      calc u * (x⁻¹ * h₀) * u⁻¹ = (u * x⁻¹) * h₀ * u⁻¹ := by group
        _ = x⁻¹ * u * h₀ * u⁻¹ := by rw [hux']
        _ = x⁻¹ * (u * h₀ * u⁻¹) := by group
        _ = x⁻¹ * h₁ := by rw [hust]
    rw [← this]
    exact hSinv u hu hux huH _ hsS
  have hS := ncard_union_five h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 hcov
  rw [ncard_inter_block hHs80 hfull1, ncard_inter_singleton S x, ncard_inter_block hB3_80 hfull3,
    ncard_inter_singleton S x⁻¹, ncard_inter_block hB5_80 hfull5] at hS
  refine ⟨(if Hs ⊆ S then 1 else 0) + (if B3 ⊆ S then 1 else 0) + (if B5 ⊆ S then 1 else 0), ?_, ?_⟩
  · split_ifs <;> omega
  · rw [hS]
    split_ifs <;> omega

theorem ncard_conjOrbit (N : Subgroup G) (y : G) :
    (conjOrbit N y).ncard = (cx y).relIndex N := by
  classical
  letI : MulAction N G := MulAction.compHom G (MulAut.conj.comp N.subtype)
  have hsmul : ∀ (g : N) (z : G), g • z = (g : G) * z * (g : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit N y = conjOrbit N y := by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, (hsmul g y).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, hsmul _ y⟩
  have hstab : MulAction.stabilizer N y = (cx y).subgroupOf N := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (g : G) * y = (g : G) * y * (g : G)⁻¹ * g := by group
        _ = y * g := by rw [h]
    · intro h
      calc (g : G) * y * (g : G)⁻¹ = y * g * (g : G)⁻¹ := by rw [h]
        _ = y := by group
  rw [← horb, ← MulAction.index_stabilizer, hstab]
  rfl

theorem relIndex_mul_cent {A : Subgroup G} {y : G} (hy : y ∈ A) :
    (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G)) =
      (cx y).relIndex (Subgroup.normalizer (A : Set G)) *
        (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G) ⊓ cx y) := by
  have h1 : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) ⊓ cx y :=
    le_inf (Subgroup.centralizer_le_normalizer _)
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hy))
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 inf_le_left, mul_comm]
  congr 1
  rw [show Subgroup.normalizer (A : Set G) ⊓ cx y = cx y ⊓ Subgroup.normalizer (A : Set G) from
    inf_comm _ _]
  exact Subgroup.inf_relIndex_right _ _

theorem fusion_contra {A H : Subgroup G} {x a : G} (hA : IsElemAbelian 3 A) (hHA : H ≤ A)
    (hH : Nat.card H = 3 ^ 4) (hA5 : Nat.card A = 3 ^ 5) (hxA : x ∈ A) (hxH : x ∉ H)
    (hAHx : A ≤ H ⊔ Subgroup.zpowers x)
    (h3 : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ cx x → (∃ k : ℕ, g ^ (3 ^ k) = 1) →
      g ∈ Subgroup.centralizer (A : Set G))
    (hU : ∀ h ∈ H, h ≠ 1 → ∀ h' ∈ H, h' ≠ 1 → ∃ u ∈ Subgroup.normalizer (A : Set G),
      u ∈ cx x ∧ u ∈ Subgroup.normalizer (H : Set G) ∧ u * h * u⁻¹ = h')
    (hn : ∃ n ∈ Subgroup.normalizer (A : Set G), (∃ k : ℕ, n ^ (3 ^ k) = 1) ∧
      n ∉ Subgroup.centralizer (A : Set G))
    (ha : a ∈ A) (ha1 : a ≠ 1)
    (hax : ∀ g ∈ Subgroup.normalizer (A : Set G), g * x * g⁻¹ ≠ a ∧ g * x⁻¹ * g⁻¹ ≠ a)
    (h9 : ¬ 9 ∣ (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G) ⊓ cx a)) :
    False := by
  classical
  set N := Subgroup.normalizer (A : Set G) with hN
  have hOA : ∀ y ∈ A, conjOrbit N y ⊆ (A : Set G) := by
    rintro y hy z ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  have hO1 : ∀ y : G, y ≠ 1 → (1 : G) ∉ conjOrbit N y := by
    rintro y hy ⟨g, -, h⟩
    apply hy
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hOinv : ∀ y : G, ∀ u ∈ N, u ∈ cx x → u ∈ Subgroup.normalizer (H : Set G) →
      ∀ s ∈ conjOrbit N y, u * s * u⁻¹ ∈ conjOrbit N y := by
    rintro y u huN - - s ⟨g, hg, rfl⟩
    exact ⟨u * g, N.mul_mem huN hg, by group⟩
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxOx : x ∈ conjOrbit N x := ⟨1, N.one_mem, by group⟩
  obtain ⟨m, hm, hcx⟩ := card_inv_set hA hHA hH hxA hxH hAHx hU (conjOrbit N x) (hOA x hxA)
    (hO1 x hx1) (hOinv x)
  obtain ⟨n, hnN, hn3, hnA⟩ := hn
  have h3x := three_dvd_orbit h3 hnN hn3 hnA
  rw [if_pos hxOx] at hcx
  have h81x : 81 ∣ (conjOrbit N x).ncard := by
    rw [hcx] at h3x ⊢
    by_cases hxi : x⁻¹ ∈ conjOrbit N x
    · rw [if_pos hxi] at h3x ⊢
      interval_cases m <;> omega
    · rw [if_neg hxi] at h3x ⊢
      interval_cases m <;> omega
  have haOa : a ∈ conjOrbit N a := ⟨1, N.one_mem, by group⟩
  have hxOa : x ∉ conjOrbit N a := by
    rintro ⟨g, hg, h⟩
    apply (hax g⁻¹ (N.inv_mem hg)).1
    calc g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]; group
      _ = a := by group
  have hxiOa : x⁻¹ ∉ conjOrbit N a := by
    rintro ⟨g, hg, h⟩
    apply (hax g⁻¹ (N.inv_mem hg)).2
    calc g⁻¹ * x⁻¹ * g⁻¹⁻¹ = g⁻¹ * (g * a * g⁻¹) * g := by rw [h]; group
      _ = a := by group
  obtain ⟨m', hm', hca⟩ := card_inv_set hA hHA hH hxA hxH hAHx hU (conjOrbit N a) (hOA a ha)
    (hO1 a ha1) (hOinv a)
  rw [if_neg hxOa, if_neg hxiOa] at hca
  have hdisj : Disjoint (conjOrbit N x) (conjOrbit N a) := by
    rw [Set.disjoint_left]
    rintro z ⟨g, hg, rfl⟩ ⟨g', hg', h⟩
    apply (hax (g'⁻¹ * g) (N.mul_mem (N.inv_mem hg') hg)).1
    calc g'⁻¹ * g * x * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * x * g⁻¹) * g' := by group
      _ = g'⁻¹ * (g' * a * g'⁻¹) * g' := by rw [h]
      _ = a := by group
  have hsub : conjOrbit N x ∪ conjOrbit N a ⊆ (A : Set G) \ {1} := by
    rintro z (hz | hz)
    · exact ⟨hOA x hxA hz, fun h => hO1 x hx1 (Set.mem_singleton_iff.1 h ▸ hz)⟩
    · exact ⟨hOA a ha hz, fun h => hO1 a ha1 (Set.mem_singleton_iff.1 h ▸ hz)⟩
  have hcardA : ((A : Set G) \ {1}).ncard = 242 := by
    rw [Set.ncard_diff_singleton_of_mem A.one_mem, ← Nat.card_coe_set_eq]
    change Nat.card A - 1 = 242
    rw [hA5]
    norm_num
  have hle : (conjOrbit N x).ncard + (conjOrbit N a).ncard ≤ 242 := by
    rw [← Set.ncard_union_eq hdisj, ← hcardA]
    exact Set.ncard_le_ncard hsub
  have hpos : 0 < (conjOrbit N a).ncard := (Set.ncard_pos).2 ⟨a, haOa⟩
  have hm'2 : m' = 1 ∨ m' = 2 := by
    have h81pos : 81 ≤ (conjOrbit N x).ncard :=
      Nat.le_of_dvd ((Set.ncard_pos).2 ⟨x, hxOx⟩) h81x
    omega
  have hix := ncard_conjOrbit N x
  have hia := ncard_conjOrbit N a
  have hmx := relIndex_mul_cent (A := A) hxA
  have hma := relIndex_mul_cent (A := A) ha
  apply h9
  have h81 : 81 ∣ (conjOrbit N a).ncard *
      (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G) ⊓ cx a) := by
    rw [hia, ← hma, hmx, ← hix]
    exact Dvd.dvd.mul_right h81x _
  have h81' : 81 ∣
      (Subgroup.centralizer (A : Set G)).relIndex (Subgroup.normalizer (A : Set G) ⊓ cx a) := by
    rw [hca] at h81
    rcases hm'2 with h | h <;> rw [h] at h81
    · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h81)
    · exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h81)
  exact (show (9 : ℕ) ∣ 81 by norm_num).trans h81'

end S8.L84

end CFSG.LocalAnalysis.GLTheoremA
