module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Broad
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracK5
public import CFSG.Sporadic.Recognition.McLCentralizerCert
public import CFSG.Sporadic.Recognition.McLMultiplierCert
public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultLocal
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

namespace Sec6L51B

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {H J : Subgroup X} (hJH : J ≤ H) {c : ↥H}
    (hc : c ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    (c : X) ∈ normalizer (J : Set X) := by
  rw [mem_normalizer_iff] at hc ⊢
  intro x
  constructor
  · intro hx
    exact (hc ⟨x, hJH hx⟩).1 hx
  · intro hx
    have hxH : x ∈ H := by
      have h1 : (c : X) * x * (c : X)⁻¹ ∈ H := hJH hx
      have h2 : x = (c : X)⁻¹ * ((c : X) * x * (c : X)⁻¹) * (c : X) := by group
      rw [h2]
      exact H.mul_mem (H.mul_mem (H.inv_mem c.2) h1) c.2
    exact (hc ⟨x, hxH⟩).2 hx

theorem KProd_le_normalizer {H J : Subgroup X} (hJ : IsPCompIn 2 H J) :
    KProd ↥H ≤ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  refine sSup_le fun K hK => ?_
  by_cases heq : K = J.subgroupOf H
  · rw [heq]
    exact le_normalizer
  · exact ((distinct_p_components_core_commutation 2 Nat.prime_two _ _ hJ.2 hK.1).2
      (Ne.symm heq)).1

theorem KProdIn_le_normalizer {H J : Subgroup X} (hJ : IsPCompIn 2 H J) :
    KProdIn H ≤ normalizer (J : Set X) := by
  rintro _ ⟨k, hk, rfl⟩
  exact mem_normalizer_of_mem_normalizer_subgroupOf hJ.1 (KProd_le_normalizer hJ hk)

omit [Finite X] in
theorem KProdIn_subgroupOf (H : Subgroup X) : (KProdIn H).subgroupOf H = KProd ↥H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

omit [Finite X] in
theorem mem_normalizer_KProdIn {H : Subgroup X} {h : X} (hh : h ∈ H) :
    h ∈ normalizer (KProdIn H : Set X) := by
  have hKH : KProdIn H ≤ H := Subgroup.map_subtype_le _
  refine mem_normalizer_of_mem_normalizer_subgroupOf (c := ⟨h, hh⟩) hKH ?_
  rw [KProdIn_subgroupOf, mem_normalizer_iff]
  intro y
  have hN : (KProd ↥H).Normal := KProd.normal _
  constructor
  · intro hy
    exact hN.conj_mem y hy _
  · intro hy
    have e : y = (⟨h, hh⟩ : ↥H)⁻¹ * ((⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹) *
        (⟨h, hh⟩ : ↥H)⁻¹⁻¹ := by group
    rw [e]
    exact hN.conj_mem _ hy _

theorem isKComp_of_le_KProdIn {H J F : Subgroup X} (hJ : IsPCompIn 2 H J) (hFJ : F ≤ J)
    (hFK : F ≤ KProdIn H) (hF : IsTwoGenQuasi ↥F) : IsKComp (J.subgroupOf H) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  set J₀ : Subgroup ↥H := J.subgroupOf H with hJ₀
  set O₀ : Subgroup ↥H := pPrimeCoreOf 2 J₀ with hO₀
  have hle : KProd ↥H ≤ centralizerSection J₀ O₀ := by
    refine sSup_le fun K hK => ?_
    have hne : J₀ ≠ K := by
      intro h
      apply hnot
      rw [h]
      exact hK
    obtain ⟨hKN, -, hcomm, -⟩ :=
      (distinct_p_components_core_commutation 2 Nat.prime_two _ _ hJ.2 hK.1).2 hne
    intro c hc
    refine ⟨hKN hc, mem_normalizer_oddCoreOf_of_mem_normalizer (hKN hc), fun k hk => ?_⟩
    exact (hcomm (Subgroup.commutator_mem_commutator hk hc)).1
  have hFH : F ≤ H := hFJ.trans hJ.1
  have hF₀K : F.subgroupOf H ≤ KProd ↥H := by
    have h1 := Subgroup.subgroupOf_mono H hFK
    rwa [KProdIn_subgroupOf] at h1
  have hF₀J : F.subgroupOf H ≤ J₀ := Subgroup.subgroupOf_mono H hFJ
  have hcomm : ⁅F.subgroupOf H, F.subgroupOf H⁆ ≤ O₀ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (hle (hF₀K hb)).2.2 a (hF₀J ha)
  have hF₀q : IsTwoGenQuasi ↥(F.subgroupOf H) := (isTwoGenQuasi_subgroupOf_iff hFH).2 hF
  refine not_commutator_le_of_odd hF₀q ?_ hcomm
  have h1 : Nat.card O₀ = Nat.card (pPrimeCore 2 ↥J₀) :=
    Subgroup.card_map_of_injective J₀.subtype_injective
  rw [h1]
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

theorem exists_isPCompIn_of_le_KProdIn {H J' : Subgroup X} {u : X}
    (hJ'C : J' ≤ cen u ⊓ H) (hJ' : IsPComponent 2 (J'.subgroupOf (cen u ⊓ H))) (huJ' : u ∈ J')
    (hu2 : u ^ 2 = 1) (hJ'K : J' ≤ KProdIn H) :
    ∃ J : Subgroup X, IsPCompIn 2 H J ∧ J' ≤ J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ'H : J' ≤ H := hJ'C.trans inf_le_right
  have hJ'Cu : J' ≤ cen u := hJ'C.trans inf_le_left
  have huH : u ∈ H := hJ'H huJ'
  have hcen : centralizer ({(⟨u, huH⟩ : ↥H)} : Set ↥H) = (cen u).subgroupOf H :=
    centralizer_singleton_subgroup huH
  have hEC : J'.subgroupOf H ≤ centralizer ({(⟨u, huH⟩ : ↥H)} : Set ↥H) := by
    rw [hcen]
    exact Subgroup.subgroupOf_mono H hJ'Cu
  have hu₀2 : (⟨u, huH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using hu2)
  have hE : IsPComponent 2 ((J'.subgroupOf H).subgroupOf
      (centralizer ({(⟨u, huH⟩ : ↥H)} : Set ↥H))) := by
    rw [hcen]
    exact (isPComponent_subgroupOf_subgroupOf_iff hJ'Cu hJ'H).2 hJ'
  have hEL : J'.subgroupOf H ≤ pLayer ↥H 2 := by
    have h1 := Subgroup.subgroupOf_mono H hJ'K
    rw [KProdIn_subgroupOf] at h1
    exact h1.trans (sSup_le fun K hK => le_sSup (s := {L : Subgroup ↥H | IsPComponent 2 L}) hK.1)
  obtain ⟨M, hM, hEM⟩ := exists_isPComponent_le_of_mem_pLayer hEC huJ' hu₀2 hE hEL
  refine ⟨M.map H.subtype, ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · change IsPComponent 2 ((M.map H.subtype).comap H.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hM
  · have h1 := Subgroup.map_mono (f := H.subtype) hEM
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ'H] at h1

theorem exists_J' (h : SolMinCEx X) {H Lu E : Subgroup X} {u : X} (hH : H ≠ ⊤)
    (hu : orderOf u = 2) (hLu : IsAhatIntr X u Lu) (hEC : E ≤ cen u) (hEH : E ≤ H)
    (hcov : Lu ≤ E ⊔ oddCoreOf (cen u)) (huH : u ∈ H) :
    ∃ J' : Subgroup X, J' ≤ cen u ⊓ H ∧ IsPComponent 2 (J'.subgroupOf (cen u ⊓ H)) ∧
      J' ≤ E ⊔ (oddCoreOf (cen u) ⊓ H) ∧
      (∀ x ∈ Lu ⊓ H, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ J') ∧
      Nonempty (↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥Lu ⧸ pPrimeCore 2 ↥Lu) ∧ J' ≤ KProdIn H ∧
      u ∈ J' := by
  obtain ⟨hJC, huJ, hJpc, m, hm, hdc⟩ := hLu
  obtain ⟨J', hJ'CH, hJ'pc, hJ'E, hJ'two, ⟨q⟩⟩ := exists_isPComponent_inf_of_covered
    (C := cen u) (H := H) (O := oddCoreOf (cen u)) (E := E) (J := Lu) (oddCoreOf_le _)
    (le_normalizer_oddCoreOf _) (odd_card_oddCoreOf _) hEC hEH hJC hJpc hcov
  have hJ'C : J' ≤ cen u := hJ'CH.trans inf_le_left
  have hJ'H : J' ≤ H := hJ'CH.trans inf_le_right
  have hcen : centralizer ({(⟨u, huH⟩ : ↥H)} : Set ↥H) = (cen u).subgroupOf H :=
    centralizer_singleton_subgroup huH
  have hu2 : u ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hu]
    exact pow_orderOf_eq_one _
  have huJ' : u ∈ J' := hJ'two u (Subgroup.mem_inf.2 ⟨huJ, huH⟩) ⟨1, hu2⟩
  have hint : IsAhatIntr ↥H ⟨u, huH⟩ (J'.subgroupOf H) := by
    refine ⟨?_, huJ', ?_, m, hm, ?_⟩
    · rw [hcen]
      exact Subgroup.subgroupOf_mono H hJ'C
    · rw [hcen]
      exact (isPComponent_subgroupOf_subgroupOf_iff hJ'C hJ'H).2 hJ'pc
    · obtain ⟨q₀⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ'H)
      exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr (q₀.trans q).symm hdc
  have hu' : orderOf (⟨u, huH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hJ'K : J'.subgroupOf H ≤ KProd ↥H := h.ihSub hH ⟨u, huH⟩ hu' _ (Or.inl hint)
  have hJ'KI : J' ≤ KProdIn H := by
    have h2 := Subgroup.map_mono (f := H.subtype) hJ'K
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ'H] at h2
  exact ⟨J', hJ'CH, hJ'pc, hJ'E, hJ'two, ⟨q⟩, hJ'KI, huJ'⟩

theorem le_of_mem_of_center_eq_bot {L N : Subgroup X} (hLq : IsTwoGenQuasi ↥L)
    (hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) (hnorm : ∀ c ∈ L, c ∈ normalizer (N : Set X))
    {v : X} (hvL : v ∈ L) (hvN : v ∈ N) (hv : orderOf v = 2) : L ≤ N := by
  have hA : (N.subgroupOf L).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (mem_normalizer_iff.1 (hnorm g g.2) a).1 ha
  have htop : N.subgroupOf L = ⊤ :=
    eq_top_of_normal_of_involution hLq hZ (s := ⟨v, hvL⟩) hvN
      (by rw [Subgroup.orderOf_mk]; exact hv)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥L) ∈ N.subgroupOf L := htop ▸ Subgroup.mem_top _
  exact hx'

theorem exists_involution_of_isTwoGenQuasi {L : Subgroup X} (hq : IsTwoGenQuasi ↥L) :
    ∃ v ∈ L, orderOf v = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥L := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    obtain ⟨a, b, hab⟩ := hq.2.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hdvd : 2 ∣ Nat.card ↥L := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥L) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := primeResidual_eq_bot_of_coprime_card (G := ↥L) 2 hcop
    rw [hq.1] at h1
    exact top_ne_bot h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

omit [Finite X] in
theorem conj_mem_centralizerSection {K M : Subgroup X} {c x : X}
    (hcK : c ∈ normalizer (K : Set X)) (hcM : c ∈ normalizer (M : Set X))
    (hx : x ∈ centralizerSection K M) : c * x * c⁻¹ ∈ centralizerSection K M := by
  obtain ⟨hxK, hxM, hxc⟩ := hx
  refine ⟨mul_mem (mul_mem hcK hxK) (inv_mem hcK), mul_mem (mul_mem hcM hxM) (inv_mem hcM),
    fun k hk => ?_⟩
  have hk' : c⁻¹ * k * c⁻¹⁻¹ ∈ K := (mem_normalizer_iff.1 (inv_mem hcK) k).1 hk
  have h2 : c * ⁅c⁻¹ * k * c⁻¹⁻¹, x⁆ * c⁻¹ ∈ M := (mem_normalizer_iff.1 hcM _).1 (hxc _ hk')
  have h3 : ⁅k, c * x * c⁻¹⁆ = c * ⁅c⁻¹ * k * c⁻¹⁻¹, x⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h3]
  exact h2

omit [Finite X] in
theorem mem_normalizer_centralizerSection {K M : Subgroup X} {c : X}
    (hcK : c ∈ normalizer (K : Set X)) (hcM : c ∈ normalizer (M : Set X)) :
    c ∈ normalizer (centralizerSection K M : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_centralizerSection hcK hcM, fun hx => ?_⟩
  have h1 := conj_mem_centralizerSection (inv_mem hcK) (inv_mem hcM) hx
  have h2 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
  rwa [h2] at h1

theorem center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q] (hq : IsQuasisimple Q) :
    center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h]
    exact Subgroup.mem_top _

theorem pPrimeCore_eq_bot_of_isDoubleCoverOfAlt {K : Type} [Group K] [Finite K] {m : ℕ}
    (h : IsDoubleCoverOfAlt K m) : pPrimeCore 2 K = ⊥ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 K)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  rcases LocalCores.quasisimple_normal_subgroups h.1 (pPrimeCore_normal (p := 2) (G := K)) with
    htop | hcen
  · exfalso
    have h1 : Nat.card (center K) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
    rw [h.2.1] at h1
    have h2 : Nat.card (pPrimeCore 2 K) = Nat.card K := by rw [htop, Subgroup.card_top]
    rw [h2] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
  · have h1 : Nat.card (pPrimeCore 2 K) ∣ 2 := by
      have h0 := Subgroup.card_dvd_of_le hcen
      rwa [h.2.1] at h0
    have h2 : Nat.card (pPrimeCore 2 K) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
      · exact h3
      · rw [h3] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.eq_bot_of_card_eq _ h2

theorem isPGroup_center_of_pPrimeCore_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hO : pPrimeCore 2 Q = ⊥) : IsPGroup 2 ↥(center Q) := by
  intro z
  have hz0 : orderOf (z : Q) ≠ 0 := (orderOf_pos (z : Q)).ne'
  obtain ⟨a, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd hz0
  have hyc : (z : Q) ^ (2 ^ a) ∈ center Q := (center Q).pow_mem z.2 _
  have hyo : orderOf ((z : Q) ^ (2 ^ a)) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hdec]; exact dvd_mul_right _ _), hdec]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hN : (zpowers ((z : Q) ^ (2 ^ a))).Normal :=
    Subgroup.normal_of_le_center ((zpowers_le (G := Q)).2 hyc)
  have hbot : zpowers ((z : Q) ^ (2 ^ a)) = ⊥ := by
    refine (pPrimeCore_eq_bot_iff.1 hO) _ hN ?_
    rw [Nat.card_zpowers, hyo]
    exact Nat.coprime_two_left.2 hm
  have h1 : (z : Q) ^ (2 ^ a) = 1 := by
    have := Subgroup.mem_zpowers ((z : Q) ^ (2 ^ a))
    rwa [hbot, Subgroup.mem_bot] at this
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

theorem exists_conj_of_isConj {J : Subgroup X}
    (hconj : ∀ a b : ↥J ⧸ pPrimeCore 2 ↥J, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {s w : X} (hsJ : s ∈ J) (hwJ : w ∈ J) (hs : orderOf s = 2) (hw : orderOf w = 2) :
    ∃ g ∈ J, s = g * w * g⁻¹ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hord : ∀ x : ↥J, orderOf x = 2 →
      orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥J) x) = 2 := by
    intro x hx
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
    · intro h1
      have h2 : x ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff x).1 h1
      have h3 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥J) h2
      rw [hx] at h3
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h3)
  have hs₀ : orderOf (⟨s, hsJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have hw₀ : orderOf (⟨w, hwJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk]; exact hw
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj _ _ (hord _ hw₀) (hord _ hs₀))
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective c
  set y : ↥J := g₀ * ⟨w, hwJ⟩ * g₀⁻¹ with hy
  have hy2 : y ^ 2 = 1 := by
    rw [hy, conj_pow, ← hw₀, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hmem : (⟨s, hsJ⟩ : ↥J) ∈ Subgroup.zpowers y ⊔ pPrimeCore 2 ↥J := by
    have h1 : y⁻¹ * ⟨s, hsJ⟩ ∈ pPrimeCore 2 ↥J := by
      rw [← QuotientGroup.eq]
      simpa [hy] using hc
    have h2 : (⟨s, hsJ⟩ : ↥J) = y * (y⁻¹ * ⟨s, hsJ⟩) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers y) h1
  have hs2 : (⟨s, hsJ⟩ : ↥J) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hs₀]
    exact pow_orderOf_eq_one _
  obtain ⟨o, -, a, ha, -, hsa⟩ := exists_conj_twoElt_of_mem_sup_odd hOodd hmem hs2
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hy2' : y ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two]
    exact hy2
  have hk : y ^ k = 1 ∨ y ^ k = y := by
    rw [zpow_eq_zpow_emod k hy2']
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  rcases hk with hk | hk
  · exfalso
    rw [hk, mul_one, mul_inv_cancel] at hsa
    have h1 : orderOf (⟨s, hsJ⟩ : ↥J) = 1 := by rw [hsa, orderOf_one]
    rw [hs₀] at h1
    exact absurd h1 (by norm_num)
  · refine ⟨((o * g₀ : ↥J) : X), (o * g₀).2, ?_⟩
    rw [hk, hy] at hsa
    have h1 := congrArg Subtype.val hsa
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h1, Subgroup.coe_mul, mul_inv_rev]
    group

theorem sec6MComp_of_conj {n : ℕ} {H J Jw : Subgroup X} {w : X} (hJ : IsPCompIn 2 H J)
    (hty : IsSec6MType n (↥J ⧸ pPrimeCore 2 ↥J))
    (hconj : ∀ a b : ↥J ⧸ pPrimeCore 2 ↥J, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hwJ : w ∈ J) (hw : orderOf w = 2) (hJw : IsAhatIntr X w Jw)
    (hcov : Jw ≤ (J ⊓ cen w) ⊔ oddCoreOf (cen w)) : Sec6MComp X n H J := by
  refine ⟨⟨hJ, ?_, fun s hs hs2 => ?_⟩, hty⟩
  · rcases hty with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · obtain ⟨g, hg, rfl⟩ := exists_conj_of_isConj hconj hs hwJ hs2 hw
    refine ⟨Jw.map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
    · have h1 := IsAhatIntr.map_mulEquiv (MulAut.conj g) hJw
      rwa [MulAut.conj_apply] at h1
    · have hJφ : J.map (MulAut.conj g).toMonoidHom = J :=
        map_conj_eq_of_mem_normalizer (le_normalizer hg)
      have hCφ : (cen w).map (MulAut.conj g).toMonoidHom = cen (g * w * g⁻¹) := by
        rw [← MulAut.conj_apply]
        exact (centralizer_singleton_map_mulEquiv (MulAut.conj g) w).symm
      have hOφ : (oddCoreOf (cen w)).map (MulAut.conj g).toMonoidHom =
          oddCoreOf (cen (g * w * g⁻¹)) := by
        rw [← hCφ]
        exact (pPrimeCoreOf_map_mulEquiv (MulAut.conj g) (cen w)).symm
      calc Jw.map (MulAut.conj g).toMonoidHom
          ≤ ((J ⊓ cen w) ⊔ oddCoreOf (cen w)).map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono hcov
        _ = (J ⊓ cen (g * w * g⁻¹)) ⊔ oddCoreOf (cen (g * w * g⁻¹)) := by
            rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hJφ, hCφ,
              hOφ]

theorem isDoubleCoverOfAlt_of_isPComponent_cen {J F : Subgroup X} {w : X} (hwJ : w ∈ J)
    (hw : orderOf w = 2) (hFJ : F ≤ J ⊓ cen w) (hF : IsPComponent 2 (F.subgroupOf (J ⊓ cen w)))
    {m : ℕ} (hC : ∀ c : ↥J ⧸ pPrimeCore 2 ↥J, orderOf c = 2 →
      IsDoubleCoverOfAlt ↥(centralizer ({c} : Set (↥J ⧸ pPrimeCore 2 ↥J))) m) :
    IsDoubleCoverOfAlt (↥F ⧸ pPrimeCore 2 ↥F) m := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hw₀2 : (⟨w, hwJ⟩ : ↥J) * ⟨w, hwJ⟩ = 1 := by
    apply Subtype.ext
    show w * w = 1
    rw [← pow_two, ← hw]
    exact pow_orderOf_eq_one w
  have hc2 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥J) (⟨w, hwJ⟩ : ↥J)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, hw₀2, map_one]
    · intro h1
      have h2 : (⟨w, hwJ⟩ : ↥J) ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff _).1 h1
      have h3 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 ↥J) h2
      rw [Subgroup.orderOf_mk, hw] at h3
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h3)
  set q : ↥J →* ↥J ⧸ pPrimeCore 2 ↥J := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hq
  set C : Subgroup (↥J ⧸ pPrimeCore 2 ↥J) :=
    centralizer ({q ⟨w, hwJ⟩} : Set (↥J ⧸ pPrimeCore 2 ↥J)) with hCdef
  have hdc : IsDoubleCoverOfAlt ↥C m := hC _ hc2
  have hFc : F ≤ cen w := hFJ.trans inf_le_right
  have hFJ' : F ≤ J := hFJ.trans inf_le_left
  have hF₁X : F.subgroupOf J ≤ (cen w).subgroupOf J := Subgroup.subgroupOf_mono J hFc
  have hF₁comp : IsPComponent 2 ((F.subgroupOf J).subgroupOf ((cen w).subgroupOf J)) := by
    have h1 : IsPComponent 2 (F.subgroupOf (cen w ⊓ J)) := by rwa [inf_comm] at hF
    exact (isPComponent_subgroupOf_subgroupOf_iff hFc hFJ').2 h1
  have hker : ¬ 2 ∣ Nat.card q.ker := by
    rw [hq, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
  have hXq : ((cen w).subgroupOf J).map q = C := by
    have hT : IsPGroup 2 ↥(Subgroup.zpowers (⟨w, hwJ⟩ : ↥J)) := isPGroup_zpowers_of_mul_self hw₀2
    have : Fact (IsPGroup 2 ↥(Subgroup.zpowers (⟨w, hwJ⟩ : ↥J))) := ⟨hT⟩
    have h := centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers (⟨w, hwJ⟩ : ↥J))
      (pPrimeCore 2 ↥J) pPrimeCore_normal pPrimeCore_coprime_card
    simp only at h
    rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton] at h
    simp only [Subgroup.centralizer_closure] at h
    rw [← centralizer_singleton_subgroup hwJ]
    exact h.symm
  have hFh : IsPComponent 2 (((F.subgroupOf J).map q).subgroupOf C) := by
    have := ComponentClassification.GSThmB.OddQuot.isPComponent_map q hker hF₁X hF₁comp
    rwa [hXq] at this
  have hFhC : (F.subgroupOf J).map q ≤ C := hXq ▸ Subgroup.map_mono hF₁X
  have hFheq : (F.subgroupOf J).map q = C := by
    have hsub := (isPComponent_two_iff.1 hFh).1
    have hq' : IsTwoGenQuasi ↥(((F.subgroupOf J).map q).subgroupOf C) :=
      (isPComponent_two_iff.1 hFh).2
    have hcomp : IsComponent (⊤ : Subgroup ↥C) :=
      ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hdc.1,
        Subgroup.IsSubnormal.top⟩
    rcases LocalCores.component_subnormal_subgroup hcomp hsub with h | h
    · refine le_antisymm hFhC fun x hx => ?_
      exact h (Subgroup.mem_top (⟨x, hx⟩ : ↥C))
    · exfalso
      refine not_commutator_le_of_odd hq' (R := ⊥) (by simp) ?_
      rw [← h]
      exact Subgroup.commutator_mono le_top le_rfl
  obtain ⟨e₁⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hFJ')
  obtain ⟨e₂⟩ :=
    ComponentClassification.GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv q hker
      (F.subgroupOf J)
  obtain ⟨e₃⟩ := nonempty_quotPPrimeCore_equiv (MulEquiv.subgroupCongr hFheq)
  have hOC : pPrimeCore 2 ↥C = ⊥ := pPrimeCore_eq_bot_of_isDoubleCoverOfAlt hdc
  let e₄ : ↥C ⧸ pPrimeCore 2 ↥C ≃* ↥C :=
    (QuotientGroup.quotientMulEquivOfEq hOC).trans QuotientGroup.quotientBot
  exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr
    (e₁.symm.trans (e₂.trans (e₃.trans e₄))).symm hdc

theorem isDoubleCoverOfAlt_unique {K : Type} [Group K] [Finite K] {n m : ℕ}
    (h : IsDoubleCoverOfAlt K n) (h' : IsDoubleCoverOfAlt K m) (hn : 8 ≤ n) (hm : 8 ≤ m) :
    n = m := by
  have hcard : ∀ {k : ℕ}, 2 ≤ k → IsDoubleCoverOfAlt K k → Nat.card K = k.factorial := by
    intro k hk hk'
    obtain ⟨-, hc, ⟨e⟩⟩ := hk'
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
    rw [Nat.card_congr e.toEquiv, hc] at h1
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
    rw [h1, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    exact Nat.div_mul_cancel (Nat.dvd_factorial (by norm_num) hk)
  have h1 := hcard (by omega) h
  have h2 := hcard (by omega) h'
  have h3 : n.factorial = m.factorial := h1.symm.trans h2
  exact (Nat.factorial_inj (by
    have := Nat.self_le_factorial n
    omega)).1 h3

theorem exists_not_comm_alt8 : ∃ a b : alternatingGroup (Fin 8), a * b ≠ b * a := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  refine GH74.GLS.Stage2.Bender.Thm1.LyMult.exists_noncomm_of_simple ?_
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem isDoubleCoverOfAlt_centralizer_McL
    {Q : Type} [Group Q] (e : Q ≃* Blueprint.NativeSporadic.McL) (c : Q) (hc : orderOf c = 2) :
    IsDoubleCoverOfAlt ↥(centralizer ({c} : Set Q)) 8 := by
  obtain ⟨hperf, hcen, ⟨f⟩⟩ :=
    Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ hc
  let f' : ↥(centralizer ({c} : Set Q)) ⧸ center ↥(centralizer ({c} : Set Q)) ≃*
      alternatingGroup (Fin 8) := (QuotientGroup.quotientMulEquivOfEq hcen).trans f
  have hs : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨⟨hperf, f'.isSimpleGroup, ?_⟩, ?_, ⟨f'⟩⟩
  · obtain ⟨a, b, hab⟩ := exists_not_comm_alt8
    refine ⟨f'.symm a, f'.symm b, fun h => hab ?_⟩
    have h1 := congrArg f' h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  · rw [hcen, Nat.card_zpowers, Subgroup.orderOf_mk, hc]

theorem isDoubleCoverOfAlt_centralizer_Ly
    {Q : Type} [Group Q] (e : Q ≃* Blueprint.NativeSporadic.Ly) (c : Q) (hc : orderOf c = 2) :
    IsDoubleCoverOfAlt ↥(centralizer ({c} : Set Q)) 11 :=
  Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ c hc

theorem isConj_of_mulEquiv {Q S : Type} [Group Q] [Group S] (e : Q ≃* S)
    (h : ∀ a b : S, orderOf a = 2 → orderOf b = 2 → IsConj a b) (a b : Q) (ha : orderOf a = 2)
    (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (h (e a) (e b) (by rw [MulEquiv.orderOf_eq]; exact ha)
    (by rw [MulEquiv.orderOf_eq]; exact hb))
  refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
  simp [hc]

theorem isConj_of_equiv_McL
    {Q : Type} [Group Q] (e : Q ≃* Blueprint.NativeSporadic.McL) (a b : Q) (ha : orderOf a = 2)
    (hb : orderOf b = 2) : IsConj a b := by
  have hS : ∀ a b : Blueprint.NativeSporadic.McL, orderOf a = 2 → orderOf b = 2 → IsConj a b :=
    fun a b ha hb => Sporadic.Recognition.McLAS.mcl_involutions_conj a b ha hb
  exact @isConj_of_mulEquiv Q Blueprint.NativeSporadic.McL _ Units.instGroup e hS a b ha hb

theorem isConj_of_equiv_Ly
    {Q : Type} [Group Q] (e : Q ≃* Blueprint.NativeSporadic.Ly)
    (a b : Q) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  have hS : ∀ a b : Blueprint.NativeSporadic.Ly, orderOf a = 2 → orderOf b = 2 → IsConj a b :=
    fun a b ha hb => Sporadic.Recognition.LyonsSims.ly_isConj_of_involutions ha hb
  exact @isConj_of_mulEquiv Q Blueprint.NativeSporadic.Ly _ Units.instGroup e hS a b ha hb

theorem nonempty_equiv_McL_of_center
    {Q : Type} [Group Q] [Finite Q] (hO : pPrimeCore 2 Q = ⊥) (hq : IsQuasisimple Q)
    (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.McL) :
    Nonempty (Q ≃* Blueprint.NativeSporadic.McL) := by
  have hdvd := Sporadic.Recognition.McLMultiplier.card_center_dvd_three_of_certificate hq.1 e
  have hcen : center Q = ⊥ := by
    refine (pPrimeCore_eq_bot_iff.1 hO) (center Q) inferInstance ?_
    exact Nat.Coprime.coprime_dvd_right hdvd (by norm_num)
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcen.symm)).trans e⟩

theorem nonempty_equiv_Ly_of_center
    {Q : Type} [Group Q] [Finite Q] (hO : pPrimeCore 2 Q = ⊥)
    (hq : IsQuasisimple Q) (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.Ly) :
    Nonempty (Q ≃* Blueprint.NativeSporadic.Ly) := by
  have hker := GH74.GLS.Stage2.Bender.Thm1.LyMult.lyMult_two ⟨e⟩
    (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _) hq.1
    (QuotientGroup.ker_mk' _).le
    (by rw [QuotientGroup.ker_mk']; exact isPGroup_center_of_pPrimeCore_eq_bot hO)
  rw [QuotientGroup.ker_mk'] at hker
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker.symm)).trans e⟩

theorem center_eq_bot_of_McL_or_Ly
    {Q : Type} [Group Q] (hq : IsQuasisimple Q)
    (h : Nonempty (Q ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (Q ≃* Blueprint.NativeSporadic.Ly)) : center Q = ⊥ := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact @center_eq_bot_of_simple Q _
      (@MulEquiv.isSimpleGroup _ _ _ _ Sporadic.McL.isSimpleGroup_McL e) hq
  · obtain ⟨e⟩ := h
    exact @center_eq_bot_of_simple Q _
      (@MulEquiv.isSimpleGroup _ _ _ _ Sporadic.Ly.fam_ly_simplicity.2.2 e) hq

theorem sec5Comp_of_isDoubleCoverOfAlt {n m : ℕ} {H J J' Lu E : Subgroup X} {u : X}
    (hu : orderOf u = 2) (hJ : IsPCompIn 2 H J)
    (hdc : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) m)
    (hJ'CH : J' ≤ cen u ⊓ H) (hJ'pc : IsPComponent 2 (J'.subgroupOf (cen u ⊓ H)))
    (hJ'J : J' ≤ J) (huJ' : u ∈ J') (hJ'n : IsDoubleCoverOfAlt (↥J' ⧸ pPrimeCore 2 ↥J') n)
    (hLu : IsAhatIntr X u Lu) (hJ'Lu : J' ≤ Lu) (hEJ' : E ≤ J') (hEJC : E ≤ J ⊓ cen u)
    (hEq : IsTwoGenQuasi ↥E) (hLuEq : Lu = pPrimeCoreOf 2 Lu ⊔ E) : Sec5Comp X n H J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ'C : J' ≤ cen u := hJ'CH.trans inf_le_left
  have hJ'JC : J' ≤ J ⊓ cen u := le_inf hJ'J hJ'C
  have hJCH : J ⊓ cen u ≤ cen u ⊓ H := le_inf inf_le_right (inf_le_left.trans hJ.1)
  have hJ'pcJ : IsPComponent 2 (J'.subgroupOf (J ⊓ cen u)) :=
    isPComponent_subgroupOf_mono hJ'JC hJCH hJ'pc
  have huu : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have htc : u ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
    mem_centralizerSection_of_piece hdc (hJ'J huJ') huu hJ'JC hJ'pcJ huJ'
  have hJq : IsTwoGenQuasi ↥J :=
    (isTwoGenQuasi_subgroupOf_iff hJ.1).1 (isPComponent_two_iff.1 hJ.2).2
  set P : Subgroup X := oTwoPrimeOf (J ⊓ cen u) with hP
  have hPcov : P.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ :=
    oTwoPrimeOf_inf_centralizer_covers hu2 hJq.1 htc
  have hPJC : P ≤ J ⊓ cen u := oTwoPrimeOf_le _
  have hPJ : P ≤ J := hPJC.trans inf_le_left
  have hPq : IsTwoGenQuasi ↥P :=
    isTwoGenQuasi_of_covers hPJ hPcov (primeResidual_oTwoPrimeOf _) hJq
  have hPCH : P ≤ cen u ⊓ H := hPJC.trans hJCH
  have hPsub : (P.subgroupOf (cen u ⊓ H)).IsSubnormal := by
    have hA : ((J ⊓ cen u).subgroupOf (cen u ⊓ H)).IsSubnormal := by
      have h1 : (J ⊓ cen u).subgroupOf (cen u ⊓ H) =
          (J.subgroupOf H).comap (Subgroup.inclusion (inf_le_right : cen u ⊓ H ≤ H)) := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf,
          Subgroup.coe_inclusion]
        exact ⟨fun h => h.1, fun h => ⟨h, x.2.1⟩⟩
      rw [h1]
      exact (isPComponent_two_iff.1 hJ.2).1.comap _
    exact isSubnormal_subgroupOf_of_normal_of_subnormal hJCH hPJC hA
      (normal_subgroupOf_oTwoPrimeOf _)
  have hPpc : IsPCompIn 2 (cen u ⊓ H) P :=
    ⟨hPCH, isPComponent_two_iff.2 ⟨hPsub, (isTwoGenQuasi_subgroupOf_iff hPCH).2 hPq⟩⟩
  have hEP : E ≤ P := by
    have h1 := oTwoPrimeOf_mono hEJC
    rwa [oTwoPrimeOf_eq_self_of_primeResidual hEq.1] at h1
  have hJ'P : J' = P := eq_of_isPCompIn_of_le ⟨hJ'CH, hJ'pc⟩ hPpc hEJ' hEP hEq
  have hJ'cov : J'.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
    rw [hJ'P]
    exact hPcov
  have hJn : IsDoubleCoverOfAlt (↥J ⧸ pPrimeCore 2 ↥J) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hJ'J hJ'cov n).1 hJ'n
  refine ⟨⟨u, hu, hJ'J huJ', hJ, ?_, Lu, hLu, ?_⟩, hJn⟩
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    have h1 := (covers_subgroupOf_iff hPJ).1 hPcov
    rw [sup_comm] at h1
    exact h1.symm
  · rw [oPrimeResidualOf_two_eq_oTwoPrimeOf]
    have hPLu : P ≤ Lu := hJ'P ▸ hJ'Lu
    refine le_antisymm ?_ (sup_le (Subgroup.map_subtype_le _) hPLu)
    calc Lu = pPrimeCoreOf 2 Lu ⊔ E := hLuEq
      _ ≤ pPrimeCoreOf 2 Lu ⊔ P := sup_le_sup_left hEP _

theorem exists_sec6KComp_of_sec5Comp
    (h : SolMinCEx X) {n : ℕ} (hn8 : 8 ≤ n)
    {H H' L : Subgroup X} (hH : H ≠ ⊤) (hH'H : H' ≤ H) (hL : Sec5Comp X n H' L) :
    ∃ J : Subgroup X, Sec6KComp X n H J ∧ L ≤ J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨u, hLi⟩, hLn⟩ := hL
  have hLK : L ≤ KProdIn H := h.le_KProdIn_of_isIntrinsicIn hH hH'H hLi
  obtain ⟨hu, huL, ⟨hLH', hLpc⟩, hLeq, Lu, hLu, hLuEq⟩ := hLi
  rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at hLeq hLuEq
  set E : Subgroup X := oTwoPrimeOf (L ⊓ cen u) with hE
  have hLH : L ≤ H := hLH'.trans hH'H
  have hEL : E ≤ L := (oTwoPrimeOf_le _).trans inf_le_left
  have hEC : E ≤ cen u := (oTwoPrimeOf_le _).trans inf_le_right
  have hEH : E ≤ H := hEL.trans hLH
  have hELu : E ≤ Lu := by
    rw [hLuEq]
    exact le_sup_right
  have hOLu : pPrimeCoreOf 2 Lu ≤ oddCoreOf (cen u) :=
    pPrimeCoreOf_le_oddCoreOf hLu.1 (isPComponent_two_iff.1 hLu.2.2.1).1
  have hcov : Lu ≤ E ⊔ oddCoreOf (cen u) :=
    calc Lu = pPrimeCoreOf 2 Lu ⊔ E := hLuEq
      _ ≤ oddCoreOf (cen u) ⊔ E := sup_le_sup_right hOLu E
      _ = E ⊔ oddCoreOf (cen u) := sup_comm _ _
  have huH : u ∈ H := hLH huL
  have hu2 : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLH').1 (isPComponent_two_iff.1 hLpc).2
  have hcovL : E.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
    rw [covers_subgroupOf_iff hEL, sup_comm]
    exact hLeq.symm
  have hcovLu : E.subgroupOf Lu ⊔ pPrimeCore 2 ↥Lu = ⊤ := by
    rw [covers_subgroupOf_iff hELu, sup_comm]
    exact hLuEq.symm
  have hEq : IsTwoGenQuasi ↥E :=
    isTwoGenQuasi_of_covers hEL hcovL (primeResidual_oTwoPrimeOf _) hLq
  have hLun : IsDoubleCoverOfAlt (↥Lu ⧸ pPrimeCore 2 ↥Lu) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hELu hcovLu n).1
      ((isDoubleCoverOfAlt_quot_iff_of_covers hEL hcovL n).2 hLn)
  obtain ⟨J', hJ'CH, hJ'pc, hJ'E, hJ'two, ⟨qJ'⟩, hJ'K, huJ'⟩ :=
    exists_J' h hH hu hLu hEC hEH hcov huH
  have hJ'C : J' ≤ cen u := hJ'CH.trans inf_le_left
  have hJ'q : IsTwoGenQuasi ↥J' :=
    (isTwoGenQuasi_subgroupOf_iff hJ'CH).1 (isPComponent_two_iff.1 hJ'pc).2
  have hJ'n : IsDoubleCoverOfAlt (↥J' ⧸ pPrimeCore 2 ↥J') n :=
    isDoubleCoverOfAlt_congr' qJ'.symm hLun
  have hEJ' : E ≤ J' := by
    rw [hE, oTwoPrimeOf_le_iff]
    intro x hx h2
    have hxE : x ∈ E := mem_oTwoPrimeOf_of_twoElt hx h2
    exact hJ'two x ⟨hELu hxE, hEH hxE⟩ h2
  have hJ'Lu : J' ≤ Lu := by
    have hJ'sup : J' ≤ Lu ⊔ oddCoreOf (cen u) :=
      hJ'E.trans (sup_le (hELu.trans le_sup_left) (inf_le_left.trans le_sup_right))
    have hLuC : Lu ≤ cen u := hLu.1
    have h1 : J'.subgroupOf (cen u) ≤ Lu.subgroupOf (cen u) ⊔ pPrimeCore 2 ↥(cen u) := by
      have h2 := Subgroup.subgroupOf_mono (cen u) hJ'sup
      rwa [Subgroup.subgroupOf_sup hLuC (oddCoreOf_le _), oddCoreOf_subgroupOf] at h2
    have hgen : primeResidual 2 ↥(J'.subgroupOf (cen u)) = ⊤ :=
      ((isTwoGenQuasi_subgroupOf_iff hJ'C).2 hJ'q).1
    have h3 := le_of_le_sup_pPrimeCore hLu.2.2.1 hgen h1
    have h4 := Subgroup.map_mono (f := (cen u).subtype) h3
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ'C, Subgroup.map_subgroupOf_eq_of_le hLuC] at h4
  obtain ⟨J, hJ, hJ'J⟩ := exists_isPCompIn_of_le_KProdIn hJ'CH hJ'pc huJ' hu2 hJ'K
  have hLJ : L ≤ J := le_of_covers_of_normalized hEL hcovL hLq.1 (hEJ'.trans hJ'J)
    fun c hc => KProdIn_le_normalizer hJ (hLK hc)
  have hJK : IsKType (↥J ⧸ pPrimeCore 2 ↥J) := by
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ.1)
    exact IsKType.congr f (isKComp_of_le_KProdIn hJ hJ'J hJ'K hJ'q).2
  have hEJC : E ≤ J ⊓ cen u := le_inf (hEL.trans hLJ) hEC
  have hJ'JC : J' ≤ J ⊓ cen u := le_inf hJ'J hJ'C
  have hJ'pcJ : IsPComponent 2 (J'.subgroupOf (J ⊓ cen u)) :=
    isPComponent_subgroupOf_mono hJ'JC (le_inf inf_le_right (inf_le_left.trans hJ.1)) hJ'pc
  have huJ : u ∈ J := hJ'J huJ'
  have hLucov : Lu ≤ (J ⊓ cen u) ⊔ oddCoreOf (cen u) :=
    calc Lu = pPrimeCoreOf 2 Lu ⊔ E := hLuEq
      _ ≤ oddCoreOf (cen u) ⊔ (J ⊓ cen u) := sup_le_sup hOLu hEJC
      _ = (J ⊓ cen u) ⊔ oddCoreOf (cen u) := sup_comm _ _
  have hO : pPrimeCore 2 (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  rcases hJK.2 with ⟨m, -, hdc⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨J, Or.inl (sec5Comp_of_isDoubleCoverOfAlt hu hJ hdc hJ'CH hJ'pc hJ'J huJ' hJ'n hLu
      hJ'Lu hEJ' hEJC hEq hLuEq), hLJ⟩
  · obtain ⟨e'⟩ := nonempty_equiv_McL_of_center hO hJK.1 e
    have h8 := isDoubleCoverOfAlt_of_isPComponent_cen huJ hu hJ'JC hJ'pcJ
      (isDoubleCoverOfAlt_centralizer_McL e')
    have hn8' : n = 8 := isDoubleCoverOfAlt_unique hJ'n h8 hn8 le_rfl
    exact ⟨J, Or.inr (sec6MComp_of_conj hJ (Or.inl ⟨hn8', ⟨e'⟩⟩)
      (isConj_of_equiv_McL e') huJ hu hLu hLucov), hLJ⟩
  · obtain ⟨e'⟩ := nonempty_equiv_Ly_of_center hO hJK.1 e
    have h11 := isDoubleCoverOfAlt_of_isPComponent_cen huJ hu hJ'JC hJ'pcJ
      (isDoubleCoverOfAlt_centralizer_Ly e')
    have hn11 : n = 11 := isDoubleCoverOfAlt_unique hJ'n h11 hn8 (by norm_num)
    exact ⟨J, Or.inr (sec6MComp_of_conj hJ (Or.inr ⟨hn11, ⟨e'⟩⟩)
      (isConj_of_equiv_Ly e') huJ hu hLu hLucov), hLJ⟩

theorem exists_sec6MComp_of_sec6MComp
    (h : SolMinCEx X) {n : ℕ}
    (hn : IsMaxAhatDeg X n) {H H' L : Subgroup X} (hH : H ≠ ⊤) (hH'H : H' ≤ H)
    (hL : Sec6MComp X n H' L) : ∃ J : Subgroup X, Sec6MComp X n H J ∧ L ≤ J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLi, hLty⟩ := hL
  have hLH' : L ≤ H' := hLi.1.1
  have hLH : L ≤ H := hLH'.trans hH'H
  have hLq : IsTwoGenQuasi ↥L :=
    (isTwoGenQuasi_subgroupOf_iff hLH').1 (isPComponent_two_iff.1 hLi.1.2).2
  have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := center_eq_bot_of_McL_or_Ly hLq.2 hLi.2.1
  obtain ⟨v, hvL, hv⟩ := exists_involution_of_isTwoGenQuasi hLq
  have hv2 : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hvv : v * v = 1 := by rw [← pow_two]; exact hv2
  obtain ⟨Jv, hJv, hJvcov⟩ := hLi.2.2 v hvL hv
  obtain ⟨J', hJ'CH, hJ'pc, -, -, ⟨qJ'⟩, hJ'K, hvJ'⟩ :=
    exists_J' h hH hv hJv inf_le_right (inf_le_left.trans hLH) hJvcov (hLH hvL)
  have hLK : L ≤ KProdIn H := le_of_mem_of_center_eq_bot hLq hZ
    (fun c hc => mem_normalizer_KProdIn (hLH hc)) hvL (hJ'K hvJ') hv
  obtain ⟨J, hJ, hJ'J⟩ := exists_isPCompIn_of_le_KProdIn hJ'CH hJ'pc hvJ' hv2 hJ'K
  have hLJ : L ≤ J := le_of_mem_of_center_eq_bot hLq hZ
    (fun c hc => KProdIn_le_normalizer hJ (hLK hc)) hvL (hJ'J hvJ') hv
  have hJ'C : J' ≤ cen v := hJ'CH.trans inf_le_left
  have hJ'q : IsTwoGenQuasi ↥J' :=
    (isTwoGenQuasi_subgroupOf_iff hJ'CH).1 (isPComponent_two_iff.1 hJ'pc).2
  have hJK : IsKType (↥J ⧸ pPrimeCore 2 ↥J) := by
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ.1)
    exact IsKType.congr f (isKComp_of_le_KProdIn hJ hJ'J hJ'K hJ'q).2
  have hJ'JC : J' ≤ J ⊓ cen v := le_inf hJ'J hJ'C
  have hJ'pcJ : IsPComponent 2 (J'.subgroupOf (J ⊓ cen v)) :=
    isPComponent_subgroupOf_mono hJ'JC (le_inf inf_le_right (inf_le_left.trans hJ.1)) hJ'pc
  have hvJ : v ∈ J := hLJ hvL
  have hJvcovJ : Jv ≤ (J ⊓ cen v) ⊔ oddCoreOf (cen v) :=
    hJvcov.trans (sup_le_sup_right (inf_le_inf_right _ hLJ) _)
  have hO : pPrimeCore 2 (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  rcases hJK.2 with ⟨m, -, hdc⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exfalso
    have htc : v ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
      mem_centralizerSection_of_piece hdc hvJ hvv hJ'JC hJ'pcJ hvJ'
    have hLc : L ≤ centralizerSection J (pPrimeCoreOf 2 J) := le_of_mem_of_center_eq_bot hLq hZ
      (fun c hc => mem_normalizer_centralizerSection (le_normalizer (hLJ hc))
        (mem_normalizer_oddCoreOf_of_mem_normalizer (le_normalizer (hLJ hc)))) hvL htc hv
    have hcomm : ⁅L, L⁆ ≤ pPrimeCoreOf 2 J := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (hLc hb).2.2 a (hLJ ha)
    exact not_commutator_le_of_odd hLq (odd_card_oddCoreOf J) hcomm
  · obtain ⟨e'⟩ := nonempty_equiv_McL_of_center hO hJK.1 e
    rcases hLty with ⟨h8, -⟩ | ⟨-, ⟨eL⟩⟩
    · exact ⟨J, sec6MComp_of_conj hJ (Or.inl ⟨h8, ⟨e'⟩⟩)
        (isConj_of_equiv_McL e') hvJ hv hJv hJvcovJ, hLJ⟩
    · exfalso
      have hcovL : L.subgroupOf L ⊔ pPrimeCore 2 ↥L = ⊤ := by
        rw [Subgroup.subgroupOf_self, top_sup_eq]
      have hle := card_quot_pPrimeCore_le_of_covers (le_refl L) hLJ hcovL
      rw [Nat.card_congr eL.toEquiv, Nat.card_congr e'.toEquiv, Sporadic.Ly.card_Ly,
        Sporadic.McL.card_McL] at hle
      norm_num at hle
  · obtain ⟨e'⟩ := nonempty_equiv_Ly_of_center hO hJK.1 e
    rcases hLty with ⟨h8, -⟩ | ⟨h11, -⟩
    · exfalso
      have h11' := isDoubleCoverOfAlt_of_isPComponent_cen hvJ hv hJ'JC hJ'pcJ
        (isDoubleCoverOfAlt_centralizer_Ly e')
      have hJv11 : IsDoubleCoverOfAlt (↥Jv ⧸ pPrimeCore 2 ↥Jv) 11 :=
        isDoubleCoverOfAlt_congr' qJ' h11'
      have h1 := hn.2.2 11 v Jv (by norm_num) hv hJv hJv11
      omega
    · exact ⟨J, sec6MComp_of_conj hJ (Or.inr ⟨h11, ⟨e'⟩⟩)
        (isConj_of_equiv_Ly e') hvJ hv hJv hJvcovJ, hLJ⟩

theorem sec6K_le_of_le
    (h : SolMinCEx X) {n : ℕ} (hn : IsMaxAhatDeg X n)
    {H H' : Subgroup X} (hH : H ≠ ⊤) (hH'H : H' ≤ H) :
    Sec6K X n H' ≤ Sec6K X n H ∧ Sec6M X n H' ≤ Sec6M X n H := by
  unfold Sec6K Sec6M
  refine ⟨sSup_le fun L hL => ?_, sSup_le fun L hL => ?_⟩
  · rcases hL with hL | hL
    · obtain ⟨J, hJ, hLJ⟩ := exists_sec6KComp_of_sec5Comp h hn.1 hH hH'H hL
      exact hLJ.trans (le_sSup hJ)
    · obtain ⟨J, hJ, hLJ⟩ := exists_sec6MComp_of_sec6MComp h hn hH hH'H hL
      exact hLJ.trans (le_sSup (Or.inr hJ))
  · obtain ⟨J, hJ, hLJ⟩ := exists_sec6MComp_of_sec6MComp h hn hH hH'H hL
    exact hLJ.trans (le_sSup hJ)

end Sec6L51B

theorem sec6Lemma51_b
    {X : Type} [Group X] [Finite X] (hc : SolCEx X) {n : ℕ}
    (hn : IsMaxAhatDeg X n) (H : Subgroup X) (hH : H ≠ ⊤) (t : X) (htH : t ∈ H)
    (ht : orderOf t = 2) :
    Sec6K X n (H ⊓ cen t) ≤ Sec6K X n H ∧ Sec6M X n (H ⊓ cen t) ≤ Sec6M X n H :=
  Sec6L51B.sec6K_le_of_le hc.toSolMinCEx hn hH inf_le_left

theorem sec6Lemma51
    {X : Type} [Group X] [Finite X] (hc : SolCEx X) {n : ℕ}
    (hn : IsMaxAhatDeg X n) : Sec6Lemma51 X n where
  b H hH t htH ht := sec6Lemma51_b hc hn H hH t htH ht
  sub s hs H hHs := by
    have := hc.simple
    exact Sec6L51B.sec6K_le_of_le hc.toSolMinCEx hn
      (centralizer_ne_top_of_involution hc.nonabelian hs) hHs

end CFSG.OddStandard.Solomon75
