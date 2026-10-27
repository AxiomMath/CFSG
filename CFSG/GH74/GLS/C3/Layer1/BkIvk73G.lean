module

public import CFSG.GH74.GLS.C3.Layer1.BkL114SEAsm
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Abs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53M
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L55B

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

section GLevel

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem exists_isSylowOf_ge_two {Q R : Subgroup G} (hQ : IsPGroup 2 ↥Q) (hQR : Q ≤ R) :
    ∃ T : Subgroup G, IsSylowOf 2 T R ∧ Q ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf R) := hQ.comap_subtype
  obtain ⟨T', hT'⟩ := hQ'.exists_le_sylow
  refine ⟨(T' : Subgroup R).map R.subtype, ⟨T', rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQR hq⟩, hT' (show (⟨q, hQR hq⟩ : R) ∈ Q.subgroupOf R from hq), rfl⟩

omit [Finite G] in
theorem isQuasisimple_of_isCompIn' {X M : Subgroup G} (h : IsCompIn X M) : IsQuasisimple ↥M :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.1

omit [Finite G] in
theorem centerlessBar_of_kbar {m : ℕ} (hm : m = 5 ∨ m = 7) {M : Subgroup G}
    (h : Nonempty (kBar M ≃* alternatingGroup (Fin m))) : CenterlessBar M := by
  rcases hm with rfl | rfl
  · exact centerlessBar_of_A5 h
  · exact centerlessBar_of_A7 h

theorem isSylowOf_Q_centralizer (hn : n = 5 ∨ n = 7) (h : IsAConfigW n x K T Q S a) :
    IsSylowOf 2 Q (centralizer (K : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hterm := h.terminal
  have hKcomp : IsCompIn (centralizer ({x} : Set G)) K := hterm.2.1
  have hKq : IsQuasisimple ↥K := isQuasisimple_of_isCompIn' hKcomp
  have hev : 2 ∣ Nat.card ↥K := hterm.2.2.1
  have hcen : CenterlessBar K := centerlessBar_of_kbar hn h.kbar
  have hCxK : CxK x K ≤ centralizer (K : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.2 fun k hk => (Th2.commute_of_mem_cSec hKq hc.2 k hk).symm
  have hCK_cs : centralizer (K : Set G) ≤ centralizerSection K (pPrimeCoreOf 2 K) := fun c hc =>
    C3.Layer1.Back.mem_centralizerSection_of_centralizes
      (fun k hk => (Subgroup.mem_centralizer_iff.1 hc k hk).symm) (TwoThin.pPrimeCoreOf_le K)
  have hQC : Q ≤ centralizer (K : Set G) := h.Q_le_CxK.trans hCxK
  have hQ2 : IsPGroup 2 ↥Q := h.sylowQ.isPGroup
  obtain ⟨Qs, hQs, hQQs⟩ := exists_isSylowOf_ge_two hQ2 hQC
  have hQs2 : IsPGroup 2 ↥Qs := hQs.isPGroup
  have hxQs : x ∈ Qs := hQQs h.x_mem_Q
  have hW : Qs ⊓ centralizer ({x} : Set G) = Q :=
    h.sylowQ.eq_of_le (fun q hq => ⟨hQQs hq, (h.Q_le_CxK hq).1⟩)
      (fun c hc => ⟨hc.2, hCK_cs (hQs.le hc.1)⟩) hQs2.to_inf_left
  have hQsne : Qs ≠ ⊥ := by
    intro h0
    have h1 : x ∈ (⊥ : Subgroup G) := h0 ▸ hxQs
    rw [Subgroup.mem_bot] at h1
    have := h.x_order
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨u, huQs, hu2, huc⟩ := Th2.exists_central_involution hQs2 hQsne
  have huQ : u ∈ Q := by
    rw [← hW]
    exact ⟨huQs, mem_centralizer_singleton_iff.2 (huc x hxQs)⟩
  have huK : u ∈ centralizer (K : Set G) := hQs.le huQs
  have hKu := hterm.2.2.2 u hu2 huK
  have hKC : K ≤ centralizer ({u} : Set G) := hKu.1
  have hK2 : IsPCompIn 2 (centralizer ({u} : Set G)) K := isPCompIn_two_of_isCompIn_of_even hKu hev
  obtain ⟨hpumpK, hKK⟩ := Th2.pumpUp_eq_self hKC hK2
  have hQab : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := fun q hq q' hq' => by
    have := h.elemQ
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥Q)).comm ⟨q, hq⟩ ⟨q', hq'⟩)
  have hrank : 3 ≤ pRank 2 ↥(centralizer ({u} : Set G)) := by
    obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 hev
    have ht2 : orderOf (t' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht'
    have htK : (t' : G) ∈ K := t'.2
    have htQ : (t' : G) ∉ Q := fun htQ =>
      no_central_involution_of_centerless hcen ht2 htK fun k hk =>
        Subgroup.mem_centralizer_iff.1 (hQC htQ) k hk
    have hcd : Th2.CommDisj Q (zpowers (t' : G)) := by
      refine ⟨fun q hq z hz => ?_, ?_⟩
      · obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hz
        have hqt : q * (t' : G) = (t' : G) * q :=
          (Subgroup.mem_centralizer_iff.1 (hQC hq) _ htK).symm
        exact (Commute.zpow_right (show Commute q (t' : G) from hqt) j).eq
      · refine eq_bot_iff.2 fun z hz => ?_
        rcases GLS.mem_zpowers_two ht2 hz.2 with h0 | h0
        · simp [h0]
        · exact absurd (h0 ▸ hz.1) htQ
    have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers (t' : G)) :=
      Th2.isElementaryAbelian_zpowers_of_orderOf_two ht2
    have hQr : pRank 2 ↥Q = 2 := by
      have h1 := C3.Layer1.Back.card_eq_two_pow_pRank h.elemQ
      rw [h.card_Q] at h1
      have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥Q := by simpa using h1
      exact (Nat.pow_right_injective le_rfl h2).symm
    have hsup := hcd.pRank_sup h.elemQ hxel le_rfl le_rfl
    have hle : Q ⊔ zpowers (t' : G) ≤ centralizer ({u} : Set G) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.2 (hQab q hq u huQ)) ?_
      refine zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_)
      exact Subgroup.mem_centralizer_iff.1 huK _ htK
    have := C3.Layer1.Back.pRank_mono' hle
    rw [hsup, hQr, Th2.pRank_zpowers_of_orderOf_two ht2] at this
    omega
  have hILo_u : IsILo 2 u K := ⟨hu2, by simpa [oBound] using hrank, hK2⟩
  have hterm' : IsPTerminal 2 x K := h.twoTerminal
  have hpump : PumpUpLT 2 x K u K :=
    ⟨hterm'.1, hILo_u, (h.T_le_C (h.Q_le_T huQ)), (h.Q_le_CxK huQ).2, by rw [hpumpK]; exact hKK⟩
  have hsyl_u := hterm'.2.2 Q h.sylowQ u K hpump huQ (fun q hq => huc q (hQQs hq))
  have hQsle : Qs ≤ centralizer ({u} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K) :=
    le_inf (fun c hc => mem_centralizer_singleton_iff.2 (huc c hc).symm)
      (fun c hc => hCK_cs (hQs.le hc))
  have hEq : Qs = Q := hsyl_u.eq_of_le hQQs hQsle hQs2
  rw [hEq] at hQs
  exact hQs

theorem isPCompIn_subgroupOf_centralizer {N K : Subgroup G} {u : G} (huN : u ∈ N) (hKN : K ≤ N)
    (h : IsPCompIn 2 (centralizer ({u} : Set G)) K) :
    IsPCompIn 2 (centralizer ({(⟨u, huN⟩ : ↥N)} : Set ↥N)) (K.subgroupOf N) := by
  have hKC : K ≤ centralizer ({u} : Set G) := h.1
  have h1 : IsPCompIn 2 (centralizer ({u} : Set G) ⊓ N) K :=
    isPCompIn_of_le h (le_inf hKC hKN) inf_le_left
  rw [EvenCore.centralizer_singleton_mk_eq u huN]
  refine ⟨fun m hm => hKC hm, ?_⟩
  have h2 := (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (X := N)
    (Y := centralizer ({u} : Set G) ⊓ N) (L := K) inf_le_right 2 Nat.prime_two).2 h1.2
  rwa [Subgroup.inf_subgroupOf_right] at h2

omit [Finite G] in
theorem centralizer_subgroupOf_eq {N K : Subgroup G} (hKN : K ≤ N) :
    centralizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) =
      (centralizer (K : Set G) ⊓ N).subgroupOf N := by
  ext m
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    SetLike.mem_coe]
  constructor
  · intro hm
    refine ⟨fun k hk => ?_, m.2⟩
    have h1 := hm ⟨k, hKN hk⟩ (show (⟨k, hKN hk⟩ : ↥N) ∈ K.subgroupOf N from hk)
    exact congrArg Subtype.val h1
  · rintro ⟨hm, -⟩ k hk
    exact Subtype.ext (hm k hk)

theorem isSylowOf_subgroupOf_of_le {N P A : Subgroup G} (hPA : P ≤ A) (hAN : A ≤ N)
    (h : IsSylowOf 2 P A) : IsSylowOf 2 (P.subgroupOf N) (A.subgroupOf N) := by
  have h2 : IsSylowOf 2 ((P.subgroupOf N).map N.subtype) ((A.subgroupOf N).map N.subtype) := by
    rw [Subgroup.map_subgroupOf_eq_of_le (hPA.trans hAN), Subgroup.map_subgroupOf_eq_of_le hAN]
    exact h
  exact (isSylowOf_map_subtype_iff N).1 h2

theorem pPrimeCoreOf_le_NW (h : IsAConfigW n x K T Q S a) :
    pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 (NW x) := by
  have hKC : K ≤ centralizer ({x} : Set G) := h.K_le_C
  have hKn : (K.subgroupOf (centralizer ({x} : Set G))).Normal :=
    ⟨fun y hy g => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact h.normalInC g g.2 y hy⟩
  have h1 : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) :=
    pPrimeCoreOf_le_of_normal 2 hKC hKn
  have h2 : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ pPrimeCoreOf 2 (NW x) := by
    refine le_pPrimeCoreOf_of_normal Subgroup.le_normalizer ?_
      (TwoThin.card_pPrimeCoreOf_odd _)
    intro g hg y hy
    exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy
  exact h1.trans h2

omit [Finite G] in
theorem mem_pPrimeCore_of_le {N K : Subgroup G} [Finite G] (hKN : K ≤ N)
    (h : pPrimeCoreOf 2 K ≤ pPrimeCoreOf 2 N) :
    ∀ k : ↥(K.subgroupOf N), k ∈ pPrimeCore 2 ↥(K.subgroupOf N) → (k : ↥N) ∈ pPrimeCore 2 ↥N := by
  intro k hk
  let ψ : ↥(K.subgroupOf N) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKN
  have h1 : ψ k ∈ pPrimeCore 2 ↥K := by
    rw [← pPrimeCore_map_iso 2 ψ]
    exact ⟨k, hk, rfl⟩
  have h2 : ((ψ k : ↥K) : G) ∈ pPrimeCoreOf 2 K := ⟨ψ k, h1, rfl⟩
  obtain ⟨o, ho, hoe⟩ := h h2
  have : o = (k : ↥N) := Subtype.ext hoe
  rwa [← this]

end GLevel

section Main

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

omit [Finite G] in
theorem isQuasisimple_alt {m : ℕ} (hm : m = 5 ∨ m = 7) :
    IsQuasisimple ↥(alternatingGroup (Fin m)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rcases hm with rfl | rfl <;> simp)
  have hnc : ∃ a b : ↥(alternatingGroup (Fin m)), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact alt_not_isSolvable m hm
      ((IsSimpleGroup.comm_iff_isSolvable (G := ↥(alternatingGroup (Fin m)))).1 hc)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem NW_ne_top (hks : IsKProperSimple G) (h : IsAConfigW n x K T Q S a)
    (hW : pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥) : NW x ≠ ⊤ := by
  intro htop
  have hs : IsSimpleGroup G := (isKProperSimple_iff.1 hks).1
  have hnc : ∃ a b : G, a * b ≠ b * a := (isKProperSimple_iff.1 hks).2.1
  have hWn : (pPrimeCoreOf 2 (centralizer ({x} : Set G))).Normal :=
    ⟨fun y hy g => by
      have hg : g ∈ NW x := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.1 hg y).1 hy⟩
  have hWne : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≠ ⊥ := by
    intro hb
    apply hW
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hb
  rcases hs.eq_bot_or_eq_top_of_normal (pPrimeCoreOf 2 (centralizer ({x} : Set G))) with hb | ht
  · exact hWne hb
  · have hC : centralizer ({x} : Set G) = ⊤ :=
      top_le_iff.1 (ht ▸ TwoThin.pPrimeCoreOf_le _)
    exact centralizer_involution_ne_top hs hnc h.x_order hC

theorem card_le_card_S_of_isPGroup (h : IsAConfigW n x K T Q S a) {R : Subgroup (NWbar x)}
    (hR : IsPGroup 2 ↥R) : Nat.card ↥R ≤ Nat.card ↥S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hd1 : Nat.card ↥R ∣ Nat.card (NWbar x) := Subgroup.card_subgroup_dvd_card R
  have hd2 : Nat.card (NWbar x) ∣ Nat.card ↥(NW x) := Subgroup.card_quotient_dvd_card _
  have hd3 : Nat.card ↥(NW x) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  have hdG : 2 ^ k ∣ Nat.card G := hk ▸ (hd1.trans (hd2.trans hd3))
  have hS := h.sylowS.card_eq
  rw [Subgroup.card_top] at hS
  have hk2 : k ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdG
  rw [hk, hS]
  exact Nat.pow_le_pow_right (by norm_num) hk2

end Main

section Seven

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_isComponent_of_card_two_part {K Q : Subgroup Y} {g x : Y}
    (hK : IsComponent K) (hZ : ∀ y ∈ K, (∀ k ∈ K, k * y = y * k) → y = 1)
    (h8 : 2 ^ 3 ∣ Nat.card ↥K) (hQS : IsSylowOf 2 Q (centralizer (K : Set Y)))
    (hQcard : Nat.card ↥Q ≤ 4) (hxC : x ∈ centralizer (K : Set Y)) (hx1 : x ≠ 1)
    (hgx : g * x * g⁻¹ ∈ K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' : Subgroup Y := K.map (MulAut.conj g⁻¹).toMonoidHom with hK'def
  have hK' : IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hK
  have hxK' : x ∈ K' := by
    rw [hK'def, mem_map_conjHom_iff]
    simpa using hgx
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with heq | hcomm
  ·
    have hxK : x ∈ K := heq ▸ hxK'
    exact hx1 (hZ x hxK fun k hk => (Subgroup.mem_centralizer_iff.1 hxC k hk))
  ·
    have hK'C : K' ≤ centralizer (K : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := Subgroup.commutator_mem_commutator hk hy
      rw [hcomm, Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1)
    have hcard' : Nat.card ↥K' = Nat.card ↥K :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have h8' : 2 ^ 3 ∣ Nat.card ↥K' := hcard' ▸ h8
    obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8'
    have hR2 : IsPGroup 2 ↥(R.map K'.subtype) := by
      have : IsPGroup 2 ↥R := IsPGroup.of_card hR
      exact this.map K'.subtype
    have hRle : R.map K'.subtype ≤ centralizer (K : Set Y) :=
      (Subgroup.map_subtype_le R).trans hK'C
    have hRcard : Nat.card ↥(R.map K'.subtype) = 2 ^ 3 := by
      rw [Subgroup.card_map_of_injective K'.subtype_injective]; exact hR
    obtain ⟨T', hT', hRT'⟩ := exists_isSylowOf_ge_two hR2 hRle
    have hle : Nat.card ↥(R.map K'.subtype) ≤ Nat.card ↥T' := Subgroup.card_le_of_le hRT'
    have hTQ : Nat.card ↥T' = Nat.card ↥Q := hT'.card_eq.trans hQS.card_eq.symm
    omega

end Seven

section Final

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def B_ivk_7_3_A57_std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfigW 5 x K T Q S a → S = T ⊔ zpowers a →
      a * x * a⁻¹ ∈ T ⊓ K → a ∈ NW x → pPrimeCore 2 ↥(centralizer ({x} : Set G)) ≠ ⊥ →
        ¬ CFSG.IsComponent (toNWbar x K)

end Final

end CFSG.GH74.GLS.C3.Layer1.Bk
