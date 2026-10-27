module

public import CFSG.GH74.GLS.C3.Layer1.Th2P812
public import CFSG.GH74.GLS.C3.Layer1.BkL114SE
public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10Proof
public import CFSG.GH74.GLS.C3.Layer1.Th2P61Strong
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem WeakBalAt.conj {B : Subgroup G} {a g : G} (hg : g ∈ normalizer (B : Set G))
    (h : WeakBalAt B a) : WeakBalAt B (g * a * g⁻¹) := by
  intro D hD c hc b hb
  have hginv : g⁻¹ ∈ normalizer (B : Set G) := Subgroup.inv_mem _ hg
  have hBcj : cj g⁻¹ B = B := cj_eq_of_mem_normalizer hginv
  have hD' : IsE 2 B (cj g⁻¹ D) := by
    have := isE_cj hD g⁻¹
    rwa [hBcj] at this
  have hDD' : cj g (cj g⁻¹ D) = D := cj_inv_cj g D
  have hcA : c ∈ cj g (AG (cj g⁻¹ D)) := by
    rw [← AG_cj, hDD']; exact hc.1
  have hcC : c ∈ cj g (centralizer ({a} : Set G)) := by
    rw [cj_centralizer_singleton]; exact hc.2
  rw [mem_cj_iff] at hcA hcC
  have hb' : g⁻¹ * b * g ∈ B := by
    have := (Subgroup.mem_normalizer_iff.1 hginv b).1 hb
    simpa using this
  have hmain := h (cj g⁻¹ D) hD' (g⁻¹ * c * g) ⟨hcA, hcC⟩ (g⁻¹ * b * g) hb'
  rw [← cj_centralizer_singleton, pPrimeCoreOf_cj, mem_cj_iff]
  have e : g⁻¹ * ⁅c, b⁆ * g = ⁅g⁻¹ * c * g, g⁻¹ * b * g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hmain

theorem mem_of_even_mem_sup_swap {F : Subgroup (Perm (Fin 7))} {t σ : Perm (Fin 7)}
    (hF : F ≤ alternatingGroup (Fin 7)) (ht : t.IsSwap) (hdisj : ∀ f ∈ F, Disjoint f t)
    (hσ : σ ∈ F ⊔ Subgroup.zpowers t) (hev : σ ∈ alternatingGroup (Fin 7)) : σ ∈ F := by
  have hcomm : ∀ f ∈ F, ∀ q ∈ Subgroup.zpowers t, f * q = q * f := by
    intro f hf q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact ((hdisj f hf).commute.zpow_right n).eq
  obtain ⟨f, hf, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hσ
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
  obtain ⟨x, y, hxy, rfl⟩ := ht
  have hsf : Equiv.Perm.sign f = 1 := Equiv.Perm.mem_alternatingGroup.1 (hF hf)
  have hsσ : Equiv.Perm.sign (f * swap x y ^ n) = 1 := Equiv.Perm.mem_alternatingGroup.1 hev
  rw [map_mul, hsf, one_mul, map_zpow, Equiv.Perm.sign_swap hxy] at hsσ
  have hsq : swap x y ^ 2 = 1 := by
    rw [pow_two]; exact swap_mul_self x y
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have : swap x y ^ (2 * k) = 1 := by
      rw [zpow_mul, zpow_two, ← pow_two, hsq, one_zpow]
    rw [this, mul_one]
    exact hf
  · exfalso
    have : (-1 : ℤˣ) ^ (2 * k + 1) = -1 := by
      rw [zpow_add, zpow_one, zpow_mul]
      simp
    rw [this] at hsσ
    exact absurd hsσ (by decide)

theorem Obstr52.false_of_solvable {B : Subgroup G} {a : G} {J : Subgroup G} (h : Obstr52 B a J)
    (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hsol : Group.IsSolvable ↥(centralizer ({a} : Set G))) : False := by
  obtain ⟨e⟩ := h.nonempty_A7_of_rank_four hG4 hB
  have hJs : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h.comp.1)
  have hbar : Group.IsSolvable (kBar J) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J))
  have hA7 : Group.IsSolvable (alternatingGroup (Fin 7)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact C3.Layer1.Bk.alt_not_isSolvable 7 (Or.inr rfl) hA7

theorem eq_of_obstr_x {x y : G} {K T S J : Subgroup G} (hs : Th2Std x y K T S)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hJc : IsPCompIn 2 (centralizer ({x} : Set G)) J)
    (hJ7 : Nonempty (kBar J ≃* alternatingGroup (Fin 7))) : J = K := by
  by_contra hne
  obtain ⟨e⟩ := hJ7
  have hle : J ≤ centralizerSection K (pPrimeCoreOf 2 K) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hJc hs.comp hne
  have hJC : J ≤ CxK x K := le_inf hJc.1 hle
  have h2520 : Nat.card (kBar J) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hJcard : Nat.card ↥J = Nat.card (kBar J) * Nat.card ↥(pPrimeCore 2 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J)
  have h8 : 8 ∣ Nat.card ↥J := by
    rw [hJcard, h2520]
    exact Dvd.dvd.mul_right ⟨315, by norm_num⟩ _
  have h8' : 8 ∣ Nat.card ↥(CxK x K) := h8.trans (Subgroup.card_dvd_of_le hJC)
  have hsyl := hs.sylow_Q.card_eq
  rw [hQ4] at hsyl
  have hv : (Nat.card ↥(CxK x K)).factorization 2 = 2 := by
    have h4 : 2 ^ 2 = 2 ^ (Nat.card ↥(CxK x K)).factorization 2 := by simpa using hsyl
    exact (Nat.pow_right_injective le_rfl h4).symm
  have hpos : Nat.card ↥(CxK x K) ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ≤ (Nat.card ↥(CxK x K)).factorization 2 := by
    have : 2 ^ 3 ∣ Nat.card ↥(CxK x K) := by simpa using h8'
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 this
  omega

theorem false_of_obstr_x (hG : C3Hyp G) {x y : G} {K T S : Subgroup G}
    (hs : Th2Std x y K T S) (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4)
    {D B : Subgroup G} (hD : IsDSub K (T ⊓ K) D) (hDB : D ≤ B)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) {J : Subgroup G} (hJ : Obstr52 B x J) : False := by
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G) := hJ.normalizes hG4 hBel
  have hJ7 := hJ.nonempty_A7_of_rank_four hG4 hBel
  have hJK : J = K := eq_of_obstr_x hs hQ4 hJ.comp hJ7
  have hJ' : Obstr52 B x K := hJK ▸ hJ
  have hBN' : ∀ g ∈ B, g ∈ normalizer (K : Set G) := hJK ▸ hBN
  obtain ⟨D', hD'⟩ := hJ'.exists_D
  obtain ⟨hDP, hPK, hDel, hD4, e', hmoved⟩ := hD
  obtain ⟨t, ht, hdis, hE⟩ := (hD'.B_inv hBN').2 e'
  have hF := hD'.D_root e'
  have hdisj : ∀ f ∈ (D'.subgroupOf (normalizer (K : Set G))).map (a7Act K e'), Disjoint f t := by
    intro f hf i
    by_cases h : f i = i
    · exact Or.inl h
    · exact Or.inr (hdis i ⟨f, hf, h⟩)
  have hmem : ∀ d (hd : d ∈ D), ∃ f ∈ (D'.subgroupOf (normalizer (K : Set G))).map (a7Act K e'),
      f = ((e' (QuotientGroup.mk (⟨d, (hDP hd).2⟩ : ↥K)) : alternatingGroup (Fin 7)) :
        Perm (Fin 7)) := by
    intro d hd
    have hdK : d ∈ K := (hDP hd).2
    have hdB : d ∈ B := hDB hd
    have hψd : a7Act K e' ⟨d, Subgroup.le_normalizer hdK⟩ =
        ((e' (QuotientGroup.mk (⟨d, hdK⟩ : ↥K)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
      a7Act_of_mem e' hdK
    have hdE : a7Act K e' ⟨d, Subgroup.le_normalizer hdK⟩ ∈
        (B.subgroupOf (normalizer (K : Set G))).map (a7Act K e') :=
      ⟨⟨d, Subgroup.le_normalizer hdK⟩, Subgroup.mem_subgroupOf.mpr hdB, rfl⟩
    rw [hE] at hdE
    have hev : a7Act K e' ⟨d, Subgroup.le_normalizer hdK⟩ ∈ alternatingGroup (Fin 7) := by
      rw [hψd]; exact (e' _).2
    exact ⟨_, mem_of_even_mem_sup_swap hF.1 ht hdisj hdE hev, hψd⟩
  have hsub : {i : Fin 7 | ∃ d ∈ D, ∃ hd : d ∈ K,
      ((e' (QuotientGroup.mk (⟨d, hd⟩ : ↥K)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) i ≠ i} ⊆
      {i | ∃ f ∈ (D'.subgroupOf (normalizer (K : Set G))).map (a7Act K e'), f i ≠ i} := by
    rintro i ⟨d, hd, hdK, hi⟩
    obtain ⟨f, hf, hfe⟩ := hmem d hd
    exact ⟨f, hf, by rw [hfe]; exact hi⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hmoved, hF.ncard_moved] at hle
  omega

theorem q_elementary {x y : G} {K T S : Subgroup G} (hs : Th2Std x y K T S)
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hnot : ¬ IsExceptionalA7Triple x y K) :
    CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) := by
  have h2 : 2 ≤ pRank 2 ↥(CxK x K) := (hs.v2ss.isV2Triple.2.2.1).resolve_right hnot
  have h2Q : 2 ≤ pRank 2 ↥(T ⊓ CxK x K) := by
    rw [Th2.pRank_eq_of_isSylowOf hs.sylow_Q]; exact h2
  obtain ⟨E, hEQ, hEel, hErk⟩ := exists_elemAbelian_pRank (T ⊓ CxK x K)
  have hEcard : 2 ^ 2 ≤ Nat.card ↥E := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel, hErk]
    exact Nat.pow_le_pow_right (by norm_num) h2Q
  have hle : Nat.card ↥E ≤ Nat.card ↥(T ⊓ CxK x K) := Subgroup.card_le_of_le hEQ
  have heq : E = T ⊓ CxK x K := Subgroup.eq_of_le_of_card_ge hEQ (by omega)
  rw [← heq]
  exact hEel

end Basic

end CFSG.GH74.GLS.Th2.Obs

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs CFSG.GH74.GLS.Th2.Bal

@[expose] def B_prop43f_3b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) →
        ∀ D : Subgroup G, IsDSub K (T ⊓ K) D →
          ∀ b ∈ (⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom : Subgroup G), (∃ c : G, c * x * c⁻¹ = b) →
            ∃ g ∈ normalizer ((⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G),
              g * x * g⁻¹ = b

@[expose] def B_prop412a_3b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) →
        ∀ u : G, orderOf u = 2 → (¬ ∃ c : G, c * x * c⁻¹ = u) →
          Group.IsSolvable ↥(centralizer ({u} : Set G))

theorem b_prop615_of_comp
    (hcomp : ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ a : G, orderOf a = 2 →
      ∀ L : Subgroup (CentralizerBar a), IsComponent L →
        ¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) →
          Nonempty (↥L ≃* alternatingGroup (Fin 7)) ∨ HasL2Model ↥L (fun q => Odd q ∧ ¬ IsFM9 q))
    (h3b : B_thm2_A7_3b_T) (hexc : B_thm2_A7_exc) (hf : B_prop43f_3b) (hg : B_prop412a_3b) :
    B_prop615 := by
  intro G _ _ hG x y K T S hs h7 hQ4 hTS D hD
  have hBdef : ∃ B : Subgroup G, B = ⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ := hBdef
  rw [← hBdef]
  obtain ⟨hBel', -, -⟩ := h3b G hG x y K T S hs h7 hQ4 hTS D hD
  rw [← hBdef] at hBel'
  have hQel : CFSG.IsElementaryAbelian 2 ↥(T ⊓ CxK x K) :=
    q_elementary hs hQ4 (hexc G hG x y K T S hs)
  have hDB : D ≤ B := fun d hd => by
    rw [hBdef]
    exact Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem (one_mem S)
      ⟨d, hd, by show 1 * d * 1⁻¹ = d; group⟩)
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hx1 : x ≠ 1 := by
    intro h1
    have := hs.orderOf_x
    rw [h1, orderOf_one] at this
    omega
  have hcomp' := hcomp G hG
  rw [isWeakKBal_two_iff]
  intro a haB ha1
  obtain ⟨-, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel'
  have ha2 : orderOf a = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hBsq a haB) ha1
  by_cases hconj : ∃ c : G, c * x * c⁻¹ = a
  · obtain ⟨g, hgN, hga⟩ := hf G hG x y K T S hs h7 hQ4 hTS hQel D hD a
      (by rw [← hBdef]; exact haB) hconj
    rw [← hBdef] at hgN
    have hxB : x ∈ B := by
      have hginv : g⁻¹ ∈ normalizer (B : Set G) := Subgroup.inv_mem _ hgN
      have h1 := (Subgroup.mem_normalizer_iff.1 hginv a).1 haB
      have e : g⁻¹ * a * g⁻¹⁻¹ = x := by rw [← hga]; group
      rwa [e] at h1
    have hWx : WeakBalAt B x := by
      by_contra hnot
      obtain ⟨J, hJ⟩ := exists_obstr52_at_of_comp hBel' hxB hx1 hcomp' hnot
      exact false_of_obstr_x hG hs hQ4 hD hDB hBel' hJ
    rw [← hga]
    exact WeakBalAt.conj hgN hWx
  · by_contra hnot
    obtain ⟨J, hJ⟩ := exists_obstr52_at_of_comp hBel' haB ha1 hcomp' hnot
    exact hJ.false_of_solvable hG4 hBel'
      (hg G hG x y K T S hs h7 hQ4 hTS hQel a ha2 hconj)

theorem b_prop615_of
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    (h3b : B_thm2_A7_3b_T) (hexc : B_thm2_A7_exc) (hf : B_prop43f_3b) (hg : B_prop412a_3b) :
    B_prop615 :=
  b_prop615_of_comp
    (fun _ _ _ hG _ ha _ hL hnb =>
      (Th2.Bal.component_local hGKF hE2 b_ivk_10_5 hL34 hG ha hL).2 hnb)
    h3b hexc hf hg

end CFSG.GH74.GLS
