module

public import CFSG.GH74.GLS.C3.Layer1.BkS4Wr
public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
public import CFSG.GH74.GLS.C3.Layer1.Th2P73

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_a_of_lt [Finite G] {T S : Subgroup G} (hS : IsPGroup 2 ↥S) (hTS : T < S) :
    ∃ a ∈ S, a ∈ normalizer (T : Set G) ∧ a ∉ T ∧ a * a ∈ T := by
  have hH : T.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h0 => ?_
    exact not_le_of_gt hTS (Subgroup.subgroupOf_eq_top.1 h0)
  obtain ⟨a, ha, haT, ha2⟩ := exists_normalizer_sq_mem_of_lt_top hS hH
  rw [← Subgroup.subgroupOf_normalizer_eq hTS.le] at ha
  refine ⟨(a : G), a.2, ha, haT, ?_⟩
  have h2 : (a : G) ^ 2 ∈ T := ha2
  rwa [sq] at h2

theorem mem_of_two_mul_card [Finite G] {P D : Subgroup G} (hDP : D ≤ P)
    (h : 2 * Nat.card ↥D = Nat.card ↥P) : ∀ p ∈ P, ∀ d ∈ D, p * d * p⁻¹ ∈ D := by
  have hcard : Nat.card ↥(D.subgroupOf P) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDP).toEquiv
  have hidx : (D.subgroupOf P).index = 2 := by
    have h1 := Subgroup.index_mul_card (D.subgroupOf P)
    rw [hcard] at h1
    have hpos : 0 < Nat.card ↥D := Nat.card_pos
    have : (D.subgroupOf P).index * Nat.card ↥D = 2 * Nat.card ↥D := by rw [h1, h]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have : (D.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hidx
  intro p hp d hd
  have h2 := this.conj_mem ⟨d, hDP hd⟩ hd ⟨p, hp⟩
  exact h2

theorem sec4Core_th2_A7 [Finite G] (hc5 : B_thm2_cent5) (hG : C3Hyp G) {x y : G}
    {K T S : Subgroup G} (hs : Th2Std x y K T S) (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) (hTS : T < S) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K)) :
    ∃ a : G, Sec4Core a (T ⊓ K) (T ⊓ CxK x K) T S ∧ Nat.card ↥T ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := hs.T_pGroup
  have hS2 : IsPGroup 2 ↥S := hs.sylowS.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := hs.T_le_C
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K :=
    hs.K_normal (by rw [hG.pRank_eq_four]) hcen hP2
  obtain ⟨a, haS, haN, haT, ha2⟩ := exists_a_of_lt hS2 hTS
  have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
    ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hKN t (hTC ht) p hp.2⟩
  have hNxK : ∀ t ∈ T, t ∈ NxK x K := by
    intro t ht
    refine ⟨hTC ht, mem_normalizer_of_two_sided (fun w hw => hKN t (hTC ht) w hw) (fun w hw => ?_)⟩
    have := hKN t⁻¹ ((centralizer ({x} : Set G)).inv_mem (hTC ht)) w hw
    simpa using this
  have hQn : ∀ t ∈ T, ∀ q ∈ T ⊓ CxK x K, t * q * t⁻¹ ∈ T ⊓ CxK x K := by
    intro t ht q hq
    refine ⟨T.mul_mem (T.mul_mem ht hq.1) (T.inv_mem ht), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (NxK_le_normalizer_CxK x K (hNxK t ht)) q).1 hq.2
  have hPD8 : IsD8 (T ⊓ K) := isD8_of_inf_alt7 hT2 hs.sylow_P e7
  have hCD := hs.commDisj hcen
  obtain ⟨ψ, hker, hψK⟩ := lemma113d_alt hs.K_le_C hKN (n := 7) (by norm_num) (by norm_num) e7
  have hker' : ψ.ker = (CMK (centralizer ({x} : Set G)) K).subgroupOf (centralizer ({x} : Set G)) :=
    hker
  have hQ4' : Nat.card ↥(T ⊓ CMK (centralizer ({x} : Set G)) K) = 4 := hQ4
  have hT64 : Nat.card ↥T ≤ 64 := card_le_sixtyfour_of_alt7 hT2 hTC ψ hker' hQ4'
  obtain ⟨ι, hιinj, hιcard, hι⟩ := inf_embeds_alt7 hT2 hs.sylow_P e7
  have hclause : ∀ g ∈ T, (∀ p ∈ T ⊓ K, g * p * g⁻¹ * p⁻¹ ∈ T ⊓ CxK x K) →
      g * g ∈ T ⊓ CxK x K := by
    intro g hgT hcomm
    have hgM : g ∈ centralizer ({x} : Set G) := hTC hgT
    have hkerm : ∀ (u : G) (hu : u ∈ centralizer ({x} : Set G)),
        ψ ⟨u, hu⟩ = 1 ↔ u ∈ CMK (centralizer ({x} : Set G)) K := by
      intro u hu
      rw [← MonoidHom.mem_ker, hker', Subgroup.mem_subgroupOf]
    have hσc : ∀ p : ↥(T ⊓ K), ψ ⟨g, hgM⟩ * ψ ⟨(p : G), hTC p.2.1⟩ =
        ψ ⟨(p : G), hTC p.2.1⟩ * ψ ⟨g, hgM⟩ := by
      intro p
      have hcp := hcomm p p.2
      have hcpM : g * p * g⁻¹ * p⁻¹ ∈ centralizer ({x} : Set G) :=
        (centralizer ({x} : Set G)).mul_mem
          ((centralizer ({x} : Set G)).mul_mem
            ((centralizer ({x} : Set G)).mul_mem hgM (hTC p.2.1))
            ((centralizer ({x} : Set G)).inv_mem hgM))
          ((centralizer ({x} : Set G)).inv_mem (hTC p.2.1))
      have h1 : ψ ⟨g * p * g⁻¹ * p⁻¹, hcpM⟩ = 1 := (hkerm _ hcpM).2 hcp.2
      have e1 : (⟨g * p * g⁻¹ * p⁻¹, hcpM⟩ : ↥(centralizer ({x} : Set G))) =
          ⟨g, hgM⟩ * ⟨(p : G), hTC p.2.1⟩ * ⟨g, hgM⟩⁻¹ * ⟨(p : G), hTC p.2.1⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : ⁅ψ ⟨g, hgM⟩, ψ ⟨(p : G), hTC p.2.1⟩⁆ = 1 := by
        rw [commutatorElement_def]
        exact h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
    have hsq : ψ ⟨g, hgM⟩ * ψ ⟨g, hgM⟩ = 1 := by
      refine alt7_centralizer_sq (X := ι.range) hιcard (ψ ⟨g, hgM⟩) ?_
      rintro y ⟨p, rfl⟩
      have h1 : ((ι p : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          ψ ⟨(p : G), hTC p.2.1⟩ := by
        rw [hι p]
        exact (hψK p p.2.2).symm
      rw [h1]
      exact hσc p
    have hgg : g * g ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).mul_mem hgM hgM
    have h3 : ψ ⟨g * g, hgg⟩ = 1 := by
      have e1 : (⟨g * g, hgg⟩ : ↥(centralizer ({x} : Set G))) = ⟨g, hgM⟩ * ⟨g, hgM⟩ := rfl
      rw [e1, map_mul]
      exact hsq
    exact ⟨T.mul_mem hgT hgT, (hkerm _ hgg).1 h3⟩
  have hshape : Sec4Shape (T ⊓ K) (T ⊓ CxK x K) T := by
    have hQcomm : IsMulCommutative ↥(T ⊓ CxK x K) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hQ4]; norm_num)
    have hcommQ : ∀ u v : ↥(T ⊓ CxK x K), u * v = v * u := fun u v => hQcomm.is_comm.comm u v
    by_cases hsq : ∀ g : ↥(T ⊓ CxK x K), g * g = 1
    · left
      exact isElementaryAbelian_of_forall
        (fun u hu v hv => congrArg Subtype.val (hcommQ ⟨u, hu⟩ ⟨v, hv⟩))
        (fun u hu => congrArg Subtype.val (hsq ⟨u, hu⟩))
    · right
      push Not at hsq
      obtain ⟨g, hg⟩ := hsq
      refine ⟨?_, hclause⟩
      have hdvd : orderOf g ∣ 2 ^ 2 := by
        have := orderOf_dvd_natCard g
        rwa [hQ4, show (4 : ℕ) = 2 ^ 2 by norm_num] at this
      obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hi2 : i = 2 := by
        interval_cases i
        · exfalso
          apply hg
          have h0 : orderOf g = 1 := by simpa using hgi
          rw [orderOf_eq_one_iff.1 h0]
          simp
        · exfalso
          apply hg
          have h0 : g ^ 2 = 1 := by
            rw [← pow_orderOf_eq_one g, hgi]
            simp
          rwa [sq] at h0
        · rfl
      exact isCyclic_of_orderOf_eq_card g (by rw [hgi, hi2, hQ4]; norm_num)
  have hcent6 : ∀ u ∈ T ⊓ CxK x K, u ≠ 1 → (∀ t ∈ T, u * t = t * u) →
      ∀ s ∈ S, s * u = u * s → s ∈ T := by
    intro u hu hu1 huT s hsS hsu
    have hodvd : orderOf u ∣ 2 ^ 2 := by
      have := Subgroup.orderOf_dvd_natCard (T ⊓ CxK x K) hu
      rwa [hQ4, show (4 : ℕ) = 2 ^ 2 by norm_num] at this
    have hu1' : orderOf u ≠ 1 := fun h0 => hu1 (orderOf_eq_one_iff.1 h0)
    have h2dvd : 2 ∣ orderOf u := by
      obtain ⟨i, hi, hui⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hodvd
      rcases i with _ | i
      · exact absurd (by simpa using hui) hu1'
      · rw [hui]
        exact dvd_pow_self 2 (Nat.succ_ne_zero i)
    have hv2 : orderOf (u ^ (orderOf u / 2)) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos u).ne' h2dvd
    have hvQ : u ^ (orderOf u / 2) ∈ T ⊓ CxK x K := Subgroup.pow_mem _ hu _
    have hvT : ∀ t ∈ T, u ^ (orderOf u / 2) * t = t * u ^ (orderOf u / 2) := fun t ht =>
      (Commute.pow_left (show Commute u t from huT t ht) _).eq
    have hsv : s * u ^ (orderOf u / 2) = u ^ (orderOf u / 2) * s :=
      (Commute.pow_right (show Commute s u from hsu) _).eq
    have hsyl := hc5 G hG x y K T S hs _ hvQ hvT hv2
    have hsC : s ∈ centralizer ({u ^ (orderOf u / 2)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hsv
    have hle : T ⊔ zpowers s ≤ centralizer ({u ^ (orderOf u / 2)} : Set G) :=
      sup_le hsyl.le (zpowers_le.2 hsC)
    have hleS : T ⊔ zpowers s ≤ S := sup_le hs.T_le_S (zpowers_le.2 hsS)
    have heq : T ⊔ zpowers s = T := hsyl.eq_of_le le_sup_left hle (hS2.to_le hleS)
    exact heq ▸ Subgroup.mem_sup_right (mem_zpowers s)
  have hrank4 : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E ≤ 16 := by
    intro E hE
    have h1 := card_eq_two_pow_pRank hE
    have h2 : pRank 2 ↥E ≤ pRank 2 G := Bg.pRank_subgroup_le one_lt_two E
    have h3 := hG.pRank_eq_four
    rw [h1]
    calc 2 ^ pRank 2 ↥E ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  refine ⟨a, ?_, hT64⟩
  exact
    { T_pgroup := hT2
      S_pgroup := hS2
      T_le_S := hs.T_le_S
      a_mem := haS
      a_mem_norm := haN
      a_not_mem := haT
      a_sq_mem := ha2
      P_le := inf_le_left
      Q_le := inf_le_left
      P_norm := hPn
      Q_norm := hQn
      P_d8 := hPD8
      Q_shape := hshape
      Q_card := hQ4
      PQ_comm := hCD.comm
      PQ_disj := hCD.inf
      cent6 := hcent6
      rank4 := hrank4 }

theorem b_thm2_A7_3b_T (hc5 : B_thm2_cent5) : B_thm2_A7_3b_T := by
  intro G _ _ hG x y K T S hs h7 hQ4 hTS D hD
  obtain ⟨e7⟩ := h7
  obtain ⟨hDP, hPK, hDel, hD4, -⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : pRank 2 ↥D = 2 := by
    have h1 := card_eq_two_pow_pRank hDel
    rw [hD4] at h1
    have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥D := by simpa using h1
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := hD2.symm.le.trans (pRank_mono' hDP)
  obtain ⟨a, hcore, hT64⟩ := sec4Core_th2_A7 hc5 hG hs e7 hQ4 hTS hP2
  have hTeq := hcore.T_eq_sup_of_card_le hT64
  have hxQ : x ∈ T ⊓ CxK x K := ⟨hs.x_mem_T, hs.x_mem_CxK⟩
  have hx2 : orderOf x = 2 := hs.orderOf_x
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    omega
  have hxx : x * x = 1 := by
    have h1 : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    rwa [sq] at h1
  have hxT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hs.T_le_C ht)).symm
  obtain ⟨z, hzP, hz1, hzc, hxPa, hza⟩ := hcore.exists_swap_of_card_le hT64 hxQ hx1 hxT
  have hcentx : ∀ s ∈ S, s * x = x * s → s ∈ T := hcore.cent6 x hxQ hx1 hxT
  have hS1 : ∀ n ∈ S, n ∈ normalizer (T : Set G) → n ∈ T ∨ a⁻¹ * n ∈ T := fun n hn hnN =>
    hcore.mem_T_or_of_normalizer hTeq hzP hz1 hzc hxPa hx1 hxx hxT hza hcentx hn hnN
  have hScases := hcore.S_cases hTeq hS1
  have hDnP := mem_of_two_mul_card hDP (by rw [hD4, hcore.P_d8.card_eq])
  have hDnT : ∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ ∈ D := by
    intro t ht d hd
    rw [hTeq] at ht
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute hcore.comm_P_conj ht
    have hdq : d * q = q * d := hcore.comm_P_conj d (hDP hd) q hq
    have e : p * q * d * (p * q)⁻¹ = p * d * p⁻¹ := by
      calc p * q * d * (p * q)⁻¹ = p * (q * d) * q⁻¹ * p⁻¹ := by group
        _ = p * (d * q) * q⁻¹ * p⁻¹ := by rw [hdq]
        _ = p * d * p⁻¹ := by group
    rw [e]
    exact hDnP p hp d hd
  have hsup : (⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom) = D ⊔ conjugate D a := by
    apply le_antisymm
    · refine iSup₂_le fun s hs' => ?_
      rintro _ ⟨d, hd, rfl⟩
      rcases hScases s hs' with hsT | hsT
      · exact Subgroup.mem_sup_left (show s * d * s⁻¹ ∈ D from hDnT s hsT d hd)
      · refine Subgroup.mem_sup_right ?_
        have h1 : (a⁻¹ * s) * d * (a⁻¹ * s)⁻¹ ∈ D := hDnT _ hsT d hd
        have h2 := hcore.conj_fwd hDnT h1
        have e : a * ((a⁻¹ * s) * d * (a⁻¹ * s)⁻¹) * a⁻¹ = s * d * s⁻¹ := by group
        rw [e] at h2
        exact h2
    · refine sup_le ?_ ?_
      · intro d hd
        exact Subgroup.mem_iSup_of_mem (1 : G) (Subgroup.mem_iSup_of_mem (one_mem S)
          ⟨d, hd, by show 1 * d * 1⁻¹ = d; group⟩)
      · intro y hy
        have hy' : a * y * a⁻¹ ∈ D := mem_conjugate_iff'.1 hy
        exact Subgroup.mem_iSup_of_mem a⁻¹ (Subgroup.mem_iSup_of_mem (S.inv_mem hcore.a_mem)
          ⟨a * y * a⁻¹, hy', by show a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y; group⟩)
  rw [hsup]
  have hPaT : conjugate (T ⊓ K) a ≤ T := hcore.conj_le hcore.P_le
  have hDaP : conjugate D a ≤ conjugate (T ⊓ K) a := by
    intro y hy
    rw [mem_conjugate_iff'] at hy ⊢
    exact hDP hy
  have hDa_el : CFSG.IsElementaryAbelian 2 ↥(conjugate D a) := isElementaryAbelian_conjugate hDel a
  have hcomm : ∀ d ∈ D, ∀ d' ∈ conjugate D a, d * d' = d' * d := fun d hd d' hd' =>
    hcore.comm_P_conj d (hDP hd) d' (hDaP hd')
  have hdisj : D ⊓ conjugate D a = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ (T ⊓ K) ⊓ conjugate (T ⊓ K) a := ⟨hDP hy.1, hDaP hy.2⟩
    rw [hcore.P_inf_conj] at this
    exact this
  have hEel := isElementaryAbelian_sup_of_commute hDel hDa_el hcomm
  have hEcard : Nat.card ↥(D ⊔ conjugate D a) = 16 := by
    rw [card_sup_of_commute_of_disjoint hcomm hdisj, card_conjugate', hD4]
  refine ⟨hEel, ?_, sup_le (hDP.trans hcore.P_le) (hDaP.trans hPaT)⟩
  have h1 := card_eq_two_pow_pRank hEel
  rw [hEcard] at h1
  have h2 : (2 : ℕ) ^ 4 = 2 ^ pRank 2 ↥(D ⊔ conjugate D a) := by simpa using h1
  exact (Nat.pow_right_injective le_rfl h2).le

end CFSG.GH74.GLS.C3.Layer1.Bk
