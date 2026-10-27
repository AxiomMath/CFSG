module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617F
public import CFSG.GH74.GLS.C3.Layer1.Th2P617L

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem exists_Qpp (hG : C3Hyp G) (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    ∃ Q'' : Subgroup G, T ⊓ CxK x K ≤ Q'' ∧ Q'' ≤ T ∧
      (∀ p ∈ T ⊓ K, ∀ q ∈ Q'', p * q = q * p) ∧ (T ⊓ K) ⊓ Q'' = ⊥ ∧
      ∀ s ∈ T, ∃ p ∈ T ⊓ K, ∃ q ∈ Q'', s = p * q := by
  classical
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hTN := Th2Std.T_le_normalizer hG hs ⟨eK⟩
  by_cases hTR : ∀ s ∈ T, s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)
  · refine ⟨T ⊓ CxK x K, le_rfl, inf_le_left, fun p hp q hq => hcd.comm p hp q hq, hcd.inf,
      fun s hs' => ?_⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm (hTR s hs')
    exact ⟨p, hp, q, hq, rfl⟩
  · push Not at hTR
    obtain ⟨s₀, hs₀T, hs₀R⟩ := hTR
    obtain ⟨t, htT, htR, ht2, hcoset, htP⟩ :=
      exists_odd_involution_coset hs hcd ⟨eK⟩ eK hTN hs₀T hs₀R
    set ψ := actOn eK hTN with hψ
    set f : Perm (Fin 7) := ψ ⟨t, htT⟩ with hf
    have hfodd : f ∉ alternatingGroup (Fin 7) := fun hev => htR (mem_R_of_actOn_even hs hcd ⟨eK⟩ eK hTN htT hev)
    have hff : f * f = 1 := by
      have h1 : ψ ⟨t * t, T.mul_mem htT htT⟩ = 1 := (actOn_T_eq_one_iff hs eK hTN _).2 ht2
      have h2 : (⟨t * t, T.mul_mem htT htT⟩ : ↥T) = ⟨t, htT⟩ * ⟨t, htT⟩ := rfl
      rw [h2, map_mul] at h1
      exact h1
    let A : Subgroup ↥T := (zpowers f).comap ψ
    let Q'' : Subgroup G := (T ⊓ centralizer ((T ⊓ K : Subgroup G) : Set G)) ⊓ A.map T.subtype
    have hQ''mem : ∀ g, g ∈ Q'' ↔ g ∈ T ∧ (∀ p ∈ T ⊓ K, p * g = g * p) ∧
        ∃ hg : g ∈ T, ψ ⟨g, hg⟩ ∈ zpowers f := by
      intro g
      constructor
      · rintro ⟨⟨hgT, hgc⟩, ⟨h, hhA, rfl⟩⟩
        exact ⟨h.2, fun p hp => Subgroup.mem_centralizer_iff.1 hgc p hp, h.2, hhA⟩
      · rintro ⟨hgT, hc, hg, hz⟩
        exact ⟨⟨hgT, Subgroup.mem_centralizer_iff.2 hc⟩, ⟨⟨g, hg⟩, hz, rfl⟩⟩
    have hQle : T ⊓ CxK x K ≤ Q'' := by
      intro q hq
      refine (hQ''mem q).2 ⟨hq.1, fun p hp => hcd.comm p hp q hq, hq.1, ?_⟩
      rw [(actOn_T_eq_one_iff hs eK hTN hq.1).2 hq]
      exact one_mem _
    have hf1 : f ≠ 1 := fun h => hfodd (h ▸ one_mem _)
    have hfo : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hff) hf1
    have hPQ'' : (T ⊓ K) ⊓ Q'' = ⊥ := by
      refine eq_bot_iff.2 fun w hw => ?_
      obtain ⟨hwP, hwQ⟩ := hw
      obtain ⟨hwT, -, hwT', hwz⟩ := (hQ''mem w).1 hwQ
      have hev : ψ ⟨w, hwT⟩ ∈ alternatingGroup (Fin 7) :=
        actOn_even_of_mem_R hcd hs eK hTN (Subgroup.mem_sup_left hwP) hwT
      have hw1 : w = 1 := by
        rcases mem_zpowers_two hfo hwz with h0 | h0
        · have hwQ' : w ∈ T ⊓ CxK x K := (actOn_T_eq_one_iff hs eK hTN hwT).1 h0
          exact hcd.eq_one_of_mem hwP hwQ'
        · exact absurd (h0 ▸ hev) hfodd
      rw [hw1]
      exact Subgroup.one_mem _
    refine ⟨Q'', hQle, fun g hg => ((hQ''mem g).1 hg).1, ?_, hPQ'', ?_⟩
    · intro p hp q hq
      exact ((hQ''mem q).1 hq).2.1 p hp
    · intro s hsT
      by_cases hsR : s ∈ (T ⊓ K) ⊔ (T ⊓ CxK x K)
      · obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hsR
        exact ⟨p, hp, q, hQle hq, rfl⟩
      · have hr := hcoset s hsT hsR
        obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_of_mem_sup_of_commute hcd.comm hr
        refine ⟨p, hp, q * t, ?_, ?_⟩
        · refine (hQ''mem (q * t)).2 ⟨T.mul_mem hq.1 htT, fun p' hp' => ?_, T.mul_mem hq.1 htT, ?_⟩
          · calc p' * (q * t) = (p' * q) * t := by group
              _ = (q * p') * t := by rw [hcd.comm p' hp' q hq]
              _ = q * (p' * t) := by group
              _ = q * (t * p') := by rw [(htP p' hp').symm]
              _ = (q * t) * p' := by group
          · have h1 : (⟨q * t, T.mul_mem hq.1 htT⟩ : ↥T) = ⟨q, hq.1⟩ * ⟨t, htT⟩ := rfl
            have h2 : ψ ⟨q * t, T.mul_mem hq.1 htT⟩ = f := by
              rw [h1, map_mul, (actOn_T_eq_one_iff hs eK hTN hq.1).2 hq, one_mul]
            rw [h2]
            exact mem_zpowers f
        · calc s = (s * t⁻¹) * t := by group
            _ = (p * q) * t := by rw [hpq]
            _ = p * (q * t) := by group

theorem IsRootFour.mul_self_eq_one_of_mem {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F)
    {t : Perm (Fin 7)} (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i)
    {w : Perm (Fin 7)} (hw : w ∈ F ⊔ zpowers t) : w * w = 1 := by
  classical
  have hcomm := IsRootFour.comm_swap hdis
  have ht2 : orderOf t = 2 := ht.orderOf
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, sq] at this
  obtain ⟨f, hf, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun f hf s hs => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      exact (Commute.zpow_right (show Commute f t from hcomm f hf) m).eq) hw
  have hfq : f * q = q * f := by
    rcases mem_zpowers_two ht2 hq with h0 | h0
    · rw [h0]; simp
    · rw [h0]; exact hcomm f hf
  have hqq : q * q = 1 := by
    rcases mem_zpowers_two ht2 hq with h0 | h0
    · rw [h0]; simp
    · rw [h0]; exact htt
  calc f * q * (f * q) = f * (q * f) * q := by group
    _ = f * (f * q) * q := by rw [← hfq]
    _ = (f * f) * (q * q) := by group
    _ = 1 := by rw [hqq, hF.2.2.1 f hf]; simp

theorem Qpp_dihedral_of_z (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ2 : pRank 2 ↥(T ⊓ CxK x K) ≤ 2) (h4 : 4 < Nat.card ↥(T ⊓ CxK x K))
    {B : Subgroup G} (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G}
    (hobs : Obstr52 B b J) {U E : Subgroup G} (hU : IsFourSub (T ⊓ K) U)
    (hES : IsS (T ⊓ CxK x K) E) (hE2 : 2 ≤ pRank 2 ↥E) (hBdef : B = U ⊔ E) {z : G} (hzU : z ∈ U)
    (hz1 : z ≠ 1) (hzc : ∀ p ∈ T ⊓ K, p * z = z * p) (hb : b = z)
    {Q'' : Subgroup G} (hQQ : T ⊓ CxK x K ≤ Q'') (hQT : Q'' ≤ T)
    (hQc : ∀ p ∈ T ⊓ K, ∀ q ∈ Q'', p * q = q * p) (hPQ : (T ⊓ K) ⊓ Q'' = ⊥)
    (hdec : ∀ s ∈ T, ∃ p ∈ T ⊓ K, ∃ q ∈ Q'', s = p * q) :
    Nonempty (↥Q'' ≃* DihedralGroup 4) ∧ T ⊓ CxK x K = Q'' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hE4 : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE4.2.1
  have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hB.1.1
  have hBT : B ≤ T := hBR.trans (sup_le inf_le_left inf_le_left)
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨eJ⟩ := hobs.nonempty_A7_of_rank_four hG4 hBel
  have hEQ : E ≤ T ⊓ CxK x K := hES.1
  have hUP : U ≤ T ⊓ K := hU.1
  have hUB : U ≤ B := hBdef ▸ le_sup_left
  have hEB : E ≤ B := hBdef ▸ le_sup_right
  have hzB : z ∈ B := hUB hzU
  have hzP : z ∈ T ⊓ K := hUP hzU
  have hT2 : IsPGroup 2 ↥T := hs.T_pGroup
  have hzT : ∀ s ∈ T, s * z = z * s := by
    intro s hsT
    obtain ⟨p, hp, q, hq, rfl⟩ := hdec s hsT
    calc p * q * z = p * (q * z) := by group
      _ = p * (z * q) := by rw [← hQc z hzP q hq]
      _ = (p * z) * q := by group
      _ = (z * p) * q := by rw [hzc p hp]
      _ = z * (p * q) := by group
  have hTC : T ≤ centralizer ({b} : Set G) := fun s hs' =>
    mem_centralizer_singleton_iff.2 (by rw [hb]; exact hzT s hs')
  have hTN : T ≤ normalizer (J : Set G) := hTC.trans (hobs.centralizer_le_normalizer hG4 hBel)
  have hbC : b ∉ CxK x K := by
    intro hbC
    rw [hb] at hbC
    exact hz1 (hcd.eq_one_of_mem hzP ⟨hzP.1, hbC⟩)
  have hzE : z ∉ E := fun hzE => hz1 (hcd.eq_one_of_mem hzP (hEQ hzE))
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := hobs.exists_image_B hG4 hBel eJ hBT hTN
  set ψ := actOn eJ hTN with hψ
  have hWmem : ∀ β (hβ : β ∈ B), ψ ⟨β, hBT hβ⟩ ∈ F ⊔ zpowers t := fun β hβ => by
    rw [← hrange]
    exact ⟨⟨β, hβ⟩, rfl⟩
  have hWsurj : ∀ w ∈ F ⊔ zpowers t, ∃ β, ∃ hβ : β ∈ B, ψ ⟨β, hBT hβ⟩ = w := by
    intro w hw
    rw [← hrange] at hw
    obtain ⟨⟨β, hβ⟩, rfl⟩ := hw
    exact ⟨β, hβ, rfl⟩
  have hKnJ : ∀ m ∈ centralizer ({b} : Set G), ∀ k ∈ J, m * k * m⁻¹ ∈ J := fun m hm k hk =>
    (Subgroup.mem_normalizer_iff.1 (hobs.centralizer_le_normalizer hG4 hBel hm) k).1 hk
  have hQnorm : ∀ v ∈ T, ∀ n ∈ Q'', v * n * v⁻¹ ∈ Q'' := by
    intro v hv n hn
    obtain ⟨p, hp, q, hq, rfl⟩ := hdec v hv
    have hqnq : q * n * q⁻¹ ∈ Q'' := Q''.mul_mem (Q''.mul_mem hq hn) (Q''.inv_mem hq)
    have h1 : p * q * n * (p * q)⁻¹ = q * n * q⁻¹ := by
      have hc := hQc p hp (q * n * q⁻¹) hqnq
      calc p * q * n * (p * q)⁻¹ = p * (q * n * q⁻¹) * p⁻¹ := by group
        _ = (q * n * q⁻¹ * p) * p⁻¹ := by rw [hc]
        _ = q * n * q⁻¹ := by group
    rw [h1]
    exact hqnq
  have hQinj : ∀ q ∈ Q'', ∀ hq : q ∈ T, ψ ⟨q, hq⟩ = 1 → q = 1 := by
    intro q hqQ hqT hψ1
    by_contra hq1
    set N : Subgroup G := Q'' ⊓ CxK b J with hN
    have hqN : q ∈ N := ⟨hqQ, hTC hqT, (actOn_eq_one_iff eJ hTN hqT).1 hψ1⟩
    have hN1 : N ≠ ⊥ := fun h => hq1 (by
      have := h ▸ hqN
      simpa using this)
    have hconj : ∀ v ∈ T, ∀ n ∈ N, v * n * v⁻¹ ∈ N := fun v hv n hn =>
      ⟨hQnorm v hv n hn.1, CxK_conj_mem hKnJ (hTC hv) hn.2⟩
    have hNn : T ≤ normalizer (N : Set G) := fun v hv =>
      mem_normalizer_of_conj_mem' (hconj v hv) (fun n hn => by
        simpa using hconj v⁻¹ (T.inv_mem hv) n hn)
    have hbN := hobs.b_mem_of_normal_ker hG4 hBel hE4.2.2 (X := T) hT2 hBT (N := N)
      (fun n hn => hQT hn.1) hNn inf_le_right hN1
    rw [hb] at hbN
    have hzPQ : z ∈ (T ⊓ K) ⊓ Q'' := ⟨hzP, hbN.1⟩
    rw [hPQ] at hzPQ
    exact hz1 (by simpa using hzPQ)
  have hEinj : ∀ g ∈ E, ∀ hg : g ∈ T, ψ ⟨g, hg⟩ = 1 → g = 1 := by
    intro g hgE hgT hψ1
    have hgs : g ∈ centralizerSection J (pPrimeCoreOf 2 J) := (actOn_eq_one_iff eJ hTN hgT).1 hψ1
    rcases hobs.B_inf_ker hG4 hBel hE4.2.2 (hEB hgE) hgs with h1 | h1
    · exact h1
    · exact absurd (hb ▸ h1 ▸ hgE) hzE
  have hnoswap : ∀ g ∈ E, ∀ hg : g ∈ T, ψ ⟨g, hg⟩ ≠ t := by
    intro g hgE hgT hgt
    have hesw : (a7Act J eJ ⟨g, hTN hgT⟩).IsSwap := by
      have : a7Act J eJ ⟨g, hTN hgT⟩ = ψ ⟨g, hgT⟩ := rfl
      rw [this, hgt]
      exact ht
    exact false_of_swap_in_E_A7 hL34 h102 hG hs ⟨eK⟩ hBel hobs eJ (a := z) (q := 1) hzP.2 hzB
      (one_mem _) (one_mem _) (by rw [mul_one, hb]) hbC (hEQ hgE).2 (hEB hgE) (hTN hgT) hesw
  have hZ : ∀ q ∈ Q'', (∀ e' ∈ E, q * e' = e' * q) → q ∈ E := by
    intro q hqQ hqc
    have hqT := hQT hqQ
    have hqB' : ∀ β ∈ B, q * β = β * q := by
      intro β hβ
      have hβ' : β ∈ U ⊔ E := hBdef ▸ hβ
      obtain ⟨u, hu, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute
        (fun u hu q hq => hBc u (hUB hu) q (hEB hq)) hβ'
      calc q * (u * e') = (q * u) * e' := by group
        _ = (u * q) * e' := by rw [← hQc u (hUP hu) q hqQ]
        _ = u * (q * e') := by group
        _ = u * (e' * q) := by rw [hqc e' he']
        _ = (u * e') * q := by group
    have hqW : ψ ⟨q, hqT⟩ ∈ F ⊔ zpowers t := by
      refine centralizer_rootFour_sup_swap hF ht hdis (fun w hw => ?_)
      obtain ⟨β, hβ, rfl⟩ := hWsurj w hw
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hqB' β hβ)
    have hsq := IsRootFour.mul_self_eq_one_of_mem hF ht hdis hqW
    have hqq : q * q = 1 := by
      have h1 : ψ ⟨q * q, T.mul_mem hqT hqT⟩ = 1 := by
        have : (⟨q * q, T.mul_mem hqT hqT⟩ : ↥T) = ⟨q, hqT⟩ * ⟨q, hqT⟩ := rfl
        rw [this, map_mul]
        exact hsq
      exact hQinj (q * q) (Q''.mul_mem hqQ hqQ) (T.mul_mem hqT hqT) h1
    have hqBm : q ∈ B := mem_of_commute_rank_four hG4 hBel hE4.2.2 hqq
      (fun β hβ => (hqB' β hβ).symm)
    obtain ⟨u, hu, e'', he'', hq_eq⟩ := exists_mul_of_mem_sup_of_commute
      (fun u hu q hq => hBc u (hUB hu) q (hEB hq)) (hBdef ▸ hqBm : q ∈ U ⊔ E)
    have hu1 : u = 1 := by
      have huQ : u ∈ Q'' := by
        have : u = q * e''⁻¹ := by rw [hq_eq]; group
        rw [this]
        exact Q''.mul_mem hqQ (Q''.inv_mem (hQQ (hEQ he'')))
      have hu' : u ∈ (T ⊓ K) ⊓ Q'' := ⟨hUP hu, huQ⟩
      rw [hPQ] at hu'
      simpa using hu'
    rw [hq_eq, hu1, one_mul]
    exact he''
  have hEQ'' : E ≤ Q'' := hEQ.trans hQQ
  have hE4' : Nat.card ↥E = 4 := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hES.2.1
    have h2 : pRank 2 ↥E ≤ 2 := (C3.Layer1.Back.pRank_mono' hEQ).trans hQ2
    have h3 : pRank 2 ↥E = 2 := le_antisymm h2 hE2
    rw [h1, h3]
    norm_num
  have hVab : IsMulCommutative ↥(E.subgroupOf Q'') :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hBc a.1.1 (hEB a.2) b.1.1 (hEB b.2)))⟩⟩
  have hVexp : ∀ v ∈ E.subgroupOf Q'', v ^ 2 = 1 := fun v hv =>
    Subtype.ext (by simpa [sq] using hBsq (v : G) (hEB hv))
  have hVcard : Nat.card ↥(E.subgroupOf Q'') = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ'').toEquiv]
    exact hE4'
  have hcent : centralizer ((E.subgroupOf Q'' : Subgroup ↥Q'') : Set ↥Q'') = E.subgroupOf Q'' := by
    ext q
    constructor
    · intro hq
      rw [Subgroup.mem_subgroupOf]
      refine hZ q.1 q.2 (fun e' he' => ?_)
      have := Subgroup.mem_centralizer_iff.1 hq ⟨e', hEQ'' he'⟩ (Subgroup.mem_subgroupOf.2 he')
      exact (congrArg Subtype.val this).symm
    · intro hq
      refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
      exact Subtype.ext (hBc _ (hEB hv) _ (hEB hq))
  have hQ2grp : IsPGroup 2 ↥Q'' := hT2.to_le hQT
  let ψQ : ↥Q'' →* Perm (Fin 7) := ψ.comp (Subgroup.inclusion hQT)
  have hψQinj : Function.Injective ψQ := by
    refine (injective_iff_map_eq_one ψQ).2 fun g hg => ?_
    exact Subtype.ext (hQinj g.1 g.2 (hQT g.2) hg)
  have hexp : ∀ g : ↥Q'', g ^ 4 = 1 := by
    intro g
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ2grp) g
    have h1 : orderOf (ψQ g) = 2 ^ k := by rw [orderOf_injective ψQ hψQinj g, hk]
    have h2 := orderOf_dvd_four_of_eq_two_pow h1
    rw [orderOf_injective ψQ hψQinj g] at h2
    exact orderOf_dvd_iff_pow_eq_one.1 h2
  have hQge : 4 < Nat.card ↥Q'' := lt_of_lt_of_le h4 (Subgroup.card_le_of_le hQQ)
  have hD8 : Nonempty (↥Q'' ≃* DihedralGroup 4) := by
    rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hQ2grp _ hVab hVexp hVcard hcent with
      ⟨n, hn2, ⟨e⟩⟩ | ⟨n, hn4, ⟨e⟩⟩
    · have hcard : Nat.card ↥Q'' = 2 * 2 ^ (n - 1) := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hn3 : n ≤ 3 := by
        by_contra hcon
        push Not at hcon
        have h1 := hexp (e.symm (DihedralGroup.r 1))
        have ho : orderOf (e.symm (DihedralGroup.r 1)) = 2 ^ (n - 1) := by
          rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
        have hdvd := orderOf_dvd_of_pow_eq_one h1
        rw [ho] at hdvd
        have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      have hn : n = 3 := by
        by_contra hne
        have h2 : n = 2 := by omega
        subst h2
        rw [hcard] at hQge
        norm_num at hQge
      subst hn
      exact ⟨e⟩
    · exfalso
      obtain ⟨x8, hx8⟩ := CFSG.ABGDGroups.semidihedral_exists_orderOf_eq_eight hn4
      have h1 := hexp (e.symm x8)
      have ho : orderOf (e.symm x8) = 8 := by rw [MulEquiv.orderOf_eq, hx8]
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rw [ho] at hdvd
      exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  refine ⟨hD8, ?_⟩
  obtain ⟨e8⟩ := hD8
  have hcard8 : Nat.card ↥Q'' = 8 := by
    rw [Nat.card_congr e8.toEquiv, DihedralGroup.nat_card]
  have hQdvd : Nat.card ↥(T ⊓ CxK x K) ∣ 2 ^ 3 := by
    have h8 : (2 : ℕ) ^ 3 = Nat.card ↥Q'' := by rw [hcard8]; norm_num
    rw [h8]
    exact Subgroup.card_dvd_of_le hQQ
  have hQ8 : Nat.card ↥(T ⊓ CxK x K) = 8 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hQdvd
    have : i = 3 := by
      by_contra hne
      have : i ≤ 2 := by omega
      have : 2 ^ i ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      omega
    rw [hi', this]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge hQQ (by rw [hcard8, hQ8])

end CFSG.GH74.GLS.Th2.Obs
