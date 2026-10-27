module

public import CFSG.Literature.Janko67Setting
public import CFSG.LargeExtraspecial.AS62Conf2
public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.Literature.Janko67

open CFSG CFSG.RankThree.GF2n.Parrott CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial


theorem isSimpleGroup {G : Type} [Group G] [Finite G] (S : Setting G) (f : S.M ≃* C0)
    (hf : f S.zM = tC) {H : Subgroup G} (hc : AS62.ConfHyp S H) : IsSimpleGroup G := by
  classical
  obtain ⟨P, hP_eq, hP_center⟩ := exists_sylow_eq_map_P0 S f hf
  have hP_card : Nat.card ↥(P : Subgroup G) = 64 := card_sylow_two S f hf P
  have hP_le_M : (P : Subgroup G) ≤ S.M :=
    hP_eq ▸ Subgroup.map_subtype_le (P0.map (f.symm : C0 →* S.M))
  have hzP : S.z ∈ (P : Subgroup G) := by
    have : Nontrivial ↥(P : Subgroup G) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hP_card]; norm_num)
    obtain ⟨c, hc_ne⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (P.isPGroup'.bot_lt_center).ne'
    have hcomm : ∀ d ∈ (P : Subgroup G), ((c : ↥(P : Subgroup G)) : G) * d =
        d * ((c : ↥(P : Subgroup G)) : G) := by
      intro d hd
      have h := Subgroup.mem_center_iff.mp c.2 (⟨d, hd⟩ : ↥(P : Subgroup G))
      exact (congrArg Subtype.val h).symm
    have hc1 : (c : ↥(P : Subgroup G)) ≠ 1 := fun h => hc_ne (Subtype.ext h)
    have hz : ((c : ↥(P : Subgroup G)) : G) = S.z :=
      (hP_center _ (c : ↥(P : Subgroup G)).2 hcomm).resolve_left
        (fun h => hc1 (Subtype.ext h))
    rw [← hz]
    exact (c : ↥(P : Subgroup G)).2
  have : Nontrivial G := ⟨1, S.z, fun h => S.z_ne_one h.symm⟩
  apply IsSimpleGroup.mk
  intro N hN
  have : N.Normal := hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  let NM : Subgroup S.M := (N ⊓ S.M).subgroupOf S.M
  let fN : Subgroup C0 := NM.map (f : S.M →* C0)
  have hNMdef : NM = N.subgroupOf S.M := Subgroup.inf_subgroupOf_right N S.M
  have hNMnormal : NM.Normal := by
    rw [hNMdef]
    exact hN.subgroupOf S.M
  have hfNnormal : fN.Normal := hNMnormal.map (f : S.M →* C0) f.surjective
  have : fN.Normal := hfNnormal
  have hcardfN : Nat.card fN = Nat.card ↥(N ⊓ S.M) := by
    show Nat.card (NM.map (f : S.M →* C0)) = Nat.card ↥(N ⊓ S.M)
    rw [Subgroup.card_map_of_injective f.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ S.M ≤ S.M)).toEquiv]
  have hpCore_le_P0 : CFSG.pCore 2 C0 ≤ P0 := by
    rw [pCore_C0_eq, P0]
    exact Subgroup.closure_mono (by intro x hx; simp_all)
  have hNodd : Odd (Nat.card N) → N = ⊥ := by
    intro hodd
    have hfNodd : Odd (Nat.card fN) := by
      rw [hcardfN]
      exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : N ⊓ S.M ≤ N))
    have hfNbot : fN = ⊥ := eq_bot_of_normal_of_odd_card_C0 fN hfNodd
    have hNMbot : NM = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective NM f.injective).mp (by
        show fN = ⊥
        exact hfNbot)
    have hIntBot : N ⊓ S.M = ⊥ := by
      have h1 : NM.map S.M.subtype = N ⊓ S.M :=
        Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ S.M ≤ S.M)
      rw [← h1, hNMbot, Subgroup.map_bot]
    have hCz : ∀ n ∈ N, n * S.z = S.z * n → n = 1 := by
      intro n hn hcomm
      have hnM : n ∈ S.M := S.mem_M_iff.mpr hcomm
      have : n ∈ N ⊓ S.M := ⟨hn, hnM⟩
      rw [hIntBot] at this
      exact Subgroup.mem_bot.mp this
    have hCpoint : ∀ q ∈ S.zConj H, q ≠ S.z → ∀ n ∈ N, n * q = q * n → n = 1 := by
      rintro q ⟨k, -, rfl⟩ - n hn hcomm
      have h1 : k⁻¹ * n * k = 1 := by
        apply hCz (k⁻¹ * n * k) (by simpa using hN.conj_mem n hn k⁻¹)
        calc (k⁻¹ * n * k) * S.z = k⁻¹ * (n * (k * S.z * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * S.z * k⁻¹) * n) * k := by rw [hcomm]
          _ = S.z * (k⁻¹ * n * k) := by group
      calc n = k * (k⁻¹ * n * k) * k⁻¹ := by group
        _ = k * 1 * k⁻¹ := by rw [h1]
        _ = 1 := by group
    have hC : ∀ q ∈ S.zConj H, ∀ n ∈ N, q * n = n * q → n = 1 := by
      intro q hq n hn hcomm
      rcases eq_or_ne q S.z with rfl | hqz
      · exact hCz n hn hcomm.symm
      · exact hCpoint q hq hqz n hn hcomm.symm
    obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
    obtain ⟨L, -⟩ := hc.exists_label hp hpz
    have hnorm : ∀ i : Fin 5, L.zz i ∈ Subgroup.normalizer (N : Set G) := by
      intro i
      rw [Subgroup.normalizer_eq_top_iff.mpr hN]
      exact Subgroup.mem_top _
    have hinv : ∀ i : Fin 5, ∀ n ∈ N, L.zz i * n * (L.zz i)⁻¹ = n⁻¹ := by
      intro i n hn
      exact CFSG.LargeExtraspecial.S4.conj_eq_inv_of_centralizer (L.zz_mul_self i) (hnorm i)
        (fun m hm hmc => hC (L.zz i) (L.zz_mem i) m hm hmc) hn
    have hfix2 : ∀ (a b : G), (∀ n ∈ N, a * n * a⁻¹ = n⁻¹) →
        (∀ n ∈ N, b * n * b⁻¹ = n⁻¹) → ∀ n ∈ N, (a * b) * n * (a * b)⁻¹ = n := by
      intro a b ha hb n hn
      calc (a * b) * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * n⁻¹ * a⁻¹ := by rw [hb n hn]
        _ = (n⁻¹)⁻¹ := ha n⁻¹ (N.inv_mem hn)
        _ = n := inv_inv n
    have hfix_inv : ∀ (a b : G), (∀ n ∈ N, a * n * a⁻¹ = n) →
        (∀ n ∈ N, b * n * b⁻¹ = n⁻¹) → ∀ n ∈ N, (a * b) * n * (a * b)⁻¹ = n⁻¹ := by
      intro a b ha hb n hn
      calc (a * b) * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
        _ = a * n⁻¹ * a⁻¹ := by rw [hb n hn]
        _ = n⁻¹ := ha n⁻¹ (N.inv_mem hn)
    have h01 : ∀ n ∈ N, (L.zz 0 * L.zz 1) * n * (L.zz 0 * L.zz 1)⁻¹ = n :=
      hfix2 _ _ (hinv 0) (hinv 1)
    have h012 : ∀ n ∈ N, (L.zz 0 * L.zz 1 * L.zz 2) * n * (L.zz 0 * L.zz 1 * L.zz 2)⁻¹ = n⁻¹ :=
      hfix_inv _ _ h01 (hinv 2)
    have h0123 : ∀ n ∈ N, (L.zz 0 * L.zz 1 * L.zz 2 * L.zz 3) * n *
        (L.zz 0 * L.zz 1 * L.zz 2 * L.zz 3)⁻¹ = n :=
      hfix2 _ _ h012 (hinv 3)
    have h01234 : ∀ n ∈ N, (L.zz 0 * L.zz 1 * L.zz 2 * L.zz 3 * L.zz 4) * n *
        (L.zz 0 * L.zz 1 * L.zz 2 * L.zz 3 * L.zz 4)⁻¹ = n⁻¹ :=
      hfix_inv _ _ h0123 (hinv 4)
    have hself : ∀ n ∈ N, n = n⁻¹ := by
      intro n hn
      have h := h01234 n hn
      rw [L.prod_zz hc, one_mul, inv_one, mul_one] at h
      exact h
    have hNbot' : N = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro n hn
      have h2 : n * n = 1 := by
        calc n * n = n * n⁻¹ := by nth_rewrite 2 [hself n hn]; rfl
          _ = 1 := mul_inv_cancel n
      have hord : Odd (orderOf n) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hn)
      have hdvd : orderOf n ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        simpa [pow_two] using h2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        obtain ⟨m, hm⟩ := hord
        omega
    exact hNbot'
  have hNeven : Even (Nat.card N) := Nat.not_odd_iff_even.mp (fun h => hNbot (hNodd h))
  have h2dvdN : 2 ∣ Nat.card N := even_iff_two_dvd.mp hNeven
  have hzN : S.z ∈ N := by
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (N ⊓ (P : Subgroup G)) N := by
      have hPG : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup G) (⊤ : Subgroup G) := by
        rw [CFSG.ABGLocalTools.isSylowOf_iff]
        refine ⟨le_top, P.isPGroup', ?_⟩
        rw [Subgroup.relIndex_top_right]
        exact P.not_dvd_index
      have hnorm : (⊤ : Subgroup G) ≤ Subgroup.normalizer (N : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hN]
      have h := hPG.inf_of_le_normalizer (N := N) le_top hnorm
      rwa [inf_comm] at h
    have hfac : 0 < (Nat.card N).factorization 2 :=
      Nat.prime_two.factorization_pos_of_dvd Nat.card_pos.ne' h2dvdN
    have hcardS : Nat.card ↥(N ⊓ (P : Subgroup G)) = 2 ^ (Nat.card N).factorization 2 :=
      hSyl.card_eq
    have hgt : 1 < Nat.card ↥(N ⊓ (P : Subgroup G)) := by
      rw [hcardS]
      exact one_lt_pow' (by norm_num) hfac.ne'
    have hKnormal : ((N ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)).Normal := by
      rw [Subgroup.inf_subgroupOf_right N (P : Subgroup G)]
      exact hN.subgroupOf (P : Subgroup G)
    have : ((N ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)).Normal := hKnormal
    have hKne : ((N ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)) ≠ ⊥ := by
      rw [← Subgroup.nontrivial_iff_ne_bot]
      have hcardK : Nat.card ↥((N ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)) =
          Nat.card ↥(N ⊓ (P : Subgroup G)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : N ⊓ (P : Subgroup G) ≤ (P : Subgroup G))).toEquiv
      exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardK]; exact hgt)
    have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
    have hcenter_ne : ((N ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G)) ⊓
        Subgroup.center ↥(P : Subgroup G) ≠ ⊥ :=
      Group.IsNilpotent.inf_center_ne_bot_of_normal hKne
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
    have hxK : x.1 ∈ (N ⊓ (P : Subgroup G)).subgroupOf (P : Subgroup G) :=
      (Subgroup.mem_inf.mp x.2).1
    have hxcenter : x.1 ∈ Subgroup.center ↥(P : Subgroup G) := (Subgroup.mem_inf.mp x.2).2
    have hcomm : ∀ d ∈ (P : Subgroup G), (x.1 : G) * d = d * (x.1 : G) := by
      intro d hd
      have h := Subgroup.mem_center_iff.mp hxcenter (⟨d, hd⟩ : ↥(P : Subgroup G))
      exact (congrArg Subtype.val h).symm
    have hxN : (x.1 : G) ∈ N := (Subgroup.mem_subgroupOf.mp hxK).1
    have hxne : (x.1 : G) ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
    have hzx : (x.1 : G) = S.z := (hP_center _ x.1.2 hcomm).resolve_left hxne
    rw [← hzx]
    exact hxN
  have hP0_le_fN : P0 ≤ fN := by
    obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
    have hpM : p ∈ S.M := hc.mem_M_of_mem hp
    have hpN : p ∈ N := by
      obtain ⟨k, -, rfl⟩ := hp
      exact hN.conj_mem S.z hzN k
    have hmem : f ⟨p, hpM⟩ ∈ fN :=
      Subgroup.mem_map_of_mem (f : S.M →* C0)
        (Subgroup.mem_subgroupOf.mpr (show ((⟨p, hpM⟩ : S.M) : G) ∈ N ⊓ S.M from ⟨hpN, hpM⟩))
    have hp1 : p ≠ 1 := by
      obtain ⟨k, -, rfl⟩ := hp
      intro h
      have hz1 : S.z = 1 := by
        calc S.z = k⁻¹ * (k * S.z * k⁻¹) * k := by group
          _ = 1 := by rw [h]; group
      exact S.z_ne_one hz1
    have hp2 : p * p = 1 := AS62.zConj_mul_self S hp
    have horder : orderOf (⟨p, hpM⟩ : S.M) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rwa [pow_two]) hp1
    have hy2 : orderOf (f ⟨p, hpM⟩) = 2 :=
      (orderOf_injective (f : S.M →* C0) f.injective _).trans horder
    have hyQ : f ⟨p, hpM⟩ ∉ CFSG.pCore 2 C0 := by
      intro hy
      rw [← map_Q_eq S f] at hy
      obtain ⟨q, hq, hfq⟩ := Subgroup.mem_map.mp hy
      have hqeq : q = ⟨p, hpM⟩ := f.injective hfq
      have hqG : (q : G) ∈ S.QG := ⟨q, hq, rfl⟩
      rw [hqeq] at hqG
      exact hc.not_mem_QG hp hpz (by simpa using hqG)
    rcases isConj_uC_or_of_not_mem_pCore hy2 hyQ with h | h
    · have hu : uC ∈ fN := by
        obtain ⟨g, hg⟩ := isConj_iff.mp h
        rw [← hg]
        exact hfNnormal.conj_mem (f ⟨p, hpM⟩) hmem g
      exact P0_le_of_uC_mem (K := fN) hu
    · have hu : uC * tC ∈ fN := by
        obtain ⟨g, hg⟩ := isConj_iff.mp h
        rw [← hg]
        exact hfNnormal.conj_mem (f ⟨p, hpM⟩) hmem g
      exact P0_le_of_uC_mul_tC_mem (K := fN) hu
  have hQG_le_N : S.QG ≤ N := by
    intro q hq
    have hqM : q ∈ S.M := S.QG_le_M hq
    have hqQ : (⟨q, hqM⟩ : S.M) ∈ S.Q := by
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
      have hx' : x = ⟨q, hqM⟩ := Subtype.ext hxq
      rwa [hx'] at hx
    have hfqQ : f ⟨q, hqM⟩ ∈ CFSG.pCore 2 C0 := by
      rw [← map_Q_eq S f]
      exact Subgroup.mem_map_of_mem (f : S.M →* C0) hqQ
    have hfqN : f ⟨q, hqM⟩ ∈ fN := hP0_le_fN (hpCore_le_P0 hfqQ)
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hfqN
    have hxeq : x = ⟨q, hqM⟩ := f.injective hfx
    have hxint : (x : G) ∈ N ⊓ S.M := Subgroup.mem_subgroupOf.mp hx
    rw [hxeq] at hxint
    exact hxint.1
  have hH_le_N : H ≤ N := by
    obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
    obtain ⟨k, -, hkH, -⟩ := hc.exists_conj_eq hp hpz
    have hQa_le : S.Qa k ≤ N := by
      rw [S.Qa_eq_map]
      rintro _ ⟨x, hx, rfl⟩
      exact hN.conj_mem x (hQG_le_N hx) k
    rw [← hkH]
    exact sup_le hQG_le_N hQa_le
  have hcard_cases : Nat.card fN = 64 ∨ Nat.card fN = 192 ∨ Nat.card fN = 576 := by
    have hdvd : Nat.card P0 ∣ Nat.card fN := Subgroup.card_dvd_of_le hP0_le_fN
    rw [card_P0] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hindex : Nat.card fN * fN.index = Nat.card C0 := Subgroup.card_mul_index fN
    rw [hm, qp45_card_centralizer_t] at hindex
    have hmn : m * fN.index = 9 := by
      have h' : 64 * (m * fN.index) = 64 * 9 := by
        rw [← Nat.mul_assoc, hindex]
      exact Nat.mul_left_cancel (by norm_num) h'
    have hle : m ≤ 9 := Nat.le_of_dvd (by norm_num) ⟨fN.index, hmn.symm⟩
    have hm_cases : m = 1 ∨ m = 3 ∨ m = 9 := by
      interval_cases m <;> omega
    rcases hm_cases with rfl | rfl | rfl
    · left; rw [hm]
    · right; left; rw [hm]
    · right; right; rw [hm]
  rcases hcard_cases with h64 | h192 | h576
  ·
    have hfN2 : IsPGroup 2 fN := IsPGroup.of_card (n := 6) (by rw [h64]; norm_num)
    have hpCore : fN ≤ CFSG.pCore 2 C0 :=
      le_sSup (show fN ∈ {K : Subgroup C0 | K.Normal ∧ IsPGroup 2 K} from ⟨hfNnormal, hfN2⟩)
    have hle := Subgroup.card_le_of_le hpCore
    rw [h64, card_pCore_C0] at hle
    exact absurd hle (by norm_num)
  ·
    have hcardInt : Nat.card ↥(N ⊓ S.M) = 192 := by rw [← hcardfN, h192]
    have hHM_eq : H ⊓ S.M = N ⊓ S.M := by
      refine Subgroup.eq_of_le_of_card_ge (inf_le_inf_right S.M hH_le_N) ?_
      rw [hcardInt, hc.card_inf_M]
    set V : Subgroup G := Subgroup.closure (S.zConj H) with hVdef
    have hV_le_HM : V ≤ H ⊓ S.M := le_inf hc.V_le hc.V_le_M
    have hV_le_K : V ≤ N ⊓ S.M := hHM_eq ▸ hV_le_HM
    have hVnormK : (V.subgroupOf (N ⊓ S.M)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hV_le_K]
      intro x k hx hk
      rw [← hHM_eq] at hk
      rw [hVdef] at hx
      exact Asc77.conj_mem_closure_conjIn hk.1 hx
    have hV2 : IsPGroup 2 (V.subgroupOf (N ⊓ S.M)) := by
      refine IsPGroup.of_card (n := 4) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_K).toEquiv, hVdef, hc.card_V]
      norm_num
    have hVsub_le : V.subgroupOf (N ⊓ S.M) ≤ CFSG.pCore 2 ↥(N ⊓ S.M) :=
      le_sSup (show V.subgroupOf (N ⊓ S.M) ∈
          {K : Subgroup ↥(N ⊓ S.M) | K.Normal ∧ IsPGroup 2 K} from ⟨hVnormK, hV2⟩)
    have hV_le_O : V ≤ CFSG.Open.pCoreOf 2 (N ⊓ S.M) := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hV_le_K]
      exact Subgroup.map_mono hVsub_le
    have hK_le_SM : N ⊓ S.M ≤ S.M := inf_le_right
    have hSM_le_norm : S.M ≤ Subgroup.normalizer ((N ⊓ S.M : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_SM).mp hNMnormal
    have hOSM : CFSG.Open.pCoreOf 2 S.M = S.QG := by
      rw [CFSG.Open.pCoreOf, ← S.Q_eq_pCore]
      rfl
    have hV_le_QG : V ≤ S.QG :=
      hV_le_O.trans
        ((CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hK_le_SM hSM_le_norm).trans
          (le_of_eq hOSM))
    obtain ⟨p, hp, hpz⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc.ncard_zConj]; norm_num) S.z
    have hcq : S.QG ⊓ Subgroup.centralizer ({p} : Set G) = V := by
      rw [hc.cqx_eq hp hpz, ← hVdef, inf_eq_left.mpr hV_le_QG]
    have hcard8 := hc.card_cqx hp hpz
    rw [hcq, hVdef, hc.card_V] at hcard8
    exact absurd hcard8 (by norm_num)
  ·
    have hfN_top : fN = ⊤ := by
      refine Subgroup.eq_top_of_card_eq fN ?_
      rw [h576, qp45_card_centralizer_t]
    have hSM_le_N : S.M ≤ N := by
      intro m hm
      have hmf : f ⟨m, hm⟩ ∈ fN := by rw [hfN_top]; exact Subgroup.mem_top _
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hmf
      have hxeq : x = ⟨m, hm⟩ := f.injective hfx
      have hxint : (x : G) ∈ N ⊓ S.M := Subgroup.mem_subgroupOf.mp hx
      rw [hxeq] at hxint
      exact hxint.1
    have hP_le_N : (P : Subgroup G) ≤ N := by
      rw [hP_eq]
      exact (Subgroup.map_subtype_le (P0.map (f.symm : C0 →* S.M))).trans hSM_le_N
    have hsup : Subgroup.normalizer (P : Set G) ⊔ N = ⊤ :=
      Sylow.normalizer_sup_eq_top' P hP_le_N
    have hnorm_le_N : Subgroup.normalizer (P : Set G) ≤ N := by
      intro g hg
      apply hSM_le_N
      refine S.mem_M_iff.mpr ?_
      have hmemP : g * S.z * g⁻¹ ∈ (P : Subgroup G) :=
        (Subgroup.mem_normalizer_iff.mp hg S.z).mp hzP
      have hcent : ∀ d ∈ (P : Subgroup G),
          (g * S.z * g⁻¹) * d = d * (g * S.z * g⁻¹) := by
        intro d hd
        have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set G) := Subgroup.inv_mem _ hg
        have hd' : g⁻¹ * d * g ∈ (P : Subgroup G) := by
          simpa using (Subgroup.mem_normalizer_iff.mp hg' d).mp hd
        have hcomm' : (g⁻¹ * d * g) * S.z = S.z * (g⁻¹ * d * g) :=
          S.z_comm (hP_le_M hd')
        calc (g * S.z * g⁻¹) * d = g * (S.z * (g⁻¹ * d * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * d * g) * S.z) * g⁻¹ := by rw [← hcomm']
          _ = d * (g * S.z * g⁻¹) := by group
      have hz : g * S.z * g⁻¹ = S.z :=
        (hP_center _ hmemP hcent).resolve_left (fun h1 => by
          have h2 : S.z = 1 := by
            calc S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
              _ = 1 := by rw [h1]; group
          exact S.z_ne_one h2)
      calc g * S.z = (g * S.z * g⁻¹) * g := by group
        _ = S.z * g := by rw [hz]
    have htop_le : (⊤ : Subgroup G) ≤ N := by
      rw [← hsup]
      exact sup_le hnorm_le_N le_rfl
    exact top_le_iff.mp htop_le

end CFSG.Literature.Janko67
