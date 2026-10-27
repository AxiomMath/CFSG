module

public import CFSG.CGT.Stroth76.Lemma7One
public import CFSG.CGT.Stroth76.Lemma7Two
public import CFSG.CGT.Stroth76.SylowCw

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

variable {G : Type*} [Group G] [Finite G] {K : Config G}

theorem sElt_one2 (D : IdxTwo K) : D.sElt one2 = 1 := by
  rw [one2, D.sElt_zero_fst, tElt_zero]

theorem sElt_mul_self (D : IdxTwo K) (hD : ∀ a b, D.smul a b = sm2 a b) (r : Sc) :
    D.sElt r * D.sElt r = D.sElt (sm2 r r) := by rw [← hD, D.sElt_mul]

theorem orderOf_sElt_of_isInv2 (D : IdxTwo K) (hD : ∀ a b, D.smul a b = sm2 a b) {r : Sc}
    (h : isInv2 r = true) : orderOf (D.sElt r) = 2 := by
  simp only [isInv2, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, sElt_mul_self D hD, h.1, sElt_one2]
  · intro h1
    exact h.2 (D.sElt_injective (h1.trans (sElt_one2 D).symm))

theorem isInv2_of_sElt (D : IdxTwo K) (hD : ∀ a b, D.smul a b = sm2 a b) {r : Sc}
    (h2 : D.sElt r * D.sElt r = 1) (h1 : D.sElt r ≠ 1) : isInv2 r = true := by
  simp only [isInv2, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  refine ⟨D.sElt_injective ?_, fun h => h1 (by rw [h, sElt_one2])⟩
  rw [← sElt_mul_self D hD, h2, sElt_one2]

theorem exists_conj_target [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) [Fact (Nat.Prime 2)]
    (S : Sylow 2 G) (D : IdxTwo K) (hD : ∀ a b, D.smul a b = sm2 a b)
    (hSD : (S : Subgroup G) = D.Ssub) (χ : Sc → ZMod 2) (hχ : ∀ a b, χ (sm2 a b) = χ a + χ b)
    [DecidablePred (fun r => χ r = 0)] (hcard : Fintype.card {r : Sc // χ r = 0} = 2 ^ 8)
    {tab : List (Sc × Sc × Sc)} {targets : List Sc} (hchk : checkTab tab targets = true)
    (hcompl : ∀ r : Sc, χ r = 0 → isInv2 r = true → tab.any (·.1 == r) = true)
    {r₀ : Sc} (hr₀ : χ r₀ ≠ 0) (hinv : isInv2 r₀ = true) :
    ∃ tg ∈ targets, IsConj (D.sElt r₀) (D.sElt tg) := by
  set U := charSub D hD χ hχ
  have hUS : U ≤ (S : Subgroup G) := hSD ▸ charSub_le D hD χ hχ
  have hidx : U.relIndex (S : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := U) (K := (S : Subgroup G))
    have hS : Nat.card (S : Subgroup G) = 2 ^ 9 := by rw [hSD]; exact D.card_Ssub
    rw [inf_of_le_left hUS, card_charSub, hcard, hS] at h
    omega
  have hr₀S : D.sElt r₀ ∈ (S : Subgroup G) := hSD ▸ D.sElt_mem r₀
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.exists_conj_mem_complement hnonab S.isPGroup'
    S.not_dvd_index hUS hidx hr₀S (not_mem_charSub D hD χ hχ hr₀)
    (orderOf_sElt_of_isInv2 D hD hinv)
  obtain ⟨r, hr, hre⟩ := hg
  have hinvr : isInv2 r = true := by
    simp only [isInv2, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hinv
    refine isInv2_of_sElt D hD ?_ ?_
    · rw [hre]
      calc g⁻¹ * D.sElt r₀ * g * (g⁻¹ * D.sElt r₀ * g) = g⁻¹ * (D.sElt r₀ * D.sElt r₀) * g := by
            group
        _ = 1 := by rw [sElt_mul_self D hD, hinv.1, sElt_one2]; group
    · rw [hre]
      intro h
      apply hinv.2
      apply D.sElt_injective
      rw [sElt_one2]
      calc D.sElt r₀ = g * (g⁻¹ * D.sElt r₀ * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
  obtain ⟨e, he, he1⟩ := List.any_eq_true.1 (hcompl r hr hinvr)
  rw [beq_iff_eq] at he1
  obtain ⟨hc, htg⟩ := isConj_of_mem_tab D hD hchk he
  refine ⟨e.2.2, htg, ?_⟩
  rw [he1] at hc
  refine IsConj.trans ?_ hc
  rw [hre]
  exact isConj_iff.2 ⟨g⁻¹, by group⟩

section Names

variable (K)

theorem tElt_z2 : tElt K ((0, 2, 2), (0, 0, 0)) = (K.x * K.y) ^ 2 := by
  rw [show ((0, 2, 2), (0, 0, 0)) = (((0, 2, 2), 0) : Tc) from rfl, tElt_ev, ev_022, K.xy_sq]
theorem tElt_x2 : tElt K ((0, 2, 0), (0, 0, 0)) = K.x ^ 2 := by
  rw [show ((0, 2, 0), (0, 0, 0)) = (((0, 2, 0), 0) : Tc) from rfl, tElt_ev, ev_020]
theorem tElt_y2 : tElt K ((0, 0, 2), (0, 0, 0)) = K.y ^ 2 := by
  rw [show ((0, 0, 2), (0, 0, 0)) = (((0, 0, 2), 0) : Tc) from rfl, tElt_ev, ev_002]
theorem tElt_wxuv : tElt K ((1, 1, 0), (1, 0, 0)) = K.w * K.x * K.uv := by
  rw [show ((1, 1, 0), (1, 0, 0)) = tmul (tmul ((1, 0, 0), 0) ((0, 1, 0), 0)) (0, (1, 0, 0))
    from rfl, tElt_mul, tElt_mul, tElt_w, tElt_x, tElt_gen_uv]
theorem tElt_t' : tElt K ((0, 0, 0), (0, 1, 0)) = K.t := tElt_gen_t K
theorem tElt_u' : tElt K ((0, 0, 0), (0, 0, 1)) = K.u := tElt_gen_u K
theorem tElt_w' : tElt K ((1, 0, 0), (0, 0, 0)) = K.w := tElt_w K
theorem tElt_one' : tElt K ((0, 0, 0), (0, 0, 0)) = 1 := tElt_zero K
theorem tElt_xyuv'' : tElt K ((0, 1, 1), (1, 0, 0)) = K.x * K.y * K.uv := tElt_xyuvC K
theorem tElt_wu' : tElt K ((1, 0, 0), (0, 0, 1)) = K.w * K.u := tElt_wu K

end Names

theorem sq_wxuv_c : sm2 (0, ((1, 1, 0), (1, 0, 0))) (0, ((1, 1, 0), (1, 0, 0))) = one2 := by
  decide
theorem sq_wu_c : sm2 (0, ((1, 0, 0), (0, 0, 1))) (0, ((1, 0, 0), (0, 0, 1))) = one2 := by decide
theorem ne_wxuv_c : ((0, ((1, 1, 0), (1, 0, 0))) : Sc) ≠ one2 := by decide
theorem ne_wu_c : ((0, ((1, 0, 0), (0, 0, 1))) : Sc) ≠ one2 := by decide

theorem chi1_wxuv : chi1 (0, ((1, 1, 0), (1, 0, 0))) ≠ 0 := by decide
theorem isInv2_wxuv : isInv2 (0, ((1, 1, 0), (1, 0, 0))) = true := by decide
theorem chi3_wc2 : chi3 wc2 ≠ 0 := by decide
theorem chi4_wc2 : chi4 wc2 ≠ 0 := by decide
theorem isInv2_wc2 : isInv2 wc2 = true := by decide

theorem ne_x2c : (((0, 2, 0), (0, 0, 0)) : Tc) ≠ (0, 0) := by decide
theorem ne_tc : ((0, (0, 1, 0)) : Tc) ≠ (0, 0) := by decide
theorem ne_uvc : ((0, (1, 0, 0)) : Tc) ≠ (0, 0) := by decide

theorem x2_mem_E : K.x ^ 2 ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) :=
  Subgroup.subset_closure (by simp)
theorem y2_mem_E : K.y ^ 2 ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) :=
  Subgroup.subset_closure (by simp)
theorem t_mem_E : K.t ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) :=
  Subgroup.subset_closure (by simp)
theorem uv_mem_E : K.uv ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem mem_normalizer_A_of_sq_char {Q : Subgroup G} (hAQ : K.A ≤ Q)
    (hsq : ∀ q ∈ Q, q * q ∈ K.A)
    (hchar : ∀ q ∈ Q, (∀ r ∈ Q, q * (r * r) = (r * r) * q) → q ∈ K.A)
    {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (K.A : Set G) := by
  have hQ : ∀ q, q ∈ Q ↔ g * q * g⁻¹ ∈ Q := fun q => Subgroup.mem_normalizer_iff.1 hg q
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have hq := (hQ a).1 (hAQ ha)
    refine hchar _ hq (fun r hr => ?_)
    have hs : g⁻¹ * r * g ∈ Q := by
      have := (hQ (g⁻¹ * r * g)).2
      simpa [mul_assoc] using this (by simpa [mul_assoc] using hr)
    have hcomm := K.comm ha (hsq _ hs)
    calc g * a * g⁻¹ * (r * r) = g * (a * ((g⁻¹ * r * g) * (g⁻¹ * r * g))) * g⁻¹ := by group
      _ = g * (((g⁻¹ * r * g) * (g⁻¹ * r * g)) * a) * g⁻¹ := by rw [hcomm]
      _ = r * r * (g * a * g⁻¹) := by group
  · intro ha
    have hq : a ∈ Q := (hQ a).2 (hAQ ha)
    refine hchar a hq (fun r hr => ?_)
    have hs : g * r * g⁻¹ ∈ Q := (hQ r).1 hr
    have hcomm := K.comm ha (hsq _ hs)
    have h2 : g * (a * (r * r)) * g⁻¹ = g * ((r * r) * a) * g⁻¹ := by
      calc g * (a * (r * r)) * g⁻¹ = g * a * g⁻¹ * ((g * r * g⁻¹) * (g * r * g⁻¹)) := by group
        _ = ((g * r * g⁻¹) * (g * r * g⁻¹)) * (g * a * g⁻¹) := by rw [hcomm]
        _ = g * ((r * r) * a) * g⁻¹ := by group
    simpa using h2

theorem comm_T_facts :
    tmul ((0, 2, 0), 0) ((1, 1, 0), (1, 0, 0)) = tmul ((1, 1, 0), (1, 0, 0)) ((0, 2, 0), 0) ∧
    tmul ((0, 0, 2), 0) ((1, 1, 0), (1, 0, 0)) = tmul ((1, 1, 0), (1, 0, 0)) ((0, 0, 2), 0) ∧
    tmul (0, (0, 1, 0)) ((1, 1, 0), (1, 0, 0)) = tmul ((1, 1, 0), (1, 0, 0)) (0, (0, 1, 0)) ∧
    tmul ((0, 2, 0), 0) (0, (0, 1, 0)) = tmul (0, (0, 1, 0)) ((0, 2, 0), 0) ∧
    tmul ((0, 0, 2), 0) (0, (0, 1, 0)) = tmul (0, (0, 1, 0)) ((0, 0, 2), 0) := by decide

theorem e8_i1 : tmul ((0, 2, 0), 0) ((0, 2, 0), 0) = (0, 0) := by decide
theorem e8_i2 : tmul ((0, 0, 2), 0) ((0, 0, 2), 0) = (0, 0) := by decide
theorem e8_i3 : tmul (0, (0, 1, 0)) (0, (0, 1, 0)) = (0, 0) := by decide
theorem e8_n1 : (((0, 2, 0), 0) : Tc) ≠ ((0, 0, 2), 0) := by decide
theorem e8_n2 : ((0, (0, 1, 0)) : Tc) ≠ ((0, 2, 0), 0) := by decide
theorem e8_n3 : ((0, (0, 1, 0)) : Tc) ≠ ((0, 0, 2), 0) := by decide
theorem e8_n4 : ((0, (0, 1, 0)) : Tc) ≠ tmul ((0, 2, 0), 0) ((0, 0, 2), 0) := by decide
theorem e8_j1 :
    tmul (tmul ((0, 2, 0), 0) ((0, 0, 2), 0)) (tmul ((0, 2, 0), 0) ((0, 0, 2), 0)) = (0, 0) := by
  decide
theorem e8_j2 :
    tmul (tmul ((0, 2, 0), 0) (0, (0, 1, 0))) (tmul ((0, 2, 0), 0) (0, (0, 1, 0))) = (0, 0) := by
  decide
theorem e8_j3 :
    tmul (tmul ((0, 0, 2), 0) (0, (0, 1, 0))) (tmul ((0, 0, 2), 0) (0, (0, 1, 0))) = (0, 0) := by
  decide
theorem e8_j4 : tmul (tmul (tmul ((0, 2, 0), 0) ((0, 0, 2), 0)) (0, (0, 1, 0)))
    (tmul (tmul ((0, 2, 0), 0) ((0, 0, 2), 0)) (0, (0, 1, 0))) = (0, 0) := by decide
theorem e8_k1 : tmul ((0, 2, 0), 0) ((0, 0, 2), 0) ≠ (0, 0) := by decide
theorem e8_k2 : tmul ((0, 2, 0), 0) (0, (0, 1, 0)) ≠ (0, 0) := by decide
theorem e8_k3 : tmul ((0, 0, 2), 0) (0, (0, 1, 0)) ≠ (0, 0) := by decide
theorem e8_k4 : tmul (tmul ((0, 2, 0), 0) ((0, 0, 2), 0)) (0, (0, 1, 0)) ≠ (0, 0) := by decide
theorem e8_k5 : (((0, 2, 0), 0) : Tc) ≠ (0, 0) := by decide
theorem e8_k6 : (((0, 0, 2), 0) : Tc) ≠ (0, 0) := by decide
theorem e8_k7 : ((0, (0, 1, 0)) : Tc) ≠ (0, 0) := by decide
theorem e8_c1 : tmul ((0, 2, 0), 0) ((0, 0, 2), 0) = tmul ((0, 0, 2), 0) ((0, 2, 0), 0) := by
  decide

theorem arch76Lemma7_self_centralizing [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (huw : IsConj K.u K.w) (hwu : IsConj (K.w * K.u) (K.x * K.y * K.uv))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) {s : G}
    (hS : (S : Subgroup G) = Tsub K ⊔ Subgroup.closure {s})
    (hs2 : s ^ 2 = 1) (hsw : s⁻¹ * K.w * s = K.w) (hsx : s⁻¹ * K.x * s = K.x⁻¹)
    (hsy : s⁻¹ * K.y * s = K.y⁻¹) (hsuv : s⁻¹ * K.uv * s = K.x * K.y * K.uv)
    (hst : s⁻¹ * K.t * s = K.x⁻¹ * K.t) (hsu : s⁻¹ * K.u * s = K.u) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set z := (K.x * K.y) ^ 2 with hzdef
  have hsT := s_not_mem_T K hsx hsy
  set D := idxTwo2 K hs2 hsw hsx hsy hsuv hst hsu hsT with hDdef
  have hD : ∀ a b, D.smul a b = sm2 a b := fun _ _ => rfl
  have hSD : (S : Subgroup G) = D.Ssub := hS
  have hDs : D.s = s := rfl
  have e1 : ∀ p, D.sElt (1, p) = s * tElt K p := fun p => D.sElt_one_fst p
  have e0 : ∀ p, D.sElt (0, p) = tElt K p := fun p => D.sElt_zero_fst p
  have hzE : ∀ e ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G), e ≠ 1 →
      IsConj e z := hfusE
  have hne1 : ∀ p : Tc, p ≠ (0, 0) → tElt K p ≠ 1 := fun p hp => tElt_ne_one K hp
  have hx2z : IsConj (K.x ^ 2) z := hzE _ (x2_mem_E) (by rw [← tElt_x2 K]; exact hne1 _ ne_x2c)
  have htz : IsConj K.t z := hzE _ (t_mem_E) (by rw [← tElt_gen_t K]; exact hne1 _ ne_tc)
  have huvz : IsConj K.uv z := hzE _ (uv_mem_E) (by rw [← tElt_gen_uv K]; exact hne1 _ ne_uvc)
  have hxyuv : IsConj (K.x * K.y * K.uv) z :=
    (isConj_of_conj s hsuv).symm.trans huvz
  have hwuz : IsConj (K.w * K.u) z := hwu.trans hxyuv
  have hnot : ∀ {g : G}, IsConj g K.w → IsConj g z → False := fun h1 h2 => hAnn1 (h1.symm.trans h2)
  have hS_mem : ∀ r : Sc, D.sElt r ∈ (S : Subgroup G) := fun r => hSD ▸ D.sElt_mem r
  have hcompl3 : ∀ r : Sc, chi3 r = 0 → isInv2 r = true → tabS3.any (·.1 == r) = true := by
    intro r h1 h2
    have := compl_S3 r
    rw [(inS3_iff r).2 h1, h2] at this
    simpa using this
  have hcompl4 : ∀ r : Sc, chi4 r = 0 → isInv2 r = true → tabS4.any (·.1 == r) = true := by
    intro r h1 h2
    have := compl_S4 r
    rw [(inS4_iff r).2 h1, h2] at this
    simpa using this
  have hcompl1 : ∀ r : Sc, chi1 r = 0 → isInv2 r = true → tabS1.any (·.1 == r) = true := by
    intro r h1 h2
    have := compl_S1 r
    rw [(inS1_iff r).2 h1, h2] at this
    simpa using this
  have hwinv : isInv2 wc2 = true := isInv2_wc2
  have hw_el : D.sElt wc2 = K.w := by rw [wc2, e0, tElt_w']
  obtain ⟨tg3, htg3, hc3⟩ := exists_conj_target hnonab S D hD hSD chi3 chi3_sm2 card_chi3
    checkTab_S3 hcompl3 chi3_wc2 hwinv
  rw [hw_el] at hc3
  have h3 : IsConj K.w s ∨ IsConj K.w (s * (K.w * K.u)) := by
    simp only [targets3, List.mem_cons, List.mem_nil_iff, or_false] at htg3
    rcases htg3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e0, tElt_z2] at hc3; exact (hAnn1 hc3).elim
    · rw [e0, tElt_x2] at hc3; exact (hAnn1 (hc3.trans hx2z)).elim
    · rw [e0, tElt_t'] at hc3; exact (hAnn1 (hc3.trans htz)).elim
    · rw [e0, tElt_xyuv''] at hc3; exact (hAnn1 (hc3.trans hxyuv)).elim
    · rw [e0, tElt_wu'] at hc3; exact (hAnn1 (hc3.trans hwuz)).elim
    · rw [e1, tElt_one', mul_one] at hc3; exact Or.inl hc3
    · rw [e1, tElt_wu'] at hc3; exact Or.inr hc3
  obtain ⟨tg4, htg4, hc4⟩ := exists_conj_target hnonab S D hD hSD chi4 chi4_sm2 card_chi4
    checkTab_S4 hcompl4 chi4_wc2 hwinv
  rw [hw_el] at hc4
  have h4 : IsConj K.w (s * K.u) ∨ IsConj K.w (s * K.w) := by
    simp only [targets4, List.mem_cons, List.mem_nil_iff, or_false] at htg4
    rcases htg4 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e0, tElt_z2] at hc4; exact (hAnn1 hc4).elim
    · rw [e0, tElt_x2] at hc4; exact (hAnn1 (hc4.trans hx2z)).elim
    · rw [e0, tElt_t'] at hc4; exact (hAnn1 (hc4.trans htz)).elim
    · rw [e0, tElt_xyuv''] at hc4; exact (hAnn1 (hc4.trans hxyuv)).elim
    · rw [e0, tElt_wu'] at hc4; exact (hAnn1 (hc4.trans hwuz)).elim
    · rw [e1, tElt_u'] at hc4; exact Or.inl hc4
    · rw [e1, tElt_w'] at hc4; exact Or.inr hc4
  have hz_el : D.sElt zc2 = z := by rw [zc2, e0, tElt_z2]
  have hzS : (S : Subgroup G) ≤ Subgroup.centralizer {z} := by
    intro g hg
    rw [hSD] at hg
    obtain ⟨r, rfl⟩ := D.exists_sElt hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← hz_el, ← D.sElt_mul, ← D.sElt_mul, hD, hD,
      zc2_central]
  have hfact : ∀ r' ∈ (S : Subgroup G), r' * r' = 1 → r' ≠ 1 → r' ≠ z →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * r' * q = r' * z := by
    intro g hg hg2 hg1 hgz
    rw [hSD] at hg
    obtain ⟨r, rfl⟩ := D.exists_sElt hg
    have hinv := isInv2_of_sElt D hD hg2 hg1
    have hrz : r ≠ zc2 := fun h => hgz (by rw [h, hz_el])
    have hc := compl_Z r
    rw [Bool.or_eq_true, Bool.or_eq_true] at hc
    rcases hc with (hc | hc) | hc
    · rw [hinv] at hc; exact absurd hc (by decide)
    · exact absurd (beq_iff_eq.1 hc) hrz
    obtain ⟨e, he, he1⟩ := List.any_eq_true.1 hc
    simp only [beq_iff_eq] at he1
    have hchk := List.all_eq_true.1 checkTab_Z e he
    simp only [conjChk, beq_iff_eq] at hchk
    refine ⟨D.sElt e.2, hS_mem _, ?_⟩
    have h3 : D.sElt e.1 * D.sElt e.2 = D.sElt e.2 * (D.sElt e.1 * D.sElt zc2) := by
      rw [← D.sElt_mul, ← D.sElt_mul, ← D.sElt_mul, hD, hD, hD, hchk]
    rw [← he1, ← hz_el]
    calc (D.sElt e.2)⁻¹ * D.sElt e.1 * D.sElt e.2
        = (D.sElt e.2)⁻¹ * (D.sElt e.1 * D.sElt e.2) := by group
      _ = D.sElt e.1 * D.sElt zc2 := by rw [h3]; group
  have hs_el : D.sElt (1, (0, 0)) = s := by rw [e1, tElt_zero, mul_one]
  have hsS : s ∈ (S : Subgroup G) := hs_el ▸ hS_mem _
  have hTS : Tsub K ≤ (S : Subgroup G) := by rw [hSD]; exact le_sup_left
  have hwuS : K.w * K.u ∈ (S : Subgroup G) := hTS (by rw [← tElt_wu' K]; exact tElt_mem K _)
  have huS : K.u ∈ (S : Subgroup G) := hTS (Subgroup.mem_sup_right (u_mem_D K))
  have hsw' : K.w * s = s * K.w := by
    calc K.w * s = s * (s⁻¹ * K.w * s) := by group
      _ = s * K.w := by rw [hsw]
  have hsu' : K.u * s = s * K.u := by
    calc K.u * s = s * (s⁻¹ * K.u * s) := by group
      _ = s * K.u := by rw [hsu]
  have huw' : K.u * K.w = K.w * K.u := by
    have h := K.hu_w
    calc K.u * K.w = K.u * (K.u⁻¹ * K.w * K.u) := by rw [h]
      _ = K.w * K.u := by rw [u_inv K, ← mul_assoc, ← mul_assoc, u_mul_self K, one_mul]
  have hss : s * s = 1 := by rw [← pow_two, hs2]
  have hs1 : s ≠ 1 := fun h => hsT (h ▸ (Tsub K).one_mem)
  have hsT' : ∀ g ∈ Tsub K, s * g ∉ Tsub K := fun g hg h => hsT (by
    have := (Tsub K).mul_mem h ((Tsub K).inv_mem hg); simpa using this)
  have hwuT : K.w * K.u ∈ Tsub K := by rw [← tElt_wu' K]; exact tElt_mem K _
  have huT : K.u ∈ Tsub K := Subgroup.mem_sup_right (u_mem_D K)
  have hwT : K.w ∈ Tsub K := Subgroup.mem_sup_left K.w_mem
  have hs_wus : IsConj s (s * (K.w * K.u)) :=
    isConj_mul_of_isConj_central S hzS hfact hwuz hsS hwuS
      (by
        calc s * (K.w * K.u) = (s * K.w) * K.u := by group
          _ = (K.w * s) * K.u := by rw [hsw']
          _ = K.w * (s * K.u) := by group
          _ = K.w * (K.u * s) := by rw [hsu']
          _ = K.w * K.u * s := by group) hss hs1
      (fun h => hsT (h ▸ hwuT))
  have hus_ws : IsConj (s * K.u) (s * K.w) := by
    have h := isConj_mul_of_isConj_central S hzS hfact hwuz
      ((S : Subgroup G).mul_mem hsS huS) hwuS
      (by
        calc s * K.u * (K.w * K.u) = s * (K.u * K.w * K.u) := by group
          _ = s * K.w := by rw [huw', mul_assoc, u_mul_self K, mul_one]
          _ = K.w * s := hsw'.symm
          _ = K.w * s * (K.u * K.u) := by rw [u_mul_self K, mul_one]
          _ = K.w * (K.u * s) * K.u := by rw [hsu']; group
          _ = K.w * K.u * (s * K.u) := by group)
      (by
        calc s * K.u * (s * K.u) = s * (K.u * s) * K.u := by group
          _ = s * (s * K.u) * K.u := by rw [hsu']
          _ = 1 := by rw [← mul_assoc, hss, one_mul, u_mul_self K])
      (fun h => hsT' _ huT (h ▸ (Tsub K).one_mem))
      (fun h => hsT (by
        have : s = K.w * K.u * K.u⁻¹ := by rw [← h]; group
        rw [this]; exact (Tsub K).mul_mem hwuT ((Tsub K).inv_mem huT)))
    have he : s * K.u * (K.w * K.u) = s * K.w := by
      calc s * K.u * (K.w * K.u) = s * (K.u * K.w * K.u) := by group
        _ = s * K.w := by rw [huw', mul_assoc, u_mul_self K, mul_one]
    rwa [he] at h
  have hws : IsConj K.w s := h3.elim id fun h => h.trans hs_wus.symm
  have hwsu : IsConj K.w (s * K.u) := h4.elim id fun h => h.trans hus_ws.symm
  have hwxuv_el : D.sElt (0, ((1, 1, 0), (1, 0, 0))) = K.w * K.x * K.uv := by
    rw [e0, tElt_wxuv]
  obtain ⟨tg1, htg1, hc1⟩ := exists_conj_target hnonab S D hD hSD chi1 chi1_sm2 card_chi1
    checkTab_S1 hcompl1 chi1_wxuv isInv2_wxuv
  rw [hwxuv_el] at hc1
  have h7 : IsConj (K.w * K.x * K.uv) z ∨ IsConj (K.w * K.x * K.uv) K.w := by
    simp only [targets1, List.mem_cons, List.mem_nil_iff, or_false] at htg1
    rcases htg1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e0, tElt_z2] at hc1; exact Or.inl hc1
    · rw [e0, tElt_x2] at hc1; exact Or.inl (hc1.trans hx2z)
    · rw [e0, tElt_t'] at hc1; exact Or.inl (hc1.trans htz)
    · rw [e0, tElt_xyuv''] at hc1; exact Or.inl (hc1.trans hxyuv)
    · rw [e0, tElt_u'] at hc1; exact Or.inr (hc1.trans huw)
    · rw [e1, tElt_one', mul_one] at hc1; exact Or.inr (hc1.trans hws.symm)
    · rw [e1, tElt_u'] at hc1; exact Or.inr (hc1.trans hwsu.symm)
  set Q₁ := (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} with hQ₁def
  have hQ₁c : Q₁ ≤ Subgroup.centralizer {K.w} := inf_le_right
  have hQ₁p : IsPGroup 2 Q₁ := S.isPGroup'.to_le inf_le_left
  have hcoordQ : ∀ g ∈ Q₁, ∃ r : Sc, inQ1 r = true ∧ D.sElt r = g := by
    intro g hg
    obtain ⟨hgS, hgw⟩ := Subgroup.mem_inf.1 hg
    rw [hSD] at hgS
    obtain ⟨r, rfl⟩ := D.exists_sElt hgS
    refine ⟨r, ?_, rfl⟩
    have h1 : sm2 r wc2 = sm2 wc2 r := D.sElt_injective (by
      rw [← hD, ← hD, D.sElt_mul, D.sElt_mul, hw_el]
      exact Subgroup.mem_centralizer_singleton_iff.1 hgw)
    have := inQ1_of_comm_w r
    rw [h1, beq_self_eq_true, Bool.not_true, Bool.false_or] at this
    exact this
  have hmemQ : ∀ r : Sc, inQ1 r = true → D.sElt r ∈ Q₁ := by
    intro r hr
    refine Subgroup.mem_inf.2 ⟨hS_mem r, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h := q1_comm_w r
    rw [hr, Bool.not_true, Bool.false_or, beq_iff_eq] at h
    rw [← hw_el, ← D.sElt_mul, ← D.sElt_mul, hD, hD, h]
  have hA_el : ∀ v : Co, D.sElt (0, (v, 0)) = K.ev v := fun v => by rw [e0, tElt_ev]
  have hmemA : ∀ r : Sc, r.1 = 0 → r.2.2 = 0 → D.sElt r ∈ K.A := by
    rintro ⟨e, v, d⟩ he hd
    simp only at he hd
    subst he hd
    rw [hA_el]
    exact K.ev_mem v
  have hAQ : K.A ≤ Q₁ := by
    intro a ha
    obtain ⟨v, rfl⟩ := K.exists_ev ha
    rw [← hA_el]
    exact hmemQ _ rfl
  have hsqQ : ∀ q ∈ Q₁, q * q ∈ K.A := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := hcoordQ q hq
    have h := q1_sq_mem_A r
    rw [hr, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    rw [sElt_mul_self D hD]
    exact hmemA _ h.1 h.2
  have hx_Q : K.x ∈ Q₁ := hAQ K.x_mem
  have hxu_Q : K.x * K.u ∈ Q₁ := by
    have : D.sElt (0, ((0, 1, 0), (0, 0, 1))) = K.x * K.u := by
      rw [e0, show ((0, 1, 0), (0, 0, 1)) = tmul ((0, 1, 0), 0) (0, (0, 0, 1)) from rfl,
        tElt_mul, tElt_x, tElt_gen_u]
    rw [← this]
    exact hmemQ _ rfl
  have hcharQ : ∀ q ∈ Q₁, (∀ r ∈ Q₁, q * (r * r) = (r * r) * q) → q ∈ K.A := by
    intro q hq hcomm
    obtain ⟨r, hr, rfl⟩ := hcoordQ q hq
    have hx := hcomm _ hx_Q
    have hxy := hcomm _ hxu_Q
    rw [← pow_two, ← tElt_x2 K, ← e0, ← D.sElt_mul, ← D.sElt_mul, hD, hD] at hx
    rw [← pow_two, xu_sq, xy_eq, ← e0, ← D.sElt_mul, ← D.sElt_mul, hD, hD] at hxy
    have h1 : sm2 r (0, ((0, 2, 0), 0)) = sm2 (0, ((0, 2, 0), 0)) r := D.sElt_injective hx
    have h2 : sm2 r (0, ((0, 1, 1), 0)) = sm2 (0, ((0, 1, 1), 0)) r := D.sElt_injective hxy
    have h := q1_comm_mem_A r
    rw [hr, h1, h2] at h
    simp only [beq_self_eq_true, Bool.true_and, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      beq_iff_eq] at h
    exact hmemA _ h.1 h.2
  have hsN : s ∈ Subgroup.normalizer (K.A : Set G) :=
    mem_normalizer_of_conj_ev K hss (f := lin (1, 0, 0) (0, 3, 0) (0, 0, 3))
      (K.conj_ev_of (by rw [hsw, K.ev_w]) (by rw [hsx, K.ev_030])
        (by rw [hsy, ← tElt_y_inv K, tElt_ev]))
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K.A : Set G) := by
    rw [hS]
    exact sup_le (Tsub_le_normalizer_A K) ((Subgroup.closure_le _).2 (by
      rintro _ rfl; exact hsN))
  have hmax : ∀ {Q : Subgroup G}, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {K.w} → Q₁ ≤ Q →
      Q = Q₁ := fun hQ hQw hQQ =>
    eq_of_le_centralizer_w K hfusE hAnn1 S hTS hSN
      (fun g hg => mem_normalizer_A_of_sq_char hAQ hsqQ hcharQ hg) hQ hQw hQQ
  have hwtype : ∀ tg ∈ targetsQ, IsConj (D.sElt tg) K.w := by
    intro tg htg
    simp only [targetsQ, List.mem_cons, List.mem_nil_iff, or_false] at htg
    rcases htg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e0, tElt_w']
    · rw [e0, tElt_u']; exact huw
    · rw [e1, tElt_one', mul_one]; exact hws.symm
    · rw [e1, tElt_u']; exact hwsu.symm
    · rw [e1, tElt_w']; exact hus_ws.symm.trans hwsu.symm
    · rw [e1, tElt_wu']; exact hs_wus.symm.trans hws.symm
  have hzQ : ∀ g ∈ Q₁, g * g = 1 → g ≠ 1 → IsConj g z → ∃ r ∈ zQ1, D.sElt r = g := by
    intro g hg hg2 hg1 hgz
    obtain ⟨r, hr, rfl⟩ := hcoordQ g hg
    have hinv := isInv2_of_sElt D hD hg2 hg1
    have h := compl_Q1 r
    rw [hr, hinv, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨r, List.contains_iff_mem.1 h, rfl⟩
    · exfalso
      obtain ⟨e, he, he1⟩ := List.any_eq_true.1 h
      simp only [beq_iff_eq] at he1
      obtain ⟨hc, htg⟩ := isConj_of_mem_tab D hD checkTab_Q1 he
      rw [he1] at hc
      exact hAnn1 ((hc.trans (hwtype _ htg)).symm.trans hgz)
  have hconjQ : ∀ {g : G} {M : Subgroup G}, IsConj g K.w → IsPGroup 2 M →
      M ≤ Subgroup.centralizer {g} →
      ∃ φ : G →* G, Function.Injective φ ∧ (∀ a, IsConj (φ a) a) ∧ ∀ m ∈ M, φ m ∈ Q₁ := by
    intro g M hg hMp hMc
    obtain ⟨c, hc⟩ := isConj_iff.1 hg
    set M' := M.map (MulAut.conj c).toMonoidHom
    have hM'c : M' ≤ Subgroup.centralizer {K.w} := by
      rintro _ ⟨m, hm, rfl⟩
      have hmg : m * g = g * m := Subgroup.mem_centralizer_singleton_iff.1 (hMc hm)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hc]
      calc c * m * c⁻¹ * (c * g * c⁻¹) = c * (m * g) * c⁻¹ := by group
        _ = c * (g * m) * c⁻¹ := by rw [hmg]
        _ = c * g * c⁻¹ * (c * m * c⁻¹) := by group
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_maximal hQ₁c hQ₁p hmax (hMp.map _) hM'c
    refine ⟨(MulAut.conj (k⁻¹ * c)).toMonoidHom, (MulAut.conj (k⁻¹ * c)).injective,
      fun a => ?_, fun m hm => ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (isConj_iff.2 ⟨k⁻¹ * c, rfl⟩).symm
    · have := hk _ ⟨m, hm, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this ⊢
      simpa [mul_assoc] using this
  have hx2T : K.x ^ 2 ∈ Tsub K := Subgroup.mem_sup_left (K.A.pow_mem K.x_mem 2)
  have hy2T : K.y ^ 2 ∈ Tsub K := Subgroup.mem_sup_left (K.A.pow_mem K.y_mem 2)
  have htT : K.t ∈ Tsub K := Subgroup.mem_sup_right (t_mem_D K)
  have hwxuvT : K.w * K.x * K.uv ∈ Tsub K := by rw [← tElt_wxuv K]; exact tElt_mem K _
  obtain ⟨f1, f2, f3, f4, f5⟩ := comm_T_facts
  have commT : ∀ {p q : Tc}, tmul p q = tmul q p → tElt K p * tElt K q = tElt K q * tElt K p :=
    fun h => by rw [← tElt_mul, ← tElt_mul, h]
  have hx2' : tElt K ((0, 2, 0), 0) = K.x ^ 2 := tElt_x2 K
  have hy2' : tElt K ((0, 0, 2), 0) = K.y ^ 2 := tElt_y2 K
  have hwxuv' : tElt K ((1, 1, 0), (1, 0, 0)) = K.w * K.x * K.uv := tElt_wxuv K
  have h9 : ¬ IsConj (K.w * K.x * K.uv) K.w := by
    intro hc
    set M := Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.t} : Set G)
    have hMT : M ≤ Tsub K := (Subgroup.closure_le _).2 (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      exacts [hx2T, hy2T, htT])
    have hMp : IsPGroup 2 M := S.isPGroup'.to_le (hMT.trans hTS)
    have hMc : M ≤ Subgroup.centralizer {K.w * K.x * K.uv} := (Subgroup.closure_le _).2 (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl | rfl
      · rw [← hx2', ← hwxuv']; exact commT f1
      · rw [← hy2', ← hwxuv']; exact commT f2
      · rw [← tElt_gen_t K, ← hwxuv']; exact commT f3)
    obtain ⟨φ, hφi, hφc, hφQ⟩ := hconjQ hc hMp hMc
    have hx2M : K.x ^ 2 ∈ M := Subgroup.subset_closure (by simp)
    have hy2M : K.y ^ 2 ∈ M := Subgroup.subset_closure (by simp)
    have htM : K.t ∈ M := Subgroup.subset_closure (by simp)
    have hinvT : ∀ {p : Tc}, tmul p p = (0, 0) → p ≠ (0, 0) →
        tElt K p * tElt K p = 1 ∧ tElt K p ≠ 1 := fun h1 h2 =>
      ⟨by rw [← tElt_mul, h1, tElt_zero], tElt_ne_one K h2⟩
    have hz' : ∀ {p : Tc}, tElt K p ∈ M → tElt K p ∈
        Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) → tmul p p = (0, 0) →
        p ≠ (0, 0) → ∃ r ∈ zQ1, D.sElt r = φ (tElt K p) := by
      intro p hpM hpE h1 h2
      obtain ⟨hp2, hp1⟩ := hinvT h1 h2
      refine hzQ _ (hφQ _ hpM) ?_ ?_ ((hφc _).trans (hzE _ hpE hp1))
      · rw [← map_mul, hp2, map_one]
      · intro h; exact hp1 (hφi (h.trans (map_one φ).symm))
    have hEM : ∀ {a b : G}, a ∈ M → b ∈ M → a * b ∈ M := fun ha hb => M.mul_mem ha hb
    have hEE : ∀ {a b : G}, a ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) →
        b ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) →
        a * b ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) :=
      fun ha hb => Subgroup.mul_mem _ ha hb
    have hpa : tElt K ((0, 2, 0), 0) ∈ M := by rw [hx2']; exact hx2M
    have hpb : tElt K ((0, 0, 2), 0) ∈ M := by rw [hy2']; exact hy2M
    have hpd : tElt K (0, (0, 1, 0)) ∈ M := by rw [tElt_gen_t K]; exact htM
    have hea : tElt K ((0, 2, 0), 0) ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) := by
      rw [hx2']; exact x2_mem_E
    have heb : tElt K ((0, 0, 2), 0) ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) := by
      rw [hy2']; exact y2_mem_E
    have hed : tElt K (0, (0, 1, 0)) ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) := by
      rw [tElt_gen_t K]; exact t_mem_E
    obtain ⟨ra, hra, hra'⟩ := hz' hpa hea e8_i1 e8_k5
    obtain ⟨rb, hrb, hrb'⟩ := hz' hpb heb e8_i2 e8_k6
    obtain ⟨rd, hrd, hrd'⟩ := hz' hpd hed e8_i3 e8_k7
    have hprod : ∀ {p q : Tc} {rp rq : Sc}, D.sElt rp = φ (tElt K p) →
        D.sElt rq = φ (tElt K q) → D.sElt (sm2 rp rq) = φ (tElt K (tmul p q)) := by
      intro p q rp rq hp hq
      rw [← hD, D.sElt_mul, hp, hq, tElt_mul, map_mul]
    obtain ⟨rab, hrab, hrab'⟩ := hz' (by rw [tElt_mul]; exact hEM hpa hpb)
      (by rw [tElt_mul]; exact hEE hea heb) e8_j1 e8_k1
    obtain ⟨rad, hrad, hrad'⟩ := hz' (by rw [tElt_mul]; exact hEM hpa hpd)
      (by rw [tElt_mul]; exact hEE hea hed) e8_j2 e8_k2
    obtain ⟨rbd, hrbd, hrbd'⟩ := hz' (by rw [tElt_mul]; exact hEM hpb hpd)
      (by rw [tElt_mul]; exact hEE heb hed) e8_j3 e8_k3
    obtain ⟨rabd, hrabd, hrabd'⟩ := hz' (by rw [tElt_mul, tElt_mul]; exact hEM (hEM hpa hpb) hpd)
      (by rw [tElt_mul, tElt_mul]; exact hEE (hEE hea heb) hed) e8_j4 e8_k4
    have eab : sm2 ra rb = rab := D.sElt_injective ((hprod hra' hrb').trans hrab'.symm)
    have ead : sm2 ra rd = rad := D.sElt_injective ((hprod hra' hrd').trans hrad'.symm)
    have ebd : sm2 rb rd = rbd := D.sElt_injective ((hprod hrb' hrd').trans hrbd'.symm)
    have eabd : sm2 (sm2 ra rb) rd = rabd := D.sElt_injective
      ((hprod (hprod hra' hrb') hrd').trans hrabd'.symm)
    have hcomm : ∀ {p q : Tc} {rp rq : Sc}, tmul p q = tmul q p → D.sElt rp = φ (tElt K p) →
        D.sElt rq = φ (tElt K q) → sm2 rp rq = sm2 rq rp := by
      intro p q rp rq hpq hp hq
      apply D.sElt_injective
      rw [← hD, ← hD, D.sElt_mul, D.sElt_mul, hp, hq, ← map_mul, ← map_mul, commT hpq]
    have hcab : sm2 ra rb = sm2 rb ra :=
      hcomm e8_c1 hra' hrb'
    have hcad : sm2 ra rd = sm2 rd ra := hcomm f4 hra' hrd'
    have hcbd : sm2 rb rd = sm2 rd rb := hcomm f5 hrb' hrd'
    have hne : ∀ {p q : Tc} {rp rq : Sc}, p ≠ q → D.sElt rp = φ (tElt K p) →
        D.sElt rq = φ (tElt K q) → rp ≠ rq := by
      intro p q rp rq hpq hp hq h
      apply hpq
      apply tElt_injective K
      apply hφi
      rw [← hp, ← hq, h]
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 zQ1_no_E8 ra hra)
      rb hrb) rd hrd
    have b1 : (sm2 ra rb == sm2 rb ra) = true := beq_iff_eq.2 hcab
    have b2 : (sm2 ra rd == sm2 rd ra) = true := beq_iff_eq.2 hcad
    have b3 : (sm2 rb rd == sm2 rd rb) = true := beq_iff_eq.2 hcbd
    have c1 : zQ1.contains (sm2 ra rb) = true := by rw [eab]; exact List.contains_iff_mem.2 hrab
    have c2 : zQ1.contains (sm2 ra rd) = true := by rw [ead]; exact List.contains_iff_mem.2 hrad
    have c3 : zQ1.contains (sm2 rb rd) = true := by rw [ebd]; exact List.contains_iff_mem.2 hrbd
    have c4 : zQ1.contains (sm2 (sm2 ra rb) rd) = true := by
      rw [eabd]; exact List.contains_iff_mem.2 hrabd
    have d1 : (ra != rb) = true := bne_iff_ne.2 (hne e8_n1 hra' hrb')
    have d2 : (rd != ra) = true := bne_iff_ne.2 (hne e8_n2 hrd' hra')
    have d3 : (rd != rb) = true := bne_iff_ne.2 (hne e8_n3 hrd' hrb')
    have d4 : (rd != sm2 ra rb) = true := bne_iff_ne.2 (by rw [eab]; exact hne e8_n4 hrd' hrab')
    rw [b1, b2, b3, d1, d2, d3, d4, c1, c2, c3, c4] at h1
    exact absurd h1 (by decide)
  have h10 : ¬ IsConj (K.w * K.x * K.uv) z := by
    intro hwz
    set N := Subgroup.closure ({K.w * K.x * K.uv, K.w * K.u} : Set G)
    have hNS : N ≤ (S : Subgroup G) := (Subgroup.closure_le _).2 (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      exacts [hTS hwxuvT, hwuS])
    have hNp : IsPGroup 2 N := S.isPGroup'.to_le hNS
    have hsu_el : D.sElt (1, ((0, 0, 0), (0, 0, 1))) = s * K.u := by rw [e1, tElt_u']
    have hwu_el : D.sElt (0, ((1, 0, 0), (0, 0, 1))) = K.w * K.u := by rw [e0, tElt_wu']
    obtain ⟨cf1, cf2⟩ := (Bool.and_eq_true _ _).mp comm_facts
    have hNc : N ≤ Subgroup.centralizer {s * K.u} := (Subgroup.closure_le _).2 (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl
      · rw [← hwxuv_el, ← hsu_el, ← D.sElt_mul, ← D.sElt_mul, hD, hD, beq_iff_eq.1 cf1]
      · rw [← hwu_el, ← hsu_el, ← D.sElt_mul, ← D.sElt_mul, hD, hD, beq_iff_eq.1 cf2])
    obtain ⟨φ, hφi, hφc, hφQ⟩ := hconjQ hwsu.symm hNp hNc
    have hwxuvN : K.w * K.x * K.uv ∈ N := Subgroup.subset_closure (by simp)
    have hwuN : K.w * K.u ∈ N := Subgroup.subset_closure (by simp)
    have hinv1 : (K.w * K.x * K.uv) * (K.w * K.x * K.uv) = 1 := by
      rw [← hwxuv_el, sElt_mul_self D hD, sq_wxuv_c, sElt_one2]
    have hinv2 : (K.w * K.u) * (K.w * K.u) = 1 := by
      rw [← hwu_el, sElt_mul_self D hD, sq_wu_c, sElt_one2]
    have hne1 : K.w * K.x * K.uv ≠ 1 := by
      rw [← hwxuv_el, ← sElt_one2 D]
      exact fun h => ne_wxuv_c (D.sElt_injective h)
    have hne2 : K.w * K.u ≠ 1 := by
      rw [← hwu_el, ← sElt_one2 D]
      exact fun h => ne_wu_c (D.sElt_injective h)
    have hφinv : ∀ {g : G}, g * g = 1 → g ≠ 1 → φ g * φ g = 1 ∧ φ g ≠ 1 := fun h2 h1 =>
      ⟨by rw [← map_mul, h2, map_one], fun h => h1 (hφi (h.trans (map_one φ).symm))⟩
    obtain ⟨ra, hra, hra'⟩ := hzQ _ (hφQ _ hwxuvN) (hφinv hinv1 hne1).1 (hφinv hinv1 hne1).2
      ((hφc _).trans hwz)
    obtain ⟨rb, hrb, hrb'⟩ := hzQ _ (hφQ _ hwuN) (hφinv hinv2 hne2).1 (hφinv hinv2 hne2).2
      ((hφc _).trans hwuz)
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 zQ1_no_D16 ra hra) rb hrb
    simp only [beq_iff_eq] at h1
    have hfour : ∀ r : Sc, D.sElt (sm2 (sm2 r r) (sm2 r r)) = D.sElt r ^ 4 := fun r => by
      rw [← sElt_mul_self D hD, ← sElt_mul_self D hD, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
        pow_two, pow_two]
    have h2 : (φ (K.w * K.x * K.uv * (K.w * K.u))) ^ 4 = 1 := by
      rw [map_mul, ← hra', ← hrb', ← D.sElt_mul, hD, ← hfour, h1, sElt_one2]
    have h3 : (K.w * K.x * K.uv * (K.w * K.u)) ^ 4 = 1 :=
      hφi (by rw [map_pow, h2, map_one])
    have h4 := wxuv_wu_ord
    simp only [bne_iff_ne, ne_eq] at h4
    apply h4
    apply D.sElt_injective
    rw [sElt_one2, hfour, ← hD, D.sElt_mul, hwxuv_el, hwu_el]
    exact h3
  rcases h7 with h | h
  · exact h10 h
  · exact h9 h

end CFSG.CGT.Stroth76
