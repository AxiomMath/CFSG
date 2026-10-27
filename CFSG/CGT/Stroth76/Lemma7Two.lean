module

public import CFSG.CGT.Stroth76.TExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Thompson
public import CFSG.CGT.Stroth76.TFacts

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

@[expose] def xyuvClass : List Tc :=
  [((0, 1, 1), (1, 0, 0)), ((0, 3, 3), (1, 0, 0)), ((0, 1, 3), (1, 0, 0)), ((0, 3, 1), (1, 0, 0))]

theorem mem_xyuvClass_033 : ((0, 3, 3), (1, 0, 0)) ∈ xyuvClass := by decide
theorem mem_xyuvClass_013 : ((0, 1, 3), (1, 0, 0)) ∈ xyuvClass := by decide

@[expose] def sqInvCheck (p : Tc) : Bool :=
  !(tmul (tmul p p) (tmul p p) == (0, 0)) || tmul p p == (0, 0) || decide (IsEc (tmul p p)) ||
    xyuvClass.contains (tmul p p)

theorem sqInvCheck_all : ∀ p : Tc, sqInvCheck p = true := by
  decide +kernel

theorem tc_sq_inv_aux (p : Tc)
    (h : tmul (tmul p p) (tmul p p) = (0, 0) ∧ tmul p p ≠ (0, 0)) :
      IsEc (tmul p p) ∨ tmul p p ∈ xyuvClass := by
  have hc := sqInvCheck_all p
  simp only [sqInvCheck, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · exact absurd h.1 hc
  · exact absurd hc h.2
  · exact Or.inl hc
  · exact Or.inr hc

theorem tc_sq_inv (p : Tc) (h1 : tmul (tmul p p) (tmul p p) = (0, 0)) (h0 : tmul p p ≠ (0, 0)) :
    IsEc (tmul p p) ∨ tmul p p ∈ xyuvClass :=
  tc_sq_inv_aux p ⟨h1, h0⟩

theorem tc_xyuvClass_conj : ∀ q ∈ xyuvClass, ∃ p : Tc, tmul (tmul (tinv p) q) p = xyuvC := by
  decide +kernel

section Elements

variable {X : Type*} [Group X] (K : Config X)

theorem tElt_ne_one {p : Tc} (h : p ≠ (0, 0)) : tElt K p ≠ 1 := by
  rw [← tElt_zero K]
  exact fun he => h (tElt_injective K he)

end Elements

@[expose] def notSqrtWCheck (p : Tc) : Bool :=
  !(tmul p ((0, 1, 0), 0) == tmul ((0, 1, 0), 0) p) ||
    !(tmul p ((0, 0, 1), 0) == tmul ((0, 0, 1), 0) p) || !(tmul p p == ((1, 0, 0), 0))

theorem notSqrtWCheck_all : ∀ p : Tc, notSqrtWCheck p = true := by decide +kernel

theorem tc_not_sqrt_w (p : Tc)
    (h : tmul p ((0, 1, 0), 0) = tmul ((0, 1, 0), 0) p ∧
      tmul p ((0, 0, 1), 0) = tmul ((0, 0, 1), 0) p) : tmul p p ≠ ((1, 0, 0), 0) := by
  have hc := notSqrtWCheck_all p
  simp only [notSqrtWCheck, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hc
  rcases hc with (hc | hc) | hc
  · exact absurd h.1 hc
  · exact absurd h.2 hc
  · exact hc

@[expose] def sig3 (p : Tc) : Tc :=
  subst ((1, 0, 0), 0) ((0, 1, 0), 0) ((0, 0, 1), 0) ((0, 3, 3), (1, 0, 0)) ((0, 1, 0), (0, 1, 0))
    (0, (0, 0, 1)) p

theorem sig3_sq_ne : ∀ p : Tc, tmul (tmul ((1, 0, 0), 0) (sig3 p)) p ≠ (0, 0) := by
  decide +kernel

section Main

variable {G : Type*} [Group G] [Finite G] (K : Config G)

@[expose] def idxTwo3 {c : G} (hcx : c⁻¹ * K.x * c = K.x) (hcy : c⁻¹ * K.y * c = K.y)
    (hc2 : c ^ 2 = K.w) (huv : K.uv⁻¹ * c * K.uv = c * K.x⁻¹ * K.y⁻¹)
    (ht : K.t⁻¹ * c * K.t = c * K.x) (hu : K.u⁻¹ * c * K.u = c) (hcT : c ∉ Tsub K) :
    IdxTwo K where
  s := c
  iw := ((1, 0, 0), 0)
  ix := ((0, 1, 0), 0)
  iy := ((0, 0, 1), 0)
  iuv := ((0, 3, 3), (1, 0, 0))
  it := ((0, 1, 0), (0, 1, 0))
  iu := (0, (0, 0, 1))
  z := ((1, 0, 0), 0)
  hw := by
    rw [tElt_w, ← hc2, pow_two]
    group
  hx := by rw [tElt_x, hcx]
  hy := by rw [tElt_y, hcy]
  huv := by
    have h1 : tElt K ((0, 3, 3), (1, 0, 0)) = K.x⁻¹ * K.y⁻¹ * K.uv := by
      rw [show ((0, 3, 3), (1, 0, 0)) = tmul ((0, 3, 3), 0) (0, (1, 0, 0)) from rfl, tElt_mul,
        tElt_ev, tElt_gen_uv, K.ev_033]
    rw [h1]
    calc c⁻¹ * K.uv * c = c⁻¹ * (K.uv * c * K.uv⁻¹) * K.uv := by group
      _ = c⁻¹ * (K.uv⁻¹ * c * K.uv) * K.uv := by rw [uv_inv K]
      _ = K.x⁻¹ * K.y⁻¹ * K.uv := by rw [huv]; group
  ht := by
    have h1 : tElt K ((0, 1, 0), (0, 1, 0)) = K.x * K.t := by
      rw [show ((0, 1, 0), (0, 1, 0)) = tmul ((0, 1, 0), 0) (0, (0, 1, 0)) from rfl, tElt_mul,
        tElt_x, tElt_gen_t]
    rw [h1]
    calc c⁻¹ * K.t * c = c⁻¹ * (K.t * c * K.t⁻¹) * K.t := by group
      _ = c⁻¹ * (K.t⁻¹ * c * K.t) * K.t := by rw [t_inv K]
      _ = K.x * K.t := by rw [ht]; group
  hu := by
    rw [tElt_gen_u]
    calc c⁻¹ * K.u * c = c⁻¹ * (K.u * c * K.u⁻¹) * K.u := by group
      _ = c⁻¹ * (K.u⁻¹ * c * K.u) * K.u := by rw [u_inv K]
      _ = K.u := by rw [hu]; group
  hz := by rw [tElt_w, ← hc2, pow_two]
  hsT := hcT

theorem isConj_tElt_xyuv {q : Tc} (hq : q ∈ xyuvClass) :
    IsConj (tElt K q) (K.x * K.y * K.uv) := by
  obtain ⟨p, hp⟩ := tc_xyuvClass_conj q hq
  rw [isConj_iff]
  refine ⟨(tElt K p)⁻¹, ?_⟩
  rw [← tElt_xyuvC K, ← hp, inv_inv, tElt_mul, tElt_mul, tElt_tinv]

theorem isConj_xyuv_sq
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    {q : Tc} (hq : q ∈ xyuvClass) (h : IsConj K.uv (tElt K q)) :
    IsConj (K.x * K.y * K.uv) ((K.x * K.y) ^ 2) := by
  have huv : IsConj K.uv ((K.x * K.y) ^ 2) := hfusE _ (Subgroup.subset_closure (by simp)) (by
    rw [← tElt_gen_uv K]
    exact tElt_ne_one K (by decide))
  exact ((isConj_tElt_xyuv K hq).symm.trans h.symm).trans huv

theorem isConj_of_conj {a b : G} (g : G) (h : g⁻¹ * a * g = b) : IsConj a b :=
  isConj_iff.2 ⟨g⁻¹, by rw [inv_inv, ← h]⟩

theorem arch76Lemma7_index_two [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (huw : IsConj K.u K.w) (hwu : IsConj (K.w * K.u) (K.x * K.y * K.uv))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) {c : G}
    (hS : (S : Subgroup G) = Tsub K ⊔ Subgroup.closure {c})
    (hcx : c⁻¹ * K.x * c = K.x) (hcy : c⁻¹ * K.y * c = K.y) (hc2 : c ^ 2 = K.w)
    (hcase : (K.uv⁻¹ * c * K.uv = c * K.x⁻¹ * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x ∧
        K.u⁻¹ * c * K.u = c) ∨
      (K.uv⁻¹ * c * K.uv = c * K.x * K.y⁻¹ ∧ K.t⁻¹ * c * K.t = c * K.x * K.y ^ 2 ∧
        K.u⁻¹ * c * K.u = c⁻¹)) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconjuv : ∀ {v : G}, K.uv⁻¹ * c * K.uv = c * v → c⁻¹ * K.uv * c = v * K.uv := by
    intro v hv
    calc c⁻¹ * K.uv * c = c⁻¹ * (K.uv * c * K.uv⁻¹) * K.uv := by group
      _ = c⁻¹ * (K.uv⁻¹ * c * K.uv) * K.uv := by rw [uv_inv K]
      _ = v * K.uv := by rw [hv]; group
  rcases hcase with ⟨huv, ht, hu⟩ | ⟨huv, ht, hu⟩
  ·
    have hxyuv : IsConj (K.x * K.y * K.uv) ((K.x * K.y) ^ 2) := by
      refine isConj_xyuv_sq K hfusE mem_xyuvClass_033 ?_
      have h1 : tElt K ((0, 3, 3), (1, 0, 0)) = K.x⁻¹ * K.y⁻¹ * K.uv := by
        rw [show ((0, 3, 3), (1, 0, 0)) = tmul ((0, 3, 3), 0) (0, (1, 0, 0)) from rfl,
          tElt_mul, tElt_ev, tElt_gen_uv, K.ev_033]
      rw [h1]
      exact isConj_of_conj c (by rw [hconjuv (v := K.x⁻¹ * K.y⁻¹) (by rw [huv]; group)])
    have hcT : c ∉ Tsub K := by
      intro hc
      obtain ⟨p, rfl⟩ := exists_tElt K hc
      have hx : tmul p ((0, 1, 0), 0) = tmul ((0, 1, 0), 0) p := tElt_injective K (by
        rw [tElt_mul, tElt_mul, tElt_x]
        calc tElt K p * K.x = tElt K p * ((tElt K p)⁻¹ * K.x * tElt K p) := by rw [hcx]
          _ = K.x * tElt K p := by group)
      have hy : tmul p ((0, 0, 1), 0) = tmul ((0, 0, 1), 0) p := tElt_injective K (by
        rw [tElt_mul, tElt_mul, tElt_y]
        calc tElt K p * K.y = tElt K p * ((tElt K p)⁻¹ * K.y * tElt K p) := by rw [hcy]
          _ = K.y * tElt K p := by group)
      have hsq : tmul p p = ((1, 0, 0), 0) := tElt_injective K (by
        rw [tElt_mul, tElt_w, ← hc2, pow_two])
      exact tc_not_sqrt_w p ⟨hx, hy⟩ hsq
    set D := idxTwo3 K hcx hcy hc2 huv ht hu hcT
    have hSD : (S : Subgroup G) = D.Ssub := hS
    have hσ : ∀ p, D.σ p = sig3 p := fun p => rfl
    have hinvT : ∀ z ∈ (S : Subgroup G), z * z = 1 → z ∈ Tsub K := by
      intro z hz hz2
      rw [hSD] at hz
      obtain ⟨⟨e, p⟩, rfl⟩ := D.exists_sElt hz
      rcases zmod2_cases e with rfl | rfl
      · rw [D.sElt_zero_fst]; exact tElt_mem K p
      · exfalso
        rw [← D.sElt_mul, D.smul_11, D.sElt_zero_fst, hσ] at hz2
        exact sig3_sq_ne p (tElt_injective K (hz2.trans (tElt_zero K).symm))
    have hcS : c ∈ (S : Subgroup G) := by
      rw [hS]; exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
    have hTS : Tsub K ≤ (S : Subgroup G) := by rw [hS]; exact le_sup_left
    have hidx : (Tsub K).relIndex (S : Subgroup G) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := Tsub K) (K := (S : Subgroup G))
      have hcard : Nat.card (S : Subgroup G) = 2 ^ 9 := by rw [hSD]; exact D.card_Ssub
      rw [inf_of_le_left hTS, card_Tsub, hcard] at h
      omega
    refine CFSG.EvenSporadicStandard.TwoHS.false_of_thompson_pow hnonab S.isPGroup'
      S.not_dvd_index hTS hidx hcS hcT ?_ ?_
    · intro g k hgk
      have hc4 : c ^ (2 * k) = K.w ^ k := by rw [pow_mul, hc2]
      rw [hc4] at hgk ⊢
      refine hinvT _ hgk ?_
      rw [show g⁻¹ * K.w ^ k * g * (g⁻¹ * K.w ^ k * g) = g⁻¹ * (K.w ^ k * K.w ^ k) * g by group,
        ← pow_add, ← two_mul, pow_mul, K.hw, one_pow]
      group
    · intro g hg
      obtain ⟨p, hp⟩ := exists_tElt K hg
      have hsq : tElt K (tmul p p) = g⁻¹ * K.w * g := by
        rw [tElt_mul, hp, ← hc2, pow_two]; group
      have hw2 : K.w * K.w = 1 := by rw [← pow_two, K.hw]
      have h1 : tmul (tmul p p) (tmul p p) = (0, 0) := tElt_injective K (by
        rw [tElt_mul, hsq, tElt_zero]
        calc g⁻¹ * K.w * g * (g⁻¹ * K.w * g) = g⁻¹ * (K.w * K.w) * g := by group
          _ = 1 := by rw [hw2]; group)
      have h0 : tmul p p ≠ (0, 0) := fun h => w_ne_one K (by
        have := congrArg (tElt K) h
        rw [hsq, tElt_zero] at this
        calc K.w = g * (g⁻¹ * K.w * g) * g⁻¹ := by group
          _ = 1 := by rw [this]; group)
      have hwq : IsConj K.w (tElt K (tmul p p)) := by rw [hsq]; exact isConj_of_conj g rfl
      rcases tc_sq_inv p h1 h0 with hE | hcl
      · exact hAnn1 (hwq.trans (hfusE _ (tElt_mem_E_of_isEc K hE) (tElt_ne_one K h0)))
      · exact hAnn1 (hwq.trans ((isConj_tElt_xyuv K hcl).trans hxyuv))
  ·
    have hxyuv : IsConj (K.x * K.y * K.uv) ((K.x * K.y) ^ 2) := by
      refine isConj_xyuv_sq K hfusE mem_xyuvClass_013 ?_
      have h1 : tElt K ((0, 1, 3), (1, 0, 0)) = K.x * K.y⁻¹ * K.uv := by
        rw [show ((0, 1, 3), (1, 0, 0)) = tmul ((0, 1, 3), 0) (0, (1, 0, 0)) from rfl,
          tElt_mul, tElt_ev, tElt_gen_uv]
        simp [Config.ev, K.y_inv_eq, show (1 : ZMod 4).val = 1 from rfl,
          show (3 : ZMod 4).val = 3 from rfl]
      rw [h1]
      exact isConj_of_conj c (by rw [hconjuv (v := K.x * K.y⁻¹) (by rw [huv]; group)])
    have huc : c⁻¹ * K.u * c = K.u * K.w := by
      calc c⁻¹ * K.u * c = K.u * (K.u⁻¹ * c * K.u)⁻¹ * c := by group
        _ = K.u * K.w := by rw [hu, inv_inv, ← hc2, pow_two, mul_assoc]
    have hcomm : K.u * K.w = K.w * K.u := by
      have := K.hu_w
      rw [u_inv K] at this
      calc K.u * K.w = K.u * (K.u * K.w * K.u) := by rw [this]
        _ = K.w * K.u := by rw [← mul_assoc, ← mul_assoc, u_mul_self K, one_mul]
    have h1 : IsConj K.u (K.w * K.u) := hcomm ▸ isConj_of_conj c huc
    exact hAnn1 ((huw.symm.trans h1).trans (hwu.trans hxyuv))

end Main

end CFSG.CGT.Stroth76
