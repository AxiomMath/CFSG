module

public import CFSG.CGT.Stroth76.TModel

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

@[expose] def wpar (p : Tc) : ZMod 2 := p.1.1

theorem wpar_tmul (p q : Tc) : wpar (tmul p q) = wpar p + wpar q := by
  simp only [wpar, tmul, Prod.fst_add, dact_fst]

theorem wpar_tinv (p : Tc) : wpar (tinv p) = wpar p := by
  simp only [wpar, tinv, Prod.fst_neg, dact_fst]
  exact ZModModule.neg_eq_self _

@[expose] def IsQc (p : Tc) : Prop := p.2.1 = 0 ∧ p.2.2.1 = 0

instance : DecidablePred IsQc := fun p => by unfold IsQc; infer_instance

@[expose] def IsUc (p : Tc) : Prop := p.1.1 = p.2.2.2

instance : DecidablePred IsUc := fun p => by unfold IsUc; infer_instance

theorem isQc_tmul {p q : Tc} (hp : IsQc p) (hq : IsQc q) : IsQc (tmul p q) := by
  obtain ⟨v, a, b, c⟩ := p
  obtain ⟨v', a', b', c'⟩ := q
  simp only [IsQc] at hp hq ⊢
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨rfl, rfl⟩ := hq
  simp [tmul, dmul]

theorem isQc_tinv {p : Tc} (hp : IsQc p) : IsQc (tinv p) := by
  obtain ⟨v, a, b, c⟩ := p
  simp only [IsQc] at hp ⊢
  obtain ⟨rfl, rfl⟩ := hp
  simp [tinv, dinv]

theorem isUc_tmul {p q : Tc} (hp : IsUc p) (hq : IsUc q) : IsUc (tmul p q) := by
  obtain ⟨v, a, b, c⟩ := p
  obtain ⟨v', a', b', c'⟩ := q
  simp only [IsUc] at hp hq ⊢
  have h1 : (tmul (v, a, b, c) (v', a', b', c')).1.1 = v.1 + v'.1 := by
    simp only [tmul, Prod.fst_add, dact_fst]
  rw [h1, hp, hq]
  rfl

theorem isUc_tinv {p : Tc} (hp : IsUc p) : IsUc (tinv p) := by
  obtain ⟨v, a, b, c⟩ := p
  simp only [IsUc] at hp ⊢
  have h1 : (tinv (v, a, b, c)).1.1 = -v.1 := by simp only [tinv, Prod.fst_neg, dact_fst]
  rw [h1, hp, ZModModule.neg_eq_self]
  rfl

@[expose] def IsEc (p : Tc) : Prop :=
  p.1.1 = 0 ∧ (p.1.2.1 = 0 ∨ p.1.2.1 = 2) ∧ (p.1.2.2 = 0 ∨ p.1.2.2 = 2) ∧ p.2.2.2 = 0

instance : DecidablePred IsEc := fun p => by unfold IsEc; infer_instance

section Elements

variable {X : Type*} [Group X] (K : Config X)

@[expose] def tSub (P : Tc → Prop) (h1 : P (0, 0)) (hmul : ∀ {p q}, P p → P q → P (tmul p q))
    (hinv : ∀ {p}, P p → P (tinv p)) : Subgroup X where
  carrier := tElt K '' {p | P p}
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨tmul p q, hmul hp hq, tElt_mul K p q⟩
  one_mem' := ⟨(0, 0), h1, tElt_zero K⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨tinv p, hinv hp, tElt_tinv K p⟩

theorem tElt_mem_tSub_iff {P : Tc → Prop} {h1 hmul hinv} {p : Tc} :
    tElt K p ∈ tSub K P h1 hmul hinv ↔ P p := by
  refine ⟨?_, fun hp => ⟨p, hp, rfl⟩⟩
  rintro ⟨q, hq, h⟩
  rwa [← tElt_injective K h]

theorem card_tSub (P : Tc → Prop) [DecidablePred P] {h1 hmul hinv} :
    Nat.card (tSub K P h1 hmul hinv) = Fintype.card {p // P p} := by
  rw [← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {p // P p} => (⟨tElt K p, ⟨p, p.2, rfl⟩⟩ : tSub K P h1 hmul hinv)) ⟨?_, ?_⟩)
  · intro p q h
    exact Subtype.ext (tElt_injective K (congrArg Subtype.val h))
  · rintro ⟨g, p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

theorem tElt_w : tElt K ((1, 0, 0), 0) = K.w := by rw [tElt_ev, K.ev_w]
theorem tElt_x : tElt K ((0, 1, 0), 0) = K.x := by rw [tElt_ev, K.ev_x]
theorem tElt_y : tElt K ((0, 0, 1), 0) = K.y := by rw [tElt_ev, K.ev_y]

@[expose] def Qsub : Subgroup X := tSub K IsQc (by decide) isQc_tmul isQc_tinv

theorem card_Qsub : Nat.card (Qsub K) = 2 ^ 6 := by
  rw [Qsub, card_tSub]
  decide

theorem Qsub_le_Tsub : Qsub K ≤ Tsub K := by
  rintro _ ⟨p, -, rfl⟩
  exact tElt_mem K p

theorem tc_comm_w (p : Tc) (h : tmul p ((1, 0, 0), 0) = tmul ((1, 0, 0), 0) p) : IsQc p := by
  revert p; decide +kernel

theorem mem_Q_of_comm_w {g : X} (hg : g ∈ Tsub K) (hw : g * K.w = K.w * g) : g ∈ Qsub K := by
  obtain ⟨p, rfl⟩ := exists_tElt K hg
  refine ⟨p, tc_comm_w p (tElt_injective K ?_), rfl⟩
  rw [tElt_mul, tElt_mul, tElt_w, hw]

theorem tc_Q_comm_w (p : Tc) (hp : IsQc p) : tmul p ((1, 0, 0), 0) = tmul ((1, 0, 0), 0) p := by
  revert p; decide +kernel

theorem Qsub_le_centralizer_w : Qsub K ≤ Subgroup.centralizer {K.w} := by
  rintro _ ⟨p, hp, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← tElt_w K, ← tElt_mul, ← tElt_mul,
    tc_Q_comm_w p hp]

theorem tc_Q_comm_sq (p : Tc) (hp : IsQc p)
    (h1 : tmul p ((0, 2, 0), 0) = tmul ((0, 2, 0), 0) p)
    (h2 : tmul p ((0, 1, 1), 0) = tmul ((0, 1, 1), 0) p) : p.2 = 0 := by
  revert p; decide +kernel

theorem tc_Q_sq (p : Tc) (hp : IsQc p) : (tmul p p).2 = 0 := by
  revert p; decide +kernel

theorem tElt_mem_A_iff (p : Tc) : tElt K p ∈ K.A ↔ p.2 = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨v, d⟩ := p
    have hd : dElt K d ∈ K.A := by
      have : dElt K d = (K.ev v)⁻¹ * tElt K (v, d) := by simp [tElt]
      rw [this]
      exact K.A.mul_mem (K.A.inv_mem (K.ev_mem v)) h
    exact eq_zero_of_dElt_mem K hd
  · obtain ⟨v, d⟩ := p
    simp only at h
    subst h
    rw [tElt_ev]
    exact K.ev_mem v

theorem x_sq_eq : K.x ^ 2 = tElt K ((0, 2, 0), 0) := by
  rw [← tElt_x, pow_two, ← tElt_mul]
  rfl

theorem xy_eq : K.x * K.y = tElt K ((0, 1, 1), 0) := by
  rw [← tElt_x, ← tElt_y, ← tElt_mul]
  rfl

theorem xu_sq : (K.x * K.u) ^ 2 = K.x * K.y := by
  rw [xy_eq, ← tElt_x, ← tElt_gen_u, ← tElt_mul, pow_two, ← tElt_mul]
  congr 1

theorem mem_normalizer_A_of_mem_normalizer_Q {g : X}
    (hg : g ∈ Subgroup.normalizer (Qsub K : Set X)) :
    g ∈ Subgroup.normalizer (K.A : Set X) := by
  have hQ : ∀ q, q ∈ Qsub K ↔ g * q * g⁻¹ ∈ Qsub K := fun q =>
    Subgroup.mem_normalizer_iff.1 hg q
  have hsq : ∀ q ∈ Qsub K, q * q ∈ K.A := by
    rintro _ ⟨p, hp, rfl⟩
    rw [← tElt_mul, tElt_mem_A_iff]
    exact tc_Q_sq p hp
  have hAQ : K.A ≤ Qsub K := by
    intro a ha
    obtain ⟨v, rfl⟩ := K.exists_ev ha
    exact ⟨(v, 0), ⟨rfl, rfl⟩, tElt_ev K v⟩
  have hchar : ∀ q ∈ Qsub K, (∀ r ∈ Qsub K, q * (r * r) = (r * r) * q) → q ∈ K.A := by
    rintro _ ⟨p, hp, rfl⟩ hcomm
    have hx := hcomm (K.x) (hAQ K.x_mem)
    have hxu := hcomm (K.x * K.u) ⟨((0, 1, 0), (0, 0, 1)), ⟨rfl, rfl⟩, by
      rw [← tElt_x, ← tElt_gen_u, ← tElt_mul]; rfl⟩
    rw [← pow_two, x_sq_eq, ← tElt_mul, ← tElt_mul] at hx
    rw [← pow_two, xu_sq, xy_eq, ← tElt_mul, ← tElt_mul] at hxu
    rw [tElt_mem_A_iff]
    exact tc_Q_comm_sq p hp (tElt_injective K hx) (tElt_injective K hxu)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have hq := (hQ a).1 (hAQ ha)
    refine hchar _ hq (fun r hr => ?_)
    have hs : g⁻¹ * r * g ∈ Qsub K := by
      have := (hQ (g⁻¹ * r * g)).2
      simpa [mul_assoc] using this (by simpa [mul_assoc] using hr)
    have hcomm := K.comm ha (hsq _ hs)
    calc g * a * g⁻¹ * (r * r) = g * (a * ((g⁻¹ * r * g) * (g⁻¹ * r * g))) * g⁻¹ := by group
      _ = g * (((g⁻¹ * r * g) * (g⁻¹ * r * g)) * a) * g⁻¹ := by rw [hcomm]
      _ = r * r * (g * a * g⁻¹) := by group
  · intro ha
    have hq : a ∈ Qsub K := (hQ a).2 (hAQ ha)
    have := hchar a hq (fun r hr => ?_)
    · exact this
    have hs : g * r * g⁻¹ ∈ Qsub K := (hQ r).1 hr
    have hcomm := K.comm ha (hsq _ hs)
    have h2 : g * (a * (r * r)) * g⁻¹ = g * ((r * r) * a) * g⁻¹ := by
      calc g * (a * (r * r)) * g⁻¹ = g * a * g⁻¹ * ((g * r * g⁻¹) * (g * r * g⁻¹)) := by group
        _ = ((g * r * g⁻¹) * (g * r * g⁻¹)) * (g * a * g⁻¹) := by rw [hcomm]
        _ = g * ((r * r) * a) * g⁻¹ := by group
    simpa using h2

theorem co_two_nsmul (v : Co) (h : 2 • v = 0) (hv : v ≠ 0) :
    v = (0, 2, 0) ∨ v = (0, 0, 2) ∨ v = (0, 2, 2) ∨
      v = (1, 0, 0) ∨ v = (1, 2, 0) ∨ v = (1, 0, 2) ∨ v = (1, 2, 2) := by
  revert v; decide

theorem conj_t_w : K.t⁻¹ * K.w * K.t = K.ev (1, 2, 0) := by rw [K.ht_w, K.ev_120]
theorem conj_uv_w : K.uv⁻¹ * K.w * K.uv = K.ev (1, 2, 2) := by rw [K.huv_w, K.ev_122]
theorem conj_uvt_w : (K.uv * K.t)⁻¹ * K.w * (K.uv * K.t) = K.ev (1, 0, 2) := by
  rw [conj_mul_mul, ← K.ev_w, K.conj_uv_ev, K.conj_t_ev]
  rfl

@[expose] def xyuvC : Tc := ((0, 1, 1), (1, 0, 0))

theorem tElt_xyuvC : tElt K xyuvC = K.x * K.y * K.uv := by
  rw [xy_eq, ← tElt_gen_uv, ← tElt_mul]
  rfl

@[expose] def IsCc (p : Tc) : Prop := tmul p xyuvC = tmul xyuvC p

instance : DecidablePred IsCc := fun p => by unfold IsCc; infer_instance

theorem isCc_iff (p : Tc) : IsCc p ↔ tElt K p * (K.x * K.y * K.uv) = (K.x * K.y * K.uv) * tElt K p := by
  rw [← tElt_xyuvC, ← tElt_mul, ← tElt_mul]
  exact ⟨fun h => congrArg (tElt K) h, fun h => tElt_injective K h⟩

theorem card_isCc : Fintype.card {p // IsCc p} = 2 ^ 6 := by decide +kernel

theorem comm_u_tx : K.u⁻¹ * (K.t * K.x)⁻¹ * K.u * (K.t * K.x) = K.x * K.y * K.uv := by
  rw [← tElt_xyuvC, ← tElt_gen_u, ← tElt_gen_t, ← tElt_x, ← tElt_mul, ← tElt_tinv, ← tElt_tinv,
    ← tElt_mul, ← tElt_mul, ← tElt_mul]
  rfl

theorem isCc_u : IsCc (0, (0, 0, 1)) := by decide +kernel
theorem isCc_tx : IsCc (tmul (0, (0, 1, 0)) ((0, 1, 0), 0)) := by decide +kernel

@[expose] def Usub : Subgroup X := tSub K IsUc (by decide) isUc_tmul isUc_tinv

theorem card_isUc : Fintype.card {p // IsUc p} = 2 ^ 7 := by decide +kernel

theorem w_not_mem_Usub : K.w ∉ Usub K := by
  rw [← tElt_w, Usub, tElt_mem_tSub_iff]
  decide

theorem Usub_le_Tsub : Usub K ≤ Tsub K := by
  rintro _ ⟨p, -, rfl⟩
  exact tElt_mem K p

theorem tElt_wu : tElt K ((1, 0, 0), (0, 0, 1)) = K.w * K.u := by
  rw [← tElt_w, ← tElt_gen_u, ← tElt_mul]
  rfl

theorem ev_mem_closure_xy {v : Co} (hv : v.1 = 0) {s : Set X} (hx : K.x ∈ s) (hy : K.y ∈ s) :
    K.ev v ∈ Subgroup.closure s := by
  simp only [Config.ev, hv, ZMod.val_zero, pow_zero, one_mul]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure hx) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure hy) _)

theorem tElt_mem_closure_of {p : Tc} (hv : p.1.1 = 0) (hc : p.2.2.2 = 0) {s : Set X}
    (hx : K.x ∈ s) (hy : K.y ∈ s) (huv : K.uv ∈ s) (ht : K.t ∈ s) :
    tElt K p ∈ Subgroup.closure s := by
  obtain ⟨v, a, b, c⟩ := p
  simp only at hv hc
  subst hc
  refine Subgroup.mul_mem _ (ev_mem_closure_xy K hv hx hy) ?_
  simp only [dElt, ZMod.val_zero, pow_zero, mul_one]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure huv) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure ht) _)

theorem tc_split_wu (v : Co) (a b : ZMod 2) (hv : v.1 = 1) :
    tmul (v - dact (dinv (a, b, 0)) (1, 0, 0), (a, b, 0)) ((1, 0, 0), (0, 0, 1)) = (v, a, b, 1) ∧
      (v - dact (dinv (a, b, 0)) (1, 0, 0)).1 = 0 := by
  revert v a b; decide +kernel

theorem closure_wu_eq : Subgroup.closure {K.x, K.y, K.uv, K.t, K.w * K.u} = Usub K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by decide, tElt_x K⟩
    · exact ⟨_, by decide, tElt_y K⟩
    · exact ⟨_, by decide, tElt_gen_uv K⟩
    · exact ⟨_, by decide, tElt_gen_t K⟩
    · exact ⟨_, by decide, tElt_wu K⟩
  · rintro _ ⟨⟨v, a, b, c⟩, hp, rfl⟩
    simp only [IsUc] at hp
    have hx : K.x ∈ ({K.x, K.y, K.uv, K.t, K.w * K.u} : Set X) := by simp
    have hy : K.y ∈ ({K.x, K.y, K.uv, K.t, K.w * K.u} : Set X) := by simp
    have huv : K.uv ∈ ({K.x, K.y, K.uv, K.t, K.w * K.u} : Set X) := by simp
    have ht : K.t ∈ ({K.x, K.y, K.uv, K.t, K.w * K.u} : Set X) := by simp
    have hwu : K.w * K.u ∈ ({K.x, K.y, K.uv, K.t, K.w * K.u} : Set X) := by simp
    rcases zmod2_cases c with rfl | rfl
    · exact tElt_mem_closure_of K hp rfl hx hy huv ht
    · obtain ⟨hsplit, hq⟩ := tc_split_wu v a b hp
      rw [← hsplit, tElt_mul, tElt_wu]
      exact Subgroup.mul_mem _ (tElt_mem_closure_of K hq rfl hx hy huv ht)
        (Subgroup.subset_closure hwu)

@[expose] def IsU0c (p : Tc) : Prop := p.1.1 = 0

instance : DecidablePred IsU0c := fun p => by unfold IsU0c; infer_instance

theorem isU0c_tmul {p q : Tc} (hp : IsU0c p) (hq : IsU0c q) : IsU0c (tmul p q) := by
  simp only [IsU0c] at hp hq ⊢
  have := wpar_tmul p q
  simp only [wpar] at this
  rw [this, hp, hq, add_zero]

theorem isU0c_tinv {p : Tc} (hp : IsU0c p) : IsU0c (tinv p) := by
  simp only [IsU0c] at hp ⊢
  have := wpar_tinv p
  simp only [wpar] at this
  rw [this, hp]

@[expose] def U0sub : Subgroup X := tSub K IsU0c (by decide) isU0c_tmul isU0c_tinv

theorem card_isU0c : Fintype.card {p // IsU0c p} = 2 ^ 7 := by decide +kernel

theorem w_not_mem_U0sub : K.w ∉ U0sub K := by
  rw [← tElt_w, U0sub, tElt_mem_tSub_iff]
  decide

theorem U0sub_le_Tsub : U0sub K ≤ Tsub K := by
  rintro _ ⟨p, -, rfl⟩
  exact tElt_mem K p

theorem closure_u_eq : Subgroup.closure {K.x, K.y, K.uv, K.t, K.u} = U0sub K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by decide, tElt_x K⟩
    · exact ⟨_, by decide, tElt_y K⟩
    · exact ⟨_, by decide, tElt_gen_uv K⟩
    · exact ⟨_, by decide, tElt_gen_t K⟩
    · exact ⟨_, by decide, tElt_gen_u K⟩
  · rintro _ ⟨⟨v, a, b, c⟩, hp, rfl⟩
    simp only [IsU0c] at hp
    refine Subgroup.mul_mem _ (ev_mem_closure_xy K hp (by simp) (by simp)) ?_
    simp only [dElt]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

theorem ev_020 : K.ev (0, 2, 0) = K.x ^ 2 := by
  simp [Config.ev, show (2 : ZMod 4).val = 2 from rfl]
theorem ev_002 : K.ev (0, 0, 2) = K.y ^ 2 := by
  simp [Config.ev, show (2 : ZMod 4).val = 2 from rfl]
theorem ev_022 : K.ev (0, 2, 2) = K.x ^ 2 * K.y ^ 2 := by
  simp [Config.ev, show (2 : ZMod 4).val = 2 from rfl]

theorem w_ne_one : K.w ≠ 1 := by
  rw [← K.ev_w, Ne, K.ev_eq_one_iff]
  decide

theorem orderOf_w : orderOf K.w = 2 :=
  orderOf_eq_prime K.hw (w_ne_one K)

theorem tElt_mem_E_of_isEc {p : Tc} (hp : IsEc p) :
    tElt K p ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set X) := by
  obtain ⟨⟨i, j, l⟩, a, b, c⟩ := p
  obtain ⟨hi, hj, hl, hc⟩ := hp
  simp only at hi hj hl hc
  subst hi hc
  have hx2 : K.x ^ 2 ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set X) :=
    Subgroup.subset_closure (by simp)
  have hy2 : K.y ^ 2 ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set X) :=
    Subgroup.subset_closure (by simp)
  have hpx : K.x ^ j.val ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set X) := by
    rcases hj with rfl | rfl
    · simp
    · exact hx2
  have hpy : K.y ^ l.val ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set X) := by
    rcases hl with rfl | rfl
    · simp
    · exact hy2
  simp only [tElt, Config.ev, dElt, ZMod.val_zero, pow_zero, one_mul, mul_one]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hpx hpy)
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))

end Elements

end CFSG.CGT.Stroth76
