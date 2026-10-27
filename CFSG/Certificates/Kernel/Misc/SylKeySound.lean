module

public import Certificates.Data.Kernel.Misc.SylKey
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KC.SylKey

open CFSG.KS.PK

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem rd_eq (c i : Nat) : rd c i = fd 4 c i := by
  change (c >>> (4 * i)) &&& (2 ^ 4 - 1) = c / 2 ^ (4 * i) % 2 ^ 4
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem cdF_eq (f : Nat → Nat) : cdF f = enc 4 f 12 := by
  have e : ∀ a b : Nat, Nat.shiftLeft a b = a * 2 ^ b := fun a b => Nat.shiftLeft_eq a b
  have h1 : cdF f = f 0 + f 1 * 2 ^ 4 + f 2 * 2 ^ 8 + f 3 * 2 ^ 12 + f 4 * 2 ^ 16 +
      f 5 * 2 ^ 20 + f 6 * 2 ^ 24 + f 7 * 2 ^ 28 + f 8 * 2 ^ 32 + f 9 * 2 ^ 36 +
      f 10 * 2 ^ 40 + f 11 * 2 ^ 44 := by
    unfold cdF
    simp only [Nat.add_eq, e]
  rw [h1]
  simp only [enc_succ, enc_zero]
  ring

theorem fd_cd (σ : Equiv.Perm (Fin 12)) {i : Nat} (hi : i < 12) :
    fd 4 (cd σ) i = σ ⟨i, hi⟩ := by
  rw [cd, cdF_eq, fd_enc _ hi, dif_pos hi]
  intro j hj
  rw [dif_pos hj]
  exact (σ _).2.trans (by norm_num)

theorem cd_inj {σ τ : Equiv.Perm (Fin 12)} (h : cd σ = cd τ) : σ = τ := by
  ext i
  have h1 := fd_cd σ i.2
  rw [h, fd_cd τ i.2] at h1
  exact h1.symm

theorem mulK_cd (σ τ : Equiv.Perm (Fin 12)) : mulK (cd σ) (cd τ) = cd (σ * τ) := by
  have h1 : mulK (cd σ) (cd τ) = enc 4 (fun i => rd (cd σ) (rd (cd τ) i)) 12 := cdF_eq _
  have h2 : cd (σ * τ) =
      enc 4 (fun i => if h : i < 12 then ((σ * τ) ⟨i, h⟩ : Nat) else 0) 12 := cdF_eq _
  rw [h1, h2]
  apply enc_congr
  intro i hi
  rw [dif_pos hi, rd_eq, rd_eq, fd_cd τ hi, fd_cd σ (τ _).2, Equiv.Perm.mul_apply]

theorem idK_eq : cd 1 = idK := by decide +kernel

theorem pw_cd (σ : Equiv.Perm (Fin 12)) (e : Nat) : pw (cd σ) e = cd (σ ^ e) := by
  induction e with
  | zero => rw [pow_zero, idK_eq]; rfl
  | succ e ih =>
    change mulK (cd σ) (pw (cd σ) e) = _
    rw [ih, mulK_cd, pow_succ']

@[expose] def mnS (σ : Equiv.Perm (Fin 12)) : Nat → Nat
  | 0 => cd σ
  | t + 1 => min (mnS σ t) (cd (σ ^ (t + 2)))

theorem mnS_le (σ : Equiv.Perm (Fin 12)) (t : Nat) {j : Nat} (h1 : 1 ≤ j) (h2 : j ≤ t + 1) :
    mnS σ t ≤ cd (σ ^ j) := by
  induction t with
  | zero =>
    obtain rfl : j = 1 := by omega
    rw [pow_one]; exact le_rfl
  | succ t ih =>
    rcases Nat.lt_or_ge j (t + 2) with h | h
    · exact (min_le_left _ _).trans (ih (by omega))
    · obtain rfl : j = t + 2 := by omega
      exact min_le_right _ _

theorem mnS_mem (σ : Equiv.Perm (Fin 12)) (t : Nat) :
    ∃ j, 1 ≤ j ∧ j ≤ t + 1 ∧ mnS σ t = cd (σ ^ j) := by
  induction t with
  | zero => exact ⟨1, le_rfl, le_rfl, by rw [pow_one]; rfl⟩
  | succ t ih =>
    obtain ⟨j, h1, h2, h⟩ := ih
    rcases min_choice (mnS σ t) (cd (σ ^ (t + 2))) with hm | hm
    · refine ⟨j, h1, by omega, ?_⟩
      rw [mnS, hm, h]
    · refine ⟨t + 2, by omega, le_rfl, ?_⟩
      rw [mnS, hm]

theorem bmin (m y : Nat) : Bool.rec (motive := fun _ => Nat) y m (Nat.ble m y) = min m y := by
  by_cases hle : m ≤ y
  · rw [Nat.ble_eq_true_of_le hle, min_eq_left hle]
  · have h : Nat.ble m y = false := by
      cases h' : Nat.ble m y
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h') hle
    rw [h, min_eq_right (by omega)]

theorem kgo_spec (σ : Equiv.Perm (Fin 12)) (k : Nat) :
    ∀ s t, kgo (cd σ) k s (mnS σ t) (cd (σ ^ (t + 1))) = true →
      mnS σ (t + s) = k ∧ σ ^ (t + s + 2) = 1
  | 0, t, h => by
    change (Nat.beq (mnS σ t) k && Nat.beq (mulK (cd σ) (cd (σ ^ (t + 1)))) idK) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    refine ⟨h.1, cd_inj ?_⟩
    rw [mulK_cd, ← pow_succ'] at h
    rw [h.2, idK_eq]
  | s + 1, t, h => by
    change strictB (mulK (cd σ) (cd (σ ^ (t + 1)))) (fun y =>
      strictB (Bool.rec (motive := fun _ => Nat) y (mnS σ t) (Nat.ble (mnS σ t) y))
        fun m' => kgo (cd σ) k s m' y) = true at h
    rw [strictB_eq, strictB_eq, bmin, mulK_cd, ← pow_succ'] at h
    have := kgo_spec σ k s (t + 1) h
    rw [show t + 1 + s = t + (s + 1) by omega] at this
    exact this

theorem keyB_spec {p k : Nat} [hp : Fact p.Prime] {σ : Equiv.Perm (Fin 12)}
    (h : keyB p k (cd σ) = true) : orderOf σ = p ∧ mnS σ (p - 2) = k := by
  have h2 := hp.out.two_le
  rw [keyB, strictB_eq, Bool.and_eq_true] at h
  have h1 := kgo_spec σ k (p - 2) 0 (by rw [pow_one]; exact h.2)
  rw [zero_add, show p - 2 + 2 = p by omega] at h1
  refine ⟨orderOf_eq_prime h1.2 fun h0 => ?_, h1.1⟩
  have := h.1
  rw [h0, idK_eq] at this
  simp at this

theorem ordB_spec {p : Nat} [hp : Fact p.Prime] {σ : Equiv.Perm (Fin 12)}
    (h : ordB p (cd σ) = true) : orderOf σ = p := by
  unfold ordB at h
  rw [Bool.and_eq_true, pw_cd, Nat.beq_eq, ← idK_eq] at h
  refine orderOf_eq_prime (cd_inj h.2) fun h0 => ?_
  rw [h0] at h
  simp at h

theorem exists_pow_of_mem {τ x : Equiv.Perm (Fin 12)} {p : Nat} (ho : orderOf τ = p)
    (hx : x ∈ Subgroup.zpowers τ) (h1 : x ≠ 1) : ∃ i, 1 ≤ i ∧ i ≤ p - 1 ∧ x = τ ^ i := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ho, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  refine ⟨i, ?_, by omega, rfl⟩
  rcases Nat.eq_zero_or_pos i with rfl | h
  · exact absurd (pow_zero τ) h1
  · exact h

theorem mnS_le_of_zpowers {σ τ : Equiv.Perm (Fin 12)} {p : Nat} (h2 : 2 ≤ p)
    (hs : orderOf σ = p) (ht : orderOf τ = p) (h : Subgroup.zpowers σ = Subgroup.zpowers τ) :
    mnS τ (p - 2) ≤ mnS σ (p - 2) := by
  obtain ⟨j, hj1, hj2, hj⟩ := mnS_mem σ (p - 2)
  rw [hj]
  have hm : σ ^ j ∈ Subgroup.zpowers τ := h ▸ Subgroup.npow_mem_zpowers σ j
  have hne : σ ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  obtain ⟨i, hi1, hi2, hi⟩ := exists_pow_of_mem ht hm hne
  rw [hi]
  exact mnS_le τ (p - 2) hi1 (by omega)

theorem mnS_eq_of_zpowers {σ τ : Equiv.Perm (Fin 12)} {p : Nat} (h2 : 2 ≤ p)
    (hs : orderOf σ = p) (ht : orderOf τ = p) (h : Subgroup.zpowers σ = Subgroup.zpowers τ) :
    mnS σ (p - 2) = mnS τ (p - 2) :=
  le_antisymm (mnS_le_of_zpowers h2 ht hs h.symm) (mnS_le_of_zpowers h2 hs ht h)

theorem pinB_spec {T : Nat} : ∀ {L : List (Equiv.Perm (Fin 12))} {i0 : Nat},
    pinB T L i0 = true → ∀ j (hj : j < L.length), lk T (i0 + j) = cd L[j]
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | σ :: L, i0, h, j, hj => by
    change (Nat.beq (lk T i0) (cd σ) && pinB T L (Nat.succ i0)) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := pinB_spec h.2 j (by simpa using hj)
      rw [List.getElem_cons_succ, ← this, Nat.succ_eq_add_one]
      congr 1
      omega

theorem wB_spec {g0 g1 g2 T : Nat} : ∀ {W : List (List Nat)} {i0 : Nat},
    wB g0 g1 g2 T W i0 = true → ∀ j (hj : j < W.length), wev g0 g1 g2 W[j] = lk T (i0 + j)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | w :: W, i0, h, j, hj => by
    change (Nat.beq (wev g0 g1 g2 w) (lk T i0) && wB g0 g1 g2 T W (Nat.succ i0)) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := wB_spec h.2 j (by simpa using hj)
      rw [List.getElem_cons_succ, this, Nat.succ_eq_add_one]
      congr 1
      omega

theorem wev_spec {M : Subgroup (Equiv.Perm (Fin 12))} {a0 a1 a2 : Equiv.Perm (Fin 12)}
    (h0 : a0 ∈ M) (h1 : a1 ∈ M) (h2 : a2 ∈ M) :
    ∀ w : List Nat, ∃ σ ∈ M, wev (cd a0) (cd a1) (cd a2) w = cd σ
  | [] => ⟨1, M.one_mem, idK_eq.symm⟩
  | z :: w => by
    obtain ⟨σ, hσ, he⟩ := wev_spec h0 h1 h2 w
    have hg : ∃ a ∈ M, gK (cd a0) (cd a1) (cd a2) z = cd a := by
      unfold gK
      cases Nat.beq z 0
      · cases Nat.beq z 1
        · exact ⟨a2, h2, rfl⟩
        · exact ⟨a1, h1, rfl⟩
      · exact ⟨a0, h0, rfl⟩
    obtain ⟨a, ha, hga⟩ := hg
    refine ⟨a * σ, M.mul_mem ha hσ, ?_⟩
    change mulK (gK (cd a0) (cd a1) (cd a2) z) (wev (cd a0) (cd a1) (cd a2) w) = _
    rw [hga, he, mulK_cd]

theorem nrmB_spec {M : Subgroup (Equiv.Perm (Fin 12))} {a0 a1 a2 ρ : Equiv.Perm (Fin 12)}
    (h0 : a0 ∈ M) (h1 : a1 ∈ M) (h2 : a2 ∈ M) :
    ∀ {X : List (List Nat × Nat)} {prev : Nat},
      nrmB (cd a0) (cd a1) (cd a2) (cd ρ) X prev = true →
      ∃ xs : List (Equiv.Perm (Fin 12)), xs.length = X.length ∧ xs.Nodup ∧
        ∀ x ∈ xs, x ∈ M ∧ prev < cd x ∧ ∃ e : Nat, x * ρ = ρ ^ e * x
  | [], _, _ => ⟨[], rfl, List.nodup_nil, by simp⟩
  | xe :: X, prev, h => by
    obtain ⟨σ, hσ, he⟩ := wev_spec h0 h1 h2 xe.1
    change strictB (wev (cd a0) (cd a1) (cd a2) xe.1) (fun x => Bool.and (Nat.blt prev x)
      (Bool.and (Nat.beq (mulK x (cd ρ)) (mulK (pw (cd ρ) xe.2) x))
        (nrmB (cd a0) (cd a1) (cd a2) (cd ρ) X x))) = true at h
    rw [strictB_eq, he] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨hlt, hc, hrest⟩ := h
    obtain ⟨xs, hl, hnd, hxs⟩ := nrmB_spec h0 h1 h2 hrest
    refine ⟨σ :: xs, by simp [hl], List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, ?_⟩
    · exact absurd (hxs σ hm).2.1 (lt_irrefl _)
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · refine ⟨hσ, hlt, xe.2, cd_inj ?_⟩
        rw [← mulK_cd, ← mulK_cd, ← pw_cd]
        exact hc
      · obtain ⟨hm, hl', he'⟩ := hxs x hx
        exact ⟨hm, hlt.trans hl', he'⟩

theorem allE_spec {p NT NIT RT : Nat} [hp : Fact p.Prime] {Ns Rs : List (Equiv.Perm (Fin 12))}
    (hN : ∀ i < 54, ∃ n ∈ Ns, lk NT i = cd n ∧ lk NIT i = cd n⁻¹)
    (hR : ∀ j < 80, ∃ r ∈ Rs, lk RT j = cd r) :
    ∀ {E : List (Nat × Nat)} {prev : Nat}, allE p NT NIT RT E prev = true →
      ∃ cs : List (Equiv.Perm (Fin 12)), cs.length = E.length ∧
        (cs.map Subgroup.zpowers).Nodup ∧
        ∀ c ∈ cs, orderOf c = p ∧ prev < mnS c (p - 2) ∧ ∃ n ∈ Ns, ∃ r ∈ Rs, c = n * r * n⁻¹
  | [], _, _ => ⟨[], rfl, List.nodup_nil, by simp⟩
  | e :: E, prev, h => by
    change (Nat.blt prev e.2 && (entB p NT NIT RT e && allE p NT NIT RT E e.2)) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hlt, he, hrest⟩ := h
    unfold entB at he
    simp only [Bool.and_eq_true, Nat.blt_eq] at he
    obtain ⟨hi, hj, hk⟩ := he
    obtain ⟨n, hn, hn1, hn2⟩ := hN _ hi
    obtain ⟨r, hr, hr1⟩ := hR _ hj
    rw [hn1, hn2, hr1, mulK_cd, mulK_cd] at hk
    obtain ⟨ho, hkey⟩ := keyB_spec hk
    obtain ⟨cs, hl, hnd, hcs⟩ := allE_spec hN hR hrest
    refine ⟨n * (r * n⁻¹) :: cs, by simp [hl], ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, hnd⟩
      obtain ⟨c, hc, hz⟩ := List.mem_map.1 hm
      have h3 := mnS_eq_of_zpowers hp.out.two_le (hcs c hc).1 ho hz
      have h4 := (hcs c hc).2.1
      omega
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · refine ⟨ho, by rw [hkey]; exact hlt, n, hn, r, hr, by rw [mul_assoc]⟩
      · obtain ⟨h1, h2, h3⟩ := hcs c hc
        exact ⟨h1, hlt.trans h2, h3⟩

theorem mem_normalizer_zpowers {G : Type*} [Group G] [Finite G] {r x : G} {e : Nat}
    (h : x * r = r ^ e * x) : x ∈ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
  have hc : MulAut.conj x r = r ^ e := by
    rw [MulAut.conj_apply, h, mul_inv_cancel_right]
  have hle : (Subgroup.zpowers r).map (MulAut.conj x).toMonoidHom ≤ Subgroup.zpowers r := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by
      change MulAut.conj x r ∈ _
      rw [hc]
      exact Subgroup.npow_mem_zpowers r e)
  have heq : (Subgroup.zpowers r).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers r :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : MulAut.conj x y ∈ (Subgroup.zpowers r).map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hy
    rw [heq, MulAut.conj_apply] at this
    exact this
  · intro hy
    rw [← heq] at hy
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.1 hy
    change MulAut.conj x y' = x * y * x⁻¹ at hyy
    rw [MulAut.conj_apply] at hyy
    have : y' = y := by simpa using hyy
    rwa [← this]

theorem sylow_cover {K : Type*} [Group K] (H : Subgroup K) [Finite H] {p : ℕ}
    [hp : Fact p.Prime] (hH : ¬ p ^ 2 ∣ Nat.card H) {r : K} (hr : r ∈ H) (hro : orderOf r = p)
    {X : List K} (hXH : ∀ x ∈ X, x ∈ H) (hXn : ∀ x ∈ X, ∃ e : ℕ, x * r = r ^ e * x)
    (hXd : X.Nodup) {cs : List K} (hcH : ∀ c ∈ cs, c ∈ H) (hco : ∀ c ∈ cs, orderOf c = p)
    (hcd : (cs.map Subgroup.zpowers).Nodup) (hcard : Nat.card H ≤ cs.length * X.length)
    {g : K} (hg : g ∈ H) (hgo : orderOf g = p) :
    ∃ c ∈ cs, Subgroup.zpowers c = Subgroup.zpowers g := by
  classical
  have hne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card H).factorization p = 1 := by
    have hdvd : p ∣ Nat.card H := by
      rw [← hgo, ← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _
    have h1 : 1 ≤ (Nat.card H).factorization p :=
      (hp.out.pow_dvd_iff_le_factorization hne).1 (by rwa [pow_one])
    have h2 : ¬ 2 ≤ (Nat.card H).factorization p :=
      fun h => hH ((hp.out.pow_dvd_iff_le_factorization hne).2 h)
    omega
  have hcardz : ∀ (x : K) (hx : x ∈ H), orderOf x = p →
      Nat.card (Subgroup.zpowers (⟨x, hx⟩ : H)) = p ^ (Nat.card H).factorization p := by
    intro x hx ho
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ho, hfac, pow_one]
  have hsyl : ∀ (x : K) (hx : x ∈ H) (ho : orderOf x = p),
      ((Sylow.ofCard _ (hcardz x hx ho) : Subgroup H).map H.subtype) =
        Subgroup.zpowers x := by
    intro x hx ho
    change (Subgroup.zpowers (⟨x, hx⟩ : H)).map H.subtype = _
    rw [MonoidHom.map_zpowers]
    rfl
  have : Fintype (Sylow p H) := Fintype.ofFinite _
  let φ : Sylow p H → Subgroup K := fun P => (P : Subgroup H).map H.subtype
  let A : Finset (Subgroup K) := (cs.map Subgroup.zpowers).toFinset
  have hA : A.card = cs.length := by
    rw [List.toFinset_card_of_nodup hcd, List.length_map]
  have hAsub : A ⊆ Finset.univ.image φ := by
    intro Q hQ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hQ)
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, hsyl c (hcH c hc) (hco c hc)⟩
  let P0 := Sylow.ofCard _ (hcardz r hr hro)
  let N := Subgroup.normalizer ((P0 : Subgroup H) : Set H)
  have hN : X.length ≤ Nat.card N := by
    have hsub : (X.toFinset : Set K) ⊆ ((N.map H.subtype : Subgroup K) : Set K) := by
      intro x hx
      have hx' := List.mem_toFinset.1 (Finset.mem_coe.1 hx)
      obtain ⟨e, he⟩ := hXn x hx'
      refine Subgroup.mem_map.2 ⟨⟨x, hXH x hx'⟩, ?_, rfl⟩
      change _ ∈ Subgroup.normalizer (Subgroup.zpowers (⟨r, hr⟩ : H) : Set H)
      apply mem_normalizer_zpowers (e := e)
      exact Subtype.ext (by simpa using he)
    have hfin : ((N.map H.subtype : Subgroup K) : Set K).Finite := by
      rw [Subgroup.coe_map]
      exact (Set.toFinite _).image _
    have h1 := Nat.card_mono hfin hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hXd] at h1
    rw [← Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective]
    exact h1
  have hidx : Fintype.card (Sylow p H) ≤ cs.length := by
    rw [← Nat.card_eq_fintype_card, P0.card_eq_index_normalizer]
    have h1 := N.index_mul_card
    have hpos : 0 < Nat.card N := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc N.index * Nat.card N = Nat.card H := h1
      _ ≤ cs.length * X.length := hcard
      _ ≤ cs.length * Nat.card N := Nat.mul_le_mul_left _ hN
  have hAeq : A = Finset.univ.image φ :=
    Finset.eq_of_subset_of_card_le hAsub (by
      rw [hA]
      exact (Finset.card_image_le).trans (by rw [Finset.card_univ]; exact hidx))
  have hgA : Subgroup.zpowers g ∈ A := by
    rw [hAeq]
    exact Finset.mem_image.2 ⟨_, Finset.mem_univ _, hsyl g hg hgo⟩
  obtain ⟨c, hc, hz⟩ := List.mem_map.1 (List.mem_toFinset.1 hgA)
  exact ⟨c, hc, hz⟩

end CFSG.KC.SylKey

end
