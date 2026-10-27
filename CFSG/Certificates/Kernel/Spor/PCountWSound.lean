module

public import Certificates.Data.Kernel.Spor.PCountW
public import CFSG.Certificates.Kernel.Spor.PCountSound

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum CFSG.KS.PK CFSG.Sporadic.Schreier

variable {n w : Nat}

@[expose] def pkw (w : Nat) (σ : Equiv.Perm (Fin n)) : Nat := enc w (pv σ) n

theorem pv_lt_w (hw : n ≤ 2 ^ w) (σ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) :
    pv σ x < 2 ^ w :=
  lt_of_lt_of_le (pv_lt σ hx) hw

theorem fd_pkw (hw : n ≤ 2 ^ w) (σ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) :
    fd w (pkw w σ) x = pv σ x :=
  fd_enc (fun _ hi => pv_lt_w hw σ hi) hx

theorem pkw_lt (hw : n ≤ 2 ^ w) (σ : Equiv.Perm (Fin n)) : pkw w σ < 2 ^ (w * n) :=
  enc_lt (fun _ hi => pv_lt_w hw σ hi)

theorem pkw_mul (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (σ τ : Equiv.Perm (Fin n)) :
    pcomp n w (mask w) (pkw w σ) (pkw w τ) = pkw w (σ * τ) := by
  refine eq_of_fd_eq (pcomp_lt h32 w _ _) (pkw_lt hw _) fun i hi => ?_
  rw [fd_pcomp h32 w _ _ hi, fd_pkw hw τ hi, fd_pkw hw σ (pv_lt τ hi), fd_pkw hw _ hi,
    pv_mul _ _ hi]

theorem pkw_inj (hw : n ≤ 2 ^ w) {σ τ : Equiv.Perm (Fin n)} (h : pkw w σ = pkw w τ) : σ = τ := by
  refine Equiv.ext fun i => Fin.ext ?_
  have h1 := congrArg (fun x => fd w x i) h
  simp only [fd_pkw hw _ i.isLt, pv, i.isLt, ↓reduceDIte] at h1
  exact h1

theorem beq_pkw_iff (hw : n ≤ 2 ^ w) {σ τ : Equiv.Perm (Fin n)} :
    Nat.beq (pkw w σ) (pkw w τ) = true ↔ σ = τ := by
  rw [Nat.beq_eq]
  exact ⟨pkw_inj hw, fun h => h ▸ rfl⟩

theorem pkw_ppw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (σ : Equiv.Perm (Fin n)) (k : Nat) :
    ppw n w (mask w) (pkw w σ) k = pkw w (σ ^ (k + 1)) := by
  induction k with
  | zero => rw [pow_one]; rfl
  | succ k ih =>
    have h : ppw n w (mask w) (pkw w σ) (k + 1) =
        strictN (ppw n w (mask w) (pkw w σ) k) (fun y => pcomp n w (mask w) (pkw w σ) y) := rfl
    rw [h, strictN_eq, ih, pkw_mul hw h32, ← pow_succ']

variable {G : Type*} [Group G]

theorem orderOf_eq_four_iff' (g : G) : orderOf g = 4 ↔ g * g ≠ 1 ∧ g * g * (g * g) = 1 := by
  have e2 : g * g = g ^ 2 := (pow_two g).symm
  have e4 : g * g * (g * g) = g ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4, e2]
  constructor
  · intro h
    refine ⟨fun h2 => ?_, h ▸ pow_orderOf_eq_one g⟩
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h] at this
    omega
  · rintro ⟨h2, h4⟩
    have hd := orderOf_dvd_of_pow_eq_one h4
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : orderOf g
    · norm_num at hd
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h]; norm_num)) h2
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h])) h2
    · norm_num at hd
    · rfl

theorem orderOf_eq_prime_iff' {p : Nat} (hp : p.Prime) (g : G) :
    orderOf g = p ↔ g ≠ 1 ∧ g ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [orderOf_eq_prime_iff, and_comm]

theorem ordTwo_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (σ : Equiv.Perm (Fin n)) :
    ordTwo n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w σ) =
      if orderOf σ = 2 then 1 else 0 := by
  unfold ordTwo
  rw [pkw_mul hw h32]
  simp only [nIf_eq, beq_pkw_iff hw]
  by_cases h1 : σ = 1
  · simp [h1]
  · by_cases h2 : σ * σ = 1
    · simp [h1, h2, (orderOf_eq_two_iff' σ).2 ⟨h1, h2⟩]
    · have h : orderOf σ ≠ 2 := fun h => h2 ((orderOf_eq_two_iff' σ).1 h).2
      simp [h1, h2, h]

theorem ordFour_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (σ : Equiv.Perm (Fin n)) :
    ordFour n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w σ) =
      if orderOf σ = 4 then 1 else 0 := by
  unfold ordFour
  rw [pkw_mul hw h32, strictN_eq, pkw_mul hw h32]
  simp only [nIf_eq, beq_pkw_iff hw]
  have e := orderOf_eq_four_iff' σ
  by_cases h2 : σ * σ = 1 <;> by_cases h4 : σ * σ * (σ * σ) = 1 <;> simp_all

theorem ordPr_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) {k : Nat} (hk : (k + 1).Prime)
    (σ : Equiv.Perm (Fin n)) :
    ordPr n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w σ) k =
      if orderOf σ = k + 1 then 1 else 0 := by
  unfold ordPr
  rw [pkw_ppw hw h32]
  simp only [nIf_eq, beq_pkw_iff hw]
  have e := orderOf_eq_prime_iff' hk σ
  by_cases h1 : σ = 1 <;> by_cases hp : σ ^ (k + 1) = 1 <;> simp_all

theorem ordSix_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (σ : Equiv.Perm (Fin n)) :
    ordSix n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w σ) =
      if orderOf σ = 6 then 1 else 0 := by
  unfold ordSix
  rw [pkw_ppw hw h32, pkw_ppw hw h32, pkw_ppw hw h32]
  simp only [nIf_eq, beq_pkw_iff hw]
  have e := orderOf_eq_six_iff' σ
  by_cases h6 : σ ^ (5 + 1) = 1 <;> by_cases h2 : σ ^ (1 + 1) = 1 <;>
    by_cases h3 : σ ^ (2 + 1) = 1 <;> simp_all

@[expose] def PartnerW (x y : Equiv.Perm (Fin n)) : Prop :=
  orderOf y = 4 ∧ orderOf (x * y * y) = 5 ∧ orderOf (x * y) = 11 ∧
    orderOf (x * y * x⁻¹ * y⁻¹) = 6

noncomputable instance (x y : Equiv.Perm (Fin n)) : Decidable (PartnerW x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem partnerW_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) {x : Equiv.Perm (Fin n)}
    (hx : orderOf x = 2) (y : Equiv.Perm (Fin n)) :
    partnerW n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w x) (pkw w y) =
      if PartnerW x y then 1 else 0 := by
  unfold partnerW PartnerW
  rw [ordFour_pkw hw h32]
  by_cases hy : orderOf y = 4
  · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right ((orderOf_eq_two_iff' x).1 hx).2
    have hyi : y⁻¹ = y * y * y :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← mul_assoc]; exact
        (by simpa [mul_assoc] using ((orderOf_eq_four_iff' y).1 hy).2))
    simp only [hy, ↓reduceIte, nIf_eq, strictN_eq, Nat.beq_refl]
    rw [pkw_mul hw h32 x y, pkw_mul hw h32 (x * y) y, ordPr_pkw hw h32 (k := 4) Nat.prime_five,
      ordPr_pkw hw h32 (k := 10) Nat.prime_eleven, pkw_mul hw h32 (x * y) x, pkw_mul hw h32 y y,
      pkw_mul hw h32 (y * y) y, pkw_mul hw h32 (x * y * x) (y * y * y), ordSix_pkw hw h32, hxi, hyi]
    have hc : x * y * x * (y * y * y) = x * y * x * (y * y * y) := rfl
    by_cases h5 : orderOf (x * y * y) = 5 <;> by_cases h11 : orderOf (x * y) = 11 <;>
      by_cases h6 : orderOf (x * y * x * (y * y * y)) = 6 <;> simp_all [mul_assoc]
  · simp [hy]

theorem cntW_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) {x : Equiv.Perm (Fin n)}
    (hx : orderOf x = 2) (y : Equiv.Perm (Fin n)) :
    cntW n w (mask w) (pkw w (1 : Equiv.Perm (Fin n))) (pkw w x) (pkw w y) =
      (if orderOf y = 2 then 1 else 0) + 1048576 * (if PartnerW x y then 1 else 0) := by
  unfold cntW
  rw [ordTwo_pkw hw h32, partnerW_pkw hw h32 hx]
  simp only [Nat.add_eq, Nat.mul_eq]

theorem pcnt_pkw (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (F : Nat → Nat) :
    ∀ (Ts : List (List (Equiv.Perm (Fin n)))) (g : Equiv.Perm (Fin n)) (acc : Nat),
      pcnt n w (mask w) F (Ts.map fun T => T.map (pkw w)) (pkw w g) acc =
        acc + ((products Ts).map fun h => F (pkw w (g * h))).sum
  | [], g, acc => by
    rw [List.map_nil, pcnt_nil]
    simp [products]
  | T :: Ts, g, acc => by
    rw [List.map_cons, pcnt_cons]
    induction T generalizing acc with
    | nil => simp [pRow_nil, products]
    | cons t T ih =>
      rw [List.map_cons, pRow_cons, pkw_mul hw h32, pcnt_pkw hw h32 F Ts (g * t) acc, ih]
      simp only [products, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, mul_assoc]
      omega

theorem sum_products_slices {M : Type*} [Monoid M] (f : M → Nat) (rest : List (List M))
    (k : Nat) : ∀ (S : Nat) (T : List M), T.length ≤ k * S →
      ((products (T :: rest)).map f).sum =
        ((List.range S).map fun j => ((products (((T.drop (k * j)).take k) :: rest)).map f).sum).sum
  | 0, T, hT => by
    have : T = [] := List.eq_nil_of_length_eq_zero (by simpa using hT)
    subst this
    simp [products]
  | S + 1, T, hT => by
    have hsplit : T = T.take k ++ T.drop k := (List.take_append_drop k T).symm
    rw [hsplit, products_append_head, List.map_append, List.sum_append,
      sum_products_slices f rest k S (T.drop k) (by rw [List.length_drop]; rw [Nat.mul_succ] at hT; omega),
      List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    congr 1
    · simp
    · congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, List.drop_drop, List.take_append_drop]
      rw [Nat.mul_succ, Nat.add_comm]

theorem products_fix {Ts : List (List (Equiv.Perm (Fin n)))} {b : Fin n}
    (h : ∀ T ∈ Ts, ∀ t ∈ T, t b = b) : ∀ g ∈ products Ts, g b = b := by
  intro g hg
  have := mem_of_mem_products (MulAction.stabilizer (Equiv.Perm (Fin n)) b).toSubmonoid Ts
    (fun T hT t ht => MulAction.mem_stabilizer_iff.2 (h T hT t ht)) g hg
  exact MulAction.mem_stabilizer_iff.1 this

theorem products_nodup_of_baseOK :
    ∀ {Ts : List (List (Equiv.Perm (Fin n)))} {bs : List (Fin n)}, baseOK Ts bs = true →
      (products Ts).Nodup
  | [], [], _ => by simp [products]
  | [], _ :: _, h => by simp [baseOK] at h
  | _ :: _, [], h => by simp [baseOK] at h
  | T :: Ts, b :: bs, h => by
    simp only [baseOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨hnd, hfix⟩, hrest⟩ := h
    have ih := products_nodup_of_baseOK hrest
    have hfixP := products_fix hfix
    rw [products, List.nodup_flatMap]
    refine ⟨fun t _ => ih.map (mul_right_injective t), ?_⟩
    refine (List.pairwise_map.1 hnd).imp fun {t t'} hne => ?_
    rw [Function.onFun, List.disjoint_left]
    intro g hg hg'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hg
    obtain ⟨u', hu', he⟩ := List.mem_map.1 hg'
    apply hne
    have h1 := congrArg (fun g : Equiv.Perm (Fin n) => g b) he
    simp only [Equiv.Perm.mul_apply, hfixP u hu, hfixP u' hu'] at h1
    exact h1.symm

theorem mem_iff_of_nodup_card {M : Type*} [Group M] (H : Subgroup M) [Finite H] {L : List M}
    (hL : L.Nodup) (hsub : ∀ g ∈ L, g ∈ H) (hlen : Nat.card H ≤ L.length) :
    ∀ g, g ∈ L ↔ g ∈ H := by
  classical
  intro g
  refine ⟨hsub g, fun hg => ?_⟩
  by_contra hgL
  have hnd : (g :: L).Nodup := List.nodup_cons.2 ⟨hgL, hL⟩
  have hsub' : ∀ x ∈ g :: L, x ∈ H := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hg
    · exact hsub x hx
  have : Fintype H := Fintype.ofFinite H
  have h1 := (List.Nodup.pmap (f := fun x hx => (⟨x, hx⟩ : H)) (H := hsub')
    (fun _ _ _ _ h => congrArg Subtype.val h) hnd).length_le_card
  rw [List.length_pmap, List.length_cons, ← Nat.card_eq_fintype_card] at h1
  omega

private def DInv (P : Nat → Prop) (s : DState) : Prop :=
  s.1.Nodup ∧ (∀ k ∈ s.1, P k) ∧ ∀ k ∈ s.2, P k

private theorem dAdd_inv {P : Nat → Prop} {z : Nat} {s : DState} (hz : P z) (hs : DInv P s) :
    DInv P (dAdd z s) := by
  unfold dAdd dIf
  cases hm : memB z s.1 with
  | true => exact hs
  | false =>
    have hz' : z ∉ s.1 := fun h => by rw [(memB_iff z s.1).2 h] at hm; exact Bool.noConfusion hm
    refine ⟨List.nodup_cons.2 ⟨hz', hs.1⟩, fun k hk => ?_, fun k hk => ?_⟩
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hz
      · exact hs.2.1 k hk
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hz
      · exact hs.2.2 k hk

private theorem dStep_inv {P : Nat → Prop} {n w m A Ai B Bi : Nat}
    (hA : ∀ k, P k → P (cjP n w m A Ai k)) (hB : ∀ k, P k → P (cjP n w m B Bi k)) :
    ∀ {s : DState}, DInv P s → DInv P (dStep n w m A Ai B Bi s)
  | (K, []), hs => hs
  | (K, e :: rest), hs => by
    have he : P e := hs.2.2 e List.mem_cons_self
    change DInv P (dAdd (cjP n w m B Bi e) (dAdd (cjP n w m A Ai e) (K, rest)))
    exact dAdd_inv (hB e he) (dAdd_inv (hA e he)
      ⟨hs.1, hs.2.1, fun k hk => hs.2.2 k (List.mem_cons_of_mem e hk)⟩)

theorem conjDFS_spec {P : Nat → Prop} {n w m A Ai B Bi r : Nat} (hr : P r)
    (hA : ∀ k, P k → P (cjP n w m A Ai k)) (hB : ∀ k, P k → P (cjP n w m B Bi k)) (fuel : Nat) :
    (conjDFS n w m A Ai B Bi r fuel).Nodup ∧ ∀ k ∈ conjDFS n w m A Ai B Bi r fuel, P k := by
  have h : DInv P (Nat.rec (motive := fun _ => DState) ([r], [r])
      (fun _ ih => dStep n w m A Ai B Bi ih) fuel) := by
    induction fuel with
    | zero =>
      refine ⟨List.nodup_singleton r, fun k hk => ?_, fun k hk => ?_⟩ <;>
        · rw [List.mem_singleton.1 hk]
          exact hr
    | succ fuel ih => exact dStep_inv hA hB ih
  exact ⟨h.1, h.2.1⟩

theorem conjDFS_mem_w (hw : n ≤ 2 ^ w) (h32 : n < 2 ^ 32) (H : Subgroup (Equiv.Perm (Fin n)))
    {a b ρ : Equiv.Perm (Fin n)} (ha : a ∈ H) (hb : b ∈ H) (fuel : Nat) :
    (conjDFS n w (mask w) (pkw w a) (pkw w a⁻¹) (pkw w b) (pkw w b⁻¹) (pkw w ρ) fuel).Nodup ∧
      ∀ k ∈ conjDFS n w (mask w) (pkw w a) (pkw w a⁻¹) (pkw w b) (pkw w b⁻¹) (pkw w ρ) fuel,
        ∃ c ∈ H, k = pkw w (c * ρ * c⁻¹) := by
  have hstep : ∀ g ∈ H, ∀ k, (∃ c ∈ H, k = pkw w (c * ρ * c⁻¹)) →
      ∃ c ∈ H, cjP n w (mask w) (pkw w g) (pkw w g⁻¹) k = pkw w (c * ρ * c⁻¹) := by
    rintro g hg k ⟨c, hc, rfl⟩
    refine ⟨g * c, H.mul_mem hg hc, ?_⟩
    rw [cjP, pkw_mul hw h32, pkw_mul hw h32]
    group
  exact conjDFS_spec ⟨1, H.one_mem, by simp⟩ (hstep a ha) (hstep b hb) fuel

@[expose] noncomputable def upkw (n w : Nat) (x : Nat) : Equiv.Perm (Fin n) := permOf n (fd w x)

theorem upkw_pkw (hw : n ≤ 2 ^ w) (σ : Equiv.Perm (Fin n)) : upkw n w (pkw w σ) = σ := by
  rw [upkw, permOf_congr (g := fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x)
    (fun x hx => by rw [fd_pkw hw σ hx]; rfl)]
  exact permOf_val σ

theorem upkw_conj (hw : n ≤ 2 ^ w) {H : Subgroup (Equiv.Perm (Fin n))} {ρ : Equiv.Perm (Fin n)}
    {K : List Nat} (hK : ∀ k ∈ K, ∃ c ∈ H, k = pkw w (c * ρ * c⁻¹)) :
    (∀ y ∈ K.map (upkw n w), ∃ c ∈ H, y = c * ρ * c⁻¹) ∧ (K.map (upkw n w)).map (pkw w) = K := by
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    obtain ⟨c, hc, rfl⟩ := hK k hk
    exact ⟨c, hc, upkw_pkw hw _⟩
  · rw [List.map_map]
    conv_rhs => rw [← List.map_id K]
    refine List.map_congr_left fun k hk => ?_
    obtain ⟨c, hc, rfl⟩ := hK k hk
    rw [Function.comp_apply, upkw_pkw hw, id]

end CFSG.KS.PCnt

end
