module

public import Certificates.Data.Kernel.Spor.PCount
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Comp
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Make
public import CFSG.Sporadic.Schreier.Enumeration
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KS.PCnt

open CFSG.KC.Enum CFSG.KS.PK CFSG.Sporadic.Schreier

variable {n : Nat}

@[expose] def pv (σ : Equiv.Perm (Fin n)) (x : Nat) : Nat :=
  if h : x < n then (σ ⟨x, h⟩ : Nat) else x

@[expose] def pk (σ : Equiv.Perm (Fin n)) : Nat := enc 4 (pv σ) n

theorem pv_lt (σ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) : pv σ x < n := by
  simp only [pv, hx, ↓reduceDIte]
  exact (σ ⟨x, hx⟩).isLt

theorem pv_lt_pow (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) :
    pv σ x < 2 ^ 4 := by
  have := pv_lt σ hx
  omega

theorem fd_pk (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) :
    fd 4 (pk σ) x = pv σ x :=
  fd_enc (fun _ hi => pv_lt_pow hn σ hi) hx

theorem pk_lt (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) : pk σ < 2 ^ (4 * n) :=
  enc_lt (fun _ hi => pv_lt_pow hn σ hi)

theorem pv_mul (σ τ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) :
    pv (σ * τ) x = pv σ (pv τ x) := by
  simp only [pv, hx, (τ ⟨x, hx⟩).isLt, ↓reduceDIte, Equiv.Perm.mul_apply]

theorem pk_mul (hn : n ≤ 16) (σ τ : Equiv.Perm (Fin n)) :
    pcomp n 4 (mask 4) (pk σ) (pk τ) = pk (σ * τ) := by
  have hn32 : n < 2 ^ 32 := by omega
  refine eq_of_fd_eq (pcomp_lt hn32 4 _ _) (pk_lt hn _) fun i hi => ?_
  rw [fd_pcomp hn32 4 _ _ hi, fd_pk hn τ hi, fd_pk hn σ (pv_lt τ hi), fd_pk hn _ hi,
    pv_mul _ _ hi]

theorem pk_one (hn : n ≤ 16) : pk (1 : Equiv.Perm (Fin n)) = pidn n 4 := by
  rw [pidn_eq (by omega) (by omega)]
  exact enc_congr fun i hi => by simp [pv, hi]

theorem pk_inj (hn : n ≤ 16) {σ τ : Equiv.Perm (Fin n)} (h : pk σ = pk τ) : σ = τ := by
  refine Equiv.ext fun i => Fin.ext ?_
  have h1 := congrArg (fun x => fd 4 x i) h
  simp only [fd_pk hn _ i.isLt, pv, i.isLt, ↓reduceDIte] at h1
  exact h1

theorem beq_pk_iff (hn : n ≤ 16) {σ τ : Equiv.Perm (Fin n)} :
    Nat.beq (pk σ) (pk τ) = true ↔ σ = τ := by
  rw [Nat.beq_eq]
  exact ⟨pk_inj hn, fun h => h ▸ rfl⟩

theorem pk_ppw (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) (k : Nat) :
    ppw n 4 (mask 4) (pk σ) k = pk (σ ^ (k + 1)) := by
  induction k with
  | zero => rw [pow_one]; rfl
  | succ k ih =>
    have h : ppw n 4 (mask 4) (pk σ) (k + 1) =
        strictN (ppw n 4 (mask 4) (pk σ) k) (fun y => pcomp n 4 (mask 4) (pk σ) y) := rfl
    rw [h, strictN_eq, ih, pk_mul hn, ← pow_succ']

variable {G : Type*} [Group G]

theorem orderOf_eq_two_iff' (g : G) : orderOf g = 2 ↔ g ≠ 1 ∧ g * g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, pow_two, and_comm]

theorem orderOf_eq_three_iff' (g : G) : orderOf g = 3 ↔ g ≠ 1 ∧ g * (g * g) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_eq_prime_iff, pow_three, and_comm]

theorem orderOf_eq_eleven_iff' (g : G) : orderOf g = 11 ↔ g ≠ 1 ∧ g ^ 11 = 1 := by
  have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  rw [orderOf_eq_prime_iff, and_comm]

theorem orderOf_eq_six_iff' (g : G) :
    orderOf g = 6 ↔ g ^ 6 = 1 ∧ g ^ 2 ≠ 1 ∧ g ^ 3 ≠ 1 := by
  constructor
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one g, fun h2 => ?_, fun h3 => ?_⟩
    · have := orderOf_dvd_of_pow_eq_one h2
      rw [h] at this
      omega
    · have := orderOf_dvd_of_pow_eq_one h3
      rw [h] at this
      omega
  · rintro ⟨h6, h2, h3⟩
    have hd := orderOf_dvd_of_pow_eq_one h6
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : orderOf g
    · norm_num at hd
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h]; norm_num)) h2
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h])) h2
    · exact absurd (orderOf_dvd_iff_pow_eq_one.1 (by rw [h])) h3
    · norm_num at hd
    · norm_num at hd
    · rfl

theorem ordTwo_pk (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) :
    ordTwo n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk σ) =
      if orderOf σ = 2 then 1 else 0 := by
  unfold ordTwo
  rw [pk_mul hn]
  simp only [nIf_eq, beq_pk_iff hn]
  by_cases h1 : σ = 1
  · simp [h1]
  · by_cases h2 : σ * σ = 1
    · simp [h1, h2, (orderOf_eq_two_iff' σ).2 ⟨h1, h2⟩]
    · have h : orderOf σ ≠ 2 := fun h => h2 ((orderOf_eq_two_iff' σ).1 h).2
      simp [h1, h2, h]

theorem ordThree_pk (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) :
    ordThree n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk σ) =
      if orderOf σ = 3 then 1 else 0 := by
  unfold ordThree
  rw [pk_mul hn, pk_mul hn]
  simp only [nIf_eq, beq_pk_iff hn]
  by_cases h1 : σ = 1
  · simp [h1]
  · by_cases h2 : σ * (σ * σ) = 1
    · simp [h1, h2, (orderOf_eq_three_iff' σ).2 ⟨h1, h2⟩]
    · have h : orderOf σ ≠ 3 := fun h => h2 ((orderOf_eq_three_iff' σ).1 h).2
      simp [h1, h2, h]

theorem ordSix_pk (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) :
    ordSix n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk σ) =
      if orderOf σ = 6 then 1 else 0 := by
  unfold ordSix
  rw [pk_ppw hn, pk_ppw hn, pk_ppw hn]
  simp only [nIf_eq, beq_pk_iff hn]
  have e := orderOf_eq_six_iff' σ
  by_cases h6 : σ ^ (5 + 1) = 1 <;> by_cases h2 : σ ^ (1 + 1) = 1 <;>
    by_cases h3 : σ ^ (2 + 1) = 1 <;> simp_all

theorem partner_pk (hn : n ≤ 16) {x : Equiv.Perm (Fin n)} (hx : orderOf x = 2)
    (y : Equiv.Perm (Fin n)) :
    partner n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) (pk y) =
      if orderOf y = 3 ∧ orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6 then 1 else 0 := by
  unfold partner
  rw [ordThree_pk hn]
  by_cases hy : orderOf y = 3
  · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right ((orderOf_eq_two_iff' x).1 hx).2
    have hyi : y⁻¹ = y * y := inv_eq_of_mul_eq_one_right ((orderOf_eq_three_iff' y).1 hy).2
    simp only [hy, ↓reduceIte, nIf_eq, strictN_eq]
    rw [pk_mul hn x y, pk_ppw hn, pk_mul hn (x * y) x, pk_mul hn y y, pk_mul hn (x * y * x) (y * y),
      ordSix_pk hn, hxi, hyi]
    simp only [beq_pk_iff hn, Nat.beq_refl, ↓reduceIte, true_and]
    have e := orderOf_eq_eleven_iff' (x * y)
    by_cases h1 : x * y = 1 <;> by_cases h11 : (x * y) ^ (10 + 1) = 1 <;> simp_all
  · simp [hy]

theorem cnt4_pk (hn : n ≤ 16) {x₁ x₂ : Equiv.Perm (Fin n)} (h₁ : orderOf x₁ = 2)
    (h₂ : orderOf x₂ = 2) (y : Equiv.Perm (Fin n)) :
    cnt4 n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x₁) (pk x₂) (pk y) =
      (if orderOf y = 2 then 1 else 0) + 1048576 * (if orderOf y = 3 then 1 else 0) +
        1099511627776 * (if orderOf y = 3 ∧ orderOf (x₁ * y) = 11 ∧
          orderOf (x₁ * y * x₁⁻¹ * y⁻¹) = 6 then 1 else 0) +
        1152921504606846976 * (if orderOf y = 3 ∧ orderOf (x₂ * y) = 11 ∧
          orderOf (x₂ * y * x₂⁻¹ * y⁻¹) = 6 then 1 else 0) := by
  unfold cnt4
  rw [ordTwo_pk hn, ordThree_pk hn, partner_pk hn h₁, partner_pk hn h₂]
  simp only [Nat.add_eq, Nat.mul_eq, Nat.add_assoc]

theorem pRow_nil (w m : Nat) (k : Nat → Nat → Nat) (g acc : Nat) :
    pRow n w m k g [] acc = acc := rfl

theorem pRow_cons (w m : Nat) (k : Nat → Nat → Nat) (g t : Nat) (T : List Nat) (acc : Nat) :
    pRow n w m k g (t :: T) acc = pRow n w m k g T (k (pcomp n w m g t) acc) := by
  have h : pRow n w m k g (t :: T) acc =
      strictN (pcomp n w m g t) (fun h => strictN (k h acc) (pRow n w m k g T)) := rfl
  rw [h, strictN_eq, strictN_eq]

theorem pcnt_nil (w m : Nat) (F : Nat → Nat) (g acc : Nat) :
    pcnt n w m F [] g acc = acc + F g := rfl

theorem pcnt_cons (w m : Nat) (F : Nat → Nat) (T : List Nat) (Ts : List (List Nat)) (g acc : Nat) :
    pcnt n w m F (T :: Ts) g acc = pRow n w m (pcnt n w m F Ts) g T acc := rfl

theorem pcnt_pk (hn : n ≤ 16) (F : Nat → Nat) :
    ∀ (Ts : List (List (Equiv.Perm (Fin n)))) (g : Equiv.Perm (Fin n)) (acc : Nat),
      pcnt n 4 (mask 4) F (Ts.map fun T => T.map pk) (pk g) acc =
        acc + ((products Ts).map fun h => F (pk (g * h))).sum
  | [], g, acc => by
    rw [List.map_nil, pcnt_nil]
    simp [products]
  | T :: Ts, g, acc => by
    rw [List.map_cons, pcnt_cons]
    induction T generalizing acc with
    | nil => simp [pRow_nil, products]
    | cons t T ih =>
      rw [List.map_cons, pRow_cons, pk_mul hn, pcnt_pk hn F Ts (g * t) acc, ih]
      simp only [products, List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, mul_assoc]
      omega

theorem products_append_head {M : Type*} [Monoid M] (A B : List M) (Ts : List (List M)) :
    products ((A ++ B) :: Ts) = products (A :: Ts) ++ products (B :: Ts) := by
  simp [products, List.flatMap_append]

theorem sum_ite_eq_countP {α : Type*} (L : List α) (P : α → Prop) [DecidablePred P] :
    (L.map fun h => if P h then 1 else 0).sum = L.countP fun h => decide (P h) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    by_cases h : P a <;> simp [h, Nat.add_comm]

theorem memB_iff (x : Nat) : ∀ L : List Nat, memB x L = true ↔ x ∈ L
  | [] => by simp [memB]
  | a :: L => by
    have h : memB x (a :: L) = bIf(Nat.beq x a, true, memB x L) := rfl
    rw [h, List.mem_cons, ← memB_iff x L]
    simp only [bIf_eq, Nat.beq_eq]
    by_cases hx : x = a <;> simp [hx]

theorem nodup_of_distB : ∀ {L : List Nat}, distB L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: L, h => by
    have h' : distB (a :: L) = bIf(memB a L, false, distB L) := rfl
    rw [h', bIf_eq] at h
    by_cases ha : memB a L = true
    · simp only [ha, ↓reduceIte] at h
      exact absurd h (by simp)
    · simp only [ha, ↓reduceIte, Bool.false_eq_true] at h
      exact List.nodup_cons.2 ⟨fun hm => ha ((memB_iff a L).2 hm), nodup_of_distB h⟩

theorem getN_eq : ∀ (L : List Nat) (i : Nat), getN L i = L.getD i 0
  | [], _ => rfl
  | a :: L, 0 => rfl
  | a :: L, i + 1 => by
    have h : getN (a :: L) (i + 1) = getN L i := rfl
    rw [h, getN_eq L i]
    rfl

theorem conjTreeP_sound (hn : n ≤ 16) (H : Subgroup (Equiv.Perm (Fin n)))
    {a b ρ : Equiv.Perm (Fin n)} (ha : a ∈ H) (hb : b ∈ H) {K P Lb : List Nat}
    (h : conjTreeP n 4 (mask 4) (pk a) (pk a⁻¹) (pk b) (pk b⁻¹) (pk ρ) K P Lb = true) :
    ∀ k < K.length, ∃ c ∈ H, getN K k = pk (c * ρ * c⁻¹) := by
  unfold conjTreeP at h
  rw [allN_iff] at h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk' := h k hk
    rw [bIf_eq] at hk'
    by_cases h0 : k = 0
    · subst h0
      have hz : Nat.beq 0 0 = true := rfl
      simp only [hz, ↓reduceIte, Nat.beq_eq] at hk'
      exact ⟨1, H.one_mem, by rw [hk']; simp⟩
    · have hz : (Nat.beq k 0 = true) = False := by rw [Nat.beq_eq]; exact eq_false h0
      simp only [hz, ↓reduceIte] at hk'
      rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, nIf_eq] at hk'
      obtain ⟨hp, he⟩ := hk'
      obtain ⟨c, hc, hce⟩ := ih _ hp (hp.trans hk)
      split_ifs at he
      · refine ⟨a * c, H.mul_mem ha hc, ?_⟩
        rw [he, cjP, hce, pk_mul hn, pk_mul hn]
        group
      · refine ⟨b * c, H.mul_mem hb hc, ?_⟩
        rw [he, cjP, hce, pk_mul hn, pk_mul hn]
        group

theorem conjTreeP_mem (hn : n ≤ 16) (H : Subgroup (Equiv.Perm (Fin n)))
    {a b ρ : Equiv.Perm (Fin n)} (ha : a ∈ H) (hb : b ∈ H) {K P Lb : List Nat}
    (h : conjTreeP n 4 (mask 4) (pk a) (pk a⁻¹) (pk b) (pk b⁻¹) (pk ρ) K P Lb = true) :
    ∀ k ∈ K, ∃ c ∈ H, k = pk (c * ρ * c⁻¹) := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
  obtain ⟨c, hc, he⟩ := conjTreeP_sound hn H ha hb h i hi
  rw [getN_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at he
  exact ⟨c, hc, he⟩

theorem of_ite_eq_one {P : Prop} [Decidable P] (h : (if P then 1 else 0) = 1) : P := by
  by_contra hp
  simp only [hp, ↓reduceIte, Nat.zero_ne_one] at h

@[expose] noncomputable def upk (n : Nat) (x : Nat) : Equiv.Perm (Fin n) := permOf n (fd 4 x)

theorem upk_pk (hn : n ≤ 16) (σ : Equiv.Perm (Fin n)) : upk n (pk σ) = σ := by
  rw [upk, permOf_congr (g := fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x)
    (fun x hx => by rw [fd_pk hn σ hx]; rfl)]
  exact permOf_val σ

theorem upk_conj (hn : n ≤ 16) {H : Subgroup (Equiv.Perm (Fin n))} {ρ : Equiv.Perm (Fin n)}
    {K : List Nat} (hK : ∀ k ∈ K, ∃ c ∈ H, k = pk (c * ρ * c⁻¹)) :
    (∀ y ∈ K.map (upk n), ∃ c ∈ H, y = c * ρ * c⁻¹) ∧ (K.map (upk n)).map pk = K := by
  refine ⟨fun y hy => ?_, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    obtain ⟨c, hc, rfl⟩ := hK k hk
    exact ⟨c, hc, upk_pk hn _⟩
  · rw [List.map_map]
    conv_rhs => rw [← List.map_id K]
    refine List.map_congr_left fun k hk => ?_
    obtain ⟨c, hc, rfl⟩ := hK k hk
    rw [Function.comp_apply, upk_pk hn, id]

theorem sum_eq_two_classes {G : Type*} [Group G] (H : Subgroup G) (p : G → Nat)
    (hp : ∀ c ∈ H, ∀ x, p (c * x * c⁻¹) = p x) (XG : List G)
    (hclosed : ∀ c ∈ H, ∀ x ∈ XG, c * x * c⁻¹ ∈ XG) {r₁ r₂ : G} (h₁ : r₁ ∈ XG) (h₂ : r₂ ∈ XG)
    {C₁ C₂ : List G} (hC₁ : ∀ y ∈ C₁, ∃ c ∈ H, y = c * r₁ * c⁻¹)
    (hC₂ : ∀ y ∈ C₂, ∃ c ∈ H, y = c * r₂ * c⁻¹) (hnd : (C₁ ++ C₂).Nodup)
    (hlen : XG.length ≤ C₁.length + C₂.length) :
    (XG.map p).sum = C₁.length * p r₁ + C₂.length * p r₂ := by
  have hsub : C₁ ++ C₂ ⊆ XG := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨c, hc, rfl⟩ := hC₁ y hy
      exact hclosed c hc _ h₁
    · obtain ⟨c, hc, rfl⟩ := hC₂ y hy
      exact hclosed c hc _ h₂
  have hperm := (hnd.subperm hsub).perm_of_length_le (by rw [List.length_append]; exact hlen)
  have hconst : ∀ (r : G) (C : List G), (∀ y ∈ C, ∃ c ∈ H, y = c * r * c⁻¹) →
      (C.map p).sum = C.length * p r := by
    intro r C hC
    rw [List.map_congr_left (g := fun _ => p r) fun y hy => by
      obtain ⟨c, hc, rfl⟩ := hC y hy
      exact hp c hc r, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [← (hperm.map p).sum_eq, List.map_append, List.sum_append, hconst r₁ C₁ hC₁,
    hconst r₂ C₂ hC₂]

end CFSG.KS.PCnt

end
