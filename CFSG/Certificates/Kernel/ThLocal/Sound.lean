module

public import Certificates.Data.Kernel.ThLocal.Defs
public import CFSG.Open.LocalVocabulary
import CFSG.Certificates.Kernel.Th.Spec.DceMat
public import CFSG.Certificates.Kernel.ThCensus.Sound

public section

namespace CFSG.KC.ThLocal.Sound

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus CFSG.KC.ThCensus.Sound
  CFSG.KC.ThLocal Subgroup

section Group

variable {G : Type*} [Group G]

theorem isElemAbelian_closure_comm {p : ℕ} {S : Set G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hp : ∀ a ∈ S, a ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.closure S) := by
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    induction hx using Subgroup.closure_induction with
    | mem a ha =>
      induction hy using Subgroup.closure_induction with
      | mem b hb => exact hS a ha b hb
      | one => simp
      | mul b c _ _ hb hc => rw [← mul_assoc, hb, mul_assoc, hc, mul_assoc]
      | inv b _ hb => exact (Commute.inv_right (show Commute a b from hb)).eq
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha => exact (Commute.inv_left (show Commute a y from ha)).eq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact hp a ha
  | one => simp
  | mul a b ha hb ha' hb' =>
    rw [(show Commute a b from hcomm a ha b hb).mul_pow, ha', hb', one_mul]
  | inv a _ ha' => rw [inv_pow, ha', inv_one]

theorem pow_mod_three {x : G} (hx : x ^ 3 = 1) (n : ℕ) : x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def pairP (x y : G) (ij : Fin 3 × Fin 3) : G := x ^ ij.1.val * y ^ ij.2.val

theorem pairP_mul {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (u v : Fin 3 × Fin 3) :
    pairP x y u * pairP x y v = pairP x y
      (⟨(u.1.val + v.1.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨(u.2.val + v.2.val) % 3, Nat.mod_lt _ (by norm_num)⟩) := by
  unfold pairP
  rw [← pow_mod_three hx, ← pow_mod_three hy, pow_add, pow_add]
  have hc : y ^ u.2.val * x ^ v.1.val = x ^ v.1.val * y ^ u.2.val :=
    ((Commute.pow_pow (show Commute x y from hxy) v.1.val u.2.val).eq).symm
  calc x ^ u.1.val * y ^ u.2.val * (x ^ v.1.val * y ^ v.2.val)
      = x ^ u.1.val * (y ^ u.2.val * x ^ v.1.val) * y ^ v.2.val := by group
    _ = x ^ u.1.val * (x ^ v.1.val * y ^ u.2.val) * y ^ v.2.val := by rw [hc]
    _ = x ^ u.1.val * x ^ v.1.val * (y ^ u.2.val * y ^ v.2.val) := by group

theorem mem_closure_pair {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    {w : G} (hw : w ∈ Subgroup.closure ({x, y} : Set G)) : ∃ u, pairP x y u = w := by
  induction hw using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · exact ⟨(1, 0), by simp [pairP]⟩
    · exact ⟨(0, 1), by simp [pairP]⟩
  | one => exact ⟨(0, 0), by simp [pairP]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    exact ⟨_, (pairP_mul hxy hx hy u v).symm⟩
  | inv a _ ha =>
    obtain ⟨⟨i, j⟩, rfl⟩ := ha
    refine ⟨(⟨(3 - i.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(3 - j.val) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [pairP_mul hxy hx hy]
    have hi := i.isLt
    have hj := j.isLt
    have h1 : (i.val + (3 - i.val) % 3) % 3 = 0 := by omega
    have h2 : (j.val + (3 - j.val) % 3) % 3 = 0 := by omega
    simp only [pairP, h1, h2, pow_zero, mul_one]

theorem pairP_mem {x y : G} (u : Fin 3 × Fin 3) :
    pairP x y u ∈ Subgroup.closure ({x, y} : Set G) := by
  have hx' : x ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert x _)
  have hy' : y ∈ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
  unfold pairP
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx' _) (Subgroup.pow_mem _ hy' _)

@[expose] def negP (v : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (⟨(3 - v.1.val) % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨(3 - v.2.val) % 3, Nat.mod_lt _ (by norm_num)⟩)

theorem pairP_negP {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (v : Fin 3 × Fin 3) : pairP x y v * pairP x y (negP v) = 1 := by
  rw [pairP_mul hxy hx hy]
  have hi := v.1.isLt
  have hj := v.2.isLt
  have h1 : (v.1.val + (negP v).1.val) % 3 = 0 := by
    change (v.1.val + (3 - v.1.val) % 3) % 3 = 0
    omega
  have h2 : (v.2.val + (negP v).2.val) % 3 = 0 := by
    change (v.2.val + (3 - v.2.val) % 3) % 3 = 0
    omega
  change x ^ ((v.1.val + (negP v).1.val) % 3) * y ^ ((v.2.val + (negP v).2.val) % 3) = 1
  rw [h1, h2, pow_zero, pow_zero, mul_one]

theorem pairP_injective {x y : G} (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hne : ∀ u : Fin 3 × Fin 3, u ≠ (0, 0) → pairP x y u ≠ 1) :
    Function.Injective (pairP x y) := by
  intro u v e
  have hu : pairP x y u * pairP x y (negP v) = 1 := by rw [e, pairP_negP hxy hx hy]
  rw [pairP_mul hxy hx hy] at hu
  by_contra huv
  refine hne _ ?_ hu
  intro h0
  apply huv
  have a1 := congrArg (fun p : Fin 3 × Fin 3 => p.1.val) h0
  have a2 := congrArg (fun p : Fin 3 × Fin 3 => p.2.val) h0
  have w1 : (negP v).1.val = (3 - v.1.val) % 3 := rfl
  have w2 : (negP v).2.val = (3 - v.2.val) % 3 := rfl
  simp only [Fin.val_zero] at a1 a2
  rw [w1] at a1
  rw [w2] at a2
  have hu1 := u.1.isLt
  have hu2 := u.2.isLt
  have hv1 := v.1.isLt
  have hv2 := v.2.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> omega

theorem e9_facts {t x y Z : G} (hxt : x * t = t * x) (hyt : y * t = t * y) (hxy : x * y = y * x)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hZ1 : Z ≠ 1) (hZ2 : Z ^ 2 ≠ 1)
    (hc : ∀ u : Fin 3 × Fin 3, u ≠ (0, 0) → IsConj (pairP x y u) Z ∨ IsConj (pairP x y u) (Z ^ 2)) :
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({t} : Set G) ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∀ w ∈ E, w ≠ 1 → IsConj w Z ∨ IsConj w (Z ^ 2) := by
  have hne : ∀ u : Fin 3 × Fin 3, u ≠ (0, 0) → pairP x y u ≠ 1 := by
    intro u hu e
    rcases hc u hu with h | h
    · rw [e, isConj_one_right] at h
      exact hZ1 h
    · rw [e, isConj_one_right] at h
      exact hZ2 h
  have hinj := pairP_injective hxy hx hy hne
  refine ⟨Subgroup.closure ({x, y} : Set G), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hxt
    · exact Subgroup.mem_centralizer_singleton_iff.2 hyt
  · refine isElemAbelian_closure_comm ?_ ?_
    · intro a ha b hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hxy
      · exact hxy.symm
      · rfl
    · intro a ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hy
  · have e : (Subgroup.closure ({x, y} : Set G) : Set G) = Set.range (pairP x y) := by
      ext w
      constructor
      · intro hw
        exact mem_closure_pair hxy hx hy hw
      · rintro ⟨u, rfl⟩
        exact pairP_mem u
    have e2 : Nat.card (Subgroup.closure ({x, y} : Set G)) = Nat.card (Set.range (pairP x y)) := by
      rw [← e, SetLike.coe_sort_coe]
    rw [e2, Nat.card_range_of_injective hinj]
    simp
  · intro w hw hw1
    obtain ⟨u, rfl⟩ := mem_closure_pair hxy hx hy hw
    refine hc u ?_
    rintro rfl
    exact hw1 (by simp [pairP])

theorem surj_of_mapsTo' [Finite G] {T : Set G} (f : G → G) (hf : Function.Injective f)
    (hm : ∀ y ∈ T, f y ∈ T) : ∀ y ∈ T, ∃ z ∈ T, f z = y := by
  intro y hy
  let F : T → T := fun z => ⟨f z, hm z z.2⟩
  have hF : Function.Injective F := fun a b e => Subtype.ext (hf (congrArg Subtype.val e))
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.1 hF) ⟨y, hy⟩
  exact ⟨z, z.2, congrArg Subtype.val hz⟩

theorem card_inf_centralizer_ge [Finite G] (g : ℕ → G) {t : G} {S : Set G} (hS : S.Finite)
    (hS27 : S.ncard ≤ 27) (ht : t ∈ S) (htQ : t ∈ SylowPc.pcSub g 10 0)
    (hQ : Nat.card (SylowPc.pcSub g 10 0) = 3 ^ 10)
    (hcl : ∀ k < 10, ∀ y ∈ S, g k * y * (g k)⁻¹ ∈ S) :
    3 ^ 7 ≤ Nat.card ↥(SylowPc.pcSub g 10 0 ⊓ Subgroup.centralizer ({t} : Set G)) := by
  set Q := SylowPc.pcSub g 10 0 with hQdef
  have hall : ∀ p ∈ Q, ∀ y ∈ S, p * y * p⁻¹ ∈ S := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hcl k hk.2
    | one =>
      intro y hy
      rw [one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := surj_of_mapsTo' (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  let tQ : ↥Q := ⟨t, htQ⟩
  have hsub : (conjugatesOf tQ).ncard ≤ S.ncard := by
    refine Set.ncard_le_ncard_of_injOn Subtype.val ?_ (fun a _ b _ e => Subtype.ext e) hS
    intro y hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    exact hall c.1 c.2 t ht
  have h1 := Subgroup.index_mul_card (Subgroup.centralizer ({tQ} : Set ↥Q))
  rw [Subgroup.index_centralizer_eq_ncard, hQ] at h1
  have h2 : 3 ^ 7 ≤ Nat.card (Subgroup.centralizer ({tQ} : Set ↥Q)) := by
    have h3 : (conjugatesOf tQ).ncard ≤ 27 := hsub.trans hS27
    have h4 : (conjugatesOf tQ).ncard * Nat.card (Subgroup.centralizer ({tQ} : Set ↥Q)) ≤
        27 * Nat.card (Subgroup.centralizer ({tQ} : Set ↥Q)) := Nat.mul_le_mul_right _ h3
    rw [h1] at h4
    norm_num at h4 ⊢
    omega
  refine h2.trans (Nat.card_le_card_of_injective
    (fun x => ⟨x.1.1, x.1.2, ?_⟩) ?_)
  · have hx := Subgroup.mem_centralizer_singleton_iff.1 x.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hx)
  · intro a b e
    have e2 := congrArg Subtype.val e
    apply Subtype.ext
    apply Subtype.ext
    exact e2

end Group

section Nf

variable {G : Type*} [Group G] (g : ℕ → G)

omit g in
theorem nf_mem {g' : ℕ → G} (n : ℕ) : nfFrom g' 10 0 n ∈ SylowPc.pcSub g' 10 0 :=
  nfFrom_mem g' 10 10 0 n le_rfl

theorem nfFrom_digit {d : ℕ} (hd : d < 3) :
    ∀ t s k, k < t → nfFrom g t s (d * 3 ^ k) = g (s + k) ^ d
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | t + 1, s, 0, _ => by
    rw [nfFrom_succ, pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hd, Nat.div_eq_of_lt hd,
      nfFrom_zero, mul_one, Nat.add_zero]
  | t + 1, s, k + 1, hk => by
    rw [nfFrom_succ]
    have e1 : d * 3 ^ (k + 1) % 3 = 0 := by rw [pow_succ]; simp [← mul_assoc]
    have e2 : d * 3 ^ (k + 1) / 3 = d * 3 ^ k := by
      rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
    rw [e1, e2, pow_zero, one_mul, nfFrom_digit hd t (s + 1) k (by omega)]
    congr 2
    omega

theorem nfFrom_pow3 {k : ℕ} (hk : k < 10) : nfFrom g 10 0 (3 ^ k) = g k := by
  have h := nfFrom_digit g (d := 1) (by norm_num) 10 0 k hk
  rw [one_mul, pow_one, Nat.zero_add] at h
  exact h

theorem nfFrom_z : nfFrom g 10 0 19683 = g 9 := by
  have h := nfFrom_pow3 g (k := 9) (by norm_num)
  norm_num at h
  exact h

theorem nfFrom_z2 : nfFrom g 10 0 39366 = g 9 ^ 2 := by
  have h := nfFrom_digit g (d := 2) (by norm_num) 10 0 9 (by norm_num)
  norm_num at h
  exact h

end Nf

section Perm

variable {G : Type*} [Group G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)} {g : ℕ → G}
  {vec : ℕ → Fin 248 → ZMod 2} {TT : ℕ}
  (hstep : ∀ k < 10, ∀ d < 3, ∀ p < 243, permStep TT k d p < 243 ∧
      vec (permStep TT k d p) = Matrix.vecMul (vec p) (φ (g k ^ d)))

include hstep in
theorem iterW_spec (n : ℕ) : ∀ a p, p < 243 → iterW TT n a p < 243 ∧
    vec (iterW TT n a p) = Matrix.vecMul (vec p) (φ (nfFrom g 10 0 n ^ a)) := by
  intro a
  induction a with
  | zero =>
    intro p hp
    refine ⟨hp, ?_⟩
    change vec p = _
    rw [pow_zero, map_one, Matrix.vecMul_one]
  | succ a ih =>
    intro p hp
    have e : iterW TT n (a + 1) p = iterW TT n a (permWalk TT p n) := by
      change CFSG.KC.Loop.strictN (permWalk TT p n) (iterW TT n a) = _
      rw [strictN_eq]
    obtain ⟨h1, h2⟩ := permWalk_spec hstep hp n
    obtain ⟨h3, h4⟩ := ih _ h1
    rw [e]
    refine ⟨h3, ?_⟩
    rw [h4, h2, Matrix.vecMul_vecMul, ← map_mul, ← pow_succ']

variable (hinj : ∀ p < 243, ∀ q < 243, vec p = vec q → p = q) {o0 o1 o2 : ℕ}
  (ho0 : o0 < 243) (ho1 : o1 < 243) (ho2 : o2 < 243)
  (hsurj : ∀ x ∈ SylowPc.pcSub g 10 0, ∃ m < 3 ^ 10, nfFrom g 10 0 m = x)
  (hmove : ∀ n < 3 ^ 10, n ≠ 0 →
    ¬ (permWalk TT o0 n = o0 ∧ permWalk TT o1 n = o1 ∧ permWalk TT o2 n = o2))
include hstep hinj ho0 ho1 ho2 hsurj hmove

theorem eq_of_base {x y : G} (hx : x ∈ SylowPc.pcSub g 10 0) (hy : y ∈ SylowPc.pcSub g 10 0)
    (h0 : Matrix.vecMul (vec o0) (φ x) = Matrix.vecMul (vec o0) (φ y))
    (h1 : Matrix.vecMul (vec o1) (φ x) = Matrix.vecMul (vec o1) (φ y))
    (h2 : Matrix.vecMul (vec o2) (φ x) = Matrix.vecMul (vec o2) (φ y)) : x = y :=
  mul_inv_eq_one.mp (base_spec hstep hinj ho0 ho1 ho2 hsurj hmove (mul_mem hx (inv_mem hy))
    (fix_of_eq h0) (fix_of_eq h1) (fix_of_eq h2))

theorem key3_spec {c n r : ℕ} (h : key3 TT o0 o1 o2 c n r = true) :
    nfFrom g 10 0 c * nfFrom g 10 0 n = nfFrom g 10 0 r * nfFrom g 10 0 c := by
  have h' : bAnd(permKeyAt TT o0 c n r, bAnd(permKeyAt TT o1 c n r, permKeyAt TT o2 c n r)) =
      true := h
  obtain ⟨k0, h''⟩ := rec_and h'
  obtain ⟨k1, k2⟩ := rec_and h''
  have key : ∀ o < 243, permKeyAt TT o c n r = true →
      Matrix.vecMul (vec o) (φ (nfFrom g 10 0 c * nfFrom g 10 0 n)) =
        Matrix.vecMul (vec o) (φ (nfFrom g 10 0 r * nfFrom g 10 0 c)) := by
    intro o ho hk
    have e := Nat.eq_of_beq_eq_true hk
    obtain ⟨a1, a2⟩ := permWalk_spec hstep ho c
    obtain ⟨b1, b2⟩ := permWalk_spec hstep a1 n
    obtain ⟨c1, c2⟩ := permWalk_spec hstep ho r
    obtain ⟨d1, d2⟩ := permWalk_spec hstep c1 c
    have ev := congrArg vec e
    rw [b2, a2, d2, c2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← map_mul, ← map_mul] at ev
    exact ev
  exact eq_of_base hstep hinj ho0 ho1 ho2 hsurj hmove (mul_mem (nf_mem c) (nf_mem n))
    (mul_mem (nf_mem r) (nf_mem c)) (key o0 ho0 k0) (key o1 ho1 k1) (key o2 ho2 k2)

theorem cube3_spec {n : ℕ} (h : cube3 TT o0 o1 o2 n = true) : nfFrom g 10 0 n ^ 3 = 1 := by
  have h' : bAnd(permCubeFix TT o0 n, bAnd(permCubeFix TT o1 n, permCubeFix TT o2 n)) = true := h
  obtain ⟨k0, h''⟩ := rec_and h'
  obtain ⟨k1, k2⟩ := rec_and h''
  have key : ∀ o < 243, permCubeFix TT o n = true →
      Matrix.vecMul (vec o) (φ (nfFrom g 10 0 n ^ 3)) = Matrix.vecMul (vec o) (φ 1) := by
    intro o ho hk
    have e := Nat.eq_of_beq_eq_true hk
    obtain ⟨a1, a2⟩ := permWalk_spec hstep ho n
    obtain ⟨b1, b2⟩ := permWalk_spec hstep a1 n
    obtain ⟨c1, c2⟩ := permWalk_spec hstep b1 n
    have ev := congrArg vec e
    rw [c2, b2, a2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← map_mul, ← map_mul,
      ← pow_three] at ev
    rw [ev, map_one, Matrix.vecMul_one]
  exact eq_of_base hstep hinj ho0 ho1 ho2 hsurj hmove (pow_mem (nf_mem n) 3) (one_mem _)
    (key o0 ho0 k0) (key o1 ho1 k1) (key o2 ho2 k2)

theorem e9Key_spec {e1 e2 a b c r : ℕ} (h0 : e9KeyAt TT o0 e1 e2 a b c r = true)
    (h1 : e9KeyAt TT o1 e1 e2 a b c r = true) (h2 : e9KeyAt TT o2 e1 e2 a b c r = true) :
    nfFrom g 10 0 c * (nfFrom g 10 0 e1 ^ a * nfFrom g 10 0 e2 ^ b) =
      nfFrom g 10 0 r * nfFrom g 10 0 c := by
  have key : ∀ o < 243, e9KeyAt TT o e1 e2 a b c r = true →
      Matrix.vecMul (vec o) (φ (nfFrom g 10 0 c * (nfFrom g 10 0 e1 ^ a * nfFrom g 10 0 e2 ^ b))) =
        Matrix.vecMul (vec o) (φ (nfFrom g 10 0 r * nfFrom g 10 0 c)) := by
    intro o ho hk
    have e := Nat.eq_of_beq_eq_true hk
    obtain ⟨a1, a2⟩ := permWalk_spec hstep ho c
    obtain ⟨b1, b2⟩ := iterW_spec hstep e1 a _ a1
    obtain ⟨c1, c2⟩ := iterW_spec hstep e2 b _ b1
    obtain ⟨d1, d2⟩ := permWalk_spec hstep ho r
    obtain ⟨f1, f2⟩ := permWalk_spec hstep d1 c
    have ev := congrArg vec e
    rw [c2, b2, a2, f2, d2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
      ← map_mul, ← map_mul, ← map_mul] at ev
    exact ev
  exact eq_of_base hstep hinj ho0 ho1 ho2 hsurj hmove
    (mul_mem (nf_mem c) (mul_mem (pow_mem (nf_mem e1) a) (pow_mem (nf_mem e2) b)))
    (mul_mem (nf_mem r) (nf_mem c)) (key o0 ho0 h0) (key o1 ho1 h1) (key o2 ho2 h2)

end Perm

theorem memH_spec {x : ℕ} : ∀ L : List (List ℕ), memH x L = true → ∃ e ∈ L, headN e = x
  | [], h => absurd h Bool.false_ne_true
  | e :: L, h => by
    rcases Dce.orB_iff.1 h with h | h
    · exact ⟨e, List.mem_cons_self .., Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨e', he', h'⟩ := memH_spec L h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

theorem clsRow_spec {TT o0 o1 o2 : ℕ} {L : List (List ℕ)} {s : ℕ} :
    ∀ (l : List ℕ) (k : ℕ), clsRowOK TT o0 o1 o2 L s l k = true → ∀ i < l.length,
      memH (l.getD i 0) L = true ∧ key3 TT o0 o1 o2 (3 ^ (k + i)) s (l.getD i 0) = true
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | s' :: l, k, h, i, hi => by
    have h' : bAnd(memH s' L, bAnd(key3 TT o0 o1 o2 (Nat.pow 3 k) s s',
        clsRowOK TT o0 o1 o2 L s l (Nat.succ k))) = true := h
    obtain ⟨hm, h2⟩ := rec_and h'
    obtain ⟨hk, h3⟩ := rec_and h2
    rcases i with _ | i
    · exact ⟨hm, hk⟩
    · have ih := clsRow_spec l (k + 1) h3 i (by simpa using hi)
      rw [List.getD_cons_succ]
      refine ⟨ih.1, ?_⟩
      have e : k + 1 + i = k + (i + 1) := by omega
      rw [← e]
      exact ih.2

theorem clsRows_spec {TT o0 o1 o2 : ℕ} {L : List (List ℕ)} :
    ∀ M : List (List ℕ), clsRowsOK TT o0 o1 o2 L M = true → ∀ e ∈ M,
      lenN e = 11 ∧ clsRowOK TT o0 o1 o2 L (headN e) (tailN e) 0 = true
  | [], _, e, he => absurd he List.not_mem_nil
  | x :: M, h, e, he => by
    have h' : bAnd(Nat.beq (lenN x) 11, bAnd(clsRowOK TT o0 o1 o2 L (headN x) (tailN x) 0,
        clsRowsOK TT o0 o1 o2 L M)) = true := h
    obtain ⟨h1, h2⟩ := rec_and h'
    obtain ⟨h3, h4⟩ := rec_and h2
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨Nat.eq_of_beq_eq_true h1, h3⟩
    · exact clsRows_spec M h4 e he

section Dec

variable {TT o0 o1 o2 : ℕ} {reps tgts fus : List (List ℕ)}

theorem zcOK_dec (h : zcOK TT o0 o1 o2 = true) :
    ∀ k < 10, key3 TT o0 o1 o2 (3 ^ k) 19683 19683 = true :=
  rec_all (fun k => key3 TT o0 o1 o2 (Nat.pow 3 k) 19683 19683) 10 h

theorem tgtLocOK_dec {j : ℕ} {L : List (List ℕ)} {E : List ℕ}
    (h : tgtLocOK TT o0 o1 o2 reps tgts fus j L E = true) :
    Nat.beq (headN (headL L)) (permNfNum (tgts.getD j [])) = true ∧ Nat.ble (lenN L) 27 = true ∧
      clsOK TT o0 o1 o2 L = true ∧
      e9OK TT o0 o1 o2 reps tgts fus (permNfNum (tgts.getD j [])) E = true := by
  have h' : bAnd(Nat.beq (headN (headL L)) (permNfNum (tgts.getD j [])),
      bAnd(Nat.ble (lenN L) 27, bAnd(clsOK TT o0 o1 o2 L,
        e9OK TT o0 o1 o2 reps tgts fus (permNfNum (tgts.getD j [])) E))) = true := h
  obtain ⟨t1, h2⟩ := rec_and h'
  obtain ⟨t2, h3⟩ := rec_and h2
  obtain ⟨t3, t4⟩ := rec_and h3
  exact ⟨t1, t2, t3, t4⟩

theorem e9OK_dec {t : ℕ} {E : List ℕ} (h : e9OK TT o0 o1 o2 reps tgts fus t E = true) :
    key3 TT o0 o1 o2 (E.getD 0 0) t t = true ∧ key3 TT o0 o1 o2 (E.getD 1 0) t t = true ∧
      key3 TT o0 o1 o2 (E.getD 0 0) (E.getD 1 0) (E.getD 1 0) = true ∧
      cube3 TT o0 o1 o2 (E.getD 0 0) = true ∧ cube3 TT o0 o1 o2 (E.getD 1 0) = true ∧
      e9RecsOK TT o0 o1 o2 reps tgts fus E (E.getD 0 0) (E.getD 1 0) = true := by
  have h' : bAnd(key3 TT o0 o1 o2 (E.getD 0 0) t t, bAnd(key3 TT o0 o1 o2 (E.getD 1 0) t t,
      bAnd(key3 TT o0 o1 o2 (E.getD 0 0) (E.getD 1 0) (E.getD 1 0),
        bAnd(cube3 TT o0 o1 o2 (E.getD 0 0), bAnd(cube3 TT o0 o1 o2 (E.getD 1 0),
          e9RecsOK TT o0 o1 o2 reps tgts fus E (E.getD 0 0) (E.getD 1 0)))))) = true := h
  obtain ⟨u1, t5⟩ := rec_and h'
  obtain ⟨u2, t6⟩ := rec_and t5
  obtain ⟨u3, t7⟩ := rec_and t6
  obtain ⟨u4, t8⟩ := rec_and t7
  obtain ⟨u5, u6⟩ := rec_and t8
  exact ⟨u1, u2, u3, u4, u5, u6⟩

theorem e9RecsOK_dec {E : List ℕ} {e1 e2 : ℕ} (h : e9RecsOK TT o0 o1 o2 reps tgts fus E e1 e2 = true) :
    ∀ i < 8, e9RecOK TT o0 o1 o2 reps tgts fus e1 e2 ((i + 1) / 3) ((i + 1) % 3)
      (E.getD (2 + 2 * i) 0) (E.getD (3 + 2 * i) 0) = true :=
  rec_all (fun i => e9RecOK TT o0 o1 o2 reps tgts fus e1 e2 (Nat.div (Nat.succ i) 3)
    (Nat.mod (Nat.succ i) 3) (E.getD (Nat.add 2 (Nat.mul 2 i)) 0)
    (E.getD (Nat.add 3 (Nat.mul 2 i)) 0)) 8 h

theorem e9RecOK_dec {e1 e2 a b c f : ℕ}
    (h : e9RecOK TT o0 o1 o2 reps tgts fus e1 e2 a b c f = true) :
    zRepOK tgts fus f = true ∧ e9KeyAt TT o0 e1 e2 a b c (zRep reps fus f) = true ∧
      e9KeyAt TT o1 e1 e2 a b c (zRep reps fus f) = true ∧
      e9KeyAt TT o2 e1 e2 a b c (zRep reps fus f) = true := by
  have h' : bAnd(zRepOK tgts fus f, bAnd(e9KeyAt TT o0 e1 e2 a b c (zRep reps fus f),
      bAnd(e9KeyAt TT o1 e1 e2 a b c (zRep reps fus f),
        e9KeyAt TT o2 e1 e2 a b c (zRep reps fus f)))) = true := h
  obtain ⟨hz, hk2⟩ := rec_and h'
  obtain ⟨k0, hk3⟩ := rec_and hk2
  obtain ⟨k1, k2⟩ := rec_and hk3
  exact ⟨hz, k0, k1, k2⟩

theorem zRepOK_dec {f : ℕ} (h : zRepOK tgts fus f = true) :
    f < 52 ∧ (50 ≤ f ∨ isZ (permNfNum (tgts.getD ((fus.getD f []).getD 1 0) [])) = true) := by
  have h' : bAnd(Nat.blt f 52, orB (Nat.ble 50 f)
      (isZ (permNfNum (tgts.getD ((fus.getD f []).getD 1 0) [])))) = true := h
  obtain ⟨h1, h2⟩ := rec_and h'
  refine ⟨Nat.blt_eq.mp h1, ?_⟩
  rcases Dce.orB_iff.1 h2 with h3 | h3
  · exact Or.inl (Nat.le_of_ble_eq_true h3)
  · exact Or.inr h3

theorem zRep_of_lt {f : ℕ} (h : f < 50) :
    zRep reps fus f = permNfNum (reps.getD ((fus.getD f []).getD 0 0) []) := by
  have b1 : Nat.beq f 50 = false := by
    cases hb : Nat.beq f 50
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  have b2 : Nat.beq f 51 = false := by
    cases hb : Nat.beq f 51
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  unfold zRep
  rw [b1, b2]

theorem isZ_dec {n : ℕ} (h : isZ n = true) : n = 19683 ∨ n = 39366 := by
  rcases Dce.orB_iff.1 h with h1 | h1
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Nat.eq_of_beq_eq_true h1)

theorem invOK_dec {RB : ℕ → ℕ} {c rm ONE r2 r3 rz n w : ℕ}
    (h : invOK RB c rm ONE r2 r3 rz n w = true) :
    Nat.beq (mulB c rm (wordR RB c rm 1 2 r2 r3 n w ONE) (wordR RB c rm 1 2 r2 r3 n w ONE)) ONE =
        true ∧
      notB (Nat.beq (mulB c rm (wordR RB c rm 1 2 r2 r3 n w ONE) ONE) ONE) = true ∧
      Nat.beq (mulB c rm (wordR RB c rm 1 2 r2 r3 n w ONE) (RB rz))
        (mulB c rm (RB rz) (wordR RB c rm 1 2 r2 r3 n w ONE)) = true := by
  have h' : bAnd(Nat.beq (mulB c rm (wordR RB c rm 1 2 r2 r3 n w ONE)
      (wordR RB c rm 1 2 r2 r3 n w ONE)) ONE,
      bAnd(notB (Nat.beq (mulB c rm (wordR RB c rm 1 2 r2 r3 n w ONE) ONE) ONE),
        Nat.beq (mulB c rm (wordR RB c rm 1 2 r2 r3 n w ONE) (RB rz))
          (mulB c rm (RB rz) (wordR RB c rm 1 2 r2 r3 n w ONE)))) = true := h
  obtain ⟨v1, h2⟩ := rec_and h'
  obtain ⟨v2, v3⟩ := rec_and h2
  exact ⟨v1, v2, v3⟩

theorem coverOK_dec {reps tgts F : List (List ℕ)} {nr : ℕ} (h : coverOK reps tgts F nr = true) :
    ∀ i < nr, orB (anyL (fun e => Nat.beq (e.getD 0 0) i) F)
      (anyL (fun t => Nat.beq (nfX t) (nfX (reps.getD i []))) tgts) = true :=
  (Dce.allB_iff _ nr).1 h

end Dec

theorem tailN_length : ∀ e : List ℕ, (tailN e).length = e.length - 1
  | [] => rfl
  | _ :: _ => rfl

theorem headN_mem_of_headL {L : List (List ℕ)} {x : ℕ} (h : headN (headL L) = x)
    (hne : L ≠ []) : ∃ e ∈ L, headN e = x := by
  cases L with
  | nil => exact absurd rfl hne
  | cons e L => exact ⟨e, List.mem_cons_self .., h⟩

end CFSG.KC.ThLocal.Sound

end
