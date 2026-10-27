module

public import CFSG.CGT.Stroth76.TModel

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

abbrev Cc8 : Type := ZMod 2 × ZMod 8 × ZMod 8

@[expose] def lin8 (p q r : Cc8) (v : Cc8) : Cc8 := v.1.val • p + v.2.1.val • q + v.2.2.val • r

@[expose] def guv8 : Cc8 → Cc8 := lin8 (1, 4, 4) (1, 5, 2) (1, 2, 5)

@[expose] def gt8 : Cc8 → Cc8 := lin8 (1, 4, 0) (0, 7, 0) (1, 6, 3)

@[expose] def gu8 : Cc8 → Cc8 := lin8 (1, 0, 0) (0, 0, 1) (0, 1, 0)

@[expose] def pw8 (f : Cc8 → Cc8) (k : ZMod 2) (v : Cc8) : Cc8 := if k = 0 then v else f v

@[expose] def dact8 (d : Dc) (v : Cc8) : Cc8 := pw8 gu8 d.2.2 (pw8 gt8 d.2.1 (pw8 guv8 d.1 v))

abbrev Sc8 : Type := Cc8 × Dc

@[expose] def smul8 (p q : Sc8) : Sc8 := (p.1 + dact8 (dinv p.2) q.1, dmul p.2 q.2)

@[expose] def sinv8 (p : Sc8) : Sc8 := (-dact8 p.2 p.1, dinv p.2)

theorem dact8_eq_id_iff (d : Dc) :
    (dact8 d (1, 0, 0) = (1, 0, 0) ∧ dact8 d (0, 1, 0) = (0, 1, 0) ∧
      dact8 d (0, 0, 1) = (0, 0, 1)) ↔ d = 0 := by
  revert d; decide

theorem smul8_sinv8 (p : Sc8) : smul8 (sinv8 p) p = (0, 0) := by
  obtain ⟨v, d⟩ := p
  simp only [smul8, sinv8, dinv_dinv, dinv_dmul, neg_add_cancel]

structure CBasis8 {X : Type*} [Group X] (K : Config X) where
  C : Subgroup X
  a : X
  b : X
  hC : C = Subgroup.closure {K.w, a, b}
  hCc : IsMulCommutative C
  hCcard : Nat.card C = 2 ^ 7
  ha2 : a ^ 2 = K.x
  hb2 : b ^ 2 = K.y

structure ShapeII {X : Type*} [Group X] (K : Config X) extends CBasis8 K where
  huv_a : K.uv⁻¹ * a * K.uv = K.w * a ^ 5 * b ^ 2
  huv_b : K.uv⁻¹ * b * K.uv = K.w * b ^ 5 * a ^ 2
  ht_a : K.t⁻¹ * a * K.t = a⁻¹
  ht_b : K.t⁻¹ * b * K.t = K.w * b ^ 3 * a⁻¹ ^ 2
  hu_a : K.u⁻¹ * a * K.u = b

namespace CBasis8

variable {X : Type*} [Group X] {K : Config X} (P : CBasis8 K)

theorem w_mem : K.w ∈ P.C := by rw [P.hC]; exact Subgroup.subset_closure (by simp)
theorem a_mem : P.a ∈ P.C := by rw [P.hC]; exact Subgroup.subset_closure (by simp)
theorem b_mem : P.b ∈ P.C := by rw [P.hC]; exact Subgroup.subset_closure (by simp)

theorem comm {g h : X} (hg : g ∈ P.C) (hh : h ∈ P.C) : g * h = h * g := by
  haveI := P.hCc
  exact Subgroup.mul_comm_of_mem_isMulCommutative P.C hg hh

theorem a_pow_eight : P.a ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, P.ha2, K.hx]

theorem b_pow_eight : P.b ^ 8 = 1 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, P.hb2, K.hy]

@[expose] def ev8 (v : Cc8) : X := K.w ^ v.1.val * P.a ^ v.2.1.val * P.b ^ v.2.2.val

theorem ev8_mem (v : Cc8) : P.ev8 v ∈ P.C :=
  mul_mem (mul_mem (pow_mem P.w_mem _) (pow_mem P.a_mem _)) (pow_mem P.b_mem _)

theorem ev8_add (v v' : Cc8) : P.ev8 (v + v') = P.ev8 v * P.ev8 v' := by
  obtain ⟨i, j, l⟩ := v
  obtain ⟨i', j', l'⟩ := v'
  simp only [ev8, Prod.mk_add_mk]
  rw [pow_val_add K.hw, pow_val_add P.a_pow_eight, pow_val_add P.b_pow_eight]
  have hwa : ∀ m n : ℕ, K.w ^ m * P.a ^ n = P.a ^ n * K.w ^ m := fun m n =>
    P.comm (pow_mem P.w_mem _) (pow_mem P.a_mem _)
  have hwb : ∀ m n : ℕ, K.w ^ m * P.b ^ n = P.b ^ n * K.w ^ m := fun m n =>
    P.comm (pow_mem P.w_mem _) (pow_mem P.b_mem _)
  have hab : ∀ m n : ℕ, P.a ^ m * P.b ^ n = P.b ^ n * P.a ^ m := fun m n =>
    P.comm (pow_mem P.a_mem _) (pow_mem P.b_mem _)
  calc K.w ^ i.val * K.w ^ i'.val * (P.a ^ j.val * P.a ^ j'.val) * (P.b ^ l.val * P.b ^ l'.val)
      = K.w ^ i.val * (K.w ^ i'.val * P.a ^ j.val) * P.a ^ j'.val * P.b ^ l.val *
          P.b ^ l'.val := by group
    _ = K.w ^ i.val * (P.a ^ j.val * K.w ^ i'.val) * P.a ^ j'.val * P.b ^ l.val *
          P.b ^ l'.val := by rw [hwa]
    _ = K.w ^ i.val * P.a ^ j.val * (K.w ^ i'.val * P.a ^ j'.val * P.b ^ l.val) *
          P.b ^ l'.val := by group
    _ = K.w ^ i.val * P.a ^ j.val * (P.b ^ l.val * (K.w ^ i'.val * P.a ^ j'.val)) *
          P.b ^ l'.val := by
        rw [show K.w ^ i'.val * P.a ^ j'.val * P.b ^ l.val =
            K.w ^ i'.val * (P.a ^ j'.val * P.b ^ l.val) by group, hab,
          show K.w ^ i'.val * (P.b ^ l.val * P.a ^ j'.val) =
            (K.w ^ i'.val * P.b ^ l.val) * P.a ^ j'.val by group, hwb]
        group
    _ = K.w ^ i.val * P.a ^ j.val * P.b ^ l.val *
          (K.w ^ i'.val * P.a ^ j'.val * P.b ^ l'.val) := by group

@[simp] theorem ev8_zero : P.ev8 0 = 1 := by simp [ev8]

theorem ev8_nsmul (n : ℕ) (v : Cc8) : P.ev8 (n • v) = P.ev8 v ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, P.ev8_add, ih, pow_succ]

theorem ev8_neg (v : Cc8) : P.ev8 (-v) = (P.ev8 v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← P.ev8_add, neg_add_cancel, P.ev8_zero]

theorem ev8_w : P.ev8 (1, 0, 0) = K.w := by
  simp [ev8, show (1 : ZMod 2).val = 1 from rfl]
theorem ev8_a : P.ev8 (0, 1, 0) = P.a := by
  simp [ev8, show (1 : ZMod 8).val = 1 from rfl]
theorem ev8_b : P.ev8 (0, 0, 1) = P.b := by
  simp [ev8, show (1 : ZMod 8).val = 1 from rfl]

theorem exists_ev8 {g : X} (hg : g ∈ P.C) : ∃ v : Cc8, P.ev8 v = g := by
  rw [P.hC] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [⟨_, P.ev8_w⟩, ⟨_, P.ev8_a⟩, ⟨_, P.ev8_b⟩]
  | one => exact ⟨0, P.ev8_zero⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨v, rfl⟩ := ihg
    obtain ⟨v', rfl⟩ := ihh
    exact ⟨v + v', P.ev8_add v v'⟩
  | inv g _ ihg =>
    obtain ⟨v, rfl⟩ := ihg
    exact ⟨-v, P.ev8_neg v⟩

theorem ev8_injective [Finite X] : Function.Injective P.ev8 := by
  let f : Cc8 → P.C := fun v => ⟨P.ev8 v, P.ev8_mem v⟩
  have hsurj : Function.Surjective f := fun ⟨g, hg⟩ => by
    obtain ⟨v, rfl⟩ := P.exists_ev8 hg
    exact ⟨v, rfl⟩
  have hcard : Nat.card Cc8 ≤ Nat.card P.C := by
    rw [P.hCcard, Nat.card_eq_fintype_card]
    simp only [Fintype.card_prod, ZMod.card]
    norm_num
  have hinj : Function.Injective f :=
    (Function.Surjective.bijective_of_nat_card_le hsurj hcard).1
  intro v v' h
  exact hinj (Subtype.ext h)

theorem conj_ev8_of {g : X} {p q r : Cc8} (hw : g⁻¹ * K.w * g = P.ev8 p)
    (ha : g⁻¹ * P.a * g = P.ev8 q) (hb : g⁻¹ * P.b * g = P.ev8 r) (v : Cc8) :
    g⁻¹ * P.ev8 v * g = P.ev8 (lin8 p q r v) := by
  simp only [ev8, lin8]
  rw [Config.conj_mul_eq, Config.conj_mul_eq, Config.conj_pow_eq, Config.conj_pow_eq,
    Config.conj_pow_eq, hw, ha, hb]
  simp only [← ev8_nsmul, ← ev8_add]
  rfl

theorem x_eq : K.x = P.ev8 (0, 2, 0) := by
  rw [← P.ha2]; simp [ev8, show (2 : ZMod 8).val = 2 from rfl]
theorem y_eq : K.y = P.ev8 (0, 0, 2) := by
  rw [← P.hb2]; simp [ev8, show (2 : ZMod 8).val = 2 from rfl]

end CBasis8

namespace ShapeII

variable {X : Type*} [Group X] {K : Config X} (P : ShapeII K)

theorem conj_uv_ev8 (v : Cc8) : K.uv⁻¹ * P.ev8 v * K.uv = P.ev8 (guv8 v) := by
  refine P.conj_ev8_of ?_ ?_ ?_ v
  · have h : K.uv⁻¹ * K.w * K.uv = P.ev8 (1, 0, 0) * (P.ev8 (0, 2, 0) * P.ev8 (0, 0, 2)) ^ 2 := by
      rw [K.huv_w, ← P.x_eq, ← P.y_eq, P.ev8_w]
    rw [h, ← P.ev8_add, pow_two, ← P.ev8_add, ← P.ev8_add]
    congr 1
  · rw [P.huv_a, ← P.ev8_w, ← P.ev8_a, ← P.ev8_b, ← P.ev8_nsmul, ← P.ev8_nsmul, ← P.ev8_add,
      ← P.ev8_add]
    rfl
  · rw [P.huv_b, ← P.ev8_w, ← P.ev8_a, ← P.ev8_b, ← P.ev8_nsmul, ← P.ev8_nsmul, ← P.ev8_add,
      ← P.ev8_add]
    rfl

theorem conj_t_ev8 (v : Cc8) : K.t⁻¹ * P.ev8 v * K.t = P.ev8 (gt8 v) := by
  refine P.conj_ev8_of ?_ ?_ ?_ v
  · rw [K.ht_w, P.x_eq, ← P.ev8_w, ← P.ev8_nsmul, ← P.ev8_add]
    rfl
  · rw [P.ht_a, ← P.ev8_a, ← P.ev8_neg]
    rfl
  · rw [P.ht_b, ← P.ev8_w, ← P.ev8_a, ← P.ev8_b, ← P.ev8_neg, ← P.ev8_nsmul, ← P.ev8_nsmul,
      ← P.ev8_add, ← P.ev8_add]
    rfl

theorem hu_b : K.u⁻¹ * P.b * K.u = P.a := by
  rw [← P.hu_a, u_inv K]
  calc K.u * (K.u * P.a * K.u) * K.u = (K.u * K.u) * P.a * (K.u * K.u) := by group
    _ = P.a := by rw [u_mul_self K]; group

theorem conj_u_ev8 (v : Cc8) : K.u⁻¹ * P.ev8 v * K.u = P.ev8 (gu8 v) := by
  refine P.conj_ev8_of ?_ ?_ ?_ v
  · rw [K.hu_w, P.ev8_w]
  · rw [P.hu_a, P.ev8_b]
  · rw [P.hu_b, P.ev8_a]

@[expose] def sElt8 (p : Sc8) : X := P.ev8 p.1 * dElt K p.2

theorem conj_pow_val_ev8 {g : X} {f : Cc8 → Cc8} (hf : ∀ v, g⁻¹ * P.ev8 v * g = P.ev8 (f v))
    (k : ZMod 2) (v : Cc8) : (g ^ k.val)⁻¹ * P.ev8 v * g ^ k.val = P.ev8 (pw8 f k v) := by
  fin_cases k
  · show (g ^ 0)⁻¹ * P.ev8 v * g ^ 0 = P.ev8 (pw8 f 0 v)
    simp [pw8]
  · show (g ^ 1)⁻¹ * P.ev8 v * g ^ 1 = P.ev8 (pw8 f 1 v)
    rw [pow_one, hf]
    rfl

theorem conj_dElt_ev8 (d : Dc) (v : Cc8) :
    (dElt K d)⁻¹ * P.ev8 v * dElt K d = P.ev8 (dact8 d v) := by
  obtain ⟨a, b, c⟩ := d
  simp only [dElt, dact8]
  rw [conj_mul_mul, conj_mul_mul, P.conj_pow_val_ev8 P.conj_uv_ev8,
    P.conj_pow_val_ev8 P.conj_t_ev8, P.conj_pow_val_ev8 P.conj_u_ev8]

theorem dElt_mul_ev8 (d : Dc) (v : Cc8) :
    dElt K d * P.ev8 v = P.ev8 (dact8 (dinv d) v) * dElt K d := by
  have h := P.conj_dElt_ev8 (dinv d) v
  rw [← dElt_inv, inv_inv] at h
  rw [← h]
  group

theorem sElt8_mul (p q : Sc8) : P.sElt8 (smul8 p q) = P.sElt8 p * P.sElt8 q := by
  obtain ⟨v, d⟩ := p
  obtain ⟨v', d'⟩ := q
  simp only [sElt8, smul8]
  rw [P.ev8_add, dElt_mul, show P.ev8 v * dElt K d * (P.ev8 v' * dElt K d') =
    P.ev8 v * (dElt K d * P.ev8 v') * dElt K d' by group, P.dElt_mul_ev8]
  group

theorem sElt8_zero : P.sElt8 (0, 0) = 1 := by simp [sElt8, dElt_zero]

theorem sElt8_sinv8 (p : Sc8) : P.sElt8 (sinv8 p) = (P.sElt8 p)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← P.sElt8_mul, smul8_sinv8, P.sElt8_zero]

theorem eq_zero_of_dElt_mem [Finite X] {d : Dc} (h : dElt K d ∈ P.C) : d = 0 := by
  have hfix : ∀ v, dact8 d v = v := fun v => by
    have h1 := P.conj_dElt_ev8 d v
    rw [mul_assoc, ← P.comm h (P.ev8_mem v), ← mul_assoc, inv_mul_cancel, one_mul] at h1
    exact (P.ev8_injective h1).symm
  exact (dact8_eq_id_iff d).1 ⟨hfix _, hfix _, hfix _⟩

theorem sElt8_injective [Finite X] : Function.Injective P.sElt8 := by
  rintro ⟨v, d⟩ ⟨v', d'⟩ h
  simp only [sElt8] at h
  have hmem : dElt K (dmul d (dinv d')) ∈ P.C := by
    rw [dElt_mul, ← dElt_inv]
    have : dElt K d * (dElt K d')⁻¹ = (P.ev8 v)⁻¹ * P.ev8 v' := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_inv_cancel_right]
    rw [this]
    exact P.C.mul_mem (P.C.inv_mem (P.ev8_mem v)) (P.ev8_mem v')
  have hd : d = d' := (dmul_dinv_eq_zero_iff d d').1 (P.eq_zero_of_dElt_mem hmem)
  subst hd
  have hv : P.ev8 v = P.ev8 v' := mul_right_cancel h
  rw [P.ev8_injective hv]

@[expose] def Ssub8 : Subgroup X := P.C ⊔ Subgroup.closure {K.uv, K.t, K.u}

theorem sElt8_mem (p : Sc8) : P.sElt8 p ∈ P.Ssub8 :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left (P.ev8_mem p.1))
    (Subgroup.mem_sup_right (dElt_mem_D K p.2))

@[expose] def sRange8 : Subgroup X where
  carrier := Set.range P.sElt8
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨smul8 p q, P.sElt8_mul p q⟩
  one_mem' := ⟨(0, 0), P.sElt8_zero⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    exact ⟨sinv8 p, P.sElt8_sinv8 p⟩

theorem sElt8_ev (v : Cc8) : P.sElt8 (v, 0) = P.ev8 v := by simp [sElt8, dElt_zero]
theorem sElt8_gen_uv : P.sElt8 (0, (1, 0, 0)) = K.uv := by
  simp [sElt8, dElt, show (1 : ZMod 2).val = 1 from rfl]
theorem sElt8_gen_t : P.sElt8 (0, (0, 1, 0)) = K.t := by
  simp [sElt8, dElt, show (1 : ZMod 2).val = 1 from rfl]
theorem sElt8_gen_u : P.sElt8 (0, (0, 0, 1)) = K.u := by
  simp [sElt8, dElt, show (1 : ZMod 2).val = 1 from rfl]

theorem Ssub8_le_sRange8 : P.Ssub8 ≤ P.sRange8 := by
  refine sup_le (fun c hc => ?_) ((Subgroup.closure_le _).2 ?_)
  · obtain ⟨v, rfl⟩ := P.exists_ev8 hc
    exact ⟨(v, 0), P.sElt8_ev v⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [⟨_, P.sElt8_gen_uv⟩, ⟨_, P.sElt8_gen_t⟩, ⟨_, P.sElt8_gen_u⟩]

theorem exists_sElt8 {g : X} (hg : g ∈ P.Ssub8) : ∃ p, P.sElt8 p = g := P.Ssub8_le_sRange8 hg

end ShapeII

end CFSG.CGT.Stroth76
