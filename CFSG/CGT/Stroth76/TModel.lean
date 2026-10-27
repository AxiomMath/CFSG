module

public import CFSG.CGT.Stroth77.Arch76Lemma2Coord

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

abbrev Dc : Type := ZMod 2 × ZMod 2 × ZMod 2

@[expose] def dmul (d e : Dc) : Dc := (d.1 + e.1 + d.2.2 * e.2.1, d.2.1 + e.2.1, d.2.2 + e.2.2)

@[expose] def dinv (d : Dc) : Dc := (d.1 + d.2.2 * d.2.1, d.2.1, d.2.2)

@[expose] def pw (f : Co → Co) (k : ZMod 2) (v : Co) : Co := if k = 0 then v else f v

@[expose] def dact (d : Dc) (v : Co) : Co := pw fu d.2.2 (pw ft d.2.1 (pw fuv d.1 v))

abbrev Tc : Type := Co × Dc

@[expose] def tmul (p q : Tc) : Tc := (p.1 + dact (dinv p.2) q.1, dmul p.2 q.2)

@[expose] def tinv (p : Tc) : Tc := (-dact p.2 p.1, dinv p.2)

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem dmul_dinv (d : Dc) : dmul d (dinv d) = 0 := by revert d; decide
theorem dinv_dmul (d : Dc) : dmul (dinv d) d = 0 := by revert d; decide
theorem dinv_dinv (d : Dc) : dinv (dinv d) = d := by revert d; decide
theorem dmul_zero (d : Dc) : dmul d 0 = d := by revert d; decide
theorem dmul_assoc (d e f : Dc) : dmul (dmul d e) f = dmul d (dmul e f) := by
  revert d e f; decide

theorem dmul_eq_steps (d e : Dc) :
    dmul d e = dmul (dmul (dmul d (e.1, 0, 0)) (0, e.2.1, 0)) (0, 0, e.2.2) := by
  revert d e; decide

theorem dact_zero (v : Co) : dact 0 v = v := by revert v; decide

theorem dact_eq_id_iff (d : Dc) :
    (dact d (1, 0, 0) = (1, 0, 0) ∧ dact d (0, 1, 0) = (0, 1, 0) ∧ dact d (0, 0, 1) = (0, 0, 1)) ↔
      d = 0 := by
  revert d; decide

theorem dact_fst (d : Dc) (v : Co) : (dact d v).1 = v.1 := by revert d v; decide

theorem tmul_tinv (p : Tc) : tmul (tinv p) p = (0, 0) := by
  obtain ⟨v, d⟩ := p
  simp only [tmul, tinv, dinv_dinv, dinv_dmul, neg_add_cancel]

section Elements

variable {X : Type*} [Group X] (K : Config X)

@[expose] def dElt (d : Dc) : X := K.uv ^ d.1.val * K.t ^ d.2.1.val * K.u ^ d.2.2.val

@[expose] def tElt (p : Tc) : X := K.ev p.1 * dElt K p.2

theorem uv_mul_self : K.uv * K.uv = 1 := by rw [← pow_two, K.huv2]
theorem t_mul_self : K.t * K.t = 1 := by rw [← pow_two, K.ht2]
theorem u_mul_self : K.u * K.u = 1 := by rw [← pow_two, K.hu2]

theorem uv_inv : K.uv⁻¹ = K.uv := inv_eq_of_mul_eq_one_right (uv_mul_self K)
theorem t_inv : K.t⁻¹ = K.t := inv_eq_of_mul_eq_one_right (t_mul_self K)
theorem u_inv : K.u⁻¹ = K.u := inv_eq_of_mul_eq_one_right (u_mul_self K)

theorem u_mul_t : K.u * K.t = K.uv * K.t * K.u := by
  have h := K.htu
  rw [u_inv] at h
  calc K.u * K.t = K.u * K.t * K.u * K.u := by
        rw [mul_assoc (K.u * K.t), u_mul_self, mul_one]
    _ = K.uv * K.t * K.u := by rw [h]

theorem pow_val_add_one {g : X} (hg : g * g = 1) (k : ZMod 2) :
    g ^ (k + 1).val = g ^ k.val * g := by
  fin_cases k
  · show g ^ 1 = g ^ 0 * g
    rw [pow_zero, pow_one, one_mul]
  · show g ^ 0 = g ^ 1 * g
    rw [pow_zero, pow_one, hg]

theorem u_pow_mul_uv (n : ℕ) : K.u ^ n * K.uv = K.uv * K.u ^ n :=
  ((show Commute K.uv K.u from K.huvu).symm.pow_left n).eq

theorem t_pow_mul_uv (n : ℕ) : K.t ^ n * K.uv = K.uv * K.t ^ n :=
  ((show Commute K.uv K.t from K.huvt).symm.pow_left n).eq

theorem dElt_zero : dElt K 0 = 1 := by simp [dElt]

theorem dElt_mul_uv (d : Dc) : dElt K d * K.uv = dElt K (dmul d (1, 0, 0)) := by
  obtain ⟨a, b, c⟩ := d
  simp only [dElt, dmul, mul_zero, add_zero]
  rw [pow_val_add_one (uv_mul_self K), mul_assoc (K.uv ^ a.val * K.t ^ b.val), u_pow_mul_uv,
    ← mul_assoc, mul_assoc (K.uv ^ a.val), t_pow_mul_uv]
  simp only [mul_assoc]

theorem dElt_mul_t (d : Dc) : dElt K d * K.t = dElt K (dmul d (0, 1, 0)) := by
  obtain ⟨a, b, c⟩ := d
  simp only [dElt, dmul, mul_one, add_zero]
  rw [pow_val_add_one (t_mul_self K)]
  rcases zmod2_cases c with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, mul_one, add_zero, mul_assoc]
  · have h1 : (1 : ZMod 2).val = 1 := rfl
    simp only [h1, pow_one]
    rw [mul_assoc _ K.u K.t, u_mul_t, pow_val_add_one (uv_mul_self K)]
    calc K.uv ^ a.val * K.t ^ b.val * (K.uv * K.t * K.u)
        = K.uv ^ a.val * (K.t ^ b.val * K.uv) * K.t * K.u := by simp only [mul_assoc]
      _ = K.uv ^ a.val * (K.uv * K.t ^ b.val) * K.t * K.u := by rw [t_pow_mul_uv]
      _ = K.uv ^ a.val * K.uv * (K.t ^ b.val * K.t) * K.u := by simp only [mul_assoc]

theorem dElt_mul_u (d : Dc) : dElt K d * K.u = dElt K (dmul d (0, 0, 1)) := by
  obtain ⟨a, b, c⟩ := d
  simp only [dElt, dmul, mul_zero, add_zero]
  rw [pow_val_add_one (u_mul_self K), mul_assoc]

theorem dElt_mul_uv_pow (d : Dc) (k : ZMod 2) :
    dElt K d * K.uv ^ k.val = dElt K (dmul d (k, 0, 0)) := by
  fin_cases k
  · show dElt K d * K.uv ^ 0 = dElt K (dmul d 0)
    rw [pow_zero, mul_one, dmul_zero]
  · show dElt K d * K.uv ^ 1 = dElt K (dmul d (1, 0, 0))
    rw [pow_one, dElt_mul_uv]

theorem dElt_mul_t_pow (d : Dc) (k : ZMod 2) :
    dElt K d * K.t ^ k.val = dElt K (dmul d (0, k, 0)) := by
  fin_cases k
  · show dElt K d * K.t ^ 0 = dElt K (dmul d 0)
    rw [pow_zero, mul_one, dmul_zero]
  · show dElt K d * K.t ^ 1 = dElt K (dmul d (0, 1, 0))
    rw [pow_one, dElt_mul_t]

theorem dElt_mul_u_pow (d : Dc) (k : ZMod 2) :
    dElt K d * K.u ^ k.val = dElt K (dmul d (0, 0, k)) := by
  fin_cases k
  · show dElt K d * K.u ^ 0 = dElt K (dmul d 0)
    rw [pow_zero, mul_one, dmul_zero]
  · show dElt K d * K.u ^ 1 = dElt K (dmul d (0, 0, 1))
    rw [pow_one, dElt_mul_u]

theorem dElt_mul (d e : Dc) : dElt K (dmul d e) = dElt K d * dElt K e := by
  rw [dmul_eq_steps d e,
    show dElt K e = K.uv ^ e.1.val * K.t ^ e.2.1.val * K.u ^ e.2.2.val from rfl,
    ← mul_assoc, ← mul_assoc, dElt_mul_uv_pow, dElt_mul_t_pow, dElt_mul_u_pow]

theorem dElt_inv (d : Dc) : (dElt K d)⁻¹ = dElt K (dinv d) := by
  refine (eq_inv_of_mul_eq_one_right ?_).symm
  rw [← dElt_mul, dmul_dinv, dElt_zero]

theorem conj_mul_mul {g h a : X} : (g * h)⁻¹ * a * (g * h) = h⁻¹ * (g⁻¹ * a * g) * h := by
  group

theorem conj_pow_val_ev {g : X} {f : Co → Co} (hf : ∀ v, g⁻¹ * K.ev v * g = K.ev (f v))
    (k : ZMod 2) (v : Co) : (g ^ k.val)⁻¹ * K.ev v * g ^ k.val = K.ev (pw f k v) := by
  fin_cases k
  · show (g ^ 0)⁻¹ * K.ev v * g ^ 0 = K.ev (pw f 0 v)
    simp [pw]
  · show (g ^ 1)⁻¹ * K.ev v * g ^ 1 = K.ev (pw f 1 v)
    rw [pow_one, hf]
    rfl

theorem conj_dElt_ev (d : Dc) (v : Co) :
    (dElt K d)⁻¹ * K.ev v * dElt K d = K.ev (dact d v) := by
  obtain ⟨a, b, c⟩ := d
  simp only [dElt, dact]
  rw [conj_mul_mul, conj_mul_mul, conj_pow_val_ev K K.conj_uv_ev,
    conj_pow_val_ev K K.conj_t_ev, conj_pow_val_ev K K.conj_u_ev]

theorem dElt_mul_ev (d : Dc) (v : Co) :
    dElt K d * K.ev v = K.ev (dact (dinv d) v) * dElt K d := by
  have h := conj_dElt_ev K (dinv d) v
  rw [← dElt_inv, inv_inv] at h
  rw [← h]
  group

theorem tElt_mul (p q : Tc) : tElt K (tmul p q) = tElt K p * tElt K q := by
  obtain ⟨v, d⟩ := p
  obtain ⟨v', d'⟩ := q
  simp only [tElt, tmul]
  rw [K.ev_add, dElt_mul, show K.ev v * dElt K d * (K.ev v' * dElt K d') =
    K.ev v * (dElt K d * K.ev v') * dElt K d' by group, dElt_mul_ev]
  group

theorem tElt_zero : tElt K (0, 0) = 1 := by simp [tElt, dElt_zero]

theorem tElt_tinv (p : Tc) : tElt K (tinv p) = (tElt K p)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← tElt_mul, tmul_tinv, tElt_zero]

theorem dmul_dinv_eq_zero_iff (d e : Dc) : dmul d (dinv e) = 0 ↔ d = e := by
  revert d e; decide

theorem eq_zero_of_dElt_mem {d : Dc} (h : dElt K d ∈ K.A) : d = 0 := by
  have hfix : ∀ v, dact d v = v := fun v => K.ev_injective (by
    rw [← conj_dElt_ev, mul_assoc, ← K.comm h (K.ev_mem v), ← mul_assoc, inv_mul_cancel,
      one_mul])
  exact (dact_eq_id_iff d).1 ⟨hfix _, hfix _, hfix _⟩

theorem tElt_injective : Function.Injective (tElt K) := by
  rintro ⟨v, d⟩ ⟨v', d'⟩ h
  simp only [tElt] at h
  have hmem : dElt K (dmul d (dinv d')) ∈ K.A := by
    rw [dElt_mul, ← dElt_inv]
    have : dElt K d * (dElt K d')⁻¹ = (K.ev v)⁻¹ * K.ev v' := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, mul_inv_cancel_right]
    rw [this]
    exact K.A.mul_mem (K.A.inv_mem (K.ev_mem v)) (K.ev_mem v')
  have hd : d = d' := (dmul_dinv_eq_zero_iff d d').1 (eq_zero_of_dElt_mem K hmem)
  subst hd
  have hv : K.ev v = K.ev v' := mul_right_cancel h
  rw [K.ev_injective hv]

@[expose] def Tsub : Subgroup X := K.A ⊔ Subgroup.closure {K.uv, K.t, K.u}

theorem uv_mem_D : K.uv ∈ Subgroup.closure ({K.uv, K.t, K.u} : Set X) :=
  Subgroup.subset_closure (by simp)
theorem t_mem_D : K.t ∈ Subgroup.closure ({K.uv, K.t, K.u} : Set X) :=
  Subgroup.subset_closure (by simp)
theorem u_mem_D : K.u ∈ Subgroup.closure ({K.uv, K.t, K.u} : Set X) :=
  Subgroup.subset_closure (by simp)

theorem dElt_mem_D (d : Dc) : dElt K d ∈ Subgroup.closure ({K.uv, K.t, K.u} : Set X) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (uv_mem_D K) _)
    (Subgroup.pow_mem _ (t_mem_D K) _)) (Subgroup.pow_mem _ (u_mem_D K) _)

theorem tElt_mem (p : Tc) : tElt K p ∈ Tsub K :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.ev_mem p.1))
    (Subgroup.mem_sup_right (dElt_mem_D K p.2))

@[expose] def tRange : Subgroup X where
  carrier := Set.range (tElt K)
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨tmul p q, tElt_mul K p q⟩
  one_mem' := ⟨(0, 0), tElt_zero K⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    exact ⟨tinv p, tElt_tinv K p⟩

theorem tElt_gen_uv : tElt K (0, (1, 0, 0)) = K.uv := by
  simp [tElt, dElt, show (1 : ZMod 2).val = 1 from rfl]
theorem tElt_gen_t : tElt K (0, (0, 1, 0)) = K.t := by
  simp [tElt, dElt, show (1 : ZMod 2).val = 1 from rfl]
theorem tElt_gen_u : tElt K (0, (0, 0, 1)) = K.u := by
  simp [tElt, dElt, show (1 : ZMod 2).val = 1 from rfl]
theorem tElt_ev (v : Co) : tElt K (v, 0) = K.ev v := by simp [tElt, dElt_zero]

theorem Tsub_le_tRange : Tsub K ≤ tRange K := by
  refine sup_le (fun a ha => ?_) ((Subgroup.closure_le _).2 ?_)
  · obtain ⟨v, rfl⟩ := K.exists_ev ha
    exact ⟨(v, 0), tElt_ev K v⟩
  · intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    exacts [⟨_, tElt_gen_uv K⟩, ⟨_, tElt_gen_t K⟩, ⟨_, tElt_gen_u K⟩]

theorem exists_tElt {g : X} (hg : g ∈ Tsub K) : ∃ p, tElt K p = g := Tsub_le_tRange K hg

theorem card_Tsub : Nat.card (Tsub K) = 2 ^ 8 := by
  have hbij : Function.Bijective (fun p : Tc => (⟨tElt K p, tElt_mem K p⟩ : Tsub K)) :=
    ⟨fun p q h => tElt_injective K (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨p, rfl⟩ := exists_tElt K hg
      exact ⟨p, rfl⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, ZMod.card]
  norm_num

end Elements

end CFSG.CGT.Stroth76
