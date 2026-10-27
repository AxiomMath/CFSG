module

public import CFSG.CGT.Stroth76.TModel

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

@[expose] def tpow (q : Tc) : ℕ → Tc
  | 0 => (0, 0)
  | n + 1 => tmul (tpow q n) q

@[expose] def subst (iw ix iy iuv it iu : Tc) (p : Tc) : Tc :=
  tmul (tmul (tmul (tmul (tmul (tpow iw p.1.1.val) (tpow ix p.1.2.1.val)) (tpow iy p.1.2.2.val))
    (tpow iuv p.2.1.val)) (tpow it p.2.2.1.val)) (tpow iu p.2.2.2.val)

abbrev Sc : Type := ZMod 2 × Tc

@[expose] def smulC (σ : Tc → Tc) (z : Tc) (a b : Sc) : Sc :=
  (a.1 + b.1, tmul (tmul (if a.1 = 1 ∧ b.1 = 1 then z else (0, 0))
    (if b.1 = 1 then σ a.2 else a.2)) b.2)

section Elements

variable {X : Type*} [Group X] (K : Config X)

theorem tElt_tpow (q : Tc) (n : ℕ) : tElt K (tpow q n) = tElt K q ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact tElt_zero K
  | succ n ih => rw [tpow, tElt_mul, ih, pow_succ]

theorem tElt_eq_gens (p : Tc) :
    tElt K p = K.w ^ p.1.1.val * K.x ^ p.1.2.1.val * K.y ^ p.1.2.2.val *
      (K.uv ^ p.2.1.val * K.t ^ p.2.2.1.val * K.u ^ p.2.2.2.val) := rfl

theorem conj_tElt_eq_subst {g : X} {iw ix iy iuv it iu : Tc}
    (hw : g⁻¹ * K.w * g = tElt K iw) (hx : g⁻¹ * K.x * g = tElt K ix)
    (hy : g⁻¹ * K.y * g = tElt K iy) (huv : g⁻¹ * K.uv * g = tElt K iuv)
    (ht : g⁻¹ * K.t * g = tElt K it) (hu : g⁻¹ * K.u * g = tElt K iu) (p : Tc) :
    g⁻¹ * tElt K p * g = tElt K (subst iw ix iy iuv it iu p) := by
  rw [tElt_eq_gens]
  simp only [subst, tElt_mul, tElt_tpow, ← hw, ← hx, ← hy, ← huv, ← ht, ← hu,
    ← Config.conj_pow_eq]
  group

structure IdxTwo where
  s : X
  iw : Tc
  ix : Tc
  iy : Tc
  iuv : Tc
  it : Tc
  iu : Tc
  z : Tc
  hw : s⁻¹ * K.w * s = tElt K iw
  hx : s⁻¹ * K.x * s = tElt K ix
  hy : s⁻¹ * K.y * s = tElt K iy
  huv : s⁻¹ * K.uv * s = tElt K iuv
  ht : s⁻¹ * K.t * s = tElt K it
  hu : s⁻¹ * K.u * s = tElt K iu
  hz : s * s = tElt K z
  hsT : s ∉ Tsub K

namespace IdxTwo

variable {K} (D : IdxTwo K)

@[expose] def σ (p : Tc) : Tc := subst D.iw D.ix D.iy D.iuv D.it D.iu p

theorem conj_s (p : Tc) : D.s⁻¹ * tElt K p * D.s = tElt K (D.σ p) :=
  conj_tElt_eq_subst K D.hw D.hx D.hy D.huv D.ht D.hu p

@[expose] def smul (a b : Sc) : Sc := smulC D.σ D.z a b

@[expose] def sElt (a : Sc) : X := D.s ^ a.1.val * tElt K a.2

theorem tmul_zero_left (p : Tc) : tmul (0, 0) p = p := by
  obtain ⟨v, d⟩ := p
  have h1 : dinv (0 : Dc) = 0 := by decide
  have h2 : dmul (0 : Dc) d = d := by revert d; decide
  simp only [tmul, h1, dact_zero, zero_add, h2]

theorem s_mul_tElt (p : Tc) : tElt K p * D.s = D.s * tElt K (D.σ p) := by
  rw [← D.conj_s]
  group

theorem val_zero2 : (0 : ZMod 2).val = 0 := rfl
theorem val_one2 : (1 : ZMod 2).val = 1 := rfl

theorem smul_00 (p q : Tc) : D.smul (0, p) (0, q) = (0, tmul p q) := by
  simp (config := { decide := true }) [smul, smulC, tmul_zero_left]

theorem smul_01 (p q : Tc) : D.smul (0, p) (1, q) = (1, tmul (D.σ p) q) := by
  simp (config := { decide := true }) [smul, smulC, tmul_zero_left]

theorem smul_10 (p q : Tc) : D.smul (1, p) (0, q) = (1, tmul p q) := by
  simp (config := { decide := true }) [smul, smulC, tmul_zero_left]

theorem smul_11 (p q : Tc) : D.smul (1, p) (1, q) = (0, tmul (tmul D.z (D.σ p)) q) := by
  simp (config := { decide := true }) [smul, smulC]

theorem sElt_zero_fst (p : Tc) : D.sElt (0, p) = tElt K p := by
  simp only [sElt, val_zero2, pow_zero, one_mul]

theorem sElt_one_fst (p : Tc) : D.sElt (1, p) = D.s * tElt K p := by
  simp only [sElt, val_one2, pow_one]

theorem sElt_mul (a b : Sc) : D.sElt (D.smul a b) = D.sElt a * D.sElt b := by
  obtain ⟨e, p⟩ := a
  obtain ⟨e', q⟩ := b
  rcases zmod2_cases e with rfl | rfl <;> rcases zmod2_cases e' with rfl | rfl
  · rw [smul_00, sElt_zero_fst, sElt_zero_fst, sElt_zero_fst, tElt_mul]
  · rw [smul_01, sElt_one_fst, sElt_zero_fst, sElt_one_fst, tElt_mul, ← mul_assoc,
      ← s_mul_tElt, mul_assoc]
  · rw [smul_10, sElt_one_fst, sElt_one_fst, sElt_zero_fst, tElt_mul, mul_assoc]
  · rw [smul_11, sElt_zero_fst, sElt_one_fst, sElt_one_fst, tElt_mul, tElt_mul, ← D.hz,
      show D.s * tElt K p * (D.s * tElt K q) = D.s * (tElt K p * D.s) * tElt K q by group,
      s_mul_tElt]
    group

theorem s_not_mem_mul {p q : Tc} : D.s * tElt K p ≠ tElt K q := by
  intro h
  apply D.hsT
  have : D.s = tElt K q * (tElt K p)⁻¹ := by rw [← h]; group
  rw [this]
  exact (Tsub K).mul_mem (tElt_mem K q) ((Tsub K).inv_mem (tElt_mem K p))

theorem sElt_injective : Function.Injective D.sElt := by
  rintro ⟨e, p⟩ ⟨e', q⟩ h
  rcases zmod2_cases e with rfl | rfl <;> rcases zmod2_cases e' with rfl | rfl
  · rw [sElt_zero_fst, sElt_zero_fst] at h
    rw [tElt_injective K h]
  · rw [sElt_zero_fst, sElt_one_fst] at h
    exact (D.s_not_mem_mul h.symm).elim
  · rw [sElt_one_fst, sElt_zero_fst] at h
    exact (D.s_not_mem_mul h).elim
  · rw [sElt_one_fst, sElt_one_fst] at h
    rw [tElt_injective K (mul_left_cancel h)]

@[expose] def Ssub : Subgroup X := Tsub K ⊔ Subgroup.closure {D.s}

theorem sElt_mem (a : Sc) : D.sElt a ∈ D.Ssub :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton D.s))) _)
    (Subgroup.mem_sup_left (tElt_mem K a.2))

theorem inv_s_mul_tElt (p : Tc) :
    (D.s * tElt K p)⁻¹ = D.s * tElt K (D.σ (tmul (tinv p) (tinv D.z))) := by
  have hz : D.s⁻¹ = (tElt K D.z)⁻¹ * D.s := by rw [← D.hz]; group
  rw [mul_inv_rev, hz, ← tElt_tinv, ← tElt_tinv, ← mul_assoc, ← tElt_mul, s_mul_tElt]

@[expose] def sRange : Subgroup X where
  carrier := Set.range D.sElt
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨D.smul a b, D.sElt_mul a b⟩
  one_mem' := ⟨(0, (0, 0)), by rw [sElt_zero_fst, tElt_zero]⟩
  inv_mem' := by
    rintro _ ⟨⟨e, p⟩, rfl⟩
    rcases zmod2_cases e with rfl | rfl
    · exact ⟨(0, tinv p), by rw [sElt_zero_fst, sElt_zero_fst, tElt_tinv]⟩
    · exact ⟨(1, D.σ (tmul (tinv p) (tinv D.z))), by
        rw [sElt_one_fst, sElt_one_fst, inv_s_mul_tElt]⟩

theorem Ssub_le_sRange : D.Ssub ≤ D.sRange := by
  refine sup_le (fun g hg => ?_) ((Subgroup.closure_le _).2 ?_)
  · obtain ⟨p, rfl⟩ := exists_tElt K hg
    exact ⟨(0, p), D.sElt_zero_fst p⟩
  · rintro _ rfl
    exact ⟨(1, (0, 0)), by rw [sElt_one_fst, tElt_zero, mul_one]⟩

theorem exists_sElt {g : X} (hg : g ∈ D.Ssub) : ∃ a, D.sElt a = g := D.Ssub_le_sRange hg

theorem card_Ssub : Nat.card D.Ssub = 2 ^ 9 := by
  have hbij : Function.Bijective (fun a : Sc => (⟨D.sElt a, D.sElt_mem a⟩ : D.Ssub)) :=
    ⟨fun a b h => D.sElt_injective (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨a, rfl⟩ := D.exists_sElt hg
      exact ⟨a, rfl⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card]
  simp only [Fintype.card_prod, ZMod.card]
  norm_num

end IdxTwo

end Elements

end CFSG.CGT.Stroth76
