module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxFinW2
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.FinW

@[expose] def enc4 (r0 r1 r2 r3 : ZMod 2) : ℕ := r0.val + 2 * r1.val + 4 * r2.val + 8 * r3.val

theorem enc4_lt (r0 r1 r2 r3 : ZMod 2) : enc4 r0 r1 r2 r3 < 16 := by
  revert r0 r1 r2 r3
  decide +kernel

theorem enc4_add (r0 r1 r2 r3 s0 s1 s2 s3 : ZMod 2) :
    enc4 (r0 + s0) (r1 + s1) (r2 + s2) (r3 + s3) = enc4 r0 r1 r2 r3 ^^^ enc4 s0 s1 s2 s3 := by
  revert r0 r1 r2 r3 s0 s1 s2 s3
  decide +kernel

theorem enc4_inj {r0 r1 r2 r3 s0 s1 s2 s3 : ZMod 2} (h : enc4 r0 r1 r2 r3 = enc4 s0 s1 s2 s3) :
    r0 = s0 ∧ r1 = s1 ∧ r2 = s2 ∧ r3 = s3 := by
  revert r0 r1 r2 r3 s0 s1 s2 s3
  decide +kernel

theorem enc4_surj : ∀ n < 16, ∃ r0 r1 r2 r3 : ZMod 2, enc4 r0 r1 r2 r3 = n := by
  decide +kernel

theorem bf_enc4 (r0 r1 r2 r3 s0 s1 s2 s3 : ZMod 2) :
    bf (enc4 r0 r1 r2 r3) (enc4 s0 s1 s2 s3) = (r0 * s2 + r2 * s0 + r1 * s3 + r3 * s1).val := by
  revert r0 r1 r2 r3 s0 s1 s2 s3
  decide +kernel

theorem ap_enc4 (t : Tup) (r0 r1 r2 r3 : ZMod 2) :
    ap t (enc4 r0 r1 r2 r3) =
      (if r0 = 0 then 0 else t.i0) ^^^ (if r1 = 0 then 0 else t.i1) ^^^
        (if r2 = 0 then 0 else t.i2) ^^^ (if r3 = 0 then 0 else t.i3) := by
  have h : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  rcases h r0 with rfl | rfl <;> rcases h r1 with rfl | rfl <;> rcases h r2 with rfl | rfl <;>
    rcases h r3 with rfl | rfl <;> rfl

theorem zmod_val_one : (1 : ZMod 2).val = 1 := by decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def cc (bs : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 2) V) (x : V) : ℕ :=
  enc4 (bs.repr x (.inl 0)) (bs.repr x (.inl 1)) (bs.repr x (.inr 0)) (bs.repr x (.inr 1))

variable (bs : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 2) V)

theorem cc_lt (x : V) : cc bs x < 16 := enc4_lt _ _ _ _

theorem cc_add (x y : V) : cc bs (x + y) = cc bs x ^^^ cc bs y := by
  unfold cc
  simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  exact enc4_add _ _ _ _ _ _ _ _

theorem cc_zero : cc bs (0 : V) = 0 := by
  simp [cc, enc4]

theorem cc_inj {x y : V} (h : cc bs x = cc bs y) : x = y := by
  obtain ⟨h0, h1, h2, h3⟩ := enc4_inj h
  apply bs.repr.injective
  ext i
  rcases i with i | i <;> fin_cases i <;> assumption

theorem cc_eq_zero_iff {x : V} : cc bs x = 0 ↔ x = 0 :=
  ⟨fun h => cc_inj bs (h.trans (cc_zero bs).symm), fun h => h ▸ cc_zero bs⟩

theorem cc_smul (r : ZMod 2) (x : V) : cc bs (r • x) = if r = 0 then 0 else cc bs x := by
  have h : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  rcases h r with rfl | rfl
  · simp [cc_zero]
  · simp

theorem eq_sum (x : V) :
    x = bs.repr x (.inl 0) • bs (.inl 0) + bs.repr x (.inl 1) • bs (.inl 1) +
      bs.repr x (.inr 0) • bs (.inr 0) + bs.repr x (.inr 1) • bs (.inr 1) := by
  have h := bs.sum_repr x
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two] at h
  exact h.symm.trans (add_assoc _ _ _).symm

theorem cc_surj {n : ℕ} (hn : n < 16) : ∃ x : V, cc bs x = n := by
  obtain ⟨r0, r1, r2, r3, h⟩ := enc4_surj n hn
  refine ⟨r0 • bs (.inl 0) + r1 • bs (.inl 1) + r2 • bs (.inr 0) + r3 • bs (.inr 1), ?_⟩
  rw [← h]
  simp [cc]

@[expose] noncomputable def tupOf (g : V ≃ₗ[ZMod 2] V) : Tup :=
  ⟨cc bs (g (bs (.inl 0))), cc bs (g (bs (.inl 1))), cc bs (g (bs (.inr 0))),
    cc bs (g (bs (.inr 1)))⟩

theorem cc_apply (g : V ≃ₗ[ZMod 2] V) (x : V) : cc bs (g x) = ap (tupOf bs g) (cc bs x) := by
  conv_lhs => rw [eq_sum bs x]
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, cc_add, cc_add, cc_add,
    cc_smul, cc_smul, cc_smul, cc_smul]
  exact (ap_enc4 (tupOf bs g) _ _ _ _).symm

theorem cc_pow (g : V ≃ₗ[ZMod 2] V) (k : ℕ) (x : V) :
    cc bs ((g ^ k) x) = apN (tupOf bs g) k (cc bs x) := by
  induction k with
  | zero => simp [apN]
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, cc_apply, ih]; rfl

section Form

variable (β : LinearMap.BilinForm (ZMod 2) V)
  (h1 : ∀ i j, β (bs (.inl i)) (bs (.inl j)) = 0) (h2 : ∀ i j, β (bs (.inr i)) (bs (.inr j)) = 0)
  (h3 : ∀ i j, β (bs (.inl i)) (bs (.inr j)) = if i = j then 1 else 0) (halt : β.IsAlt)

include h1 h2 h3 halt

theorem gram_rl (i j : Fin 2) :
    β (bs (.inr i)) (bs (.inl j)) = if j = i then 1 else 0 := by
  rw [← halt.neg_eq, h3]
  split_ifs <;> simp

theorem form_expand (x y : V) :
    β x y = bs.repr x (.inl 0) * bs.repr y (.inr 0) + bs.repr x (.inr 0) * bs.repr y (.inl 0) +
      bs.repr x (.inl 1) * bs.repr y (.inr 1) + bs.repr x (.inr 1) * bs.repr y (.inl 1) := by
  have h4 := gram_rl bs β h1 h2 h3 halt
  conv_lhs => rw [eq_sum bs x, eq_sum bs y]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2, h3,
    h4]
  simp
  ring

theorem bf_cc (x y : V) : bf (cc bs x) (cc bs y) = (β x y).val := by
  rw [form_expand bs β h1 h2 h3 halt x y]
  exact bf_enc4 _ _ _ _ _ _ _ _

theorem tupOf_mem_L (g : V ≃ₗ[ZMod 2] V) (hg : ∀ x y, β (g x) (g y) = β x y) :
    tupOf bs g ∈ L := by
  have h4 := gram_rl bs β h1 h2 h3 halt
  have hb : ∀ p q : Fin 2 ⊕ Fin 2,
      bf (cc bs (g (bs p))) (cc bs (g (bs q))) = (β (bs p) (bs q)).val := by
    intro p q
    rw [bf_cc bs β h1 h2 h3 halt, hg]
  have c02 := hb (.inl 0) (.inr 0)
  have c01 := hb (.inl 0) (.inl 1)
  have c03 := hb (.inl 0) (.inr 1)
  have c21 := hb (.inr 0) (.inl 1)
  have c23 := hb (.inr 0) (.inr 1)
  have c13 := hb (.inl 1) (.inr 1)
  simp only [h1, h2, h3, h4] at c02 c01 c03 c21 c23 c13
  simp [zmod_val_one] at c02 c01 c03 c21 c23 c13
  unfold L
  simp only [List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range, Bool.and_eq_true,
    beq_iff_eq]
  exact ⟨cc bs (g (bs (.inl 0))), cc_lt bs _, cc bs (g (bs (.inr 0))), ⟨cc_lt bs _, c02⟩,
    cc bs (g (bs (.inl 1))), ⟨cc_lt bs _, c01, c21⟩, cc bs (g (bs (.inr 1))),
    ⟨cc_lt bs _, ⟨c03, c23⟩, c13⟩, rfl⟩

theorem tupOf_mem_L3 (g : V ≃ₗ[ZMod 2] V) (hg : ∀ x y, β (g x) (g y) = β x y) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : tupOf bs g ∈ L3 := by
  unfold L3
  rw [List.mem_filter]
  refine ⟨tupOf_mem_L bs β h1 h2 h3 halt g hg, ?_⟩
  rw [decide_eq_true_eq]
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := cc_surj bs hx
    rw [← cc_pow, hg3]
    rfl
  · obtain ⟨y, hy⟩ : ∃ y, g y ≠ y := by
      by_contra hcon
      push Not at hcon
      exact hg1 (LinearEquiv.ext hcon)
    exact ⟨cc bs y, cc_lt bs y, by rw [← cc_apply]; exact fun h => hy (cc_inj bs h)⟩

end Form

theorem cc_b0 : cc bs (bs (.inl 0)) = 1 := by
  have h : bs.repr (bs (.inl 0)) = Finsupp.single (.inl 0) 1 := Module.Basis.repr_self bs _
  simp [cc, h, enc4, zmod_val_one]

theorem cc_b1 : cc bs (bs (.inl 1)) = 2 := by
  have h : bs.repr (bs (.inl 1)) = Finsupp.single (.inl 1) 1 := Module.Basis.repr_self bs _
  simp [cc, h, enc4, zmod_val_one]

theorem cc_b2 : cc bs (bs (.inr 0)) = 4 := by
  have h : bs.repr (bs (.inr 0)) = Finsupp.single (.inr 0) 1 := Module.Basis.repr_self bs _
  simp [cc, h, enc4, zmod_val_one]

theorem cc_b3 : cc bs (bs (.inr 1)) = 8 := by
  have h : bs.repr (bs (.inr 1)) = Finsupp.single (.inr 1) 1 := Module.Basis.repr_self bs _
  simp [cc, h, enc4, zmod_val_one]

theorem tupOf_pow_two (g : V ≃ₗ[ZMod 2] V) : tupOf bs (g ^ 2) = sq (tupOf bs g) := by
  show (⟨cc bs ((g ^ 2) (bs (.inl 0))), cc bs ((g ^ 2) (bs (.inl 1))),
    cc bs ((g ^ 2) (bs (.inr 0))), cc bs ((g ^ 2) (bs (.inr 1)))⟩ : Tup) = sq (tupOf bs g)
  unfold sq
  simp only [cc_pow, cc_b0, cc_b1, cc_b2, cc_b3]

theorem cc_prod (a c : V ≃ₗ[ZMod 2] V) (p : ℕ) (z : V) :
    cc bs ((a ^ (p / 3) * c ^ (p % 3)) z) = prodAp (tupOf bs a) (tupOf bs c) p (cc bs z) := by
  rw [LinearEquiv.mul_apply, cc_pow, cc_pow]
  rfl

theorem pairHyp_tupOf (a c : V ≃ₗ[ZMod 2] V) (hca : c ≠ a) (hca2 : c ≠ a ^ 2)
    (hcomm : a * c = c * a) (k1 : keyT (tupOf bs a) ≤ keyT (tupOf bs (a ^ 2)))
    (k2 : keyT (tupOf bs c) ≤ keyT (tupOf bs (c ^ 2)))
    (k3 : keyT (tupOf bs a) ≤ keyT (tupOf bs c)) :
    PairHyp (tupOf bs a) (tupOf bs c) := by
  refine ⟨by rwa [← tupOf_pow_two], by rwa [← tupOf_pow_two], k3, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := cc_surj bs hx
    rw [← cc_apply, ← cc_apply, ← cc_apply, ← cc_apply]
    exact congrArg (cc bs) (congrArg (fun m => m y) hcomm)
  · obtain ⟨y, hy⟩ : ∃ y, c y ≠ a y := by
      by_contra hcon
      push Not at hcon
      exact hca (LinearEquiv.ext hcon)
    exact ⟨cc bs y, cc_lt bs y, by rw [← cc_apply, ← cc_apply]; exact fun h => hy (cc_inj bs h)⟩
  · obtain ⟨y, hy⟩ : ∃ y, c y ≠ (a ^ 2) y := by
      by_contra hcon
      push Not at hcon
      exact hca2 (LinearEquiv.ext hcon)
    exact ⟨cc bs y, cc_lt bs y, by rw [← cc_apply, ← cc_pow]; exact fun h => hy (cc_inj bs h)⟩

theorem finite_aut (bs : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod 2) V) :
    Finite (V ≃ₗ[ZMod 2] V) := by
  haveI : Finite V := Finite.of_equiv _ bs.equivFun.symm.toEquiv
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

end CFSG.GF2Type.Aschbacher1976Full.HS.FinW
