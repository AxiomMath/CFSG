module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12Model

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open Fin.NatCast

structure WMod where
  a : Fin 4
  b : Fin 4
  i : Fin 2
  deriving DecidableEq

namespace WMod

@[expose] def mul (g h : WMod) : WMod :=
  ⟨g.a + (M12Mod.act g.i 0 h.a h.b).1, g.b + (M12Mod.act g.i 0 h.a h.b).2, g.i + h.i⟩

@[expose] def inv (g : WMod) : WMod :=
  ⟨(M12Mod.act g.i 0 (-g.a) (-g.b)).1, (M12Mod.act g.i 0 (-g.a) (-g.b)).2, g.i⟩

instance : Mul WMod := ⟨mul⟩

instance : One WMod := ⟨⟨0, 0, 0⟩⟩

instance : Inv WMod := ⟨inv⟩

theorem mul_assoc' (g h k : WMod) : g * h * k = g * (h * k) := by
  obtain ⟨a1, b1, i1⟩ := g
  obtain ⟨a2, b2, i2⟩ := h
  obtain ⟨a3, b3, i3⟩ := k
  have h1 := M12Mod.act_add i1 0 a2 b2 (M12Mod.act i2 0 a3 b3).1 (M12Mod.act i2 0 a3 b3).2
  have h2 := M12Mod.act_act i1 0 i2 0 a3 b3
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  show mul (mul ⟨a1, b1, i1⟩ ⟨a2, b2, i2⟩) ⟨a3, b3, i3⟩ =
    mul ⟨a1, b1, i1⟩ (mul ⟨a2, b2, i2⟩ ⟨a3, b3, i3⟩)
  simp only [mul]
  rw [h2, add_zero] at e1 e2
  simp only [e1, e2, add_assoc]

theorem one_mul' (g : WMod) : 1 * g = g := by
  obtain ⟨a, b, i⟩ := g
  show mul ⟨0, 0, 0⟩ ⟨a, b, i⟩ = ⟨a, b, i⟩
  simp [mul, M12Mod.act_zero]

theorem mul_one' (g : WMod) : g * 1 = g := by
  obtain ⟨a, b, i⟩ := g
  show mul ⟨a, b, i⟩ ⟨0, 0, 0⟩ = ⟨a, b, i⟩
  simp [mul, M12Mod.act_zero_args]

theorem inv_mul_cancel_aux :
    ∀ (a b : Fin 4) (i : Fin 2), mul (inv ⟨a, b, i⟩) ⟨a, b, i⟩ = ⟨0, 0, 0⟩ := by
  decide +kernel

instance : Group WMod where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := fun ⟨a, b, i⟩ => inv_mul_cancel_aux a b i

@[expose] def equivProd : WMod ≃ Fin 4 × Fin 4 × Fin 2 where
  toFun g := (g.a, g.b, g.i)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : Fintype WMod :=
  Fintype.ofEquiv (Fin 4 × Fin 4 × Fin 2) equivProd.symm

theorem card_eq : Nat.card WMod = 32 := by
  rw [Nat.card_congr equivProd]
  simp [Nat.card_eq_fintype_card]

theorem forall_iff (P : WMod → Prop) : (∀ g, P g) ↔ ∀ a b i, P ⟨a, b, i⟩ :=
  ⟨fun h a b i => h _, fun h ⟨a, b, i⟩ => h a b i⟩

@[expose] def wx₁ : WMod := ⟨1, 0, 0⟩

@[expose] def wx₂ : WMod := ⟨0, 1, 0⟩

@[expose] def wlam : WMod := ⟨0, 0, 1⟩

private theorem fin_natCast_add_one (n k : ℕ) [NeZero k] :
    (n : Fin k) + 1 = ((n + 1 : ℕ) : Fin k) := by
  ext
  simp [Fin.val_add, Nat.add_mod]

private theorem wx₁_pow (n : ℕ) : wx₁ ^ n = (⟨(n : Fin 4), 0, 0⟩ : WMod) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change mul (⟨(n : Fin 4), 0, 0⟩ : WMod) wx₁ = (⟨((n + 1 : ℕ) : Fin 4), 0, 0⟩ : WMod)
    rw [show mul (⟨(n : Fin 4), 0, 0⟩ : WMod) wx₁ = (⟨(n : Fin 4) + 1, 0, 0⟩ : WMod) from by
          simp only [mul, wx₁, M12Mod.act_zero, zero_add, add_zero]]
    rw [fin_natCast_add_one]

private theorem wx₂_pow (n : ℕ) : wx₂ ^ n = (⟨0, (n : Fin 4), 0⟩ : WMod) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change mul (⟨0, (n : Fin 4), 0⟩ : WMod) wx₂ = (⟨0, ((n + 1 : ℕ) : Fin 4), 0⟩ : WMod)
    rw [show mul (⟨0, (n : Fin 4), 0⟩ : WMod) wx₂ = (⟨0, (n : Fin 4) + 1, 0⟩ : WMod) from by
          simp only [mul, wx₂, M12Mod.act_zero, zero_add, add_zero]]
    rw [fin_natCast_add_one]

private theorem wlam_pow (n : ℕ) : wlam ^ n = (⟨0, 0, (n : Fin 2)⟩ : WMod) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    change mul (⟨0, 0, (n : Fin 2)⟩ : WMod) wlam = (⟨0, 0, ((n + 1 : ℕ) : Fin 2)⟩ : WMod)
    rw [show mul (⟨0, 0, (n : Fin 2)⟩ : WMod) wlam = (⟨0, 0, (n : Fin 2) + 1⟩ : WMod) from by
          simp only [mul, wlam, M12Mod.act_zero_args, zero_add, add_zero]]
    rw [fin_natCast_add_one]

theorem eq_pow_mul (g : WMod) : g = wx₁ ^ g.a.val * wx₂ ^ g.b.val * wlam ^ g.i.val := by
  obtain ⟨a, b, i⟩ := g
  rw [wx₁_pow a.val, wx₂_pow b.val, wlam_pow i.val]
  simp only [Fin.cast_val_eq_self]
  change (⟨a, b, i⟩ : WMod) = mul (mul ⟨a, 0, 0⟩ ⟨0, b, 0⟩) ⟨0, 0, i⟩
  simp [mul, M12Mod.act_zero, M12Mod.act_zero_args]

theorem closure_eq_top : wreathGrp wx₁ wx₂ wlam = ⊤ := by
  rw [eq_top_iff]
  intro g _
  rw [eq_pow_mul g, wreathGrp]
  exact mul_mem
    (mul_mem (pow_mem (subset_closure (by simp)) g.a.val)
      (pow_mem (subset_closure (by simp)) g.b.val))
    (pow_mem (subset_closure (by simp)) g.i.val)

end WMod

variable {G : Type*} [Group G] {x₁ x₂ lam : G}

private theorem conj_x₁_eq (h : WreathRel x₁ x₂ lam) : lam * x₁ = x₂ * lam :=
  mul_inv_eq_iff_eq_mul.mp h.conj_x₁

private theorem conj_x₂_eq (h : WreathRel x₁ x₂ lam) : lam * x₂ = x₁ * lam := by
  have hlam2 : lam * lam = 1 := by
    rw [← pow_two, ← h.ord_lam]; exact pow_orderOf_eq_one lam
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
  calc lam * x₂ = lam * (lam * x₁ * lam⁻¹) := by rw [← h.conj_x₁]
    _ = lam * lam * x₁ * lam⁻¹ := by group
    _ = x₁ * lam⁻¹ := by rw [hlam2, one_mul]
    _ = x₁ * lam := by rw [hlinv]

private theorem x₁_pow_comm (h : WreathRel x₁ x₂ lam) (m n : ℕ) :
    x₁ ^ m * x₂ ^ n = x₂ ^ n * x₁ ^ m :=
  (show Commute x₁ x₂ from h.comm).pow_pow m n

private theorem x₁_pow_add_mod (h : WreathRel x₁ x₂ lam) (m n : ℕ) :
    x₁ ^ m * x₁ ^ n = x₁ ^ ((m + n) % 4) := by
  rw [← pow_add, ← h.ord_x₁]
  exact (pow_mod_orderOf x₁ (m + n)).symm

private theorem x₂_pow_add_mod (h : WreathRel x₁ x₂ lam) (m n : ℕ) :
    x₂ ^ m * x₂ ^ n = x₂ ^ ((m + n) % 4) := by
  rw [← pow_add, ← h.ord_x₂]
  exact (pow_mod_orderOf x₂ (m + n)).symm

private theorem lam_pow_add_mod (h : WreathRel x₁ x₂ lam) (m n : ℕ) :
    lam ^ m * lam ^ n = lam ^ ((m + n) % 2) := by
  rw [← pow_add, ← h.ord_lam]
  exact (pow_mod_orderOf lam (m + n)).symm

private theorem lam_mul_pow (h : WreathRel x₁ x₂ lam) (n : ℕ) :
    lam * lam ^ n = lam ^ ((1 + n) % 2) := by
  nth_rewrite 1 [← pow_one lam]
  rw [lam_pow_add_mod h 1 n]

private theorem lam_mul_x₁_pow (h : WreathRel x₁ x₂ lam) (n : ℕ) :
    lam * x₁ ^ n = x₂ ^ n * lam := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc lam * x₁ ^ (n + 1) = (lam * x₁ ^ n) * x₁ := by rw [pow_succ, mul_assoc]
      _ = (x₂ ^ n * lam) * x₁ := by rw [ih]
      _ = x₂ ^ n * (lam * x₁) := by rw [mul_assoc]
      _ = x₂ ^ n * (x₂ * lam) := by rw [conj_x₁_eq h]
      _ = (x₂ ^ n * x₂) * lam := by rw [← mul_assoc]
      _ = x₂ ^ (n + 1) * lam := by rw [← pow_succ]

private theorem lam_mul_x₂_pow (h : WreathRel x₁ x₂ lam) (n : ℕ) :
    lam * x₂ ^ n = x₁ ^ n * lam := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc lam * x₂ ^ (n + 1) = (lam * x₂ ^ n) * x₂ := by rw [pow_succ, mul_assoc]
      _ = (x₁ ^ n * lam) * x₂ := by rw [ih]
      _ = x₁ ^ n * (lam * x₂) := by rw [mul_assoc]
      _ = x₁ ^ n * (x₁ * lam) := by rw [conj_x₂_eq h]
      _ = (x₁ ^ n * x₁) * lam := by rw [← mul_assoc]
      _ = x₁ ^ (n + 1) * lam := by rw [← pow_succ]

private theorem lam_mul_base (h : WreathRel x₁ x₂ lam) (c d : Fin 4) :
    lam * (x₁ ^ c.val * x₂ ^ d.val) = x₂ ^ c.val * x₁ ^ d.val * lam := by
  rw [← mul_assoc, lam_mul_x₁_pow h c.val, mul_assoc, lam_mul_x₂_pow h d.val, mul_assoc]

private theorem base_normal (h : WreathRel x₁ x₂ lam) (a b c d : Fin 4) :
    x₁ ^ a.val * x₂ ^ b.val * (x₁ ^ c.val * x₂ ^ d.val) =
      x₁ ^ (a + c).val * x₂ ^ (b + d).val := by
  rw [Commute.mul_mul_mul_comm (x₁_pow_comm h c.val b.val).symm (x₁ ^ a.val) (x₂ ^ d.val)]
  rw [x₁_pow_add_mod h a.val c.val, x₂_pow_add_mod h b.val d.val]
  rfl

private theorem base_normal' (h : WreathRel x₁ x₂ lam) (a b c d : Fin 4) :
    x₁ ^ a.val * x₂ ^ b.val * (x₂ ^ c.val * x₁ ^ d.val) =
      x₁ ^ (a + d).val * x₂ ^ (b + c).val := by
  rw [← x₁_pow_comm h d.val c.val]
  rw [Commute.mul_mul_mul_comm (x₁_pow_comm h d.val b.val).symm (x₁ ^ a.val) (x₂ ^ c.val)]
  rw [x₁_pow_add_mod h a.val d.val, x₂_pow_add_mod h b.val c.val]
  rfl

private theorem embHom_mul (h : WreathRel x₁ x₂ lam) (g g' : WMod) :
    x₁ ^ (g * g').a.val * x₂ ^ (g * g').b.val * lam ^ (g * g').i.val =
      (x₁ ^ g.a.val * x₂ ^ g.b.val * lam ^ g.i.val) *
      (x₁ ^ g'.a.val * x₂ ^ g'.b.val * lam ^ g'.i.val) := by
  obtain ⟨a, b, i⟩ := g
  obtain ⟨c, d, k⟩ := g'
  fin_cases i
  · change x₁ ^ (a + c).val * x₂ ^ (b + d).val * lam ^ (0 + k).val =
        (x₁ ^ a.val * x₂ ^ b.val * lam ^ (0 : Fin 2).val) *
          (x₁ ^ c.val * x₂ ^ d.val * lam ^ k.val)
    rw [Fin.val_zero, pow_zero, mul_one]
    rw [← mul_assoc, base_normal h a b c d]
    simp only [Fin.val_add, Fin.val_zero, zero_add, Nat.mod_eq_of_lt k.isLt]
  · change x₁ ^ (a + d).val * x₂ ^ (b + c).val * lam ^ (1 + k).val =
        (x₁ ^ a.val * x₂ ^ b.val * lam ^ (1 : Fin 2).val) *
          (x₁ ^ c.val * x₂ ^ d.val * lam ^ k.val)
    rw [Fin.val_one, pow_one]
    have hstep : (x₁ ^ a.val * x₂ ^ b.val * lam) * (x₁ ^ c.val * x₂ ^ d.val * lam ^ k.val) =
        (x₁ ^ a.val * x₂ ^ b.val) * ((lam * (x₁ ^ c.val * x₂ ^ d.val)) * lam ^ k.val) := by
      group
    rw [hstep, lam_mul_base h c d]
    have hstep2 : (x₁ ^ a.val * x₂ ^ b.val) *
          ((x₂ ^ c.val * x₁ ^ d.val * lam) * lam ^ k.val) =
        (x₁ ^ a.val * x₂ ^ b.val * (x₂ ^ c.val * x₁ ^ d.val)) * (lam * lam ^ k.val) := by
      group
    rw [hstep2, base_normal' h a b c d, lam_mul_pow h k.val]
    simp only [Fin.val_add, Fin.val_one]

private def embHom (h : WreathRel x₁ x₂ lam) : WMod →* G where
  toFun g := x₁ ^ g.a.val * x₂ ^ g.b.val * lam ^ g.i.val
  map_one' := by
    show x₁ ^ (0 : ℕ) * x₂ ^ (0 : ℕ) * lam ^ (0 : ℕ) = 1
    simp
  map_mul' := embHom_mul h

private theorem base_inj (h : WreathRel x₁ x₂ lam) {a b a' b' : Fin 4}
    (heq : x₁ ^ a.val * x₂ ^ b.val = x₁ ^ a'.val * x₂ ^ b'.val) :
    a = a' ∧ b = b' := by
  have hw : (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val = x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ := by
    have h1 := congrArg (fun z => (x₁ ^ a'.val)⁻¹ * z * (x₂ ^ b.val)⁻¹) heq
    have h2 : (x₁ ^ a'.val)⁻¹ * (x₁ ^ a.val * x₂ ^ b.val) * (x₂ ^ b.val)⁻¹ =
        (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val := by group
    have h3 : (x₁ ^ a'.val)⁻¹ * (x₁ ^ a'.val * x₂ ^ b'.val) * (x₂ ^ b.val)⁻¹ =
        x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ := by group
    rw [h2, h3] at h1
    exact h1
  have hw1 : (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val ∈ zpowers x₁ :=
    mul_mem (inv_mem (npow_mem_zpowers x₁ a'.val)) (npow_mem_zpowers x₁ a.val)
  have hw2 : (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val ∈ zpowers x₂ := by
    rw [hw]
    exact mul_mem (npow_mem_zpowers x₂ b'.val) (inv_mem (npow_mem_zpowers x₂ b.val))
  have hw_eq : (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val = 1 := by
    have hmem : (x₁ ^ a'.val)⁻¹ * x₁ ^ a.val ∈ zpowers x₁ ⊓ zpowers x₂ := ⟨hw1, hw2⟩
    rwa [h.inf_eq_bot, Subgroup.mem_bot] at hmem
  have hpow₁ : x₁ ^ a.val = x₁ ^ a'.val := by
    calc x₁ ^ a.val = x₁ ^ a'.val * ((x₁ ^ a'.val)⁻¹ * x₁ ^ a.val) := by group
      _ = x₁ ^ a'.val * 1 := by rw [hw_eq]
      _ = x₁ ^ a'.val := by rw [mul_one]
  have hpow₂ : x₂ ^ b'.val = x₂ ^ b.val := by
    calc x₂ ^ b'.val = x₂ ^ b'.val * (x₂ ^ b.val)⁻¹ * x₂ ^ b.val := by group
      _ = ((x₁ ^ a'.val)⁻¹ * x₁ ^ a.val) * x₂ ^ b.val := by rw [← hw]
      _ = 1 * x₂ ^ b.val := by rw [hw_eq]
      _ = x₂ ^ b.val := by rw [one_mul]
  have haa : a.val = a'.val := by
    have hmod := (pow_inj_mod (x := x₁)).mp hpow₁
    rwa [h.ord_x₁, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt a'.isLt] at hmod
  have hbb : b'.val = b.val := by
    have hmod := (pow_inj_mod (x := x₂)).mp hpow₂
    rwa [h.ord_x₂, Nat.mod_eq_of_lt b'.isLt, Nat.mod_eq_of_lt b.isLt] at hmod
  exact ⟨Fin.ext haa, Fin.ext hbb.symm⟩

private theorem lam_notMem_base (h : WreathRel x₁ x₂ lam) : lam ∉ baseGrp x₁ x₂ := by
  intro hmem
  have hcomm : lam * x₁ = x₁ * lam := by
    have hle : baseGrp x₁ x₂ ≤ Subgroup.centralizer ({x₁} : Set G) := by
      rw [baseGrp, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h.comm.symm
    have := hle hmem
    rwa [Subgroup.mem_centralizer_singleton_iff] at this
  have hx₂_eq : x₂ = x₁ := by
    rw [← h.conj_x₁, hcomm]
    group
  have hx1 : x₁ ∈ zpowers x₁ ⊓ zpowers x₂ := by
    refine ⟨Subgroup.mem_zpowers x₁, ?_⟩
    rw [hx₂_eq]
    exact Subgroup.mem_zpowers x₁
  rw [h.inf_eq_bot, Subgroup.mem_bot] at hx1
  have h1 : orderOf x₁ = 1 := by rw [hx1, orderOf_one]
  have h4 : orderOf x₁ = 4 := h.ord_x₁
  omega

theorem WreathRel.exists_embedding (h : WreathRel x₁ x₂ lam) :
    ∃ φ : WMod →* G, Function.Injective φ ∧ φ.range = wreathGrp x₁ x₂ lam ∧
      φ WMod.wx₁ = x₁ ∧ φ WMod.wx₂ = x₂ ∧ φ WMod.wlam = lam := by
  refine ⟨embHom h, ?hinj, ?hrange, ?hx₁, ?hx₂, ?hlam⟩
  · intro g g' heq
    obtain ⟨a, b, i⟩ := g
    obtain ⟨a', b', i'⟩ := g'
    change x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val =
      x₁ ^ a'.val * x₂ ^ b'.val * lam ^ i'.val at heq
    fin_cases i <;> fin_cases i'
    · simp only [Fin.val_zero, pow_zero, mul_one] at heq
      obtain ⟨haa, hbb⟩ := base_inj h heq
      simp [haa, hbb]
    · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at heq
      exfalso
      have hmem : lam ∈ baseGrp x₁ x₂ := by
        have h2 : (x₁ ^ a'.val * x₂ ^ b'.val)⁻¹ * (x₁ ^ a.val * x₂ ^ b.val) = lam := by
          rw [heq]; group
        rw [← h2]
        exact mul_mem
          (inv_mem (mul_mem (pow_mem (subset_closure (by simp)) a'.val)
            (pow_mem (subset_closure (by simp)) b'.val)))
          (mul_mem (pow_mem (subset_closure (by simp)) a.val)
            (pow_mem (subset_closure (by simp)) b.val))
      exact lam_notMem_base h hmem
    · simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at heq
      exfalso
      have hmem : lam ∈ baseGrp x₁ x₂ := by
        have h2 : (x₁ ^ a.val * x₂ ^ b.val)⁻¹ * (x₁ ^ a'.val * x₂ ^ b'.val) = lam := by
          rw [← heq]; group
        rw [← h2]
        exact mul_mem
          (inv_mem (mul_mem (pow_mem (subset_closure (by simp)) a.val)
            (pow_mem (subset_closure (by simp)) b.val)))
          (mul_mem (pow_mem (subset_closure (by simp)) a'.val)
            (pow_mem (subset_closure (by simp)) b'.val))
      exact lam_notMem_base h hmem
    · simp only [Fin.val_one, pow_one] at heq
      obtain ⟨haa, hbb⟩ := base_inj h (mul_right_cancel heq)
      simp [haa, hbb]
  · apply le_antisymm
    · rintro y ⟨g, rfl⟩
      obtain ⟨a, b, i⟩ := g
      change x₁ ^ a.val * x₂ ^ b.val * lam ^ i.val ∈ wreathGrp x₁ x₂ lam
      rw [wreathGrp]
      exact mul_mem
        (mul_mem (pow_mem (subset_closure (by simp)) a.val)
          (pow_mem (subset_closure (by simp)) b.val))
        (pow_mem (subset_closure (by simp)) i.val)
    · rw [wreathGrp, Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨WMod.wx₁, by simp [embHom, WMod.wx₁]⟩
      · exact ⟨WMod.wx₂, by simp [embHom, WMod.wx₂]⟩
      · exact ⟨WMod.wlam, by simp [embHom, WMod.wlam]⟩
  · simp [embHom, WMod.wx₁]
  · simp [embHom, WMod.wx₂]
  · simp [embHom, WMod.wlam]

theorem WreathRel.card_wreathGrp (h : WreathRel x₁ x₂ lam) :
    Nat.card (wreathGrp x₁ x₂ lam) = 32 := by
  obtain ⟨φ, hinj, hrange, -⟩ := h.exists_embedding
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact WMod.card_eq

end CFSG.OddStandard.SmallF3.HarrisU33
