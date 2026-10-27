module

public import CFSG.Quasithin.Background.HMathieuBits

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Quasithin.H.Mathieu

section MaskProd

variable {G : Type*} [Group G]

@[expose] def maskProd : List G → ℕ → G
  | [], _ => 1
  | g :: gs, m => (if m % 2 = 1 then g else 1) * maskProd gs (m / 2)

@[simp] theorem maskProd_nil (m : ℕ) : maskProd ([] : List G) m = 1 := rfl

theorem maskProd_cons (g : G) (gs : List G) (m : ℕ) :
    maskProd (g :: gs) m = (if m % 2 = 1 then g else 1) * maskProd gs (m / 2) := rfl

theorem maskProd_zero : ∀ gs : List G, maskProd gs 0 = 1
  | [] => rfl
  | g :: gs => by simp [maskProd_cons, maskProd_zero gs]

theorem maskProd_map {H : Type*} [Group H] (f : G →* H) :
    ∀ (gs : List G) (m : ℕ), maskProd (gs.map f) m = f (maskProd gs m)
  | [], m => by simp
  | g :: gs, m => by
    rw [List.map_cons, maskProd_cons, maskProd_cons, maskProd_map f gs, map_mul]
    split_ifs <;> simp

theorem maskProd_mem (K : Subgroup G) :
    ∀ (gs : List G), (∀ g ∈ gs, g ∈ K) → ∀ m, maskProd gs m ∈ K
  | [], _, m => K.one_mem
  | g :: gs, h, m => by
    rw [maskProd_cons]
    refine K.mul_mem ?_ (maskProd_mem K gs (fun x hx => h x (List.mem_cons_of_mem g hx)) _)
    split_ifs
    · exact h g List.mem_cons_self
    · exact K.one_mem

theorem commute_maskProd {x : G} :
    ∀ (gs : List G), (∀ g ∈ gs, Commute x g) → ∀ m, Commute x (maskProd gs m)
  | [], _, m => Commute.one_right x
  | g :: gs, h, m => by
    rw [maskProd_cons]
    refine Commute.mul_right ?_
      (commute_maskProd gs (fun y hy => h y (List.mem_cons_of_mem g hy)) _)
    split_ifs
    · exact h g List.mem_cons_self
    · exact Commute.one_right x

theorem maskProd_xor : ∀ (gs : List G), (∀ g ∈ gs, g * g = 1) →
    (∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g) →
    ∀ a b : ℕ, maskProd gs (a ^^^ b) = maskProd gs a * maskProd gs b
  | [], _, _, a, b => by simp
  | g :: gs, hsq, hcomm, a, b => by
    have hsq' : ∀ x ∈ gs, x * x = 1 := fun x hx => hsq x (List.mem_cons_of_mem g hx)
    have hcomm' : ∀ x ∈ gs, ∀ y ∈ gs, x * y = y * x := fun x hx y hy =>
      hcomm x (List.mem_cons_of_mem g hx) y (List.mem_cons_of_mem g hy)
    have hg : ∀ m, g * maskProd gs m = maskProd gs m * g := fun m =>
      commute_maskProd gs (fun y hy => hcomm g List.mem_cons_self y (List.mem_cons_of_mem g hy)) m
    have hgg : g * g = 1 := hsq g List.mem_cons_self
    rw [maskProd_cons, maskProd_cons, maskProd_cons, Nat.xor_div_two,
      maskProd_xor gs hsq' hcomm' (a / 2) (b / 2)]
    have hgP := hg (a / 2)
    have hgQ := hg (b / 2)
    generalize maskProd gs (a / 2) = P at hgP ⊢
    generalize maskProd gs (b / 2) = Q at hgQ ⊢
    have hx := mod_two_xor a b
    by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1
    · rw [if_neg (fun h => (hx.1 h) ⟨fun _ => hb, fun _ => ha⟩), if_pos ha, if_pos hb]
      calc 1 * (P * Q) = (g * g) * (P * Q) := by rw [hgg]
        _ = g * (g * P) * Q := by simp only [mul_assoc]
        _ = g * (P * g) * Q := by rw [hgP]
        _ = g * P * (g * Q) := by simp only [mul_assoc]
    · rw [if_pos (hx.2 (fun h => hb (h.1 ha))), if_pos ha, if_neg hb]
      simp only [one_mul, mul_assoc]
    · rw [if_pos (hx.2 (fun h => ha (h.2 hb))), if_neg ha, if_pos hb]
      calc g * (P * Q) = (g * P) * Q := (mul_assoc _ _ _).symm
        _ = (P * g) * Q := by rw [hgP]
        _ = 1 * P * (g * Q) := by simp only [one_mul, mul_assoc]
    · rw [if_neg (fun h => (hx.1 h) ⟨fun h' => absurd h' ha, fun h' => absurd h' hb⟩), if_neg ha,
        if_neg hb]
      simp only [one_mul]

theorem xorHom_zero {ψ : ℕ → G} (hψ : ∀ a b, ψ (a ^^^ b) = ψ a * ψ b) : ψ 0 = 1 := by
  have h := hψ 0 0
  rw [Nat.xor_self] at h
  exact left_eq_mul.1 h

theorem maskProd_map_actM (ψ : ℕ → G) (hψ : ∀ a b, ψ (a ^^^ b) = ψ a * ψ b) :
    ∀ (cs : List ℕ) (m : ℕ), maskProd (cs.map ψ) m = ψ (actM cs m)
  | [], m => by simp [actM, xorHom_zero hψ]
  | c :: cs, m => by
    rw [List.map_cons, maskProd_cons, maskProd_map_actM ψ hψ cs, actM, hψ]
    split_ifs <;> simp [xorHom_zero hψ]

theorem maskProd_mod : ∀ (gs : List G) (m : ℕ), maskProd gs (m % 2 ^ gs.length) = maskProd gs m
  | [], m => by simp
  | g :: gs, m => by
    have h2 : 2 ^ (g :: gs).length = 2 * 2 ^ gs.length := by rw [List.length_cons, pow_succ']
    rw [maskProd_cons, maskProd_cons, h2, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _),
      Nat.mod_mul_right_div_self, maskProd_mod gs (m / 2)]

theorem maskProd_two_pow : ∀ (gs : List G) (j : ℕ), maskProd gs (2 ^ j) = gs.getD j 1
  | [], j => by simp
  | g :: gs, 0 => by simp [maskProd_cons, maskProd_zero]
  | g :: gs, j + 1 => by
    have h1 : 2 ^ (j + 1) % 2 = 0 := by
      rw [pow_succ]
      exact Nat.mul_mod_left _ _
    have h2 : 2 ^ (j + 1) / 2 = 2 ^ j := by
      rw [pow_succ]
      exact Nat.mul_div_cancel _ (by norm_num)
    rw [maskProd_cons, h2, maskProd_two_pow gs j, List.getD_cons_succ, if_neg (by omega),
      one_mul]

end MaskProd

structure MaskVM (V : Type*) [Group V] (n : ℕ) where
  vm : ℕ → V
  vm_xor : ∀ a b, vm (a ^^^ b) = vm a * vm b
  vm_mod : ∀ a, vm (a % 2 ^ n) = vm a
  vm_inj : ∀ a b, a < 2 ^ n → b < 2 ^ n → vm a = vm b → a = b
  vm_surj : ∀ v, ∃ m < 2 ^ n, vm m = v

section MaskEquiv

variable {V : Type*} [Group V]

theorem MaskVM.vm_zero {n : ℕ} (c : MaskVM V n) : c.vm 0 = 1 := xorHom_zero c.vm_xor

@[expose] noncomputable def maskOfW (n : ℕ) (w : Wn n) : ℕ := (toW_surj n w).choose

theorem maskOfW_lt {n : ℕ} (w : Wn n) : maskOfW n w < 2 ^ n := (toW_surj n w).choose_spec.1

theorem toW_maskOfW {n : ℕ} (w : Wn n) : toW n (maskOfW n w) = w := (toW_surj n w).choose_spec.2

theorem maskOfW_toW {n m : ℕ} (hm : m < 2 ^ n) : maskOfW n (toW n m) = m :=
  toW_inj (maskOfW_lt _) hm (toW_maskOfW _)

theorem maskOfW_toW_mod (n m : ℕ) : maskOfW n (toW n m) = m % 2 ^ n := by
  rw [← toW_mod]
  exact maskOfW_toW (Nat.mod_lt _ (Nat.two_pow_pos n))

@[expose] noncomputable def maskVMHom {n : ℕ} (c : MaskVM V n) : Wn n →* V where
  toFun w := c.vm (maskOfW n w)
  map_one' := by
    have h : maskOfW n 1 = 0 := by
      have := maskOfW_toW (n := n) (m := 0) (Nat.two_pow_pos n)
      rwa [toW_zero] at this
    rw [h, c.vm_zero]
  map_mul' w₁ w₂ := by
    have h : maskOfW n (w₁ * w₂) = maskOfW n w₁ ^^^ maskOfW n w₂ := by
      apply toW_inj (maskOfW_lt _) (Nat.xor_lt_two_pow (maskOfW_lt _) (maskOfW_lt _))
      rw [toW_maskOfW, toW_xor, toW_maskOfW, toW_maskOfW]
    show c.vm (maskOfW n (w₁ * w₂)) = c.vm (maskOfW n w₁) * c.vm (maskOfW n w₂)
    rw [h, c.vm_xor]

theorem maskVMHom_apply {n : ℕ} (c : MaskVM V n) (w : Wn n) :
    maskVMHom c w = c.vm (maskOfW n w) := rfl

theorem maskVMHom_bijective {n : ℕ} (c : MaskVM V n) : Function.Bijective (maskVMHom c) := by
  refine ⟨fun w₁ w₂ h => ?_, fun v => ?_⟩
  · rw [maskVMHom_apply, maskVMHom_apply] at h
    have := c.vm_inj _ _ (maskOfW_lt w₁) (maskOfW_lt w₂) h
    rw [← toW_maskOfW w₁, ← toW_maskOfW w₂, this]
  · obtain ⟨m, hm, hv⟩ := c.vm_surj v
    refine ⟨toW n m, ?_⟩
    rw [maskVMHom_apply, maskOfW_toW hm, hv]

@[expose] noncomputable def maskVMEquiv {n : ℕ} (c : MaskVM V n) : Wn n ≃* V :=
  MulEquiv.ofBijective (maskVMHom c) (maskVMHom_bijective c)

theorem maskVMEquiv_toW {n : ℕ} (c : MaskVM V n) (m : ℕ) :
    maskVMEquiv c (toW n m) = c.vm m := by
  rw [maskVMEquiv, MulEquiv.ofBijective_apply, maskVMHom_apply, maskOfW_toW_mod, c.vm_mod]

end MaskEquiv

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
