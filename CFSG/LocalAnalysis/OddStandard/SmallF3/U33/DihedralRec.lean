module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

private lemma rel_zpow_mul {G : Type*} [Group G] {ρ σ : G}
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    σ * ρ ^ t = ρ ^ (-(t : ℤ)) * σ := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h' : σ * ρ = ρ⁻¹ * σ := by
        simpa [mul_assoc] using congrArg (fun x : G => x * σ) hrel
      calc
        σ * ρ ^ (t + 1) = σ * (ρ ^ t * ρ) := by rw [pow_succ]
        _ = (σ * ρ ^ t) * ρ := by rw [mul_assoc]
        _ = (ρ ^ (-(t : ℤ)) * σ) * ρ := by rw [ih]
        _ = ρ ^ (-(t : ℤ)) * (σ * ρ) := by rw [mul_assoc]
        _ = ρ ^ (-(t : ℤ)) * (ρ⁻¹ * σ) := by rw [h']
        _ = (ρ ^ (-(t : ℤ)) * ρ⁻¹) * σ := by rw [mul_assoc]
        _ = ρ ^ (-((t + 1 : ℕ) : ℤ)) * σ := by
              rw [← zpow_neg_one ρ, ← zpow_add]
              exact congrArg (fun e : ℤ => ρ ^ e * σ) (by omega)

private lemma zpow_mul_rel {G : Type*} [Group G] {ρ σ : G}
    (hσ2 : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    ρ ^ t * σ = σ * ρ ^ (-(t : ℤ)) := by
  have h1 := rel_zpow_mul (ρ := ρ) (σ := σ) hrel t
  have hstep : ρ ^ t = σ * ρ ^ (-(t : ℤ)) * σ := by
    calc
      ρ ^ t = (σ * σ) * ρ ^ t := by rw [← pow_two, hσ2, one_mul]
      _ = σ * (σ * ρ ^ t) := by rw [mul_assoc]
      _ = σ * (ρ ^ (-(t : ℤ)) * σ) := by rw [h1]
      _ = σ * ρ ^ (-(t : ℤ)) * σ := by rw [mul_assoc]
  calc
    ρ ^ t * σ = (σ * ρ ^ (-(t : ℤ)) * σ) * σ := by rw [hstep]
    _ = σ * ρ ^ (-(t : ℤ)) := by
          calc
            (σ * ρ ^ (-(t : ℤ)) * σ) * σ = σ * ρ ^ (-(t : ℤ)) * (σ * σ) := by group
            _ = σ * ρ ^ (-(t : ℤ)) * (σ ^ 2) := by rw [← pow_two]
            _ = σ * ρ ^ (-(t : ℤ)) := by rw [hσ2, mul_one]

private lemma pow_val_add_eq_four {G : Type*} [Group G] {ρ : G} (hρ4 : ρ ^ 4 = 1)
    (i j : ZMod 4) : ρ ^ ((i + j).val) = ρ ^ i.val * ρ ^ j.val := by
  have hcong : (i.val + j.val) % 4 ≡ i.val + j.val [MOD 4] := Nat.mod_modEq _ _
  calc
    ρ ^ ((i + j).val) = ρ ^ ((i.val + j.val) % 4) := by rw [ZMod.val_add (n := 4) i j]
    _ = ρ ^ (i.val + j.val) := pow_eq_pow_of_modEq hcong hρ4
    _ = ρ ^ i.val * ρ ^ j.val := by rw [pow_add]

private lemma pow_val_sub_zpow_four {G : Type*} [Group G] {ρ : G} (hρ4 : ρ ^ 4 = 1)
    (i j : ZMod 4) : ρ ^ ((j - i).val) = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
  have hji : (i + (j - i) : ZMod 4) = j := by simp [sub_eq_add_neg]
  have hval : j.val = (i.val + (j - i).val) % 4 := by
    calc
      j.val = (i + (j - i) : ZMod 4).val := by rw [hji]
      _ = (i.val + (j - i).val) % 4 := ZMod.val_add (n := 4) i (j - i)
  have hcong : j.val ≡ i.val + (j - i).val [MOD 4] := by
    rw [hval]
    exact Nat.mod_modEq _ _
  have hp : ρ ^ j.val = ρ ^ i.val * ρ ^ ((j - i).val) := by
    calc
      ρ ^ j.val = ρ ^ (i.val + (j - i).val) := pow_eq_pow_of_modEq hcong hρ4
      _ = ρ ^ i.val * ρ ^ ((j - i).val) := by rw [pow_add]
  calc
    ρ ^ ((j - i).val) = (ρ ^ i.val)⁻¹ * ρ ^ j.val := by rw [hp]; group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ (j.val : ℤ) := by
          rw [← zpow_natCast (a := ρ) (n := i.val), ← zpow_neg (a := ρ) (n := (i.val : ℤ)),
            ← zpow_natCast (a := ρ) (n := j.val)]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_add]
          exact congrArg (fun e : ℤ => ρ ^ e) (by ring)

private lemma map_mul_rs_four {G : Type*} [Group G] {ρ σ : G} (hρ4 : ρ ^ 4 = 1)
    (hσ2 : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (i j : ZMod 4) :
    ρ ^ i.val * (σ * ρ ^ j.val) = σ * ρ ^ (j - i).val := by
  calc
    ρ ^ i.val * (σ * ρ ^ j.val) = (ρ ^ i.val * σ) * ρ ^ j.val := by rw [mul_assoc]
    _ = (σ * ρ ^ (-(i.val : ℤ))) * ρ ^ j.val := by rw [zpow_mul_rel hσ2 hrel i.val]
    _ = σ * (ρ ^ (-(i.val : ℤ)) * ρ ^ j.val) := by rw [mul_assoc]
    _ = σ * ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_natCast (a := ρ) (n := j.val), ← zpow_add]
          exact congrArg (fun e : ℤ => σ * ρ ^ e) (by ring)
    _ = σ * ρ ^ (j - i).val := by rw [pow_val_sub_zpow_four hρ4 i j]

private lemma map_mul_ss_four {G : Type*} [Group G] {ρ σ : G} (hρ4 : ρ ^ 4 = 1)
    (hσ2 : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (i j : ZMod 4) :
    (σ * ρ ^ i.val) * (σ * ρ ^ j.val) = ρ ^ (j - i).val := by
  calc
    (σ * ρ ^ i.val) * (σ * ρ ^ j.val) = σ * (ρ ^ i.val * σ) * ρ ^ j.val := by group
    _ = σ * (σ * ρ ^ (-(i.val : ℤ))) * ρ ^ j.val := by rw [zpow_mul_rel hσ2 hrel i.val]
    _ = (σ * σ) * (ρ ^ (-(i.val : ℤ)) * ρ ^ j.val) := by group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ j.val := by rw [← pow_two, hσ2, one_mul]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_natCast (a := ρ) (n := j.val), ← zpow_add]
          exact congrArg (fun e : ℤ => ρ ^ e) (by ring)
    _ = ρ ^ (j - i).val := by rw [pow_val_sub_zpow_four hρ4 i j]

private lemma map_mul_sr_four {G : Type*} [Group G] {ρ σ : G} (hρ4 : ρ ^ 4 = 1)
    (i j : ZMod 4) : σ * ρ ^ (i + j).val = (σ * ρ ^ i.val) * ρ ^ j.val := by
  calc
    σ * ρ ^ (i + j).val = σ * (ρ ^ i.val * ρ ^ j.val) := by rw [pow_val_add_eq_four hρ4 i j]
    _ = (σ * ρ ^ i.val) * ρ ^ j.val := by rw [mul_assoc]

private def dihedralMap4 {G : Type*} [Group G] {a b : G} (ha4 : a ^ 4 = 1)
    (hb : b ^ 2 = 1) (hba : b * a * b⁻¹ = a⁻¹) : DihedralGroup 4 →* G where
  toFun := fun x =>
    match x with
    | DihedralGroup.r i => a ^ i.val
    | DihedralGroup.sr i => b * a ^ i.val
  map_one' := by
    change a ^ (0 : ZMod 4).val = 1
    simp
  map_mul' := by
    intro x y
    match x with
    | DihedralGroup.r i =>
        match y with
        | DihedralGroup.r j =>
            change a ^ (i + j).val = a ^ i.val * a ^ j.val
            exact pow_val_add_eq_four ha4 i j
        | DihedralGroup.sr j =>
            change b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
            exact (map_mul_rs_four ha4 hb hba i j).symm
    | DihedralGroup.sr i =>
        match y with
        | DihedralGroup.r j =>
            change b * a ^ (i + j).val = (b * a ^ i.val) * a ^ j.val
            exact map_mul_sr_four ha4 i j
        | DihedralGroup.sr j =>
            change a ^ (j - i).val = (b * a ^ i.val) * (b * a ^ j.val)
            exact (map_mul_ss_four ha4 hb hba i j).symm

private lemma mem_zpowers_of_pow_eq_mul {G : Type*} [Group G] {a b : G} {m n : ℕ}
    (h : a ^ m = b * a ^ n) : b ∈ Subgroup.zpowers a := by
  refine Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ) - (n : ℤ), ?_⟩
  have hb : b = a ^ m * (a ^ n)⁻¹ := by
    calc b = (b * a ^ n) * (a ^ n)⁻¹ := by group
      _ = a ^ m * (a ^ n)⁻¹ := by rw [← h]
  rw [hb, ← zpow_natCast (a := a) (n := m), ← zpow_natCast (a := a) (n := n),
    ← zpow_neg, ← zpow_add]
  ring_nf

private lemma mem_zpowers_of_mul_eq_pow {G : Type*} [Group G] {a b : G} {m n : ℕ}
    (h : b * a ^ m = a ^ n) : b ∈ Subgroup.zpowers a := by
  refine Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ) - (m : ℤ), ?_⟩
  have hb : b = a ^ n * (a ^ m)⁻¹ := by
    calc b = (b * a ^ m) * (a ^ m)⁻¹ := by group
      _ = a ^ n * (a ^ m)⁻¹ := by rw [h]
  rw [hb, ← zpow_natCast (a := a) (n := n), ← zpow_natCast (a := a) (n := m),
    ← zpow_neg, ← zpow_add]
  ring_nf

theorem nonempty_mulEquiv_dihedral_four {G : Type*} [Group G] {a b : G}
    (ha : orderOf a = 4) (hb : b ^ 2 = 1) (hba : b * a * b⁻¹ = a⁻¹) (hb' : b ∉ zpowers a) :
    Nonempty (↥(closure {a, b}) ≃* DihedralGroup 4) := by
  have ha4 : a ^ 4 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  let φ : DihedralGroup 4 →* G := dihedralMap4 ha4 hb hba
  have hφr : ∀ i : ZMod 4, φ (DihedralGroup.r i) = a ^ i.val := fun _ => rfl
  have hφsr : ∀ i : ZMod 4, φ (DihedralGroup.sr i) = b * a ^ i.val := fun _ => rfl
  have hval_inj : ∀ {i j : ZMod 4}, a ^ i.val = a ^ j.val → i = j := by
    intro i j hij
    have hmod : i.val % orderOf a = j.val % orderOf a := pow_inj_mod.mp hij
    rw [ha] at hmod
    rw [Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)] at hmod
    exact ZMod.val_injective 4 hmod
  have hinj : Function.Injective φ := by
    intro x y h
    match x with
    | DihedralGroup.r i =>
        match y with
        | DihedralGroup.r j =>
            exact congrArg DihedralGroup.r (hval_inj (by simpa only [hφr] using h))
        | DihedralGroup.sr j =>
            exact absurd (mem_zpowers_of_pow_eq_mul (by simpa only [hφr, hφsr] using h)) hb'
    | DihedralGroup.sr i =>
        match y with
        | DihedralGroup.r j =>
            exact absurd (mem_zpowers_of_mul_eq_pow (by simpa only [hφsr, hφr] using h)) hb'
        | DihedralGroup.sr j =>
            exact congrArg DihedralGroup.sr
              (hval_inj (mul_left_cancel (by simpa only [hφsr] using h)))
  have hrange_le : φ.range ≤ closure {a, b} := by
    rintro _ ⟨x, rfl⟩
    have ha_mem : a ∈ closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    have hb_mem : b ∈ closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
    match x with
    | DihedralGroup.r i => exact Subgroup.pow_mem (closure {a, b}) ha_mem i.val
    | DihedralGroup.sr i =>
        exact Subgroup.mul_mem (closure {a, b}) hb_mem
          (Subgroup.pow_mem (closure {a, b}) ha_mem i.val)
  have hrange_ge : closure {a, b} ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨DihedralGroup.r 1, by
        show a ^ (1 : ZMod 4).val = a
        rw [show (1 : ZMod 4).val = 1 by decide, pow_one]⟩
    · rw [hx]
      exact ⟨DihedralGroup.sr 0, by
        show b * a ^ (0 : ZMod 4).val = b
        rw [ZMod.val_zero, pow_zero, mul_one]⟩
  have hrange : φ.range = closure {a, b} := le_antisymm hrange_le hrange_ge
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33

end
