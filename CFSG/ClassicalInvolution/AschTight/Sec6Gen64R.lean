module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Q

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

theorem exists_dihedral_iso {Q : Type*} [Group Q] {a ρ : Q} (ha : a * a = 1)
    (hρ : orderOf ρ = 6) (hinv : a * ρ * a⁻¹ = ρ⁻¹) (ha' : ∀ i : ℕ, a ≠ ρ ^ i)
    (hgen : ∀ q : Q, ∃ i : ℤ, q = ρ ^ i ∨ q = a * ρ ^ i) :
    Nonempty (DihedralGroup 6 ≃* Q) := by
  have h6 : ρ ^ 6 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  set e : ZMod 6 → Q := fun i => ρ ^ i.val with he
  have e_add : ∀ i j, e (i + j) = e i * e j := by
    intro i j
    simp only [he]
    rw [ZMod.val_add, ← pow_eq_pow_mod _ h6, pow_add]
  have e_zero : e 0 = 1 := by simp [he]
  have e_neg : ∀ i, e (-i) = (e i)⁻¹ := by
    intro i
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← e_add, neg_add_cancel, e_zero]
  have e_sub : ∀ i j, e (j - i) = e j * (e i)⁻¹ := by
    intro i j
    rw [sub_eq_add_neg, e_add, e_neg]
  have e_comm : ∀ i j, e i * e j = e j * e i := by
    intro i j
    simp only [he, ← pow_add, add_comm]
  have conj_e : ∀ i, a * e i * a⁻¹ = (e i)⁻¹ := by
    intro i
    simp only [he]
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  have e_a : ∀ i, e i * a = a * (e i)⁻¹ := by
    intro i
    calc e i * a = a * (a⁻¹ * e i * a) := by group
      _ = a * (a * e i * a⁻¹) := by rw [hai]
      _ = a * (e i)⁻¹ := by rw [conj_e]
  let f : DihedralGroup 6 → Q := fun x => match x with
    | DihedralGroup.r i => e i
    | DihedralGroup.sr i => a * e i
  have f_mul : ∀ x y, f (x * y) = f x * f y := by
    rintro (i | i) (j | j)
    · rw [DihedralGroup.r_mul_r]
      exact e_add i j
    · rw [DihedralGroup.r_mul_sr]
      show a * e (j - i) = e i * (a * e j)
      calc a * e (j - i) = a * (e j * (e i)⁻¹) := by rw [e_sub]
        _ = a * ((e i)⁻¹ * e j) := by rw [← e_neg, e_comm]
        _ = (a * (e i)⁻¹) * e j := by group
        _ = (e i * a) * e j := by rw [e_a]
        _ = e i * (a * e j) := by group
    · rw [DihedralGroup.sr_mul_r]
      show a * e (i + j) = a * e i * e j
      rw [e_add, mul_assoc]
    · rw [DihedralGroup.sr_mul_sr]
      show e (j - i) = a * e i * (a * e j)
      calc e (j - i) = e j * (e i)⁻¹ := e_sub i j
        _ = (e i)⁻¹ * e j := by rw [← e_neg, e_comm]
        _ = (a * a) * (e i)⁻¹ * e j := by rw [ha, one_mul]
        _ = a * (a * (e i)⁻¹) * e j := by group
        _ = a * (e i * a) * e j := by rw [e_a]
        _ = a * e i * (a * e j) := by group
  let ψ : DihedralGroup 6 →* Q :=
    { toFun := f
      map_one' := by rw [DihedralGroup.one_def]; exact e_zero
      map_mul' := f_mul }
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).mpr ?_
    rintro (i | i) h
    · have h1 : ρ ^ i.val = 1 := h
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hρ] at h2
      have h3 : i.val < 6 := ZMod.val_lt i
      have h4 : i.val = 0 := by omega
      rw [ZMod.val_eq_zero] at h4
      rw [h4, DihedralGroup.one_def]
    · exfalso
      have h1 : a * e i = 1 := h
      apply ha' (-i).val
      show a = e (-i)
      calc a = (e i)⁻¹ := eq_inv_of_mul_eq_one_left h1
        _ = e (-i) := (e_neg i).symm
  have hsurj : Function.Surjective ψ := by
    intro q
    have hz : ∀ i : ℤ, e (i : ZMod 6) = ρ ^ i := by
      intro i
      show ρ ^ (i : ZMod 6).val = ρ ^ i
      rw [← zpow_natCast, ZMod.val_intCast, ← hρ, zpow_mod_orderOf]
    obtain ⟨i, h | h⟩ := hgen q
    · exact ⟨DihedralGroup.r (i : ZMod 6), (hz i).trans h.symm⟩
    · exact ⟨DihedralGroup.sr (i : ZMod 6), (congrArg (a * ·) (hz i)).trans h.symm⟩
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩⟩

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

theorem bar_r_ne_pow [((𝕏(K, J)).subgroupOf (pairNormalizers K J z j)).Normal] (i : ℕ) :
    bar 𝕏(K, J) d.r_mem_Y ≠ bar 𝕏(K, J) d.rho_mem_Y ^ i := by
  intro h
  rw [bar_pow] at h
  have hz := conj_eq_of_bar_eq _ d.r_mem_Y _ h d.c.X_le_centralizer_z
  have hj := conj_eq_of_bar_eq _ d.r_mem_Y _ h d.c.X_le_centralizer_j
  rw [d.c.conj_z d.hr, ← zpow_natCast] at hz
  obtain ⟨k, hk⟩ := (d.c.conj_rho_zpow_z_eq_iff d.hr d.hru d.ht d.htv i).mp hz.symm
  rw [d.c.conj_j_of_not_mem d.hr d.hru, ← zpow_natCast, hk, d.conj_rho_zpow_three_j] at hj
  exact d.c.zj_ne_j hj

theorem exists_D12 (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    ∃ φ : ↥(pairNormalizers K J z j) →* DihedralGroup 6, Function.Surjective φ ∧
      φ.ker = (𝕏(K, J)).subgroupOf (pairNormalizers K J z j) := by
  have := d.normal
  have hinv : bar 𝕏(K, J) d.r_mem_Y * bar 𝕏(K, J) d.rho_mem_Y * (bar 𝕏(K, J) d.r_mem_Y)⁻¹ =
      (bar 𝕏(K, J) d.rho_mem_Y)⁻¹ := by
    rw [d.bar_rho]
    exact dihedral_conj d.bar_r_sq d.bar_t_sq
  obtain ⟨ψ⟩ := exists_dihedral_iso d.bar_r_sq (d.orderOf_rho hA) hinv d.bar_r_ne_pow d.normal_form
  refine ⟨ψ.symm.toMonoidHom.comp (QuotientGroup.mk' _),
    ψ.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext y
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
