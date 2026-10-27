module

public import CFSG.LocalAnalysis.GH72.DDSubgroups

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open CFSG.CGT.Foote81L6

variable {G : Type*} [Group G]

theorem odd_normalizes_e16_of_dd {D D₁ D₂ A : Subgroup G} (hd : DDDecomp D D₁ D₂)
    {u : G} (hu : Odd (orderOf u)) (huN : u ∈ Subgroup.normalizer (D : Set G))
    (hA : A ≤ D) (hA16 : IsE16 A) : u ∈ Subgroup.normalizer (A : Set G) := by
  obtain ⟨a₀, ha₀, ⟨e₀⟩⟩ := hd.dih₁
  obtain ⟨a₁, ha₁, ⟨e₁⟩⟩ := hd.dih₂
  let a : Bool → ℕ := fun b => if b then a₁ else a₀
  have ha_false : a false = a₀ := by simp [a]
  have ha_true : a true = a₁ := by simp [a]
  let α : DihedralGroup (2 ^ a₀) × DihedralGroup (2 ^ a₁) ≃* PX a :=
    { toFun := fun p b =>
        Bool.rec (motive := fun b => DihedralGroup (2 ^ (if b then a₁ else a₀))) p.1 p.2 b
      invFun := fun f => (f false, f true)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro f; funext b; cases b <;> rfl
      map_mul' := by intro p q; funext b; cases b <;> rfl }
  let μ : ↥D₁ × ↥D₂ ≃* ↥D := hd.exists_mulEquiv.choose
  let φ : ↥D ≃* PX a := μ.symm.trans ((e₀.prodCongr e₁).trans α)
  let σ : MulAut ↥D := Subgroup.normalizerMonoidHom (H := D) ⟨u, huN⟩
  have hσ_apply : ∀ d : ↥D, ((σ d : ↥D) : G) = u * (d : G) * u⁻¹ := by
    intro d
    rfl
  let y : MulAut (PX a) := MulAut.congr φ σ
  have hy_apply : ∀ d : ↥D, y (φ d) = φ (σ d) := by
    intro d
    simp only [y, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply]
  have hσ_dvd : orderOf σ ∣ orderOf u := by
    change orderOf ((Subgroup.normalizerMonoidHom (H := D)) ⟨u, huN⟩) ∣ orderOf u
    rw [← Subgroup.orderOf_mk u huN]
    exact orderOf_map_dvd _ _
  have hordery : orderOf y = orderOf σ := MulEquiv.orderOf_eq (MulAut.congr φ) σ
  have hodd : Odd (orderOf y) := by
    rw [hordery]
    exact hu.of_dvd_nat hσ_dvd
  have hfix : ∀ j, 2 ≤ a j → y (zz a j) = zz a j := by
    intro j hj
    by_cases h0 : a false = 1
    ·
      have hj1 : j = true := by
        cases j with
        | false => rw [h0] at hj; omega
        | true => rfl
      subst hj1
      obtain ⟨i, hi2, -, hzi, -⟩ := sig (a := a) (j := true)
        (by rw [ha_true]; exact ha₁) y
      have hi : i = true := by
        cases i with
        | false => rw [h0] at hi2; omega
        | true => rfl
      simpa [hi] using hzi
    ·
      have h0' : 2 ≤ a false := by
        have h1 : 1 ≤ a false := by rw [ha_false]; exact ha₀
        omega
      obtain ⟨i, hi2, -, hzi, -⟩ := sig (a := a) (j := false) h0' y
      obtain ⟨i', hi'2, -, hzi', -⟩ := sig (a := a) (j := true)
        (by rw [ha_true]; exact ha₁) y
      have hpq : zz a false ≠ zz a true := by
        intro h
        have hh := zz_injective (a := a) (i := false) (j := true)
          (by rw [ha_false]; exact ha₀) (by rw [ha_true]; omega) h
        exact Bool.false_ne_true hh
      cases i with
      | false =>
        cases i' with
        | false =>
          exact absurd (y.injective (hzi'.trans hzi.symm)) (Ne.symm hpq)
        | true =>
          cases j with
          | false => exact hzi
          | true => exact hzi'
      | true =>
        cases i' with
        | true =>
          exact absurd (y.injective (hzi.trans hzi'.symm)) hpq
        | false =>
          exfalso
          have h2 : (y ^ 2) (zz a false) = zz a false := by
            rw [pow_two, MulAut.mul_apply, hzi, hzi']
          have heven : ∀ k, (y ^ (2 * k)) (zz a false) = zz a false := by
            intro k
            induction k with
            | zero => simp
            | succ k ih =>
              rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, MulAut.mul_apply, h2, ih]
          obtain ⟨k, hk⟩ := hodd
          have hodd_app : (y ^ orderOf y) (zz a false) = zz a true := by
            rw [hk, pow_succ', MulAut.mul_apply, heven k, hzi]
          rw [pow_orderOf_eq_one, MulAut.one_apply] at hodd_app
          exact hpq hodd_app
  have hcentral : ∀ x z : PX a, z * (x⁻¹ * y x) = (x⁻¹ * y x) * z :=
    comm_central_of_fix (a := a) (N := orderOf y) y hodd (pow_orderOf_eq_one y) hfix
  let AD : Subgroup ↥D := A.subgroupOf D
  let A' : Subgroup (PX a) := AD.map φ.toMonoidHom
  have hcenterD : Subgroup.center ↥D ≤ AD := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    refine hd.center_le hA hA16 z.2 ?_
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨s, hs⟩)
  have hcenter_le : Subgroup.center (PX a) ≤ A' := by
    calc Subgroup.center (PX a) = (Subgroup.center ↥D).map φ.toMonoidHom :=
          (Subgroup.map_center_eq φ).symm
      _ ≤ AD.map φ.toMonoidHom := Subgroup.map_mono hcenterD
  haveI : Fintype (PX a) := inferInstance
  have hmap_le : A'.map y.toMonoidHom ≤ A' := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    have hc : (φ d)⁻¹ * y (φ d) ∈ Subgroup.center (PX a) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact hcentral (φ d) w
    have hyx : y (φ d) = φ d * ((φ d)⁻¹ * y (φ d)) := by group
    change y (φ d) ∈ A'
    rw [hyx]
    exact mul_mem (Subgroup.mem_map_of_mem φ.toMonoidHom hd) (hcenter_le hc)
  have heq : A'.map y.toMonoidHom = A' :=
    Subgroup.eq_of_le_of_card_ge hmap_le
      (le_of_eq (Subgroup.card_map_of_injective y.injective).symm)
  have hmapA_le : A.map (MulAut.conj u).toMonoidHom ≤ A := by
    rintro x ⟨a, ha, rfl⟩
    have hdA : (⟨a, hA ha⟩ : ↥D) ∈ AD := by
      rw [Subgroup.mem_subgroupOf]
      exact ha
    have hφA : φ ⟨a, hA ha⟩ ∈ A' := Subgroup.mem_map_of_mem φ.toMonoidHom hdA
    have hyA : y (φ ⟨a, hA ha⟩) ∈ A' := by
      have h := Subgroup.mem_map_of_mem y.toMonoidHom hφA
      rwa [heq] at h
    have hσA : φ (σ ⟨a, hA ha⟩) ∈ A' := by
      have hyA' : y (φ ⟨a, hA ha⟩) ∈ A' := hyA
      simpa only [hy_apply ⟨a, hA ha⟩] using hyA'
    have hσmem : σ ⟨a, hA ha⟩ ∈ AD :=
      (Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).1 hσA
    rw [Subgroup.mem_subgroupOf] at hσmem
    change u * a * u⁻¹ ∈ A
    rw [← hσ_apply ⟨a, hA ha⟩]
    exact hσmem
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA16.2]; norm_num)
  have hmapA_eq : A.map (MulAut.conj u).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hmapA_le
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj u).injective).symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hmapA_eq


theorem odd_fixes_central_involutions_of_dd {D D₁ D₂ : Subgroup G} (hd : DDDecomp D D₁ D₂)
    (h₁ : IsDihNonab D₁) {u : G} (hu : Odd (orderOf u))
    (huN : u ∈ Subgroup.normalizer (D : Set G)) {z : G} (hzD : z ∈ D)
    (hzc : ∀ y ∈ D, y * z = z * y) (hz2 : orderOf z = 2) : u * z * u⁻¹ = z := by
  obtain ⟨a₀, ha₀, ⟨e₀⟩⟩ := h₁
  obtain ⟨a₁, ha₁, ⟨e₁⟩⟩ := hd.dih₂
  let a : Bool → ℕ := fun b => if b then a₁ else a₀
  have ha_false : a false = a₀ := by simp [a]
  have ha_true : a true = a₁ := by simp [a]
  let α : DihedralGroup (2 ^ a₀) × DihedralGroup (2 ^ a₁) ≃* PX a :=
    { toFun := fun p b =>
        Bool.rec (motive := fun b => DihedralGroup (2 ^ (if b then a₁ else a₀))) p.1 p.2 b
      invFun := fun f => (f false, f true)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro f; funext b; cases b <;> rfl
      map_mul' := by intro p q; funext b; cases b <;> rfl }
  let μ : ↥D₁ × ↥D₂ ≃* ↥D := hd.exists_mulEquiv.choose
  let φ : ↥D ≃* PX a := μ.symm.trans ((e₀.prodCongr e₁).trans α)
  let σ : MulAut ↥D := Subgroup.normalizerMonoidHom (H := D) ⟨u, huN⟩
  have hσ_apply : ∀ d : ↥D, ((σ d : ↥D) : G) = u * (d : G) * u⁻¹ := by
    intro d
    rfl
  let y : MulAut (PX a) := MulAut.congr φ σ
  have hy_apply : ∀ d : ↥D, y (φ d) = φ (σ d) := by
    intro d
    simp only [y, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.apply_symm_apply]
  have hσ_dvd : orderOf σ ∣ orderOf u := by
    change orderOf ((Subgroup.normalizerMonoidHom (H := D)) ⟨u, huN⟩) ∣ orderOf u
    rw [← Subgroup.orderOf_mk u huN]
    exact orderOf_map_dvd _ _
  have hordery : orderOf y = orderOf σ := MulEquiv.orderOf_eq (MulAut.congr φ) σ
  have hodd : Odd (orderOf y) := by
    rw [hordery]
    exact hu.of_dvd_nat hσ_dvd
  have h0' : 2 ≤ a false := by rw [ha_false]; exact ha₀
  have h1' : 2 ≤ a true := by rw [ha_true]; exact ha₁
  have hfix : ∀ j, 2 ≤ a j → y (zz a j) = zz a j := by
    intro j hj
    obtain ⟨i, -, -, hzi, -⟩ := sig (a := a) (j := false) h0' y
    obtain ⟨i', -, -, hzi', -⟩ := sig (a := a) (j := true) h1' y
    have hpq : zz a false ≠ zz a true := by
      intro h
      have hh := zz_injective (a := a) (i := false) (j := true)
        (by rw [ha_false]; omega) (by rw [ha_true]; omega) h
      exact Bool.false_ne_true hh
    cases i with
    | false =>
      cases i' with
      | false =>
        exact absurd (y.injective (hzi'.trans hzi.symm)) (Ne.symm hpq)
      | true =>
        cases j with
        | false => exact hzi
        | true => exact hzi'
    | true =>
      cases i' with
      | true =>
        exact absurd (y.injective (hzi.trans hzi'.symm)) hpq
      | false =>
        exfalso
        have h2 : (y ^ 2) (zz a false) = zz a false := by
          rw [pow_two, MulAut.mul_apply, hzi, hzi']
        have heven : ∀ k, (y ^ (2 * k)) (zz a false) = zz a false := by
          intro k
          induction k with
          | zero => simp
          | succ k ih =>
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, MulAut.mul_apply, h2, ih]
        obtain ⟨k, hk⟩ := hodd
        have hodd_app : (y ^ orderOf y) (zz a false) = zz a true := by
          rw [hk, pow_succ', MulAut.mul_apply, heven k, hzi]
        rw [pow_orderOf_eq_one, MulAut.one_apply] at hodd_app
        exact hpq hodd_app
  set w : PX a := φ ⟨z, hzD⟩ with hw
  have hwcentD : (⟨z, hzD⟩ : ↥D) ∈ Subgroup.center ↥D :=
    Subgroup.mem_center_iff.2 fun d => Subtype.ext (hzc d d.2)
  have hwcentral : w ∈ Subgroup.center (PX a) := by
    rw [hw, ← Subgroup.map_center_eq φ]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hwcentD
  have hcomp : ∀ i (g : DihedralGroup (2 ^ a i)), w i * g = g * w i :=
    (comm_mulSingle_iff (a := a) w).1 fun i g =>
      (Subgroup.mem_center_iff.1 hwcentral (Pi.mulSingle i g)).symm
  have hw0 : w false = 1 ∨ w false = zc (a false) :=
    eq_one_or_zc_of_comm (a := a false) h0' fun g => (hcomp false g).symm
  have hw1 : w true = 1 ∨ w true = zc (a true) :=
    eq_one_or_zc_of_comm (a := a true) h1' fun g => (hcomp true g).symm
  have hcases : w = 1 ∨ w = zz a false ∨ w = zz a true ∨
      w = zz a false * zz a true := by
    rcases hw0 with h0 | h0 <;> rcases hw1 with h1 | h1
    · left
      funext b
      cases b with
      | false => exact h0
      | true => exact h1
    · right; right; left
      funext b
      cases b with
      | false => rw [h0, zz_apply_ne (by decide : false ≠ true)]
      | true => rw [h1, zz_apply_same]
    · right; left
      funext b
      cases b with
      | false => rw [h0, zz_apply_same]
      | true => rw [h1, zz_apply_ne (by decide : true ≠ false)]
    · right; right; right
      funext b
      cases b with
      | false =>
        rw [h0, Pi.mul_apply, zz_apply_same, zz_apply_ne (by decide : false ≠ true), mul_one]
      | true =>
        rw [h1, Pi.mul_apply, zz_apply_ne (by decide : true ≠ false), zz_apply_same, one_mul]
  have hyw : y w = w := by
    rcases hcases with h | h | h | h
    · rw [h, map_one]
    · rw [h]
      change y (zz a false) = zz a false
      exact hfix false h0'
    · rw [h]
      change y (zz a true) = zz a true
      exact hfix true h1'
    · rw [h]
      change y (zz a false * zz a true) = zz a false * zz a true
      calc y (zz a false * zz a true) = y (zz a false) * y (zz a true) := map_mul y _ _
        _ = zz a false * zz a true := by rw [hfix false h0', hfix true h1']
  have hyw' : y (φ ⟨z, hzD⟩) = φ ⟨z, hzD⟩ := by
    simpa [hw] using hyw
  have hσz : σ ⟨z, hzD⟩ = ⟨z, hzD⟩ := by
    refine φ.injective ?_
    rw [← hy_apply ⟨z, hzD⟩]
    exact hyw'
  change u * ((⟨z, hzD⟩ : ↥D) : G) * u⁻¹ = z
  rw [← hσ_apply ⟨z, hzD⟩]
  simpa using congrArg Subtype.val hσz

end CFSG.GH72
