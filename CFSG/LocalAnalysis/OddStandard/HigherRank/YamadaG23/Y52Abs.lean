module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement
open scoped IsMulCommutative

private lemma rotate_helper {M : Type*} [CommGroup M] (x a b c : M) (hx : x * x = 1) :
    (x * a) * (x * b) * (x * c) = x * (a * b * c) := by
  have hx3 : x * x * x = x := by
    calc x * x * x = (x * x) * x := rfl
      _ = 1 * x := by rw [hx]
      _ = x := one_mul x
  calc (x * a) * (x * b) * (x * c) = (x * x * x) * (a * b * c) := by ac_rfl
    _ = x * (a * b * c) := by rw [hx3]

theorem y52_abs {Q : Type} [Group Q] (C : Subgroup Q) (b u v v' a : Q)
    (hb : b ≠ 1) (hb2 : b * b = 1) (hbC : b ∈ C) (hbc : ∀ x ∈ C, x * b = b * x)
    (huC : u ∈ C) (hvC : v ∈ C) (hv'C : v' ∈ C)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hv'2 : v' * v' = 1)
    (hcov : ∀ x ∈ C, ∃ i : ℕ, ∃ y ∈ ({1, u, v, v'} : Set Q), x = b ^ i * y)
    (huvv' : u * v * v' = 1 ∨ u * v * v' = b)
    (ha2 : a * a = 1) (hab : a * b * a⁻¹ = b) (hau : a * u * a⁻¹ = b * u)
    (hav : a * v * a⁻¹ = v' ∨ a * v * a⁻¹ = b * v')
    (hav' : a * v' * a⁻¹ = v ∨ a * v' * a⁻¹ = b * v) : False := by
  have hyCmem : ∀ y ∈ ({1, u, v, v'} : Set Q), y ∈ C := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact huC
    · exact hvC
    · exact hv'C
  have hsq : ∀ x ∈ C, x * x = 1 := by
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := hcov x hx
    have hyy : y * y = 1 := by
      rcases hy with rfl | rfl | rfl | rfl
      · exact one_mul 1
      · exact hu2
      · exact hv2
      · exact hv'2
    have hby : Commute b y := (hbc y (hyCmem y hy)).symm
    have hbyi : Commute (b ^ i) y := hby.pow_left i
    have hbii : (b ^ i) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm i 2, pow_mul, pow_two, hb2, one_pow]
    calc (b ^ i * y) * (b ^ i * y) = (b ^ i * y) ^ 2 := (pow_two _).symm
      _ = (b ^ i) ^ 2 * y ^ 2 := hbyi.mul_pow 2
      _ = 1 := by rw [hbii, pow_two, hyy, mul_one]
  have hCcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    have hx2 := hsq x hx
    have hy2 := hsq y hy
    have hxy2 := hsq (x * y) (C.mul_mem hx hy)
    have hxy_inv : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy2
    have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    calc x * y = (x * y)⁻¹ := hxy_inv.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hx_inv, hy_inv]
  haveI hCcommI : IsMulCommutative ↥C :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hCcomm x x.2 y y.2)
  have hab_i : ∀ i : ℕ, a * b ^ i * a⁻¹ = b ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ']
      calc a * (b * b ^ i) * a⁻¹ = (a * b * a⁻¹) * (a * b ^ i * a⁻¹) := by group
        _ = b * b ^ i := by rw [hab, ih]
  have ha_set : ∀ y ∈ ({1, u, v, v'} : Set Q), a * y * a⁻¹ ∈ C := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · simpa using C.one_mem
    · rw [hau]; exact C.mul_mem hbC huC
    · rcases hav with h | h
      · rw [h]; exact hv'C
      · rw [h]; exact C.mul_mem hbC hv'C
    · rcases hav' with h | h
      · rw [h]; exact hvC
      · rw [h]; exact C.mul_mem hbC hvC
  have haC : ∀ x ∈ C, a * x * a⁻¹ ∈ C := by
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := hcov x hx
    rw [show a * (b ^ i * y) * a⁻¹ = (a * b ^ i * a⁻¹) * (a * y * a⁻¹) by group]
    exact C.mul_mem (by rw [hab_i]; exact C.pow_mem hbC i) (ha_set y hy)
  let α : ↥C →* ↥C :=
    { toFun := fun x => ⟨a * x * a⁻¹, haC x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change a * ((x : Q) * (y : Q)) * a⁻¹ =
          (a * (x : Q) * a⁻¹) * (a * (y : Q) * a⁻¹)
        group }
  have hα2 : ∀ x : ↥C, α (α x) = x := by
    intro x
    apply Subtype.ext
    change a * (a * (x : Q) * a⁻¹) * a⁻¹ = (x : Q)
    calc a * (a * (x : Q) * a⁻¹) * a⁻¹ = (a * a) * (x : Q) * (a * a)⁻¹ := by group
      _ = (x : Q) := by rw [ha2]; group
  let bC : ↥C := ⟨b, hbC⟩
  let uC : ↥C := ⟨u, huC⟩
  let vC : ↥C := ⟨v, hvC⟩
  let v'C : ↥C := ⟨v', hv'C⟩
  have hαb : α bC = bC := by
    apply Subtype.ext
    simpa [α, bC] using hab
  have hαu : α uC = bC * uC := by
    apply Subtype.ext
    simpa [α, uC, bC] using hau
  have hαv : α vC = v'C ∨ α vC = bC * v'C := by
    rcases hav with h | h
    · left; apply Subtype.ext; simpa [α, vC, v'C] using h
    · right; apply Subtype.ext; simpa [α, vC, bC, v'C] using h
  have hαv' : α v'C = vC ∨ α v'C = bC * vC := by
    rcases hav' with h | h
    · left; apply Subtype.ext; simpa [α, v'C, vC] using h
    · right; apply Subtype.ext; simpa [α, v'C, bC, vC] using h
  have hδC : uC * vC * v'C = 1 ∨ uC * vC * v'C = bC := by
    rcases huvv' with h | h
    · left; apply Subtype.ext; simpa [uC, vC, v'C] using h
    · right; apply Subtype.ext; simpa [uC, vC, v'C, bC] using h
  have hb2C : bC * bC = 1 := by apply Subtype.ext; simpa [bC] using hb2
  rcases hαv with hv | hv <;> rcases hαv' with hv' | hv' <;> rcases hδC with hδ | hδ
  ·
    have hkey : (bC * uC) * v'C * vC = α (uC * vC * v'C) := by
      rw [show α (uC * vC * v'C) = (bC * uC) * v'C * vC by
        rw [map_mul, map_mul, hαu, hv, hv']]
    have hkey2 := hkey
    rw [show (bC * uC) * v'C * vC = bC * (uC * vC * v'C) by ac_rfl] at hkey2
    rw [hδ, mul_one, map_one] at hkey2
    exact absurd (congrArg Subtype.val hkey2) hb
  ·
    have hkey : (bC * uC) * v'C * vC = α (uC * vC * v'C) := by
      rw [show α (uC * vC * v'C) = (bC * uC) * v'C * vC by
        rw [map_mul, map_mul, hαu, hv, hv']]
    have hkey2 := hkey
    rw [show (bC * uC) * v'C * vC = bC * (uC * vC * v'C) by ac_rfl] at hkey2
    rw [hδ, hb2C, hαb] at hkey2
    exact absurd (congrArg Subtype.val hkey2.symm) hb
  ·
    have h := hα2 vC
    rw [hv, hv'] at h
    have h2 : bC * vC = 1 * vC := by rw [one_mul]; exact h
    exact absurd (congrArg Subtype.val (mul_right_cancel h2)) hb
  ·
    have h := hα2 vC
    rw [hv, hv'] at h
    have h2 : bC * vC = 1 * vC := by rw [one_mul]; exact h
    exact absurd (congrArg Subtype.val (mul_right_cancel h2)) hb
  ·
    have h := hα2 vC
    rw [hv, map_mul, hαb, hv'] at h
    have h2 : bC * vC = 1 * vC := by rw [one_mul]; exact h
    exact absurd (congrArg Subtype.val (mul_right_cancel h2)) hb
  ·
    have h := hα2 vC
    rw [hv, map_mul, hαb, hv'] at h
    have h2 : bC * vC = 1 * vC := by rw [one_mul]; exact h
    exact absurd (congrArg Subtype.val (mul_right_cancel h2)) hb
  ·
    have hkey : (bC * uC) * (bC * v'C) * (bC * vC) = α (uC * vC * v'C) := by
      rw [show α (uC * vC * v'C) = (bC * uC) * (bC * v'C) * (bC * vC) by
        rw [map_mul, map_mul, hαu, hv, hv']]
    have hkey2 := hkey
    rw [rotate_helper bC uC v'C vC hb2C,
      show uC * v'C * vC = uC * vC * v'C by ac_rfl] at hkey2
    rw [hδ, mul_one, map_one] at hkey2
    exact absurd (congrArg Subtype.val hkey2) hb
  ·
    have hkey : (bC * uC) * (bC * v'C) * (bC * vC) = α (uC * vC * v'C) := by
      rw [show α (uC * vC * v'C) = (bC * uC) * (bC * v'C) * (bC * vC) by
        rw [map_mul, map_mul, hαu, hv, hv']]
    have hkey2 := hkey
    rw [rotate_helper bC uC v'C vC hb2C,
      show uC * v'C * vC = uC * vC * v'C by ac_rfl] at hkey2
    rw [hδ, hb2C, hαb] at hkey2
    exact absurd (congrArg Subtype.val hkey2.symm) hb

theorem y52_mod_abs {Q : Type} [Group Q] (C N : Subgroup Q) (t k : Q)
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (htC : t ∈ C) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hk3 : k ^ 3 = 1) (hkC : ∀ x ∈ C, k * x * k⁻¹ ∈ C) (hkt : k * t * k⁻¹ = t)
    (hfix : ∀ x ∈ C, k * x * k⁻¹ = x → x = 1 ∨ x = t)
    (hNC : ∀ n ∈ N, ∀ x ∈ C, n * x * n⁻¹ ∈ C) (hNt : ∀ n ∈ N, n * t * n⁻¹ = t)
    (hNk : ∀ n ∈ N, n * k * n⁻¹ = k ∨ n * k * n⁻¹ = k⁻¹) : t ∉ ⁅C, N⁆ := by
  haveI hCcommI : IsMulCommutative ↥C :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hC x x.2 y y.2)
  let σ : ↥C →* ↥C :=
    { toFun := fun x => ⟨k * x * k⁻¹, hkC x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change k * ((x : Q) * (y : Q)) * k⁻¹ = (k * (x : Q) * k⁻¹) * (k * (y : Q) * k⁻¹)
        group }
  let tC : ↥C := ⟨t, htC⟩
  have ht2C : tC * tC = 1 := by apply Subtype.ext; simpa [tC] using ht2
  have hσ3 : ∀ x : ↥C, σ (σ (σ x)) = x := by
    intro x
    apply Subtype.ext
    change k * (k * (k * (x : Q) * k⁻¹) * k⁻¹) * k⁻¹ = (x : Q)
    have h : k * (k * (k * (x : Q) * k⁻¹) * k⁻¹) * k⁻¹ =
        (k * k * k) * (x : Q) * (k * k * k)⁻¹ := by group
    have hk3' : k * k * k = 1 := by
      calc k * k * k = (k * k) * k := rfl
        _ = k ^ 2 * k := by rw [pow_two]
        _ = k ^ (2 + 1) := (pow_succ k 2).symm
        _ = 1 := by rw [show (2 : ℕ) + 1 = 3 by norm_num, hk3]
    rw [h, hk3']
    group
  let ν : ↥C →* ↥C := (MonoidHom.id ↥C) * σ * σ.comp σ
  have hνapply : ∀ x : ↥C, ν x = x * σ x * σ (σ x) := by intro x; rfl
  have hσfix : ∀ x : ↥C, σ (ν x) = ν x := by
    intro x
    rw [hνapply, map_mul, map_mul, hσ3 x]
    ac_rfl
  have hνcases : ∀ x : ↥C, ν x = 1 ∨ ν x = tC := by
    intro x
    have hfixk : k * (ν x : Q) * k⁻¹ = (ν x : Q) := by
      simpa [σ] using congrArg Subtype.val (hσfix x)
    rcases hfix (ν x : Q) (ν x).2 hfixk with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hσt : σ tC = tC := by apply Subtype.ext; simpa [σ, tC] using hkt
  have hνt : ν tC = tC := by
    rw [hνapply, hσt, hσt, ht2C, one_mul]
  have hker_le : ⁅C, N⁆ ≤ (ν.ker).map C.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx n hn
    let τ : ↥C →* ↥C :=
      { toFun := fun y => ⟨n * y * n⁻¹, hNC n hn y y.2⟩
        map_one' := by ext; simp
        map_mul' := fun y z => by
          apply Subtype.ext
          change n * ((y : Q) * (z : Q)) * n⁻¹ = (n * (y : Q) * n⁻¹) * (n * (z : Q) * n⁻¹)
          group }
    have hdisj : (∀ y : ↥C, σ (τ y) = τ (σ y)) ∨
        (∀ y : ↥C, σ (τ y) = τ (σ (σ y))) := by
      rcases hNk n hn with hk | hk
      · left
        intro y
        apply Subtype.ext
        change k * (n * (y : Q) * n⁻¹) * k⁻¹ = n * (k * (y : Q) * k⁻¹) * n⁻¹
        have hnk : k * n = n * k := by
          have h1 : n * k = k * n := by
            calc n * k = (n * k * n⁻¹) * n := by group
              _ = k * n := by rw [hk]
          exact h1.symm
        rw [show k * (n * (y : Q) * n⁻¹) * k⁻¹ = (k * n) * (y : Q) * (k * n)⁻¹ by group,
          show n * (k * (y : Q) * k⁻¹) * n⁻¹ = (n * k) * (y : Q) * (n * k)⁻¹ by group, hnk]
      · right
        intro y
        apply Subtype.ext
        change k * (n * (y : Q) * n⁻¹) * k⁻¹ =
          n * (k * (k * (y : Q) * k⁻¹) * k⁻¹) * n⁻¹
        have hkinv : k⁻¹ = k * k := by
          calc k⁻¹ = k⁻¹ * 1 := (mul_one _).symm
            _ = k⁻¹ * k ^ 3 := by rw [hk3]
            _ = k ^ 2 := by group
            _ = k * k := by rw [pow_two]
        have hn_eq : n = k⁻¹ * n * k⁻¹ := by
          calc n = (n * k) * k⁻¹ := by group
            _ = (k⁻¹ * n) * k⁻¹ := by rw [show n * k = k⁻¹ * n by
                calc n * k = (n * k * n⁻¹) * n := by group
                  _ = k⁻¹ * n := by rw [hk]]
        have hkn1 : k * n = n * k⁻¹ := by
          conv_lhs => rw [hn_eq]
          group
        have hkn : k * n = n * (k * k) := by rw [hkn1, hkinv]
        rw [show k * (n * (y : Q) * n⁻¹) * k⁻¹ = (k * n) * (y : Q) * (k * n)⁻¹ by group,
          show n * (k * (k * (y : Q) * k⁻¹) * k⁻¹) * n⁻¹ =
            (n * (k * k)) * (y : Q) * (n * (k * k))⁻¹ by group, hkn]
    have hντ : ∀ y : ↥C, ν (τ y) = τ (ν y) := by
      intro y
      rcases hdisj with hσ | hσ
      · calc ν (τ y) = (τ y) * σ (τ y) * σ (σ (τ y)) := hνapply (τ y)
          _ = (τ y) * τ (σ y) * τ (σ (σ y)) := by rw [hσ y, hσ (σ y)]
          _ = τ (y * σ y * σ (σ y)) := by rw [map_mul, map_mul]
          _ = τ (ν y) := by rw [← hνapply y]
      · calc ν (τ y) = (τ y) * σ (τ y) * σ (σ (τ y)) := hνapply (τ y)
          _ = (τ y) * τ (σ (σ y)) * τ (σ y) := by
                rw [hσ y, hσ (σ (σ y)), hσ3]
          _ = τ (y * σ y * σ (σ y)) := by rw [map_mul, map_mul]; ac_rfl
          _ = τ (ν y) := by rw [← hνapply y]
    let xC : ↥C := ⟨x, hx⟩
    have hτν : τ (ν xC) = ν xC := by
      rcases hνcases xC with h | h
      · rw [h, map_one]
      · rw [h]
        apply Subtype.ext
        change n * t * n⁻¹ = t
        exact hNt n hn
    have hτx : ν (τ xC) = ν xC := by rw [hντ xC, hτν]
    have hmem : ⁅x, n⁆ ∈ C := by
      have h1 : n * x⁻¹ * n⁻¹ ∈ C := hNC n hn x⁻¹ (C.inv_mem hx)
      have h2 : x * (n * x⁻¹ * n⁻¹) ∈ C := C.mul_mem hx h1
      simpa [commutatorElement_def, mul_assoc] using h2
    have hker : ν (⟨⁅x, n⁆, hmem⟩ : ↥C) = 1 := by
      have hEq : (⟨⁅x, n⁆, hmem⟩ : ↥C) = xC * (τ xC)⁻¹ := by
        apply Subtype.ext
        change ⁅x, n⁆ = x * (n * x * n⁻¹)⁻¹
        rw [commutatorElement_def]
        group
      rw [hEq, map_mul, map_inv, hτx]
      simp
    exact Subgroup.mem_map.mpr
      ⟨⟨⁅x, n⁆, hmem⟩, by rw [MonoidHom.mem_ker]; exact hker, rfl⟩
  intro ht
  obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp (hker_le ht)
  have hct : c = tC := Subtype.ext hce
  have hker := MonoidHom.mem_ker.mp hc
  rw [hct, hνt] at hker
  exact ht1 (by simpa [tC] using (Subtype.ext_iff.mp hker))

end CFSG.OddStandard.HigherRank.YamadaG23
