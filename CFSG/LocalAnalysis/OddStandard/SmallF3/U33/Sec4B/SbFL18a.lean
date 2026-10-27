module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma conj_eq_inv_of_sq_eq_one {g x : G} (hg2 : g * g = 1)
    (h : (g * x) * (g * x) = 1) : g * x * g = x⁻¹ := by
  have hg_inv : g⁻¹ = g := (eq_inv_of_mul_eq_one_right hg2).symm
  have h' : g * x = (g * x)⁻¹ := (mul_eq_one_iff_eq_inv).mp h
  rw [h']
  simp only [mul_inv_rev, hg_inv]
  rw [mul_assoc, hg2, mul_one]

private lemma comm_mem_Y_of_sq_eq_one {Ξ Y : Subgroup G} {g : G} (hg2 : g * g = 1)
    (hsq : ∀ x ∈ Ξ, x * x ∈ Y) {x : G} (hx : x ∈ Ξ)
    (ht : (g * x) * (g * x) = 1) : g * x * g⁻¹ * x⁻¹ ∈ Y := by
  have hg_inv : g⁻¹ = g := (eq_inv_of_mul_eq_one_right hg2).symm
  have h1 : g * x * g = x⁻¹ := conj_eq_inv_of_sq_eq_one hg2 ht
  have h2 : g * x * g⁻¹ * x⁻¹ = (x * x)⁻¹ := by
    rw [hg_inv, h1]
    group
  rw [h2]
  exact Y.inv_mem (hsq x hx)

private lemma inv_mul_comm_of_T {Ξ Y : Subgroup G} {g : G} (hg2 : g * g = 1)
    (hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x) (hY2 : ∀ y ∈ Y, y * y = 1)
    {b x : G} (hbΞ : b ∈ Ξ) (hbT : (g * b) * (g * b) = 1) (hxΞ : x ∈ Ξ)
    (hxT : (g * x) * (g * x) = 1) (hy : b⁻¹ * x ∈ Y) :
    g * (b⁻¹ * x) = (b⁻¹ * x) * g := by
  have hg_inv : g⁻¹ = g := (eq_inv_of_mul_eq_one_right hg2).symm
  have hy2 : (b⁻¹ * x) * (b⁻¹ * x) = 1 := hY2 _ hy
  have hby : b * (b⁻¹ * x) = (b⁻¹ * x) * b := hYc _ hy b hbΞ
  have hbg : g * b * g = b⁻¹ := conj_eq_inv_of_sq_eq_one hg2 hbT
  have hxg : g * x * g = x⁻¹ := conj_eq_inv_of_sq_eq_one hg2 hxT
  have hgbg : (g * b * g)⁻¹ = g * b⁻¹ * g := by
    rw [mul_inv_rev, mul_inv_rev, hg_inv]
    group
  have hstep : (g * b⁻¹ * g) * (g * x * g) = g * (b⁻¹ * x) * g := by
    calc (g * b⁻¹ * g) * (g * x * g)
        = g * b⁻¹ * ((g * g) * (x * g)) := by group
      _ = g * b⁻¹ * (1 * (x * g)) := by rw [hg2]
      _ = g * (b⁻¹ * x) * g := by group
  have h1 : g * (b⁻¹ * x) * g = (g * b * g)⁻¹ * (g * x * g) := by
    rw [← hstep, ← hgbg]
  have hgyg : g * (b⁻¹ * x) * g = b⁻¹ * x := by
    rw [h1, hbg, hxg]
    have hx_eq : x = b * (b⁻¹ * x) := by group
    have hy_inv : (b⁻¹ * x)⁻¹ = b⁻¹ * x := (eq_inv_of_mul_eq_one_right hy2).symm
    have hx_inv : x⁻¹ = (b⁻¹ * x) * b⁻¹ := by
      calc x⁻¹ = (b * (b⁻¹ * x))⁻¹ := congrArg Inv.inv hx_eq
        _ = (b⁻¹ * x)⁻¹ * b⁻¹ := by rw [mul_inv_rev]
        _ = (b⁻¹ * x) * b⁻¹ := by rw [hy_inv]
    rw [inv_inv, hx_inv, ← mul_assoc, hby]
    group
  have htwo : g * (b⁻¹ * x) * g = (b⁻¹ * x) * g * g := by
    rw [hgyg, mul_assoc, hg2, mul_one]
  exact mul_right_cancel htwo

private lemma inv_mul_comm_of_cent {g b x : G} (hb : b * g = g * b) (hx : x * g = g * x) :
    g * (b⁻¹ * x) = (b⁻¹ * x) * g := by
  have hx_eq : x = b * (b⁻¹ * x) := by group
  have h1 : b * ((b⁻¹ * x) * g) = b * (g * (b⁻¹ * x)) := by
    calc b * ((b⁻¹ * x) * g) = (b * (b⁻¹ * x)) * g := by group
      _ = x * g := (congrArg (fun z => z * g) hx_eq).symm
      _ = g * x := hx
      _ = g * (b * (b⁻¹ * x)) := congrArg (fun z => g * z) hx_eq
      _ = b * (g * (b⁻¹ * x)) := by rw [← mul_assoc, hb.symm, mul_assoc]
  exact (mul_left_cancel h1).symm

private theorem card_le_sixteen_of_data {Y D : Subgroup G} {g : G}
    (hY : Nat.card Y = 16)
    (hCY : Nat.card {y : G // y ∈ Y ∧ g * y = y * g} ≤ 4)
    (hYD : Y ≤ D) (hDcard : Nat.card D ≤ 64)
    (P : G → Prop) (hPD : ∀ x : G, P x → x ∈ D)
    (hcomm : ∀ b x : G, P b → P x → b⁻¹ * x ∈ Y →
      g * (b⁻¹ * x) = (b⁻¹ * x) * g) :
    Nat.card {x : G // P x} ≤ 16 := by
  classical
  let T : Type := {x : G // P x}
  let CY : Type := {y : G // y ∈ Y ∧ g * y = y * g}
  let coset : T → D ⧸ Y.subgroupOf D := fun x =>
    ((⟨x.1, hPD x.1 x.2⟩ : D) : D ⧸ Y.subgroupOf D)
  let S : Type := Set.range coset
  let base : S → T := fun q => Classical.choose (Set.mem_range.mp q.2)
  have base_spec : ∀ q : S, coset (base q) = q.1 := by
    intro q
    exact Classical.choose_spec (Set.mem_range.mp q.2)
  have y_mem : ∀ x : T, (base ⟨coset x, ⟨x, rfl⟩⟩).1⁻¹ * x.1 ∈ Y := by
    intro x
    have hspec := base_spec ⟨coset x, ⟨x, rfl⟩⟩
    have hq : ((⟨(base ⟨coset x, ⟨x, rfl⟩⟩).1,
          hPD _ (base ⟨coset x, ⟨x, rfl⟩⟩).2⟩ : D) : D ⧸ Y.subgroupOf D)
        = ((⟨x.1, hPD _ x.2⟩ : D) : D ⧸ Y.subgroupOf D) := by
      simpa only [coset] using hspec
    have hmem := (QuotientGroup.eq).mp hq
    simpa [Subgroup.mem_subgroupOf] using hmem
  let Φ : T → CY × S := fun x =>
    (⟨(base ⟨coset x, ⟨x, rfl⟩⟩).1⁻¹ * x.1, y_mem x,
      hcomm (base ⟨coset x, ⟨x, rfl⟩⟩).1 x.1 (base ⟨coset x, ⟨x, rfl⟩⟩).2 x.2
        (y_mem x)⟩,
      ⟨coset x, ⟨x, rfl⟩⟩)
  have hinj : Function.Injective Φ := by
    intro x x' hxx'
    have hcoset : coset x = coset x' :=
      congrArg (fun p : CY × S => (p.2 : S).1) hxx'
    have hy : (base ⟨coset x, ⟨x, rfl⟩⟩).1⁻¹ * x.1
        = (base ⟨coset x', ⟨x', rfl⟩⟩).1⁻¹ * x'.1 := by
      have h := congrArg (fun p : CY × S => (p.1 : CY).1) hxx'
      simpa [Φ] using h
    have hbase : base ⟨coset x, ⟨x, rfl⟩⟩ = base ⟨coset x', ⟨x', rfl⟩⟩ :=
      congrArg base (Subtype.ext hcoset)
    have hb : ((base ⟨coset x, ⟨x, rfl⟩⟩).1 : G)
        = ((base ⟨coset x', ⟨x', rfl⟩⟩).1 : G) :=
      congrArg (fun t : T => (t : G)) hbase
    apply Subtype.ext
    calc (x : G) = ((base ⟨coset x, ⟨x, rfl⟩⟩).1 : G) *
          (((base ⟨coset x, ⟨x, rfl⟩⟩).1 : G)⁻¹ * (x : G)) := by group
      _ = ((base ⟨coset x', ⟨x', rfl⟩⟩).1 : G) *
          (((base ⟨coset x', ⟨x', rfl⟩⟩).1 : G)⁻¹ * (x' : G)) := by rw [hy, hb]
      _ = (x' : G) := by group
  have hquot : Nat.card (D ⧸ Y.subgroupOf D) ≤ 4 := by
    have hY'card : Nat.card (Y.subgroupOf D) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv, hY]
    have hmul := Subgroup.card_mul_index (Y.subgroupOf D)
    rw [hY'card] at hmul
    have hidx : (Y.subgroupOf D).index ≤ 4 := by
      have hle : 16 * (Y.subgroupOf D).index ≤ 16 * 4 := by
        rw [hmul, show (16 : ℕ) * 4 = 64 by norm_num]
        exact hDcard
      exact Nat.le_of_mul_le_mul_left hle (by norm_num)
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hS : Nat.card S ≤ 4 := by
    have h1 : Nat.card S ≤ Nat.card (D ⧸ Y.subgroupOf D) :=
      Nat.card_le_card_of_injective (fun q : S => q.1) (fun _ _ h => Subtype.ext h)
    exact le_trans h1 hquot
  have hCY' : Nat.card CY ≤ 4 := by
    change Nat.card {y : G // y ∈ Y ∧ g * y = y * g} ≤ 4
    exact hCY
  calc Nat.card T ≤ Nat.card (CY × S) := Nat.card_le_card_of_injective Φ hinj
    _ = Nat.card CY * Nat.card S := Nat.card_prod _ _
    _ ≤ 4 * 4 := Nat.mul_le_mul hCY' hS
    _ = 16 := by norm_num

theorem fl2_card_T_le {Ξ Y D : Subgroup G} {g : G} (hg2 : g * g = 1)
    (hgΞ : ∀ x ∈ Ξ, g * x * g⁻¹ ∈ Ξ) (hgY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hYΞ : Y ≤ Ξ)
    (hYc : ∀ y ∈ Y, ∀ x ∈ Ξ, x * y = y * x) (hY2 : ∀ y ∈ Y, y * y = 1)
    (hsq : ∀ x ∈ Ξ, x * x ∈ Y) (hY : Nat.card Y = 16)
    (hCY : Nat.card {y : G // y ∈ Y ∧ g * y = y * g} ≤ 4) (hDΞ : D ≤ Ξ)
    (hD : ∀ x ∈ Ξ, g * x * g⁻¹ * x⁻¹ ∈ Y → x ∈ D) (hDcard : Nat.card D ≤ 64) :
    Nat.card {x : G // x ∈ Ξ ∧ (g * x) * (g * x) = 1} ≤ 16 := by
  have hYD : Y ≤ D := by
    intro y hy
    exact hD y (hYΞ hy) (Y.mul_mem (hgY y hy) (Y.inv_mem hy))
  refine card_le_sixteen_of_data (P := fun x => x ∈ Ξ ∧ (g * x) * (g * x) = 1)
    hY hCY hYD hDcard ?_ ?_
  · intro x hx
    exact hD x hx.1 (comm_mem_Y_of_sq_eq_one hg2 hsq hx.1 hx.2)
  · intro b x hb hx hy
    exact inv_mul_comm_of_T hg2 hYc hY2 hb.1 hb.2 hx.1 hx.2 hy

theorem fl2_card_cent_le {Ξ Y D : Subgroup G} {g : G} (hgY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hYΞ : Y ≤ Ξ) (hY : Nat.card Y = 16)
    (hCY : Nat.card {y : G // y ∈ Y ∧ g * y = y * g} ≤ 4) (hDΞ : D ≤ Ξ)
    (hD : ∀ x ∈ Ξ, g * x * g⁻¹ * x⁻¹ ∈ Y → x ∈ D) (hDcard : Nat.card D ≤ 64) :
    Nat.card {x : G // x ∈ Ξ ∧ g * x = x * g} ≤ 16 := by
  have hYD : Y ≤ D := by
    intro y hy
    exact hD y (hYΞ hy) (Y.mul_mem (hgY y hy) (Y.inv_mem hy))
  refine card_le_sixteen_of_data (P := fun x => x ∈ Ξ ∧ g * x = x * g)
    hY hCY hYD hDcard ?_ ?_
  · intro x hx
    apply hD x hx.1
    have h1 : g * x * g⁻¹ * x⁻¹ = 1 := by rw [hx.2]; group
    rw [h1]
    exact Y.one_mem
  · intro b x hb hx _hy
    exact inv_mul_comm_of_cent hb.2.symm hx.2.symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
