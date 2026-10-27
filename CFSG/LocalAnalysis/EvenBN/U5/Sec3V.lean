module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4End
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

section Generic

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hB]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem commutator_sup_le {X I N : Subgroup G} (hIX : I ≤ normalizer (X : Set G))
    (hI : ∀ i ∈ I, ∀ j ∈ I, i * j = j * i) (hXN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hXX : ∀ x ∈ X, ∀ x' ∈ X, x * x' * x⁻¹ * x'⁻¹ ∈ N)
    (hIXN : ∀ i ∈ I, ∀ x ∈ X, i * x * i⁻¹ * x⁻¹ ∈ N) : ⁅X ⊔ I, X ⊔ I⁆ ≤ N := by
  refine commutator_le.2 fun w hw w' hw' => ?_
  obtain ⟨x, hx, i, hi, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hIX hw
  obtain ⟨x', hx', i', hi', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hIX hw'
  have hii : i' * i⁻¹ = i⁻¹ * i' := hI i' hi' i⁻¹ (inv_mem hi)
  have e : ⁅x * i, x' * i'⁆ = (x * (i * x' * i⁻¹ * x'⁻¹) * x⁻¹) * (x * x' * x⁻¹ * x'⁻¹) *
      (x' * (i' * x * i'⁻¹ * x⁻¹) * x'⁻¹)⁻¹ := by
    calc ⁅x * i, x' * i'⁆ = x * i * x' * (i' * i⁻¹) * x⁻¹ * i'⁻¹ * x'⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = x * i * x' * (i⁻¹ * i') * x⁻¹ * i'⁻¹ * x'⁻¹ := by rw [hii]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem (hXN x hx _ (hIXN i hi x' hx')) (hXX x hx x' hx'))
    (inv_mem (hXN x' hx' _ (hIXN i' hi' x hx)))

end Generic

section Torus

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem torus_comm {j j' : hypSU h 2 1} (hj : j ∈ hypTorus h 2 1) (hj' : j' ∈ hypTorus h 2 1) :
    j * j' = j' * j := by
  apply mat_injective
  rw [mat_mul, mat_mul, torus_mat hj, torus_mat hj', Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem odd_card_hypTorus (h : UnitaryFieldData 2 f K) : Odd (Nat.card (hypTorus h 2 1)) := by
  have := h.charP
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨⟨j, hj⟩, hj2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have hjj : j * j = 1 := by
    have := pow_orderOf_eq_one (⟨j, hj⟩ : hypTorus h 2 1)
    rw [hj2, sq] at this
    exact congrArg Subtype.val this
  have hdiag : ∀ a, mat j a a = 1 := by
    intro a
    have e := torus_mul_apply hj hj a
    rw [hjj, mat_one, Matrix.one_apply_eq] at e
    have e2 : (mat j a a - 1) * (mat j a a - 1) = 0 := by
      linear_combination -e + (1 - mat j a a) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.1 (mul_self_eq_zero.1 e2)
  have hj1 : j = 1 := by
    apply mat_injective
    rw [torus_mat hj, mat_one]
    have : (fun a => mat j a a) = fun _ => (1 : K) := funext hdiag
    rw [this, Matrix.diagonal_one]
  have : (⟨j, hj⟩ : hypTorus h 2 1) = 1 := Subtype.ext hj1
  rw [this, orderOf_one] at hj2
  exact absurd hj2 (by norm_num)

end Torus

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

open CFSG.EvenSmallLie.UnitarySix.YamadaD (crossed_eq_one_iff crossed_conj crossedHom
  crossedHom_apply mem_ker_crossedHom card_eq_card_ker_mul_card_range)

omit [Finite G] in
theorem I_comm (d : Data G h) {i j : G} (hi : i ∈ d.I) (hj : j ∈ d.I) : i * j = j * i := by
  obtain ⟨i', hi', rfl⟩ := hi
  obtain ⟨j', hj', rfl⟩ := hj
  rw [← map_mul, ← map_mul, torus_comm hi' hj']

omit [Finite G] in
theorem odd_card_I (d : Data G h) : Odd (Nat.card d.I) :=
  Odd.of_dvd_nat (odd_card_hypTorus h) (Subgroup.card_map_dvd _ _)

omit [Finite G] in
theorem I₃_le_I (d : Data G h) : d.I₃ ≤ d.I := d.pull_mono (torusEq_le _)

theorem coprime_card_of_odd {X Y : Subgroup G} (hX : Odd (Nat.card X)) (hY : IsPGroup 2 Y) :
    (Nat.card X).Coprime (Nat.card Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY
  rw [hk]
  exact Nat.Coprime.pow_right _ (Odd.coprime_two_right hX)

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set G) :=
  mem_normalizer_of_conj_le fun x hx => hg ▸ ⟨x, hx, rfl⟩

omit [Finite G] in
theorem coe_ιZp_mul_inv (d : Data G h) (a b : h.fixedField) :
    (d.ιZp (Multiplicative.ofAdd a) : G) * (d.ιZp (Multiplicative.ofAdd b) : G)⁻¹ =
      d.ιZp (Multiplicative.ofAdd (a - b)) := by
  rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← map_inv, ← map_mul, sub_eq_add_neg, ofAdd_add,
    ofAdd_neg]

theorem Hyp.I₃_le_centralizer_Zp (hd : d.Hyp) : d.I₃ ≤ centralizer (d.Zp : Set G) :=
  Subgroup.le_centralizer_iff.2 ((d.sec2_1_two hd.two_le).1.le.trans inf_le_right)

theorem Hyp.I_le_H (hd : d.Hyp) :
    d.I ≤ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G) := fun _ hi =>
  ⟨d.normalizer_tP_le_normalizer_ZtP (hd.I_le hi).2, (hd.I_le hi).1⟩

theorem Hyp.I_le_normalizer_B₄ (hd : d.Hyp) : d.I ≤ normalizer (d.B₄ : Set G) := fun _ hi =>
  d.le_normalizer_B₄ (hd.I_le_H hi).1

theorem Hyp.exists_I_scalar_ne_one (hd : d.Hyp) :
    ∃ i ∈ d.I, ∃ l : h.fixedField, l ≠ 1 ∧ ∀ x : h.fixedField,
      i * (d.ιZp (Multiplicative.ofAdd x) : G) * i⁻¹ = d.ιZp (Multiplicative.ofAdd (l * x)) := by
  have := finite_fixedField h
  have := charP_fixedField h
  have hK2 : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have := hd.four_le
    omega
  obtain ⟨b, hb0, hb1⟩ := exists_ne_zero_ne_one hK2
  have hb0' : (b : K) ≠ 0 := fun e0 => hb0 (Subtype.ext e0)
  obtain ⟨j, hj, h1, -, -, h4, -⟩ := exists_jSU h hb0' (h.mem_fixedField.1 b.2)
  refine ⟨d.η j, ⟨j, hj, rfl⟩, b * b, fun e => hb1 ?_, d.conj_ιZp_torus hj h1 h4⟩
  have e2 : (b - 1) * (b - 1) = 0 := by
    linear_combination e + (1 - b) * (CharTwo.two_eq_zero : (2 : h.fixedField) = 0)
  exact sub_eq_zero.1 (mul_self_eq_zero.1 e2)

theorem Hyp.cr_mem (hd : d.Hyp) {x : G} (hx : x ∈ d.B₄) : x⁻¹ * d.t * x * d.t ∈ d.Zp :=
  hd.cosetData.crossed_mem x (d.B₄_le hx)

theorem Hyp.cr_mul (hd : d.Hyp) {x y : G} (hx : x ∈ d.B₄) (hy : y ∈ d.B₄) :
    (x * y)⁻¹ * d.t * (x * y) * d.t = (x⁻¹ * d.t * x * d.t) * (y⁻¹ * d.t * y * d.t) :=
  hd.cosetData.crossed_mul_of_mem ⟨d.B₄_le hx, hd.two_core_B₄.1 hx⟩
    ⟨d.B₄_le hy, hd.two_core_B₄.1 hy⟩

theorem Hyp.cr_inv (hd : d.Hyp) {x : G} (hx : x ∈ d.B₄) :
    x⁻¹⁻¹ * d.t * x⁻¹ * d.t = (x⁻¹ * d.t * x * d.t)⁻¹ :=
  hd.cosetData.crossed_inv_of_mem ⟨d.B₄_le hx, hd.two_core_B₄.1 hx⟩

theorem Hyp.cr_eq_one_iff (hd : d.Hyp) {x : G} (hx : x ∈ d.B₄) :
    x⁻¹ * d.t * x * d.t = 1 ↔ x ∈ d.B₂ := by
  rw [crossed_eq_one_iff hd.t_mul_t, ← hd.two_core_B₄.2.2.1, mem_inf,
    mem_centralizer_singleton_iff]
  exact ⟨fun e => ⟨hx, e⟩, fun e => e.2⟩

@[expose] def CB₄I₃ (d : Data G h) : Subgroup G := d.B₄ ⊓ centralizer (d.I₃ : Set G)

omit [Finite G] in
theorem CB₄I₃_le (d : Data G h) : d.CB₄I₃ ≤ d.B₄ := inf_le_left

theorem Hyp.I_le_normalizer_CB₄I₃ (hd : d.Hyp) : d.I ≤ normalizer (d.CB₄I₃ : Set G) := by
  intro i hi
  refine mem_normalizer_of_conj_le fun x hx => ⟨(mem_normalizer_iff.1
    (hd.I_le_normalizer_B₄ hi) x).1 hx.1, mem_centralizer_iff.2 fun s hs => ?_⟩
  have hsi : s * i = i * s := d.I_comm (d.I₃_le_I hs) hi
  have hsx : s * x = x * s := mem_centralizer_iff.1 hx.2 s hs
  have hsi' : s * i⁻¹ = i⁻¹ * s := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hsi, inv_mul_cancel_left]
  calc s * (i * x * i⁻¹) = i * (s * x) * i⁻¹ := by rw [← mul_assoc, ← mul_assoc, hsi]; group
    _ = i * x * (s * i⁻¹) := by rw [hsx]; group
    _ = i * x * i⁻¹ * s := by rw [hsi']; group

theorem Hyp.t_mem_CB₄I₃ (hd : d.Hyp) : d.t ∈ d.CB₄I₃ := by
  obtain ⟨-, -, hB₂, -, -⟩ := hd.two_core_B₄
  refine ⟨(hB₂.symm ▸ inf_le_left : d.B₂ ≤ d.B₄) (mem_sup_left (mem_zpowers _)),
    mem_centralizer_iff.2 fun s hs => ?_⟩
  exact (hd.comm_t (d.pull_le_L _ hs))

theorem Hyp.Zp_le_CB₄I₃ (hd : d.Hyp) : d.Zp ≤ d.CB₄I₃ := fun z hz =>
  ⟨(hd.centerIn_B₄ ▸ hz : z ∈ CFSG.centerIn d.B₄).1,
    mem_centralizer_iff.2 fun _ hs =>
      (mem_centralizer_iff.1 (hd.I₃_le_centralizer_Zp hs) z hz).symm⟩

theorem Hyp.exists_mem_CB₄I₃_mul (hd : d.Hyp) {m : G} (hm : m ∈ d.B₄) :
    ∃ c ∈ d.CB₄I₃, ∃ n ∈ d.B₂, m = c * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hB₂, -, -⟩ := hd.two_core_B₄
  have hB₄2 : IsPGroup 2 d.B₄ := by
    rw [B₄_eq_oTwo]
    exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _
  have hsolv : Group.IsSolvable d.B₄ := by
    have := hB₄2.isNilpotent
    infer_instance
  have hI₃H : ∀ s ∈ d.I₃, s ∈ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun s hs => hd.I_le_H (d.I₃_le_I hs)
  exact exists_mem_inf_centralizer_mul_of_coprime (hB₂.symm ▸ inf_le_left)
    (fun x hx => hd.normalizer_ZtP_le_normalizer_B₂ (d.B₄_le hx))
    (fun s hs => d.le_normalizer_B₄ (hI₃H s hs).1)
    (fun s hs => hd.normalizer_ZtP_le_normalizer_B₂ (hI₃H s hs).1) hsolv
    (coprime_card_of_odd (Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₃_le_I))
      hB₄2) hm fun s hs => by
      have hsm : s * m * s⁻¹ ∈ d.B₄ := (mem_normalizer_iff.1 (d.le_normalizer_B₄ (hI₃H s hs).1)
        m).1 hm
      refine (hd.cr_eq_one_iff (mul_mem (inv_mem hm) hsm)).1 ?_
      rw [hd.cr_mul (inv_mem hm) hsm, hd.cr_inv hm,
        crossed_conj (mem_centralizer_singleton_iff.1 (hI₃H s hs).2),
        ← mem_centralizer_iff.1 (hd.I₃_le_centralizer_Zp hs) _ (hd.cr_mem hm),
        mul_inv_cancel_right, inv_mul_cancel]

theorem Hyp.CB₄I₃_inf_B₂ (hd : d.Hyp) : d.CB₄I₃ ⊓ d.B₂ = d.ZtP := by
  obtain ⟨-, -, hB₂, -, -⟩ := hd.two_core_B₄
  have hZ := (d.sec2_1_two hd.two_le).1
  apply le_antisymm
  · rintro x ⟨⟨-, hxc⟩, hxB⟩
    rw [hd.ZtP_eq]
    obtain ⟨a, ha, hxa | hxa⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hxB
    · rw [hxa] at hxc ⊢
      exact mem_sup_right (hZ ▸ ⟨d.A₂_le_P ha, hxc⟩ : a ∈ d.Zp)
    · rw [hxa] at hxc ⊢
      refine mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (hZ ▸ ⟨d.A₂_le_P ha, ?_⟩))
      refine mem_centralizer_iff.2 fun s hs => ?_
      have h1 := mem_centralizer_iff.1 hxc s hs
      have h2 : s * d.t = d.t * s := hd.comm_t (d.pull_le_L _ hs)
      have : d.t * (s * a) = d.t * (a * s) := by
        calc d.t * (s * a) = (d.t * s) * a := by group
          _ = (s * d.t) * a := by rw [h2]
          _ = s * (d.t * a) := by group
          _ = d.t * a * s := h1
          _ = d.t * (a * s) := by group
      exact mul_left_cancel this
  · have hZtP : d.ZtP ≤ d.B₂ := hd.B₂_spec.1
    refine le_inf (le_inf ((hZtP.trans (hB₂.symm ▸ inf_le_left : d.B₂ ≤ d.B₄))) ?_) hZtP
    rw [hd.ZtP_eq]
    exact sup_le (zpowers_le.2 (hd.t_mem_CB₄I₃.2)) fun z hz => (hd.Zp_le_CB₄I₃ hz).2

theorem Hyp.exists_CB₄I₃_cr_eq (hd : d.Hyp) {y : G} (hy : y ∈ d.Zp) :
    ∃ x ∈ d.CB₄I₃, x⁻¹ * d.t * x * d.t = y := by
  obtain ⟨-, -, -, htr, -⟩ := hd.two_core_B₄
  obtain ⟨m, hm, hmt⟩ := htr y hy
  obtain ⟨c, hc, n, hn, rfl⟩ := hd.exists_mem_CB₄I₃_mul hm
  have hnB : n ∈ d.B₄ := (hd.two_core_B₄.2.2.1.symm ▸ inf_le_left : d.B₂ ≤ d.B₄) hn
  refine ⟨c, hc, ?_⟩
  have e1 := (hd.cosetData.crossed_eq_iff hy).2 hmt
  rw [hd.cr_mul hc.1 hnB, (hd.cr_eq_one_iff hnB).2 hn, mul_one] at e1
  exact e1

theorem Hyp.card_ZtP (hd : d.Hyp) : Nat.card d.ZtP = 2 * 2 ^ f := by
  rw [hd.ZtP_eq, hd.card_zpowers_sup d.Zp_le_L, d.card_Zp]

theorem Hyp.card_CB₄I₃ (hd : d.Hyp) : Nat.card d.CB₄I₃ = 2 * (2 ^ f) ^ 2 := by
  obtain ⟨hZ, -, hB₂, -, -⟩ := hd.two_core_B₄
  have hYZ : d.CB₄I₃ ≤ centralizer (d.Zp : Set G) := (d.CB₄I₃_le).trans hZ
  have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaD.card_eq_of_crossed hd.t_mul_t hYZ
    fun x hx => hd.cr_mem hx.1
  have hker : d.CB₄I₃ ⊓ centralizer ({d.t} : Set G) = d.ZtP := by
    rw [← hd.CB₄I₃_inf_B₂, ← hB₂]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.1.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
  have hrange : (crossedHom hd.t_mul_t d.Zp d.CB₄I₃ hYZ fun x hx => hd.cr_mem hx.1).range = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, hx, hxt⟩ := hd.exists_CB₄I₃_cr_eq y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxt⟩
  rw [hker, hrange, Subgroup.card_top, d.card_Zp, hd.card_ZtP] at h1
  rw [h1]
  ring

theorem Hyp.t_ne_sq (hd : d.Hyp) {w : G} (hw : w ∈ d.B₄) : w * w ≠ d.t := by
  intro hwt
  have hwC : w ∈ d.B₂ := by
    rw [← hd.two_core_B₄.2.2.1]
    refine ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hwt, mul_assoc]
  obtain ⟨a, ha, rfl | rfl⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hwC
  · exact hd.t_not_mem_L (hwt ▸ mul_mem (d.A₂_le_L ha) (d.A₂_le_L ha))
  · refine hd.t_not_mem_L ?_
    rw [← hwt, mul_self_t_mul hd.t_mul_t (hd.comm_t (d.A₂_le_L ha))]
    exact mul_mem (d.A₂_le_L ha) (d.A₂_le_L ha)

theorem Hyp.mul_self_mem_Zp (hd : d.Hyp) {x : G} (hx : x ∈ d.CB₄I₃) : x * x ∈ d.Zp := by
  have hxx : x * x ∈ d.CB₄I₃ ⊓ d.B₂ := by
    refine ⟨mul_mem hx hx, (hd.cr_eq_one_iff (mul_mem hx.1 hx.1)).1 ?_⟩
    rw [hd.cr_mul hx.1 hx.1]
    have := (d.isElementaryAbelian_Zp)
    have hc := hd.cr_mem hx.1
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hc
  rw [hd.CB₄I₃_inf_B₂, hd.ZtP_eq] at hxx
  obtain ⟨z, hz, hzx | hzx⟩ := hd.exists_of_mem_zpowers_sup d.Zp_le_L hxx
  · exact hzx ▸ hz
  · exfalso
    obtain ⟨g, hg, hgt⟩ := hd.transitive_tP z hz
    have hgB : g ∈ normalizer (d.B₄ : Set G) :=
      d.le_normalizer_B₄ (d.normalizer_tP_le_normalizer_ZtP hg)
    have hw : g * x * g⁻¹ ∈ d.B₄ := (mem_normalizer_iff.1 hgB x).1 hx.1
    refine hd.t_ne_sq hw ?_
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = g * (g⁻¹ * d.t * g) * g⁻¹ := by rw [hzx, hgt]
      _ = d.t := by group

theorem Hyp.comm_mem_Zp (hd : d.Hyp) {x y : G} (hx : x ∈ d.CB₄I₃) (hy : y ∈ d.CB₄I₃) :
    x * y * x⁻¹ * y⁻¹ ∈ d.Zp := by
  have hZc : ∀ z ∈ d.Zp, ∀ w ∈ d.CB₄I₃, z * w = w * z := fun z hz w hw =>
    mem_centralizer_iff.1 (hd.two_core_B₄.1 hw.1) z hz
  have hx2 := hd.mul_self_mem_Zp hx
  have hy2 := hd.mul_self_mem_Zp hy
  have hxy2 := hd.mul_self_mem_Zp (mul_mem hx hy)
  have hc : (x * x)⁻¹ * y = y * (x * x)⁻¹ := hZc _ (inv_mem hx2) y hy
  have e : x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (x * x)⁻¹ * (y * y)⁻¹ := by
    calc x * y * x⁻¹ * y⁻¹ = x * y * x * ((x * x)⁻¹ * y) * (y * y)⁻¹ := by group
      _ = x * y * x * (y * (x * x)⁻¹) * (y * y)⁻¹ := by rw [hc]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem hxy2 (inv_mem hx2)) (inv_mem hy2)

@[expose] def V (d : Data G h) : Subgroup G := ⁅d.CB₄I₃ ⊔ d.I, d.CB₄I₃ ⊔ d.I⁆ ⊓ d.B₄

theorem Hyp.commutator_mem_CB₄I₃ (hd : d.Hyp) {i x : G} (hi : i ∈ d.I) (hx : x ∈ d.CB₄I₃) :
    i * x * i⁻¹ * x⁻¹ ∈ d.CB₄I₃ :=
  mul_mem ((mem_normalizer_iff.1 (hd.I_le_normalizer_CB₄I₃ hi) x).1 hx) (inv_mem hx)

theorem Hyp.commutator_le_CB₄I₃ (hd : d.Hyp) : ⁅d.I, d.CB₄I₃⁆ ≤ d.CB₄I₃ :=
  commutator_le.2 fun _ hi _ hx => hd.commutator_mem_CB₄I₃ hi hx

theorem Hyp.Zp_le_commutator (hd : d.Hyp) : d.Zp ≤ ⁅d.I, d.CB₄I₃⁆ := by
  obtain ⟨i, hi, l, hl1, hl⟩ := hd.exists_I_scalar_ne_one
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.2 hl1
  intro z hz
  obtain ⟨m, hm⟩ := d.ιZp.surjective ⟨z, hz⟩
  set c := Multiplicative.toAdd m with hc
  have hz' : z = d.ιZp (Multiplicative.ofAdd c) := by rw [hc, ofAdd_toAdd, hm]
  set c' := c / (l - 1) with hc'
  have hmem : (d.ιZp (Multiplicative.ofAdd c') : G) ∈ d.CB₄I₃ := hd.Zp_le_CB₄I₃ (Subtype.prop _)
  have e : ⁅i, (d.ιZp (Multiplicative.ofAdd c') : G)⁆ = z := by
    rw [commutatorElement_def, hl, d.coe_ιZp_mul_inv, hz']
    congr 3
    rw [hc']
    field_simp
  rw [← e]
  exact commutator_mem_commutator hi hmem

theorem Hyp.conj_mem_commutator (hd : d.Hyp) {x v : G} (hx : x ∈ d.CB₄I₃)
    (hv : v ∈ ⁅d.I, d.CB₄I₃⁆) : x * v * x⁻¹ ∈ ⁅d.I, d.CB₄I₃⁆ := by
  have e : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
  rw [e]
  exact mul_mem (hd.Zp_le_commutator (hd.comm_mem_Zp hx (hd.commutator_le_CB₄I₃ hv))) hv

theorem Hyp.V_eq (hd : d.Hyp) : d.V = ⁅d.I, d.CB₄I₃⁆ := by
  apply le_antisymm
  · refine inf_le_left.trans (commutator_sup_le (hd.I_le_normalizer_CB₄I₃)
      (fun i hi j hj => d.I_comm hi hj) (fun x hx v hv => hd.conj_mem_commutator hx hv)
      (fun x hx x' hx' => hd.Zp_le_commutator (hd.comm_mem_Zp hx hx'))
      fun i hi x hx => commutator_mem_commutator hi hx)
  · exact le_inf (commutator_mono le_sup_right le_sup_left)
      (hd.commutator_le_CB₄I₃.trans d.CB₄I₃_le)

theorem Hyp.V_le_CB₄I₃ (hd : d.Hyp) : d.V ≤ d.CB₄I₃ := hd.V_eq ▸ hd.commutator_le_CB₄I₃

theorem Hyp.Zp_le_V (hd : d.Hyp) : d.Zp ≤ d.V := hd.V_eq ▸ hd.Zp_le_commutator

theorem Hyp.t_not_mem_V (hd : d.Hyp) : d.t ∉ d.V := by
  intro htV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : IsPGroup 2 d.CB₄I₃ := by
    have : IsPGroup 2 d.B₄ := by
      rw [B₄_eq_oTwo]
      exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _
    exact this.to_le d.CB₄I₃_le
  have htZ := mem_of_mem_commutator_sup_of_fixed hd.Zp_le_CB₄I₃
    (fun y hy y' hy' => hd.comm_mem_Zp hy hy') hd.I_le_normalizer_CB₄I₃ d.I_le_normalizer_Zp
    (coprime_card_of_odd d.odd_card_I hX2) (mem_sup_left (hd.V_eq ▸ htV)) fun a ha => by
      rw [hd.comm_t (d.pull_le_L _ ha), mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  exact hd.t_not_mem_L (d.Zp_le_L htZ)

theorem Hyp.V_inf_centralizer_t (hd : d.Hyp) : d.V ⊓ centralizer ({d.t} : Set G) = d.Zp := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxt⟩ := Subgroup.mem_inf.1 hx
    have hxB : x ∈ d.CB₄I₃ ⊓ d.B₂ := ⟨hd.V_le_CB₄I₃ hxV, by
      rw [← hd.two_core_B₄.2.2.1]
      exact ⟨(hd.V_le_CB₄I₃ hxV).1, hxt⟩⟩
    rw [hd.CB₄I₃_inf_B₂, hd.ZtP_eq] at hxB
    obtain ⟨z, hz, rfl | rfl⟩ := hd.exists_of_mem_zpowers_sup d.Zp_le_L hxB
    · exact hz
    · exfalso
      refine hd.t_not_mem_V ?_
      have := mul_mem hxV (inv_mem (hd.Zp_le_V hz))
      rwa [mul_inv_cancel_right] at this
  · exact le_inf hd.Zp_le_V fun z hz => mem_centralizer_singleton_iff.2 (hd.comm_t (d.Zp_le_L hz))

theorem Hyp.V_inf_B₂ (hd : d.Hyp) : d.V ⊓ d.B₂ = d.Zp := by
  refine le_antisymm ?_ (le_inf hd.Zp_le_V (fun z hz => ?_))
  · rw [← hd.V_inf_centralizer_t]
    exact inf_le_inf_left _ (hd.B₂_spec.2.1.trans hd.tP_le_centralizer)
  · exact hd.B₂_spec.1 (hd.ZtP_eq ▸ mem_sup_right hz)

theorem Hyp.exists_V_cr_eq (hd : d.Hyp) {y : G} (hy : y ∈ d.Zp) :
    ∃ v ∈ d.V, v⁻¹ * d.t * v * d.t = y := by
  obtain ⟨i, hi, l, hl1, hl⟩ := hd.exists_I_scalar_ne_one
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.2 hl1
  obtain ⟨m, hm⟩ := d.ιZp.surjective ⟨y, hy⟩
  set c := Multiplicative.toAdd m with hc
  have hy' : y = d.ιZp (Multiplicative.ofAdd c) := by rw [hc, ofAdd_toAdd, hm]
  obtain ⟨x, hx, hxt⟩ := hd.exists_CB₄I₃_cr_eq
    (d.ιZp (Multiplicative.ofAdd (c / (l - 1)))).2
  have hix : i * x * i⁻¹ ∈ d.B₄ :=
    (mem_normalizer_iff.1 (hd.I_le_normalizer_B₄ hi) x).1 hx.1
  refine ⟨i * x * i⁻¹ * x⁻¹, hd.V_eq ▸ commutator_mem_commutator hi hx, ?_⟩
  rw [hd.cr_mul hix (inv_mem hx.1), hd.cr_inv hx.1,
    crossed_conj (mem_centralizer_singleton_iff.1 (hd.I_le_H hi).2), hxt, hl, d.coe_ιZp_mul_inv,
    hy']
  congr 3
  field_simp

theorem Hyp.card_V (hd : d.Hyp) : Nat.card d.V = (2 ^ f) ^ 2 := by
  have hYZ : d.V ≤ centralizer (d.Zp : Set G) :=
    (hd.V_le_CB₄I₃.trans d.CB₄I₃_le).trans hd.two_core_B₄.1
  have h1 := CFSG.EvenSmallLie.UnitarySix.YamadaD.card_eq_of_crossed hd.t_mul_t hYZ
    fun x hx => hd.cr_mem ((hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hx)
  have hrange : (crossedHom hd.t_mul_t d.Zp d.V hYZ fun x hx =>
      hd.cr_mem ((hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hx)).range = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq y.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvt⟩
  rw [hd.V_inf_centralizer_t, hrange, Subgroup.card_top, d.card_Zp] at h1
  rw [h1, sq]

theorem Hyp.CB₄I₃_eq (hd : d.Hyp) : d.CB₄I₃ = d.V ⊔ zpowers d.t := by
  refine le_antisymm (fun x hx => ?_) (sup_le hd.V_le_CB₄I₃ (zpowers_le.2 hd.t_mem_CB₄I₃))
  obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq (hd.cr_mem hx.1)
  have hvX := hd.V_le_CB₄I₃ hv
  have hw : v⁻¹ * x ∈ d.CB₄I₃ ⊓ d.B₂ := by
    have hvB := d.CB₄I₃_le hvX
    have hxB := d.CB₄I₃_le hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hvX) hx,
      (hd.cr_eq_one_iff (mul_mem (inv_mem hvB) hxB)).1 ?_⟩
    rw [hd.cr_mul (inv_mem hvB) hxB, hd.cr_inv hvB, hvt, inv_mul_cancel]
  rw [hd.CB₄I₃_inf_B₂, hd.ZtP_eq] at hw
  obtain ⟨z, hz, hwz | hwz⟩ := hd.exists_of_mem_zpowers_sup d.Zp_le_L hw
  · have : x = v * z := by rw [← hwz, mul_inv_cancel_left]
    rw [this]
    exact mul_mem (mem_sup_left hv) (mem_sup_left (hd.Zp_le_V hz))
  · have : x = v * z * d.t := by
      rw [mul_assoc, hd.comm_t (d.Zp_le_L hz), ← hwz, mul_inv_cancel_left]
    rw [this]
    exact mul_mem (mul_mem (mem_sup_left hv) (mem_sup_left (hd.Zp_le_V hz)))
      (mem_sup_right (mem_zpowers _))

theorem Hyp.B₄_eq_V_sup_B₂ (hd : d.Hyp) : d.B₄ = d.V ⊔ d.B₂ := by
  have hB₂B₄ : d.B₂ ≤ d.B₄ := hd.two_core_B₄.2.2.1.symm ▸ inf_le_left
  refine le_antisymm (fun m hm => ?_) (sup_le (hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hB₂B₄)
  obtain ⟨c, hc, n, hn, rfl⟩ := hd.exists_mem_CB₄I₃_mul hm
  rw [hd.CB₄I₃_eq] at hc
  refine mul_mem ((sup_le_sup_left (zpowers_le.2 ?_) _) hc) (mem_sup_right hn)
  exact hd.B₂_spec.1 (hd.ZtP_eq ▸ mem_sup_left (mem_zpowers _))

theorem Hyp.I_le_normalizer_V (hd : d.Hyp) : d.I ≤ normalizer (d.V : Set G) := by
  intro i hi
  refine mem_normalizer_of_map_conj_eq ?_
  rw [hd.V_eq, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer
    (hd.I_le_normalizer_CB₄I₃ hi)]
  congr 1
  refine le_antisymm (fun x hx => ?_) fun x hx => ⟨x, hx, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := hx
    change i * j * i⁻¹ ∈ d.I
    rw [d.I_comm hi hj, mul_inv_cancel_right]
    exact hj
  · change i * x * i⁻¹ = x
    rw [d.I_comm hi hx, mul_inv_cancel_right]

theorem Hyp.s_mem_normalizer_V (hd : d.Hyp) : d.s ∈ normalizer (d.V : Set G) := by
  obtain ⟨hsI, hsI₃⟩ := And.intro (d.sec2_1_five.2.1) (d.sec2_1_five.2.2.1)
  have hsB₄ : d.s ∈ normalizer (d.B₄ : Set G) := d.le_normalizer_B₄ hd.s_mem_K₀.1.1
  have hsX : d.s ∈ normalizer (d.CB₄I₃ : Set G) := mem_normalizer_inf hsB₄
    (Prelim.normalizer_le_normalizer_centralizer d.I₃ (mem_normalizer_of_map_conj_eq hsI₃))
  refine mem_normalizer_of_map_conj_eq ?_
  rw [hd.V_eq, Subgroup.map_commutator, hsI, map_conj_eq_of_mem_normalizer hsX]

theorem Hyp.exists_crossedHom_V (hd : d.Hyp) :
    ∃ ψ : d.V →* d.Zp, Function.Surjective ψ ∧ ψ.ker = d.Zp.subgroupOf d.V ∧
      (∀ v : d.V, (ψ v : G) = (v : G)⁻¹ * d.t * v * d.t) ∧
      ∀ c ∈ d.I, ∀ v : d.V,
        ∃ hv : c * v * c⁻¹ ∈ d.V, (ψ ⟨c * v * c⁻¹, hv⟩ : G) = c * ψ v * c⁻¹ := by
  have hVB : d.V ≤ d.B₄ := hd.V_le_CB₄I₃.trans d.CB₄I₃_le
  have hYZ : d.V ≤ centralizer (d.Zp : Set G) := hVB.trans hd.two_core_B₄.1
  refine ⟨crossedHom hd.t_mul_t d.Zp d.V hYZ fun x hx => hd.cr_mem (hVB hx), ?_, ?_,
    fun v => rfl, fun c hc v => ⟨(mem_normalizer_iff.1 (hd.I_le_normalizer_V hc) v).1 v.2, ?_⟩⟩
  · rintro ⟨y, hy⟩
    obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq hy
    exact ⟨⟨v, hv⟩, Subtype.ext hvt⟩
  · ext v
    rw [mem_ker_crossedHom, mem_subgroupOf, ← hd.V_inf_centralizer_t, mem_inf,
      mem_centralizer_singleton_iff]
    exact ⟨fun e => ⟨v.2, e⟩, fun e => e.2⟩
  · exact crossed_conj (mem_centralizer_singleton_iff.1 (hd.I_le_H hc).2)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
