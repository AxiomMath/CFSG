module

public import CFSG.GH74.Uniqueness.Section165
public import CFSG.GH74.Uniqueness.Section165GapOdd
public import CFSG.GH74.Uniqueness.Section165GapConj
public import CFSG.GH74.Uniqueness.Section165GapOrder
public import CFSG.GH74.Uniqueness.Section17Lemma311

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace SecGap

omit [Finite X] in
theorem cenHull_map_conj (hZ : IsInvariantInvolutionSet Z) (g a : X) :
    (cenHull Z a).map (MulAut.conj g).toMonoidHom = cenHull Z (g * a * g⁻¹) := by
  unfold cenHull zHull
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_inter_iff, SetLike.mem_coe, mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hxZ, hxa⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have := hZ.2 x hxZ g⁻¹
      simpa using this
    · calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
        _ = g * (a * x) * g⁻¹ := by rw [hxa]
        _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  · rintro ⟨hyZ, hya⟩
    refine ⟨g⁻¹ * y * g, ⟨hZ.2 y hyZ g, ?_⟩, by group⟩
    have h1 : y * (g * a * g⁻¹) = g * a * g⁻¹ * y := hya
    calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * y) * g := by rw [h1]
      _ = a * (g⁻¹ * y * g) := by group

theorem exists_conj_tw {B : Subgroup X} {n : ℕ} (hB : Bender.BenderType ↥B n 1 1) {t w : X}
    (htB : t ∈ B) (hwN : w ∈ normalizer (B : Set X)) (ht2 : t * t = 1) (hw2 : w * w = 1)
    (htw : t * w = w * t)
    (hniw : ¬ ∃ g : ↥B, ∀ x : ↥B, Sec165.conjAut hwN x = g * x * g⁻¹) :
    ∃ g ∈ B, g * w * g⁻¹ = t * w := by
  have htwN : t * w ∈ normalizer (B : Set X) := mul_mem (le_normalizer htB) hwN
  have htw2 : (t * w) * (t * w) = 1 := by
    calc (t * w) * (t * w) = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [htw]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [ht2, hw2, one_mul]
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hnitw : ¬ ∃ g : ↥B, ∀ x : ↥B, Sec165.conjAut htwN x = g * x * g⁻¹ := by
    rintro ⟨g₁, hg₁⟩
    apply hniw
    refine ⟨(⟨t, htB⟩ : ↥B)⁻¹ * g₁, fun x => ?_⟩
    apply Subtype.ext
    have h1 := congrArg Subtype.val (hg₁ x)
    rw [Sec165.conjAut_apply] at h1
    rw [Sec165.conjAut_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    calc w * (x : X) * w⁻¹ = t⁻¹ * ((t * w) * x * (t * w)⁻¹) * t := by group
      _ = t⁻¹ * ((g₁ : X) * x * (g₁ : X)⁻¹) * t := by rw [h1]
      _ = _ := by group
  obtain ⟨g, hg⟩ := Bender.BenderType.exists_conj_outer_involution hB (Sec165.conjAut hwN)
    (Sec165.conjAut htwN) (Sec165.conjAut_mul_self hwN hw2) (Sec165.conjAut_mul_self htwN htw2)
    hniw hnitw
  set gX : X := (g : X) with hgX
  have hgB : gX ∈ B := g.2
  set c' : X := (gX * w * gX⁻¹)⁻¹ * (t * w) with hc'
  have hc'comm : ∀ x ∈ B, c' * x = x * c' := by
    intro x hx
    have h1 := congrArg Subtype.val (hg ⟨x, hx⟩)
    rw [Sec165.conjAut_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Sec165.conjAut_apply] at h1
    have hxc : c' * x * c'⁻¹ = x := by
      rw [hc']
      calc (gX * w * gX⁻¹)⁻¹ * (t * w) * x * ((gX * w * gX⁻¹)⁻¹ * (t * w))⁻¹
          = (gX * w * gX⁻¹)⁻¹ * ((t * w) * x * (t * w)⁻¹) * (gX * w * gX⁻¹) := by group
        _ = (gX * w * gX⁻¹)⁻¹ * (gX * (w * (gX⁻¹ * x * gX) * w⁻¹) * gX⁻¹) *
              (gX * w * gX⁻¹) := by rw [h1]
        _ = x := by group
    calc c' * x = (c' * x * c'⁻¹) * c' := by group
      _ = x * c' := by rw [hxc]
  have hc'B : c' ∈ B := by
    have e : c' = gX * (w * (gX⁻¹ * t) * w⁻¹) := by
      rw [hc']
      calc (gX * w * gX⁻¹)⁻¹ * (t * w) = gX * w⁻¹ * gX⁻¹ * (t * w) := by group
        _ = gX * (w * (gX⁻¹ * t) * w⁻¹) := by rw [hwi]; group
    rw [e]
    have : w * (gX⁻¹ * t) * w⁻¹ ∈ B :=
      (mem_normalizer_iff.mp hwN _).mp (mul_mem (inv_mem hgB) htB)
    exact mul_mem hgB this
  have hc'center : (⟨c', hc'B⟩ : ↥B) ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc'comm y y.2).symm
  rw [hB.center_eq_bot, Subgroup.mem_bot] at hc'center
  have hc'1 : c' = 1 := congrArg Subtype.val hc'center
  exact ⟨gX, hgB, inv_mul_eq_one.mp hc'1⟩

omit [Finite X] in
theorem mem_cenHull_of_inverted (hZ : IsInvariantInvolutionSet Z) {t y x : X} (ht : t ∈ Z)
    (hty : t * y = y * t) (hxy : x * y = y * x) (hxt : t * x * t⁻¹ = x⁻¹)
    (hodd : Odd (orderOf x)) : x ∈ cenHull Z y := by
  have htC : t ∈ cenHull Z y := subset_closure ⟨ht, mem_centralizer_singleton_iff.mpr hty⟩
  have hxN : x ∈ normalizer (cenHull Z y : Set X) :=
    le_normalizer_zHull hZ _ (mem_centralizer_singleton_iff.mpr hxy)
  have hcomm : ⁅t, x⁆ = x⁻¹ * x⁻¹ := by
    rw [commutatorElement_def, hxt]
  have hcC : ⁅t, x⁆ ∈ cenHull Z y := by
    rw [commutatorElement_def]
    have h1 : x * t⁻¹ * x⁻¹ ∈ cenHull Z y := (mem_normalizer_iff.mp hxN t⁻¹).mp (inv_mem htC)
    have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem htC h1
  refine Sec165.mem_of_mul_self_mem hodd ?_
  have : (x⁻¹ * x⁻¹)⁻¹ ∈ cenHull Z y := inv_mem (hcomm ▸ hcC)
  simpa [mul_inv_rev] using this

theorem odd_card_of_forall_orderOf_ne_two {A : Subgroup X}
    (h : ∀ e ∈ A, orderOf e ≠ 2) : Odd (Nat.card A) := by
  by_contra hne
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hne
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 2 hne
  exact h e e.2 (by rw [Subgroup.orderOf_coe]; exact he)

omit [Finite X] in
theorem false_of_zpow {u x x' : X} {m : ℕ} (hm : 3 ≤ m) (hx'o : orderOf x' = m)
    (hxu : u * x * u⁻¹ = x) (hx'u : u * x' * u⁻¹ = x'⁻¹) (h : ∃ j : ℤ, x' = x ^ j) : False := by
  obtain ⟨j, hj⟩ := h
  have h1 : u * x' * u⁻¹ = x' := by
    rw [hj]
    have := map_zpow (MulAut.conj u) x j
    simp only [MulAut.conj_apply] at this
    rw [this, hxu]
  have h2 : x' * x' = 1 := by
    have : x' = x'⁻¹ := h1.symm.trans hx'u
    calc x' * x' = x' * x'⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel x'
  have h3 : orderOf x' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  rw [hx'o] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

omit [Finite X] in
theorem false_of_cube {u x x' : X} {m : ℕ} (hm : 5 ≤ m) (hmo : Odd m) (hx'o : orderOf x' = m)
    (hxu : u * x * u⁻¹ = x) (hx'u : u * x' * u⁻¹ = x'⁻¹)
    (h : ∃ j : ℤ, x' ^ 3 = x ^ (3 * j)) : False := by
  obtain ⟨j, hj⟩ := h
  have h1 : u * x' ^ 3 * u⁻¹ = x' ^ 3 := by
    rw [hj]
    have := map_zpow (MulAut.conj u) x (3 * j)
    simp only [MulAut.conj_apply] at this
    rw [this, hxu]
  have h1' : u * x' ^ 3 * u⁻¹ = (x' ^ 3)⁻¹ := by
    have := map_pow (MulAut.conj u) x' 3
    simp only [MulAut.conj_apply] at this
    rw [this, hx'u, inv_pow]
  have h2 : x' ^ 6 = 1 := by
    have : x' ^ 3 = (x' ^ 3)⁻¹ := h1.symm.trans h1'
    have h3 : x' ^ 3 * x' ^ 3 = 1 := by
      calc x' ^ 3 * x' ^ 3 = x' ^ 3 * (x' ^ 3)⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel _
    rw [← h3, ← pow_add]
  have h3 : m ∣ 6 := by rw [← hx'o]; exact orderOf_dvd_of_pow_eq_one h2
  have h4 : m ∣ 3 := by
    have hcop : Nat.Coprime m 2 := hmo.coprime_two_right
    exact hcop.dvd_of_dvd_mul_right (by rw [show 3 * 2 = 6 by norm_num]; exact h3)
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem endgame
    (S : ZDSetup X Z M) (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M)
    (h311 : Lemma311BenderStmt) (c : Conf16 Z M) {w : X} (hwD : w ∈ c.D) (hw2 : w * w = 1)
    (hwu : w ≠ c.u) (huw : c.u * w = w * c.u) (hwt : w * c.t = c.t * w)
    (hwz : w * c.z = c.z * w) {k : ℕ} (hk : 1 ≤ k) (hwN : w ∈ normalizer (c.B0 : Set X))
    (hB0T : Bender.BenderType ↥c.B0 (2 * k) 1 1)
    (hniw : ¬ ∃ g : ↥c.B0, ∀ x : ↥c.B0, Sec165.conjAut hwN x = g * x * g⁻¹)
    (hisow : Nonempty (Bender.autFixed (Sec165.conjAut hwN) ≃* CFSG.Theory.Comparator.PSL2Model k))
    {x x' : X} (hxD : x ∈ c.D) (hx'D : x' ∈ c.D) (hxo : orderOf x = 2 ^ k + 1)
    (hx'o : orderOf x' = 2 ^ k + 1) (hxu : x * c.u = c.u * x) (hxt : c.t * x * c.t⁻¹ = x⁻¹)
    (hxw : w * x * w⁻¹ = x⁻¹) (hx't : c.t * x' * c.t⁻¹ = x'⁻¹)
    (hx'u : c.u * x' * c.u⁻¹ = x'⁻¹) (hx'w : x' * w = w * x') : False := by
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  have hu2 : c.u * c.u = 1 := c.u_mul_self
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huz : c.u * c.z = c.z * c.u := (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c)).symm
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have hui : c.u⁻¹ = c.u := inv_eq_of_mul_eq_one_right hu2
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hm3 : 3 ≤ 2 ^ k + 1 := by
    have : 2 ≤ 2 ^ k := Nat.le_of_dvd (by positivity) h2k
    omega
  have hmodd : Odd (2 ^ k + 1) := Nat.odd_iff.mpr (by omega)
  have hxodd : Odd (orderOf x) := by rw [hxo]; exact hmodd
  have hx'odd : Odd (orderOf x') := by rw [hx'o]; exact hmodd
  set y := c.t * c.u * w with hy
  have hty : c.t * y = y * c.t := by
    rw [hy]
    calc c.t * (c.t * c.u * w) = c.t * (c.t * c.u) * w := by group
      _ = c.t * (c.u * c.t) * w := by rw [hut]
      _ = c.t * c.u * (c.t * w) := by group
      _ = c.t * c.u * (w * c.t) := by rw [hwt]
      _ = c.t * c.u * w * c.t := by group
  have hxuc : c.u * x * c.u⁻¹ = x := by rw [← hxu]; group
  have hxu1 : c.u * x⁻¹ * c.u⁻¹ = x⁻¹ := by
    calc c.u * x⁻¹ * c.u⁻¹ = (c.u * x * c.u⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [hxuc]
  have hxt1 : c.t * x⁻¹ * c.t⁻¹ = x := by
    calc c.t * x⁻¹ * c.t⁻¹ = (c.t * x * c.t⁻¹)⁻¹ := by group
      _ = x := by rw [hxt, inv_inv]
  have hx'w' : w * x' * w⁻¹ = x' := by
    calc w * x' * w⁻¹ = (x' * w) * w⁻¹ := by rw [hx'w]
      _ = x' := by group
  have hx't1 : c.t * x'⁻¹ * c.t⁻¹ = x' := by
    calc c.t * x'⁻¹ * c.t⁻¹ = (c.t * x' * c.t⁻¹)⁻¹ := by group
      _ = x' := by rw [hx't, inv_inv]
  have hyx : y * x * y⁻¹ = x := by
    calc y * x * y⁻¹ = c.t * (c.u * (w * x * w⁻¹) * c.u⁻¹) * c.t⁻¹ := by rw [hy]; group
      _ = c.t * (c.u * x⁻¹ * c.u⁻¹) * c.t⁻¹ := by rw [hxw]
      _ = c.t * x⁻¹ * c.t⁻¹ := by rw [hxu1]
      _ = x := hxt1
  have hyx' : y * x' * y⁻¹ = x' := by
    calc y * x' * y⁻¹ = c.t * (c.u * (w * x' * w⁻¹) * c.u⁻¹) * c.t⁻¹ := by rw [hy]; group
      _ = c.t * (c.u * x' * c.u⁻¹) * c.t⁻¹ := by rw [hx'w']
      _ = c.t * x'⁻¹ * c.t⁻¹ := by rw [hx'u]
      _ = x' := hx't1
  have hxy : x * y = y * x := by
    calc x * y = (y * x * y⁻¹) * y := by rw [hyx]
      _ = y * x := by group
  have hx'y : x' * y = y * x' := by
    calc x' * y = (y * x' * y⁻¹) * y := by rw [hyx']
      _ = y * x' := by group
  have hxF : x ∈ cenHull Z y := mem_cenHull_of_inverted S.invariant c.ht hty hxy hxt hxodd
  have hx'F : x' ∈ cenHull Z y := mem_cenHull_of_inverted S.invariant c.ht hty hx'y hx't hx'odd
  have htF : c.t ∈ cenHull Z y :=
    subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr hty⟩
  obtain ⟨g, hgB, hgw⟩ := exists_conj_tw hB0T (Sec164.t_mem_B0 c) hwN ht2 hw2 hwt.symm hniw
  have hgu : g * c.u = c.u * g := mem_centralizer_singleton_iff.mp (Sec164.B0_le_B c hgB)
  have hgy : g * (c.u * w) * g⁻¹ = y := by
    have hgu' : g * c.u * g⁻¹ = c.u := by rw [hgu]; group
    calc g * (c.u * w) * g⁻¹ = (g * c.u * g⁻¹) * (g * w * g⁻¹) := by group
      _ = c.u * (c.t * w) := by rw [hgu', hgw]
      _ = (c.u * c.t) * w := by group
      _ = y := by rw [hut]
  set ψ : X →* X := (MulAut.conj g⁻¹).toMonoidHom with hψ
  have hψapp : ∀ a, ψ a = g⁻¹ * a * g := fun a => by simp [hψ]
  have hψinj : Function.Injective ψ := (MulAut.conj g⁻¹).injective
  have hψo : ∀ a, orderOf (ψ a) = orderOf a := fun a => orderOf_injective ψ hψinj a
  have hF' : (cenHull Z y).map ψ = cenHull Z (c.u * w) := by
    rw [hψ, cenHull_map_conj S.invariant]
    congr 1
    calc g⁻¹ * y * g⁻¹⁻¹ = g⁻¹ * (g * (c.u * w) * g⁻¹) * g := by rw [hgy, inv_inv]
      _ = c.u * w := by group
  have huw2 : (c.u * w) * (c.u * w) = 1 := by
    calc (c.u * w) * (c.u * w) = c.u * (w * c.u) * w := by group
      _ = c.u * (c.u * w) * w := by rw [huw]
      _ = (c.u * c.u) * (w * w) := by group
      _ = 1 := by rw [hu2, hw2, one_mul]
  have huw1 : c.u * w ≠ 1 := fun h => hwu (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hui])
  have huwo : orderOf (c.u * w) = 2 := orderOf_eq_prime (by rw [sq]; exact huw2) huw1
  have huwD : c.u * w ∈ c.D := mul_mem c.hu hwD
  have huwM : c.u * w ∈ M := (mem_inf.mp huwD).1
  have huwt : (c.u * w) * c.t = c.t * (c.u * w) := by
    calc (c.u * w) * c.t = c.u * (w * c.t) := by group
      _ = c.u * (c.t * w) := by rw [hwt]
      _ = (c.u * c.t) * w := by group
      _ = (c.t * c.u) * w := by rw [hut]
      _ = c.t * (c.u * w) := by group
  have huwz : (c.u * w) * c.z = c.z * (c.u * w) := by
    calc (c.u * w) * c.z = c.u * (w * c.z) := by group
      _ = c.u * (c.z * w) := by rw [hwz]
      _ = (c.u * c.z) * w := by group
      _ = (c.z * c.u) * w := by rw [huz]
      _ = c.z * (c.u * w) := by group
  have hCM' : ¬ centralizer ({c.u * w} : Set X) ≤ M := fun h =>
    c.htM (h (mem_centralizer_singleton_iff.mpr huwt.symm))
  have hns' := Sec165.not_solvable_of_commute_t h163 c huwM huwo huwt
  have hne' := Sec165.exists_mem_ne_of_not_solvable S c.toCtx16 huwo hCM' huwz.symm hns'
  obtain ⟨n₁, i₁, e₁, hBS⟩ := S.benderSub_exists (S.cor714_centralizer_ne_top huwo) hCM'
    ⟨c.z, c.hz, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr huwz.symm, c.hzM⟩⟩ hns'
  have hzF' : c.z ∈ cenHull Z (c.u * w) :=
    subset_closure ⟨c.hz, mem_centralizer_singleton_iff.mpr huwz.symm⟩
  have htF' : c.t ∈ cenHull Z (c.u * w) :=
    subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr huwt.symm⟩
  set A : Subgroup X := c.D ⊓ cenHull Z y with hA
  have hnoinv : ∀ e ∈ A, orderOf e ≠ 2 := by
    intro e he he2
    obtain ⟨heD, heF⟩ := mem_inf.mp he
    have heF' : ψ e ∈ cenHull Z (c.u * w) := hF' ▸ mem_map_of_mem ψ heF
    have hZe' := hBS.invol _ heF' (by rw [hψo]; exact he2)
    have hZe : e ∈ Z := by
      have := S.invariant.2 _ hZe' g⁻¹
      rw [hψapp] at this
      simpa [mul_assoc] using this
    have heM : e ∈ M := (mem_inf.mp heD).1
    have heMt : c.t⁻¹ * e * c.t ∈ M := by
      have h1 := mem_conjugate_iff.mp (mem_inf.mp heD).2
      rw [hti] at h1 ⊢
      exact h1
    exact c.htM (S.prodDisc.mem_of_conj_mem hZe heM heMt)
  have hAodd : Odd (Nat.card A) := odd_card_of_forall_orderOf_ne_two hnoinv
  have htA : ∀ a ∈ A, c.t * a * c.t⁻¹ ∈ A := by
    intro a ha
    obtain ⟨haD, haF⟩ := mem_inf.mp ha
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have haM : a ∈ M := (mem_inf.mp haD).1
      have haMt : c.t * a * c.t⁻¹ ∈ M := mem_conjugate_iff.mp (mem_inf.mp haD).2
      refine mem_inf.mpr ⟨haMt, ?_⟩
      rw [mem_conjugate_iff]
      have e : c.t * (c.t * a * c.t⁻¹) * c.t⁻¹ = a := by
        calc c.t * (c.t * a * c.t⁻¹) * c.t⁻¹ = (c.t * c.t) * a * (c.t⁻¹ * c.t⁻¹) := by group
          _ = a := by rw [ht2, hti, ht2, one_mul, mul_one]
      rw [e]
      exact haM
    · have htN : c.t ∈ normalizer (cenHull Z y : Set X) :=
        le_normalizer_zHull S.invariant _ (mem_centralizer_singleton_iff.mpr hty)
      exact (mem_normalizer_iff.mp htN a).mp haF
  have hxA : x ∈ A := mem_inf.mpr ⟨hxD, hxF⟩
  have hx'A : x' ∈ A := mem_inf.mpr ⟨hx'D, hx'F⟩
  set A' : Subgroup X := A.map ψ with hA'def
  have hAF' : A' ≤ cenHull Z (c.u * w) := by
    rw [← hF']
    exact Subgroup.map_mono inf_le_right
  have hA' : Odd (Nat.card A') := by
    rw [hA'def, Subgroup.card_map_of_injective hψinj]
    exact hAodd
  have hsF : ψ c.t ∈ cenHull Z (c.u * w) := hF' ▸ mem_map_of_mem ψ htF
  have hs2 : ψ c.t * ψ c.t = 1 := by rw [← map_mul, ht2, map_one]
  have hs1 : ψ c.t ≠ 1 := by
    intro h
    have h1 : c.t = 1 := hψinj (by rw [h, map_one])
    have := S.invariant.1 c.t c.ht
    rw [h1, orderOf_one] at this
    omega
  have hsA' : ∀ a ∈ A', ψ c.t * a * (ψ c.t)⁻¹ ∈ A' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨c.t * a * c.t⁻¹, htA a ha, ?_⟩
    simp [map_mul, map_inv]
  have hx₁A : ψ x ∈ A' := mem_map_of_mem ψ hxA
  have hx₁'A : ψ x' ∈ A' := mem_map_of_mem ψ hx'A
  have hsx₁ : ψ c.t * ψ x * (ψ c.t)⁻¹ = (ψ x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hxt, map_inv]
  have hsx₁' : ψ c.t * ψ x' * (ψ c.t)⁻¹ = (ψ x')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hx't, map_inv]
  have hord₁ : orderOf (ψ x) = orderOf (ψ x') := by rw [hψo, hψo, hxo, hx'o]
  have hx₁1 : ψ x ≠ 1 := by
    intro h
    have : orderOf (ψ x) = 1 := by rw [h, orderOf_one]
    rw [hψo, hxo] at this
    omega
  have hxu' : c.u * x * c.u⁻¹ = x := hxuc
  obtain ⟨m', hm'2, hcase⟩ := h162 c.toCtx16 (cenHull Z (c.u * w))
    (Sec164.cenHull_ne_top S huwo) hzF' htF' hne' (zHull_zHull _)
  rcases hcase with ⟨-, hT⟩ | ⟨hL2, ⟨e₂, hB3⟩, -, hfix⟩
  ·
    have hmain : ∃ j : ℤ, ψ x' = ψ x ^ j := by
      rcases hT with hT | hT
      · exact exists_zpow_of_linear hT hAF' hA' hx₁A hx₁'A hx₁1 hord₁
      · exact exists_zpow_of_suzuki hT hAF' hA' hx₁A hx₁'A hx₁1 hord₁
    obtain ⟨j, hj⟩ := hmain
    refine false_of_zpow hm3 hx'o hxu' hx'u ⟨j, hψinj ?_⟩
    rw [map_zpow]
    exact hj
  ·
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have hk1 : k = 1 := by omega
      have huuw : c.u * (c.u * w) = (c.u * w) * c.u := by
        calc c.u * (c.u * w) = c.u * (w * c.u) := by rw [huw]
          _ = (c.u * w) * c.u := by group
      have huN' : c.u ∈ normalizer (cenHull Z (c.u * w) : Set X) :=
        le_normalizer_zHull S.invariant _ (mem_centralizer_singleton_iff.mpr huuw)
      have hfixzt : ∀ x : ↥(cenHull Z (c.u * w)), (x : X) = c.z ∨ (x : X) = c.t →
          Sec165.conjAut huN' x = x := by
        rintro x (hx | hx)
        · exact Sec165.conjAut_fix huN' (by rw [hx]; exact huz)
        · exact Sec165.conjAut_fix huN' (by rw [hx]; exact hut)
      have hfz := hfix (Sec165.conjAut huN') (Sec165.conjAut_mul_self huN' hu2) hfixzt
      have hfZle : fZero Z M (cenHull Z (c.u * w)) c.t ≤ cenHull Z (c.u * w) := by
        refine (closure_le _).mpr ?_
        rintro y' (hy' | hy')
        · exact (mem_inf.mp (Cor713.zHull_le _ hy')).2
        · rw [Set.mem_singleton_iff] at hy'
          rw [hy']
          exact htF'
      have hcommu : ∀ f ∈ fZero Z M (cenHull Z (c.u * w)) c.t, f * c.u = c.u * f := by
        intro f hf
        have h1 := congrArg Subtype.val (hfz ⟨f, hfZle hf⟩ hf)
        rw [Sec165.conjAut_apply] at h1
        calc f * c.u = (c.u * f * c.u⁻¹) * c.u := by rw [show c.u * f * c.u⁻¹ = f from h1]
          _ = c.u * f := by group
      have hcommw : ∀ f ∈ fZero Z M (cenHull Z (c.u * w)) c.t, f * w = w * f := by
        intro f hf
        have h1 : f * (c.u * w) = (c.u * w) * f :=
          mem_centralizer_singleton_iff.mp (Cor713.zHull_le _ (hfZle hf))
        apply mul_left_cancel (a := c.u)
        calc c.u * (f * w) = (c.u * f) * w := by group
          _ = (f * c.u) * w := by rw [hcommu f hf]
          _ = f * (c.u * w) := by group
          _ = (c.u * w) * f := h1
          _ = c.u * (w * f) := by group
      have hF0B : fZero Z M (cenHull Z (c.u * w)) c.t ≤ c.B0 := by
        have hzh : zHull Z (M ⊓ cenHull Z (c.u * w)) ≤ c.B0 := by
          refine (closure_le _).mpr ?_
          rintro g' ⟨hgZ, hgMF⟩
          have hgf : g' ∈ fZero Z M (cenHull Z (c.u * w)) c.t :=
            subset_closure (Or.inl (subset_closure ⟨hgZ, hgMF⟩))
          exact subset_closure ⟨hgZ, mem_centralizer_singleton_iff.mpr (hcommu g' hgf)⟩
        refine (closure_le _).mpr ?_
        rintro y' (hy' | hy')
        · exact hzh hy'
        · rw [Set.mem_singleton_iff] at hy'
          rw [hy']
          exact Sec164.t_mem_B0 c
      have hle : fZero Z M (cenHull Z (c.u * w)) c.t ≤ c.B0 ⊓ centralizer ({w} : Set X) :=
        fun f hf => mem_inf.mpr ⟨hF0B hf, mem_centralizer_singleton_iff.mpr (hcommw f hf)⟩
      have hcard1 := Subgroup.card_le_of_le hle
      obtain ⟨e₃⟩ := hisow
      have hcard2 : Nat.card ↥(c.B0 ⊓ centralizer ({w} : Set X)) = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
        rw [← Sec165.map_autFixed_conjAut hwN,
          Subgroup.card_map_of_injective c.B0.subtype_injective, Nat.card_congr e₃.toEquiv]
        exact Bender.card_psl2_even k hk
      have hcard3 : Nat.card ↥(fZero Z M (cenHull Z (c.u * w)) c.t) =
          2 ^ m' * ((2 ^ m') ^ 2 - 1) := by
        cases hL2 with
        | linear _ _ e₄ =>
          rw [Nat.card_congr e₄.toEquiv]
          exact Bender.card_psl2_even m' (by omega)
      rw [hcard2, hcard3, hk1] at hcard1
      have hP : 4 ≤ 2 ^ m' := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) hm'2
      have hQ : 16 ≤ (2 ^ m') ^ 2 := by nlinarith
      have h60 : 4 * 15 ≤ 2 ^ m' * ((2 ^ m') ^ 2 - 1) := Nat.mul_le_mul hP (by omega)
      norm_num at hcard1
      omega
    have hm5 : 5 ≤ 2 ^ k + 1 := by
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    obtain ⟨j, hj⟩ := BenderSub.cube_mem_of_pair h311 hB3 hAF' hA' hsF hs2 hs1 hsA' hx₁A hx₁'A
      hsx₁ hsx₁' hord₁
    refine false_of_cube hm5 hmodd hx'o hxu' hx'u ⟨j, hψinj ?_⟩
    rw [map_pow, map_zpow]
    exact hj

end SecGap

theorem SecGap.false_of_four_gap
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M)
    (h161 : Lemma161Stmt Z M) (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M)
    (h164 : Lemma164Stmt Z M) (c₀ : Conf16 Z M)
    (hV : ∃ V : Subgroup X, V ≤ c₀.D ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1) : False := by
  obtain ⟨c, -, v, hvD, hv2, hv1, hvu, huv, hvt, hvz⟩ := Sec165.exists_conf_four S c₀ hV
  obtain ⟨⟨n, i, e, hB⟩, -, -, -⟩ := h163 c
  have hu164 := (h164 c n i e hB).1.2
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huz : c.u * c.z = c.z * c.u := (mem_centralizer_singleton_iff.mp (Sec164.z_mem_B c)).symm
  obtain ⟨w, hwD, hw2, hw1, hwu, huw, hwt, hwz, huN, k', hk', hFT, hniu, hisou⟩ :=
    Sec165.exists_16H S h121 h161 h162 h163 c hvD hv2 hv1 hvu huv hvt hvz
  obtain ⟨hwN, -, k, hk, hB0T, hniw, hisow⟩ :=
    Sec165.B0_structure S h162 c hB hu164 hw2 hw1 hwu huw hwt hwz
  have hw2o : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hwM : w ∈ M := (mem_inf.mp hwD).1
  have hCM : ¬ centralizer ({w} : Set X) ≤ M := fun h =>
    c.htM (h (mem_centralizer_singleton_iff.mpr hwt.symm))
  obtain ⟨n', i', e', hBw⟩ := S.benderSub_exists (S.cor714_centralizer_ne_top hw2o) hCM
    ⟨c.z, c.hz, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hwz.symm, c.hzM⟩⟩
    (Sec165.not_solvable_of_commute_t h163 c hwM hw2o hwt)
  have hkk : k = k' := Sec165.eq_of_fixed S c hB hwN hwz hwt hk hisow huN hBw.invol hk' hisou
  subst hkk
  obtain ⟨x, hxDB, hxo, hxt, hxw⟩ := SecGap.exists_inverted_of_outer_order S hk hB0T c.hz c.hzM
    (Sec164.z_mem_B0 c) c.htM (Sec164.t_mem_B0 c) ht2 hwN hwD hw2 hwz hniw hisow (dvd_refl _)
  have hzF : c.z ∈ cenHull Z w :=
    subset_closure ⟨c.hz, mem_centralizer_singleton_iff.mpr hwz.symm⟩
  have htF : c.t ∈ cenHull Z w :=
    subset_closure ⟨c.ht, mem_centralizer_singleton_iff.mpr hwt.symm⟩
  obtain ⟨x', hx'DF, hx'o, hx't, hx'u⟩ := SecGap.exists_inverted_of_outer_order S hk hFT c.hz
    c.hzM hzF c.htM htF ht2 huN c.hu c.u_mul_self huz hniu hisou (dvd_refl _)
  have hxD := (mem_inf.mp hxDB).1
  have hxB := (mem_inf.mp hxDB).2
  have hx'D := (mem_inf.mp hx'DF).1
  have hx'F := (mem_inf.mp hx'DF).2
  have hxu : x * c.u = c.u * x := mem_centralizer_singleton_iff.mp (Sec164.B0_le_B c hxB)
  have hx'w : x' * w = w * x' := mem_centralizer_singleton_iff.mp (Cor713.zHull_le _ hx'F)
  exact SecGap.endgame S h162 h163 lemma311BenderStmt c hwD hw2 hwu huw hwt hwz hk hwN hB0T
    hniw hisow hxD hx'D hxo hx'o hxu hxt hxw hx't hx'u hx'w

theorem ZDSetup.prop165_gap
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h162 : Lemma162Stmt Z M) (h163 : Lemma163Stmt Z M) (h164 : Lemma164Stmt Z M) :
    Prop165Stmt Z M := by
  intro c
  refine le_antisymm ?_ ?_
  · by_contra hge
    push Not at hge
    obtain ⟨a, b, haD, hbD, ha2, hb2, hab, hcomm⟩ :=
      exists_commuting_involutions_of_two_le_pRank (Nat.succ_le_of_lt hge)
    have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
    have hbb : b * b = 1 := by rw [← sq, ← hb2, pow_orderOf_eq_one]
    have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; omega
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb2; omega
    exact SecGap.false_of_four_gap S h121 h161 h162 h163 h164 c
      ⟨fourSub a b haa hbb hcomm, fourSub_le haD hbD, card_fourSub ha1 hb1 hab,
        mul_self_of_mem_fourSub⟩
  · exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (E := zpowers c.u)
      (zpowers_le.mpr c.hu) (Sec165.isElemAbelian_zpowers_two c.hu2) (k := 1)
      (by rw [Nat.card_zpowers, c.hu2, pow_one])

end CFSG.GH74.Uniqueness
