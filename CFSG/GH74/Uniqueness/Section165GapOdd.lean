module

public import CFSG.GH74.Uniqueness.Section173Basic
public import CFSG.GH74.Uniqueness.Bender.LinearOdd

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

namespace SecGap

section PureGroup

variable {K : Type} [Group K] [Finite K]

theorem zpowers_eq_of_mem_cyclic {T : Subgroup K} (hT : IsCyclic T) {x x' : K} (hx : x ∈ T)
    (hx' : x' ∈ T) (hord : orderOf x = orderOf x') : zpowers x = zpowers x' := by
  refine Bender.eq_of_card_eq_of_cyclic hT (zpowers_le.mpr hx) (zpowers_le.mpr hx') ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hord]

omit [Finite K] in
theorem mem_commutator_of_inverted {F : Subgroup K} {s y : K} (hy : y ∈ F)
    (hsy : s * y * s⁻¹ = y⁻¹) (hodd : Odd (orderOf y)) : y ∈ ⁅F, zpowers s⁆ := by
  have hcomm : ⁅y, s⁆ = y * y := by
    rw [commutatorElement_def]
    have h1 : s * y⁻¹ * s⁻¹ = y := by
      have := congrArg (fun z => z⁻¹) hsy
      simpa [mul_assoc] using this
    calc y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) := by group
      _ = y * y := by rw [h1]
  have hmem : ⁅y, s⁆ ∈ ⁅F, zpowers s⁆ := commutator_mem_commutator hy (mem_zpowers s)
  rw [hcomm] at hmem
  exact Bender.mem_of_mul_self_mem_of_odd hodd hmem

omit [Finite K] in
theorem conj_pow_of_inverted {s y : K} (hsy : s * y * s⁻¹ = y⁻¹) (n : ℕ) :
    s * y ^ n * s⁻¹ = (y ^ n)⁻¹ := by
  have h := map_pow (MulAut.conj s) y n
  simp only [MulAut.conj_apply] at h
  rw [h, hsy, inv_pow]

omit [Finite K] in
theorem conj_zpow_of_inverted {s y : K} (hsy : s * y * s⁻¹ = y⁻¹) (n : ℤ) :
    s * y ^ n * s⁻¹ = (y ^ n)⁻¹ := by
  have h := map_zpow (MulAut.conj s) y n
  simp only [MulAut.conj_apply] at h
  rw [h, hsy, inv_zpow']
  simp

theorem zpowers_eq_of_linear
    {n : ℕ} (h : Bender.BenderType K n 1 1) {A : Subgroup K}
    (hA : Odd (Nat.card A)) {x x' : K} (hx : x ∈ A) (hx' : x' ∈ A) (hx1 : x ≠ 1)
    (hord : orderOf x = orderOf x') : zpowers x = zpowers x' := by
  have hA1 : A ≠ ⊥ := fun hb => hx1 (by simpa [hb] using hx)
  obtain ⟨T, -, hAT, hTc, -⟩ := h.linear_odd_subgroup hA hA1
  exact zpowers_eq_of_mem_cyclic hTc (hAT hx) (hAT hx') hord

theorem zpowers_eq_of_suzuki
    {n e : ℕ} (h : Bender.BenderType K n 2 e) {A : Subgroup K}
    (hA : Odd (Nat.card A)) {x x' : K} (hx : x ∈ A) (hx' : x' ∈ A) (hx1 : x ≠ 1)
    (hord : orderOf x = orderOf x') : zpowers x = zpowers x' := by
  have hA1 : A ≠ ⊥ := fun hb => hx1 (by simpa [hb] using hx)
  obtain ⟨T, hAT, hTc, -⟩ := h.suzuki_odd_subgroup hA hA1
  exact zpowers_eq_of_mem_cyclic hTc (hAT hx) (hAT hx') hord

theorem unitary_cube_mem
    (h311 : Lemma311BenderStmt) {n e : ℕ} (h : Bender.BenderType K n 3 e)
    {A : Subgroup K} (hA : Odd (Nat.card A)) {s : K} (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A) {x x' : K} (hx : x ∈ A) (hx' : x' ∈ A)
    (hsx : s * x * s⁻¹ = x⁻¹) (hsx' : s * x' * s⁻¹ = x'⁻¹) (hord : orderOf x = orderOf x') :
    x' ^ 3 ∈ zpowers (x ^ 3) := by
  by_cases hB : ∃ Q : Sylow 2 K, A ≤ Bender.borel (Q : Subgroup K)
  · obtain ⟨Q, hQ⟩ := hB
    obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
    obtain ⟨q', -, hq⟩ := hc.exists_conj_cartan_of_odd Q.isPGroup' hQ hA
    have hxc := hq x hx
    have hx'c := hq x' hx'
    have hord' : orderOf (q' * x * q'⁻¹) = orderOf (q' * x' * q'⁻¹) := by
      have e1 := orderOf_injective (MulAut.conj q').toMonoidHom (MulAut.conj q').injective x
      have e2 := orderOf_injective (MulAut.conj q').toMonoidHom (MulAut.conj q').injective x'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e1 e2
      rw [e1, e2, hord]
    have heq := zpowers_eq_of_mem_cyclic hc.isCyclic hxc hx'c hord'
    have hmem : q' * x' * q'⁻¹ ∈ zpowers (q' * x * q'⁻¹) := heq ▸ mem_zpowers _
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
    have hj' : x' = x ^ j := by
      have e : (q' * x * q'⁻¹) ^ j = q' * x ^ j * q'⁻¹ := by simp
      rw [e] at hj
      have := congrArg (fun z => q'⁻¹ * z * q') hj
      simpa [mul_assoc] using this.symm
    refine mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [hj', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  · push Not at hB
    obtain ⟨F, F₀, hF, hle⟩ := h311 h A hA s hs2 hs1 hsA hB
    have hxF₀ : x ∈ F₀ := hle (mem_sup_left hx)
    have hx'F₀ : x' ∈ F₀ := hle (mem_sup_left hx')
    obtain ⟨π, -, hπk⟩ := hF.perm
    have hodd_of : ∀ y ∈ A, Odd (orderOf y) := fun y hy => by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : A)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hA this
    have hcube : ∀ y ∈ F₀, Odd (orderOf y) → y ^ 3 ∈ F := by
      intro y hy hyo
      set g : ↥F₀ := ⟨y, hy⟩ with hg
      have hgo : Odd (orderOf g) := by rw [hg, Subgroup.orderOf_mk]; exact hyo
      have h1 : orderOf (π g) ∣ orderOf g := orderOf_map_dvd π g
      have h2 : orderOf (π g) ∣ 6 := by
        have := orderOf_dvd_natCard (π g)
        rwa [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at this
      have h3 : Odd (orderOf (π g)) := Odd.of_dvd_nat hgo h1
      have h4 : orderOf (π g) ∣ 3 := by
        have hcop : Nat.Coprime (orderOf (π g)) 2 := h3.coprime_two_right
        exact hcop.dvd_of_dvd_mul_right (by rw [show 3 * 2 = 6 by norm_num]; exact h2)
      have h5 : π g ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h4
      have h6 : g ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, h5]
      rw [hπk, Subgroup.mem_subgroupOf] at h6
      simpa using h6
    have hx3 : x ^ 3 ∈ F := hcube x hxF₀ (hodd_of x hx)
    have hx'3 : x' ^ 3 ∈ F := hcube x' hx'F₀ (hodd_of x' hx')
    have hs3 : s * x ^ 3 * s⁻¹ = (x ^ 3)⁻¹ := conj_pow_of_inverted hsx 3
    have hs3' : s * x' ^ 3 * s⁻¹ = (x' ^ 3)⁻¹ := conj_pow_of_inverted hsx' 3
    have hodd3 : Odd (orderOf (x ^ 3)) := Odd.of_dvd_nat (hodd_of x hx) (orderOf_pow_dvd 3)
    have hodd3' : Odd (orderOf (x' ^ 3)) := Odd.of_dvd_nat (hodd_of x' hx') (orderOf_pow_dvd 3)
    have hc1 := mem_commutator_of_inverted hx3 hs3 hodd3
    have hc2 := mem_commutator_of_inverted hx'3 hs3' hodd3'
    have hord3 : orderOf (x ^ 3) = orderOf (x' ^ 3) := by
      rw [orderOf_pow' _ (by norm_num), orderOf_pow' _ (by norm_num), hord]
    have heq := zpowers_eq_of_mem_cyclic hF.cyc hc1 hc2 hord3
    rw [heq]
    exact mem_zpowers _

end PureGroup

section InX

variable {X : Type} [Group X] [Finite X]

theorem exists_zpow_of_linear
    {F : Subgroup X} {n : ℕ} (h : Bender.BenderType ↥F n 1 1)
    {A : Subgroup X} (hAF : A ≤ F) (hA : Odd (Nat.card A)) {x x' : X} (hx : x ∈ A)
    (hx' : x' ∈ A) (hx1 : x ≠ 1) (hord : orderOf x = orderOf x') : ∃ j : ℤ, x' = x ^ j := by
  have hA' : Odd (Nat.card (A.subgroupOf F)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv]
  have heq := zpowers_eq_of_linear h hA' (x := (⟨x, hAF hx⟩ : ↥F)) (x' := ⟨x', hAF hx'⟩)
    (mem_subgroupOf.mpr hx) (mem_subgroupOf.mpr hx') (fun h1 => hx1 (congrArg Subtype.val h1))
    (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact hord)
  have hm : (⟨x', hAF hx'⟩ : ↥F) ∈ zpowers (⟨x, hAF hx⟩ : ↥F) := by
    rw [heq]; exact mem_zpowers _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hm
  exact ⟨j, by simpa using congrArg Subtype.val hj.symm⟩

theorem exists_zpow_of_suzuki
    {F : Subgroup X} {n e : ℕ} (h : Bender.BenderType ↥F n 2 e)
    {A : Subgroup X} (hAF : A ≤ F) (hA : Odd (Nat.card A)) {x x' : X} (hx : x ∈ A)
    (hx' : x' ∈ A) (hx1 : x ≠ 1) (hord : orderOf x = orderOf x') : ∃ j : ℤ, x' = x ^ j := by
  have hA' : Odd (Nat.card (A.subgroupOf F)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv]
  have heq := zpowers_eq_of_suzuki h hA' (x := (⟨x, hAF hx⟩ : ↥F)) (x' := ⟨x', hAF hx'⟩)
    (mem_subgroupOf.mpr hx) (mem_subgroupOf.mpr hx') (fun h1 => hx1 (congrArg Subtype.val h1))
    (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact hord)
  have hm : (⟨x', hAF hx'⟩ : ↥F) ∈ zpowers (⟨x, hAF hx⟩ : ↥F) := by
    rw [heq]; exact mem_zpowers _
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hm
  exact ⟨j, by simpa using congrArg Subtype.val hj.symm⟩

variable {Z : Set X} {M : Subgroup X}

theorem BenderSub.cube_mem_of_pair
    (h311 : Lemma311BenderStmt) {F : Subgroup X} {n e : ℕ}
    (hB : BenderSub Z M F n 3 e) {A : Subgroup X} (hAF : A ≤ F) (hA : Odd (Nat.card A)) {s : X}
    (hsF : s ∈ F) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsA : ∀ a ∈ A, s * a * s⁻¹ ∈ A) {x x' : X}
    (hx : x ∈ A) (hx' : x' ∈ A) (hsx : s * x * s⁻¹ = x⁻¹) (hsx' : s * x' * s⁻¹ = x'⁻¹)
    (hord : orderOf x = orderOf x') : ∃ j : ℤ, x' ^ 3 = x ^ (3 * j) := by
  have hZodd := hB.odd_card_center
  have hZo : ∀ z ∈ center ↥F, Odd (orderOf z) := fun z hz =>
    Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard _ hz)
  set φ : ↥F →* ↥F ⧸ center ↥F := QuotientGroup.mk' (center ↥F) with hφ
  set A₁ : Subgroup ↥F := A.subgroupOf F with hA₁
  set s₁ : ↥F := ⟨s, hsF⟩ with hs₁
  set x₁ : ↥F := ⟨x, hAF hx⟩ with hx₁
  set x₁' : ↥F := ⟨x', hAF hx'⟩ with hx₁'
  have hs₁2 : s₁ * s₁ = 1 := Subtype.ext hs2
  have hs₁i : s₁⁻¹ = s₁ := inv_eq_of_mul_eq_one_right hs₁2
  have hsx₁ : s₁ * x₁ * s₁⁻¹ = x₁⁻¹ := Subtype.ext (by simpa using hsx)
  have hsx₁' : s₁ * x₁' * s₁⁻¹ = x₁'⁻¹ := Subtype.ext (by simpa using hsx')
  have hcent : ∀ z ∈ center ↥F, s₁ * z * s₁⁻¹ = z⁻¹ → z = 1 := by
    intro z hz hsz
    have h1 : s₁ * z * s₁⁻¹ = z := by
      rw [(Subgroup.mem_center_iff.mp hz s₁), mul_assoc, mul_inv_cancel, mul_one]
    have h2 : z = z⁻¹ := h1.symm.trans hsz
    have h3 : z * z = 1 := by
      calc z * z = z * z⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel z
    exact Sec172.eq_one_of_sq h3 (hZo z hz)
  have horder : ∀ y : ↥F, s₁ * y * s₁⁻¹ = y⁻¹ → orderOf (φ y) = orderOf y := by
    intro y hsy
    apply Nat.dvd_antisymm (orderOf_map_dvd φ y)
    apply orderOf_dvd_of_pow_eq_one
    have h1 : φ (y ^ orderOf (φ y)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    have h2 : y ^ orderOf (φ y) ∈ center ↥F := by
      rwa [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hcent _ h2 (conj_pow_of_inverted hsy _)
  have hA₁card : Nat.card A₁ = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAF).toEquiv
  have hAbarodd : Odd (Nat.card ↥(A₁.map φ)) :=
    Odd.of_dvd_nat (by rw [hA₁card]; exact hA) (Subgroup.card_map_dvd A₁ φ)
  have hsbar2 : φ s₁ * φ s₁ = 1 := by rw [← map_mul, hs₁2, map_one]
  have hsbar1 : φ s₁ ≠ 1 := by
    intro h
    have hmem : s₁ ∈ center ↥F := by
      rw [← QuotientGroup.ker_mk' (center ↥F)]
      exact MonoidHom.mem_ker.mpr h
    have h2 : orderOf s₁ = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hs₁2) (fun h => hs1 (congrArg Subtype.val h))
    have h3 := hZo s₁ hmem
    rw [h2] at h3
    exact absurd h3 (by decide)
  have hsAbar : ∀ a ∈ A₁.map φ, φ s₁ * a * (φ s₁)⁻¹ ∈ A₁.map φ := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨s₁ * a * s₁⁻¹, Subgroup.mem_subgroupOf.mpr (hsA _ (Subgroup.mem_subgroupOf.mp ha)),
      by rw [map_mul, map_mul, map_inv]⟩
  have hxbar : φ x₁ ∈ A₁.map φ := ⟨x₁, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hx'bar : φ x₁' ∈ A₁.map φ := ⟨x₁', Subgroup.mem_subgroupOf.mpr hx', rfl⟩
  have hsxbar : φ s₁ * φ x₁ * (φ s₁)⁻¹ = (φ x₁)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hsx₁, map_inv]
  have hsx'bar : φ s₁ * φ x₁' * (φ s₁)⁻¹ = (φ x₁')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hsx₁', map_inv]
  have hordbar : orderOf (φ x₁) = orderOf (φ x₁') := by
    rw [horder x₁ hsx₁, horder x₁' hsx₁', hx₁, hx₁', Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hord
  have hmem := unitary_cube_mem h311 hB.bender hAbarodd hsbar2 hsbar1 hsAbar hxbar hx'bar hsxbar
    hsx'bar hordbar
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  set a : ↥F := x₁ ^ (3 * j) with ha
  set b : ↥F := x₁' ^ 3 with hb
  have hφab : φ a = φ b := by
    rw [ha, hb, map_zpow, map_pow, ← hj, zpow_mul]
    simp
  have hz : a⁻¹ * b ∈ center ↥F := by
    rw [← QuotientGroup.ker_mk' (center ↥F), MonoidHom.mem_ker, map_mul, map_inv, hφab,
      inv_mul_cancel]
  have hsa : s₁ * a * s₁⁻¹ = a⁻¹ := by rw [ha]; exact conj_zpow_of_inverted hsx₁ _
  have hsb : s₁ * b * s₁⁻¹ = b⁻¹ := by rw [hb]; exact conj_pow_of_inverted hsx₁' _
  have hz1 : a⁻¹ * b = 1 := by
    apply hcent _ hz
    set z₀ : ↥F := a⁻¹ * b with hz₀
    have hbz : b = a * z₀ := by rw [hz₀]; group
    have hsz : s₁ * z₀ * s₁⁻¹ = a * b⁻¹ := by
      rw [hz₀]
      calc s₁ * (a⁻¹ * b) * s₁⁻¹ = (s₁ * a * s₁⁻¹)⁻¹ * (s₁ * b * s₁⁻¹) := by group
        _ = a * b⁻¹ := by rw [hsa, hsb]; group
    rw [hsz, hbz]
    calc a * (a * z₀)⁻¹ = a * (z₀⁻¹ * a⁻¹) := by rw [mul_inv_rev]
      _ = (a * z₀⁻¹) * a⁻¹ := by group
      _ = (z₀⁻¹ * a) * a⁻¹ := by
        rw [show a * z₀⁻¹ = z₀⁻¹ * a from
          (Subgroup.mem_center_iff.mp ((center ↥F).inv_mem hz) a)]
      _ = z₀⁻¹ := by group
  have hab : b = a := by
    have := congrArg (fun w => a * w) hz1
    simpa using this
  refine ⟨j, ?_⟩
  have := congrArg Subtype.val hab
  simpa [ha, hb, hx₁, hx₁'] using this

end InX

end SecGap

end CFSG.GH74.Uniqueness
