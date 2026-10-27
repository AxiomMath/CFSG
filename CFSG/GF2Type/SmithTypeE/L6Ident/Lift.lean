module

public import CFSG.GF2Type.SmithTypeE.L6.Local

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14 CFSG.GF2Type.SmithTypeE.L6
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem mem_conj_QG_of_sq_eq (h34a : SmithL6E34a) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {x y g : G}
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxy : (x * y) ^ 2 = g * S.z * g⁻¹) :
    g⁻¹ * x * g ∈ S.QG := by
  by_contra hQ
  have hxi : x⁻¹ = x := SME.inv_eq_of_isConj S hx
  have hyi : y⁻¹ = y := SME.inv_eq_of_isConj S hy
  have hx2 : x * x = 1 := by rw [← mul_inv_cancel x, hxi]
  have ha : IsConj S.z ((x * y) ^ 2) := hxy ▸ isConj_iff.mpr ⟨g, rfl⟩
  have hai : ((x * y) ^ 2)⁻¹ = (x * y) ^ 2 := SME.inv_eq_of_isConj S ha
  have h1 : y * x * y⁻¹ = x * (x * y) ^ 2 := by
    rw [hyi, sq, show x * (x * y * (x * y)) = (x * x) * (y * x * y) by group, hx2, one_mul]
  have h2 : (x * y) ^ 2 * x = x * (x * y) ^ 2 := by
    have e : (x * y) ^ 2 = (y * x) ^ 2 := by
      rw [← hai, ← inv_pow, mul_inv_rev, hxi, hyi]
    calc (x * y) ^ 2 * x = (y * x) ^ 2 * x := by rw [e]
      _ = y * x * y * (x * x) := by rw [sq]; group
      _ = x * (x * y) ^ 2 := by rw [hx2, mul_one, ← h1, hyi]
  have hxM : g⁻¹ * x * g ∈ S.M := by
    rw [mem_centralizer_singleton_iff]
    have hg : g * S.z = (x * y) ^ 2 * g := by rw [hxy]; group
    calc g⁻¹ * x * g * S.z = g⁻¹ * (x * (x * y) ^ 2) * g := by
          rw [mul_assoc, hg]; group
      _ = g⁻¹ * ((x * y) ^ 2 * x) * g := by rw [h2]
      _ = S.z * (g⁻¹ * x * g) := by
          rw [show g⁻¹ * ((x * y) ^ 2 * x) * g = (g⁻¹ * (x * y) ^ 2 * g) * (g⁻¹ * x * g) by group,
            hxy]
          group
  apply h34a G S hw hU _ (hx.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)) hxM hQ
  have e : g⁻¹ * x * g * S.z = (g⁻¹ * y) * x * (g⁻¹ * y)⁻¹ := by
    rw [show (g⁻¹ * y) * x * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * x * y⁻¹) * g by group, h1, hxy]
    group
  rw [e]
  exact hx.trans (isConj_iff.mpr ⟨_, rfl⟩)

theorem card_conj_QG_dvd [Finite G] (S : Setting G) (y₀ : G) :
    Nat.card {y : G // ∃ q ∈ S.QG, y = q⁻¹ * y₀ * q} ∣ Nat.card S.QG := by
  classical
  let A : Subgroup (ConjAct G) := S.QG.map (MulEquiv.toMonoidHom ConjAct.toConjAct)
  have hA : Nat.card A = Nat.card S.QG :=
    (Nat.card_congr (S.QG.equivMapOfInjective _ ConjAct.toConjAct.injective).toEquiv).symm
  have horb : MulAction.orbit A y₀ = {y : G | ∃ q ∈ S.QG, y = q⁻¹ * y₀ * q} := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨a, ⟨q, hq, rfl⟩⟩, rfl⟩
      refine ⟨q⁻¹, S.QG.inv_mem hq, ?_⟩
      simp [Subgroup.smul_def, ConjAct.smul_def]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨ConjAct.toConjAct q⁻¹, ⟨q⁻¹, S.QG.inv_mem hq, rfl⟩⟩, ?_⟩
      simp [Subgroup.smul_def, ConjAct.smul_def]
  have e : Nat.card {y : G // ∃ q ∈ S.QG, y = q⁻¹ * y₀ * q} = (MulAction.orbit A y₀).ncard := by
    rw [horb, ← Nat.card_coe_set_eq]
    rfl
  rw [← hA, e, ← MulAction.index_stabilizer]
  exact (MulAction.stabilizer A y₀).index_dvd_card

theorem exists_lift_commute (h34a : SmithL6E34a) (h34b : SmithL6E34b)
    (hLoc : SmithL62LocalInput) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {t u y₀ : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M) (htQ : t ∉ S.QG)
    (htu : orderOf (t * u) = 3) (hy₀ : IsConj S.z y₀) (hy₀M : y₀ ∈ S.M) (hy₀Q : y₀ ∉ S.QG)
    (hty : t * y₀ * t⁻¹ * y₀⁻¹ ∈ S.QG) (huy : u * y₀ * u⁻¹ * y₀⁻¹ ∈ S.QG) :
    ∃ y : G, IsConj S.z y ∧ y₀⁻¹ * y ∈ S.QG ∧ Commute y t ∧ Commute y u := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hti : t⁻¹ = t := SME.inv_eq_of_isConj S ht
  have hui : u⁻¹ = u := SME.inv_eq_of_isConj S hu
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = t * u := ⟨_, rfl⟩
  rw [← hθ] at htu
  have hθM : θ ∈ S.M := by rw [hθ]; exact S.M.mul_mem htM huM
  have hθ3 : θ ^ 3 = 1 := htu ▸ pow_orderOf_eq_one θ
  let Y := {y : G // IsConj S.z y ∧ y₀⁻¹ * y ∈ S.QG}
  have hYM : ∀ y : Y, y.1 ∈ S.M := fun y => by
    have := S.M.mul_mem hy₀M (S.QG_le_M y.2.2)
    rwa [mul_inv_cancel_left] at this
  have hYQ : ∀ y : Y, y.1 ∉ S.QG := fun y hy => hy₀Q (by
    have := S.QG.mul_mem y.2.2 (S.QG.inv_mem hy)
    rw [mul_inv_cancel_right] at this
    simpa using S.QG.inv_mem this)
  have hnorm : ∀ {c : G}, c ∈ S.M → c * y₀ * c⁻¹ * y₀⁻¹ ∈ S.QG → ∀ y : G, y₀⁻¹ * y ∈ S.QG →
      y₀⁻¹ * (c * y * c⁻¹) ∈ S.QG := by
    intro c hc hcy y hy
    have h1 : y₀⁻¹ * (c * y₀ * c⁻¹ * y₀⁻¹) * y₀ ∈ S.QG := by
      have := S.conj_mem_QG (S.M.inv_mem hy₀M) hcy
      simpa using this
    have h2 := S.conj_mem_QG hc hy
    have := S.QG.mul_mem h1 h2
    rw [show y₀⁻¹ * (c * y₀ * c⁻¹ * y₀⁻¹) * y₀ * (c * (y₀⁻¹ * y) * c⁻¹) =
      y₀⁻¹ * (c * y * c⁻¹) by group] at this
    exact this
  have hθy : θ * y₀ * θ⁻¹ * y₀⁻¹ ∈ S.QG := by
    have h1 := S.conj_mem_QG htM huy
    have := S.QG.mul_mem h1 hty
    rw [show t * (u * y₀ * u⁻¹ * y₀⁻¹) * t⁻¹ * (t * y₀ * t⁻¹ * y₀⁻¹) =
      θ * y₀ * θ⁻¹ * y₀⁻¹ by rw [hθ]; group] at this
    exact this
  have hmapθ : ∀ (n : ℕ) (y : Y), IsConj S.z (θ ^ n * y.1 * (θ ^ n)⁻¹) ∧
      y₀⁻¹ * (θ ^ n * y.1 * (θ ^ n)⁻¹) ∈ S.QG := by
    intro n
    induction n with
    | zero => intro y; simpa using y.2
    | succ n ih =>
      intro y
      obtain ⟨h1, h2⟩ := ih y
      rw [pow_succ', show θ * θ ^ n * y.1 * (θ * θ ^ n)⁻¹ =
        θ * (θ ^ n * y.1 * (θ ^ n)⁻¹) * θ⁻¹ by group]
      exact ⟨h1.trans (isConj_iff.mpr ⟨θ, rfl⟩), hnorm hθM hθy _ h2⟩
  let σ : Equiv.Perm Y :=
    { toFun := fun y => ⟨θ * y.1 * θ⁻¹, by simpa using hmapθ 1 y⟩
      invFun := fun y => ⟨θ ^ 2 * y.1 * (θ ^ 2)⁻¹, hmapθ 2 y⟩
      left_inv := fun y => Subtype.ext (by
        simp only
        rw [show θ ^ 2 * (θ * y.1 * θ⁻¹) * (θ ^ 2)⁻¹ = θ ^ 3 * y.1 * (θ ^ 3)⁻¹ by group, hθ3]
        group)
      right_inv := fun y => Subtype.ext (by
        simp only
        rw [show θ * (θ ^ 2 * y.1 * (θ ^ 2)⁻¹) * θ⁻¹ = θ ^ 3 * y.1 * (θ ^ 3)⁻¹ by group, hθ3]
        group) }
  have hσ3 : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun y => Subtype.ext ?_
    rw [pow_one, pow_three]
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id_eq, σ, Equiv.coe_fn_mk]
    rw [show θ * (θ * (θ * y.1 * θ⁻¹) * θ⁻¹) * θ⁻¹ = θ ^ 3 * y.1 * (θ ^ 3)⁻¹ by
      rw [pow_three]; group, hθ3]
    group
  have hY3 : ¬ 3 ∣ Fintype.card Y := by
    intro h3
    have hYeq : Nat.card Y = Nat.card {y : G // ∃ q ∈ S.QG, y = q⁻¹ * y₀ * q} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
      constructor
      · rintro ⟨hy, hyQ⟩
        exact h34b G S hw hU y₀ y hy₀ hy hy₀M hy₀Q hyQ
      · rintro ⟨q, hq, rfl⟩
        refine ⟨hy₀.trans (isConj_iff.mpr ⟨q⁻¹, by group⟩), ?_⟩
        have := S.conj_mem_QG (S.M.inv_mem hy₀M) (S.QG.mul_mem (S.QG.inv_mem hq)
          (S.conj_mem_QG hy₀M hq))
        rw [show y₀⁻¹ * (q⁻¹ * (y₀ * q * y₀⁻¹)) * y₀⁻¹⁻¹ = y₀⁻¹ * (q⁻¹ * y₀ * q) by group] at this
        exact this
    have hdvd := card_conj_QG_dvd S y₀
    rw [← hYeq, Nat.card_eq_fintype_card] at hdvd
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp (S.extraspecial.1.map S.M.subtype)
    rw [show Nat.card S.QG = Nat.card (S.Q.map S.M.subtype) from rfl, hn] at hdvd
    have h32 := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) (h3.trans hdvd))
    omega
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y₁, hy₁⟩ := Equiv.Perm.exists_fixed_point_of_prime hY3 hσ3
  have hθy₁ : θ * y₁.1 * θ⁻¹ = y₁.1 := congrArg Subtype.val hy₁
  have hy₁M := hYM y₁
  have hy₁Q := hYQ y₁
  have hy₁i : y₁.1⁻¹ = y₁.1 := SME.inv_eq_of_isConj S y₁.2.1
  have huy₁ : u * y₁.1 * u⁻¹ = t * y₁.1 * t⁻¹ := by
    have hu' : u = t⁻¹ * θ := by rw [hθ]; group
    rw [hu', show t⁻¹ * θ * y₁.1 * (t⁻¹ * θ)⁻¹ = t⁻¹ * (θ * y₁.1 * θ⁻¹) * t by group, hθy₁, hti]
  by_cases h12 : t * y₁.1 * t⁻¹ = y₁.1
  · refine ⟨y₁.1, y₁.2.1, y₁.2.2, ?_, ?_⟩
    · exact (mul_inv_eq_iff_eq_mul.mp h12).symm
    · rw [h12] at huy₁
      exact (mul_inv_eq_iff_eq_mul.mp huy₁).symm
  · exfalso
    have hy₂ : IsConj S.z (t * y₁.1 * t⁻¹) := y₁.2.1.trans (isConj_iff.mpr ⟨t, rfl⟩)
    have hy₂Q : y₁.1⁻¹ * (t * y₁.1 * t⁻¹) ∈ S.QG := by
      have h0 : y₀⁻¹ * (t * y₁.1 * t⁻¹) ∈ S.QG := hnorm htM hty _ y₁.2.2
      have := S.QG.mul_mem (S.QG.inv_mem y₁.2.2) h0
      rw [show (y₀⁻¹ * y₁.1)⁻¹ * (y₀⁻¹ * (t * y₁.1 * t⁻¹)) = y₁.1⁻¹ * (t * y₁.1 * t⁻¹) by
        group] at this
      exact this
    obtain ⟨q, hq, hqe⟩ := h34b G S hw hU y₁.1 _ y₁.2.1 hy₂ hy₁M hy₁Q hy₂Q
    have hsq : (t * y₁.1) ^ 2 = t * y₁.1 * t⁻¹ * y₁.1 := by rw [sq, hti]; group
    have hcomm : t * y₁.1 * t⁻¹ * y₁.1 ∈ (⁅zpowers y₁.1, S.QG⁆ : Subgroup G) := by
      have e : t * y₁.1 * t⁻¹ * y₁.1 = q⁻¹ * y₁.1 * q⁻¹⁻¹ * y₁.1⁻¹ := by rw [hqe, hy₁i, inv_inv]
      rw [e, Subgroup.commutator_comm]
      have := Subgroup.commutator_mem_commutator (S.QG.inv_mem hq) (mem_zpowers y₁.1)
      rwa [commutatorElement_def] at this
    have h4 : (t * y₁.1) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, hsq]
      exact sq_eq_one_of_mem_commutator h34a S hw hU y₁.2.1 hy₁M hy₁Q hcomm
    have hne : (t * y₁.1) ^ 2 ≠ 1 := by
      rw [hsq]
      intro h
      apply h12
      calc t * y₁.1 * t⁻¹ = t * y₁.1 * t⁻¹ * y₁.1 * y₁.1⁻¹ := by group
        _ = y₁.1 := by rw [h, one_mul, hy₁i]
    have hord : orderOf (t * y₁.1) = 4 := by
      have hd := orderOf_dvd_of_pow_eq_one h4
      have h2 : ¬ orderOf (t * y₁.1) ∣ 2 := fun h => hne (orderOf_dvd_iff_pow_eq_one.mp h)
      have hpos := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩)
      have hle := Nat.le_of_dvd (by norm_num) hd
      interval_cases h : orderOf (t * y₁.1) <;> simp_all
    obtain ⟨g, hg⟩ := isConj_iff.mp ((hLoc G S hw hU t y₁.1 ht y₁.2.1 htM hy₁M htQ).2 hord)
    have hga : (t * y₁.1) ^ 2 = g * S.z * g⁻¹ := hg.symm
    have hgb : (u * y₁.1) ^ 2 = g * S.z * g⁻¹ := by
      rw [← hga]
      calc (u * y₁.1) ^ 2 = u * y₁.1 * u⁻¹ * y₁.1 := by rw [sq, hui]; group
        _ = t * y₁.1 * t⁻¹ * y₁.1 := by rw [huy₁]
        _ = (t * y₁.1) ^ 2 := by rw [sq, hti]; group
    have hgt := mem_conj_QG_of_sq_eq h34a S hw hU ht y₁.2.1 hga
    have hgu := mem_conj_QG_of_sq_eq h34a S hw hU hu y₁.2.1 hgb
    have hθQ : g⁻¹ * θ * g ∈ S.QG := by
      have := S.QG.mul_mem hgt hgu
      rwa [show g⁻¹ * t * g * (g⁻¹ * u * g) = g⁻¹ * θ * g by rw [hθ]; group] at this
    obtain ⟨k, hk⟩ := (S.extraspecial.1.map S.M.subtype) ⟨_, hθQ⟩
    have hk' : (g⁻¹ * θ * g) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : (g⁻¹ * θ * g) ^ 3 = 1 := by
      rw [show (g⁻¹ * θ * g) ^ 3 = g⁻¹ * θ ^ 3 * g by rw [pow_three, pow_three]; group, hθ3]
      group
    have hord' : orderOf (g⁻¹ * θ * g) = 3 := by
      rw [show g⁻¹ * θ * g = MulAut.conj g⁻¹ θ by simp [MulAut.conj_apply], MulEquiv.orderOf_eq]
      exact htu
    have := orderOf_dvd_of_pow_eq_one hk'
    rw [hord'] at this
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) this) (by norm_num)

end CFSG.GF2Type.SmithTypeE.L6Ident
