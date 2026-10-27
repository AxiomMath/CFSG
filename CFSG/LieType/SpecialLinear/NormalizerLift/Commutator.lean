module

public import CFSG.LieType.SpecialLinear.NormalizerLift.IndexBounds
public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]
  (π : SpecialLinearGroup (Fin n) F →* H)

omit [Finite F] [CharP F 2] in
theorem stdAut_fix_unitriangular (hn : 3 ≤ n) (A : GL (Fin n) F) (σ : F ≃+* F) {ε : ℕ}
    (hε : ε ≤ 1)
    (hfix : ∀ u ∈ LinearFlag.unitriangular n F,
      CFSG.QuasithinUnique.K1.stdAut A σ ε u = u) :
    σ = 1 ∧ ε = 0 := by
  rcases (show ε = 0 ∨ ε = 1 by omega) with h0 | h1
  · subst h0
    exact ⟨(CFSG.QuasithinUnique.K1.exists_matrix_of_fixes_zero hn A σ
      (fun hij t =>
        hfix _ (CFSG.QuasithinUnique.K1.transvection_mem_unitriangular hij t))).1, rfl⟩
  · subst h1
    exact (CFSG.QuasithinUnique.K1.false_of_fixes_one hn A σ
      (fun hij t =>
        hfix _ (CFSG.QuasithinUnique.K1.transvection_mem_unitriangular hij t))).elim

theorem liftAut_apply_eq_of_commute (hker : π.ker ≤ LinearFlag.scalars n F) (hn : 3 ≤ n)
    (x : rangeNormalizer π) {u : SpecialLinearGroup (Fin n) F}
    (hu : u ∈ LinearFlag.unitriangular n F) (hcomm : (x : H) * π u = π u * (x : H)) :
    liftAut π hker hn x u = u := by
  classical
  let Φ : MulAut (SpecialLinearGroup (Fin n) F) := liftAut π hker hn x
  have hπ : π (Φ u) = π u := by
    rw [liftAut_spec, hcomm]
    group
  let z : SpecialLinearGroup (Fin n) F := u⁻¹ * Φ u
  have hz_ker : z ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [z]
    rw [map_mul, map_inv, hπ, inv_mul_cancel]
  have hz_scal : z ∈ LinearFlag.scalars n F := hker hz_ker
  have hz_center : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) :=
    LinearFlag.scalars_le_center n F hz_scal
  have hΦeq : Φ u = u * z := by
    dsimp [z]
    group
  obtain ⟨P0, hP0⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := n) (by omega)
  have hU2 : IsPGroup 2 (LinearFlag.unitriangular n F) := by
    rw [← hP0]
    exact P0.isPGroup'
  obtain ⟨a, ha⟩ := hU2.exists_orderOf_eq_pow
    (⟨u, hu⟩ : LinearFlag.unitriangular n F)
  have ha' : orderOf u = 2 ^ a := by
    rw [Subgroup.orderOf_coe (⟨u, hu⟩ : LinearFlag.unitriangular n F)]
    exact ha
  have huz : Commute u z := Subgroup.mem_center_iff.mp hz_center u
  have huΦ : Commute u (Φ u) := by
    rw [hΦeq]
    exact (Commute.refl u).mul_right huz
  have hinv : Commute u⁻¹ (Φ u) := huΦ.inv_left
  have hdiv := hinv.orderOf_mul_dvd_lcm
  have hzu : u⁻¹ * Φ u = z := rfl
  rw [hzu] at hdiv
  have hz_two : orderOf z ∣ 2 ^ a := by
    refine hdiv.trans (Nat.lcm_dvd ?_ ?_)
    · rw [orderOf_inv, ha']
    · exact (orderOf_map_dvd
        (Φ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) u).trans
        (by rw [ha'])
  have hZodd : Odd (Nat.card (LinearFlag.scalars n F)) :=
    (CFSG.ClassicalGroups.SpecialLinear.odd_card_sub_one_of_char_two (F := F)).of_dvd_nat
      (LinearFlag.card_scalars_dvd (K := F) (n := n) (by omega))
  have hz_card : orderOf z ∣ Nat.card (LinearFlag.scalars n F) :=
    (LinearFlag.scalars n F).orderOf_dvd_natCard hz_scal
  have hdvd : orderOf z ∣
      Nat.gcd (2 ^ a) (Nat.card (LinearFlag.scalars n F)) :=
    Nat.dvd_gcd hz_two hz_card
  rw [((hZodd.coprime_two_left).pow_left a).gcd_eq_one] at hdvd
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  rw [hΦeq, hz1, mul_one]

theorem mem_range_of_commute_unitriangular (hker : π.ker ≤ LinearFlag.scalars n F)
    (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    {x : H} (hxN : x ∈ rangeNormalizer π) (hx2 : x * x = 1)
    (hcomm : ∀ u ∈ LinearFlag.unitriangular n F, x * π u = π u * x) :
    x ∈ π.range := by
  classical
  let xN : rangeNormalizer π := ⟨x, hxN⟩
  have hfix : ∀ u ∈ LinearFlag.unitriangular n F, liftAut π hker hn xN u = u := by
    intro u hu
    exact liftAut_apply_eq_of_commute π hker hn xN hu (hcomm u hu)
  have hfixstd : ∀ u ∈ LinearFlag.unitriangular n F,
      CFSG.QuasithinUnique.K1.stdAut (stdData π hker hn xN).1
        (stdData π hker hn xN).2.1 (stdData π hker hn xN).2.2 u = u := by
    intro u hu
    rw [← liftAut_eq_stdAut]
    exact hfix u hu
  obtain ⟨hσ, hε⟩ := stdAut_fix_unitriangular hn
    (stdData π hker hn xN).1 (stdData π hker hn xN).2.1
    (stdData_eps_le_one π hker hn xN) hfixstd
  have hfield : fieldPart π hker hn xN = 1 := hσ
  have hgraph : graphPart π hker hn xN = 1 := by
    change Multiplicative.ofAdd ((stdData π hker hn xN).2.2 : ZMod 2) = 1
    rw [hε]
    rfl
  exact mem_range_of_fieldPart_graphPart_eq_one π hker hn hodd hxN hx2 hfield hgraph

theorem exists_commutator_pow_eq (hker : π.ker ≤ LinearFlag.scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    {x : H} (hxN : x ∈ rangeNormalizer π) (hx2 : x * x = 1)
    (hxU : x ∈ Subgroup.normalizer ((LinearFlag.unitriangular n F).map π : Set H))
    (hx : x ∉ π.range) :
    ∃ g ∈ LinearFlag.unitriangular n F, ∃ u ∈ LinearFlag.unitriangular n F,
      u ≠ 1 ∧ u * u = 1 ∧ ∃ j : ℕ, π u = (x * π g * x⁻¹ * (π g)⁻¹) ^ j := by
  classical
  by_cases hcommU : ∀ g ∈ LinearFlag.unitriangular n F, x * π g = π g * x
  · exact absurd (mem_range_of_commute_unitriangular π hker hn hodd hxN hx2 hcommU) hx
  · push Not at hcommU
    obtain ⟨g, hgU, hgne⟩ := hcommU
    let w : H := x * π g * x⁻¹ * (π g)⁻¹
    have hw_ne : w ≠ 1 := by
      intro hw
      apply hgne
      calc x * π g = (x * π g * x⁻¹ * (π g)⁻¹) * (π g * x) := by group
        _ = 1 * (π g * x) := by
            rw [show x * π g * x⁻¹ * (π g)⁻¹ = 1 from hw]
        _ = π g * x := one_mul _
    have hπg_mem : π g ∈ (LinearFlag.unitriangular n F).map π :=
      Subgroup.mem_map_of_mem π hgU
    have hconj_mem : x * π g * x⁻¹ ∈ (LinearFlag.unitriangular n F).map π :=
      (Subgroup.mem_normalizer_iff.mp hxU (π g)).mp hπg_mem
    have hwU : w ∈ (LinearFlag.unitriangular n F).map π :=
      ((LinearFlag.unitriangular n F).map π).mul_mem hconj_mem
        (((LinearFlag.unitriangular n F).map π).inv_mem hπg_mem)
    obtain ⟨P0, hP0⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := n) (by omega)
    have hU2 : IsPGroup 2 (LinearFlag.unitriangular n F) := by
      rw [← hP0]
      exact P0.isPGroup'
    have hmap2 : IsPGroup 2 ((LinearFlag.unitriangular n F).map π) := hU2.map π
    obtain ⟨a, ha⟩ := hmap2.exists_orderOf_eq_pow
      (⟨w, hwU⟩ : (LinearFlag.unitriangular n F).map π)
    have ha' : orderOf w = 2 ^ a := by
      rw [Subgroup.orderOf_coe (⟨w, hwU⟩ : (LinearFlag.unitriangular n F).map π)]
      exact ha
    have hapos : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · rw [h0, pow_zero] at ha'
        exact absurd (orderOf_eq_one_iff.mp ha') hw_ne
      · exact hpos
    let j : ℕ := 2 ^ (a - 1)
    have hwj_ne : w ^ j ≠ 1 := by
      intro h1
      have hdvd : orderOf w ∣ j := orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [ha'] at hdvd
      have hle : 2 ^ a ≤ 2 ^ (a - 1) :=
        Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
      have hle' : a ≤ a - 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
      omega
    have hwjU : w ^ j ∈ (LinearFlag.unitriangular n F).map π :=
      ((LinearFlag.unitriangular n F).map π).pow_mem hwU j
    obtain ⟨u, huU, hu_eq⟩ := Subgroup.mem_map.mp hwjU
    have hu1 : u ≠ 1 := by
      intro h1
      apply hwj_ne
      rw [← hu_eq, h1, map_one]
    have hu2 : u * u = 1 := by
      have hmem : u * u ∈ LinearFlag.unitriangular n F :=
        (LinearFlag.unitriangular n F).mul_mem huU huU
      have hπsq : π (u * u) = 1 := by
        rw [map_mul, hu_eq]
        have h2j : 2 * j = 2 ^ a := by
          have ha1 : a = (a - 1) + 1 := by omega
          rw [ha1, pow_succ]
          dsimp [j]
          ring
        calc w ^ j * w ^ j = w ^ (j + j) := (pow_add w j j).symm
          _ = w ^ (2 * j) := by rw [two_mul j]
          _ = w ^ (2 ^ a) := by rw [h2j]
          _ = 1 := by rw [← ha']; exact pow_orderOf_eq_one w
      have hmemker : u * u ∈ π.ker := MonoidHom.mem_ker.mpr hπsq
      have hscal : u * u ∈ LinearFlag.scalars n F := hker hmemker
      have hbot : u * u ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin n) F)) := by
        rw [← LinearFlag.unitriangular_inf_scalars (n := n) (K := F)]
        exact ⟨hmem, hscal⟩
      simpa using hbot
    exact ⟨g, hgU, u, huU, hu1, hu2, j, hu_eq⟩

theorem exists_inner_involution_card_fix {R Y : Type*} [Ring R] [AddCommGroup Y] [Module R Y]
    [Finite Y] (π : SpecialLinearGroup (Fin n) F →* (Y ≃ₗ[R] Y))
    (hker : π.ker ≤ LinearFlag.scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set (Y ≃ₗ[R] Y)), Odd (orderOf c))
    {x : Y ≃ₗ[R] Y} (hxN : x ∈ rangeNormalizer π) (hx2 : x * x = 1)
    (hxU : x ∈ Subgroup.normalizer
      ((LinearFlag.unitriangular n F).map π : Set (Y ≃ₗ[R] Y)))
    (hx : x ∉ π.range) :
    ∃ u ∈ LinearFlag.unitriangular n F, u ≠ 1 ∧ u * u = 1 ∧
      Nat.card {y : Y // x y = y} ^ 2 ≤ Nat.card Y * Nat.card {y : Y // π u y = y} := by
  classical
  obtain ⟨g, hgU, u, huU, hu1, hu2, j, hju⟩ :=
    exists_commutator_pow_eq π hker hn hodd hxN hx2 hxU hx
  refine ⟨u, huU, hu1, hu2, ?_⟩
  let c : Y ≃ₗ[R] Y := π g
  let w : Y ≃ₗ[R] Y := x * c * x⁻¹ * c⁻¹
  have hwu : w ^ j = π u := hju.symm
  let A : AddSubgroup Y := x.fixedSubmodule.toAddSubgroup
  let B : AddSubgroup Y := A.map c.toAddEquiv.toAddMonoidHom
  have hcardfix : ∀ e : Y ≃ₗ[R] Y,
      Nat.card e.fixedSubmodule.toAddSubgroup = Nat.card {y : Y // e y = y} := by
    intro e
    refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro y
    exact (Submodule.mem_toAddSubgroup _).trans LinearMap.mem_fixedSubmodule_iff
  have hle : A ⊓ B ≤ (w ^ j).fixedSubmodule.toAddSubgroup := by
    intro y hy
    rw [AddSubgroup.mem_inf] at hy
    obtain ⟨hyA, hyB⟩ := hy
    have hxA : x y = y := by simpa [A] using hyA
    have hyB' : y ∈ A.map c.toAddEquiv.toAddMonoidHom := by simpa [B] using hyB
    obtain ⟨a, ha, haeq⟩ := hyB'
    have hxa : x a = a := by simpa [A] using ha
    have hca : c a = y := haeq
    have hcy : c⁻¹ y = a := by
      rw [← hca]
      simpa only [LinearEquiv.coe_inv] using c.symm_apply_apply a
    have hxcy : x (c⁻¹ y) = c⁻¹ y := by rw [hcy, hxa]
    have hwy : w y = y := by
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      calc w y = x (c (x⁻¹ (c⁻¹ y))) := by
            simp only [w, LinearEquiv.mul_apply]
        _ = x (c (x (c⁻¹ y))) := by rw [hxinv]
        _ = x (c (c⁻¹ y)) := by rw [hxcy]
        _ = x y := by
            have h := c.apply_symm_apply y
            rw [show c⁻¹ y = c.symm y from rfl, h]
        _ = y := hxA
    rw [Submodule.mem_toAddSubgroup, LinearMap.mem_fixedSubmodule_iff]
    change (w ^ j) y = y
    rw [LinearEquiv.pow_apply]
    exact Function.iterate_fixed hwy j
  have hcard_inf : Nat.card ↥(A ⊓ B) ≤
      Nat.card {y : Y // (w ^ j) y = y} := by
    have h1 : Nat.card ↥(A ⊓ B) ≤ Nat.card (w ^ j).fixedSubmodule.toAddSubgroup :=
      AddSubgroup.card_le_of_le hle
    rwa [hcardfix (w ^ j)] at h1
  have hprod : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) =
      Nat.card A * Nat.card B := by
    have e1 := AddSubgroup.relIndex_mul_card B (A ⊔ B)
    have e2 := AddSubgroup.relIndex_mul_card B A
    rw [inf_of_le_left (le_sup_right : B ≤ A ⊔ B), AddSubgroup.relIndex_sup_right] at e1
    rw [← e1, ← e2, inf_comm]
    ring
  have hBcard : Nat.card B = Nat.card A :=
    AddSubgroup.card_map_of_injective (f := c.toAddEquiv.toAddMonoidHom) c.injective
  have hsup : Nat.card ↥(A ⊔ B) ≤ Nat.card Y :=
    AddSubgroup.card_le_card_addGroup (A ⊔ B)
  have hmain : Nat.card A * Nat.card A ≤
      Nat.card Y * Nat.card {y : Y // (w ^ j) y = y} := by
    calc Nat.card A * Nat.card A = Nat.card A * Nat.card B := by rw [hBcard]
      _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := hprod.symm
      _ ≤ Nat.card Y * Nat.card {y : Y // (w ^ j) y = y} :=
          Nat.mul_le_mul hsup hcard_inf
  rw [← hcardfix x, pow_two, ← hwu]
  exact hmain

theorem exists_inner_involution_of_offender_inf_eq_bot {R Y : Type*} [Ring R] [AddCommGroup Y]
    [Module R Y] [Finite Y] (π : SpecialLinearGroup (Fin n) F →* (Y ≃ₗ[R] Y))
    (hker : π.ker ≤ LinearFlag.scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set (Y ≃ₗ[R] Y)), Odd (orderOf c))
    (D : Subgroup (Y ≃ₗ[R] Y)) (hD : D ≤ rangeNormalizer π) (hD2 : ∀ d ∈ D, d * d = 1)
    (hD1 : D ≠ ⊥)
    (hDU : D ≤ Subgroup.normalizer
      ((LinearFlag.unitriangular n F).map π : Set (Y ≃ₗ[R] Y)))
    (hinf : D ⊓ π.range = ⊥)
    (hoff : Nat.card Y ≤ Nat.card D * Nat.card {y : Y // ∀ d ∈ D, d y = y}) :
    ∃ u ∈ LinearFlag.unitriangular n F, u ≠ 1 ∧ u * u = 1 ∧
      Nat.card Y ≤ 16 * Nat.card {y : Y // π u y = y} := by
  classical
  have : Finite (Y ≃ₗ[R] Y) :=
    Finite.of_injective (fun e : Y ≃ₗ[R] Y => (e : Y → Y))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  have : Finite D := Subtype.finite
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
  have hd2 : d * d = 1 := hD2 d hdD
  have hdN : d ∈ rangeNormalizer π := hD hdD
  have hdU : d ∈ Subgroup.normalizer
      ((LinearFlag.unitriangular n F).map π : Set (Y ≃ₗ[R] Y)) := hDU hdD
  have hd_range : d ∉ π.range := by
    intro hdmem
    have hmem : d ∈ D ⊓ π.range := Subgroup.mem_inf.mpr ⟨hdD, hdmem⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hd1 (Subtype.ext hmem)
  obtain ⟨u, huU, hu1, hu2, hcardu⟩ :=
    exists_inner_involution_card_fix π hker hn hodd hdN hd2 hdU hd_range
  refine ⟨u, huU, hu1, hu2, ?_⟩
  have hDcard : Nat.card D ≤ 4 := by
    have h1 := card_le_four_mul_card_inf π hker hn hodd D hD hD2
    rw [hinf, Subgroup.card_bot] at h1
    simpa using h1
  have hCD_le : Nat.card {y : Y // ∀ e ∈ D, e y = y} ≤
      Nat.card {y : Y // d y = y} := by
    refine Nat.card_le_card_of_injective
      (fun y : {y : Y // ∀ e ∈ D, e y = y} => ⟨y.1, y.2 d hdD⟩) ?_
    intro y₁ y₂ h
    exact Subtype.ext (congrArg (fun z : {y : Y // d y = y} => (z : Y)) h)
  have hY_le : Nat.card Y ≤ Nat.card D * Nat.card {y : Y // d y = y} :=
    hoff.trans (Nat.mul_le_mul_left _ hCD_le)
  let C : ℕ := Nat.card {y : Y // d y = y}
  let E : ℕ := Nat.card {y : Y // π u y = y}
  have hCpos : 0 < C := by
    have : Nonempty {y : Y // d y = y} := ⟨⟨0, by simp⟩⟩
    exact Nat.card_pos
  have hC_le : C ≤ Nat.card D * E := by
    have h1 : C * C ≤ (Nat.card D * E) * C := by
      calc C * C = C ^ 2 := by ring
        _ ≤ Nat.card Y * E := hcardu
        _ ≤ (Nat.card D * C) * E := Nat.mul_le_mul_right E hY_le
        _ = (Nat.card D * E) * C := by ring
    exact Nat.le_of_mul_le_mul_right h1 hCpos
  calc Nat.card Y ≤ Nat.card D * C := hY_le
    _ ≤ Nat.card D * (Nat.card D * E) := Nat.mul_le_mul_left _ hC_le
    _ = Nat.card D * Nat.card D * E := by ring
    _ ≤ 4 * 4 * E :=
        Nat.mul_le_mul_right E (Nat.mul_le_mul hDcard hDcard)
    _ = 16 * E := by norm_num

end CFSG.LieType.SpecialLinear
