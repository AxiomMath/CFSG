module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCoverRadical
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

section Map

variable {K : Type*} [Field K] {G G' : Type*} [Group G] [Group G']

@[expose] def heisenbergMap (R : LinearCover.HeisenbergRoots K G) (ρ : G →* G') :
    LinearCover.HeisenbergRoots K G' where
  x a := ρ (R.x a)
  y b := ρ (R.y b)
  w c := ρ (R.w c)
  x_add a b := by rw [R.x_add, map_mul]
  y_add a b := by rw [R.y_add, map_mul]
  w_add a b := by rw [R.w_add, map_mul]
  w_mul_x c a := by rw [← map_mul, R.w_mul_x, map_mul]
  w_mul_y c b := by rw [← map_mul, R.w_mul_y, map_mul]
  x_mul_y a b := by rw [← map_mul, R.x_mul_y, map_mul, map_mul]
  gx := ρ R.gx
  gy := ρ R.gy
  gx_conj a := by rw [← map_inv, ← map_mul, ← map_mul, R.gx_conj]
  gy_conj b := by rw [← map_inv, ← map_mul, ← map_mul, R.gy_conj]
  S := R.S.map ρ
  x_mem a := Subgroup.mem_map_of_mem ρ (R.x_mem a)
  y_mem b := Subgroup.mem_map_of_mem ρ (R.y_mem b)
  w_mem c := Subgroup.mem_map_of_mem ρ (R.w_mem c)
  mem_S s hs := by
    obtain ⟨u, hu, rfl⟩ := hs
    obtain ⟨a, b, c, rfl⟩ := R.mem_S u hu
    exact ⟨a, b, c, by rw [map_mul, map_mul]⟩

end Map

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 0}

theorem leviHom_injective_two : Function.Injective (leviHom h 2) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, leviHom, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_hypProj] at hA
  obtain ⟨c, -, -, hc⟩ := hA
  have hm := congrArg Units.val hc
  rw [MonoidHom.comp_apply, coe_lHom, coe_slHom, GeneralLinearGroup.coe_scalar] at hm
  have hA' : (A : Matrix (Fin 2) (Fin 2) K) = scalar (Fin 2) (c : K) := by
    ext i j
    have := congrFun (congrFun hm (.inl i)) (.inl j)
    simpa [evenMat, scalar_apply, diagonal_apply] using this
  have hc2 : (c : K) ^ 2 = 1 := by
    have := A.2
    rw [hA', scalar_apply, det_diagonal, Fin.prod_univ_two] at this
    rw [pow_two]
    exact this
  have hc1 : (c : K) = 1 := by
    have h2 : ((c : K) + 1) ^ 2 = 0 := by
      rw [add_sq, hc2, mul_one, one_pow, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul,
        add_zero, CharTwo.add_self_eq_zero]
    have h1 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact h1
  refine Subgroup.mem_bot.mpr (Subtype.ext ?_)
  rw [hA', hc1, scalar_apply, diagonal_one]
  rfl

omit [CharP K 2] in
theorem levi_cover_data (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 θ.ker) [Group.IsPerfect (leviHom h r).range] :
    ∃ θR : ↥(⁅(leviHom h r).range.comap θ, (leviHom h r).range.comap θ⁆ : Subgroup E) →*
        (leviHom h r).range,
      Function.Surjective θR ∧ (∀ z, (θR z : hypPSU h r 0) = θ z) ∧
      θR.ker ≤ Subgroup.center _ ∧ IsPGroup 2 θR.ker := by
  set R := (leviHom h r).range with hR
  set Y := ⁅R.comap θ, R.comap θ⁆ with hY
  have hYR : ∀ y : Y, θ y ∈ R := fun y =>
    Subgroup.mem_comap.1 (Subgroup.commutator_le_self (R.comap θ) y.2)
  let θR : Y →* R := (θ.comp Y.subtype).codRestrict R hYR
  have hθRker : ∀ z : Y, θR z = 1 ↔ θ z = 1 := fun z => by
    rw [Subtype.ext_iff]
    rfl
  refine ⟨θR, fun x => ?_, fun z => rfl, fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθRker z).mp hz)) g), fun z => ?_⟩
  · have hx : (x : hypPSU h r 0) ∈ Y.map θ := by
      rw [SymplecticSixCover.map_derivedComap hθ R]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  · obtain ⟨n, hn⟩ := h2 ⟨(z : Y), (hθRker z).mp z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩

theorem map_conj_of_mul_eq {G G' : Type*} [Group G] [Group G'] (ρ : G →* G') {g u v : G}
    (he : g * u = v * g) : ρ g * ρ u * (ρ g)⁻¹ = ρ v := by
  rw [← map_mul, he, map_mul, mul_inv_cancel_right]

theorem levi_inj_three [Finite K] [Finite E] (hK : 8 ≤ Nat.card K) {θ : E →* hypPSU h 3 0}
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    ∀ y ∈ ⁅(leviHom h 3).range.comap θ, (leviHom h 3).range.comap θ⁆, θ y = 1 → y = 1 := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have : Group.IsPerfect (leviHom h 3).range := Group.IsPerfect.range _
  set R := (leviHom h 3).range with hR
  set Y := ⁅R.comap θ, R.comap θ⁆ with hY
  have : Group.IsPerfect Y := SymplecticSixCover.isPerfect_derivedComap hθ hC R
  obtain ⟨θR, hθRsurj, hθRval, hcen, h2R⟩ := levi_cover_data hθ hC h2
  set ρ : SpecialLinearGroup (Fin 3) K →* R := (leviHom h 3).rangeRestrict with hρ
  have hρsurj : Function.Surjective ρ := (leviHom h 3).rangeRestrict_surjective
  set roots := heisenbergMap (LinearCover.slRoots (K := K)) ρ with hroots
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hS : ∃ P : Sylow 2 R, (P : Subgroup R) = roots.S :=
    ⟨P₀.mapSurjective hρsurj, by rw [Sylow.coe_mapSurjective, hP₀]; rfl⟩
  obtain ⟨tu, htu⟩ := LinearCover.exists_units_pow_three_ne_one hK
  set t : K := (tu : K)
  have ht0 : t ≠ 0 := tu.ne_zero
  have ht3 : t ^ 3 ≠ 1 := fun h => htu (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl))
  have hs₁ : ![t, t, t⁻¹ * t⁻¹] 0 * ![t, t, t⁻¹ * t⁻¹] 1 * ![t, t, t⁻¹ * t⁻¹] 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp
  have hs₂ : ![t⁻¹ * t⁻¹, t, t] 0 * ![t⁻¹ * t⁻¹, t, t] 1 * ![t⁻¹ * t⁻¹, t, t] 2 = 1 := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    field_simp
  set h₁ := LinearCover.diagSL ![t, t, t⁻¹ * t⁻¹] hs₁
  set h₂ := LinearCover.diagSL ![t⁻¹ * t⁻¹, t, t] hs₂
  have hv₁0 : ![t, t, t⁻¹ * t⁻¹] 0 = t := rfl
  have hv₁1 : ![t, t, t⁻¹ * t⁻¹] 1 = t := rfl
  have hv₁2 : ![t, t, t⁻¹ * t⁻¹] 2 = t⁻¹ * t⁻¹ := rfl
  have hv₂0 : ![t⁻¹ * t⁻¹, t, t] 0 = t⁻¹ * t⁻¹ := rfl
  have hv₂1 : ![t⁻¹ * t⁻¹, t, t] 1 = t := rfl
  have hv₂2 : ![t⁻¹ * t⁻¹, t, t] 2 = t := rfl
  obtain ⟨g₁, hg₁⟩ := hθRsurj (ρ h₁)
  obtain ⟨g₂, hg₂⟩ := hθRsurj (ρ h₂)
  set φ₁ := MulAut.conj g₁
  set φ₂ := MulAut.conj g₂
  have hφ : ∀ (g e : Y), θR (MulAut.conj g e) = θR g * θR e * (θR g)⁻¹ := fun g e => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hconjC : ∀ (g : Y), ∀ z ∈ θR.ker, MulAut.conj g z = z := fun g z hz => by
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp (hcen hz) g, mul_inv_cancel_right]
  have := Fintype.ofFinite K
  have hm : Odd (Nat.card K - 1) := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' n.ne_zero).mpr even_two) odd_one
  have hφ₂m : φ₂ ^ (Nat.card K - 1) = 1 := by
    have hpow : h₂ ^ (Nat.card K - 1) = 1 := by
      apply Subtype.ext
      change (diagonal ![t⁻¹ * t⁻¹, t, t]) ^ (Nat.card K - 1) = 1
      rw [diagonal_pow, ← diagonal_one]
      congr 1
      funext i
      have hi : ![t⁻¹ * t⁻¹, t, t] i ≠ 0 := LinearCover.diag_ne_zero hs₂ i
      rw [Pi.pow_apply, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ hi
    have hz : g₂ ^ (Nat.card K - 1) ∈ Subgroup.center Y := hcen (by
      rw [MonoidHom.mem_ker, map_pow, hg₂, ← map_pow, hpow, map_one])
    rw [← map_pow]
    ext x
    rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right,
      MulAut.one_apply]
  have hr₂ : (t ^ 3)⁻¹ ≠ 1 := fun h => ht3 (inv_eq_one.mp h)
  have hbot := LinearCover.ker_eq_bot_of_two_weights (r₁ := t ^ 3) (r₂ := (t ^ 3)⁻¹) roots hS
    θR hθRsurj hcen h2R φ₁ φ₂ ht3 hr₂ (hconjC g₁) (hconjC g₂) hm hφ₂m
    (fun e₀ a he => by
      rw [hφ, hg₁, he]
      change ρ h₁ * ρ (LinearFieldFour.xMat a) * (ρ h₁)⁻¹ = ρ (LinearFieldFour.xMat a)
      rw [map_conj_of_mul_eq ρ (LinearCover.diagSL_mul_xMat _ hs₁ a), hv₁0, hv₁1]
      congr 2
      field_simp)
    (fun e₀ c he => by
      rw [hφ, hg₁, he]
      change ρ h₁ * ρ (LinearFieldFour.wMat c) * (ρ h₁)⁻¹ = ρ (LinearFieldFour.wMat (t ^ 3 * c))
      rw [map_conj_of_mul_eq ρ (LinearCover.diagSL_mul_wMat _ hs₁ c), hv₁0, hv₁2]
      congr 2
      field_simp)
    (fun e₀ a he => by
      rw [hφ, hg₂, he]
      change ρ h₂ * ρ (LinearFieldFour.xMat a) * (ρ h₂)⁻¹ =
        ρ (LinearFieldFour.xMat ((t ^ 3)⁻¹ * a))
      rw [map_conj_of_mul_eq ρ (LinearCover.diagSL_mul_xMat _ hs₂ a), hv₂0, hv₂1]
      congr 2
      field_simp)
    (fun e₀ b he => by
      rw [hφ, hg₂, he]
      change ρ h₂ * ρ (LinearFieldFour.yMat b) * (ρ h₂)⁻¹ = ρ (LinearFieldFour.yMat b)
      rw [map_conj_of_mul_eq ρ (LinearCover.diagSL_mul_yMat _ hs₂ b), hv₂1, hv₂2]
      congr 2
      field_simp)
    (fun e₀ c he => by
      rw [hφ, hg₂, he]
      change ρ h₂ * ρ (LinearFieldFour.wMat c) * (ρ h₂)⁻¹ =
        ρ (LinearFieldFour.wMat ((t ^ 3)⁻¹ * c))
      rw [map_conj_of_mul_eq ρ (LinearCover.diagSL_mul_wMat _ hs₂ c), hv₂0, hv₂2]
      congr 2
      field_simp)
  intro y hy hy1
  have hk : (⟨y, hy⟩ : Y) ∈ θR.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext (by rw [hθRval]; exact hy1)
  rw [hbot, Subgroup.mem_bot] at hk
  exact congrArg Subtype.val hk

theorem exists_levi_split_large [Finite E] (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    Group.IsPerfect (leviHom h r).range ∧
      ∀ y ∈ ⁅(leviHom h r).range.comap θ, (leviHom h r).range.comap θ⁆, θ y = 1 → y = 1 := by
  have := h.finite
  have hcard : Nat.card K = 2 ^ (2 * f) := h.card
  have hK16 : 16 ≤ Nat.card K := by
    rw [hcard]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr ⟨s, hs⟩)
    have : Group.IsPerfect (leviHom h 2).range := Group.IsPerfect.range _
    refine ⟨this, ?_⟩
    set R := (leviHom h 2).range with hR
    set Y := ⁅R.comap θ, R.comap θ⁆ with hY
    obtain ⟨θF, hθF, hθFι⟩ :=
      SymplecticSixCover.exists_derivedComap_cover hθ (leviHom h 2) leviHom_injective_two
    have hθFker : ∀ z : Y, θF z = 1 ↔ θ z = 1 := fun z => by
      rw [← hθFι, ← map_one (leviHom h 2)]
      exact leviHom_injective_two.eq_iff.symm
    have : Group.IsPerfect Y := SymplecticSixCover.isPerfect_derivedComap hθ hC _
    have hcenF : θF.ker ≤ Subgroup.center Y := fun z hz =>
      Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
    have h2F : IsPGroup 2 θF.ker := fun z => by
      obtain ⟨n, hn⟩ := h2 ⟨(z : Y), (hθFker z).mp z.2⟩
      exact ⟨n, Subtype.ext (Subtype.ext (by
        simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
    have hbot := CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot
      (2 * f) (by omega) hcard θF hθF hcenF h2F
    intro y hy hy1
    have hk : (⟨y, hy⟩ : Y) ∈ θF.ker := (hθFker _).mpr hy1
    rw [hbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  · have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    exact ⟨Group.IsPerfect.range _, levi_inj_three (by omega) hθ hC h2⟩
  · exact exists_levi_split (by omega) hr4 hθ hC h2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryEvenCover
