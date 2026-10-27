module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightNonsplitCentralizers

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

open scoped Pointwise

variable {Y : Type*} [Group Y]

section Nonsplit

variable {U : Subgroup Y} [U.Normal] [IsElementaryAbelian 2 U]

omit [U.Normal] in
theorem exists_independent_with_first (hU8 : Nat.card U = 8) {x0 : U} (h0 : x0 ≠ 1) :
    ∃ e : Fin 3 → U, Independent e ∧ e 0 = x0 := by
  classical
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨x1, hx1⟩ := exists_not_mem_finset_of_card_lt ({1, x0} : Finset U) (by
    rw [hU8]; exact (Finset.card_le_two).trans_lt (by omega))
  obtain ⟨x2, hx2⟩ := exists_not_mem_finset_of_card_lt ({1, x0, x1, x0 * x1} : Finset U) (by
    rw [hU8]; exact (Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx1 hx2
  refine ⟨![x0, x1, x2], independent_of_ne ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> tauto

theorem coordsS_ne_one : coordsS ≠ 1 := by
  intro h
  have := congrArg (fun σ : MulAut Coords => σ (Multiplicative.ofAdd ![0, 1, 0])) h
  revert this
  decide

omit [IsElementaryAbelian 2 U] in
theorem conjNormal_eq_one_iff (hcent : Subgroup.centralizer (U : Set Y) = U) (g : Y) :
    (MulAut.conjNormal g : MulAut U) = 1 ↔ g ∈ U := by
  have hmemc : g ∈ U ↔ g ∈ Subgroup.centralizer (U : Set Y) := by rw [hcent]
  rw [hmemc, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have h2 := congrArg (fun σ : MulAut U => ((σ ⟨z, hz⟩ : U) : Y)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc z * g = g * z * g⁻¹ * g := by rw [h2]
      _ = g * z := by group
  · intro h
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h z z.2, mul_inv_cancel_right]

theorem exists_outside_involution [Finite Y] (hU8 : Nat.card U = 8)
    (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    (hnosplit : ¬ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤) :
    ∃ x : Y, x * x = 1 ∧ x ∉ U := by
  classical
  obtain ⟨e, he⟩ := exists_independent hU8
  let ι := coordEquiv he hU8
  let σ : MulAut U := MulAut.congr ι coordsS
  have hσ1 : σ ≠ 1 := by
    intro h
    apply coordsS_ne_one
    apply (MulAut.congr ι).injective
    rw [map_one]
    exact h
  have hσ2 : σ * σ = 1 := by
    change MulAut.congr ι coordsS * MulAut.congr ι coordsS = 1
    rw [← map_mul, coordsS_mul_self, map_one]
  obtain ⟨y, hy⟩ := hfull σ
  have hρy : (MulAut.conjNormal y : MulAut U) = σ :=
    MulEquiv.ext fun z => Subtype.ext ((MulAut.conjNormal_apply y z).trans (hy z).symm)
  have hyU : y ∉ U := by
    intro hyU
    apply hσ1
    rw [← hρy]
    exact (conjNormal_eq_one_iff hcent y).mpr hyU
  have hyy : y * y ∈ U := by
    rw [← conjNormal_eq_one_iff hcent, map_mul, hρy]
    exact hσ2
  obtain ⟨b₁, b₂, u₀, h⟩ := exists_outside_plane hU8 hcent hfull hyy hyU
  obtain ⟨c₁, hc₁, c₂, hc₂, hτ₁, hτ₂, hcc⟩ := h.exists_commuting_lifts
  have hl : PlaneLifts (U ⊓ Subgroup.centralizer {y}) b₁ b₂ u₀ c₁ c₂ := ⟨hc₁, hc₂, hτ₁, hτ₂, hcc⟩
  have hsq : ∀ d ∈ planeD (U ⊓ Subgroup.centralizer {y}) c₁ c₂, d * d = planeTau u₀ d := by
    rcases h.sq_dichotomy hl with hel | hsq
    · exact absurd (h.exists_complement_of_elementary hl hel) hnosplit
    · exact hsq
  have hu₀C := h.U_le_centralizer h.u₀_mem
  have hxC : c₁ * u₀ ∈ Subgroup.centralizer
      ((U ⊓ Subgroup.centralizer {y} : Subgroup Y) : Set Y) := Subgroup.mul_mem _ hc₁ hu₀C
  have hxD : c₁ * u₀ ∉ planeD (U ⊓ Subgroup.centralizer {y}) c₁ c₂ := by
    intro hD
    apply h.u₀_not_mem_planeD hl
    have : u₀ = c₁⁻¹ * (c₁ * u₀) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (PlaneHyp.c₁_mem_planeD hl)) hD
  refine ⟨c₁ * u₀, h.outside_mul_self hl hsq hxC hxD, fun hxU => ?_⟩
  have hc₁U : c₁ ∈ U := by
    have : c₁ = (c₁ * u₀) * u₀⁻¹ := by group
    rw [this]
    exact U.mul_mem hxU (U.inv_mem h.u₀_mem)
  apply h.b₁_ne_one
  rw [← hτ₁]
  exact h.planeTau_of_mem_U hc₁U

theorem outside_involutions_conj [Finite Y] (hU8 : Nat.card U = 8)
    (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    (hnosplit : ¬ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤)
    {x y : Y} (hx2 : x * x = 1) (hxU : x ∉ U) (hy2 : y * y = 1) (hyU : y ∉ U) :
    IsConj x y := by
  classical
  let ρ : Y →* MulAut U := MulAut.conjNormal
  have hρ : ∀ (g : Y) (z : U), ((ρ g z : U) : Y) = g * z * g⁻¹ := fun g z =>
    MulAut.conjNormal_apply g z
  have hinvol : ∀ g : Y, g * g = 1 → g ∉ U → ρ g ≠ 1 ∧ ρ g * ρ g = 1 := by
    intro g hg2 hgU
    refine ⟨fun h1 => hgU ((conjNormal_eq_one_iff hcent g).mp h1), ?_⟩
    rw [← map_mul, hg2, map_one]
  obtain ⟨hx1, hx2'⟩ := hinvol x hx2 hxU
  obtain ⟨hy1, hy2'⟩ := hinvol y hy2 hyU
  obtain ⟨e, he, ha0, ha1, ha2⟩ := exists_transvection_basis hU8 hx1 hx2'
  obtain ⟨e', he', hb0, hb1, hb2⟩ := exists_transvection_basis hU8 hy1 hy2'
  let σ := basisAut he he' hU8
  have hσe : ∀ i, σ (e i) = e' i := basisAut_apply he he' hU8
  have hσinv : ∀ i, σ⁻¹ (e' i) = e i := fun i => by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq, hσe]
  have hconj : σ * ρ x * σ⁻¹ = ρ y := by
    refine mulAut_ext_of_independent he' hU8 fun i => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hσinv]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [ha0, hσe, hb0]
    · simp only [Fin.mk_one, Fin.isValue]
      rw [ha1, map_mul, hσe, hσe, hb1]
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [ha2, hσe, hb2]
  obtain ⟨g, hg⟩ := hfull σ
  have hρg : ρ g = σ := MulEquiv.ext fun z => Subtype.ext ((hρ g z).trans (hg z).symm)
  have hρx' : ρ (g * x * g⁻¹) = ρ y := by
    rw [map_mul, map_mul, map_inv, hρg, hconj]
  obtain ⟨-, -, hclass⟩ := outside_involution_centralizer hU8 hcent hfull hnosplit hy2 hyU
  have hx'C : g * x * g⁻¹ ∈ Subgroup.centralizer
      ((U ⊓ Subgroup.centralizer {y} : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨hbU, hby⟩ := Subgroup.mem_inf.mp hb
    have hyb : ρ y ⟨b, hbU⟩ = ⟨b, hbU⟩ := by
      apply Subtype.ext
      rw [hρ, ← (Subgroup.mem_centralizer_singleton_iff.mp hby), mul_inv_cancel_right]
    have hxb := congrArg Subtype.val (hρx' ▸ hyb : ρ (g * x * g⁻¹) ⟨b, hbU⟩ = ⟨b, hbU⟩)
    rw [hρ] at hxb
    calc b * (g * x * g⁻¹) = (g * x * g⁻¹) * b * (g * x * g⁻¹)⁻¹ * (g * x * g⁻¹) := by
          rw [hxb]
      _ = (g * x * g⁻¹) * b := by group
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx2]; group
  have hx'U : g * x * g⁻¹ ∉ U := by
    intro h1
    apply hxU
    have := PlaneHyp.conj_mem_U (U := U) (y := g⁻¹) h1
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  obtain ⟨n, hn⟩ := hclass _ hx'C hx'2 hx'U
  refine isConj_iff.mpr ⟨n⁻¹ * g, ?_⟩
  calc n⁻¹ * g * x * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * x * g⁻¹) * n := by group
    _ = y := by rw [← hn]; group

end Nonsplit

theorem nonsplit_eight_linear_three_extension_involutions_and_four_centralizers
    [Finite Y] {U : Subgroup Y} [U.Normal] [IsElementaryAbelian 2 U]
    (hU8 : Nat.card U = 8) (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    (hnosplit : ¬ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤) :
    (∀ x ∈ U, x ≠ 1 → orderOf x = 2) ∧
    (∀ x ∈ U, ∀ y ∈ U, x ≠ 1 → y ≠ 1 → IsConj x y) ∧
    (∀ x y : Y, orderOf x = 2 → x ∉ U → orderOf y = 2 → y ∉ U → IsConj x y) ∧
    (∀ x ∈ U, ∀ y : Y, y ∉ U → ¬ IsConj x y) ∧
    Nat.card {x : Y // x ∈ U ∧ x ≠ 1} = 7 ∧
    Nat.card {x : Y // orderOf x = 2 ∧ x ∉ U} = 84 ∧
    (∀ x ∈ U, x ≠ 1 → Nat.card (Subgroup.centralizer {x}) = 192) ∧
    (∀ x : Y, orderOf x = 2 → x ∉ U → Nat.card (Subgroup.centralizer {x}) = 16) ∧
    ∀ x : Y, orderOf x = 2 → x ∉ U → ∃ y ∈ Subgroup.centralizer {x}, orderOf y = 4 := by
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq_of : ∀ x : Y, orderOf x = 2 → x * x = 1 := fun x hx => by
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hU2 : ∀ x ∈ U, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact mul_self_eq_one_of_mem hx) hx1
  have hUconj : ∀ x ∈ U, ∀ y ∈ U, x ≠ 1 → y ≠ 1 → ∃ g : Y, g * x * g⁻¹ = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨e, he, he0⟩ := exists_independent_with_first hU8 (x0 := ⟨x, hx⟩)
      (fun h1 => hx1 (congrArg Subtype.val h1))
    obtain ⟨e', he', he'0⟩ := exists_independent_with_first hU8 (x0 := ⟨y, hy⟩)
      (fun h1 => hy1 (congrArg Subtype.val h1))
    obtain ⟨g, hg⟩ := hfull (basisAut he he' hU8)
    refine ⟨g, ?_⟩
    have := hg (e 0)
    rw [basisAut_apply, he0, he'0] at this
    exact this.symm
  obtain ⟨x₀, hx₀2, hx₀U⟩ := exists_outside_involution hU8 hcent hfull hnosplit
  have hcardY : Nat.card Y = 1344 := by
    obtain ⟨b₁, b₂, u₀, h⟩ := exists_outside_plane hU8 hcent hfull
      (by rw [hx₀2]; exact U.one_mem) hx₀U
    exact h.card_Y
  have hconjU : ∀ g x : Y, x ∈ U → g * x * g⁻¹ ∈ U := fun g x hx => PlaneHyp.conj_mem_U hx
  have hnofuse : ∀ x ∈ U, ∀ y : Y, y ∉ U → ¬ IsConj x y := by
    intro x hx y hyU hxy
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    exact hyU (hc ▸ hconjU c x hx)
  have hUset : ({y | ∃ h ∈ (⊤ : Subgroup Y), h * (1 : Y) * h⁻¹ = y} : Set Y) = {1} := by
    ext y; simp [eq_comm]
  have hUclass : ∀ x ∈ U, x ≠ 1 →
      ({y | ∃ h ∈ (⊤ : Subgroup Y), h * x * h⁻¹ = y} : Set Y) = {y | y ∈ U ∧ y ≠ 1} := by
    intro x hx hx1
    ext y
    simp only [Set.mem_ofPred_eq, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨hconjU h x hx, fun h1 => hx1 ?_⟩
      calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    · rintro ⟨hy, hy1⟩
      exact hUconj x hx y hy hx1 hy1
  have h7 : ({y | y ∈ U ∧ y ≠ 1} : Set Y).ncard = 7 := by
    have heq : ({y | y ∈ U ∧ y ≠ 1} : Set Y) = (U : Set Y) \ {1} := by
      ext y; simp
    rw [heq, Set.ncard_sdiff_singleton_of_mem (U.one_mem), ← Nat.card_coe_set_eq]
    change Nat.card U - 1 = 7
    rw [hU8]
  have hout : ∀ x : Y, orderOf x = 2 → x ∉ U →
      ({y | ∃ h ∈ (⊤ : Subgroup Y), h * x * h⁻¹ = y} : Set Y) = {y | orderOf y = 2 ∧ y ∉ U} := by
    intro x hx hxU
    ext y
    simp only [Set.mem_ofPred_eq, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨?_, fun h1 => hxU ?_⟩
      · have hord := (MulAut.conj h).orderOf_eq x
        rw [MulAut.conj_apply] at hord
        rw [hord]
        exact hx
      · have := hconjU h⁻¹ _ h1
        rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this
    · rintro ⟨hy, hyU⟩
      exact isConj_iff.mp (outside_involutions_conj hU8 hcent hfull hnosplit (hsq_of x hx) hxU
        (hsq_of y hy) hyU)
  have hx₀ord : orderOf x₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx₀2)
    (fun h1 => hx₀U (h1 ▸ U.one_mem))
  obtain ⟨hcard₀, -, -⟩ := outside_involution_centralizer hU8 hcent hfull hnosplit hx₀2 hx₀U
  refine ⟨hU2, fun x hx y hy hx1 hy1 => isConj_iff.mpr (hUconj x hx y hy hx1 hy1),
    fun x y hx hxU hy hyU => outside_involutions_conj hU8 hcent hfull hnosplit (hsq_of x hx) hxU
      (hsq_of y hy) hyU, hnofuse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h7]
    exact Nat.card_coe_set_eq _
  · have horb := ncard_subgroup_conj_mul_card_inf_centralizer ⊤ x₀
    rw [hout x₀ hx₀ord hx₀U, top_inf_eq, hcard₀, Subgroup.card_top, hcardY] at horb
    have h84 : ({y | orderOf y = 2 ∧ y ∉ U} : Set Y).ncard = 84 := by omega
    rw [← h84]
    exact Nat.card_coe_set_eq _
  · intro x hx hx1
    have horb := ncard_subgroup_conj_mul_card_inf_centralizer ⊤ x
    rw [hUclass x hx hx1, h7, top_inf_eq, Subgroup.card_top, hcardY] at horb
    omega
  · intro x hx hxU
    exact (outside_involution_centralizer hU8 hcent hfull hnosplit (hsq_of x hx) hxU).1
  · intro x hx hxU
    exact (outside_involution_centralizer hU8 hcent hfull hnosplit (hsq_of x hx) hxU).2.1

theorem nonsplit_eight_linear_three_extension_natural_or_dual [Finite Y] {U : Subgroup Y}
    (π : Y →* GL (Fin 3) (ZMod 2)) (hπ : Function.Surjective π) (hker : π.ker = U)
    (ι : U ≃* Multiplicative (Fin 3 → ZMod 2))
    (hact : (∀ (y : Y) (u v : U), (v : Y) = y * u * y⁻¹ →
        (ι v).toAdd = Matrix.mulVec (π y : Matrix (Fin 3) (Fin 3) (ZMod 2)) (ι u).toAdd) ∨
      (∀ (y : Y) (u v : U), (v : Y) = y * u * y⁻¹ →
        (ι v).toAdd =
          Matrix.mulVec
            (Matrix.transpose (((π y)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
            (ι u).toAdd))
    (hnosplit : ¬ ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤) :
    (∀ x ∈ U, x ≠ 1 → orderOf x = 2) ∧
    (∀ x ∈ U, ∀ y ∈ U, x ≠ 1 → y ≠ 1 → IsConj x y) ∧
    (∀ x y : Y, orderOf x = 2 → x ∉ U → orderOf y = 2 → y ∉ U → IsConj x y) ∧
    (∀ x ∈ U, ∀ y : Y, y ∉ U → ¬ IsConj x y) ∧
    Nat.card {x : Y // x ∈ U ∧ x ≠ 1} = 7 ∧
    Nat.card {x : Y // orderOf x = 2 ∧ x ∉ U} = 84 ∧
    (∀ x ∈ U, x ≠ 1 → Nat.card (Subgroup.centralizer {x}) = 192) ∧
    (∀ x : Y, orderOf x = 2 → x ∉ U → Nat.card (Subgroup.centralizer {x}) = 16) ∧
    ∀ x : Y, orderOf x = 2 → x ∉ U → ∃ y ∈ Subgroup.centralizer {x}, orderOf y = 4 := by
  classical
  have _ : U.Normal := hker ▸ π.normal_ker
  have hcomm : ∀ a b : U, a * b = b * a := fun a b => ι.injective (by
    rw [map_mul, map_mul, mul_comm])
  have hsq : ∀ a : U, a ^ 2 = 1 := fun a => ι.injective (by
    rw [map_pow, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    change 2 • (ι a).toAdd i = 0
    rw [two_nsmul, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul])
  have _ : IsElementaryAbelian 2 U :=
    { is_comm := ⟨hcomm⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }
  have hU8 : Nat.card U = 8 := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hcent : Subgroup.centralizer (U : Set Y) = U := by
    apply le_antisymm
    · intro y hy
      rw [← hker, MonoidHom.mem_ker]
      have hyfix : ∀ u : U, (u : Y) = y * u * y⁻¹ := fun u => by
        rw [← (Subgroup.mem_centralizer_iff.mp hy) u u.2, mul_inv_cancel_right]
      have hmat : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
          (∀ v, Matrix.mulVec M v = v) → M = 1 := by
        intro M hM
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro v
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hM, Matrix.one_mulVec]
      have hall : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
          (∀ u : U, (ι u).toAdd = Matrix.mulVec M (ι u).toAdd) → M = 1 := by
        intro M hM
        apply hmat
        intro v
        obtain ⟨u, hu⟩ := ι.surjective (Multiplicative.ofAdd v)
        have := hM u
        rw [hu] at this
        exact this.symm
      rcases hact with hnat | hdual
      · apply Units.ext
        exact hall _ fun u => hnat y u u (hyfix u)
      · have h1 := hall _ fun u => hdual y u u (hyfix u)
        have h2 : (((π y)⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
          have := congrArg Matrix.transpose h1
          rwa [Matrix.transpose_transpose, Matrix.transpose_one] at this
        have h3 : (π y)⁻¹ = 1 := Units.ext h2
        rw [← inv_inj, h3, inv_one]
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (hcomm ⟨w, hw⟩ ⟨u, hu⟩)
  have hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹ := by
    let ρ : Y →* MulAut U := MulAut.conjNormal
    have hρker : ρ.ker = U := by
      ext g
      rw [MonoidHom.mem_ker]
      exact conjNormal_eq_one_iff hcent g
    have hGL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
      rw [Matrix.card_GL_field, ZMod.card]
      simp [Fin.prod_univ_succ]
    have hrange : Nat.card ρ.range = 168 := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq (hρker.trans hker.symm)).toEquiv,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hGL]
    have : Finite (MulAut U) := Finite.of_injective (fun σ : MulAut U => (σ : U → U))
      (fun σ τ h => MulEquiv.ext (congrFun h))
    have htop := Subgroup.eq_top_of_card_eq ρ.range (by rw [hrange, card_mulAut_eq_168 hU8])
    intro σ
    obtain ⟨y, hy⟩ := MonoidHom.range_eq_top.mp htop σ
    refine ⟨y, fun x => ?_⟩
    rw [← hy]
    exact MulAut.conjNormal_apply y x
  exact nonsplit_eight_linear_three_extension_involutions_and_four_centralizers hU8 hcent hfull
    hnosplit

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
