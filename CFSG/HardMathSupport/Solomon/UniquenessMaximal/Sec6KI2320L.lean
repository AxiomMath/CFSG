module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320F21

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34
open scoped commutatorElement

open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine (rSL coe_rSL)

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut

variable {k : Type} [Field k]

theorem congr_apply_eq {G : Type*} [Group G] (φ : MulAut G) (α : MulAut G) :
    MulAut.congr φ α = φ * α * φ⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

theorem yInn_apply (g : projectiveSL 3 k) : (yInn : MulAut (projectiveSL 3 k)) g = bP * g * bP⁻¹ := rfl

section

variable (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
include hk hu

theorem map_congr_yInn_eq (i : Fin 4) (hi : i = 0 ∨ i = 2) :
    (pglSylowMax u i).map (MulAut.congr (yInn : MulAut (projectiveSL 3 k))).toMonoidHom =
      pglSylowMax u i := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  obtain ⟨hx, hy, -, hzx, hzy, hz1⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change yInn ^ 3 = 1 at hy
  change Commute ⁅xDiag u, yInn⁆ (xDiag u) at hzx
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  set x := xDiag (k := k) u
  set y := (yInn : MulAut (projectiveSL 3 k))
  set z := ⁅x, y⁆ with hz
  have hz' : z = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
  have hyx : y * x * y⁻¹ = z⁻¹ * x := by
    rw [hz']; group
  have hM : Nat.card (pglSylowMax (k := k) u i) = 9 :=
    CFSG.RankThree.Asc83Table.ex27_card_rep hx hy hzx hzy hz1 i
  have hzM : z ∈ pglSylowMax (k := k) u i := Subgroup.subset_closure (Or.inl rfl)
  have hwM : CFSG.RankThree.Asc83Table.ex27Rep x y i ∈ pglSylowMax (k := k) u i :=
    Subgroup.subset_closure (Or.inr rfl)
  have hle : (pglSylowMax (k := k) u i).map
      (MulAut.congr (yInn : MulAut (projectiveSL 3 k))).toMonoidHom ≤ pglSylowMax u i := by
    rw [pglSylowMax, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, congr_apply_eq, SetLike.mem_coe]
    rcases ha with rfl | rfl
    · have : y * z * y⁻¹ = z := by
        rw [← hzy.eq]; group
      rw [this]
      exact hzM
    · rcases hi with rfl | rfl
      · show y * x * y⁻¹ ∈ _
        rw [hyx]
        exact mul_mem (inv_mem hzM) hwM
      · show y * (x * y) * y⁻¹ ∈ _
        have : y * (x * y) * y⁻¹ = z⁻¹ * (x * y) :=
          calc y * (x * y) * y⁻¹ = y * x := by group
            _ = (y * x * y⁻¹) * y := by group
            _ = (z⁻¹ * x) * y := by rw [hyx]
            _ = z⁻¹ * (x * y) := by group
        rw [this]
        exact mul_mem (inv_mem hzM) hwM
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.congr (yInn : MulAut (projectiveSL 3 k))).injective]

end

theorem Mm_pow_three (ω : k) : Mm ω ^ 3 = ω • (1 : Matrix (Fin 3) (Fin 3) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Mm, Matrix.mul_apply, Fin.sum_univ_three]

theorem conjAut_Bgl_pow_three (u : kˣ) :
    (conjAut' 3 k (Bgl u)) ^ 3 = 1 := by
  rw [← map_pow]
  ext p
  obtain ⟨g, rfl⟩ := proj_surjective 3 k p
  have : conjAut' 3 k (Bgl u ^ 3) (proj 3 k g) = proj 3 k g := by
    refine conjAut_proj_eq_of_comm _ g ?_
    rw [Units.val_pow_eq_pow_val, coe_Bgl, Mm_pow_three, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  simpa using this

theorem yInn_proj (s : SpecialLinearGroup (Fin 3) k) :
    (yInn : MulAut (projectiveSL 3 k)) (proj 3 k s) = proj 3 k (rSL * s * rSL⁻¹) := by
  rw [yInn_apply]
  simp [bP, map_mul, map_inv]

theorem top_le_of_x12 (W : Subgroup (projectiveSL 3 k))
    (hr : ∀ w ∈ W, (yInn : MulAut (projectiveSL 3 k)) w ∈ W) (h12 : ∀ c, proj 3 k (x12 c) ∈ W) :
    ⊤ ≤ W := by
  have hH : W.comap (proj 3 k) = ⊤ := by
    refine eq_top_of_x12 _ (fun h hh => ?_) h12
    have := hr _ hh
    rwa [yInn_proj] at this
  intro y _
  obtain ⟨g, rfl⟩ := proj_surjective 3 k y
  have : g ∈ W.comap (proj 3 k) := by rw [hH]; trivial
  exact this

theorem top_le_of_x01 (W : Subgroup (projectiveSL 3 k))
    (hr : ∀ w ∈ W, (yInn : MulAut (projectiveSL 3 k)) w ∈ W) (h01 : ∀ c, proj 3 k (x01 c) ∈ W) :
    ⊤ ≤ W := by
  have hH : W.comap (proj 3 k) = ⊤ := by
    refine eq_top_of_x01 _ (fun h hh => ?_) h01
    have := hr _ hh
    rwa [yInn_proj] at this
  intro y _
  obtain ⟨g, rfl⟩ := proj_surjective 3 k y
  have : g ∈ W.comap (proj 3 k) := by rw [hH]; trivial
  exact this

theorem goodGamma_stable (A : Subgroup (MulAut (projectiveSL 3 k)))
    (hA : A.map (MulAut.congr (yInn : MulAut (projectiveSL 3 k))).toMonoidHom = A) :
    ∀ w ∈ goodGamma A, (yInn : MulAut (projectiveSL 3 k)) w ∈ goodGamma A := by
  intro w hw
  have := map_goodGamma_le (yInn : MulAut (projectiveSL 3 k)) A
  rw [hA] at this
  exact this ⟨w, hw, rfl⟩

theorem xDiag_mem_M0 {u : kˣ} : xDiag (k := k) u ∈ pglSylowMax u 0 :=
  Subgroup.subset_closure (Or.inr rfl)

theorem xDiag_mul_yInn_mem_M2 {u : kˣ} : xDiag (k := k) u * yInn ∈ pglSylowMax u 2 :=
  Subgroup.subset_closure (Or.inr rfl)

section

variable (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1)
include hk hu

theorem card_pglSylowMax (i : Fin 4) : Nat.card (pglSylowMax (k := k) u i) = 9 := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  obtain ⟨hx, hy, -, hzx, hzy, hz1⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change yInn ^ 3 = 1 at hy
  change Commute ⁅xDiag u, yInn⁆ (xDiag u) at hzx
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  exact CFSG.RankThree.Asc83Table.ex27_card_rep hx hy hzx hzy hz1 i

theorem orderOf_xDiag : orderOf (xDiag (k := k) u) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hx, -, -, -, -, hz1⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  have hx1 : xDiag (k := k) u ≠ 1 := fun h => hz1 (by rw [h]; simp)
  exact orderOf_eq_prime hx hx1

theorem orderOf_xDiag_mul_yInn : orderOf (xDiag (k := k) u * yInn) = 3 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, hz1⟩ := sylowGen_props hk hu
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  have hxy3 : (xDiag (k := k) u * yInn) ^ 3 = 1 := by
    rw [xDiag_mul_yInn]
    exact conjAut_Bgl_pow_three u
  have hxy1 : xDiag (k := k) u * yInn ≠ 1 := by
    intro h
    apply hz1
    have hy' : (yInn : MulAut (projectiveSL 3 k)) = (xDiag u)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hy']
    group
  exact orderOf_eq_prime hxy3 hxy1

theorem top_le_goodGamma_M0 : ⊤ ≤ goodGamma (pglSylowMax u 0) := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hx, hy, -, hzx, hzy, hz1⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change yInn ^ 3 = 1 at hy
  change Commute ⁅xDiag u, yInn⁆ (xDiag u) at hzx
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  have hx1 : xDiag (k := k) u ≠ 1 := fun h => hz1 (by rw [h]; simp)
  have hS : Subgroup.zpowers (xDiag (k := k) u) ≤ pglSylowMax u 0 := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hSc : Nat.card (Subgroup.zpowers (xDiag (k := k) u)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx hx1
  have hM : Nat.card (pglSylowMax (k := k) u 0) = 9 :=
    CFSG.RankThree.Asc83Table.ex27_card_rep hx hy hzx hzy hz1 0
  have hL : a5Sub ≤ goodGamma (pglSylowMax (k := k) u 0) :=
    le_goodGamma hS (by rw [hM, hSc]) (Or.inr (a5_piece hk hu))
  exact top_le_of_x12 _ (goodGamma_stable _ (map_congr_yInn_eq hk hu 0 (Or.inl rfl)))
    (fun c => hL (proj_x12_mem_a5Sub c))

theorem top_le_goodGamma_M2 : ⊤ ≤ goodGamma (pglSylowMax u 2) := by
  have hc2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hx, hy, -, hzx, hzy, hz1⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change yInn ^ 3 = 1 at hy
  change Commute ⁅xDiag u, yInn⁆ (xDiag u) at hzx
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  have hxy3 : (xDiag (k := k) u * yInn) ^ 3 = 1 := by
    rw [xDiag_mul_yInn]
    exact conjAut_Bgl_pow_three u
  have hxy1 : xDiag (k := k) u * yInn ≠ 1 := by
    intro h
    apply hz1
    have hy' : (yInn : MulAut (projectiveSL 3 k)) = (xDiag u)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hy']
    group
  have hS : Subgroup.zpowers (xDiag (k := k) u * yInn) ≤ pglSylowMax u 2 := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hSc : Nat.card (Subgroup.zpowers (xDiag (k := k) u * yInn)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxy3 hxy1
  have hM : Nat.card (pglSylowMax (k := k) u 2) = 9 :=
    CFSG.RankThree.Asc83Table.ex27_card_rep hx hy hzx hzy hz1 2
  set hω : (u : k) * u + u + 1 = 0 := val_mul_self_add hk hu with hωdef
  have hN : Subgroup.zpowers (proj 3 k (tau0 hω)) ≤ goodGamma (pglSylowMax (k := k) u 2) :=
    le_goodGamma hS (by rw [hM, hSc]) (Or.inl (tau_piece hk hu))
  have hstab := goodGamma_stable _ (map_congr_yInn_eq hk hu 2 (Or.inr rfl))
  have h0 : proj 3 k (tau0 hω) ∈ goodGamma (pglSylowMax (k := k) u 2) :=
    hN (Subgroup.mem_zpowers _)
  have h1 : proj 3 k (tau1 hω) ∈ goodGamma (pglSylowMax (k := k) u 2) := by
    have := hstab _ h0
    rwa [yInn_proj] at this
  have h2 : proj 3 k (tau2 hω) ∈ goodGamma (pglSylowMax (k := k) u 2) := by
    have := hstab _ h1
    rwa [yInn_proj] at this
  have hall : ∀ a : k, a = 0 ∨ a = 1 ∨ a = (u : k) ∨ a = (u : k) * u := by
    intro a
    rcases LinearFieldFour.eq_zero_or_eq_one_or hk u.ne_zero (val_ne_one hu) a with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, LinearFieldFour.omega_mul_omega hk u.ne_zero (val_ne_one hu)])))
  refine top_le_of_x01 _ hstab (fun c => ?_)
  have := x01_mem_of_tau hω hall ((goodGamma (pglSylowMax (k := k) u 2)).comap (proj 3 k)) h0 h1 h2 c
  exact this

end

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
