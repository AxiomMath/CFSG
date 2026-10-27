module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE6ThreeLines

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

@[expose] def E6RootLineCommuteTwo : Prop :=
  ∀ (L : Type) [Field L] [CharP L 2] (α γ : Fin Tag.E6.rank → ℤ), IsRoot Tag.E6 α →
    IsRoot Tag.E6 γ → iform α γ = -1 → ∀ g : ModGL Tag.E6 L,
      (∀ β ∈ ({α, -α, γ, -γ} : Set (Fin Tag.E6.rank → ℤ)),
        Commute g (pinnedX Tag.E6 L β 1)) →
      ∀ β ∈ ({α, -α, γ, -γ} : Set (Fin Tag.E6.rank → ℤ)), ∀ t : L,
        Commute g (pinnedX Tag.E6 L β t)

section Frames

variable {L : Type} [Field L]

theorem e6ThreeLine_commute_conj {G : Type*} [Group G] {h a b : G}
    (hc : Commute a (h * b * h⁻¹)) : Commute (h⁻¹ * a * h) b := by
  have e := hc.eq
  show h⁻¹ * a * h * b = b * (h⁻¹ * a * h)
  calc h⁻¹ * a * h * b = h⁻¹ * (a * (h * b * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * b * h⁻¹) * a) * h := by rw [e]
    _ = b * (h⁻¹ * a * h) := by group

theorem e6ThreeLine_conj_commute {G : Type*} [Group G] {h a b : G} (hc : Commute a b) :
    Commute (h * a * h⁻¹) (h * b * h⁻¹) := by
  have e := hc.eq
  show h * a * h⁻¹ * (h * b * h⁻¹) = h * b * h⁻¹ * (h * a * h⁻¹)
  calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
    _ = h * (b * a) * h⁻¹ := by rw [e]
    _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group

theorem e6ThreeLine_diag_mul_transvection (d : Fin 3 → L) (hd : ∀ k, d k ≠ 0)
    (D : SL(3, L)) (hD : (D : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal d)
    {i j : Fin 3} (hij : i ≠ j) (t : L) :
    D * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij (d i * t * (d j)⁻¹) * D := by
  ext k l
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection, hD,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hkl : k = l
  · subst hkl
    have h1 : ¬ (i = k ∧ j = k) := fun h => hij (h.1.trans h.2.symm)
    simp only [ite_true, h1, ite_false, add_zero, mul_one, one_mul]
  · by_cases h : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h
      simp only [hkl, ite_false, and_self, ite_true, zero_add]
      field_simp [hd j]
    · simp only [hkl, ite_false, h, zero_add, mul_zero, zero_mul]

theorem e6ThreeLine_units_two (h2 : (2 : L) = 0) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (φ : SL2 L →* ModGL Tag.E6 L) (a b : Lˣ)
    (hu : ∀ t, φ (uSL t) = pinnedX Tag.E6 L β ((a : L) * t))
    (hv : ∀ t, φ (vSL t) = pinnedX Tag.E6 L (-β) ((b : L) * t)) : (a : L) * b = 1 := by
  obtain ⟨s, hs⟩ := exists_comp_conjSL_eq_rootSL2 hβ φ a b hu hv
  have hneg : ∀ x : L, -x = x := fun x => by linear_combination (-x) * h2
  have huβ : ∀ t, rootSL2 Tag.E6 L β (uSL t) = pinnedX Tag.E6 L β t := fun t => by
    rw [rootSL2_uSL_eq]
    rcases pinnedSign_eq Tag.E6 β with h | h <;> rw [h]
    · rw [one_zsmul]
    · rw [neg_one_zsmul, hneg]
  obtain ⟨η, hη, hvη⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  have hη1 : η = 1 := by
    have h3 : (η - 1) ^ 2 = 0 := by linear_combination hη - η * h2 + h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h3)
  have hvβ : ∀ t, rootSL2 Tag.E6 L β (vSL t) = pinnedX Tag.E6 L (-β) t := fun t => by
    rw [hvη, hη1, one_mul]
  have e1 := DFunLike.congr_fun hs (uSL 1)
  have e2 := DFunLike.congr_fun hs (vSL 1)
  simp only [MonoidHom.comp_apply] at e1 e2
  have c1 : CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s)
      (uSL (1 : L)) = uSL ((s : L) * 1) := CFSG.RankThree.Classical.conjSL_sl2Upper s 1
  have c2 : CFSG.RankThree.Classical.conjSL (CFSG.RankThree.Classical.diagUnitOne s)
      (vSL (1 : L)) = vSL ((((s⁻¹ : Lˣ) : L)) * 1) :=
    CFSG.RankThree.Classical.conjSL_sl2Lower s 1
  rw [c1, hu, huβ] at e1
  rw [c2, hv, hvβ] at e2
  have e1' : (a : L) * s = 1 := by simpa using pinnedX_injective Tag.E6 L β e1
  have e2' : (b : L) * ((s⁻¹ : Lˣ) : L) = 1 := by simpa using pinnedX_injective Tag.E6 L (-β) e2
  calc (a : L) * b = ((a : L) * s) * ((b : L) * ((s⁻¹ : Lˣ) : L)) := by
        rw [Units.val_inv_eq_inv_val]
        field_simp
    _ = 1 := by rw [e1', e2', one_mul]

theorem e6ThreeLine_commute_range_two (hc : E6RootLineCommuteTwo) [IsAlgClosed L] [CharP L 2]
    {k : Type} [Field k] [Algebra k L] {ρ : SL(3, L) →* ModGL Tag.E6 L}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsSLFrame ρ σ) {H : SL(3, L)}
    {g : ModGL Tag.E6 L}
    (hg : ∀ Y : SL(3, k), Commute g
      (ρ (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹))) :
    ∀ x ∈ ρ.range, Commute g x := by
  classical
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  obtain ⟨e01, he01⟩ := hfr.transv 0 1 h01
  obtain ⟨e10, he10⟩ := hfr.transv 1 0 h10
  obtain ⟨e12, he12⟩ := hfr.transv 1 2 h12
  obtain ⟨e21, he21⟩ := hfr.transv 2 1 h21
  have hb0 : (e01 : L) * e10 = 1 :=
    e6ThreeLine_units_two h2 (hfr.isRoot 0 1 h01) (ρ.comp (blockSL2 L 2 0)) e01 e10
      (fun t => by
        rw [MonoidHom.comp_apply, blockSL2_uSL_eq]
        exact he01 t)
      (fun t => by
        rw [MonoidHom.comp_apply, blockSL2_vSL_eq, ← hfr.neg 0 1]
        exact he10 t)
  have hb1 : (e12 : L) * e21 = 1 :=
    e6ThreeLine_units_two h2 (hfr.isRoot 1 2 h12) (ρ.comp (blockSL2 L 2 1)) e12 e21
      (fun t => by
        rw [MonoidHom.comp_apply, blockSL2_uSL_eq]
        exact he12 t)
      (fun t => by
        rw [MonoidHom.comp_apply, blockSL2_vSL_eq, ← hfr.neg 1 2]
        exact he21 t)
  set g' : ModGL Tag.E6 L := (ρ H)⁻¹ * g * ρ H with hg'def
  have hg' : ∀ Y : SL(3, k), Commute g' (ρ (Matrix.SpecialLinearGroup.map (algebraMap k L) Y)) :=
    fun Y => e6ThreeLine_commute_conj (by
      have := hg Y
      rwa [map_mul, map_mul, map_inv] at this)
  have hgT : ∀ (i j : Fin 3) (hij : i ≠ j),
      Commute g' (ρ (Matrix.SpecialLinearGroup.transvection hij 1)) := by
    intro i j hij
    have := hg' (Matrix.SpecialLinearGroup.transvection hij 1)
    rwa [splitLine_map_transvection, map_one] at this
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq ((e01 : L) * ((e12 : L))⁻¹)
    (by norm_num : 0 < 3)
  have hμ0 : μ ≠ 0 := by
    have hne : ((e01 : L) * ((e12 : L))⁻¹) ≠ 0 := mul_ne_zero e01.ne_zero (inv_ne_zero e12.ne_zero)
    intro h0
    rw [h0, zero_pow (by norm_num)] at hμ
    exact hne hμ.symm
  set d : Fin 3 → L := ![μ * ((e01 : L))⁻¹, μ, μ * e12] with hd
  have hdv0 : d 0 = μ * ((e01 : L))⁻¹ := rfl
  have hdv1 : d 1 = μ := rfl
  have hdv2 : d 2 = μ * e12 := rfl
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i
    fin_cases i
    · exact mul_ne_zero hμ0 (inv_ne_zero e01.ne_zero)
    · exact hμ0
    · exact mul_ne_zero hμ0 e12.ne_zero
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three, hdv0, hdv1, hdv2]
    have : μ ^ 3 * ((e01 : L))⁻¹ * e12 = 1 := by
      rw [hμ]
      field_simp
    linear_combination this
  set D : SL(3, L) := ⟨Matrix.diagonal d, hdet⟩ with hDdef
  have hDT := fun {i j : Fin 3} (hij : i ≠ j) (t : L) =>
    e6ThreeLine_diag_mul_transvection d hd0 D rfl hij t
  have hconj : ∀ {i j : Fin 3} (hij : i ≠ j) (t : L),
      D * Matrix.SpecialLinearGroup.transvection hij t * D⁻¹ =
        Matrix.SpecialLinearGroup.transvection hij (d i * t * (d j)⁻¹) := by
    intro i j hij t
    rw [hDT hij t, mul_inv_cancel_right]
  have hd01 : d 0 * 1 * (d 1)⁻¹ = ((e01 : L))⁻¹ := by
    rw [hdv0, hdv1]
    field_simp
  have hd10 : d 1 * 1 * (d 0)⁻¹ = e01 := by
    rw [hdv0, hdv1]
    field_simp
  have hd12 : d 1 * 1 * (d 2)⁻¹ = ((e12 : L))⁻¹ := by
    rw [hdv1, hdv2]
    field_simp
  have hd21 : d 2 * 1 * (d 1)⁻¹ = e12 := by
    rw [hdv1, hdv2]
    field_simp
  set g'' : ModGL Tag.E6 L := ρ D * g' * (ρ D)⁻¹ with hg''def
  have hconjT : ∀ {i j : Fin 3} (hij : i ≠ j), Commute g''
      (ρ (Matrix.SpecialLinearGroup.transvection hij (d i * 1 * (d j)⁻¹))) := by
    intro i j hij
    rw [← hconj hij 1, map_mul, map_mul, map_inv]
    exact e6ThreeLine_conj_commute (hgT i j hij)
  have hx01 : Commute g'' (pinnedX Tag.E6 L (σ 0 1) 1) := by
    have := hconjT h01
    rwa [hd01, he01, mul_inv_cancel₀ e01.ne_zero] at this
  have hx10 : Commute g'' (pinnedX Tag.E6 L (-σ 0 1) 1) := by
    have := hconjT h10
    rwa [hd10, he10, hfr.neg 0 1, mul_comm, hb0] at this
  have hx12 : Commute g'' (pinnedX Tag.E6 L (σ 1 2) 1) := by
    have := hconjT h12
    rwa [hd12, he12, mul_inv_cancel₀ e12.ne_zero] at this
  have hx21 : Commute g'' (pinnedX Tag.E6 L (-σ 1 2) 1) := by
    have := hconjT h21
    rwa [hd21, he21, hfr.neg 1 2, mul_comm, hb1] at this
  have hr01 := hfr.isRoot 0 1 h01
  have hr12 := hfr.isRoot 1 2 h12
  have hiform : iform (σ 0 1) (σ 1 2) = -1 := by
    have hr02 := hfr.isRoot 0 2 (by decide)
    rw [← hfr.add 0 1 2] at hr02
    have e1 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
      (Or.inr (Or.inl rfl)) hr02
    have e2 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
      (Or.inr (Or.inl rfl)) hr01
    have e3 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
      (Or.inr (Or.inl rfl)) hr12
    rw [iform_add_left, iform_add_right, iform_add_right, iform_comm (σ 1 2) (σ 0 1)] at e1
    omega
  have hall := hc L (σ 0 1) (σ 1 2) hr01 hr12 hiform g'' (by
    rintro β (rfl | rfl | rfl | rfl)
    · exact hx01
    · exact hx10
    · exact hx12
    · exact hx21)
  have hblk : ∀ (i j : Fin 3) (hij : i ≠ j), (i, j) = (0, 1) ∨ (i, j) = (1, 0) ∨
      (i, j) = (1, 2) ∨ (i, j) = (2, 1) → ∀ t : L,
        Commute g'' (ρ (D * Matrix.SpecialLinearGroup.transvection hij t * D⁻¹)) := by
    intro i j hij hcase t
    rw [hconj hij t]
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · rw [he01]
      exact hall _ (Or.inl rfl) _
    · rw [he10, hfr.neg 0 1]
      exact hall _ (Or.inr (Or.inl rfl)) _
    · rw [he12]
      exact hall _ (Or.inr (Or.inr (Or.inl rfl))) _
    · rw [he21, hfr.neg 1 2]
      exact hall _ (Or.inr (Or.inr (Or.inr rfl))) _
  set Sg : Subgroup (SL(3, L)) := (Subgroup.centralizer {g''}).comap
    (ρ.comp (MulAut.conj D).toMonoidHom) with hSg
  have hmem : ∀ X, X ∈ Sg ↔ Commute g'' (ρ (D * X * D⁻¹)) := by
    intro X
    rw [hSg, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.symm, fun h => h.eq.symm⟩
  have hblock : ∀ c : Fin 2, (blockSL2 L 2 c).range ≤ Sg := by
    intro c
    have htop : Sg.comap (blockSL2 L 2 c) = ⊤ := by
      rw [eq_top_iff, ← sl2_closure_upper_lower (K := L), Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hmem]
        change Commute g'' (ρ (D * blockSL2 L 2 c (uSL t) * D⁻¹))
        rw [blockSL2_uSL_eq]
        fin_cases c
        · exact hblk 0 1 h01 (Or.inl rfl) t
        · exact hblk 1 2 h12 (Or.inr (Or.inr (Or.inl rfl))) t
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hmem]
        change Commute g'' (ρ (D * blockSL2 L 2 c (vSL t) * D⁻¹))
        rw [blockSL2_vSL_eq]
        fin_cases c
        · exact hblk 1 0 h10 (Or.inr (Or.inl rfl)) t
        · exact hblk 2 1 h21 (Or.inr (Or.inr (Or.inr rfl))) t
    rintro _ ⟨A, rfl⟩
    have : A ∈ Sg.comap (blockSL2 L 2 c) := by rw [htop]; exact Subgroup.mem_top A
    exact this
  have hSgtop : Sg = ⊤ := by
    rw [eq_top_iff, ← iSup_range_blockSL2 (K := L) 2]
    exact iSup_le hblock
  rintro _ ⟨X, rfl⟩
  have h1 : Commute g'' (ρ (D * (H⁻¹ * X * H) * D⁻¹)) := (hmem _).1 (hSgtop ▸ Subgroup.mem_top _)
  have h2' : Commute g' (ρ (H⁻¹ * X * H)) := by
    have := e6ThreeLine_commute_conj (h := ρ D) (a := g'') (by
      rwa [map_mul, map_mul, map_inv] at h1)
    rwa [hg''def, show (ρ D)⁻¹ * (ρ D * g' * (ρ D)⁻¹) * ρ D = g' by group] at this
  have h3 := e6ThreeLine_conj_commute (h := ρ H) h2'
  rw [hg'def, show ρ H * ((ρ H)⁻¹ * g * ρ H) * (ρ H)⁻¹ = g by group, map_mul, map_mul,
    map_inv, show ρ H * ((ρ H)⁻¹ * ρ X * ρ H) * (ρ H)⁻¹ = ρ X by group] at h3
  exact h3

end Frames

section Two

theorem e6LineCommuteAt_two (hc : E6RootLineCommuteTwo) {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) : E6LineCommuteAt K := by
  intro ρ σ hfr H g hg
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have h2K : (2 : K) = 0 := by
    let _ := Fintype.ofFinite K
    have := FiniteField.cast_card_eq_zero K
    rwa [← Nat.card_eq_fintype_card, hK2, Nat.cast_ofNat] at this
  have h2L : (2 : AlgebraicClosure K) = 0 := by
    rw [← map_ofNat (algebraMap K (AlgebraicClosure K)) 2, h2K, map_zero]
  have : CharP (AlgebraicClosure K) 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2L)
  exact e6ThreeLine_commute_range_two hc hfr hg

theorem innerPlaneBalanceAt_E6_three_of_commuteTwo (hcp : LangComponentPieces)
    (hc : E6RootLineCommuteTwo) : InnerPlaneBalanceAt .E6 3 := by
  intro q hv p hp hp7 _ hpq he
  refine innerPlaneBalance_E6_three_of_commute hcp q hv hp hp7 hpq he fun K _ _ hK => ?_
  by_cases h3 : 3 ≤ Nat.card K
  · exact e6LineCommuteAt_of_three_le h3
  · have := Finite.one_lt_card (α := K)
    exact e6LineCommuteAt_two hc (by omega)

end Two

end CFSG.HardMathSupport.Timmesfeld.CrossChar
