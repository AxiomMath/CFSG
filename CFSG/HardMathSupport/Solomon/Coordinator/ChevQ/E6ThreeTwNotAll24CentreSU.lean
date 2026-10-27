module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Equiv

variable {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}

theorem two_suN_exists_equiv_link {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hν : 3 ≤ ν) :
    ∃ F : Subfield L, Nat.card F = (ℓ ^ f) ^ 2 ∧
      ∃ e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup (stdUnitaryEquiv (ν := ν) σ),
        ∀ y, ((e y : fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) : SL(ν, L)) =
          statedSUToSL F ν (ℓ ^ f) y := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set Φ := stdUnitaryEquiv (ν := ν) σ with hΦ
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hσmap : ∀ M : Matrix (Fin ν) (Fin ν) L, M.map σ.toRingHom = M.map (· ^ ℓ ^ f) := by
    intro M
    ext i j
    simp [hσ]
  have hfix : ∀ X : SL(ν, L), X ∈ fixSubgroup Φ ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
    intro X
    rw [mem_fixSubgroup, hΦ, stdUnitaryEquiv_apply]
    have hdetX : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)).det := by
      rw [← hσmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
      exact isUnit_one
    constructor
    · intro h
      have hstd : stdUnitary σ.toRingHom X = X := h
      have h1 : (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ =
          (X : Matrix (Fin ν) (Fin ν) L) := by
        rw [← hσmap, ← coe_stdUnitary, hstd]
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := by
        have e1 : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
            (X : Matrix (Fin ν) (Fin ν) L) = ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
              (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ := by rw [h1]
        rw [e1, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdetX, Matrix.transpose_one]
      refine ⟨fun i j => ?_, X.2, hu⟩
      have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom X = invTransposeSL X := by
        have := congrArg invTransposeSL hstd
        rwa [stdUnitary, MonoidHom.comp_apply, invTransposeSL_invTransposeSL] at this
      have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.toRingHom X) = X := by
        rw [hmap, slMap_invTransposeSL, ← MonoidHom.comp_apply invTransposeSL, ← stdUnitary, hstd]
      have h3 := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L) i j) h2
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ] at h3
      rw [← pow_mul, ← sq] at h3
      exact h3
    · rintro ⟨-, -, hu'⟩
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := hu'
      apply Subtype.ext
      rw [coe_stdUnitary, hσmap]
      have : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹ =
          (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
        refine Matrix.inv_eq_left_inv ?_
        rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)),
          ← Matrix.transpose_mul, hu, Matrix.transpose_one]
      rw [this, Matrix.transpose_transpose]
  let Ψ : StatedSU ν (ℓ ^ f) F →* SL(ν, L) := statedSUToSL F ν (ℓ ^ f)
  have hΨmem : ∀ Y, Ψ Y ∈ fixSubgroup Φ := fun Y =>
    (hfix _).2 ((mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩)
  let e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (Ψ.codRestrict _ hΨmem)
    ⟨fun Y Z h => statedSUToSL_injective F ν (ℓ ^ f) (congrArg Subtype.val h), fun X => by
      obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) X).mpr
        ((hfix X).1 X.2)
      exact ⟨Y, Subtype.ext hY⟩⟩
  exact ⟨F, hFcard, e, fun y => rfl⟩


theorem coe_mem_center_SL_of_mem_center {F : Subfield L} {Q : ℕ} (σ : L ≃+* L)
    (hZ : Subgroup.center (StatedSU ν Q F) =
      (StatedScalars (Fin ν) F).subgroupOf (StatedSU ν Q F))
    (e : StatedSU ν Q F ≃* fixSubgroup (stdUnitaryEquiv (ν := ν) σ))
    (he : ∀ y, ((e y : fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) : SL(ν, L)) =
      statedSUToSL F ν Q y)
    {c : fixSubgroup (stdUnitaryEquiv (ν := ν) σ)}
    (hc : c ∈ Subgroup.center (fixSubgroup (stdUnitaryEquiv (ν := ν) σ))) :
    (c : SL(ν, L)) ∈ Subgroup.center SL(ν, L) := by
  have hy : e.symm c ∈ Subgroup.center (StatedSU ν Q F) := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hc (e y)
  rw [hZ] at hy
  obtain ⟨l, hl⟩ : ∃ l : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin ν) l =
      ((e.symm c : StatedSU ν Q F) : GL (Fin ν) F) := Subgroup.mem_subgroupOf.1 hy
  have hcy : (c : SL(ν, L)) = statedSUToSL F ν Q (e.symm c) := by
    rw [← he, MulEquiv.apply_symm_apply]
  have hmat : ((c : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      Matrix.scalar (Fin ν) ((l : F) : L) := by
    rw [hcy, coe_statedSUToSL, ← hl]
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨((l : F) : L), ?_, hmat.symm⟩
  have hdet := (c : SL(ν, L)).2
  rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
  simpa using hdet

end Equiv

theorem pow_card_eq_one_of_mem_center {K : Type} [Field K] {ν : ℕ} {A : SL(ν, K)}
    (hA : A ∈ Subgroup.center SL(ν, K)) : A ^ ν = 1 := by
  obtain ⟨l, hl, hlA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hlA, ← map_pow]
  have hl' : l ^ ν = 1 := by simpa using hl
  rw [hl', map_one]
  rfl

section Core


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem exists_center_conj_of_suN (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 4 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1) :
    ∃ z₀ : ModGL τ L, ∀ z ∈ Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i),
      ∃ A ∈ Subgroup.center SL(ν, L), A ^ ν = 1 ∧ (z : ModGL τ L) = z₀ * ψ A * z₀⁻¹ := by
  classical
  have hν3 : 3 ≤ ν := by omega
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2, z₀, hfz⟩ :=
    two_suN_exists_hom_conj S hT i hν3 hψ hΨ π hπ hr hchar he hq hs1
  rw [hs1, Nat.mul_one] at hσc
  have hνQ : (ν, r ^ e) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp at this
    omega
  obtain ⟨hfin, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr he σQ hσc hν3
  have hCperf : Group.IsPerfect
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC hνQ).1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨F, hFcard, eC, hlink⟩ := two_suN_exists_equiv_link hr he σQ hσc hν3
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hr.pos _) 2).ne')
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := ↥F) (p := r) (f := e) hFcard hν3 hνQ
  refine ⟨z₀, fun z hz => ?_⟩
  have hz' : z ∈ (Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup
      (stdUnitaryEquiv (ν := ν) σQ))).map g := by
    rw [map_center_of_surjective hCperf.commutator_eq_top g hgsurj hgker]
    exact hz
  obtain ⟨c, hc, rfl⟩ := hz'
  have hA := coe_mem_center_SL_of_mem_center σQ hZ eC hlink hc
  exact ⟨(c : SL(ν, L)), hA, pow_card_eq_one_of_mem_center hA, hfz c⟩

theorem not_three_dvd_card_center_of_pow {R : Type*} [Group R] [Finite R] {n : ℕ} (hn : ¬ 3 ∣ n)
    (h : ∀ z ∈ Subgroup.center R, z ^ n = 1) : ¬ 3 ∣ Nat.card (Subgroup.center R) := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center R)) 3 h3
  have hxn : (x : R) ^ n = 1 := h x x.2
  have : orderOf (x : R) ∣ n := orderOf_dvd_of_pow_eq_one hxn
  rw [Subgroup.orderOf_coe, hx] at this
  exact hn this

theorem not_three_dvd_center_of_suN (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : ν = 5 ∨ ν = 6)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1)
    (hψ6 : ν = 6 → ∀ A ∈ Subgroup.center SL(ν, L), A ^ 3 = 1 → ψ A = 1)
    [Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i)] :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i)) := by
  obtain ⟨z₀, hz₀⟩ := exists_center_conj_of_suN S hT i (by omega) hψ hΨ π hπ hr hchar he hq hs1
  rcases hν with rfl | rfl
  · refine not_three_dvd_card_center_of_pow (n := 5) (by norm_num) fun z hz => ?_
    obtain ⟨A, -, hA5, hzA⟩ := hz₀ z hz
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzA]
    change (z₀ * ψ A * z₀⁻¹) ^ 5 = 1
    rw [conj_pow, ← map_pow, hA5, map_one]
    group
  · refine not_three_dvd_card_center_of_pow (n := 2) (by norm_num) fun z hz => ?_
    obtain ⟨A, hAc, hA6, hzA⟩ := hz₀ z hz
    have hA2 : A ^ 2 ∈ Subgroup.center SL(6, L) := Subgroup.pow_mem _ hAc 2
    have h1 : ψ (A ^ 2) = 1 := hψ6 rfl _ hA2 (by rw [← pow_mul]; exact hA6)
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzA]
    change (z₀ * ψ A * z₀⁻¹) ^ 2 = 1
    rw [conj_pow, ← map_pow, h1]
    group

end Core


end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
