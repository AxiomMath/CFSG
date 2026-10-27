module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAPinHom

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

section Std

variable {L : Type} [Field L] {ν : ℕ}

theorem exists_subfield_card_sq [IsAlgClosed L] {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ]
    (hf : 1 ≤ f) :
    ∃ F : Subfield L, (∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c) ∧ Nat.card F = (ℓ ^ f) ^ 2 := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  refine ⟨F, fun c => by rw [hq2]; exact hF2 c, ?_⟩
  rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
  exact Nat.card_congr (Equiv.subtypeEquivRight hF2)

theorem stdUnitary_eq_self_iff {ℓ f : ℕ} (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (X : SL(ν, L)) :
    stdUnitary σ.toRingHom X = X ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
  have hσmap : ∀ M : Matrix (Fin ν) (Fin ν) L, M.map σ.toRingHom = M.map (· ^ ℓ ^ f) := by
    intro M
    ext i j
    simp [hσ]
  have hdetX : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)).det := by
    rw [← hσmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
    exact isUnit_one
  constructor
  · intro hstd
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

end Std

section Matrix

variable {L : Type} [Field L] [IsAlgClosed L]

theorem unitary_pin_conj {ν : ℕ} (hν : 3 ≤ ν) (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c)) :
    ∃ B : SL(ν, L), ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) (-(((β a b)⁻¹ : Lˣ) : L) * u) := by
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  refine ⟨B, fun a b hab u => ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
  have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
      (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
        ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
          ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
            (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
    intro Y
    simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
    permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  congr 2
  rw [hd a b hab]
  simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, inv_neg, inv_inv, neg_mul,
    neg_neg]
  have h0 : (d a : L) ≠ 0 := Units.ne_zero _
  have h0' : (d b : L) ≠ 0 := Units.ne_zero _
  field_simp

end Matrix

section Frame

variable {τ : Tag} {L : Type}
  [Field L]

theorem unitary_pin_cocycle {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (F : ModGL τ L →* ModGL τ L)
    {σQ : L ≃+* L} (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      F (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
          ((β a b : L) * σQ t))) :
    ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
  intro a b c hab hbc hac
  obtain ⟨ε, hε⟩ := hψ.transv (π c) (π a) (π.injective.ne hac).symm
  have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
  rw [mul_one] at hcomm
  have h1 := congrArg (fun X => F (ψ X)) hcomm
  simp only [map_commutatorElement] at h1
  rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
    ← map_commutatorElement ψ,
    commutator_transvection_rev (π.injective.ne hab).symm (π.injective.ne hbc).symm
      (π.injective.ne hac).symm, hε, hε] at h1
  have h2 := pinnedX_injective τ L _ h1
  have h0 : (ε : L) ≠ 0 := Units.ne_zero _
  apply Units.ext
  have h3 := mul_left_cancel₀ h0 h2
  rw [Units.val_neg, Units.val_mul]
  exact h3.symm

theorem unitary_pin_std {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} (F : ModGL τ L →* ModGL τ L)
    (σQ : L ≃+* L) (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      F (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
          ((β a b : L) * σQ t)))
    {B : SL(ν, L)}
    (hB : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) (-(((β a b)⁻¹ : Lˣ) : L) * u))
    (X : SL(ν, L)) :
    ψ B * F (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
  have h : (MulAut.conj (ψ B)).toMonoidHom.comp (F.comp ψ) =
      ψ.comp (stdUnitary σQ.toRingHom) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
    rintro _ ⟨a, b, hab, t, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hB a b hab, stdUnitary_transvection]
    congr 2
    have h0 : (β a b : L) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    field_simp
  have := DFunLike.congr_fun h X
  simpa [MulAut.conj_apply] using this

end Frame

section Lang


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem unitary_frame_step {s ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hq : S.D.q = r ^ e) {σQ : L ≃+* L} (hσc : ∀ c, σQ c = c ^ (r ^ (e * s))) :
    ∃ β : Fin ν → Fin ν → Lˣ, ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      iterHom S.D.step s (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
          ((β a b : L) * σQ t)) := by
  classical
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      iterHom S.D.step s (pinnedX τ L (σ a b) c) =
        pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  refine ⟨fun a b => μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹, fun a b hab t => ?_⟩
  rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (π.injective.ne hab).symm]
  congr 1
  rw [map_mul, hσc (ε a b : L)]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
  field_simp

theorem unitary_exists_pin {s ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hq : S.D.q = r ^ e) {σQ : L ≃+* L} (hσc : ∀ c, σQ c = c ^ (r ^ (e * s))) :
    ∃ B : SL(ν, L), ∀ X : SL(ν, L), ψ B * iterHom S.D.step s (ψ X) * (ψ B)⁻¹ =
      ψ (stdUnitary σQ.toRingHom X) := by
  obtain ⟨β, hkey⟩ := unitary_frame_step S hψ π hπ hq hσc
  obtain ⟨B, hB⟩ := unitary_pin_conj hν π β (unitary_pin_cocycle hψ _ π β hkey)
  exact ⟨B, unitary_pin_std _ σQ π β hkey hB⟩

theorem unitary_exists_hom_W (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hνQ : (ν, r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))) ≠
      (3, 2)) :
    ∃ (F : Subfield L) (σQ : L ≃+* L),
      Nat.card F = (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))) ^ 2 ∧
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)))) ∧
      ∃ W : SL(ν, L) →* ModGL τ L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i =
          (W.comp (statedSUToSL F ν
            (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))))).range ∧
        (W.comp (statedSUToSL F ν
            (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))))).ker ≤
          Subgroup.center ↥(StatedSU ν
            (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))) F) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hes : 1 ≤ e * s := Nat.mul_pos he hs0
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  obtain ⟨B, hB⟩ := unitary_exists_pin S hν hψ π hπ hq hσc
  obtain ⟨F, hF, hFcard⟩ := exists_subfield_card_sq (L := L) hr hes
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hr.pos _) 2).ne')
  have hfix : ∀ u, stdUnitary σQ.toRingHom (statedSUToSL F ν (r ^ (e * s)) u) =
      statedSUToSL F ν (r ^ (e * s)) u := fun u =>
    (stdUnitary_eq_self_iff σQ hσc _).2
      ((mem_range_statedSUToSL_iff hr F hF hFcard (by omega) _).1 ⟨u, rfl⟩)
  have hrange : ∀ Y : SL(ν, L), stdUnitary σQ.toRingHom Y = Y →
      ∃ u, statedSUToSL F ν (r ^ (e * s)) u = Y := fun Y hY =>
    (mem_range_statedSUToSL_iff hr F hF hFcard (by omega) Y).2
      ((stdUnitary_eq_self_iff σQ hσc Y).1 hY)
  have hperf : Group.IsPerfect ↥(StatedSU ν (r ^ (e * s)) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hFcard hν hνQ
  obtain ⟨W, h1, h2, h3⟩ := exists_pinned_hom S hT i hν hψ hΨ hB
    (statedSUToSL F ν (r ^ (e * s))) (statedSUToSL_injective F ν _) hfix hrange
  exact ⟨F, σQ, hFcard, hσc, W, le_antisymm h1 (h3 hperf), h2⟩

end Lang

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
