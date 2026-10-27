module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAPinHom
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

section Incl

variable {L : Type} [Field L]

@[expose] noncomputable def slSubfieldIncl (K : Subfield L) (ν : ℕ) :
    ↥(CFSG.Assembly.LargeEvenSLGroup (Fin ν) ↥K) →* SL(ν, L) :=
  (Matrix.SpecialLinearGroup.map K.subtype).comp
    Matrix.SpecialLinearGroup.toGLKerEquiv.symm.toMonoidHom

theorem coe_slSubfieldIncl (K : Subfield L) (ν : ℕ)
    (h : ↥(CFSG.Assembly.LargeEvenSLGroup (Fin ν) ↥K)) :
    ((slSubfieldIncl K ν h : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      ((h : GL (Fin ν) ↥K) : Matrix (Fin ν) (Fin ν) ↥K).map K.subtype :=
  rfl

theorem slSubfieldIncl_injective (K : Subfield L) (ν : ℕ) :
    Function.Injective (slSubfieldIncl K ν) :=
  (specialLinearGroup_map_injective K.subtype_injective).comp
    Matrix.SpecialLinearGroup.toGLKerEquiv.symm.injective

theorem largeEvenSL_isPerfect {K : Type} [Field K] {ν : ℕ} (hν : 3 ≤ ν) :
    Group.IsPerfect ↥(CFSG.Assembly.LargeEvenSLGroup (Fin ν) K) := by
  haveI : Group.IsPerfect SL(ν, K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  exact Group.IsPerfect.ofSurjective
    (f := (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin ν) (R := K)).toMonoidHom)
    Matrix.SpecialLinearGroup.toGLKerEquiv.surjective

theorem largeEvenSL_center_eq {K : Type} [Field K] {ν : ℕ} (hν : 1 ≤ ν) :
    (CFSG.Assembly.LargeEvenScalars (Fin ν) K).subgroupOf
        (CFSG.Assembly.LargeEvenSLGroup (Fin ν) K) =
      Subgroup.center ↥(CFSG.Assembly.LargeEvenSLGroup (Fin ν) K) := by
  ext h
  rw [Subgroup.mem_subgroupOf, CFSG.Assembly.largeEvenScalars_def, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Units.ext
    have hmat : ((h : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K) =
        Matrix.scalar (Fin ν) (c : K) := by
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hmat]
    exact (Matrix.scalar_commute (n := Fin ν) (c : K) (fun r => Commute.all _ r) _).eq.symm
  · intro hh
    have hu : Matrix.SpecialLinearGroup.toGLKerEquiv.symm h ∈ Subgroup.center SL(ν, K) :=
      symm_mem_center_of_mulEquiv _ hh
    obtain ⟨r, hr, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hu
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow (by simp; omega)] at hr
      exact zero_ne_one hr
    exact ⟨Units.mk0 r hr0, Units.ext (by
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      exact hru)⟩

end Incl

section Matrix

variable {L : Type} [Field L] [IsAlgClosed L]

theorem split_pin_conj {ν : ℕ} (hν : 3 ≤ ν) (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = β a b * β b c) :
    ∃ B : SL(ν, L), ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection hab (((β a b)⁻¹ : Lˣ) * u) := by
  obtain ⟨d, hd⟩ := exists_units_of_cocycle_mul hν β hcoc
  obtain ⟨d', hd'⟩ : ∃ d' : Fin ν → Lˣ, ∀ a, d' a = (d a)⁻¹ := ⟨fun a => (d a)⁻¹, fun _ => rfl⟩
  set M : GL (Fin ν) L := diagHom ν d' * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  refine ⟨B, fun a b hab u => ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
  have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
      (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d' : Matrix (Fin ν) (Fin ν) L) *
        ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
          ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
            (↑(diagHom ν d')⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
    intro Y
    simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
    permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d' hab u]
  congr 2
  rw [hd' a, hd' b, hd a b hab]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]
  have h0 : (d a : L) ≠ 0 := Units.ne_zero _
  have h0' : (d b : L) ≠ 0 := Units.ne_zero _
  field_simp

end Matrix

section Frame

variable {τ : Tag} {L : Type}
  [Field L]

theorem split_pin_cocycle {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (F : ModGL τ L →* ModGL τ L)
    {σQ : L ≃+* L} (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      F (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((β a b : L) * σQ t))) :
    ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = β a b * β b c := by
  intro a b c hab hbc hac
  obtain ⟨ε, hε⟩ := hψ.transv (π a) (π c) (π.injective.ne hac)
  have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
  rw [mul_one] at hcomm
  have h1 := congrArg (fun X => F (ψ X)) hcomm
  simp only [map_commutatorElement] at h1
  rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
    ← map_commutatorElement ψ,
    Matrix.SpecialLinearGroup.commutatorElement_transvection (π.injective.ne hab)
      (π.injective.ne hbc) (π.injective.ne hac), hε, hε] at h1
  have h2 := pinnedX_injective τ L _ h1
  have h0 : (ε : L) ≠ 0 := Units.ne_zero _
  apply Units.ext
  have h3 := mul_left_cancel₀ h0 h2
  rw [Units.val_mul]
  exact h3.symm

theorem split_pin_std {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} (F : ModGL τ L →* ModGL τ L)
    (σQ : L ≃+* L) (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      F (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((β a b : L) * σQ t)))
    {B : SL(ν, L)}
    (hB : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection hab (((β a b)⁻¹ : Lˣ) * u)) (X : SL(ν, L)) :
    ψ B * F (ψ X) * (ψ B)⁻¹ = ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) := by
  have h : (MulAut.conj (ψ B)).toMonoidHom.comp (F.comp ψ) =
      ψ.comp (Matrix.SpecialLinearGroup.map σQ.toRingHom) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
    rintro _ ⟨a, b, hab, t, rfl⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hB a b hab, slMap_transvection]
    congr 2
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rfl
  have := DFunLike.congr_fun h X
  simpa [MulAut.conj_apply] using this

end Frame

section Lang


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem split_frame_step {s ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) = σ (π a) (π b))
    {r e : ℕ} (hq : S.D.q = r ^ e) {σQ : L ≃+* L} (hσc : ∀ c, σQ c = c ^ (r ^ (e * s))) :
    ∃ β : Fin ν → Fin ν → Lˣ, ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      iterHom S.D.step s (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((β a b : L) * σQ t)) := by
  classical
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      iterHom S.D.step s (pinnedX τ L (σ a b) c) =
        pinnedX τ L (σ (π a) (π b)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  refine ⟨fun a b => μ a b * ε a b ^ (r ^ (e * s)) * (ε (π a) (π b))⁻¹, fun a b hab t => ?_⟩
  rw [hε a b hab t, hμ a b hab, hε (π a) (π b) (π.injective.ne hab)]
  congr 1
  rw [map_mul, hσc (ε a b : L)]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  have h0 : (ε (π a) (π b) : L) ≠ 0 := Units.ne_zero _
  field_simp

theorem split_exists_pin {s ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) = σ (π a) (π b))
    {r e : ℕ} (hq : S.D.q = r ^ e) {σQ : L ≃+* L} (hσc : ∀ c, σQ c = c ^ (r ^ (e * s))) :
    ∃ B : SL(ν, L), ∀ X : SL(ν, L), ψ B * iterHom S.D.step s (ψ X) * (ψ B)⁻¹ =
      ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) := by
  obtain ⟨β, hkey⟩ := split_frame_step S hψ π hπ hq hσc
  obtain ⟨B, hB⟩ := split_pin_conj hν π β (split_pin_cocycle hψ _ π β hkey)
  exact ⟨B, split_pin_std _ σQ π β hkey hB⟩

theorem split_exists_hom_W (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (hq : S.D.q = r ^ e) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)))) ∧
      ∃ W : SL(ν, L) →* ModGL τ L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i =
          (W.comp (slSubfieldIncl (fixSubfield σQ) ν)).range ∧
        (W.comp (slSubfieldIncl (fixSubfield σQ) ν)).ker ≤
          Subgroup.center ↥(CFSG.Assembly.LargeEvenSLGroup (Fin ν) ↥(fixSubfield σQ)) := by
  classical
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  obtain ⟨B, hB⟩ := split_exists_pin S hν hψ π hπ hq hσc
  set K : Subfield L := fixSubfield σQ with hK
  have hfix : ∀ u, Matrix.SpecialLinearGroup.map σQ.toRingHom (slSubfieldIncl K ν u) =
      slSubfieldIncl K ν u := fun u => by
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_slSubfieldIncl, Matrix.map_apply]
    exact (mem_fixSubfield σQ).1
      (((u : GL (Fin ν) ↥K) : Matrix (Fin ν) (Fin ν) ↥K) i j).2
  have hrange : ∀ Y : SL(ν, L), Matrix.SpecialLinearGroup.map σQ.toRingHom Y = Y →
      ∃ u, slSubfieldIncl K ν u = Y := by
    intro Y hY
    obtain ⟨c, hc⟩ := exists_map_eq_of_forall_mem_range K.subtype_injective Y fun i j => by
      have := congrArg (fun Z : SL(ν, L) => (Z : Matrix (Fin ν) (Fin ν) L) i j) hY
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
      exact ⟨⟨_, (mem_fixSubfield σQ).2 this⟩, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGLKerEquiv c, ?_⟩
    show Matrix.SpecialLinearGroup.map K.subtype
      (Matrix.SpecialLinearGroup.toGLKerEquiv.symm (Matrix.SpecialLinearGroup.toGLKerEquiv c)) = Y
    rw [MulEquiv.symm_apply_apply]
    exact hc
  obtain ⟨W, h1, h2, h3⟩ := exists_pinned_hom S hT i hν hψ hΨ hB (slSubfieldIncl K ν)
    (slSubfieldIncl_injective K ν) hfix hrange
  exact ⟨σQ, hσc, W, le_antisymm h1 (h3 (largeEvenSL_isPerfect hν)), h2⟩

end Lang

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
