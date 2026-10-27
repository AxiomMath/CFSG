module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux9
public import CFSG.RankThree.PartOne.RF4.Descent
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section Dict

variable {K : Type} [Field K] [Finite K] [CharP K 2] (D : LangLevi Tag.F4 K wF4)

scoped instance charP_L : CharP D.L 2 := charP_of_injective_algebraMap (algebraMap K D.L).injective 2

theorem hsurj_L (hK : 2 ≤ Nat.card K) : ∀ n : D.L, ∃ z, z + D.Fr z = n := by
  intro n
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  open Polynomial in
  have hdeg : (X ^ Nat.card K + (X - C n) : D.L[X]).degree ≠ 0 := by
    have h1 : (X - C n : D.L[X]).degree < (X ^ Nat.card K : D.L[X]).degree := by
      rw [degree_X_sub_C, degree_X_pow]
      exact_mod_cast (by omega : 1 < Nat.card K)
    rw [degree_add_eq_left_of_degree_lt h1, degree_X_pow]
    exact_mod_cast (by omega : Nat.card K ≠ 0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨z, ?_⟩
  simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_C] at hz
  rw [D.hFr]
  linear_combination hz

theorem exists_zeta (hK : 3 ≤ Nat.card K) : ∃ ζ : D.L, D.Fr ζ = ζ ∧ ζ ≠ 0 ∧ ζ ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : 3 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt (Finset.card_le_two (a := (0 : K)) (b := 1)) (by omega)
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  refine ⟨algebraMap K D.L x, ?_, ?_, ?_⟩
  · rw [D.hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  · exact fun h => hx.1 ((map_eq_zero (algebraMap K D.L)).1 h)
  · exact fun h => hx.2 ((map_eq_one_iff (algebraMap K D.L) (algebraMap K D.L).injective).1 h)

end Dict

section Theta

variable {K : Type} [Field K] [Finite K] [CharP K 2] (D : LangLevi Tag.F4 K wF4)

@[expose] def Θ : ModGL Tag.F4 K →* ModGL Tag.F4 D.L :=
  (MulAut.conj D.g⁻¹).toMonoidHom.comp (baseChangeGL (algebraMap K D.L))

theorem Θ_apply (x : ModGL Tag.F4 K) :
    Θ D x = D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g := by
  simp [Θ, MulAut.conj_apply]

theorem Θ_injective : Function.Injective (Θ D) := by
  intro x y h
  rw [Θ_apply, Θ_apply] at h
  exact baseChangeGL_injective (algebraMap K D.L) (mul_left_cancel (mul_right_cancel h))

theorem fr_comp_algebraMap : D.Fr.comp (algebraMap K D.L) = algebraMap K D.L := by
  haveI : Fintype K := Fintype.ofFinite K
  ext c
  simp only [RingHom.comp_apply]
  rw [D.hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem lang_nW : Units.map (entrywiseHom D.Fr) D.g = D.g * nW D.L := D.lang

theorem sig_Θ (x : ModGL Tag.F4 K) : sigHom D.Fr (Θ D x) = Θ D x := by
  have h1 : Units.map (entrywiseHom D.Fr) (baseChangeGL (algebraMap K D.L) x) =
      baseChangeGL (algebraMap K D.L) x := by
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, fr_comp_algebraMap]
  rw [sigHom_apply, Θ_apply, map_mul, map_mul, map_inv, h1, lang_nW]
  group

theorem fr_fixed_of_sig_fixed {z : ModGL Tag.F4 D.L} (hz : sigHom D.Fr z = z) :
    Units.map (entrywiseHom D.Fr) (D.g * z * D.g⁻¹) = D.g * z * D.g⁻¹ := by
  have h : nW D.L * Units.map (entrywiseHom D.Fr) z * (nW D.L)⁻¹ = z := by
    rw [← sigHom_apply]; exact hz
  rw [map_mul, map_mul, map_inv, lang_nW]
  set F := Units.map (entrywiseHom D.Fr) z
  have e : D.g * nW D.L * F * (D.g * nW D.L)⁻¹ = D.g * (nW D.L * F * (nW D.L)⁻¹) * D.g⁻¹ := by
    group
  rw [e, h]

theorem g_mem_adjoint : D.g ∈ adjointGroup Tag.F4 D.L :=
  Heis.Pθ_le_adjointGroup _ _ (Heis.Lθ_le_Pθ _ _ D.g_mem)

theorem exists_of_sig_fixed {z : ModGL Tag.F4 D.L} (hz : sigHom D.Fr z = z)
    (hzG : z ∈ adjointGroup Tag.F4 D.L) : ∃ x ∈ adjointGroup Tag.F4 K, Θ D x = z := by
  classical
  have hyG : D.g * z * D.g⁻¹ ∈ adjointGroup Tag.F4 D.L :=
    mul_mem (mul_mem (g_mem_adjoint D) hzG) (inv_mem (g_mem_adjoint D))
  obtain ⟨x, hx, hxy⟩ := CFSG.RankThree.PartOne.RF4.mem_range_baseChange_of_frobenius_fixed D.L D.Fr
    D.hFr ⟨_, hyG⟩ (fr_fixed_of_sig_fixed D hz)
  refine ⟨x, hx, ?_⟩
  rw [Θ_apply]
  have hxy' : baseChangeGL (algebraMap K D.L) x = D.g * z * D.g⁻¹ := hxy
  rw [hxy']
  group

end Theta

section Frames

open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K] [Finite K] [CharP K 2] (D : LangLevi Tag.F4 K wF4)

theorem mem_frame_iff' (S : Set (Fin Tag.F4.rank → ℤ)) (x : ModGL Tag.F4 K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup Tag.F4 K ∧ Θ D x ∈ rootSpan Tag.F4 D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap, Θ_apply]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

theorem rootSpan_le_adj (S : Set (Fin Tag.F4.rank → ℤ)) (L : Type) [Field L] :
    rootSpan Tag.F4 L S ≤ adjointGroup Tag.F4 L :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem exists_frame_of_sig_fixed (S : Set (Fin Tag.F4.rank → ℤ)) {z : ModGL Tag.F4 D.L}
    (hz : z ∈ rootSpan Tag.F4 D.L S) (hs : sigHom D.Fr z = z) :
    ∃ x ∈ D.frame S, Θ D x = z := by
  obtain ⟨x, hx, hxz⟩ := exists_of_sig_fixed D hs (rootSpan_le_adj S _ hz)
  exact ⟨x, (mem_frame_iff' D S x).2 ⟨hx, hxz ▸ hz⟩, hxz⟩

theorem mem_map_Θ {H : Subgroup (ModGL Tag.F4 K)} {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : D.frame S ≤ H) {z : ModGL Tag.F4 D.L} (hz : z ∈ rootSpan Tag.F4 D.L S)
    (hs : sigHom D.Fr z = z) : z ∈ H.map (Θ D) := by
  obtain ⟨x, hx, hxz⟩ := exists_frame_of_sig_fixed D S hz hs
  exact ⟨x, hS hx, hxz⟩

theorem bc_mem_rootSpan {S : Set (Fin Tag.F4.rank → ℤ)} {m : ModGL Tag.F4 K}
    (hm : m ∈ rootSpan Tag.F4 K S) :
    baseChangeGL (algebraMap K D.L) m ∈ rootSpan Tag.F4 D.L S := by
  have hle : rootSpan Tag.F4 K S ≤
      (rootSpan Tag.F4 D.L S).comap (baseChangeGL (algebraMap K D.L)) := by
    refine iSup₂_le fun α hα => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    show baseChangeGL (algebraMap K D.L) (pinnedX Tag.F4 K α c) ∈ rootSpan Tag.F4 D.L S
    rw [baseChangeGL_pinnedX]
    exact pinnedX_mem_rootSpan hα _
  exact hle hm

theorem Θ_mem_Qθ {m : ModGL Tag.F4 K} (hm : m ∈ Qθ Tag.F4 K) : Θ D m ∈ Qθ Tag.F4 D.L := by
  have h := Lθ_conj_mem_Qθ (inv_mem D.g_mem) (bc_mem_rootSpan D hm)
  rw [Θ_apply]
  simpa using h

end Frames

section RootSets

open CFSG.LieType.Steinberg.Adjoint

theorem orth_S₂ : ∀ α ∈ rootFinset Tag.F4,
    (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → α i = 0) →
      iform (τ := Tag.F4) rS α = 0 ∧ iform (τ := Tag.F4) pS α = 0 ∧
        iform (τ := Tag.F4) (highRoot Tag.F4) α = 0 ∧
        iform (τ := Tag.F4) (-highRoot Tag.F4) α = 0 := by
  decide +kernel

theorem rS_mem_S₁ : rS ∈ TwClass.f4Six.S₁ :=
  ⟨isRoot_rS, fun α hα => (orth_S₂ α (mem_rootFinset.2 hα.1) hα.2).1⟩

theorem pS_mem_S₁ : pS ∈ TwClass.f4Six.S₁ :=
  ⟨isRoot_pS, fun α hα => (orth_S₂ α (mem_rootFinset.2 hα.1) hα.2).2.1⟩

theorem θ_mem_S₁ : highRoot Tag.F4 ∈ TwClass.f4Six.S₁ :=
  ⟨isRoot_theta, fun α hα => (orth_S₂ α (mem_rootFinset.2 hα.1) hα.2).2.2.1⟩

theorem negθ_mem_S₁ : -highRoot Tag.F4 ∈ TwClass.f4Six.S₁ :=
  ⟨IsRoot.neg isRoot_theta, fun α hα => (orth_S₂ α (mem_rootFinset.2 hα.1) hα.2).2.2.2⟩

theorem S₂_of {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (h : ∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → α i = 0) : α ∈ TwClass.f4Six.S₂ :=
  ⟨hα, h⟩

theorem a3_mem_S₂ : a3 ∈ TwClass.f4Six.S₂ := S₂_of isRoot_a3 (by decide +kernel)
theorem a4_mem_S₂ : a4 ∈ TwClass.f4Six.S₂ := S₂_of isRoot_a4 (by decide +kernel)
theorem g5_mem_S₂ : g5 ∈ TwClass.f4Six.S₂ := S₂_of isRoot_g5 (by decide +kernel)
theorem g5n_mem_S₂ : g5n ∈ TwClass.f4Six.S₂ := S₂_of isRoot_g5n (by decide +kernel)

end RootSets

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even


