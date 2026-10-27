module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixM
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus nondegenerate_polarBilin_quadMinus_of_finite)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem conj_commutator_mem {G : Type*} [Group G] (O : Subgroup G) {g : G} (hg : g ∈ O) {h : G}
    (hh : h ∈ ⁅O, O⁆) : g * h * g⁻¹ ∈ ⁅O, O⁆ := by
  have h1 : O.map (MulAut.conj g).toMonoidHom = O := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact O.mul_mem (O.mul_mem hg hy) (O.inv_mem hg)
    · intro hx
      exact ⟨g⁻¹ * x * g, O.mul_mem (O.mul_mem (O.inv_mem hg) hx) hg, by simp [mul_assoc]⟩
  have : g * h * g⁻¹ ∈ (⁅O, O⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom := ⟨h, hh, by simp⟩
  rwa [Subgroup.map_commutator, h1] at this

theorem conj_mem_statedOmega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hg : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g ∈ orthogonalGroup (quadMinus 3 F b c))
    {h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F}
    (hh : h ∈ StatedOmega (StatedQuadMinus 3 F b c)) :
    g * h * g⁻¹ ∈ StatedOmega (StatedQuadMinus 3 F b c) := by
  rw [mem_statedOmega_iff] at hh ⊢
  have e : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F (g * h * g⁻¹) =
      toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g *
        toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F h *
        (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F g)⁻¹ := by
    simp [map_mul, map_inv]
  rw [e]
  exact conj_commutator_mem _ hg hh

theorem conj_vec_stab (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p k : ℕ}
    {E₀ : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)}
    (hE₀Ω : E₀ ≤ StatedOmega (StatedQuadMinus 3 F b c)) (hE₀a : IsElemAbelian p E₀)
    (hE₀c : Nat.card E₀ = p ^ k) {w₀ w : OW F} (g₀ : OW F ≃ₗ[F] OW F)
    (hg₀ : g₀ ∈ orthogonalGroup (quadMinus 3 F b c)) (hgw : g₀ w₀ = w)
    (hfix : ∀ g ∈ E₀, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w₀ = w₀) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
      ∀ g ∈ E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w =
          w := by
  set G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g₀ with hG₀
  have hG₀O : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G₀ ∈ orthogonalGroup (quadMinus 3 F b c) := by
    rw [hG₀, MulEquiv.apply_symm_apply]
    exact hg₀
  have hG₀w : ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w₀ = w := by
    rw [← toLinEquiv_apply, hG₀, MulEquiv.apply_symm_apply]
    exact hgw
  refine ⟨E₀.map (MulAut.conj G₀).toMonoidHom, ?_, hE₀a.map _, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_statedOmega hirr hG₀O (hE₀Ω hh)
  · rw [Subgroup.card_map_of_injective (MulAut.conj G₀).injective, hE₀c]
  · rintro _ ⟨h, hh, rfl⟩
    rw [← hG₀w]
    show (((G₀ * h * G₀⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        (((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w₀)) = _
    rw [Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    have h1 : ((G₀⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *
          ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [h1, Matrix.mul_one, ← Matrix.mulVec_mulVec, hfix h hh]

section Vectors

variable (M : NormModel F b c)

theorem charTwo_E : (2 : M.E) = 0 := by
  have : CharP M.E 2 := charP_of_injective_algebraMap (algebraMap F M.E).injective 2
  exact CharP.cast_eq_zero M.E 2

theorem quad_symm_single (l : F) :
    StatedQuadMinus 3 F b c (M.T.symm ![algebraMap F M.E l, 0, 0]) = l * l := by
  apply (algebraMap F M.E).injective
  rw [M.norm_eq, LinearEquiv.apply_symm_apply, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [zero_pow (Nat.succ_ne_zero _), add_zero, add_zero, ← map_pow]
  congr 1
  haveI := Fintype.ofFinite F
  rw [pow_succ, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem quad_symm_pair (z : M.E) :
    StatedQuadMinus 3 F b c (M.T.symm ![z, z, 0]) = 0 := by
  apply (algebraMap F M.E).injective
  rw [M.norm_eq, LinearEquiv.apply_symm_apply, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [zero_pow (Nat.succ_ne_zero _), add_zero, map_zero, ← two_mul, charTwo_E, zero_mul]

end Vectors

theorem quadMinus_eq_stated (x : OW F) : quadMinus 3 F b c x = StatedQuadMinus 3 F b c x :=
  congrFun (coe_quadMinus 3 F b c) x

theorem stated_quad_zero : StatedQuadMinus 3 F b c 0 = 0 := by
  rw [← quadMinus_eq_stated]
  exact map_zero _

theorem exists_isometry_apply_eq (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {w₀ w : OW F}
    (hw₀ : w₀ ≠ 0) (hw : w ≠ 0)
    (hQ : StatedQuadMinus 3 F b c w = StatedQuadMinus 3 F b c w₀) :
    ∃ g ∈ orthogonalGroup (quadMinus 3 F b c), g w₀ = w := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQn (k := 1) (fun _ => w₀) (fun _ => w)
    ((linearIndependent_unique_iff (v := fun _ : Fin 1 => w₀)).mpr hw₀)
    ((linearIndependent_unique_iff (v := fun _ : Fin 1 => w)).mpr hw)
    (fun i => by
      show quadMinus 3 F b c w = quadMinus 3 F b c w₀
      rw [quadMinus_eq_stated, quadMinus_eq_stated]
      exact hQ)
    (fun i j => by
      have e1 := polar_self_eq_two_mul (Q := quadMinus 3 F b c) w
      have e2 := polar_self_eq_two_mul (Q := quadMinus 3 F b c) w₀
      simp only [e1, e2, h2, zero_mul])
  exact ⟨g, hg, hgu 0⟩

theorem exists_stab_nonsing (M : NormModel F b c) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card F + 1) {w : OW F} (hw : StatedQuadMinus 3 F b c w ≠ 0) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ g ∈ E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w =
          w := by
  haveI := Fintype.ofFinite F
  obtain ⟨E₀, hE₀Ω, hE₀a, hE₀c, hE₀f⟩ := exists_E0 M hp hpq
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2)
    (StatedQuadMinus 3 F b c w)
  set w₀ : OW F := M.T.symm ![algebraMap F M.E l, 0, 0] with hw₀
  have hQ₀ : StatedQuadMinus 3 F b c w₀ = StatedQuadMinus 3 F b c w := by
    rw [hw₀, quad_symm_single, hl]
  have hw0 : w ≠ 0 := by
    intro h
    apply hw
    rw [h]
    exact (coe_quadMinus 3 F b c ▸ map_zero (quadMinus 3 F b c))
  have hw₀0 : w₀ ≠ 0 := by
    intro h
    apply hw
    rw [← hQ₀, h]
    exact (coe_quadMinus 3 F b c ▸ map_zero (quadMinus 3 F b c))
  obtain ⟨g₀, hg₀, hgw⟩ := exists_isometry_apply_eq hirr hw₀0 hw0 hQ₀.symm
  exact conj_vec_stab hirr hE₀Ω hE₀a hE₀c g₀ hg₀ hgw (fun g hg => hE₀f g hg _)

theorem exists_stab_ne_zero (M : NormModel F b c) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card F + 1) {w : OW F} (hw : w ≠ 0) :
    ∃ (k : ℕ) (E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F)), 1 ≤ k ∧
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
      ∀ g ∈ E, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ w =
          w := by
  by_cases hQ : StatedQuadMinus 3 F b c w = 0
  · obtain ⟨E₁, hE₁Ω, hE₁a, hE₁c, hE₁f⟩ := exists_E1 M hp hpq
    set w₀ : OW F := M.T.symm ![1, 1, 0] with hw₀
    have hQ₀ : StatedQuadMinus 3 F b c w₀ = 0 := by
      have := quad_symm_pair M (1 : M.E)
      exact this
    have hw₀0 : w₀ ≠ 0 := by
      intro h
      have := congrArg M.T h
      rw [hw₀, LinearEquiv.apply_symm_apply, map_zero] at this
      have h0 := congrFun this 0
      simp at h0
    obtain ⟨g₀, hg₀, hgw⟩ := exists_isometry_apply_eq hirr hw₀0 hw (hQ.trans hQ₀.symm)
    obtain ⟨E, h1, h2, h3, h4⟩ := conj_vec_stab hirr hE₁Ω hE₁a (k := 1)
      (by rw [hE₁c, pow_one]) g₀ hg₀ hgw (fun g hg => hE₁f g hg 1 1)
    exact ⟨1, E, le_rfl, h1, h2, h3, h4⟩
  · obtain ⟨E, h1, h2, h3, h4⟩ := exists_stab_nonsing M hirr hp hpq hQ
    exact ⟨2, E, by norm_num, h1, h2, h3, h4⟩

section Planes

@[expose] noncomputable def diagE (M : NormModel F b c) : M.E →ₗ[F] OW F :=
  M.T.symm.toLinearMap ∘ₗ
    { toFun := fun z => ![z, z, 0]
      map_add' := fun z z' => by
        funext i
        fin_cases i <;> simp
      map_smul' := fun r z => by
        funext i
        fin_cases i <;> simp }

theorem diagE_apply (M : NormModel F b c) (z : M.E) : diagE M z = M.T.symm ![z, z, 0] := rfl

theorem diagE_injective (M : NormModel F b c) : Function.Injective (diagE M) := by
  intro z z' h
  have := congrArg M.T h
  rw [diagE_apply, diagE_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  simpa using congrFun this 0

theorem finrank_E (M : NormModel F b c) : Module.finrank F M.E = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := F) (V := M.E)
  rw [M.card_E] at h
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  exact (Nat.pow_right_injective h2 h).symm

theorem exists_stab_plane (M : NormModel F b c) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card F + 1) (Y : Submodule F (OW F))
    (hY2 : Module.finrank F Y = 2) (hYs : ∀ y ∈ Y, StatedQuadMinus 3 F b c y = 0) :
    ∃ E : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F),
      E ≤ StatedOmega (StatedQuadMinus 3 F b c) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ g ∈ E, ∀ y ∈ Y, ((g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y ∈ Y := by
  haveI := Fintype.ofFinite F
  obtain ⟨E₂, hE₂Ω, hE₂a, hE₂c, hE₂s⟩ := exists_E2 M hp hpq
  have hQn := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  let bE : Module.Basis (Fin 2) F M.E := Module.finBasisOfFinrankEq F M.E (finrank_E M)
  let bY : Module.Basis (Fin 2) F Y := Module.finBasisOfFinrankEq F Y hY2
  have huli : LinearIndependent F (fun i => diagE M (bE i)) :=
    (bE.linearIndependent).map' (diagE M) (LinearMap.ker_eq_bot.mpr (diagE_injective M))
  have hu'li : LinearIndependent F (fun i => ((bY i : Y) : OW F)) :=
    (bY.linearIndependent).map' Y.subtype (Submodule.ker_subtype Y)
  have hQu : ∀ z : M.E, quadMinus 3 F b c (diagE M z) = 0 := fun z => by
    rw [quadMinus_eq_stated, diagE_apply]
    exact quad_symm_pair M z
  have hQu' : ∀ y ∈ Y, quadMinus 3 F b c y = 0 := fun y hy => by
    rw [quadMinus_eq_stated]
    exact hYs y hy
  obtain ⟨g₀, hg₀, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQn (k := 2) (fun i => diagE M (bE i)) (fun i => ((bY i : Y) : OW F)) huli hu'li
    (fun i => by
      show quadMinus 3 F b c ((bY i : Y) : OW F) = quadMinus 3 F b c (diagE M (bE i))
      rw [hQu' _ (bY i).2, hQu])
    (fun i j => by
      have e1 : polar (quadMinus 3 F b c) ((bY i : Y) : OW F) ((bY j : Y) : OW F) = 0 := by
        show quadMinus 3 F b c (((bY i : Y) : OW F) + ((bY j : Y) : OW F)) -
          quadMinus 3 F b c ((bY i : Y) : OW F) - quadMinus 3 F b c ((bY j : Y) : OW F) = 0
        rw [hQu' _ (Y.add_mem (bY i).2 (bY j).2), hQu' _ (bY i).2, hQu' _ (bY j).2]
        ring
      have e2 : polar (quadMinus 3 F b c) (diagE M (bE i)) (diagE M (bE j)) = 0 := by
        show quadMinus 3 F b c (diagE M (bE i) + diagE M (bE j)) -
          quadMinus 3 F b c (diagE M (bE i)) - quadMinus 3 F b c (diagE M (bE j)) = 0
        rw [← map_add (diagE M), hQu, hQu, hQu]
        ring
      rw [e1, e2])
  have hmapY : ∀ z : M.E, g₀ (diagE M z) ∈ Y := by
    intro z
    have hexp : diagE M z = ∑ i, bE.repr z i • diagE M (bE i) := by
      conv_lhs => rw [← bE.sum_repr z]
      rw [map_sum]
      simp only [map_smul]
    rw [hexp, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul, hgu i]
    exact Submodule.smul_mem _ _ (bY i).2
  have hsurj : ∀ y ∈ Y, ∃ z : M.E, g₀ (diagE M z) = y := by
    intro y hy
    refine ⟨∑ i, bY.repr ⟨y, hy⟩ i • bE i, ?_⟩
    rw [map_sum]
    simp only [map_smul, map_sum]
    have h1 : ∀ i, g₀ (diagE M (bE i)) = ((bY i : Y) : OW F) := hgu
    simp only [h1]
    have h3 := congrArg (fun t : Y => (t : OW F)) (bY.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
    exact h3
  set G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
    (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm g₀ with hG₀
  have hG₀O : toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F G₀ ∈
      orthogonalGroup (quadMinus 3 F b c) := by
    rw [hG₀, MulEquiv.apply_symm_apply]
    exact hg₀
  have hG₀mul : ∀ x : OW F, ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x =
        g₀ x := by
    intro x
    rw [← toLinEquiv_apply, hG₀, MulEquiv.apply_symm_apply]
  refine ⟨E₂.map (MulAut.conj G₀).toMonoidHom, ?_, hE₂a.map _, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_statedOmega hirr hG₀O (hE₂Ω hh)
  · rw [Subgroup.card_map_of_injective (MulAut.conj G₀).injective, hE₂c]
  · rintro _ ⟨h, hh, rfl⟩ y hy
    obtain ⟨z, hz⟩ := hsurj y hy
    have hy' : ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          diagE M z = y := by rw [hG₀mul, hz]
    have hstep : (((G₀ * h * G₀⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y) =
        ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
          (((h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
            diagE M z) := by
      rw [← hy', Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
        Matrix.mul_assoc]
      have h1 : ((G₀⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *
            ((G₀ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
              Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) =
            1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [h1, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    show (((G₀ * h * G₀⁻¹ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ y) ∈ Y
    rw [hstep]
    set y' : OW F := ((h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ
        diagE M z with hy'def
    have hT : M.T (diagE M z) = ![z, z, 0] := by
      rw [diagE_apply, LinearEquiv.apply_symm_apply]
    obtain ⟨hy0, hy2⟩ := hE₂s h hh (diagE M z) (by rw [hT]; rfl) (by rw [hT]; rfl)
    have hyd : y' = diagE M (M.T y' 0) := by
      apply M.T.injective
      rw [diagE_apply, LinearEquiv.apply_symm_apply]
      funext i
      fin_cases i
      · rfl
      · exact hy0.symm
      · exact hy2
    rw [hG₀mul, hyd]
    exact hmapY _

end Planes

end CFSG.LocalAnalysis.RankThreeUC
