module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveInvariants
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.ClassicalGroups.Alternating.Transvections

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {b : LinearMap.BilinForm (ZMod 2) E}
  {Q : QuadraticForm (ZMod 2) E}

namespace Orth

@[expose] def qForm (Q : QuadraticForm (ZMod 2) E) : QuadraticForm (ZMod 2) (E × ZMod 2) :=
  Q.prod QuadraticMap.sq

theorem qForm_apply (v : E × ZMod 2) : qForm Q v = qV Q v := by
  simp only [qForm, QuadraticMap.prod_apply, QuadraticMap.sq_apply, qV, zmod2_mul_self]

theorem qV_add (hQ : QuadraticMap.polarBilin Q = b) (v w : E × ZMod 2) :
    qV Q (v + w) = qV Q v + qV Q w + b v.1 w.1 := by
  simp only [qV, Prod.fst_add, Prod.snd_add, Q_add hQ]
  ring

@[expose] def hEquiv (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b) :
    (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2) :=
  (hHom hQ s).toLinearEquiv

theorem hEquiv_apply (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    (v : E × ZMod 2) : hEquiv hQ s v = (sE s v.1, v.2 + Q v.1 + Q (sE s v.1)) :=
  rfl

theorem hEquiv_mul_apply (hQ : QuadraticMap.polarBilin Q = b) (s t : bilinIsometryGroup b)
    (v : E × ZMod 2) : hEquiv hQ (s * t) v = hEquiv hQ s (hEquiv hQ t v) :=
  congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2) =>
    (g : (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2)) v) ((hHom hQ).map_mul s t)

theorem hEquiv_one (hQ : QuadraticMap.polarBilin Q = b) :
    hEquiv hQ (1 : bilinIsometryGroup b) = 1 :=
  LinearEquiv.ext fun v => congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
    (E × ZMod 2) => (g : (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2)) v) (hHom hQ).map_one

theorem hEquiv_injective (hQ : QuadraticMap.polarBilin Q = b) :
    Function.Injective (hEquiv hQ (b := b)) := fun s t h => by
  refine Subtype.ext (gl_ext fun x => ?_)
  have := congrArg (fun g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2) => (g (x, 0)).1) h
  exact this

theorem hEquiv_mem (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b) :
    hEquiv hQ s ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [qForm_apply, qForm_apply]
    exact qV_hHom hQ s v

theorem exists_hEquiv_eq [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) {g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q)) : ∃ s, g = hEquiv hQ s := by
  have hq : ∀ v, qV Q (g v) = qV Q v := fun v => by
    rw [← qForm_apply, ← qForm_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  have hpol : ∀ v w, b (g v).1 (g w).1 = b v.1 w.1 := fun v w => by
    have h1 := qV_add hQ (g v) (g w)
    rw [← map_add, hq, hq, hq, qV_add hQ] at h1
    exact (add_left_cancel h1).symm
  have hr : g rV = rV := by
    have h1 : ∀ x : E, b (g rV).1 x = 0 := fun x => by
      obtain ⟨v, hv⟩ := g.surjective (x, 0)
      have h2 := hpol rV v
      rwa [hv, rV, map_zero, LinearMap.zero_apply] at h2
    have h2 : (g rV).1 = 0 := hnd.1 _ h1
    have h3 := hq rV
    rw [qV, h2, QuadraticMap.map_zero, zero_add, qV, rV, QuadraticMap.map_zero, zero_add] at h3
    exact Prod.ext h2 h3
  set S₀ : E →ₗ[ZMod 2] E := (LinearMap.fst (ZMod 2) E (ZMod 2)) ∘ₗ g.toLinearMap ∘ₗ
    (LinearMap.inl (ZMod 2) E (ZMod 2)) with hS₀def
  have hS₀ : ∀ w, S₀ w = (g (w, 0)).1 := fun w => rfl
  have hS₀b : ∀ x y, b (S₀ x) (S₀ y) = b x y := fun x y => hpol (x, 0) (y, 0)
  have hinj : Function.Injective S₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine hnd.1 w fun y => ?_
    rw [← hS₀b, hw, map_zero, LinearMap.zero_apply]
  set S := LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofInjectiveEndo S₀ hinj)
  have hS : S ∈ bilinIsometryGroup b := fun x y => hS₀b x y
  refine ⟨⟨S, hS⟩, LinearEquiv.ext fun v => ?_⟩
  have hv : v = (v.1, 0) + v.2 • rV := by
    simp only [rV, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero,
      zero_add]
  have h0 : (g (v.1, 0)).2 = Q v.1 + Q (S₀ v.1) := by
    have h1 := hq (v.1, 0)
    rw [qV, qV, ← hS₀, add_zero] at h1
    rw [← h1]
    generalize Q (S₀ v.1) = p
    generalize (g (v.1, 0)).2 = c
    revert p c
    decide
  rw [hEquiv_apply]
  conv_lhs => rw [hv, map_add, map_smul, hr]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, rV, smul_zero, add_zero]
    rfl
  · simp only [Prod.snd_add, Prod.smul_snd, rV, smul_eq_mul, mul_one, h0]
    change Q v.1 + Q (S₀ v.1) + v.2 = v.2 + Q v.1 + Q (S₀ v.1)
    ring

theorem mem_orthogonalGroup_qForm_iff [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) (g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2)) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q) ↔
      ∃ S ∈ bilinIsometryGroup b, ∀ w t,
        g (w, t) = ((S : E →ₗ[ZMod 2] E) w, t + Q w + Q ((S : E →ₗ[ZMod 2] E) w)) := by
  constructor
  · intro hg
    obtain ⟨s, rfl⟩ := exists_hEquiv_eq hnd hQ hg
    exact ⟨s, s.2, fun w t => rfl⟩
  · rintro ⟨S, hS, h⟩
    have hg : g = hEquiv hQ ⟨S, hS⟩ := LinearEquiv.ext fun v => by
      rw [← Prod.mk.eta (p := v), h]
      rfl
    rw [hg]
    exact hEquiv_mem hQ _

theorem apply_rV_of_mem [FiniteDimensional (ZMod 2) E] (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) {g : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q)) : g rV = rV := by
  obtain ⟨s, rfl⟩ := exists_hEquiv_eq hnd hQ hg
  exact hHom_rV hQ s

private theorem exists_basis_antidiag [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    ∃ β : Module.Basis (Fin 4) (ZMod 2) E,
      LinearMap.BilinForm.toMatrix β b =
        CFSG.ComponentClassification.PresentationLocal.antidiagGram := by
  obtain ⟨m, c, hc⟩ := hb.exists_basis_toMatrix_eq_J hnd
  have hm : m = 2 := by
    have h := Module.finrank_eq_card_basis c
    rw [hE, Fintype.card_sum, Fintype.card_fin] at h
    omega
  subst hm
  refine ⟨c.reindex (finSumFinEquiv.trans (Equiv.swap (2 : Fin 4) 3)), ?_⟩
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.reindex_apply, ← LinearMap.BilinForm.toMatrix_apply, hc]
  fin_cases i <;> fin_cases j <;> decide

theorem card_bilinIsometryGroup [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    Nat.card (bilinIsometryGroup b) = 720 := by
  classical
  obtain ⟨β, hβ⟩ := exists_basis_antidiag hE hb hnd
  let θ : LinearMap.GeneralLinearGroup (ZMod 2) E ≃* GL (Fin 4) (ZMod 2) :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv β).toMulEquiv
  have hθ : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) E,
      ((θ g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
        LinearMap.toMatrix β β (g : E →ₗ[ZMod 2] E) := fun g => rfl
  have hmem : ∀ g, g ∈ bilinIsometryGroup b ↔
      θ g ∈ CFSG.ComponentClassification.PresentationLocal.sympFour := fun g => by
    rw [CFSG.ComponentClassification.PresentationLocal.mem_sympFour_iff, hθ, ← hβ,
      ← LinearMap.BilinForm.toMatrix_comp, (LinearMap.BilinForm.toMatrix β).injective.eq_iff,
      mem_bilinIsometryGroup]
    constructor
    · intro h
      ext x y
      exact h x y
    · intro h x y
      exact congrArg (fun B : LinearMap.BilinForm (ZMod 2) E => B x y) h
  calc Nat.card (bilinIsometryGroup b) =
        Nat.card CFSG.ComponentClassification.PresentationLocal.sympFour :=
        Nat.card_congr (θ.toEquiv.subtypeEquiv hmem)
    _ = Nat.card (Equiv.Perm (Fin 6)) := Nat.card_congr (Equiv.ofBijective _
        ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
          CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩)
    _ = 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl

theorem card_orthogonalGroup_qForm [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (qForm Q)) = 720 := by
  rw [← card_bilinIsometryGroup hE hb hnd]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun s : bilinIsometryGroup b => (⟨hEquiv hQ s, hEquiv_mem hQ s⟩ :
      TauCeti.QuadraticMap.orthogonalGroup (qForm Q))) ⟨fun s t h => ?_, fun g => ?_⟩)).symm
  · exact hEquiv_injective hQ (congrArg Subtype.val h)
  · obtain ⟨s, hs⟩ := exists_hEquiv_eq hnd hQ g.2
    exact ⟨s, Subtype.ext hs.symm⟩

theorem card_generalLinearGroup [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) E) = 20160 := by
  classical
  let β := Module.finBasisOfFinrankEq (ZMod 2) E hE
  rw [Nat.card_congr (Units.mapEquiv (LinearMap.toMatrixAlgEquiv β).toMulEquiv).toEquiv,
    Matrix.card_GL_field, ZMod.card]
  rfl

theorem exists_sE_apply_eq [FiniteDimensional (ZMod 2) E] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) : ∃ s : bilinIsometryGroup b, sE s u = v := by
  obtain ⟨g, hg, hgu⟩ :=
    (CFSG.ClassicalGroups.Alternating.alternating_transvection_vector_transitivity hb hnd).2
      u v hu hv
  exact ⟨⟨g, CFSG.ClassicalGroups.Alternating.closure_symplecticTransvection_le_bilinIsometryGroup
    hb hg⟩, hgu⟩

theorem eq_bot_or_eq_top_of_invariant [FiniteDimensional (ZMod 2) E] (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (X : Submodule (ZMod 2) E)
    (hX : ∀ (s : bilinIsometryGroup b), ∀ x ∈ X, sE s x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  by_cases h : X = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  rw [eq_top_iff]
  intro v _
  by_cases hv : v = 0
  · rw [hv]
    exact X.zero_mem
  obtain ⟨s, hs⟩ := exists_sE_apply_eq hb hnd hx0 hv
  rw [← hs]
  exact hX s x hxX

theorem eq_fst_add_smul_rV (v : E × ZMod 2) : v = (v.1, 0) + v.2 • rV := by
  simp only [rV, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero,
    zero_add]

theorem hEquiv_inv_apply (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    (v : E × ZMod 2) : hEquiv hQ s⁻¹ (hEquiv hQ s v) = v := by
  rw [← hEquiv_mul_apply, inv_mul_cancel, hEquiv_one]
  rfl

theorem invariant_submodule_V [FiniteDimensional (ZMod 2) E] (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b) (hE : 4 < Nat.card E)
    (X : Submodule (ZMod 2) (E × ZMod 2))
    (hX : ∀ (s : bilinIsometryGroup b), ∀ x ∈ X, hEquiv hQ s x ∈ X) :
    X = ⊥ ∨ X = Submodule.span (ZMod 2) {rV} ∨ X = ⊤ := by
  classical
  have : Finite E := Module.finite_of_finite (ZMod 2)
  rcases eq_bot_or_eq_top_of_invariant hb hnd (X.map (LinearMap.fst (ZMod 2) E (ZMod 2)))
    (fun s e he => by
      obtain ⟨x, hx, rfl⟩ := he
      exact ⟨hEquiv hQ s x, hX s x hx, rfl⟩) with hY | hY
  ·
    have hle : ∀ x ∈ X, x = x.2 • rV := fun x hx => by
      have h1 : x.1 ∈ X.map (LinearMap.fst (ZMod 2) E (ZMod 2)) := ⟨x, hx, rfl⟩
      rw [hY, Submodule.mem_bot] at h1
      conv_lhs => rw [eq_fst_add_smul_rV x, h1]
      rw [Prod.mk_zero_zero, zero_add]
    by_cases hr : rV ∈ X
    · refine Or.inr (Or.inl (le_antisymm (fun x hx => ?_) ?_))
      · rw [hle x hx]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hr
    · refine Or.inl (eq_bot_iff.mpr fun x hx => ?_)
      rw [Submodule.mem_bot, hle x hx]
      rcases zmod_two_cases x.2 with h | h
      · rw [h, zero_smul]
      · exact absurd (by rwa [hle x hx, h, one_smul] at hx) hr
  ·
    have hsurj : ∀ e : E, ∃ c : ZMod 2, (e, c) ∈ X := fun e => by
      have h1 : e ∈ X.map (LinearMap.fst (ZMod 2) E (ZMod 2)) := hY ▸ Submodule.mem_top
      obtain ⟨x, hx, rfl⟩ := h1
      exact ⟨x.2, hx⟩
    by_cases hr : rV ∈ X
    · refine Or.inr (Or.inr (eq_top_iff.mpr fun v _ => ?_))
      obtain ⟨c, hc⟩ := hsurj v.1
      have hv : v = (v.1, c) + (v.2 + c) • rV := by
        refine Prod.ext ?_ ?_
        · simp [rV]
        · simp only [Prod.snd_add, Prod.smul_snd, rV, smul_eq_mul, mul_one]
          have key : ∀ t c : ZMod 2, t = c + (t + c) := by decide
          exact key _ _
      rw [hv]
      exact X.add_mem hc (X.smul_mem _ hr)
    · exfalso
      have hor : ∀ v, v ∉ X → v + rV ∈ X := fun v hv => by
        obtain ⟨c, hc⟩ := hsurj v.1
        rcases zmod_two_cases (v.2 + c) with h | h
        · exact absurd (by
            have hv' : v = (v.1, c) := Prod.ext rfl (eq_of_add_eq_zero_zmod2 h)
            rwa [hv']) hv
        · have hv' : v + rV = (v.1, c) := by
            refine Prod.ext (by simp [rV]) ?_
            simp only [Prod.snd_add, rV]
            have key : ∀ t c : ZMod 2, t + c = 1 → t + 1 = c := by decide
            exact key _ _ h
          rw [hv']
          exact hc
      have hiff : ∀ (s : bilinIsometryGroup b) v, hEquiv hQ s v ∈ X ↔ v ∈ X := fun s v =>
        ⟨fun h => by
          have h1 := hX s⁻¹ _ h
          rwa [hEquiv_inv_apply] at h1, hX s v⟩
      let ℓ : (E × ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' (fun v => if v ∈ X then 0 else 1)
        fun v w => by
          by_cases hv : v ∈ X <;> by_cases hw : w ∈ X
          · simp [hv, hw, X.add_mem hv hw]
          · have : v + w ∉ X := fun h => hw (by
              have h1 := X.sub_mem h hv
              rwa [add_sub_cancel_left] at h1)
            simp [hv, hw, this]
          · have : v + w ∉ X := fun h => hv (by
              have h1 := X.sub_mem h hw
              rwa [add_sub_cancel_right] at h1)
            simp [hv, hw, this]
          · have : v + w ∈ X := by
              have h1 := X.add_mem (hor v hv) (hor w hw)
              rwa [show v + rV + (w + rV) = v + w + (rV + rV) by abel,
                add_self_eq_zero_zmod_two, add_zero] at h1
            simp only [hv, hw, this, ite_true, ite_false]
            rfl
      have h0 := eq_zero_of_invariant_linear_V hb hnd hQ hE (ℓ.toZModLinearMap 2)
        (fun s w t => by
          change (if hEquiv hQ s (w, t) ∈ X then (0 : ZMod 2) else 1) =
            if (w, t) ∈ X then 0 else 1
          rw [if_congr (hiff s (w, t)) rfl rfl]) rV
      change (if rV ∈ X then (0 : ZMod 2) else 1) = 0 at h0
      simp only [hr, ite_false] at h0
      exact absurd h0 (by decide)

theorem mem_orthogonalGroup_of_normalizes [FiniteDimensional (ZMod 2) E] (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (hQ : QuadraticMap.polarBilin Q = b) (hE : 4 < Nat.card E)
    (L : (E × ZMod 2) ≃ₗ[ZMod 2] (E × ZMod 2))
    (hL : ∀ s : bilinIsometryGroup b,
      L * hEquiv hQ s * L⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q)) :
    L ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q) := by
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have hq : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup (qForm Q), ∀ v, qV Q (g v) = qV Q v :=
    fun g hg v => by
      rw [← qForm_apply, ← qForm_apply]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  obtain ⟨β, hβ⟩ := exists_eq_mul_qV_of_invariant hb hnd hQ hE (f := fun v => qV Q (L v))
    (b.compl₁₂ ((LinearMap.fst (ZMod 2) E (ZMod 2)) ∘ₗ L.toLinearMap)
      ((LinearMap.fst (ZMod 2) E (ZMod 2)) ∘ₗ L.toLinearMap))
    (fun v w => by
      simp only [map_add, qV_add hQ]
      rfl)
    (fun s w t => by
      have h := hq _ (hL s) (L (w, t))
      rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply, show L⁻¹ (L (w, t)) = (w, t) from
        L.symm_apply_apply (w, t)] at h)
  have h1 := hβ (L.symm rV)
  simp only [L.apply_symm_apply, qV, rV, QuadraticMap.map_zero, zero_add] at h1
  have hβ1 : β = 1 := by
    rcases zmod_two_cases β with h | h
    · rw [h, zero_mul] at h1
      exact absurd h1 (by decide)
    · exact h
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
    rw [qForm_apply, qForm_apply, hβ v, hβ1, one_mul]

theorem eq_bot_of_normal_isPGroup [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (N : Subgroup (bilinIsometryGroup b)) (hN : N.Normal) (hp : IsPGroup 2 N) : N = ⊥ := by
  classical
  have : Finite E := Module.finite_of_finite (ZMod 2)
  let _ : MulAction N E :=
    { smul := fun n x => sE (n : bilinIsometryGroup b) x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have hcard : Nat.card E = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hE, Nat.card_zmod]
    norm_num
  have hmod := hp.card_modEq_card_fixedPoints E
  have h0 : (0 : E) ∈ MulAction.fixedPoints N E := fun n => map_zero (sE (n : bilinIsometryGroup b))
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ MulAction.fixedPoints N E, x ≠ 0 := by
    by_contra! h
    have h1 : MulAction.fixedPoints N E = {0} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨h0, h⟩
    have h2 : Nat.card ({0} : Set E) = 1 := Nat.card_unique
    rw [hcard, h1, h2] at hmod
    exact absurd hmod (by decide)
  let F : Submodule (ZMod 2) E :=
    { carrier := {y | ∀ n : N, sE (n : bilinIsometryGroup b) y = y}
      add_mem' := fun {y z} hy hz n => by rw [map_add, hy n, hz n]
      zero_mem' := fun n => map_zero _
      smul_mem' := fun c y hy n => by rw [map_smul, hy n] }
  have hF : F = ⊤ := by
    refine (eq_bot_or_eq_top_of_invariant hb hnd F fun s y hy n => ?_).resolve_left fun h => ?_
    · have hn : s⁻¹ * (n : bilinIsometryGroup b) * s ∈ N := by
        have := hN.conj_mem _ n.2 s⁻¹
        rwa [inv_inv] at this
      have h1 := hy ⟨_, hn⟩
      change sE (s⁻¹ * (n : bilinIsometryGroup b) * s) y = y at h1
      calc sE (n : bilinIsometryGroup b) (sE s y) =
            sE s (sE (s⁻¹ * (n : bilinIsometryGroup b) * s) y) := by
            rw [← sE_mul, ← sE_mul, show s * (s⁻¹ * (n : bilinIsometryGroup b) * s) =
              (n : bilinIsometryGroup b) * s by group]
        _ = sE s y := by rw [h1]
    · have hxF : x ∈ F := fun n => hx n
      rw [h, Submodule.mem_bot] at hxF
      exact hx0 hxF
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  refine Subtype.ext (gl_ext fun y => ?_)
  have hy : y ∈ F := hF ▸ Submodule.mem_top
  exact hy ⟨n, hn⟩

end Orth

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
