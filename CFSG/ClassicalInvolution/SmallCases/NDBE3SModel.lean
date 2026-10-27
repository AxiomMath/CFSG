module

public import CFSG.ClassicalInvolution.SmallCases.NDBE3SAlpha
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Aut
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution

public section

namespace CFSG.ClassicalInvolution.NDB.SpinStd

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.NDB.FourFrame QuadraticMap
open scoped MatrixGroups

section HypFrame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}
  (F₀ : HypFrame Q m)

theorem vec_mem_span_fst {i j : Fin m} (hij : i ≠ j) (s : Bool) :
    F₀.vec i s ∈ (F₀.toFrame hij true false).span := by
  cases s
  · exact Frame.f₁_mem_span (F₀.toFrame hij true false)
  · exact Frame.e₁_mem_span (F₀.toFrame hij true false)

theorem vec_mem_span_snd {i j : Fin m} (hij : i ≠ j) (s : Bool) :
    F₀.vec j s ∈ (F₀.toFrame hij true false).span := by
  cases s
  · exact Frame.e₂_mem_span (F₀.toFrame hij true false)
  · exact Frame.f₂_mem_span (F₀.toFrame hij true false)

theorem vec_mem_perp {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (s : Bool) :
    F₀.vec k s ∈ (F₀.toFrame hij true false).perp := by
  rw [Frame.mem_perp_iff, Frame.coords_apply]
  have h1 : ∀ t, polar Q (F₀.vec k s) (F₀.vec i t) = 0 := fun t => F₀.polar_vec_of_ne hki s t
  have h2 : ∀ t, polar Q (F₀.vec k s) (F₀.vec j t) = 0 := fun t => F₀.polar_vec_of_ne hkj s t
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [HypFrame.toFrame, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂, h1, h2]

@[expose] def vecPair (i : Fin m) : HypPair Q :=
  ⟨F₀.vec i true, F₀.vec i false, F₀.map_vec i true, F₀.map_vec i false, F₀.polar_vec_not i true⟩

theorem map_vec_add (i : Fin m) : Q (F₀.vec i true + F₀.vec i false) = 1 := by
  have h := F₀.polar_vec_not i true
  rw [Bool.not_true] at h
  rw [QuadraticMap.map_add Q, F₀.map_vec, F₀.map_vec, h]
  ring

end HypFrame

section Map

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)

@[expose] def mapPair (P : HypPair Q) : HypPair Q :=
  ⟨g P.e, g P.f, by rw [map_of_mem hg, P.Q_e], by rw [map_of_mem hg, P.Q_f],
    by rw [polar_map_of_mem hg, P.polar_ef]⟩

theorem map_mem_span_map (fr : Frame Q) {x : V} (hx : x ∈ fr.span) : g x ∈ (fr.map hg).span := by
  obtain ⟨X, rfl⟩ := hx
  exact ⟨X, Frame.map_incl fr hg X⟩

theorem map_mem_perp_map (fr : Frame Q) {x : V} (hx : x ∈ fr.perp) : g x ∈ (fr.map hg).perp := by
  rw [Frame.mem_perp_iff, Frame.map_coords, show g⁻¹ (g x) = x from g.symm_apply_apply x]
  exact (Frame.mem_perp_iff fr).mp hx

end Map

section Lift

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem le_commutator_of_layerGenOn {S : Submodule F V} (h : LayerGenOn Q S) :
    elemOn Q S ≤ ⁅elemOn Q S, elemOn Q S⁆ := by
  obtain ⟨𝓗, hH, hle⟩ := h
  refine hle.trans (iSup₂_le fun H hH' => ?_)
  obtain ⟨hHle, hHq, -⟩ := hH H hH'
  rw [← commutator_self_of_perfect hHq.1]
  exact Subgroup.commutator_mono hHle hHle

theorem top_le_of_pieces (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] {J₁ J₂ J₃ : Subgroup (V ≃ₗ[F] V)}
    (hJ₁ : J₁ ≤ elementaryGroup Q) (hJ₂ : J₂ ≤ elementaryGroup Q) (hJ₃ : J₃ ≤ elementaryGroup Q)
    (hp₁ : ⁅J₁, J₁⁆ = J₁) (hp₂ : ⁅J₂, J₂⁆ = J₂) (hp₃ : ⁅J₃, J₃⁆ = J₃)
    (hgen : elementaryGroup Q ≤ J₁ ⊔ J₂ ⊔ J₃) {w₁ w₂ w₃ : spinGroup Q}
    (hc₁ : ∀ g ∈ J₁, g * spinAction Q w₁ = spinAction Q w₁ * g)
    (hc₂ : ∀ g ∈ J₂, g * spinAction Q w₂ = spinAction Q w₂ * g)
    (hc₃ : ∀ g ∈ J₃, g * spinAction Q w₃ = spinAction Q w₃ * g) :
    Subgroup.centralizer ({w₁} : Set (spinGroup Q)) ⊔
        Subgroup.centralizer ({w₂} : Set (spinGroup Q)) ⊔
          Subgroup.centralizer ({w₃} : Set (spinGroup Q)) = ⊤ := by
  set θ := spinAction Q with hθ
  have hker : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hcen : ∀ (J : Subgroup (V ≃ₗ[F] V)) (w : spinGroup Q), (∀ g ∈ J, g * θ w = θ w * g) →
      ⁅J.comap θ, J.comap θ⁆ ≤ Subgroup.centralizer ({w} : Set (spinGroup Q)) := by
    intro J w hc g hg
    have hfix := alpha_fixes_commutators (MulAut.conj w⁻¹) (S := J.comap θ) (fun s hs => by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, MulAut.conj_apply, map_mul, map_mul, map_inv,
        inv_inv]
      have h1 := hc (θ s) hs
      calc (θ s)⁻¹ * ((θ w)⁻¹ * θ s * θ w) = (θ s)⁻¹ * ((θ w)⁻¹ * (θ s * θ w)) := by group
        _ = (θ s)⁻¹ * ((θ w)⁻¹ * (θ w * θ s)) := by rw [h1]
        _ = 1 := by group) g hg
    rw [MulAut.conj_apply, inv_inv] at hfix
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * w = w * (w⁻¹ * g * w) := by group
      _ = w * g := by rw [hfix]
  set M : Subgroup (spinGroup Q) := ⁅J₁.comap θ, J₁.comap θ⁆ ⊔ ⁅J₂.comap θ, J₂.comap θ⁆ ⊔
    ⁅J₃.comap θ, J₃.comap θ⁆ with hM
  have hlift : ∀ (J : Subgroup (V ≃ₗ[F] V)), J ≤ elementaryGroup Q → ⁅J, J⁆ = J →
      ⁅J.comap θ, J.comap θ⁆ ≤ M → J ≤ M.map θ := by
    intro J hJ hp hJM g hg
    obtain ⟨s, hs, rfl⟩ := exists_lift_commutator θ (hJ.trans hrange.ge) hp g hg
    exact ⟨s, hJM hs, rfl⟩
  have h₁ := hlift J₁ hJ₁ hp₁ (le_sup_left.trans le_sup_left)
  have h₂ := hlift J₂ hJ₂ hp₂ (le_sup_right.trans le_sup_left)
  have h₃ := hlift J₃ hJ₃ hp₃ le_sup_right
  have hdec : ∀ x : spinGroup Q, ∃ m ∈ M, ∃ z ∈ Subgroup.center (spinGroup Q), x = m * z := by
    intro x
    have hx : θ x ∈ M.map θ := (sup_le (sup_le h₁ h₂) h₃) (hgen (hrange ▸ ⟨x, rfl⟩))
    obtain ⟨m, hm, hmx⟩ := hx
    refine ⟨m, hm, m⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  have htop : (⊤ : Subgroup (spinGroup Q)) ≤ M := by
    rw [← Group.IsPerfect.commutator_eq_top (G := spinGroup Q), commutator, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec x
    obtain ⟨m', hm', z', hz', rfl⟩ := hdec y
    rw [commutatorElement_mul_central hz hz', commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')
  refine eq_top_iff.mpr (htop.trans (sup_le (sup_le ?_ ?_) ?_))
  · exact (hcen J₁ w₁ hc₁).trans (le_sup_left.trans le_sup_left)
  · exact (hcen J₂ w₂ hc₂).trans (le_sup_right.trans le_sup_left)
  · exact (hcen J₃ w₃ hc₃).trans le_sup_right

end Lift

section LongRoot

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
  (F₀ : HypFrame Q m)

theorem longSL2_injective {i j : Fin m} (hij : i ≠ j) :
    Function.Injective (F₀.longSL2 hij true false) := by
  intro A B h
  apply (F₀.toFrame hij true false).La_injective
  rw [← ModelFacts.spinAction_comp_longSL2 F₀ hij true false, MonoidHom.comp_apply,
    MonoidHom.comp_apply, h]

theorem spinAction_longSL2_neg_one {i j : Fin m} (hij : i ≠ j) :
    spinAction Q (F₀.longSL2 hij true false (-1)) = (F₀.toFrame hij true false).La (-1) := by
  rw [← ModelFacts.spinAction_comp_longSL2 F₀ hij true false, MonoidHom.comp_apply]

theorem eq_longSL2_neg_one (h2 : (2 : F) ≠ 0) {i j : Fin m} (hij : i ≠ j) {y : spinGroup Q}
    (hy : y ∈ (F₀.longSL2 hij true false).range) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    y = F₀.longSL2 hij true false (-1) := by
  obtain ⟨A, rfl⟩ := hy
  have hk : ringChar F ≠ 2 := fun h => h2 (by
    have h1 := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at h1
    exact_mod_cast h1)
  have hA2 : A ^ 2 = 1 := longSL2_injective F₀ hij (by rw [map_pow, _root_.sq, hy2, map_one])
  rcases (CFSG.LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hk A).mp hA2 with rfl | rfl
  · exact absurd (map_one _) hy1
  · rfl

end LongRoot

end CFSG.ClassicalInvolution.NDB.SpinStd
