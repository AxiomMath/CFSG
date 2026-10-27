module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphHom
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (mul_conj_mul_inv conj_range_normal)

section Sub

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {H : Subgroup (GL ι K)}

theorem ClU.fix_of_lift_sub
    (hinj : Function.Injective (MulAut.conj : StatedProj H →* MulAut (StatedProj H)))
    {i : MulAut (StatedProj H)} {R : Subgroup (MulAut (StatedProj H))}
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * i = i * y)
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R)
    (φ : H →* H) (hφi : Function.Injective φ) (hφ : ∀ g, i (projH H g) = projH H (φ g))
    {M Q : Subgroup H} (hMF : M ≤ MonoidHom.eqLocus φ (MonoidHom.id H))
    (hMn : ∀ x ∈ MonoidHom.eqLocus φ (MonoidHom.id H), ∀ q ∈ M, x * q * x⁻¹ ∈ M)
    (hQM : Q ≤ M) (hQn : ∀ x ∈ M, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hQq : IsQuasisimple Q) {y} (hy : y ∈ R) {g : H} (hg : g ∈ Q) :
    y (projH H g) = projH H g := by
  set δ : H ≃* H := MulEquiv.ofBijective φ ⟨hφi, Finite.injective_iff_surjective.1 hφi⟩
  have hMF' : M ≤ ClassicalInvolution.Balance.fixedGroup δ := fun q hq => hMF hq
  have hQ : Open.IsComponentOf Q (ClassicalInvolution.Balance.fixedGroup δ) := by
    refine ⟨hQM.trans hMF', ?_, ⟨hQq.1.commutator_eq_top, hQq.2.1⟩⟩
    refine Open.IsSubnormal.step hQM ?_
      (ClassicalInvolution.isSubnormal_of_normal_subgroupOf hMF' ?_)
    · rw [Subgroup.normal_subgroupOf_iff hQM]
      exact fun q x hq hx => hQn x hx q hq
    · rw [Subgroup.normal_subgroupOf_iff hMF']
      exact fun q x hq hx => hMn x hx q hq
  have hker : (conjProjH H).ker ≤ center H := by
    intro x hx
    have h1 : projH H x = 1 := hinj (by rw [map_one]; exact hx)
    exact scalars_subgroupOf_le_center ((QuotientGroup.eq_one_iff _).1 h1)
  have hδ : ∀ x : H, i * conjProjH H (1 * x * 1⁻¹) * i⁻¹ = conjProjH H (1 * δ x * 1⁻¹) :=
    fun x => by
      simp only [one_mul, inv_one, mul_one]
      change i * MulAut.conj (projH H x) * i⁻¹ = MulAut.conj (projH H (φ x))
      rw [mul_conj_mul_inv, hφ]
  have hmain := ClassicalInvolution.Balance.isComponentOf_map_centralizer hker 1 i δ hδ hQ
  have e : (conjProjH H).comp (MulAut.conj (1 : H)).toMonoidHom = conjProjH H := by
    ext
    simp
  rw [e] at hmain
  have : (conjProjH H).range.Normal := by
    have h : (conjProjH H).range = (MulAut.conj : StatedProj H →* MulAut (StatedProj H)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr projH_surjective,
        ← MonoidHom.range_eq_map]
    rw [h]
    exact conj_range_normal
  have hRconj : ∀ s ∈ (conjProjH H).range ⊓ centralizer ({i} : Set _), Odd (orderOf s) →
      ∀ y ∈ R, s * y * s⁻¹ ∈ R := by
    rintro _ ⟨⟨x, rfl⟩, hxi⟩ hodd y hy
    have hxi' := mem_centralizer_singleton_iff.1 hxi
    have hfix : i (projH H x) = projH H x := by
      apply hinj
      rw [← mul_conj_mul_inv]
      change i * conjProjH H x * i⁻¹ = conjProjH H x
      rw [← hxi', mul_inv_cancel_right]
    have hodd' : Odd (orderOf (projH H x)) := by
      rwa [← orderOf_injective _ hinj (projH H x)]
    exact hRc _ hfix hodd' y hy
  have h := commute_of_isComponentOf hRodd hRi hRconj hmain hy ⟨g, hg, rfl⟩
  apply hinj
  rw [← mul_conj_mul_inv]
  change y * conjProjH H g * y⁻¹ = conjProjH H g
  rw [h, mul_inv_cancel_right]

end Sub

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ClU.uLift_injective (A : uU h n) (φ : K ≃+* K) : Function.Injective (uLift h A φ) := by
  intro g₁ g₂ e
  have e' : (A : GL (Fin n) K) * glAut φ (g₁ : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ =
      (A : GL (Fin n) K) * glAut φ (g₂ : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ :=
    congrArg Subtype.val e
  exact Subtype.ext ((glAut φ).injective (mul_left_cancel (mul_right_cancel e')))

theorem ClU.graph_fix_of_components (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {s : K}
    (hs : s ≠ 0) {R : GL (Fin n) h.fixedField}
    (hR : (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
      s • ((P.map h.bar)ᵀ * P))
    {A : uU h n} {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {Y : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} (hYodd : Odd (Nat.card Y))
    (hYi : ∀ y ∈ Y, y * (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) =
      (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) * y)
    (hYc : ∀ x, (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h) :
        MulAut (StatedProj (StatedSU n (p ^ f) K))) x = x →
      Odd (orderOf x) → ∀ y ∈ Y, MulAut.conj x * y * (MulAut.conj x)⁻¹ ∈ Y)
    {Ω : Subgroup (GL (Fin n) h.fixedField)} (hΩ1 : Ω ≤ iso1 h R)
    (hΩ : ∀ (Z : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Z : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Z =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) → ∀ X ∈ Ω, Z * X * Z⁻¹ ∈ Ω)
    (hperf : ⁅Ω, Ω⁆ = Ω) {m : ℕ} {L : Fin m → Subgroup (GL (Fin n) h.fixedField)}
    (hsup : (⨆ i, L i) = Ω)
    (hL : ∀ i, IsQuasisimple (L i) ∧ L i ≤ Ω ∧ ∀ x ∈ Ω, ∀ l ∈ L i, x * l * x⁻¹ ∈ L i)
    {D : uU h n} {τ : K ≃+* K}
    (hy : uConjAut h (by omega) D * uFieldAut h (by omega) τ ∈ Y)
    {X : iso1 h R} (hX : (X : GL (Fin n) h.fixedField) ∈ Ω) :
    ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((gHom h hPPi hPiP hs hR X : StatedSU n (p ^ f) K) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map τ *
        (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((gHom h hPPi hPiP hs hR X : StatedSU n (p ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) := by
  have := h.finite
  set φ := uLift h A (barEq h) with hφdef
  have hφ : ∀ g, (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h) :
      MulAut (StatedProj (StatedSU n (p ^ f) K))) (projH (StatedSU n (p ^ f) K) g) =
        projH (StatedSU n (p ^ f) K) (φ g) :=
    fun g => uLift_proj h (by omega) A (barEq h) g
  set G := gHom h hPPi hPiP hs hR with hG
  set FΩ := (Ω.subgroupOf (iso1 h R)).map G with hFΩ
  have hF1 : FΩ ≤ MonoidHom.eqLocus φ (MonoidHom.id _) := by
    rintro _ ⟨X', -, rfl⟩
    exact uLift_gHom h hPPi hPiP hs hR hb hbP X'
  have hF2 : ∀ x ∈ MonoidHom.eqLocus φ (MonoidHom.id _), ∀ g ∈ FΩ, x * g * x⁻¹ ∈ FΩ := by
    intro x hx g hg
    refine conj_mem_map_gHom h hPPi hPiP hs hR (by omega) hb hbP hΩ1 hΩ ?_ hg
    have e : x⁻¹ * φ x = 1 := by
      rw [show φ x = x from hx, inv_mul_cancel]
    rw [e]
    exact one_mem _
  have hfixL : ∀ i, ∀ g ∈ ((L i).subgroupOf (iso1 h R)).map G,
      (uConjAut h (by omega) D * uFieldAut h (by omega) τ :
        MulAut (StatedProj (StatedSU n (p ^ f) K)))
        (projH _ g) = projH _ g := by
    intro i g hg
    obtain ⟨hq, hLΩ, hLn⟩ := hL i
    set Q := ((L i).subgroupOf (iso1 h R)).map G with hQ
    have hQF : Q ≤ FΩ := map_mono (fun x hx => hLΩ hx)
    have hQq : IsQuasisimple Q := by
      have e1 : (L i).subgroupOf (iso1 h R) ≃* L i :=
        subgroupOfEquivOfLe (hLΩ.trans hΩ1)
      have e2 : (L i).subgroupOf (iso1 h R) ≃* Q :=
        ((L i).subgroupOf (iso1 h R)).equivMapOfInjective G (gHom_injective h hPPi hPiP hs hR)
      exact LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hq
    have hQn : ∀ x ∈ FΩ, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
      rintro _ ⟨X', hX', rfl⟩ _ ⟨l, hl, rfl⟩
      exact ⟨X' * l * X'⁻¹, hLn _ hX' _ hl, by simp only [map_mul, map_inv]⟩
    exact ClU.fix_of_lift_sub hinj hYodd hYi hYc φ (ClU.uLift_injective h A (barEq h)) hφ hF1
      hF2 hQF hQn hQq hy hg
  have hΩsup : (Ω.subgroupOf (iso1 h R)) = ⨆ i, (L i).subgroupOf (iso1 h R) := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : GL (Fin n) h.fixedField) ∈ ⨆ i, L i := by rw [hsup]; exact hx
      have hmap : (⨆ i, (L i).subgroupOf (iso1 h R)).map (iso1 h R).subtype = ⨆ i, L i := by
        rw [Subgroup.map_iSup]
        exact iSup_congr fun i => by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hΩ1)]
      rw [← hmap] at hx'
      obtain ⟨x', hx', e⟩ := hx'
      rwa [← Subtype.ext e]
    · exact iSup_le fun i x hx => (hL i).2.1 hx
  have hFsup : FΩ = ⨆ i, ((L i).subgroupOf (iso1 h R)).map G := by
    rw [hFΩ, hΩsup, Subgroup.map_iSup]
  have hfix : ∀ g ∈ FΩ, (uConjAut h (by omega) D * uFieldAut h (by omega) τ :
      MulAut (StatedProj (StatedSU n (p ^ f) K))) (projH (StatedSU n (p ^ f) K) g) =
        projH (StatedSU n (p ^ f) K) g := by
    have hsubgrp : FΩ ≤ MonoidHom.eqLocus
        ((uConjAut h (by omega) D * uFieldAut h (by omega) τ :
          MulAut (StatedProj (StatedSU n (p ^ f) K))).toMonoidHom.comp
          (projH (StatedSU n (p ^ f) K))) (projH (StatedSU n (p ^ f) K)) := by
      rw [hFsup]
      exact iSup_le fun i g hg => hfixL i g hg
    exact fun g hg => hsubgrp hg
  have hperfA : ⁅Ω.subgroupOf (iso1 h R), Ω.subgroupOf (iso1 h R)⁆ =
      Ω.subgroupOf (iso1 h R) := by
    apply Subgroup.map_injective (iso1 h R).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hΩ1, hperf]
  have hperfF : ⁅FΩ, FΩ⁆ = FΩ := by rw [hFΩ, ← map_commutator, hperfA]
  exact uSemilinear_eq_of_fix h (by omega) hperfF hfix ⟨X, hX, rfl⟩

end CFSG.ComponentClassification.Foote5.OddLieCore
