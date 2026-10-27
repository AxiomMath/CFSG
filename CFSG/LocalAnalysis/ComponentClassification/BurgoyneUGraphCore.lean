module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphHom
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (isSubnormal_subgroupOf_of_normalizes
  mul_conj_mul_inv)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem graph_fix_of_components (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {s : K}
    (hs : s ≠ 0) {R : GL (Fin n) h.fixedField}
    (hR : (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
      s • ((P.map h.bar)ᵀ * P))
    {A : uU h n} {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {Ω : Subgroup (GL (Fin n) h.fixedField)} (hΩ1 : Ω ≤ iso1 h R)
    (hΩ : ∀ (Y : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) → ∀ X ∈ Ω, Y * X * Y⁻¹ ∈ Ω)
    (hperf : ⁅Ω, Ω⁆ = Ω) {m : ℕ} {L : Fin m → Subgroup (GL (Fin n) h.fixedField)}
    (hsup : (⨆ i, L i) = Ω)
    (hL : ∀ i, IsQuasisimple (L i) ∧ L i ≤ Ω ∧ ∀ x ∈ Ω, ∀ l ∈ L i, x * l * x⁻¹ ∈ L i)
    {D : uU h n} {τ : K ≃+* K}
    (hy : uConjAut h (by omega) D * uFieldAut h (by omega) τ ∈
      oddCoreIn B (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)))
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
  have hF1 : ∀ g ∈ FΩ, φ g = g := by
    rintro _ ⟨X', -, rfl⟩
    exact uLift_gHom h hPPi hPiP hs hR hb hbP X'
  have hF2 : ∀ H : StatedSU n (p ^ f) K, H⁻¹ * φ H ∈
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) →
      ∀ g ∈ FΩ, H * g * H⁻¹ ∈ FΩ :=
    fun H hH g hg => conj_mem_map_gHom h hPPi hPiP hs hR (by omega) hb hbP hΩ1 hΩ hH hg
  obtain ⟨hle, hsub⟩ := isSubnormal_map_fixedH hinj hB φ hφ hF1 hF2
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
    have hQim := isQuasisimple_map_conjProjH hinj hQq
    have hQsub : ((Q.map (conjProjH (StatedSU n (p ^ f) K))).subgroupOf
        (B ⊓ centralizer ({uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)} :
          Set _))).IsSubnormal := by
      refine isSubnormal_subgroupOf_of_normalizes (map_mono hQF) ?_ hsub
      rintro _ ⟨x, hx, rfl⟩ _ ⟨q, hq', rfl⟩
      obtain ⟨X', hX', rfl⟩ := hx
      obtain ⟨l, hl, rfl⟩ := hq'
      refine ⟨G X' * G l * (G X')⁻¹, ⟨X' * l * X'⁻¹, ?_, by simp only [map_mul, map_inv]⟩,
        by simp only [map_mul, map_inv]⟩
      exact hLn _ hX' _ hl
    have hc := commute_of_mem_pPrimeCore ((map_mono hQF).trans hle) hQim hQsub
      (even_card_of_isQuasisimple hQim) hy ⟨g, hg, rfl⟩
    apply hinj
    rw [← mul_conj_mul_inv]
    change _ * conjProjH (StatedSU n (p ^ f) K) g * _ = conjProjH (StatedSU n (p ^ f) K) g
    rw [hc, mul_inv_cancel_right]
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

end CFSG.ComponentClassification.Burgoyne.U
