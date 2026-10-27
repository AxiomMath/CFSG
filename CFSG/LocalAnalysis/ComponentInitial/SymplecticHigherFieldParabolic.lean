module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSp

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.AGLEmbedding.ParabAutIrr
open CFSG.LieType.Universal.SpecialLinear
open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fieldSp_dotW {r : ℕ} (σ : K ≃+* K)
    (w : SymplecticTorusWeyl.signedPermGroup r) : fieldSp r K σ (dotW K w) = dotW K w := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSp, coe_dotW]
  have hsign : ∀ x,
      σ (dotSign (K := K) (w : Equiv.Perm (Fin r ⊕ Fin r)) x) =
        dotSign (K := K) (w : Equiv.Perm (Fin r ⊕ Fin r)) x := by
    intro x
    rcases x with i | i
    · simp only [dotSign, Sum.elim_inl, map_one]
    · simp only [dotSign, Sum.elim_inr]
      rcases (w : Equiv.Perm (Fin r ⊕ Fin r)) (Sum.inr i) with j | j <;>
        simp [map_neg, map_one]
  ext i j
  rw [Matrix.map_apply, signedPerm_apply]
  by_cases h : i = (w : Equiv.Perm (Fin r ⊕ Fin r)) j
  · rw [if_pos h, hsign j]
  · rw [if_neg h, map_zero]

theorem map_fieldSp_eq_of_borel_le {r : ℕ} (σ : K ≃+* K) {P : Subgroup (StatedSp r K)}
    (hP : borelSubgroup r K ≤ P) : P.map (fieldSp r K σ).toMonoidHom = P := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y ⟨x, hxP, rfl⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_spBruhatCell x
    have hwP : dotW K w ∈ P := by
      have h' : dotW K w = b₁⁻¹ * (b₁ * dotW K w * b₂) * b₂⁻¹ := by group
      rw [h']
      exact P.mul_mem (P.mul_mem (P.inv_mem (hP hb₁)) hxP) (P.inv_mem (hP hb₂))
    have hdot : (MulEquiv.toMonoidHom (fieldSp r K σ)) (dotW K w) = dotW K w := by
      simpa only [MulEquiv.coe_toMonoidHom] using fieldSp_dotW σ w
    rw [map_mul, map_mul, hdot]
    exact P.mul_mem (P.mul_mem (hP (fieldSp_mem_borelSubgroup σ hb₁)) hwP)
      (hP (fieldSp_mem_borelSubgroup σ hb₂))
  · exact le_of_eq (Subgroup.card_map_of_injective (fieldSp r K σ).injective).symm

theorem map_eq_of_normalizer_le (B : StatedSp 2 K) (σ : K ≃+* K)
    (S : Sylow 2 (StatedSp 2 K))
    (hS : (S : Subgroup (StatedSp 2 K)).map (MulAut.conj B * fieldSp 2 K σ).toMonoidHom = S)
    {P : Subgroup (StatedSp 2 K)}
    (hP : Subgroup.normalizer ((S : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) ≤ P) :
    P.map (MulAut.conj B * fieldSp 2 K σ).toMonoidHom = P := by
  classical
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := K) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 K) Q S
  have hSU : (S : Subgroup (StatedSp 2 K)) =
      (unipotent 2 K).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hQ]
    rfl
  have hφU : (unipotent 2 K).map (fieldSp 2 K σ).toMonoidHom = unipotent 2 K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact fieldSp_mem_unipotent σ hu
    · exact le_of_eq (Subgroup.card_map_of_injective (fieldSp 2 K σ).injective).symm
  have hNB : Subgroup.normalizer (S : Set (StatedSp 2 K)) =
      (borelSubgroup 2 K).map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.map_equiv_normalizer_eq (H := unipotent 2 K) (MulAut.conj g)
    rw [normalizer_unipotent] at h
    rw [← hSU] at h
    exact h.symm
  have hcancel : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
      MonoidHom.id (StatedSp 2 K) := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hB_le : borelSubgroup 2 K ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    have h1 : (borelSubgroup 2 K).map (MulAut.conj g).toMonoidHom ≤ P := by
      rw [← hNB]
      exact hP
    have h2 : ((borelSubgroup 2 K).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom ≤ P.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono h1
    rw [Subgroup.map_map, hcancel, Subgroup.map_id] at h2
    exact h2
  have hN : g⁻¹ * B * fieldSp 2 K σ g ∈
      Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ (unipotent 2 K).map (fieldSp 2 K σ).toMonoidHom := by
        rw [hφU]
        exact hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
      change (MulAut.conj (g⁻¹ * B * fieldSp 2 K σ g)) (fieldSp 2 K σ u) ∈
        unipotent 2 K
      have hgu : g * u * g⁻¹ ∈ (S : Subgroup (StatedSp 2 K)) := by
        rw [hSU]
        exact Subgroup.mem_map.mpr ⟨u, hu, by simp [MulAut.conj_apply]⟩
      have hαS : (MulAut.conj B * fieldSp 2 K σ) (g * u * g⁻¹) ∈
          (S : Subgroup (StatedSp 2 K)) := by
        have hmem : (MulAut.conj B * fieldSp 2 K σ) (g * u * g⁻¹) ∈
            (S : Subgroup (StatedSp 2 K)).map
              (MulAut.conj B * fieldSp 2 K σ).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨_, hgu, rfl⟩
        rwa [hS] at hmem
      rw [hSU] at hαS
      obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hαS
      have hconj : (MulAut.conj (g⁻¹ * B * fieldSp 2 K σ g)) (fieldSp 2 K σ u) =
          (MulAut.conj g⁻¹) ((MulAut.conj B * fieldSp 2 K σ) (g * u * g⁻¹)) := by
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        simp only [map_mul, map_inv]
        group
      rw [hconj, ← hveq]
      change (MulAut.conj g⁻¹) ((MulAut.conj g) v) ∈ unipotent 2 K
      have hcancel' : (MulAut.conj g⁻¹) ((MulAut.conj g) v) = v := by
        simp only [MulAut.mul_apply, MulAut.conj_apply]
        group
      rw [hcancel']
      exact hv
    · exact le_of_eq (Subgroup.card_map_of_injective
        (MulAut.conj (g⁻¹ * B * fieldSp 2 K σ g)).injective).symm
  have hhB : g⁻¹ * B * fieldSp 2 K σ g ∈ borelSubgroup 2 K := by
    rw [← normalizer_unipotent]
    exact hN
  have hα_le : P.map (MulAut.conj B * fieldSp 2 K σ).toMonoidHom ≤ P := by
    rintro y ⟨x, hxP, rfl⟩
    change (MulAut.conj B * fieldSp 2 K σ) x ∈ P
    have hxQ : g⁻¹ * x * g ∈ P.map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hxP, by simp [MulAut.conj_apply]⟩
    have hφfix : (P.map (MulAut.conj g⁻¹).toMonoidHom).map
        (fieldSp 2 K σ).toMonoidHom = P.map (MulAut.conj g⁻¹).toMonoidHom :=
      map_fieldSp_eq_of_borel_le σ hB_le
    have hφmem : fieldSp 2 K σ (g⁻¹ * x * g) ∈
        P.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← hφfix]
      exact Subgroup.mem_map.mpr ⟨_, hxQ, rfl⟩
    obtain ⟨x', hx'P, hx'eq⟩ := Subgroup.mem_map.mp hφmem
    have hαx : (MulAut.conj B * fieldSp 2 K σ) x =
        g * (g⁻¹ * B * fieldSp 2 K σ g) * fieldSp 2 K σ (g⁻¹ * x * g) *
          (g⁻¹ * B * fieldSp 2 K σ g)⁻¹ * g⁻¹ := by
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      simp only [map_mul, map_inv]
      group
    rw [hαx, ← hx'eq]
    have hghN : g * (g⁻¹ * B * fieldSp 2 K σ g) * g⁻¹ ∈
        Subgroup.normalizer (S : Set (StatedSp 2 K)) := by
      rw [hNB]
      exact Subgroup.mem_map.mpr ⟨_, hhB, by simp [MulAut.conj_apply]⟩
    have hghP : g * (g⁻¹ * B * fieldSp 2 K σ g) * g⁻¹ ∈ P := hP hghN
    have heq : g * (g⁻¹ * B * fieldSp 2 K σ g) *
          (MulAut.conj g⁻¹) x' * (g⁻¹ * B * fieldSp 2 K σ g)⁻¹ * g⁻¹ =
        (g * (g⁻¹ * B * fieldSp 2 K σ g) * g⁻¹) * x' *
          (g * (g⁻¹ * B * fieldSp 2 K σ g) * g⁻¹)⁻¹ := by
      simp only [MulAut.mul_apply, MulAut.conj_apply]
      group
    change g * (g⁻¹ * B * fieldSp 2 K σ g) * (MulAut.conj g⁻¹) x' *
        (g⁻¹ * B * fieldSp 2 K σ g)⁻¹ * g⁻¹ ∈ P
    rw [heq]
    exact P.mul_mem (P.mul_mem hghP hx'P) (P.inv_mem hghP)
  refine Subgroup.eq_of_le_of_card_ge hα_le ?_
  exact le_of_eq (Subgroup.card_map_of_injective
    (MulAut.conj B * fieldSp 2 K σ).injective).symm

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
