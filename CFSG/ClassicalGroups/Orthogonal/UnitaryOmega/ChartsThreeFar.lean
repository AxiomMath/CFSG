module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.PhanDn CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  {E : QuadExt F K (unitaryInvolution K 2 f)}

theorem normPerm_commute_normBlock_of_fixes {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)}
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i ∈ S, σ i = i) {x : normOmega E n}
    (hx : x ∈ normBlock E n S) : Commute (normPerm E hn σ) x := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hU : (QuadraticMap.polarBilin ((normHypForm E n).comp
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S).subtype)).Nondegenerate :=
    coordSupport_nondegenerate (QR := hypPlane F) (QE := normQuad E)
      (LinearEquiv.refl F ((F × F) × (Fin n → K))) (normHypForm_apply_coord E n)
      (normHypForm_polarBilin_nondegenerate E n) (normQuad_polarBilin_nondegenerate E) S
  have hxSD : ((x : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) ∈
      supportedDerived (normHypForm E n)
        (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) := by
    simp only [normBlock] at hx
    exact Subgroup.mem_subgroupOf.mp hx
  have hgO : ((normPerm E hn σ : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n) :=
    orthDerived_le_orthogonalGroup (Q := normHypForm E n) (normPerm E hn σ).2
  have hgU : ∀ v ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S,
      ((normPerm E hn σ : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v = v := by
    intro v hv
    have hv0 : ∀ j, j ∉ S → v.2 j = 0 := (mem_coordSupport_refl_iff E S v).mp hv
    rw [normPerm_apply E hn σ v]
    refine Prod.ext rfl (funext fun j => ?_)
    dsimp only
    rw [Equiv.Perm.inv_def]
    by_cases hj : j ∈ S
    · rw [(Equiv.symm_apply_eq σ).mpr (hσ j hj).symm]
    · have hinv : σ.symm j ∉ S := by
        intro hmem
        have h1 : σ (σ.symm j) = σ.symm j := hσ _ hmem
        rw [Equiv.apply_symm_apply] at h1
        exact hj (h1 ▸ hmem)
      rw [hv0 (σ.symm j) hinv, hv0 j hj]
  have hpresU : ∀ v ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S,
      ((x : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v ∈
        coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S :=
    fun v hv => supportedDerived_apply_mem hxSD hv
  have hfixP : ∀ v ∈ suppPerp (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S),
      ((x : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v = v :=
    fun v hv => supportedDerived_apply_perp hxSD hv
  exact Subtype.ext (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq
    (Q := normHypForm E n)
    (U := coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)
    hU hgO hgU hpresU hfixP)

theorem commute_anchorBlock_of_two_charts_three {H : Type} [Group H]
    {κ₁ κ₂ : normOmega E 3 →* H} {t : Equiv.Perm (Fin 4) →* H}
    (ht₁ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 3 ↪ Fin 4)) =
      κ₁.comp (normPerm E le_rfl))
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2,
      κ₁ (normPerm E le_rfl (finRotate 3) * normOmegaCast E (by norm_num) y *
          (normPerm E le_rfl (finRotate 3))⁻¹) = κ₂ (normOmegaCast E (by norm_num) y)) :
    ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁, Commute (t (Equiv.swap 2 3)) y := by
  classical
  have h23 : 2 ≤ 3 := by norm_num
  have h33 : 3 ≤ 3 := le_rfl
  have ht01 : t (Equiv.swap (0 : Fin 4) 1) =
      κ₁ (normPerm E h33 (Equiv.swap (0 : Fin 3) 1)) := by
    have h := DFunLike.congr_fun ht₁ (Equiv.swap (0 : Fin 3) 1)
    simp only [MonoidHom.comp_apply] at h
    rw [← h, CFSG.Permutation.viaEmbeddingHom_swap]
    rw [show (Fin.castSuccEmb : Fin 3 ↪ Fin 4) (0 : Fin 3) = (0 : Fin 4) from Fin.ext rfl,
      show (Fin.castSuccEmb : Fin 3 ↪ Fin 4) (1 : Fin 3) = (1 : Fin 4) from Fin.ext rfl]
  have ht23 : t (Equiv.swap (2 : Fin 4) 3) =
      κ₂ (normPerm E h33 (Equiv.swap (1 : Fin 3) 2)) := by
    have h := DFunLike.congr_fun ht₂ (Equiv.swap (1 : Fin 3) 2)
    simp only [MonoidHom.comp_apply] at h
    rw [← h, CFSG.Permutation.viaEmbeddingHom_swap]
    rw [show (Fin.succEmb 3) (1 : Fin 3) = (2 : Fin 4) from Fin.ext rfl,
      show (Fin.succEmb 3) (2 : Fin 3) = (3 : Fin 4) from Fin.ext rfl]
  have hcomm_perm : Commute (Equiv.swap (2 : Fin 4) 3) (Equiv.swap (0 : Fin 4) 1) := by
    show Equiv.swap 2 3 * Equiv.swap 0 1 = Equiv.swap 0 1 * Equiv.swap 2 3
    apply Equiv.ext
    intro x
    fin_cases x <;> decide
  have hcomm_t : Commute (t (Equiv.swap (2 : Fin 4) 3)) (t (Equiv.swap (0 : Fin 4) 1)) :=
    Commute.map hcomm_perm t
  have hblock1 : ∀ b ∈ normBlock E 3 ({1} : Finset (Fin 3)),
      Commute (t (Equiv.swap (2 : Fin 4) 3)) (κ₁ b) := by
    intro b hb
    have hmapP : (normBlock E 3 ({0} : Finset (Fin 3))).map
        (MulAut.conj (normPerm E h33 (finRotate 3))).toMonoidHom = normBlock E 3 {1} := by
      rw [map_normBlock_normPerm (E := E) (n := 3) h33 (finRotate 3) {0},
        Finset.image_singleton]
      rw [show finRotate 3 0 = (1 : Fin 3) from by decide]
    have hb' : b ∈ (normBlock E 3 ({0} : Finset (Fin 3))).map
        (MulAut.conj (normPerm E h33 (finRotate 3))).toMonoidHom := by
      rw [hmapP]
      exact hb
    obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.mp hb'
    have hxb' : b = normPerm E h33 (finRotate 3) * x *
        (normPerm E h33 (finRotate 3))⁻¹ := by
      rw [← hxb]
      rfl
    have hxa : x ∈ anchorBlock E h23 := by
      rw [anchorBlock_eq_normBlock (E := E) (m := 3) h23]
      exact normBlock_mono E 3 (by simp) hx
    have hxr : x ∈ (normOmegaCast E h23).range := hxa
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hxr
    have hxc : Commute (normPerm E h33 (Equiv.swap (1 : Fin 3) 2))
        (normOmegaCast E h23 y) := by
      rw [hy]
      exact normPerm_commute_normBlock_of_fixes (E := E) (n := 3) (S := {0}) h33
        (Equiv.swap (1 : Fin 3) 2) (by decide) hx
    have hmap := Commute.map hxc κ₂
    rw [← ht23] at hmap
    have hpt : κ₁ b = κ₂ (normOmegaCast E h23 y) := by
      rw [hxb', ← hy]
      exact hpoint y
    rw [hpt]
    exact hmap
  have hblock0 : ∀ a ∈ normBlock E 3 ({0} : Finset (Fin 3)),
      Commute (t (Equiv.swap (2 : Fin 4) 3)) (κ₁ a) := by
    intro a ha
    have hmapQ : (normBlock E 3 ({1} : Finset (Fin 3))).map
        (MulAut.conj (normPerm E h33 (Equiv.swap (0 : Fin 3) 1))).toMonoidHom =
        normBlock E 3 {0} := by
      rw [map_normBlock_normPerm (E := E) (n := 3) h33 (Equiv.swap (0 : Fin 3) 1) {1},
        Finset.image_singleton]
      rw [show Equiv.swap (0 : Fin 3) 1 1 = (0 : Fin 3) from Equiv.swap_apply_right _ _]
    have ha' : a ∈ (normBlock E 3 ({1} : Finset (Fin 3))).map
        (MulAut.conj (normPerm E h33 (Equiv.swap (0 : Fin 3) 1))).toMonoidHom := by
      rw [hmapQ]
      exact ha
    obtain ⟨z, hz, hza⟩ := Subgroup.mem_map.mp ha'
    have hza' : a = normPerm E h33 (Equiv.swap (0 : Fin 3) 1) * z *
        (normPerm E h33 (Equiv.swap (0 : Fin 3) 1))⁻¹ := by
      rw [← hza]
      rfl
    have hQc : Commute (t (Equiv.swap (2 : Fin 4) 3))
        (κ₁ (normPerm E h33 (Equiv.swap (0 : Fin 3) 1))) := by
      rw [← ht01]
      exact hcomm_t
    rw [hza', map_mul, map_mul, map_inv]
    exact (hQc.mul_right (hblock1 z hz)).mul_right hQc.inv_right
  intro y hy
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
  have hsup : normBlock E 3 ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin 3)) =
      normBlock E 3 {⟨0, by omega⟩} ⊔ normBlock E 3 {⟨1, by omega⟩} := by
    rw [normBlock_singleton_sup_singleton]
  rw [anchorBlock_eq_normBlock (E := E) (m := 3) h23, hsup] at hg
  have hle0 : normBlock E 3 ({⟨0, by omega⟩} : Finset (Fin 3)) ≤
      (Subgroup.centralizer ({t (Equiv.swap (2 : Fin 4) 3)} : Set H)).comap κ₁ := by
    intro a ha
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hblock0 a ha
  have hle1 : normBlock E 3 ({⟨1, by omega⟩} : Finset (Fin 3)) ≤
      (Subgroup.centralizer ({t (Equiv.swap (2 : Fin 4) 3)} : Set H)).comap κ₁ := by
    intro b hb
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hblock1 b hb
  have hgC : g ∈ (Subgroup.centralizer ({t (Equiv.swap (2 : Fin 4) 3)} : Set H)).comap κ₁ :=
    sup_le hle0 hle1 hg
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hgC
  exact hgC _ (Set.mem_singleton _)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
