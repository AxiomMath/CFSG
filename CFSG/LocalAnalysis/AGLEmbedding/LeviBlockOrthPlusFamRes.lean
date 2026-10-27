module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamStab
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusLink
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusUnip
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem plusResAut_apply {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D)
    (htm : t + m = r) (g : ↥(plusFlagStab K r D)) (w : Fin m ⊕ Fin m → K) :
    plusResAut hD ht htm g w = (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
      (Function.extend (plusResIdx htm) w 0) ∘ plusResIdx htm := by
  have hsupp : ∀ x, x ∉ Set.range (plusResIdx htm) →
      Function.extend (plusResIdx htm) w (0 : Fin r ⊕ Fin r → K) x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ fun ⟨s, hs⟩ => hx ⟨s, hs⟩
  change (matrixEquiv m K (plusResBlockHom hD ht htm g)) w = _
  rw [matrixEquiv_apply, coe_plusResBlockHom, apply_eq_autMat_mulVec,
    mulVec_comp_eq_of_support (plusResIdx_injective htm) _ hsupp,
    Function.extend_comp (plusResIdx_injective htm)]

theorem extend_plusResIdx_apply {t m : ℕ} (htm : t + m = r) (w : Fin m ⊕ Fin m → K)
    (x : Fin m ⊕ Fin m) :
    Function.extend (plusResIdx htm) w (0 : Fin r ⊕ Fin r → K) (plusResIdx htm x) = w x :=
  (plusResIdx_injective htm).extend_apply _ _ x

theorem extend_plusResIdx_apply_of_not_mem {t m : ℕ} (htm : t + m = r) (w : Fin m ⊕ Fin m → K)
    {y : Fin r ⊕ Fin r} (hy : y ∉ Set.range (plusResIdx htm)) :
    Function.extend (plusResIdx htm) w (0 : Fin r ⊕ Fin r → K) y = 0 :=
  Function.extend_apply' _ _ _ fun ⟨s, hs⟩ => hy ⟨s, hs⟩

theorem smul_submodule_eq_of_mapsTo {V : Type} [AddCommGroup V] [Module K V] {h : V ≃ₗ[K] V}
    {P : Submodule K V} (h1 : ∀ x ∈ P, h x ∈ P) (h2 : ∀ x ∈ P, h⁻¹ x ∈ P) : h • P = P := by
  refine le_antisymm ?_ fun x hx => ⟨h⁻¹ x, h2 x hx, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · change h (h⁻¹ x) = x
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl

theorem plusResAut_smul_flag_two {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + 2 = r) {g : ↥(plusFlagStab K r D)}
    (hg : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • flag r K r = flag r K r) :
    plusResAut hD ht htm g • flag 2 K 2 = flag 2 K 2 := by
  have key : ∀ g' : ↥(plusFlagStab K r D),
      (g' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • flag r K r = flag r K r →
      ∀ w ∈ flag 2 K 2, plusResAut hD ht htm g' w ∈ flag 2 K 2 := by
    intro g' hg' w hw
    rw [mem_flag] at hw ⊢
    have hv : Function.extend (plusResIdx htm) w (0 : Fin r ⊕ Fin r → K) ∈ flag r K r := by
      rw [mem_flag]
      refine ⟨fun k => ?_, fun k hk => absurd k.isLt (by omega)⟩
      by_cases hk : Sum.inr k ∈ Set.range (plusResIdx htm)
      · obtain ⟨s | s, hx⟩ := hk
        · exact absurd hx (by rw [plusResIdx_inl]; exact Sum.inl_ne_inr)
        · rw [← hx, extend_plusResIdx_apply]
          exact hw.1 s
      · exact extend_plusResIdx_apply_of_not_mem htm w hk
    have hgv : (g' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
        (Function.extend (plusResIdx htm) w 0) ∈ flag r K r := by
      rw [← hg']
      exact ⟨_, hv, rfl⟩
    rw [mem_flag] at hgv
    rw [plusResAut_apply]
    exact ⟨fun j => hgv.1 _, fun j hj => absurd j.isLt (by omega)⟩
  refine smul_submodule_eq_of_mapsTo (key g hg) ?_
  rw [← map_inv]
  refine key g⁻¹ ?_
  change (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))⁻¹ • flag r K r = flag r K r
  rw [inv_smul_eq_iff, hg]

theorem mem_plusFamTwo_one_zero {x : Fin 2 ⊕ Fin 2 → K} :
    x ∈ plusFamTwo (![1, 0] : Fin 2 → K) ↔ x (Sum.inl 1) = 0 ∧ x (Sum.inr 0) = 0 := by
  simp only [mem_plusFamTwo, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, mul_one]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩

theorem plusResAut_smul_plusFamTwo {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + 2 = r) {g : ↥(plusFlagStab K r D)}
    (hg : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • Xstar r K (by omega) =
      Xstar r K (by omega)) :
    plusResAut hD ht htm g • plusFamTwo (![1, 0] : Fin 2 → K) = plusFamTwo ![1, 0] := by
  have key : ∀ g' : ↥(plusFlagStab K r D),
      (g' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • Xstar r K (by omega) =
        Xstar r K (by omega) →
      ∀ w ∈ plusFamTwo (![1, 0] : Fin 2 → K), plusResAut hD ht htm g' w ∈ plusFamTwo ![1, 0] := by
    intro g' hg' w hw
    rw [mem_plusFamTwo_one_zero] at hw ⊢
    have hv : Function.extend (plusResIdx htm) w (0 : Fin r ⊕ Fin r → K) ∈
        Xstar r K (by omega) := by
      rw [mem_Xstar]
      refine ⟨?_, fun k hk => ?_⟩
      · rw [show (Sum.inl ⟨r - 1, by omega⟩ : Fin r ⊕ Fin r) = plusResIdx htm (Sum.inl 1) by
          rw [plusResIdx_inl]; congr 1; ext; simp; omega, extend_plusResIdx_apply]
        exact hw.1
      · by_cases hkr : Sum.inr k ∈ Set.range (plusResIdx htm)
        · obtain ⟨s | s, hx⟩ := hkr
          · exact absurd hx (by rw [plusResIdx_inl]; exact Sum.inl_ne_inr)
          · rw [← hx, extend_plusResIdx_apply]
            rw [plusResIdx_inr] at hx
            fin_cases s
            · exact hw.2
            · exact absurd (Sum.inr_injective hx).symm (by
                intro h; apply hk; rw [h]; ext; simp; omega)
        · exact extend_plusResIdx_apply_of_not_mem htm w hkr
    have hgv : (g' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))
        (Function.extend (plusResIdx htm) w 0) ∈ Xstar r K (by omega) := by
      rw [← hg']
      exact ⟨_, hv, rfl⟩
    rw [mem_Xstar] at hgv
    rw [plusResAut_apply]
    refine ⟨?_, ?_⟩
    · simp only [Function.comp_apply, plusResIdx_inl]
      convert hgv.1 using 3
      ext
      simp
      omega
    · simp only [Function.comp_apply, plusResIdx_inr]
      refine hgv.2 _ fun h => ?_
      have := congrArg Fin.val h
      simp at this
      omega
  refine smul_submodule_eq_of_mapsTo (key g hg) ?_
  rw [← map_inv]
  refine key g⁻¹ ?_
  change (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))⁻¹ • Xstar r K _ = Xstar r K _
  rw [inv_smul_eq_iff, hg]

theorem plusFlagStab_eq_plusNodeStab (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2) :
    plusFlagStab K r D = plusNodeStab K hr {i | i.val + 1 ∈ D} := by
  have hV : ∀ i : Fin r, i.val + 1 ∈ D → plusNodeSpace K hr i = flag r K (i.val + 1) :=
    fun i hi => by rw [plusNodeSpace, ite_eq_left (hD _ hi).2]
  ext g
  rw [mem_plusFlagStab, mem_plusNodeStab]
  refine and_congr_right fun _ => ⟨fun h i hi => ?_, fun h d hd => ?_⟩
  · rw [hV i hi]
    exact h _ hi
  · have hd1 := (hD d hd).1
    have hd2 := (hD d hd).2
    have := h ⟨d - 1, by omega⟩ (show d - 1 + 1 ∈ D by rwa [Nat.sub_add_cancel hd1])
    rwa [hV _ (show d - 1 + 1 ∈ D by rwa [Nat.sub_add_cancel hd1]),
      show d - 1 + 1 = d by omega] at this

theorem plusFlagStab_le_closure (hr : 3 ≤ r) {D : Finset ℕ} (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2) :
    plusFlagStab K r D ≤ Subgroup.closure {γ | γ ∈ plusFlagStab K r D ∧
      (γ • flag r K r = flag r K r ∨ γ • Xstar r K (by omega) = Xstar r K (by omega))} := by
  have heq := plusFlagStab_eq_plusNodeStab (K := K) hr hD
  refine (heq.trans (plusNodeStab_generation hr _).1).le.trans (Subgroup.closure_mono ?_)
  rintro _ (hb | ⟨j, hj, rfl⟩)
  · refine ⟨heq ▸ borel_le_plusNodeStab hr _ hb, Or.inl ?_⟩
    exact MulAction.mem_stabilizer_iff.1 (borel_le_stabilizer_flag (by omega) le_rfl hb)
  · refine ⟨heq ▸ (weylElt_mem_plusNodeStab_iff hr _ j).2 hj, ?_⟩
    by_cases hj1 : j.val + 1 ≤ r - 2
    · exact Or.inl (weylElt_smul_flag_top_and_Xstar hr hj1).1
    · by_cases hj2 : j.val = r - 2
      · rw [show j = ⟨r - 2, by omega⟩ from Fin.ext hj2]
        exact Or.inl (weylElt_penult_smul hr).2
      · rw [show j = ⟨r - 1, by omega⟩ from Fin.ext (show j.val = r - 1 by have := j.isLt; omega)]
        exact Or.inr (weylElt_last_smul hr).2

theorem swapPair_smul_flag_two : swapPair K (1 : Fin 2) • flag 2 K 2 = plusFamTwo ![1, 0] := by
  rw [flag_two_eq_plusFamOne, swapPair_smul_plusFamOne]

theorem plusResAut_mem_plusFamTwoStab [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2) (hD' : ∀ d ∈ D, d ≤ r) {t : ℕ} (ht : t = 0 ∨ t ∈ D)
    (htm : t + 2 = r) (g : ↥(plusFlagStab K r D)) :
    plusResAut hD' ht htm g ∈ plusFamTwoStab K ∧
      MulAut.conj (swapPair K (1 : Fin 2)) (plusResAut hD' ht htm g) ∈ plusFamTwoStab K := by
  have hσσ : (swapPair K (1 : Fin 2))⁻¹ = swapPair K 1 :=
    inv_eq_of_mul_eq_one_right (swapPair_mul_self 1)
  have hσO : swapPair K (1 : Fin 2) ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) :=
    (swapIso K 1).2
  have hconj : ∀ h : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K),
      MulAut.conj (swapPair K (1 : Fin 2)) h = swapPair K 1 * h * swapPair K 1 := fun h => by
    rw [MulAut.conj_apply, hσσ]
  have e1 : swapPair K (1 : Fin 2) • plusFamTwo (![1, 0] : Fin 2 → K) = flag 2 K 2 := by
    rw [swapPair_smul_plusFamTwo, flag_two_eq_plusFamOne]
  set N : Subgroup ↥(plusFlagStab K r D) := (plusFamTwoStab K).comap (plusResAut hD' ht htm) ⊓
    (plusFamTwoStab K).comap ((MulAut.conj (swapPair K (1 : Fin 2))).toMonoidHom.comp
      (plusResAut hD' ht htm)) with hN
  have hgen : ∀ g' : ↥(plusFlagStab K r D),
      ((g' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • flag r K r = flag r K r ∨
      (g' : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) • Xstar r K (by omega) =
        Xstar r K (by omega)) → g' ∈ N := by
    intro g' hg'
    have hO' := plusResAut_mem_orthogonalGroup hD' ht htm g'
    have hcO : swapPair K (1 : Fin 2) * plusResAut hD' ht htm g' * swapPair K 1 ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) := mul_mem (mul_mem hσO hO') hσO
    refine ⟨Subgroup.mem_comap.2 ?_, Subgroup.mem_comap.2 ?_⟩
    · rcases hg' with hX | hX
      · exact mem_plusFamTwoStab_of_stab ⟨_, MulAction.mem_stabilizer_iff.2
          (plusResAut_smul_flag_two hD' ht htm hX)⟩ hO'
      · exact mem_plusFamTwoStab_of_stab_star hO' (plusResAut_smul_plusFamTwo hD' ht htm hX)
    · change MulAut.conj (swapPair K (1 : Fin 2)) (plusResAut hD' ht htm g') ∈ _
      rw [hconj]
      rcases hg' with hX | hX
      · refine mem_plusFamTwoStab_of_stab_star hcO ?_
        rw [← swapPair_smul_flag_two, smul_smul, mul_assoc _ (swapPair K 1) (swapPair K 1),
          swapPair_mul_self, mul_one, mul_smul, plusResAut_smul_flag_two hD' ht htm hX]
      · refine mem_plusFamTwoStab_of_stab ⟨_, MulAction.mem_stabilizer_iff.2 ?_⟩ hcO
        rw [← e1, smul_smul, mul_assoc _ (swapPair K 1) (swapPair K 1), swapPair_mul_self,
          mul_one, mul_smul, plusResAut_smul_plusFamTwo hD' ht htm hX]
  have hle : plusFlagStab K r D ≤ N.map (plusFlagStab K r D).subtype := by
    refine (plusFlagStab_le_closure hr hD).trans ((Subgroup.closure_le _).2 ?_)
    rintro γ ⟨hγ, hγX⟩
    exact ⟨⟨γ, hγ⟩, hgen ⟨γ, hγ⟩ hγX, rfl⟩
  obtain ⟨g', hg'N, hg'⟩ := hle g.2
  have : g' = g := Subtype.ext hg'
  rw [this] at hg'N
  exact ⟨hg'N.1, hg'N.2⟩

end CFSG.AGLEmbedding.LeviBlock
