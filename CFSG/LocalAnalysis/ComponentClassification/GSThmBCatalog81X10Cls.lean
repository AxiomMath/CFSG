module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfT

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace X10

variable {K : Type} [Field K]

theorem isComponent_E2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsComponent ((E2 K).subgroupOf (centralizer {u1 K})) := by
  have hE : E2 K ≤ centralizer {u1 K} := (E2_le_X0 h2).trans X0_le_centralizer
  have hX : X0 K ≤ centralizer {u1 K} := X0_le_centralizer
  refine ⟨(isQuasisimple_congr (subgroupOfEquivOfLe hE)).mpr (isQuasisimple_E2 h2 h4), ?_⟩
  have hXn : ((X0 K).subgroupOf (centralizer {u1 K})).Normal := by
    rw [normal_subgroupOf_iff hX]
    intro x c hx hc
    exact conj_mem_map_centralizer (T1 K) hc hx
  have hEX : (E2 K).subgroupOf (centralizer {u1 K}) ≤ (X0 K).subgroupOf (centralizer {u1 K}) :=
    fun x hx => E2_le_X0 h2 hx
  refine IsSubnormal.trans hEX ?_ hXn.isSubnormal
  apply Normal.isSubnormal
  rw [normal_subgroupOf_iff hEX]
  intro x c hx hc
  exact conj_mem_E2 h2 hc hx

theorem E1_ne_E2 : E1 K ≠ E2 K := by
  intro h
  set g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  have hy : proj 2 K (blkSL K (1, g)) ∈ E1 K := by
    rw [h]
    exact mem_E2.mpr ⟨g, rfl⟩
  obtain ⟨g', hg'⟩ := mem_E1.mp hy
  rcases eq_or_eq_neg_of_proj_eq hg' with e | e <;>
    simp only [coe_blkSL, Matrix.SpecialLinearGroup.coe_one] at e
  · obtain ⟨-, e2⟩ := blk_injective _ _ _ _ e
    have := congrFun (congrFun e2 0) 1
    simp [g] at this
  · rw [blk_neg] at e
    obtain ⟨-, e2⟩ := blk_injective _ _ _ _ e
    have := congrFun (congrFun e2 0) 1
    simp [g] at this

theorem not_le_pPrimeCore [Finite K] {C E : Subgroup (StatedProj (StatedSp 2 K))}
    {x : StatedProj (StatedSp 2 K)} (hxE : x ∈ E) (hxC : x ∈ C) (hx : orderOf x = 2) :
    ¬ E.subgroupOf C ≤ pPrimeCore 2 C := by
  intro hle
  have hmem : (⟨x, hxC⟩ : C) ∈ pPrimeCore 2 C := hle (mem_subgroupOf.mpr hxE)
  have h1 := orderOf_dvd_natCard (⟨⟨x, hxC⟩, hmem⟩ : ↥(pPrimeCore 2 C))
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx] at h1
  have h2 : ¬ 2 ∣ Nat.card (pPrimeCore 2 C) :=
    (Nat.prime_two.coprime_iff_not_dvd).mp (pPrimeCore_coprime_card (p := 2) (G := C))
  exact h2 h1

theorem isPComponent_E1 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsPComponent 2 ((E1 K).subgroupOf (centralizer {u1 K})) :=
  isPComponent_of_isComponent_of_not_le 2 (isComponent_E1 h2 h4)
    (not_le_pPrimeCore u1_mem_E1 (mem_centralizer_singleton_iff.mpr rfl)
      (orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)))

theorem isPComponent_E2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    IsPComponent 2 ((E2 K).subgroupOf (centralizer {u1 K})) :=
  isPComponent_of_isComponent_of_not_le 2 (isComponent_E2 h2 h4)
    (not_le_pPrimeCore u1_mem_E2 (mem_centralizer_singleton_iff.mpr rfl)
      (orderOf_eq_prime (by rw [pow_two]; exact u1_mul_u1) (u1_ne_one h2)))

theorem exists_conj_T1_mul {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K)
    {T W : StatedSp 2 K} (hTT : T * T = negS K) (hW : W ∈ fixOf (conjSp 2 K A))
    (hTW : proj 2 K T * proj 2 K W = proj 2 K W * proj 2 K T)
    (hTn : proj 2 K T ∉ (fixOf (conjSp 2 K A)).map (proj 2 K))
    (hZZ : proj 2 K (W * W) * proj 2 K (W * W) = 1) (hZ1 : proj 2 K (W * W) ≠ 1) :
    ∃ g : StatedSp 2 K, g⁻¹ * (T * (W * W)) * g = T1 K := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (odd_card_of_card_eq hp hp2 hK)
  have hZf : W * W ∈ fixOf (conjSp 2 K A) := mul_mem hW hW
  have hnc : ∀ x : StatedSp 2 K, x * negS K = negS K * x := fun x =>
    mem_center_iff.mp (mem_center_of_mem_spScalars
      ((mem_spScalars_iff _).mpr (Or.inr coe_negS))) x
  have hZn : W * W * (W * W) = negS K := by
    have hs : W * W * (W * W) ∈ spScalars 2 K := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul]
      exact hZZ
    rcases (mem_spScalars_iff _).mp hs with h | h
    · exfalso
      have h1 : W * W * (W * W) = 1 := sp_ext (by rw [h]; rfl)
      exact hZ1 (ConfP.proj_eq_one_of
        (ConfP.fixOf_eq_one_or_negS hp hp2 hf hK A hd0 hdsq hAA hμ hZf h1))
    · exact eq_negS_of_coe h
  have hc := conj_mem_spScalars_of_commute (T := W) (A := T) hTW
  have hTZ : T * (W * W) = W * W * T := by
    rcases (mem_spScalars_iff _).mp hc with h | h
    · have h1 : T * W * T⁻¹ * W⁻¹ = 1 := sp_ext (by rw [h]; rfl)
      have h3 : T * W = W * T := by
        calc T * W = T * W * T⁻¹ * W⁻¹ * (W * T) := by group
          _ = W * T := by rw [h1, one_mul]
      calc T * (W * W) = T * W * W := by group
        _ = W * T * W := by rw [h3]
        _ = W * (T * W) := by group
        _ = W * (W * T) := by rw [h3]
        _ = W * W * T := by group
    · have h1 : T * W * T⁻¹ * W⁻¹ = negS K := eq_negS_of_coe h
      have h3 : T * W = negS K * (W * T) := by
        calc T * W = T * W * T⁻¹ * W⁻¹ * (W * T) := by group
          _ = negS K * (W * T) := by rw [h1]
      calc T * (W * W) = T * W * W := by group
        _ = negS K * (W * T) * W := by rw [h3]
        _ = negS K * W * (T * W) := by group
        _ = negS K * W * (negS K * (W * T)) := by rw [h3]
        _ = negS K * (W * negS K) * (W * T) := by group
        _ = negS K * (negS K * W) * (W * T) := by rw [hnc W]
        _ = negS K * negS K * (W * W * T) := by group
        _ = W * W * T := by rw [ConfP.negS_mul_self, one_mul]
  have hsq : T * (W * W) * (T * (W * W)) = 1 := by
    calc T * (W * W) * (T * (W * W)) = T * (W * W * T) * (W * W) := by group
      _ = T * (T * (W * W)) * (W * W) := by rw [hTZ]
      _ = T * T * (W * W * (W * W)) := by group
      _ = 1 := by rw [hTT, hZn, ConfP.negS_mul_self]
  have hne1 : T * (W * W) ≠ 1 := by
    intro h
    apply hTn
    refine ⟨(W * W)⁻¹, inv_mem hZf, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h]
  have hnen : T * (W * W) ≠ negS K := by
    intro h
    apply hTn
    refine ⟨negS K * (W * W)⁻¹, mul_mem (ConfP.negS_mem_fixOf A) (inv_mem hZf), ?_⟩
    rw [← h, mul_inv_cancel_right]
  refine exists_conj_T1 h2 (T * (W * W)) ?_ ?_ ?_
  · rw [← Units.val_mul, ← Subgroup.coe_mul, hsq]
    rfl
  · intro h
    exact hne1 (sp_ext (by rw [h]; rfl))
  · intro h
    exact hnen (eq_negS_of_coe h)

end X10

end CFSG.ComponentClassification.GSThmB
