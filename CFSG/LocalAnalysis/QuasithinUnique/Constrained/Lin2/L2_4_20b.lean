module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_20a

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem exists_sl2_mulVec_e1 {F : Type*} [Field F] {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; ext i; fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![v 0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i; fin_cases i <;> simp
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i; fin_cases i <;> simp

theorem exists_sl2_mulVec_eq {F : Type*} [Field F] {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) F, (σ : Matrix (Fin 2) (Fin 2) F).mulVec v = w := by
  obtain ⟨A, hA⟩ := exists_sl2_mulVec_e1 hv
  obtain ⟨B, hB⟩ := exists_sl2_mulVec_e1 hw
  refine ⟨B * A⁻¹, ?_⟩
  rw [← hA, ← hB, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_assoc,
    inv_mul_cancel, mul_one]

section Module

variable {G : Type*} [Group G]

theorem exists_conj_mem_coset_aux {F : Type*} [Field F] {L U Zc : Subgroup G}
    (α : L →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (β : U →* Multiplicative (Fin 2 → F)) (hβker : β.ker = Zc.subgroupOf U)
    (hequiv : ∀ ℓ : L, ∀ u v : U, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) {u w : G} (hu : u ∈ U) (hw : w ∈ U)
    (hu' : u ∉ Zc) (hw' : w ∉ Zc) :
    ∃ ℓ ∈ L, ℓ * u * ℓ⁻¹ * w⁻¹ ∈ Zc := by
  have hker_iff : ∀ v : U, β v = 1 ↔ (v : G) ∈ Zc := by
    intro v
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
  have hne : ∀ v : U, (v : G) ∉ Zc → Multiplicative.toAdd (β v) ≠ 0 := by
    intro v hv h0
    apply hv
    apply (hker_iff v).1
    exact Multiplicative.toAdd.injective (by simpa using h0)
  obtain ⟨σ, hσ⟩ := exists_sl2_mulVec_eq (hne ⟨u, hu⟩ hu') (hne ⟨w, hw⟩ hw')
  obtain ⟨ℓ, hℓ⟩ := hα σ
  refine ⟨(ℓ : G), ℓ.2, ?_⟩
  have hv : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hLU ℓ.2) u).1 hu
  have hβv := hequiv ℓ ⟨u, hu⟩ ⟨_, hv⟩ rfl
  have hvw : β ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hv⟩ = β ⟨w, hw⟩ := by
    apply Multiplicative.toAdd.injective
    rw [hβv, hℓ, hσ]
  have h1 : β (⟨(ℓ : G) * u * (ℓ : G)⁻¹, hv⟩ * (⟨w, hw⟩ : U)⁻¹) = 1 := by
    rw [map_mul, map_inv, hvw, mul_inv_cancel]
  exact (hker_iff _).1 h1

theorem lin2_exists_conj_mem_coset {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n)
    (hLU : L ≤ Subgroup.normalizer (blockU L : Set G)) {u w : G} (hu : u ∈ blockU L)
    (hw : w ∈ blockU L) (hu' : u ∉ blockZ L) (hw' : w ∉ blockZ L) :
    ∃ ℓ ∈ L, ℓ * u * ℓ⁻¹ * w⁻¹ ∈ blockZ L := by
  obtain ⟨F, _, _, -, α, hα, -, β, -, hβker, hequiv⟩ := h
  exact exists_conj_mem_coset_aux α hα β hβker hequiv hLU hu hw hu' hw'

end Module

section Parts

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem lin2_20_three (h8 : Lemma2_4_8) (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D)
    {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥) {x : G}
    (hxT : x ∈ T) (hxS : x ∉ S) :
    ∀ i ∈ thompsonJ S, i ^ 2 = 1 → i ≠ 1 →
      ∃ g : G, g⁻¹ * i * g ∈ lin2Delta (thompsonJ S) Z x ∨
        (g⁻¹ * i * g ∈ Z ∧ g⁻¹ * i * g ≠ 1) := by
  obtain ⟨-, ⟨hOL, -⟩, ⟨-, -, h3⟩, -, -, -, h7, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨-, hZ2, -⟩ := h16 G T M H S L D n hcfg Z hZ
  obtain ⟨hZR, hZZ'⟩ := ((hZ2 x hxT hxS).resolve_left fun h => hc h.1).2
  have hZe : Z = centerOf L := lin2_Z_eq_centerOf hc hZ
  have hZLeq : blockZ L = centerOf L := blockZ_eq_centerOf hcfg.charTwo_L hOL
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := by
    rw [← hOL]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  have hZR_le : Z ≤ centerOf (thompsonJ S) := lin2Z_le_centerOf h16 hcfg hZ
  have hZLR : blockZ L ≤ centerOf (thompsonJ S) := by
    rw [hZLeq, ← hZe]; exact hZR_le
  have hZ'ne : conjR Z x ≠ ⊥ := fun h => lin2Z_ne_bot h16 hcfg hZ (conjR_eq_bot_iff.1 h)
  obtain ⟨⟨w, hwZ'⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ'ne
  have hw1 : w ≠ 1 := fun h => hw1' (Subtype.ext h)
  have hwR : w ∈ centerOf (thompsonJ S) := by
    rw [hZR]; exact Subgroup.mem_sup_right hwZ'
  have hwU : w ∈ blockU L := by
    have : w ∈ blockU L ⊓ conjR (blockU L) x := by
      rw [(h3 x hxT hxS).2.1]; exact hwR
    exact this.1
  have hwZ : w ∉ blockZ L := by
    intro h
    rw [hZLeq, ← hZe] at h
    have : w ∈ Z ⊓ conjR Z x := ⟨h, hwZ'⟩
    rw [hZZ', Subgroup.mem_bot] at this
    exact hw1 this
  have key : ∀ j ∈ blockU L, j ≠ 1 →
      ∃ ℓ ∈ L, ℓ * j * ℓ⁻¹ ∈ centerOf (thompsonJ S) ∧ ℓ * j * ℓ⁻¹ ≠ 1 := by
    intro j hj hj1
    by_cases hjZ : j ∈ blockZ L
    · refine ⟨1, L.one_mem, ?_, ?_⟩
      · simpa using hZLR hjZ
      · simpa using hj1
    · obtain ⟨ℓ, hℓ, hmem⟩ := lin2_exists_conj_mem_coset hcfg.lin2 hLU hj hwU hjZ hwZ
      refine ⟨ℓ, hℓ, ?_, fun h1 => hj1 (conj_eq_one_iff.1 h1)⟩
      have e : ℓ * j * ℓ⁻¹ = (ℓ * j * ℓ⁻¹ * w⁻¹) * w := by group
      rw [e]
      exact mul_mem (hZLR hmem) hwR
  intro i hi hi2 hi1
  have final : ∀ g : G, g⁻¹ * i * g ∈ centerOf (thompsonJ S) → g⁻¹ * i * g ≠ 1 →
      ∃ g' : G, g'⁻¹ * i * g' ∈ lin2Delta (thompsonJ S) Z x ∨
        (g'⁻¹ * i * g' ∈ Z ∧ g'⁻¹ * i * g' ≠ 1) := by
    intro g hy hy1
    by_cases hyZ : g⁻¹ * i * g ∈ Z
    · exact ⟨g, Or.inr ⟨hyZ, hy1⟩⟩
    · by_cases hyZ' : g⁻¹ * i * g ∈ conjR Z x
      · have e : (g * x⁻¹)⁻¹ * i * (g * x⁻¹) = x * (g⁻¹ * i * g) * x⁻¹ := by group
        refine ⟨g * x⁻¹, Or.inr ⟨?_, ?_⟩⟩
        · rw [e]; exact mem_conjR.1 hyZ'
        · rw [e]; exact fun h1 => hy1 (conj_eq_one_iff.1 h1)
      · exact ⟨g, Or.inl ⟨hy, hyZ, hyZ'⟩⟩
  have hE := isElemAbelian_zpowers_of_sq_eq_one hi2
  have hEle : Subgroup.zpowers i ≤ thompsonJ S := Subgroup.zpowers_le.2 hi
  rcases (h7 x hxT hxS).2.2 _ hEle hE with hiU | hiUx
  · obtain ⟨ℓ, -, hy, hy1⟩ := key i (hiU (Subgroup.mem_zpowers i)) hi1
    exact final ℓ⁻¹ (by rwa [inv_inv]) (by rwa [inv_inv])
  · have hi' : x * i * x⁻¹ ∈ blockU L := mem_conjR.1 (hiUx (Subgroup.mem_zpowers i))
    have hi'1 : x * i * x⁻¹ ≠ 1 := fun h => hi1 (conj_eq_one_iff.1 h)
    obtain ⟨ℓ, -, hy, hy1⟩ := key _ hi' hi'1
    have e : (x⁻¹ * ℓ⁻¹)⁻¹ * i * (x⁻¹ * ℓ⁻¹) = ℓ * (x * i * x⁻¹) * ℓ⁻¹ := by group
    exact final (x⁻¹ * ℓ⁻¹) (by rw [e]; exact hy) (by rw [e]; exact hy1)

end Parts

end CFSG.QuasithinUnique.Lin2
