module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.ClassicalInvolution.WeakCT
open scoped Pointwise

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem mem_of_map_conj_le {p : ℕ} [Fact p.Prime] {B A : Subgroup G} (hBA : B ≤ A)
    (hB : IsPGroup p B) (hidx : ¬ p ∣ B.index)
    (hN : Subgroup.normalizer (B : Set G) ≤ A) {g : G}
    (hg : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ A) : g ∈ A := by
  set C := B.map (MulAut.conj g⁻¹).toMonoidHom with hC
  have hCp : IsPGroup p C := hB.map _
  have hCi : C.index = B.index :=
    show (B.map (MulAut.conj g⁻¹).toMonoidHom).index = B.index from
      Subgroup.index_map_equiv (H := B) (MulAut.conj g⁻¹)
  have hidxC : ¬ p ∣ C.index := by
    rw [hCi]
    exact hidx
  have h1 : ¬ p ∣ (B.subgroupOf A).index := fun h => hidx (by
    rw [← Subgroup.relIndex_mul_index hBA]
    exact h.mul_right _)
  have h2 : ¬ p ∣ (C.subgroupOf A).index := fun h => hidxC (by
    rw [← Subgroup.relIndex_mul_index hg]
    exact h.mul_right _)
  let S₁ : Sylow p A := (hB.comap_of_injective A.subtype A.subtype_injective).toSylow h1
  let S₂ : Sylow p A := (hCp.comap_of_injective A.subtype A.subtype_injective).toSylow h2
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A S₂ S₁
  have hnorm : (a : G) * g⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hyC : g⁻¹ * n * g ∈ C := ⟨n, hn, by simp⟩
    have hyA : g⁻¹ * n * g ∈ A := hg hyC
    have hyS : (⟨g⁻¹ * n * g, hyA⟩ : A) ∈ (S₂ : Subgroup A) := hyC
    have hmem : MulAut.conj a • (⟨g⁻¹ * n * g, hyA⟩ : A) ∈ MulAut.conj a • (S₂ : Subgroup A) :=
      Subgroup.smul_mem_pointwise_smul _ (MulAut.conj a) (S₂ : Subgroup A) hyS
    have hS : MulAut.conj a • (S₂ : Subgroup A) = (S₁ : Subgroup A) := by
      rw [← Sylow.coe_subgroup_smul, ha]
    rw [hS] at hmem
    have hmem' : ((MulAut.conj a • (⟨g⁻¹ * n * g, hyA⟩ : A) : A) : G) ∈ B := hmem
    have e : ((MulAut.conj a • (⟨g⁻¹ * n * g, hyA⟩ : A) : A) : G) =
        (a : G) * g⁻¹ * n * ((a : G) * g⁻¹)⁻¹ := by
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at hmem'
    exact hmem'
  have hga : (a : G) * g⁻¹ ∈ A := hN hnorm
  have : g⁻¹ ∈ A := by
    have := A.mul_mem (A.inv_mem a.2) hga
    simpa using this
  simpa using A.inv_mem this

omit [Finite G] in
theorem map_conj_eq_self {A : Subgroup G} {g : G} (hg : g ∈ A) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact A.mul_mem (A.mul_mem hg hx) (A.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, A.mul_mem (A.mul_mem (A.inv_mem hg) hx) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

omit [Finite G] in
theorem map_one_mulAut (A : Subgroup G) : A.map (1 : MulAut G).toMonoidHom = A := by
  have e : (1 : MulAut G).toMonoidHom = MonoidHom.id G := by
    ext x
    rfl
  rw [e, Subgroup.map_id]

omit [Finite G] in
theorem map_conj_map_conj (A : Subgroup G) (g h : G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Sylow

section Par

variable {F : Type} [Field F]

noncomputable abbrev borel4 (F : Type) [Field F] : Subgroup (spinGroup (quadPlus 4 F)) :=
  borel (plusDatum 4 F three_le_four) (fun k => (torusD F three_le_four k).range)

@[expose] noncomputable def par (F : Type) [Field F] (J : Set (Fin 4)) :
    Subgroup (spinGroup (quadPlus 4 F)) :=
  borel4 F ⊔ ⨆ i ∈ J, rankOne (plusDatum 4 F three_le_four).rootGroup i

theorem borel4_le_par (J : Set (Fin 4)) : borel4 F ≤ par F J := le_sup_left

theorem rankOne_le_par {J : Set (Fin 4)} {i : Fin 4} (hi : i ∈ J) :
    rankOne (plusDatum 4 F three_le_four).rootGroup i ≤ par F J :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun i (_ : i ∈ J) =>
    rankOne (plusDatum 4 F three_le_four).rootGroup i) i hi le_rfl)

@[expose] def negType (F : Type) [Field F] (A : Subgroup (spinGroup (quadPlus 4 F))) :
    Set (Fin 4) :=
  {i | (plusDatum 4 F three_le_four).rootGroup (-Pi.single i 1) ≤ A}

theorem rootGroup_single_le_borel4 (i : Fin 4) :
    (plusDatum 4 F three_le_four).rootGroup (Pi.single i 1) ≤ borel4 F :=
  rootGroup_le_borel ((RootSystem.ofCartan (plusDatum 4 F three_le_four).isFiniteType
    (plusDatum 4 F three_le_four).divisible).single_mem i)
    (ht_single_pos (D := plusDatum 4 F three_le_four) i)

theorem mem_negType_par {J : Set (Fin 4)} {i : Fin 4} (hi : i ∈ J) : i ∈ negType F (par F J) :=
  (le_sup_right : (plusDatum 4 F three_le_four).rootGroup (-Pi.single i 1) ≤
    rankOne (plusDatum 4 F three_le_four).rootGroup i).trans (rankOne_le_par hi)

theorem par_negType {A : Subgroup (spinGroup (quadPlus 4 F))} (hBA : borel4 F ≤ A) :
    par F (negType F A) = A := by
  apply le_antisymm
  · refine sup_le hBA (iSup₂_le fun i hi => sup_le ((rootGroup_single_le_borel4 i).trans hBA) hi)
  · calc A = borel4 F ⊔ ⨆ i ∈ negIndices (plusDatum 4 F three_le_four) A,
          rankOne (plusDatum 4 F three_le_four).rootGroup i :=
        eq_borel_sup_rankOne spinFour_ct spinFour_extras hBA
      _ ≤ par F (negType F A) := by
        refine sup_le le_sup_left (iSup₂_le fun i hi => ?_)
        refine rankOne_le_par (J := negType F A) (i := i) ?_
        exact (le_sup_right : (plusDatum 4 F three_le_four).rootGroup (-Pi.single i 1) ≤
          rankOne (plusDatum 4 F three_le_four).rootGroup i).trans
          (rankOne_le_of_mem_negIndices hBA hi)

variable [Finite F] [CharP F 2] (hF : Nat.card F = 2)
include hF

omit [CharP F 2] in
theorem borel4_eq_posUnipotent : borel4 F = posUnipotent (plusDatum 4 F three_le_four) := by
  apply le_antisymm
  · exact sup_le (iSup_le fun k => (torusD_range_eq_bot hF k).le.trans bot_le) le_rfl
  · exact posUnipotent_le_borel

theorem negType_par (J : Set (Fin 4)) : negType F (par F J) = J := by
  have := finite_spinFour (F := F)
  ext i
  refine ⟨fun hi => ?_, mem_negType_par⟩
  by_contra hiJ
  have hN : par F J ≤
      Subgroup.normalizer (radical (plusDatum 4 F three_le_four) i : Set _) := by
    refine sup_le (borel_le_normalizer_radical spinFour_ct spinFour_extras i)
      (iSup₂_le fun j hj => ?_)
    exact rankOne_le_normalizer_radical spinFour_extras (by rintro rfl; exact hiJ hj)
  have hL : rankOne (plusDatum 4 F three_le_four).rootGroup i ≤ par F J :=
    sup_le ((rootGroup_single_le_borel4 i).trans (borel4_le_par J)) hi
  have hR2 : IsPGroup 2 (radical (plusDatum 4 F three_le_four) i) :=
    posUnipotent_spinFour_isPGroup.to_le (radical_le_posUnipotent (D := plusDatum 4 F three_le_four) i)
  have h6 := rankOne_spin_facts hF i
  have hbot : radical (plusDatum 4 F three_le_four) i ⊓
      rankOne (plusDatum 4 F three_le_four).rootGroup i = ⊥ :=
    eq_bot_of_isPGroup_two_of_card_six h6.1 h6.2.1 inf_le_right
      ((le_inf (hL.trans hN) Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      (hR2.to_le inf_le_left)
  have hα : (Pi.single i 1 : Fin (plusDatum 4 F three_le_four).rank → ℤ) ∈
      (plusDatum 4 F three_le_four).roots :=
    (RootSystem.ofCartan (plusDatum 4 F three_le_four).isFiniteType
      (plusDatum 4 F three_le_four).divisible).single_mem i
  apply spinFour_extras.ne_bot _ hα
  rw [eq_bot_iff, ← hbot]
  exact le_inf (rootGroup_le_radical (D := plusDatum 4 F three_le_four) hα
    (by show (0 : ℤ) < (Pi.single i (1 : ℤ) : Fin 4 → ℤ) i; simp)) le_sup_left

theorem par_injective : Function.Injective (par F) := fun J J' h => by
  rw [← negType_par hF J, ← negType_par hF J', h]

theorem borel4_isPGroup : IsPGroup 2 (borel4 F) := by
  rw [borel4_eq_posUnipotent hF]
  exact posUnipotent_spinFour_isPGroup

theorem not_dvd_index_borel4 : ¬ 2 ∣ (borel4 F).index := by
  have := finite_spinFour (F := F)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [borel4_eq_posUnipotent hF]
  exact not_dvd_index_posUnipotent spinFour_ct spinFour_extras
    (fun _ hγ => rootGroup_spinFour_isPGroup hγ) (Nat.coprime_one_right 2)
    (fun k g hg => by
      rw [torusD_range_eq_bot hF k, Subgroup.mem_bot] at hg
      rw [hg, one_pow])

omit [CharP F 2] in
theorem normalizer_borel4_le :
    Subgroup.normalizer (borel4 F : Set (spinGroup (quadPlus 4 F))) ≤ borel4 F := by
  have h := normalizer_posUnipotent_le_borel spinFour_ct spinFour_extras
    (D := plusDatum 4 F three_le_four)
  rw [← borel4_eq_posUnipotent hF] at h
  exact h

theorem eq_of_map_conj_par {J J' : Set (Fin 4)} (k : spinGroup (quadPlus 4 F))
    (h : (par F J).map (MulAut.conj k).toMonoidHom = par F J') : J = J' := by
  have := finite_spinFour (F := F)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : (borel4 F).map (MulAut.conj k⁻¹).toMonoidHom ≤ par F J := by
    have h1 : borel4 F ≤ (par F J).map (MulAut.conj k).toMonoidHom := h ▸ borel4_le_par J'
    have h2 := Subgroup.map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) h1
    rwa [map_conj_map_conj, inv_mul_cancel, MulAut.conj.map_one, map_one_mulAut] at h2
  have hk : k ∈ par F J := mem_of_map_conj_le (borel4_le_par J) (borel4_isPGroup hF)
    (not_dvd_index_borel4 hF) ((normalizer_borel4_le hF).trans (borel4_le_par J)) hB
  rw [map_conj_eq_self hk] at h
  exact par_injective hF h

end Par

section TypeMap

variable {F : Type} [Field F]

@[expose] def IsTypeMap (β : MulAut (spinGroup (quadPlus 4 F))) (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ J : Set (Fin 4), ∃ k : spinGroup (quadPlus 4 F),
    (par F J).map β.toMonoidHom = (par F (σ '' J)).map (MulAut.conj k).toMonoidHom

theorem isTypeMap_conj (k : spinGroup (quadPlus 4 F)) : IsTypeMap (MulAut.conj k) 1 :=
  fun J => ⟨k, by rw [Equiv.Perm.coe_one, Set.image_id]⟩

theorem isTypeMap_one : IsTypeMap (1 : MulAut (spinGroup (quadPlus 4 F))) 1 := by
  have h := isTypeMap_conj (F := F) 1
  rwa [MulAut.conj.map_one] at h

theorem map_map_conj (β : MulAut (spinGroup (quadPlus 4 F))) (A : Subgroup _) (k : _) :
    (A.map (MulAut.conj k).toMonoidHom).map β.toMonoidHom =
      (A.map β.toMonoidHom).map (MulAut.conj (β k)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem IsTypeMap.mul {β β' : MulAut (spinGroup (quadPlus 4 F))} {σ σ' : Equiv.Perm (Fin 4)}
    (h : IsTypeMap β σ) (h' : IsTypeMap β' σ') : IsTypeMap (β * β') (σ * σ') := by
  intro J
  obtain ⟨k', hk'⟩ := h' J
  obtain ⟨k, hk⟩ := h (σ' '' J)
  refine ⟨β k' * k, ?_⟩
  have e : (β * β').toMonoidHom = β.toMonoidHom.comp β'.toMonoidHom := rfl
  rw [e, ← Subgroup.map_map, hk', map_map_conj, hk, map_conj_map_conj, Equiv.Perm.coe_mul,
    Set.image_comp]

theorem IsTypeMap.inv {β : MulAut (spinGroup (quadPlus 4 F))} {σ : Equiv.Perm (Fin 4)}
    (h : IsTypeMap β σ) : IsTypeMap β⁻¹ σ⁻¹ := by
  intro J
  obtain ⟨k, hk⟩ := h (⇑(σ⁻¹) '' J)
  have hJ : σ '' (⇑(σ⁻¹) '' J) = J := by
    rw [← Set.image_comp, ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one, Set.image_id]
  rw [hJ] at hk
  refine ⟨(β⁻¹ k)⁻¹, ?_⟩
  have h1 := congrArg (fun A : Subgroup _ => A.map (β⁻¹).toMonoidHom) hk
  have e : ∀ A : Subgroup (spinGroup (quadPlus 4 F)),
      (A.map β.toMonoidHom).map (β⁻¹).toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp
  rw [e, map_map_conj] at h1
  rw [h1, map_conj_map_conj, inv_mul_cancel, MulAut.conj.map_one, map_one_mulAut]

variable [Finite F] [CharP F 2] (hF : Nat.card F = 2)
include hF

theorem IsTypeMap.unique {β : MulAut (spinGroup (quadPlus 4 F))} {σ σ' : Equiv.Perm (Fin 4)}
    (h : IsTypeMap β σ) (h' : IsTypeMap β σ') : σ = σ' := by
  ext j
  obtain ⟨k, hk⟩ := h {j}
  obtain ⟨k', hk'⟩ := h' {j}
  rw [hk', Set.image_singleton] at hk
  rw [Set.image_singleton] at hk
  have h1 := congrArg (fun A : Subgroup _ => A.map (MulAut.conj k⁻¹).toMonoidHom) hk
  simp only [map_conj_map_conj, inv_mul_cancel, MulAut.conj.map_one, map_one_mulAut] at h1
  have := eq_of_map_conj_par hF (k⁻¹ * k') h1
  rw [Set.singleton_eq_singleton_iff] at this
  rw [this]

end TypeMap

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
