module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open scoped Pointwise

variable {G : Type*} [Group G]

private lemma relIndex_eq_index_of_sup_eq_top {G : Type*} [Group G] [Finite G]
    {N M : Subgroup G} [M.Normal] (h : N ⊔ M = ⊤) : N.relIndex M = N.index := by
  have h' : M ⊔ N = ⊤ := by rw [sup_comm]; exact h
  have h1 : M.index = M.relIndex N := by
    rw [← Subgroup.relIndex_top_right (H := M), ← h', Subgroup.relIndex_sup_left]
  have key : N.relIndex M * M.index = N.index * M.index := by
    calc N.relIndex M * M.index = (N ⊓ M).index := (Subgroup.index_inf (H := N) (K := M)).symm
      _ = (M ⊓ N).index := by rw [inf_comm]
      _ = M.relIndex N * N.index := Subgroup.index_inf (H := M) (K := N)
      _ = M.index * N.index := by rw [h1]
      _ = N.index * M.index := by rw [mul_comm]
  have hM : M.index ≠ 0 := FiniteIndex.index_ne_zero
  exact Nat.mul_right_cancel (Nat.pos_of_ne_zero hM) key

private lemma relIndex_eq_relIndex_sup_of_normal {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G} [B.Normal] : A.relIndex B = A.relIndex (A ⊔ B) := by
  have h1 : (A ⊓ B).relIndex A * A.relIndex (A ⊔ B) = (A ⊓ B).relIndex (A ⊔ B) :=
    Subgroup.relIndex_mul_relIndex (H := A ⊓ B) (K := A) (L := A ⊔ B) inf_le_left le_sup_left
  have h2 : (A ⊓ B).relIndex B * B.relIndex (A ⊔ B) = (A ⊓ B).relIndex (A ⊔ B) :=
    Subgroup.relIndex_mul_relIndex (H := A ⊓ B) (K := B) (L := A ⊔ B) inf_le_right le_sup_right
  have hAB : (A ⊓ B).relIndex A = B.relIndex A := Subgroup.inf_relIndex_left A B
  have hBA : B.relIndex (A ⊔ B) = B.relIndex A := Subgroup.relIndex_sup_right A B
  have hne : B.relIndex A ≠ 0 := by
    haveI : (B.subgroupOf A).FiniteIndex := inferInstance
    exact FiniteIndex.index_ne_zero
  have key : B.relIndex A * A.relIndex (A ⊔ B) = B.relIndex A * (A ⊓ B).relIndex B := by
    simp only [hAB, hBA] at h1 h2
    rw [h1, mul_comm, h2]
  have hkey : A.relIndex (A ⊔ B) = (A ⊓ B).relIndex B :=
    Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) key
  rw [hkey, Subgroup.inf_relIndex_right]

private lemma relIndex_eq_of_card_eq {G : Type*} [Group G] [Finite G] {A B Y : Subgroup G}
    (hA : A ≤ Y) (hB : B ≤ Y) (hcard : Nat.card A = Nat.card B) :
    A.relIndex Y = B.relIndex Y := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card_div, Subgroup.index_eq_card_div,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hcard]

theorem lit_index_normalizer_odd [Finite G] {M A : Subgroup G} [M.Normal] (hAM : A ≤ M)
    (hA : IsPGroup 2 A) (hidx : ¬ 2 ∣ A.relIndex M) :
    ¬ 2 ∣ (normalizer (A : Set G)).index := by
  classical
  let P : Sylow 2 ↥M := (hA.comap_subtype (K := M)).toSylow hidx
  have hP : (P : Subgroup ↥M) = A.subgroupOf M := rfl
  have hmap : P.map M.subtype = A := by
    rw [hP, Subgroup.map_subgroupOf_eq_of_le hAM]
  have hsup : normalizer (A : Set G) ⊔ M = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top P
    rwa [hmap] at h
  have hnorm : normalizer (P : Set ↥M) = (normalizer (A : Set G)).subgroupOf M := by
    show normalizer (A.subgroupOf M : Set ↥M) = (normalizer (A : Set G)).subgroupOf M
    exact (Subgroup.subgroupOf_normalizer_eq hAM).symm
  have hcard : (normalizer (A : Set G)).index = Nat.card (Sylow 2 ↥M) := by
    rw [← relIndex_eq_index_of_sup_eq_top hsup, Sylow.card_eq_index_normalizer P, hnorm]
    rfl
  rw [hcard]
  exact not_dvd_card_sylow 2 ↥M

theorem lit_inv_sylow [Finite G] {N : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htN : ∀ x, x ∈ N ↔ t * x * t⁻¹ ∈ N) :
    ∃ S : Subgroup G, S ≤ N ∧ IsPGroup 2 S ∧ ¬ 2 ∣ S.relIndex N ∧
      ∀ x, x ∈ S ↔ t * x * t⁻¹ ∈ S := by
  classical
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htN' : t ∈ normalizer (N : Set G) := Subgroup.mem_normalizer_iff.mpr htN
  let Q : Subgroup G := N ⊔ Subgroup.zpowers t
  have htQ : t ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hNQ_normal : (N.subgroupOf Q).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr htN')
  have hz : IsPGroup 2 (Subgroup.zpowers (⟨t, htQ⟩ : ↥Q)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht]; norm_num)
  obtain ⟨S₀, hS₀⟩ := hz.exists_le_sylow
  let NQ : Subgroup ↥Q := N.subgroupOf Q
  haveI : NQ.Normal := hNQ_normal
  have hNQ_map : NQ.map Q.subtype = N := by
    rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left]
  have hS_eq : (S₀ : Subgroup ↥Q).map Q.subtype ⊓ N =
      ((S₀ : Subgroup ↥Q) ⊓ NQ).map Q.subtype := by
    rw [← hNQ_map, ← Subgroup.map_inf (S₀ : Subgroup ↥Q) NQ Q.subtype Subtype.coe_injective]
  refine ⟨(S₀ : Subgroup ↥Q).map Q.subtype ⊓ N, inf_le_right,
    (S₀.isPGroup'.map Q.subtype).to_inf_left, ?_, ?_⟩
  · have hrel : ((S₀ : Subgroup ↥Q).map Q.subtype ⊓ N).relIndex N =
        ((S₀ : Subgroup ↥Q) ⊓ NQ).relIndex NQ := by
      rw [hS_eq, ← hNQ_map]
      exact Subgroup.relIndex_map_map_of_injective (f := Q.subtype) ((S₀ : Subgroup ↥Q) ⊓ NQ) NQ
        Subtype.coe_injective
    rw [hrel, Subgroup.inf_relIndex_right, relIndex_eq_relIndex_sup_of_normal]
    exact fun h => S₀.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  · intro x
    constructor
    · rintro ⟨hxS, hxN⟩
      obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hxS
      have htS : (⟨t, htQ⟩ : ↥Q) ∈ (S₀ : Subgroup ↥Q) := hS₀ (Subgroup.mem_zpowers (⟨t, htQ⟩ : ↥Q))
      have hmem : (⟨t, htQ⟩ : ↥Q) * y * (⟨t, htQ⟩ : ↥Q)⁻¹ ∈ (S₀ : Subgroup ↥Q) :=
        (S₀ : Subgroup ↥Q).mul_mem ((S₀ : Subgroup ↥Q).mul_mem htS hyS)
          ((S₀ : Subgroup ↥Q).inv_mem htS)
      refine Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_map.mpr ⟨(⟨t, htQ⟩ : ↥Q) * y * (⟨t, htQ⟩ : ↥Q)⁻¹, hmem, ?_⟩,
          (htN (y : G)).mp hxN⟩
      rfl
    · rintro ⟨hxS, hxN⟩
      obtain ⟨z, hzS, hz⟩ := Subgroup.mem_map.mp hxS
      have htS : (⟨t, htQ⟩ : ↥Q) ∈ (S₀ : Subgroup ↥Q) := hS₀ (Subgroup.mem_zpowers (⟨t, htQ⟩ : ↥Q))
      have hmem : (⟨t, htQ⟩ : ↥Q)⁻¹ * z * (⟨t, htQ⟩ : ↥Q) ∈ (S₀ : Subgroup ↥Q) :=
        (S₀ : Subgroup ↥Q).mul_mem ((S₀ : Subgroup ↥Q).mul_mem
          ((S₀ : Subgroup ↥Q).inv_mem htS) hzS) htS
      refine Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_map.mpr ⟨(⟨t, htQ⟩ : ↥Q)⁻¹ * z * (⟨t, htQ⟩ : ↥Q), hmem, ?_⟩,
          (htN x).mpr hxN⟩
      simp only [map_mul, map_inv]
      rw [hz]
      change t⁻¹ * (t * x * t⁻¹) * t = x
      group

theorem lit_normalizer_map {H : Type*} [Group H] [Finite G] (π : G →* H)
    (hπ : Function.Surjective π) {A : Subgroup G} (hA : IsPGroup 2 A)
    (hidx : ¬ 2 ∣ A.relIndex (A ⊔ π.ker)) :
    normalizer ((A.map π : Subgroup H) : Set H) = (normalizer (A : Set G)).map π := by
  classical
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := hπ x
    let Y : Subgroup G := A ⊔ π.ker
    have hA_le_Y : A ≤ Y := le_sup_left
    let B : Subgroup G := A.map (MulAut.conj g).toMonoidHom
    have hconj : (A.map π).map (MulAut.conj (π g)) = A.map π :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
    have hcomp : (MulAut.conj (π g)).toMonoidHom.comp π =
        π.comp (MulAut.conj g).toMonoidHom := by
      ext a; simp
    have hBmap : B.map π = A.map π := by
      change (A.map (MulAut.conj g).toMonoidHom).map π = A.map π
      rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map]
      exact hconj
    have hB_le_Y : B ≤ Y := by
      have h : B ≤ (A.map π).comap π := Subgroup.map_le_iff_le_comap.mp (le_of_eq hBmap)
      rwa [Subgroup.comap_map_eq] at h
    have hB_2 : IsPGroup 2 B := hA.map _
    have hB_card : Nat.card B = Nat.card A :=
      (Nat.card_congr (Subgroup.equivMapOfInjective A _ (MulAut.conj g).injective).toEquiv).symm
    have hB_sylow : ¬ 2 ∣ B.relIndex Y := by
      rw [relIndex_eq_of_card_eq hB_le_Y hA_le_Y hB_card]
      exact hidx
    let P : Sylow 2 ↥Y := (hA.comap_subtype (K := Y)).toSylow hidx
    let Q : Sylow 2 ↥Y := (hB_2.comap_subtype (K := Y)).toSylow hB_sylow
    obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (↥Y) P Q
    have h1 : MulAut.conj y • (A.subgroupOf Y) = B.subgroupOf Y := by
      have hy' : ((y • P : Sylow 2 ↥Y) : Subgroup ↥Y) = ((Q : Sylow 2 ↥Y) : Subgroup ↥Y) := by
        rw [hy]
      rw [Sylow.smul_def, Sylow.pointwise_smul_def] at hy'
      exact hy'
    have h2 := Subgroup.conj_smul_subgroupOf (P := A) (H := Y) hA_le_Y y
    rw [h2] at h1
    have hyA : MulAut.conj (y : G) • A = B := by
      have hyY : MulAut.conj (y : G) • A ≤ Y := Subgroup.conj_smul_le_of_le hA_le_Y y
      calc MulAut.conj (y : G) • A
          = ((MulAut.conj (y : G) • A).subgroupOf Y).map Y.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hyY).symm
        _ = (B.subgroupOf Y).map Y.subtype := by rw [h1]
        _ = B := Subgroup.map_subgroupOf_eq_of_le hB_le_Y
    have hg_in : y⁻¹ * g ∈ normalizer (A : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hsmul : MulAut.conj (y⁻¹ * g) • A = A := by
        have hcm : MulAut.conj (y⁻¹ * g) = (MulAut.conj (y : G))⁻¹ * MulAut.conj g := by
          ext a
          simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_inv]
          group
        rw [hcm, mul_smul]
        change (MulAut.conj (y : G))⁻¹ • B = A
        rw [← hyA, ← mul_smul, inv_mul_cancel, one_smul]
      rwa [Subgroup.pointwise_smul_def] at hsmul
    have hyA_mem : π (y : G) ∈ (normalizer (A : Set G)).map π := by
      have hy2 : (y : G) ∈ A ⊔ π.ker := y.2
      have hker : (π.ker).map π = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro x ⟨k, hk, rfl⟩
        simpa using hk
      have h : π (y : G) ∈ A.map π := by
        have h' := Subgroup.mem_map_of_mem π hy2
        rwa [Subgroup.map_sup, hker, sup_bot_eq] at h'
      exact Subgroup.map_mono (f := π) Subgroup.le_normalizer h
    have hyinv : π (y⁻¹ * g) ∈ (normalizer (A : Set G)).map π :=
      Subgroup.mem_map.mpr ⟨y⁻¹ * g, hg_in, rfl⟩
    have hsplit : π g = π (y : G) * π (y⁻¹ * g) := by
      rw [← map_mul]
      congr 1
      exact (mul_inv_cancel_left (y : G) g).symm
    rw [hsplit]
    exact ((normalizer (A : Set G)).map π).mul_mem hyA_mem hyinv
  · exact Subgroup.le_normalizer_map π

end CFSG.OddStandard.HigherRank.YamadaG23
