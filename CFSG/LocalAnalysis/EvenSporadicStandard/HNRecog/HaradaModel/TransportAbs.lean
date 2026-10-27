module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.TransportCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.OfMulEquivAux

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

variable {H K : Type} [Group H] [Group K]

theorem range_comp_mulEquiv (e : H ≃* K) {A : Type} [Group A] (ι : A →* H) :
    (e.toMonoidHom.comp ι).range = ι.range.map e.toMonoidHom := by
  exact MonoidHom.range_comp e.toMonoidHom ι

theorem isPGroup_map_mulEquiv (e : H ≃* K) {S : Subgroup H} (h : IsPGroup 2 ↥S) :
    IsPGroup 2 ↥(S.map e.toMonoidHom) := by
  exact IsPGroup.map h e.toMonoidHom

theorem centralizer_map_le (e : H ≃* K) {X : Subgroup H} (h : centralizer (X : Set H) ≤ X) :
    centralizer ((X.map e.toMonoidHom : Subgroup K) : Set K) ≤ X.map e.toMonoidHom := by
  intro y hy
  obtain ⟨y', rfl⟩ := e.surjective y
  rw [Subgroup.mem_map]
  refine ⟨y', ?_, rfl⟩
  apply h
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro x hx
  apply e.injective
  rw [map_mul, map_mul]
  exact hy (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem card_normalizer_map (e : H ≃* K) (X : Subgroup H) :
    Nat.card ↥(normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K)) =
      Nat.card ↥(normalizer (X : Set H)) := by
  have hmap : (normalizer (X : Set H)).map e.toMonoidHom
      = normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K) := by
    apply le_antisymm (le_normalizer_map (H := X) e.toMonoidHom)
    intro y hy
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [Subgroup.mem_map]
    refine ⟨y', ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hy ⊢
    have hm : (X.map (MulAut.conj y').toMonoidHom).map e.toMonoidHom
        = X.map e.toMonoidHom := by
      calc
        (X.map (MulAut.conj y').toMonoidHom).map e.toMonoidHom
            = X.map (e.toMonoidHom.comp (MulAut.conj y').toMonoidHom) := by
              rw [Subgroup.map_map]
        _ = X.map ((MulAut.conj (e y')).toMonoidHom.comp e.toMonoidHom) := by
              rw [CFSG.EvenSporadicStandard.HNRecog.TwoHSData.conj_comp_mulEquiv]
        _ = (X.map e.toMonoidHom).map (MulAut.conj (e y')).toMonoidHom := by
              rw [Subgroup.map_map]
        _ = X.map e.toMonoidHom := hy
    apply comap_injective (f := e.symm.toMonoidHom) e.symm.surjective
    rw [← Subgroup.map_equiv_eq_comap_symm' e, ← Subgroup.map_equiv_eq_comap_symm' e]
    exact hm
  rw [← hmap, card_map_mulEquiv]

theorem fuse_map (e : H ≃* K) (X : Subgroup H) {x y : H}
    (h : ∃ n ∈ normalizer (X : Set H), n * x * n⁻¹ = y) :
    ∃ n ∈ normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K), n * e x * n⁻¹ = e y := by
  obtain ⟨n, hn, hny⟩ := h
  refine ⟨e n, (le_normalizer_map (H := X) e.toMonoidHom) (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩), ?_⟩
  rw [← hny]
  simp only [map_mul, map_inv]

theorem conj_E64_map (e : H ≃* K) {X : Subgroup H}
    (h : ∀ B : Subgroup H, Nat.card B = 64 → CFSG.Open.IsElemAbelian 2 B →
      ∃ g : H, B = X.map (MulAut.conj g).toMonoidHom) :
    ∀ B : Subgroup K, Nat.card B = 64 → CFSG.Open.IsElemAbelian 2 B →
      ∃ g : K, B = (X.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  intro B hB hBabel
  let B0 : Subgroup H := B.comap e.toMonoidHom
  have hcard : Nat.card B0 = 64 := by
    have h1 : B0 = B.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm' e B
    rw [h1, card_map_mulEquiv]
    exact hB
  have habel : CFSG.Open.IsElemAbelian 2 B0 := isElemAbelian_comap_mulEquiv e hBabel
  obtain ⟨g, hg⟩ := h B0 hcard habel
  refine ⟨e g, ?_⟩
  have hBmap : B0.map e.toMonoidHom = B := Subgroup.map_comap_eq_self_of_surjective e.surjective B
  rw [← hBmap, hg]
  rw [Subgroup.map_map, Subgroup.map_map,
    CFSG.EvenSporadicStandard.HNRecog.TwoHSData.conj_comp_mulEquiv e g]

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
