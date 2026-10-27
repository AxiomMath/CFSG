module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafLin

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NoCentralInv {A : Type*} [Group A] (L : Subgroup A) : Prop :=
  ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z * z = 1 → z = 1

theorem NoCentralInv.map {A B : Type*} [Group A] [Group B] (Φ : A ≃* B) {L : Subgroup A}
    (h : NoCentralInv L) : NoCentralInv (L.map Φ.toMonoidHom) := by
  intro z hz hzc hzz
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
  have hw1 : w = 1 := h w hw (fun y hy => Φ.injective (by
      have := hzc (Φ y) (mem_map_of_mem Φ.toMonoidHom hy)
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using this))
    (Φ.injective (by simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_one] using hzz))
  rw [hw1, map_one]

variable {S : Type} [Group S] [Finite S]

theorem leaf_J_data [IsSimpleGroup S] (hQ : FixedTwoComponentsQuasisimple S)
    (hna : ∃ x y : S, x * y ≠ y * x) {t : S} (ht2 : orderOf t = 2) {J : Subgroup S}
    (hJC : J ≤ centralizer ({t} : Set S))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set S)))) {p f : ℕ}
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f)) :
    orderOf (MulAut.conj t) = 2 ∧ IsComponent (J.subgroupOf (fixedSubgroup (MulAut.conj t))) ∧
      NoCentralInv (J.subgroupOf (fixedSubgroup (MulAut.conj t))) ∧
      Blueprint.LieModel (↥(J.subgroupOf (fixedSubgroup (MulAut.conj t))) ⧸
        center ↥(J.subgroupOf (fixedSubgroup (MulAut.conj t)))) .PSL 2 p (2 * f) := by
  have hct := orderOf_conj_eq_two (center_eq_bot_of_nonabelian hna) ht2
  have hc2 : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← pow_two, ← hct, pow_orderOf_eq_one]
  have hc1 : MulAut.conj t ≠ 1 := fun h => by
    rw [h, orderOf_one] at hct
    omega
  have hJα : J ≤ fixedSubgroup (MulAut.conj t) := by
    rw [fixedSubgroup_conj]
    exact hJC
  have hJα' : IsPComponent 2 (J.subgroupOf (fixedSubgroup (MulAut.conj t))) := by
    rw [fixedSubgroup_conj]
    exact hJ
  have hJs : IsSimpleGroup (J ⧸ pPrimeCore 2 J) :=
    Pump516.isSimpleGroup_of_lieModel_psl (by norm_num) hJm
  obtain ⟨hJc, hJZ, ⟨eJ⟩⟩ := fixed_component_data hQ hc2 hc1 hJα hJα' hJs
  exact ⟨hct, hJc, hJZ, lieModel_center_of_fixed eJ hJm⟩

end CFSG.ComponentClassification.GSThmB.Pump516
