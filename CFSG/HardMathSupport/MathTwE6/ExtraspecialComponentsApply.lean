module

public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponents
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.HardMathSupport.MathTwE6

open CFSG.Open

variable {G : Type*} [Group G]

theorem isComponentOf_map_conj_of_mem_normalizer [Finite G] {J X : Subgroup G}
    (hJ : IsComponentOf J X) {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    IsComponentOf (J.map (MulAut.conj g).toMonoidHom) X := by
  have hX : X.map (MulAut.conj g).toMonoidHom = X := (map_conj_eq_iff_mem_normalizer X g).2 hg
  refine ⟨?_, ?_, ?_⟩
  · rw [← hX]
    exact Subgroup.map_mono hJ.1
  · have h := CFSG.ComponentClassification.Components.chain_map (MulAut.conj g).toMonoidHom hJ.2.1
    rwa [hX] at h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (J.equivMapOfInjective _ (MulAut.conj g).injective).symm hJ.2.2

theorem index_center_map_conj [Finite G] (J : Subgroup G) (g : G) :
    (Subgroup.center ↥(J.map (MulAut.conj g).toMonoidHom)).index = (Subgroup.center J).index := by
  set e : J ≃* ↥(J.map (MulAut.conj g).toMonoidHom) :=
    J.equivMapOfInjective _ (MulAut.conj g).injective
  have hJ : Nat.card ↥(J.map (MulAut.conj g).toMonoidHom) = Nat.card J :=
    (Nat.card_congr e.toEquiv).symm
  have hZ : Nat.card ↥(Subgroup.center ↥(J.map (MulAut.conj g).toMonoidHom)) =
      Nat.card ↥(Subgroup.center J) :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
  have h1 := Subgroup.card_mul_index (Subgroup.center ↥(J.map (MulAut.conj g).toMonoidHom))
  have h2 := Subgroup.card_mul_index (Subgroup.center J)
  rw [hJ, hZ] at h1
  have hpos : 0 < Nat.card ↥(Subgroup.center J) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem component_relIndex_dvd_card_mulAut [Finite G] (w : G) (X Q L : Subgroup G) (n : ℕ)
    (hQL : Q ≤ L) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hCQ : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (Q : Set G) → IsPGroup 3 P →
      Nat.card P ≤ 3)
    (hdich : ∀ N : Subgroup G, N ≤ Q →
      (∀ g ∈ L, g ^ n.factorial ∈ Subgroup.normalizer (N : Set G)) →
        N ≤ Subgroup.zpowers w ∨ N = Q)
    (hidx : ¬ (Subgroup.zpowers w).relIndex Q ∣ n.factorial)
    (hG : ¬ 9 ^ (n + 1) ∣ Nat.card G) :
    ∀ J : Subgroup G, IsComponentOf J X → 9 ∣ (Subgroup.center J).index →
      (Subgroup.zpowers w).relIndex Q ∣ Nat.card (MulAut J) := by
  classical
  set S : Finset (Subgroup G) :=
    (Set.toFinite {J : Subgroup G | IsComponentOf J X ∧ 9 ∣ (Subgroup.center J).index}).toFinset
    with hSdef
  have hmemS : ∀ J, J ∈ S ↔ IsComponentOf J X ∧ 9 ∣ (Subgroup.center J).index := fun J => by
    simp [hSdef]
  have hS : ∀ g ∈ L, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S := by
    intro g hg J hJ
    rw [hmemS] at hJ ⊢
    exact ⟨isComponentOf_map_conj_of_mem_normalizer hJ.1 (hLX hg),
      (index_center_map_conj J g).symm ▸ hJ.2⟩
  have hSn : S.card ≤ n := by
    by_contra hlt
    apply hG
    refine (pow_dvd_pow 9 (by omega)).trans (pow_card_dvd_of_commute S 9 ?_ ?_)
    · intro A hA B hB hne a ha b hb
      exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne ((hmemS A).1 hA).1
        ((hmemS B).1 hB).1 hne ha hb
    · exact fun J hJ => ((hmemS J).1 hJ).2
  have h9 : ∀ J ∈ S, 9 ∣ Nat.card J := fun J hJ =>
    ((hmemS J).1 hJ).2.trans (Subgroup.index_dvd_card _)
  intro J hJ hJ9
  exact relIndex_dvd_card_mulAut w Q L S n hQL hLQ hS hSn h9 hCQ hdich hidx J
    ((hmemS J).2 ⟨hJ, hJ9⟩)

end CFSG.HardMathSupport.MathTwE6
