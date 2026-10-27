module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AF4Rad
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
import CFSG.GroupTheory.PGroupFixedPointCongruence

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA


theorem f4two_core {G : Type} [Group G] [Finite G] (hG : catalogIs G S9.isF4two)
    {Bb : Subgroup G} (hB : IsElemAbelian 3 Bb) (h27 : Nat.card Bb = 27)
    {d : G} (hd : d ∈ Bb)
    (hC : ∀ W : Subgroup G, IsPGroup 2 W → W ≤ Subgroup.centralizer ({d} : Set G) →
      Bb ≤ Subgroup.normalizer (W : Set G) → W = ⊥)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hBW : Bb ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hW1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatB.I2610.exists_adjointGroup_of_catalogIs_isF4two hG
  obtain ⟨R', hR'card, hR'N⟩ := exists_radical_of_normalizes_F4two hK
    ((Subgroup.map_eq_bot_iff_of_injective W (f := e.toMonoidHom) e.injective).not.2 hW1)
    (hW.map e.toMonoidHom)
    ((Subgroup.map_mono hBW).trans (Subgroup.le_normalizer_map e.toMonoidHom))
    (dvd_of_eq (by rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h27]))
  obtain ⟨R, hR⟩ : ∃ R : Subgroup G, R = R'.map e.symm.toMonoidHom := ⟨_, rfl⟩
  have hRcard : Nat.card R = 2 ^ 15 := by
    rw [hR, Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hR'card]
  have hBR : Bb ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR, ← Subgroup.map_equiv_normalizer_eq]
    intro b hb
    exact ⟨e b, hR'N ⟨b, hb, rfl⟩, by simp⟩
  have hBd : Bb ≤ Subgroup.centralizer ({d} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact hB.comm hd hb
  have hRd : R ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ :=
    hC _ ((IsPGroup.of_card hRcard).to_le inf_le_left) inf_le_right
      ((le_inf hBR (hBd.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hmod := CFSG.GroupTheory.card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot
    hB.isPGroup hBR (eq_bot_iff.2 ((inf_le_inf_left R
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd))).trans hRd.le))
  rw [hRcard] at hmod
  exact absurd hmod (by decide)

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
