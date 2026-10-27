module

public import CFSG.CGT.PushingUpLit.BHS.HomTransfer

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin

theorem minPar_of_minParabolic {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
    (h : CFSG.Quasithin.MinParabolic H T M) :
    CFSG.CGT.PushingUpLit.BHS.MinPar H T M := by
  refine ⟨⟨h.isSylow.1, h.isSylow.2.1, h.isSylow.2.2⟩, h.not_normal, h.le, h.maximal.1, ?_⟩
  intro X hTX hXH
  obtain ⟨N, hXN, hN⟩ := Finite.exists_le_maximal
    (α := Subgroup G) (p := fun K => K < H ∧ X ≤ K) (a := X) ⟨hXH, le_rfl⟩
  have hNmax : IsMaxSubgroupIn H N := by
    refine ⟨hN.1.1, fun K hNK hKH => ?_⟩
    by_contra hKH'
    have hKlt : K < H := lt_of_le_of_ne hKH hKH'
    have hpK : K < H ∧ X ≤ K := ⟨hKlt, hXN.trans hNK.le⟩
    exact lt_irrefl N (lt_of_lt_of_le hNK (hN.2 hpK hNK.le))
  have hNM : N = M := h.eq_of_maximal hNmax (hTX.trans hXN)
  rw [← hNM]
  exact hXN

end CFSG.AGLEmbeddingD2.Tits.E23

end
