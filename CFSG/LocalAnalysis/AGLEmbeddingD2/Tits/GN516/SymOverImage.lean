module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BlockOver
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbReduceBasic

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem inf_le_gnImg_of_isSylowTwoOf (hX : GNSetting X T) {L P : Subgroup (X ⧸ gnC T)}
    (hPb : IsMinOverBorel L (gnImg T T ⊓ L) P) {S K : Subgroup X} (hST : S ≤ T)
    (hSK : IsSylowTwoOf S K)
    (hmap : gnImg T K = conjClosure (pElementSubgroup 2 (conjClosure P
      (gnImg T S ⊓ Subgroup.normalizer (L : Set (X ⧸ gnC T))))) (gnImg T S) ⊔ gnImg T S) :
    gnImg T T ⊓ L ≤ gnImg T S := by
  have hT2 : IsPGroup 2 (gnImg T T) := hX.sylow.2.1.map _
  have hU : gnImg T T ⊓ L ≤ pElementSubgroup 2 P := by
    intro x hx
    have hxN : x ∈ L ⊓ Subgroup.normalizer ((gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) := ⟨hx.2, Subgroup.le_normalizer hx⟩
    have hxP : x ∈ P := hPb.2.1.le hxN
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx.1⟩
    have hk' : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    unfold pElementSubgroup
    exact Subgroup.subset_closure ⟨hxP, j, hj⟩
  have hPK : pElementSubgroup 2 P ≤ gnImg T K := pElementSubgroup_le_over hmap
  have hS' : IsSylowTwoOf (gnImg T S) (gnImg T K) :=
    GOrbReduce.isSylowTwoOf_map (QuotientGroup.mk' (gnC T)) hSK
  have hA : gnImg T K ⊓ gnImg T T ≤ gnImg T S :=
    (A4.isSylowTwoOf_iff_maximal.1 hS').2.2 _ inf_le_left (hT2.to_le inf_le_right)
      (le_inf hS'.1 (Subgroup.map_mono hST))
  exact (le_inf (hU.trans hPK) inf_le_left).trans hA

end CFSG.AGLEmbeddingD2.Tits.GN516
