module

public import CFSG.Monster.GMS.LeechOddThreeC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeD

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeC

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

section Leech


theorem card_centralizer_inf_le_of_threeC (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {α β t : G} (hα : IsConj a α) (hβ : β ∈ typeSet a z₀ α .threeC)
    (ht : t ∈ Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({β} : Set G))
    (ht2 : orderOf t = 2) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({α * β} : Set G)) ≤
      3 * 92897280 := by
  have hwB : IsConj z₀ t := threeC_isConj I hG hα hβ ht ht2
  obtain ⟨⟨hβa, hβne, hodd, -⟩, hk⟩ := hβ
  have hY : IsOddPair a t α β := IsOddPair.of_mem_inf hα hβa hβne.symm hodd ht
  have hty : LeechOddType t α β 1 := hk t ht hwB
  obtain ⟨L⟩ := S365.exists_leechSystem_of_isConj hG hwB
  have hyp := LeechOdd.oddPairHyp I hG hwB hY L
  have hot := LeechOdd.oddType I hG hwB hY L hty
  obtain ⟨g, hgr, hgs⟩ := CFSG.Sporadic.Co1.Module.Odd.exists_conj_base hyp.twoA hyp.conj
    hyp.ne hyp.four hot
  have hαβ : α * β ∈ Subgroup.centralizer ({t} : Set G) := mul_mem hY.1 hY.2.1
  have hφ : L.φ ⟨α * β, hαβ⟩ = L.φ ⟨α, hY.1⟩ * L.φ ⟨β, hY.2.1⟩ := by
    rw [← map_mul]
    rfl
  have hconj : IsConj TabCo1ThreeD.c1 (L.φ ⟨α * β, hαβ⟩) := by
    rw [hφ]
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [← hgr, ← hgs]
    unfold TabCo1ThreeD.c1
    group
  have h1 := (L.involution_bounds hαβ).1
  have h2 : (co1Fix (L.φ ⟨α * β, hαβ⟩)).ncard = 2 ^ 8 := TabCo1ThreeD.ncard_fix_threeD hconj
  have h3 := TabCo1ThreeD.card_centralizer_threeD_le hconj
  rw [h2] at h1
  calc _ ≤ 2 * (2 ^ 8 * Nat.card ↥(Subgroup.centralizer
          ({L.φ ⟨α * β, hαβ⟩} : Set Co1))) := h1
    _ ≤ 2 * (2 ^ 8 * 544320) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = 3 * 92897280 := by norm_num

end Leech

end CFSG.HardMathSupport.Dickson.I271.TabMThreeC
