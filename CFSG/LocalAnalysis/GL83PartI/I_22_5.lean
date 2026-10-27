module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup

public section

namespace GL83

open CFSG.Open GL83.CompFam

theorem I_22_5_proved :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → GLAPPrimeCore p X = ⊥ →
      ∀ K : Subgroup X, IsComponentOf K ⊤ →
        ∀ B : Subgroup X, IsElemAbelian p B →
          pRank p (⊤ : Subgroup (MulAut ↥K)) < pRank p B →
          ∀ k : ℕ, 1 ≤ k → k + pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ pRank p B →
            K ≤ GLBCore p k B := by
  intro X _ _ p hp hcore K hK B hB _ k _ hkr
  have : Fact p.Prime := ⟨hp⟩
  have hr1 := one_le_pRank_aut hp hcore hK
  have hF := isFam_conjSet hB hK
  have hBbig : p ^ (k + pRank p (⊤ : Subgroup (MulAut ↥K))) ≤ Nat.card B := by
    obtain ⟨E, hEB, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt B
    calc p ^ (k + pRank p (⊤ : Subgroup (MulAut ↥K))) ≤ p ^ pRank p B :=
          Nat.pow_le_pow_right hp.pos hkr
      _ = Nat.card E := hcard.symm
      _ ≤ Nat.card B := Subgroup.card_le_of_le hEB
  have h := hF.layer_le_centGen k (mem_conjSet_self B K) hr1 hBbig (card_stab_le hB K)
  refine (le_layer (mem_conjSet_self B K)).trans (h.trans ?_)
  refine iSup_le fun E => iSup_le fun hEB => iSup_le fun hEk => ?_
  have hEe : IsElemAbelian p E := elem_mono hB hEB
  obtain ⟨j, hj⟩ := exists_card_eq_pow hEe
  have hjk : k ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hEk)
  have hrk : k ≤ pRank p E := hjk.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEe hj)
  exact inf_le_right.trans
    ((Subgroup.centralizer_le_normalizer (E : Set X)).trans (le_sSup ⟨E, hEB, hrk, rfl⟩))

end GL83
