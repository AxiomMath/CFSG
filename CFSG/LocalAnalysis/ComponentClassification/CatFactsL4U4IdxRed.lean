module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxSpD
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxKa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

namespace IdxRed

variable {Y : Type} [Group Y]

theorem center_eq_bot_of_alt {n : ℕ} (hn : 5 ≤ n) (e : Y ≃* alternatingGroup (Fin n)) :
    center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hcen : e y ∈ center (alternatingGroup (Fin n)) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, mem_center_iff.mp hy w]
  rw [alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ n))] at hcen
  have : e y = e 1 := by rw [map_one]; exact mem_bot.mp hcen
  exact mem_bot.mpr (e.injective this)

theorem center_eq_bot_of_psl2 {p f : ℕ} (hY : Blueprint.LieModel Y .PSL 2 p f) :
    center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  apply mem_bot.mpr
  apply Idx.conj_injective_of_lieModel hY
  ext z
  simp only [MulAut.conj_apply, map_one, MulAut.one_apply]
  rw [← mem_center_iff.mp hy z, mul_inv_cancel_right]

end IdxRed

theorem cfProp23IndexReduced : CFProp23IndexReduced := by
  intro H _ _ h htab
  rcases htab with ⟨hKa, -, ⟨n, hn, ⟨eJ⟩, ⟨eK⟩⟩ | ⟨p, f, hp, hp2, hf, -, hJ, hK⟩⟩ |
      ⟨p, f, hp, hp2, hf, h5, hJ, hKa, hK⟩ | ⟨hJ, hKa, hK⟩ | ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩
  ·
    refine IdxKa.T_le_of_ne h hKa (IdxRed.center_eq_bot_of_alt (by omega) eJ) ?_
    rw [Nat.card_congr eK.toEquiv, Nat.card_congr eJ.toEquiv]
  ·
    refine IdxKa.T_le_of_ne h hKa (IdxRed.center_eq_bot_of_psl2 hJ) ?_
    rw [Idx.card_of_lieModel_psl2 hp2 hK, Idx.card_of_lieModel_psl2 hp2 hJ]
  ·
    exact Idx.T_le_case_psl2 h hp hp2 hf h5 hJ hKa hK
  ·
    exact Idx.T_le_case_alt h (n := 6) (by norm_num) hJ hKa hK
  ·
    exact IdxSp.T_le_case_psp h hp hp2 hf hJ hKa hK

end CFSG.ComponentClassification.CatFactsL4U4
