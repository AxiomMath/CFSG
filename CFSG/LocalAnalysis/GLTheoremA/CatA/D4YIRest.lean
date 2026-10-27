module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T

theorem d4BigCoreRest2_holds : D4BigCoreRest2 := by
  classical
  intro H _ _ K B hK hn hKc hB hBK hout hcase hU
  obtain ⟨c, hcN, hcB, hcout, hB81, ⟨E4, hE4K, hE4el, hE4c, hE4cc⟩,
    ⟨E3, W3, hE3K, hE3el, hE3c, hE3cc, hW32, hW3ne, hE3W, hcW3, hW3K⟩, hX⟩ :=
    rest2_data hK hn hB hBK hout hU
  have hBopos : 0 < Nat.card (Bo K B) := Nat.card_pos
  have hBoN : ∀ {W : Subgroup H}, W ≤ K → Bo K B ≤ Subgroup.normalizer (W : Set H) :=
    fun hWK s hs => mem_normalizer_of_centralizes fun w hw => Bo_cent hs w (hWK hw)
  rcases hcase with hall | ⟨hmax, T, hT2, hTne, hBT, hTK⟩
  · exact core3_all hKc hB hE4K hE4el hcB hcN hcout hE4cc (by rw [hE4c]; omega) hall
  · rcases hX with ⟨E, W, hEK, hEel, hEc, hEcc, hW2, hWne, hEW, hcW, hWK⟩ | hodd
    · exact core3_two hKc hB hEK hEel hcB hcN hcout hEcc hW2 hWne hEW hcW (hBoN hWK)
        (by rw [hEc]; omega) hmax
    · by_cases hTc : T ≤ Subgroup.centralizer (K : Set H)
      · refine core3_two hKc hB hE4K hE4el hcB hcN hcout hE4cc hT2 hTne ?_ (hBT hcB)
          (fun s hs => hBT (Subgroup.mem_inf.1 hs).1) (by rw [hE4c]; omega) hmax
        intro x hx
        exact mem_normalizer_of_centralizes fun t ht =>
          Subgroup.mem_centralizer_iff.1 (hTc ht) x (hE4K hx)
      · have h27 := hodd T hT2 hTne hBT hTK hTc
        exact core3_two hKc hB hE3K hE3el hcB hcN hcout hE3cc hW32 hW3ne hE3W hcW3 (hBoN hW3K)
          (by rw [hE3c]; omega) hmax

end CFSG.LocalAnalysis.GLTheoremA.D4Y
