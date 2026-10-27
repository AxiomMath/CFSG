module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Uni
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L515B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma515ab_of (hS : Asc82Lemma515Setting) (h514 : Asc82Lemma514)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h56 : Asc82Lemma56) (hZ : Asc82ZExists)
    (hB : Asc82Sec5FactB5) (h512b : Asc82Lemma512b) (h512K : Asc82Lemma512K) (tab : Asc82Tab5) :
    Asc82Lemma515a ∧ Asc82Lemma515b := by
  refine ⟨?_, ?_⟩
  · intro G _ _ t L S z r B A K₁ K₂ h c d hd
    obtain ⟨I, hs, P, hP, hPI⟩ := hS G t L S z r B A K₁ K₂ h c d hd
    obtain ⟨hlay, hcent, hodd, hT, S', z', r', B', A', hR⟩ :=
      sec5_setting_data h52a h52b h56 hZ hB h512b hs
    rw [hlay]
    exact hT
  · intro G _ _ t L S z r B A K₁ K₂ h c d hd
    obtain ⟨I, hs, P₀, hP₀, hP₀I⟩ := hS G t L S z r B A K₁ K₂ h c d hd
    obtain ⟨hlay, hcent, hodd, hT, S', z', r', B', A', hR⟩ :=
      sec5_setting_data h52a h52b h56 hZ hB h512b hs
    obtain ⟨i, j, hij, hdij⟩ := sec5_delta_support h514 c hd
    obtain ⟨l, m, hlm, hli, hlj, hmi, hmj⟩ := sec5_exists_compl i j hij
    have key : ∀ Q : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d Q →
        Q = Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m := fun Q hQ =>
      (sec5_kOf_iff h514 c hij hlm hli hlj hmi hmj hd.1 hd.2.1 hdij Q).mp hQ
    have hle : Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m ≤ I := (key P₀ hP₀) ▸ hP₀I
    have hp : Sec5Pair (Kfam5 K₁ K₂ h l) (Kfam5 K₁ K₂ h m) z :=
      Sec5Pair.of_quad (sec5b517_quad h514 c) hlm
    have hM := (sec5_pair_eq_twoRes tab h512K hs hcent hR c.pocket.1 hd.2.1.symm hp hle).1
    refine ⟨⟨P₀, hP₀⟩, ?_⟩
    intro P hP
    calc P = Kfam5 K₁ K₂ h l ⊔ Kfam5 K₁ K₂ h m := key P hP
      _ = twoRes (centralizer ({z} : Set G) ⊓ I) := hM
      _ = twoRes (centralizer ({z} : Set G) ⊓ layerC5 d) := by rw [hlay]

end CFSG.OddStandard.SmallF3.Omega
