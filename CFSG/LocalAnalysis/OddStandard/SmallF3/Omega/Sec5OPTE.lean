module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OddCoreThree
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPHypOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP4Ker
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPStep5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

theorem asc82P510TE_of
    (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b)
    (hy : Sec5B59Hyp) (h55 : Asc82Lemma55) (h58d : Asc82Lemma58d) (hFB : Asc82Sec5FactB5z)
    (h4 : Asc82FactReflCentQ6) (hD : Asc82FactQCentOrd6) (hU : Asc82FactPocketsUniq6)
    (hK : Asc82FactQCentTwo6) (hF1 : Asc82FactQCent6) : Asc82P510TE := by
  intro G _ _ t L S z r ρ B A φ K₁ K₂ a b h hs hTE
  let R : Subgroup G := sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)
  let T : Subgroup G := sec5p510_T t z R
  obtain ⟨X, hX, π, hyp⟩ := sec5op_exists_hyp_gen h hs
  have hout := sec5g_main hGold hN11a hN11b hy h55 h58d hFB h4 hD hU h hs hTE π
    hyp.surj hyp.ker
  have hA : Sec5GCaseI (sec5op_Tb z T π) ∨ Sec5GCaseII (sec5op_Tb z T π) := by
    have h' := hout
    unfold Sec5GOutcome at h'
    exact h'.2
  have hO3 : IsPGroup 3 (oddCoreIn L) := isPGroup_three_oddCoreIn h.toSec5Setting.isOm6Z2
  obtain ⟨K₁', hp₁, h2c₁, hcentR₁, -, -, hgen₁⟩ :=
    sec5op_lemmaK (K := K₁) hy hD hK hO3 h hs (Or.inl rfl)
  obtain ⟨K₂', hp₂, h2c₂, hcentR₂, -, -, hgen₂⟩ :=
    sec5op_lemmaK (K := K₂) hy hD hK hO3 h hs (Or.inr rfl)
  have hKH₁ : K₁' ≤ centralizer ({z} : Set G) := hp₁.2.1.trans inf_le_right
  have hKH₂ : K₂' ≤ centralizer ({z} : Set G) := hp₂.2.1.trans inf_le_right
  have hK₁'L : K₁' ≤ L := hp₁.2.1.trans inf_le_left
  have hKT₁ : ∀ k ∈ K₁', ∀ a ∈ T, k * a * k⁻¹ = a := by
    intro k hk a ha
    have haR : a ∈ R := sec5p510_T_le_R t z R ha
    have hkR : k ∈ centralizer (R : Set G) := hcentR₁ hk
    have hcomm : a * k = k * a := (Subgroup.mem_centralizer_iff.mp hkR) a haR
    rw [← hcomm]; group
  have hKT₂ : ∀ k ∈ K₂', ∀ a ∈ T, k * a * k⁻¹ = a := by
    intro k hk a ha
    have haR : a ∈ R := sec5p510_T_le_R t z R ha
    have hkR : k ∈ centralizer (R : Set G) := hcentR₂ hk
    have hcomm : a * k = k * a := (Subgroup.mem_centralizer_iff.mp hkR) a haR
    rw [← hcomm]; group
  have hker₁ : twoCoreIn K₁' ≤ sec5op_kerG z T π :=
    sec5op4_twoCore_le_kerG (z := z) (T := T) (π := π) hyp.surj hA hKH₁ hKT₁ hgen₁
  have hker₂ : twoCoreIn K₂' ≤ sec5op_kerG z T π :=
    sec5op4_twoCore_le_kerG (z := z) (T := T) (π := π) hyp.surj hA hKH₂ hKT₂ hgen₂
  have hQ₁ : twoCoreIn K₁ ≤ sec5op_kerG z T π := by
    rw [← h2c₁]; exact hker₁
  have hQ₂ : twoCoreIn K₂ ≤ sec5op_kerG z T π := by
    rw [← h2c₂]; exact hker₂
  have hQ : twoCoreIn K₁ ⊔ twoCoreIn K₂ ≤ sec5op_kerG z T π := sup_le hQ₁ hQ₂
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have hxE : x ∈ sec5p510_E t a b := by
      rw [← hTE]; exact hx
    have hyE : y ∈ sec5p510_E t a b := by
      rw [← hTE]; exact hy
    exact sec5p510_A_comm h (sec5p510_E_le_A h hs.ab hxE)
      (sec5p510_E_le_A h hs.ab hyE)
  refine ⟨K₁', hp₁, ?_⟩
  refine sec5op_final_of_odd (T := T) (π := π) hyp hKH₁ hgen₁ ?_
  intro k hk hkodd
  refine (sec5op_mem_kerG_iff (z := z) (T := T) (π := π)).mpr ⟨hKH₁ hk, ?_⟩
  refine sec5op_rho_eq_one (T := T) (π := π) hyp hA hTab (hKH₁ hk) hkodd (hKT₁ k hk) ?_
  intro y hyY hyt hyodd
  have hcent : y ∈ centralizer (L : Set G) :=
    sec5op_odd_cent_L hy hU hF1 h hs hyp hQ hyY hyt hyodd
  have hcomm : k * y = y * k := (Subgroup.mem_centralizer_iff.mp hcent) k (hK₁'L hk)
  rw [hcomm]; group

end CFSG.OddStandard.SmallF3.Omega
