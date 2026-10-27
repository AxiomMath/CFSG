module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E V : Subgroup Γ}

theorem commutator_eq_blockW (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hVQ : V ≤ pCoreOf 2 G) (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) (hne : ⁅E, V⁆ ≠ ⊥) :
    ⁅E, V⁆ = blockW E := by
  obtain ⟨hle, hfac, -⟩ := bridge_data_of_isBTBlock hG hT hE hVQ hEV hne
  refine le_antisymm hle ?_
  have hEn : E ≤ Subgroup.normalizer ((⁅E, V⁆ : Subgroup Γ) : Set Γ) := fun g hg =>
    mem_normalizer_commutator (Subgroup.le_normalizer hg) (hEV hg)
  calc blockW E = ⁅blockW E, E⁆ := by rw [blockW_eq_pCoreOf hE]; exact hE.perfect.symm
    _ ≤ ⁅E, V⁆ := by
      rw [Subgroup.commutator_le]
      intro w hw e he
      obtain ⟨p, hp, c, hc, rfl⟩ := hfac w hw
      have hce : c * e = e * c := (Subgroup.mem_centralizer_iff.mp hc.2 e he).symm
      have h1 : ⁅p * c, e⁆ = ⁅p, e⁆ := by
        simp only [commutatorElement_def]
        calc p * c * e * (p * c)⁻¹ * e⁻¹ = p * (c * e) * c⁻¹ * p⁻¹ * e⁻¹ := by group
          _ = p * (e * c) * c⁻¹ * p⁻¹ * e⁻¹ := by rw [hce]
          _ = p * e * p⁻¹ * e⁻¹ := by group
      rw [h1]
      have := (Subgroup.mem_normalizer_iff.mp (hEn he) p⁻¹).mp (inv_mem hp)
      have h2 : ⁅p, e⁆ = p * (e * p⁻¹ * e⁻¹) := by simp only [commutatorElement_def]; group
      rw [h2]
      exact mul_mem hp this

theorem inf_centralizer_eq_pCoreOf (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hVQ : V ≤ pCoreOf 2 G) (hEV : E ≤ Subgroup.normalizer (V : Set Γ)) (hne : ⁅E, V⁆ ≠ ⊥) :
    E ⊓ Subgroup.centralizer (V : Set Γ) = pCoreOf 2 E := by
  obtain ⟨-, -, hker⟩ := bridge_data_of_isBTBlock hG hT hE hVQ hEV hne
  rw [hker, blockW_eq_pCoreOf hE]
  exact inf_centralizer_pCoreOf_eq (charTwo_of_isBTBlock hG hT hE) hE.elemAbelian.1

omit [Finite Γ] in
theorem conjSub_mem_btBlocksMax {E : Subgroup Γ} (hE : E ∈ btBlocksMax G T) {g : Γ} (hg : g ∈ G) :
    conjSub g E ∈ btBlocksMax G T := by
  refine ⟨conjSub_mem_btBlocksG hE.1 hg, fun F hF hle => ?_⟩
  have hF' : conjSub g⁻¹ F ∈ btBlocksG G T := conjSub_mem_btBlocksG hF (G.inv_mem hg)
  have hle' : E ≤ conjSub g⁻¹ F := by
    have := conjSub_mono g⁻¹ hle
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  have heq := hE.2 _ hF' hle'
  have : F = conjSub g (conjSub g⁻¹ F) := by
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  rw [this, heq]

end CFSG.CGT.PushingUpLit.BHS7
