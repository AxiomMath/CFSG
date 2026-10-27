module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YWStruct
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YAbelian
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YInterface

public section

namespace CFSG.EvenSporadicStandard.J4Std.YExists

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

theorem exists_Y_struct [Finite G] (hS : Setting L z) (hD : LocalData L U T0) (hM : ModData L U)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u)
    (hcard : Nat.card (Csub U z) = 2 ^ 23) : ∃ Y : Subgroup G, YStruct L U z Y := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hzW : z ∈ Csub U z := V_le_Csub hS hD z_mem_V
  obtain ⟨Y, hUY, hYW, hzY, hHY, hcov⟩ := hM.split z (Csub U z) hzW hS.z_mul_self
    (z_not_mem_U hS hUL) (fun h hh => hS.z_comm h (Hloc_le_L hh))
    (fun u hu => z_comm_U hS hUL hu) (le_trans (U_le_V (z := z)) (V_le_Csub hS hD))
    (fun w hw u hu => (mem_Csub.1 hw).2 u hu) (fun w hw => sq_mem_U hS hD htrans hw)
    (fun h hh w hw => (phiVal_conj hS hD hh hw).1)
    (fun w hw => phiVal_mem hS hD (mem_Csub.1 hw).1) (exists_phi_eq hS hD hcard)
    (fun w hw hzw => Csub_comm_mem_V hS hD hw hzw)
  exact ⟨Y, hUY, hYW, hzY, hcov, hHY⟩

theorem yFacts_of_struct [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u)
    (hcard : Nat.card (Csub U z) = 2 ^ 23) {Y : Subgroup G} (hY : YStruct L U z Y) :
    YFacts L U (phiVal z) Y where
  U_le := hY.U_le
  central := fun y hy u hu => (mem_Csub.1 (hY.le_W hy)).2 u hu
  sq_mem := fun y hy => sq_mem_U hS hD htrans (hY.le_W hy)
  phi_mem := fun y hy => phiVal_mem hS hD (mem_Csub.1 (hY.le_W hy)).1
  phi_mul := fun y hy y' hy' => phiVal_mul hS hD (hY.le_W hy) (hY.le_W hy')
  phi_ker := fun y hy h1 => by
    have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
    obtain ⟨u, hu, hcase⟩ := (mem_Vsub_iff hS hUL).1
      (Csub_comm_mem_V hS hD (hY.le_W hy) ((phiVal_eq_one_iff hS).1 h1))
    rcases hcase with h | h
    · rw [h]
      exact hu
    · exfalso
      apply hY.z_not_mem
      have hz : z = y * u⁻¹ := by rw [h]; group
      rw [hz]
      exact Y.mul_mem hy (Y.inv_mem (hY.U_le hu))
  phi_surj := fun u hu => by
    obtain ⟨w, hw, hwu⟩ := exists_phi_eq hS hD hcard u hu
    rcases hY.cover w hw with hwY | hzwY
    · exact ⟨w, hwY, hwu⟩
    · refine ⟨z * w, hzwY, ?_⟩
      have hzW : z ∈ Csub U z := V_le_Csub hS hD z_mem_V
      have hz1 : phiVal z z = 1 := (phiVal_eq_one_iff hS).2 rfl
      rw [phiVal_mul hS hD hzW hw, hz1, one_mul, hwu]
  phi_conj := fun h hh y hy =>
    ⟨hY.H_inv h hh y hy, (phiVal_conj hS hD hh (hY.le_W hy)).2⟩

end CFSG.EvenSporadicStandard.J4Std.YExists

namespace CFSG.EvenSporadicStandard.J4Std

theorem exists_Y {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L U T0 : Subgroup G} {z p q u0 : G}
    (hS : Setting L z) (hD : LocalData L U T0) (hD11 : LocalData11 L U p q u0)
    (hM : ModData L U) :
    ∃ Y : Subgroup G, YStruct L U z Y ∧ ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
  have htrans := trans_of_simple hnonab hS hD
  have hcard := card_Csub hnonab hS hD hD11
  obtain ⟨Y, hY⟩ := YExists.exists_Y_struct hS hD hM htrans hcard
  exact ⟨Y, hY, YExists.Y_abelian hD (YExists.yFacts_of_struct hS hD htrans hcard hY) hM.fix
    hM.triple⟩

end CFSG.EvenSporadicStandard.J4Std
