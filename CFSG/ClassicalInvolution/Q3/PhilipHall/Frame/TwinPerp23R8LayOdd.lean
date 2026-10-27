module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8LayNorm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU29

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lay

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section Odd

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem oddCoreOf_centralizer_u_le_sigmaStarNorm (hc : P23Cfg n Y R S t K' W u e g) :
    oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ≤ sigmaStarNorm (Om R) (tightCore R) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hue_t : u * e * t = t * (u * e) := hWab _ (W.mul_mem hd.huW heW) _ hd.hzW
  have hut : t * u = u * t := hWab _ hd.hzW _ hd.huW
  have hne : t ≠ u * e := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := e_decomp hc
    exact fun h' => h h'.symm
  set Q := oddCoreOf (Subgroup.centralizer ({u} : Set Y)) with hQ
  set A : Subgroup Y := Subgroup.closure ({t, u * e} : Set Y) with hAdef
  have hA : IsElemAbelian2 A 2 :=
    T7A.isElemAbelian2_closure_pair hz.sq (ue_sq hc) hz.ne_one (ue_ne_one hc) hne hue_t.symm
  have hAC : A ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [hAdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hut
    · exact ue_comm_u hc
  have hAN : A ≤ Subgroup.normalizer (Q : Set Y) := fun a ha => mem_normalizer_oddCoreOf (hAC ha)
  have hcompl : ¬ 2 ∣ Nat.card Q := (odd_natCard_oddCoreOf _).not_two_dvd_nat
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two A Q (fun m => Subtype.ext (by simpa [pow_two] using hA.2 m m.2)) hA.1 hcompl hAN
  refine hgen.le.trans (iSup_le fun m => iSup_le fun hm => inf_le_right.trans ?_)
  rcases C25Y.mem_closure_pair hz.sq (ue_sq hc) hue_t.symm m.2 with h | h | h | h
  · exact absurd (Subtype.ext h) hm
  · rw [h]
    exact R56.centralizer_t_le_sigmaStarNorm hc
  · rw [h]
    exact centralizer_ue_le_sigmaStarNorm hc
  · rw [h, ← hue_t]
    exact centralizer_uet_le_sigmaStarNorm hc

end Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lay
