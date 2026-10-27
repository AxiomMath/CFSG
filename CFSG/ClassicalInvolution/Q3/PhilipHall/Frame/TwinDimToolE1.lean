module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A03
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf4Type

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section E1

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem e_decomp (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ (R₁ R₁' : Subgroup Y) (b₁ b' : Y), IsSylow2In R₁ (tightCore R) ∧ IsSylow2In R₁' K' ∧
      R₁ ∈ DSet (Om R) W ∧ R₁' ∈ DSet (Om R) W ∧ Commutes R₁ R₁' ∧ b₁ ∈ R₁ ∧ b' ∈ R₁' ∧
      b₁ * b₁ = t ∧ b' * b' = t ∧ u = b₁ * b' ∧ u * e ≠ t := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  have hd := hc.data
  obtain ⟨S₀, R₁, R₁', hWS, hR₁, hR₁', hRS, hR'S⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hc.std.hW hc.std.htW
  have hRD : R₁ ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK hR₁) hRS
  have hR'D : R₁' ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS
      (mem_RSet_of_isSylow2In hc.std.hK'.1 hR₁') hR'S
  have hcomm : Commutes R₁ R₁' :=
    hΩ.commutes_of_twin_of_isPGroup hK hc.std.hK'.1 hc.std.hne.symm hz hz' hR₁.1 hR₁'.1
      (S₀.isPGroup'.to_le (sup_le hRS hR'S))
  obtain ⟨b, hbRW, hb4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hc.std.hW hRD
  obtain ⟨b', hb'RW, hb'4⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four hΩ hc.std.hW hR'D
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hc.std.hW
  have hu := CFSG.ClassicalInvolution.Q8P.Asc77.T7E.involution_cases hs hR₁ hR₁' hRS hR'S hbRW.1
    hb'RW.1 hb4 hb'4 hd.hu (hWS hd.huW) hd.hu2 hd.hu1 hd.huz (hWab _ hd.huW _ hbRW.2)
    (hWab _ hd.huW _ hb'RW.2)
  have hbK : b ∈ tightCore R := hR₁.1 hbRW.1
  have hb'K' : b' ∈ K' := hR₁'.1 hb'RW.1
  have hbb : b * b = t := TwinPerp.sq_eq_of_orderOf_four hz hbK hb4
  have hb'b' : b' * b' = t := TwinPerp.sq_eq_of_orderOf_four hz' hb'K' hb'4
  have hztR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  have hzc : ∀ x ∈ tightCore R, t * x = x * t := fun x hx => hz.commute_of_mem hx
  obtain ⟨b₁, hb₁R, ob₁, hub₁, hbc⟩ : ∃ b₁ ∈ R₁, b₁ * b₁ = t ∧ u = b₁ * b' ∧
      ∀ r ∈ R₁, r * b₁ = b₁ * r → r * b = b * r := by
    rcases hu with hu | hu
    · exact ⟨b, hbRW.1, hbb, hu, fun r _ h => h⟩
    · refine ⟨t * b, R₁.mul_mem hztR hbRW.1, ?_, by rw [hu]; group, ?_⟩
      · have hzb : t * b = b * t := hzc b hbK
        calc t * b * (t * b) = t * (b * t) * b := by group
          _ = t * (t * b) * b := by rw [← hzb]
          _ = (t * t) * (b * b) := by group
          _ = t := by rw [hz.sq, hbb, one_mul]
      · intro r hr h
        have hzr : t * r = r * t := hzc r (hR₁.1 hr)
        have h1 : t * (r * b) = t * (b * r) := by
          calc t * (r * b) = r * t * b := by rw [← mul_assoc, ← hzr, mul_assoc]
            _ = r * (t * b) := by group
            _ = t * b * r := h
            _ = t * (b * r) := by group
        exact mul_left_cancel h1
  have hNe := normalizer_le_centralizer_e hd
  have hQ : IsQuatSub R₁ := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hR₁)
  refine ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'RW.1, ob₁, hb'b', hub₁, ?_⟩
  intro hte
  have hez : e = u * t := by
    have h1 : u * (u * e) = e := by rw [← mul_assoc, hd.hu2, one_mul]
    rw [← h1, hte]
  have hbc' : ∀ r ∈ R₁, r * b = b * r := by
    intro r hr
    refine hbc r hr ?_
    have hre : r * e = e * r := Subgroup.mem_centralizer_singleton_iff.mp (hNe (hRD.2 hr))
    have hzr : r * t = t * r := (hzc r (hR₁.1 hr)).symm
    have hrb' : r * b' = b' * r := hcomm r hr b' hb'RW.1
    have huz : u = e * t := by
      rw [hez, mul_assoc, hz.sq, mul_one]
    have hru : r * u = u * r := by
      rw [huz]
      calc r * (e * t) = (r * e) * t := by group
        _ = (e * r) * t := by rw [hre]
        _ = e * (r * t) := by group
        _ = e * (t * r) := by rw [hzr]
        _ = (e * t) * r := by group
    rw [hub₁] at hru
    have h2 : (r * b₁) * b' = (b₁ * r) * b' := by
      calc (r * b₁) * b' = r * (b₁ * b') := by group
        _ = (b₁ * b') * r := hru
        _ = b₁ * (b' * r) := by group
        _ = b₁ * (r * b') := by rw [hrb']
        _ = (b₁ * r) * b' := by group
    exact mul_right_cancel h2
  have := hQ.sq_eq_one_of_central hbRW.1 (fun y hy => (hbc' y hy).symm)
  rw [hbb] at this
  exact hz.ne_one this

end E1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
