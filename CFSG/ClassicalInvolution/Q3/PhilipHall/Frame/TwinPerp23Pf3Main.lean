module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Mem
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Fuse

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_std (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ A A' : Subgroup Y, IsSylow2In A (tightCore R) ∧ IsSylow2In A' K' ∧
      A ≤ Subgroup.centralizer ({e} : Set Y) ∧ A' ≤ Subgroup.centralizer ({e} : Set Y) ∧
      IsPGroup 2 ↥(A ⊔ A') ∧ Commutes A A' := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  obtain ⟨S₀, R₀, R', hWS, hR₀, hR', hRS, hR'S⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hc.std.hW hc.std.htW
  have hRD : R₀ ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK hR₀) hRS
  have hR'D : R' ∈ DSet (Om R) W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS
      (mem_RSet_of_isSylow2In hc.std.hK'.1 hR') hR'S
  have hNe := normalizer_le_centralizer_e hc.data
  have h2 : IsPGroup 2 ↥(R₀ ⊔ R') := S₀.isPGroup'.to_le (sup_le hRS hR'S)
  exact ⟨R₀, R', hR₀, hR', hRD.2.trans hNe, hR'D.2.trans hNe, h2,
    CFSG.ClassicalInvolution.Q8P.Asc77.HypOmegaMod.commutes_of_twin_of_isPGroup hΩ hK
      hc.std.hK'.1 hc.std.hne.symm hz hzK' hR₀.1 hR'.1 h2⟩

theorem fuse_KK (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) {R₁ R₂ : Subgroup Y} (hR₁ : IsSylow2In R₁ (tightCore R))
    (hR₂ : IsSylow2In R₂ K') (hcm : Commutes R₁ R₂) {x y : Y} (hx : x ∈ R₁) (hy : y ∈ R₂)
    (ox : orderOf x = 4) (oy : orderOf y = 4) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), c * u * c⁻¹ = x * y := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨A, A', hA, hA', hAe, hA'e, hAA', hAc⟩ := exists_std hc
  have hd := hc.data
  have huM : u ∈ tightCore R ⊔ K' := hd.hu
  refine fuse_general hΩ hK hc.std.hK'.1 hc.std.hne hz hzK' hA hA' hAc ?_ huM hd.hu1 hd.huz hd.hu2
    hR₁ hR₂ hcm hx hy ox oy
  intro a ha x' hx' b hb y' hy' haa hxx hbb hyy
  exact fuse_std hP hc.std.perp hc.std.hK' hc.std.hne hd.he2 hd.he1 hno hA hA' hAe hA'e hAA'
    ha hx' hb hy' haa hxx hbb hyy

end Fuse

theorem p23FuseN {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) : P23FuseN n := by
  intro Y _ _ R S t K' W u e g hc hno L hL L' hL' hne R₁ R₂ hR₁ hR₂ hcm x hx y hy ox oy
  have hKt := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hLc : L = tightCore R ∨ L = K' := by
    have := hL; rw [hKt] at this; simpa [Set.mem_insert_iff] using this
  have hL'c : L' = tightCore R ∨ L' = K' := by
    have := hL'; rw [hKt] at this; simpa [Set.mem_insert_iff] using this
  rcases hLc with hLK | hLK <;> rcases hL'c with hL'K | hL'K
  · exact absurd (hL'K.trans hLK.symm) hne
  · rw [hLK] at hR₁
    rw [hL'K] at hR₂
    exact fuse_KK hP hc hno hR₁ hR₂ hcm hx hy ox oy
  · rw [hLK] at hR₁
    rw [hL'K] at hR₂
    obtain ⟨c, hct, hcu⟩ := fuse_KK hP hc hno hR₂ hR₁ (fun a ha b hb => (hcm b hb a ha).symm)
      hy hx oy ox
    exact ⟨c, hct, by rw [hcu, ← hcm x hx y hy]⟩
  · exact absurd (hL'K.trans hLK.symm) hne

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
