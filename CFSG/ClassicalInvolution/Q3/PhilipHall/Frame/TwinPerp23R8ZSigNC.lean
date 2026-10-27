module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZSigN

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Sp62Rec
  CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Balance


section NotCentral

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g x : Y}

namespace ZCtx

variable (H : ZCtx n Y R S t K' W u e g x)
include H

theorem e_not_central : ¬ ∀ y ∈ p23XE R e x, e * y = y * e := by
  intro hcen
  have hEb : conjSub x (rLayer (Om R) e) ≤ rLayer (Om R) e := by
    rw [← rLayer_conj (R := R) x e]
    refine iSup₂_le fun Q hQ => iSup_le fun hQC => ?_
    rw [rSet_eq_of_isPGroup H.two] at hQ
    have hQEb : Q ≤ conjSub x (rLayer (Om R) e) := by
      rw [← rLayer_conj (R := R) x e]
      exact C22G.le_rLayer_of_le_centralizer (TC.mem_RSet_of_isPGroup hQ (H.two Q hQ)) hQC
    have hQN : Q ≤ p23XE R e x := hQEb.trans le_sup_right
    exact H.le_E_of_le_Ce hQ fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcen q (hQN hq)).symm
  have hcard : Nat.card (rLayer (Om R) e) ≤ Nat.card (conjSub x (rLayer (Om R) e)) :=
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge
  exact H.ne (Subgroup.eq_of_le_of_card_ge hEb hcard)

theorem et_not_central : ¬ ∀ y ∈ p23XE R e x, (e * t) * y = y * (e * t) := by
  intro hcen
  obtain ⟨f, hfinj, hfrange, hlab, -⟩ := H.hat.labels
  have hKE : tightCore R ≤ rLayer (Om R) e := H.K_le_E
  have htE : t ∈ rLayer (Om R) e := hKE H.hz.mem
  have htc : ∀ y ∈ rLayer (Om R) e, t * y = y * t := by
    intro y hy
    have hye : e * y = y * e :=
      (Subgroup.mem_centralizer_singleton_iff.mp (AAE7.rLayer_le_centralizer' (Om R) e hy)).symm
    have h1 := hcen y ((le_sup_left : rLayer (Om R) e ≤ p23XE R e x) hy)
    have h2 : e * (t * y) = e * (y * t) := by
      calc e * (t * y) = (e * t) * y := by group
        _ = y * (e * t) := h1
        _ = (y * e) * t := by group
        _ = (e * y) * t := by rw [hye]
        _ = e * (y * t) := by group
    exact mul_left_cancel h2
  obtain ⟨α, hα, b, hb⟩ := hlab.label (tightCore R) (CoreAssembly.mem_conjClass_self _) hKE
  set v : Wr 6 := f ⟨t, htE⟩ with hv
  have hvmem : v ∈ memAt α hα b := by
    rw [← hb]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr H.hz.mem)
  have hv1 : v ≠ 1 := by
    intro h
    have : (⟨t, htE⟩ : ↥(rLayer (Om R) e)) = 1 := hfinj (by rw [← hv, h, map_one])
    exact H.hz.ne_one (congrArg Subtype.val this)
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul]
    have : (⟨t, htE⟩ * ⟨t, htE⟩ : ↥(rLayer (Om R) e)) = 1 := Subtype.ext H.hz.sq
    rw [this, map_one]
  obtain ⟨g', hg', hgv⟩ := mFS_holds α hα b v hvmem hv1 hv2
  rw [← hfrange] at hg'
  obtain ⟨z, rfl⟩ := hg'
  apply hgv
  rw [hv, ← map_mul, ← map_mul]
  exact congrArg f (Subtype.ext (htc z z.2).symm)

end ZCtx

end NotCentral

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZSig
