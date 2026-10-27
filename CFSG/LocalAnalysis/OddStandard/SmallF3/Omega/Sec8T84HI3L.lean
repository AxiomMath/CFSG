module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HI3N

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem sec8t84h_lift [Finite G] (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {S : Subgroup G}
    (hS : IsSylow2Of S (Subgroup.normalizer (L : Set G))) {y' : G} (hy'S : y' ∈ S)
    {x'' : ProjOrth Q}
    (hx : projOrthToProjSim Q x'' = ffTheta6M hQ hdim hsgn e ⟨y', hS.1 hy'S⟩)
    {B : Subgroup (ProjOrth Q)} (hBP : B ≤ sec8t84hImg e S) (hB : IsElemAb2 B 4)
    {p : ProjOrth Q} (hp : p ∈ sec8t84hImg e S)
    (hcomm : ∀ b ∈ B, (p * x'') * b = b * (p * x'')) (hne : p * x'' ≠ 1) :
    ∃ B' : Subgroup G, B' ≤ L ⊓ S ∧ IsElemAb2 B' 4 ∧
      ∃ x ∈ S ⊓ Subgroup.centralizer (B' : Set G),
        ∃ hxN : x ∈ Subgroup.normalizer (L : Set G), x ∉ Subgroup.centralizer (L : Set G) ∧
          ffTheta6M hQ hdim hsgn e ⟨x, hxN⟩ = projOrthToProjSim Q (p * x'') := by
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e hodd
  have h2 : IsPGroup 2 (S ⊓ L : Subgroup G) :=
    IsPGroup.to_inf_left (H := S) (K := L) hS.2.1
  have hsub : ffImg (ff6mPhi e) (S ⊓ L) = ffImg (ff6mPhi e) S := by
    rw [ffImg, ffImg, Subgroup.inf_subgroupOf_right]
  have hPle : sec8t84hImg e S ≤ omegaProj hQ :=
    Subgroup.map_subtype_le (H := omegaProj hQ) (ffImg (ff6mPhi e) S)
  have hB'E : IsElemAb2 (B.subgroupOf (omegaProj hQ)) 4 :=
    sec8t84h_isElemAb2_subgroupOf (K := omegaProj hQ) (hBP.trans hPle) hB
  have hB'le : B.subgroupOf (omegaProj hQ) ≤ ffImg (ff6mPhi e) (S ⊓ L) := by
    intro b hb
    have hbB : (b : ProjOrth Q) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hbimg : (b : ProjOrth Q) ∈ sec8t84hImg e S := hBP hbB
    rw [sec8t84hImg, Subgroup.mem_map] at hbimg
    obtain ⟨w, hw, hwv⟩ := hbimg
    have hwb : w = b := Subtype.ext hwv
    rw [hwb] at hw
    rw [← hsub] at hw
    exact hw
  obtain ⟨BG, hBGle, hBGimg⟩ :=
    ff_cover_exists_of_le_img hφ (P := S ⊓ L) inf_le_right h2 hB'le
  have hBGE : IsElemAb2 BG 4 :=
    (ff_cover_elemAb2_iff hφ (hBGle.trans inf_le_right) (h2.to_le hBGle) 4).mpr
      (by rw [hBGimg]; exact hB'E)
  obtain ⟨lp, hlpS, hlpφ⟩ := (mem_sec8t84hImg_iff e).mp hp
  let x : G := (lp : G) * y'
  have hxS : x ∈ S := S.mul_mem hlpS hy'S
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := hS.1 hxS
  have hθx : ffTheta6M hQ hdim hsgn e ⟨x, hxN⟩ =
      projOrthToProjSim Q (p * x'') := by
    have hdec : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨(lp : G), Subgroup.le_normalizer lp.2⟩ :
            ↥(Subgroup.normalizer (L : Set G))) * ⟨y', hS.1 hy'S⟩ :=
      Subtype.ext rfl
    calc ffTheta6M hQ hdim hsgn e ⟨x, hxN⟩
        = ffTheta6M hQ hdim hsgn e
            ((⟨(lp : G), Subgroup.le_normalizer lp.2⟩ :
                ↥(Subgroup.normalizer (L : Set G))) * ⟨y', hS.1 hy'S⟩) := by
              rw [hdec]
      _ = ffTheta6M hQ hdim hsgn e ⟨(lp : G), Subgroup.le_normalizer lp.2⟩ *
            ffTheta6M hQ hdim hsgn e ⟨y', hS.1 hy'S⟩ :=
          map_mul (ffTheta6M hQ hdim hsgn e) _ _
      _ = projOrthToProjSim Q p * projOrthToProjSim Q x'' := by
            rw [ffTheta6M_of_mem, ffOmegaToSim_apply, hlpφ, ← hx]
      _ = projOrthToProjSim Q (p * x'') :=
          (map_mul (projOrthToProjSim Q) p x'').symm
  have hxCent : x ∈ Subgroup.centralizer (BG : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbSL : b ∈ S ⊓ L := hBGle hb
    let lb : ↥L := ⟨b, hbSL.2⟩
    let lb' : ↥L :=
      ⟨x * b * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN b).mp hbSL.2⟩
    have hl : (lb' : G) = ((⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) : G) *
        (lb : G) * ((⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) : G)⁻¹ := by
      show x * b * x⁻¹ = x * b * x⁻¹
      rfl
    have hconj := ffTheta_conj (Q := Q) hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e
      ⟨x, hxN⟩ lb lb' hl
    have hθx' : ffTheta hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨x, hxN⟩ =
        projOrthToProjSim Q (p * x'') := hθx
    rw [hθx', projSimAct_projOrthToProjSim, ← ff6mPhi_apply e lb,
      ← ff6mPhi_apply e lb'] at hconj
    have hwImg : ff6mPhi e lb ∈ ffImg (ff6mPhi e) BG :=
      mem_ffImg_iff.mpr ⟨lb, hb, rfl⟩
    have hwB : ((ff6mPhi e lb : ↥(omegaProj hQ)) : ProjOrth Q) ∈ B := by
      rw [hBGimg, Subgroup.mem_subgroupOf] at hwImg
      exact hwImg
    have hcommb := hcomm ((ff6mPhi e lb : ↥(omegaProj hQ)) : ProjOrth Q) hwB
    have hφeq : ((ff6mPhi e lb' : ↥(omegaProj hQ)) : ProjOrth Q) =
        ((ff6mPhi e lb : ↥(omegaProj hQ)) : ProjOrth Q) := by
      calc ((ff6mPhi e lb' : ↥(omegaProj hQ)) : ProjOrth Q)
          = (p * x'') * ((ff6mPhi e lb : ↥(omegaProj hQ)) : ProjOrth Q) *
              (p * x'')⁻¹ := hconj.symm
        _ = ((ff6mPhi e lb : ↥(omegaProj hQ)) : ProjOrth Q) := by
              rw [hcommb, mul_assoc, mul_inv_cancel, mul_one]
    have hφeq' : ff6mPhi e lb' = ff6mPhi e lb := Subtype.ext hφeq
    have hmem1 : (lb' : G) ∈ S := by
      show x * b * x⁻¹ ∈ S
      exact S.mul_mem (S.mul_mem hxS hbSL.1) (S.inv_mem hxS)
    have hmem2 : (lb : G) ∈ S := hbSL.1
    have hlb'eq : lb' = lb :=
      ff_cover_eq_of_pGroup (B := S) hφ hS.2.1 hmem1 hmem2 hφeq'
    have hxb : x * b * x⁻¹ = b := congrArg (fun l : ↥L => (l : G)) hlb'eq
    calc b * x = (x * b * x⁻¹) * x := by rw [hxb]
      _ = x * b := by group
  have hxNotCent : x ∉ Subgroup.centralizer (L : Set G) := by
    intro hxc
    have h1 : ffTheta6M hQ hdim hsgn e ⟨x, hxN⟩ = 1 :=
      (ffTheta_eq_iff (Q := Q) hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨x, hxN⟩ 1).mpr
        (inducesViaP_one_of_centralizer (hQ := hQ) (e := e) (L := L) hxc)
    have h3 : projOrthToProjSim Q (p * x'') = 1 := by rw [← hθx]; exact h1
    have h4 : p * x'' = 1 :=
      projOrthToProjSim_injective (Q := Q) (by rw [h3, map_one])
    exact hne h4
  refine ⟨BG, ?_, hBGE, x, ?_, hxN, hxNotCent, hθx⟩
  · rw [inf_comm]
    exact hBGle
  · exact Subgroup.mem_inf.mpr ⟨hxS, hxCent⟩

end CFSG.OddStandard.SmallF3.Omega
