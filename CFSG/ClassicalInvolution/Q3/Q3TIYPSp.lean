module

public import CFSG.ClassicalInvolution.RouteD.TWSSp4V
public import CFSG.ClassicalInvolution.Q3.Q3TIYComp
public import CFSG.ClassicalInvolution.Q3.Q3TIYDefs
public import CFSG.ClassicalInvolution.Q3.Q3TIYRank1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TIV
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn)

@[expose] def TwinRowSp2 (t : StatedLieTag) (n : ℕ) : Prop := t = .PSp ∧ n = 2

theorem TwinRowSp2.twinRow {t : StatedLieTag} {n : ℕ} (h : TwinRowSp2 t n) : TwinRow t n := by
  obtain ⟨rfl, rfl⟩ := h
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))


theorem twinMFNotCentralizing3_psp2
    {R R' : Subgroup (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    {x x' : (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .PSp (modelUniv .PSp 2 3 1 Nat.prime_three) R R' x x')
    {a a' : (modelUniv .PSp 2 3 1 Nat.prime_three).K} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 3 1 Nat.prime_three).K)
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 3 1 Nat.prime_three).K)
    {S : Subgroup (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    (hS : S ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D)
    (hc : ∀ s ∈ S, (a * a') * s = s * (a * a')) : False := by
  have hadm : StatedLieAdmissible .PSp 2 3 1 := Q3Z.statedLieAdmissible_psp2
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hR := (exists_isLongRootSp2_iff h2 R).mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hd.mem)
  have hR' := (exists_isLongRootSp2_iff h2 R').mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hd.mem')
  have hS' := (exists_isLongRootSp2_iff h2 S).mpr
    ((mem_fundamentalSubgroups_PSp_iff hadm S).mp hS)
  exact CFSG.ClassicalInvolution.RouteD.SCRSp4.sp4_not_centralizes h2 hR hR' hd.ne hd.hx hd.cx
    hd.nx hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq' hS' hc

theorem card_fund_centralizing3_psp2
    {R R' : Subgroup (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    {x x' ã ã' : (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .PSp (modelUniv .PSp 2 3 1 Nat.prime_three) R R' x x') (hãR : ã ∈ R)
    (hã'R : ã' ∈ R')
    (hsq : ã * ã * x⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 3 1 Nat.prime_three).K)
    (hsq' : ã' * ã' * x'⁻¹ ∈ Subgroup.center (modelUniv .PSp 2 3 1 Nat.prime_three).K) :
    Nat.card {S : Subgroup (modelUniv .PSp 2 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D ∧
        S ≤ Subgroup.centralizer ({ã * ã'} :
          Set (modelUniv .PSp 2 3 1 Nat.prime_three).K)} = 0 := by
  have : IsEmpty {S : Subgroup (modelUniv .PSp 2 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D ∧
        S ≤ Subgroup.centralizer ({ã * ã'} :
          Set (modelUniv .PSp 2 3 1 Nat.prime_three).K)} :=
    ⟨fun ⟨S, hS, hle⟩ => twinMFNotCentralizing3_psp2 hd hãR hã'R hsq hsq' hS fun s hs =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hs)).symm⟩
  exact Nat.card_of_isEmpty

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem rank_setup3_pair (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z) :
    ∃ (J : Subgroup G) (t : G) (A : AtT3 K T J z t tY nY)
      (ã ã' : (modelUniv tY nY 3 1 Nat.prime_three).K),
      J ∈ centralizingMembers (conjClass3 K) {z} ∧ J ≠ K ∧ J ≠ T ∧
      J ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      ã ∈ A.RK ∧ ã' ∈ A.RT ∧
      ã * ã * A.x⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      ã' * ã' * A.x'⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      Set.ncard {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧
        Commutes N J} =
        1 + Nat.card {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
          R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
            R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} := by
  classical
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hKiso hTiso
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts3 A e
  have hJu : J ∈ centralizingMembers (conjClass3 K) {e.u} :=
    c.mem_centralizingMembers_u e hKiso hTiso hJ hJK hJT
  have hJ₂u : A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  exact ⟨J, t, A, ã, ã', hJ, hJK, hJT, hJu, hJ₂u, hãR, hã'R, hsq, hsq',
    ncard_commuting_J3 hR hT A e huY hψu⟩


theorem rank_setup3_sp2 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .PSp 2) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z) :
    ∃ (J : Subgroup G) (t : G) (A : AtT3 K T J z t .PSp 2),
      J ∈ centralizingMembers (conjClass3 K) {z} ∧ J ≠ K ∧ J ≠ T ∧
      J ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      Set.ncard {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧
        Commutes N J} = 1 := by
  obtain ⟨J, t, A, ã, ã', hJ, hJK, hJT, hJu, hJ₂u, hãR, hã'R, hsq, hsq', hcount⟩ :=
    rank_setup3_pair h3 hnab hR (TwinRowSp2.twinRow ⟨rfl, rfl⟩) hshape hT clsT e
  refine ⟨J, t, A, hJ, hJK, hJT, hJu, hJ₂u, ?_⟩
  rw [hcount, card_fund_centralizing3_psp2 A.hdat hãR hã'R hsq hsq']

end Setup

section NoCentral

theorem twinYNoCentral3_sp2 : TwinYNoCentral3On TwinRowSp2 := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e M hM
  obtain ⟨rfl, rfl⟩ := hP
  by_contra hno
  push Not at hno
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hncs := not_commutes_self_of_mem3 hR
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member (fun N hN hNK => hT.comm_K N hN hNK)
    (fun N hN hNT => hT.comm_T N hN hNT)
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  have hMJ : Commutes M J := hno J hJ hJK hJT
  have hMJ₂ : Commutes M A.J₂ := hno A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hMt : M ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hM.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hMJ y hy t hJt.mem)⟩
  have hMJne : M ≠ J := fun h => hncs J hJ.1 (by rw [h] at hMJ; exact hMJ)
  have hMJ₂ne : M ≠ A.J₂ := fun h => hncs A.J₂ A.hJ₂t.1 (by rw [h] at hMJ₂; exact hMJ₂)
  obtain ⟨RM, hRM, hMR⟩ := A.c.big_of_ne A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso hMt hMJne
    hMJ₂ne
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts3 A e
  have h1 : locImg (conjClass3 K) t M ≤
      Subgroup.centralizer ({Gaps.locMk (conjClass3 K) t ⟨e.u, huY⟩} :
        Set (locQuot (conjClass3 K) t)) :=
    (le_centralizer_iff_locImg3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hMt ⟨e.u, huY⟩).mp hM.2
  have hcent : RM ≤ Subgroup.centralizer ({ã * ã'} :
      Set (modelUniv .PSp 2 3 1 Nat.prime_three).K) :=
    (le_centralizer_iff_map3 A.c.d.ψ A.c.d.ker_le A.c.ker_cop (A.c.rf.y.pow3 RM hRM)
      (ã * ã')).mpr (by
      rw [hψu, ← hMR]
      exact h1)
  exact twinMFNotCentralizing3_psp2 A.hdat hãR hã'R hsq hsq' hRM fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcent hs)).symm

end NoCentral

end CFSG.ClassicalInvolution.Q3.Q3TIY
