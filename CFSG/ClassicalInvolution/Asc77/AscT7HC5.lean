module

public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
import CFSG.ClassicalInvolution.Asc77.AscT7EInv

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

namespace T7H

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem layer_frame (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ (R R' : Subgroup G) (b b' : G), IsSylow2In R K ∧ IsSylow2In R' K' ∧ R ∈ DSet Ω W ∧
      R' ∈ DSet Ω W ∧ Commutes R R' ∧ b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧ orderOf b' = 4 ∧
      (u = b * b' ∨ u = z * (b * b')) := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := T7D.exists_sylow_frame hs hd.hW hd.hzW
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hd.hW hWS (mem_RSet_of_isSylow2In hK hR) hRS
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hd.hW hWS (mem_RSet_of_isSylow2In hK' hR') hR'S
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hs.hne.symm hz hz' hR.1 hR'.1
    (S.isPGroup'.to_le (sup_le hRS hR'S))
  obtain ⟨b, hbRW, hb4⟩ := Thompson.exists_orderOf_four hp hq hΩ hd.hW hRD
  obtain ⟨b', hb'RW, hb'4⟩ := Thompson.exists_orderOf_four hp hq hΩ hd.hW hR'D
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hd.hW
  have hu := T7E.involution_cases hs hR hR' hRS hR'S hbRW.1 hb'RW.1 hb4 hb'4 hd.hu
    (hWS hd.huW) hd.hu2 hd.hu1 hd.huz (hWab u hd.huW b hbRW.2) (hWab u hd.huW b' hb'RW.2)
  exact ⟨R, R', b, b', hR, hR', hRD, hR'D, hc, hbRW.1, hb'RW.1, hb4, hb'4, hu⟩


end T7H

variable {p f : ℕ} [Fact p.Prime]

open T7H in
theorem c23_4X_of_tsf (hTSF : TwinSquareFact p) : C23_4X p f := by
  intro G _ _ _ Ω K K' W z u e g h
  have hs : Hyp23Setting p f Ω K K' z := h.std.setting
  have hd : Hyp23bData Ω K K' W z u e g := h.data
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hBelow : CITBelowU p f (Nat.card G) := hst.below f hq
  have hcpg : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_sq_eq_one hd.he2
  obtain ⟨R, R', b, b', hR, hR', hRD, hR'D, hRR', hbR, hb'R', hb4, hb'4, hu⟩ := layer_frame hs hd
  have heW : e ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) := by
    rw [← hd.he]
    exact Subgroup.mem_closure_singleton_self e
  have hec : ∀ x ∈ Subgroup.normalizer (W : Set G), e * x = x * e := by
    intro x hx
    obtain ⟨y, hy, hye⟩ := heW.2
    have := Subgroup.mem_center_iff.mp hy ⟨x, hx⟩
    have h2 : (x : G) * (y : G) = (y : G) * (x : G) := congrArg Subtype.val this
    rw [← hye]
    exact h2.symm
  have hRc : R ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec r (hRD.2 hr)).symm
  have hR'c : R' ≤ Subgroup.centralizer ({e} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hec r (hR'D.2 hr)).symm
  have hKt : K ∈ tqMembers Ω e :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcpg).mpr ⟨hK, R, hR, hRc⟩
  have hK't : K' ∈ tqMembers Ω e :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcpg).mpr ⟨hK', R', hR', hR'c⟩
  have hRe : IsSylow2In R (exactCore e K) :=
    ((isSylow2In_exactCore_iff hΩ hcpg hK hKt.2).mpr ⟨hR, hRc⟩)
  have hR'e : IsSylow2In R' (exactCore e K') :=
    ((isSylow2In_exactCore_iff hΩ hcpg hK' hK't.2).mpr ⟨hR', hR'c⟩)
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := by
    have : (⨆ R ∈ DSet Ω W, R) ≤ Subgroup.normalizer (W : Set G) := iSup₂_le fun R hR => hR.2
    exact this hd.hg
  have hgc : g ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hec g hgN).symm
  have hLt : conjSub g K ∈ tqMembers Ω e := conjSub_mem_tqMembers hΩ.conjInvariant hgc hKt
  have htL : IsUniqueInvolution (conjSub g K) (u * e) := by
    rw [← hd.hgt]
    exact hz.conj g
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hd.hW
  have hzt : z * (u * e) = (u * e) * z :=
    hWab z hd.hzW (u * e) (W.mul_mem hd.huW heW.1)
  have hbK : b ∈ K := hR.1 hbR
  have hb'K' : b' ∈ K' := hR'.1 hb'R'
  have hbb : b * b = z := T7A.sq_eq_of_orderOf_four hz hbK hb4
  have hb'b' : b' * b' = z := T7A.sq_eq_of_orderOf_four hz' hb'K' hb'4
  have hzc : ∀ x ∈ K, z * x = x * z := fun x hx => hz.commute_of_mem hx
  have hzKe : z ∈ exactCore e K := (isUniqueInvolution_exactCore hp hΩ hcpg hKt hz).mem
  obtain ⟨b₁, hb₁, ob₁, hub₁, hbc⟩ : ∃ b₁ ∈ exactCore e K, b₁ * b₁ = z ∧ u = b₁ * b' ∧
      ∀ r ∈ R, r * b₁ = b₁ * r → r * b = b * r := by
    rcases hu with hu | hu
    · exact ⟨b, hRe.1 hbR, hbb, hu, fun r _ h => h⟩
    · refine ⟨z * b, (exactCore e K).mul_mem hzKe (hRe.1 hbR), ?_, by rw [hu]; group, ?_⟩
      · have hzb : z * b = b * z := hzc b hbK
        calc z * b * (z * b) = z * (b * z) * b := by group
          _ = z * (z * b) * b := by rw [← hzb]
          _ = (z * z) * (b * b) := by group
          _ = z := by rw [hz.sq, hbb, one_mul]
      · intro r hr h
        have hzr : z * r = r * z := hzc r (hR.1 hr)
        have h1 : z * (r * b) = z * (b * r) := by
          calc z * (r * b) = r * z * b := by rw [← mul_assoc, ← hzr, mul_assoc]
            _ = r * (z * b) := by group
            _ = z * b * r := h
            _ = z * (b * r) := by group
        exact mul_left_cancel h1
  have hQ : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  have htz : u * e ≠ z := by
    intro hte
    have hez : e = u * z := by
      have h1 : u * (u * e) = e := by rw [← mul_assoc, hd.hu2, one_mul]
      rw [← h1, hte]
    have hbc' : ∀ r ∈ R, r * b = b * r := by
      intro r hr
      refine hbc r hr ?_
      have hre : r * e = e * r := (hec r (hRD.2 hr)).symm
      have hzr : r * z = z * r := (hzc r (hR.1 hr)).symm
      have hrb' : r * b' = b' * r := hRR' r hr b' hb'R'
      have huz : u = e * z := by
        rw [hez, mul_assoc, hz.sq, mul_one]
      have hru : r * u = u * r := by
        rw [huz]
        calc r * (e * z) = (r * e) * z := by group
          _ = (e * r) * z := by rw [hre]
          _ = e * (r * z) := by group
          _ = e * (z * r) := by rw [hzr]
          _ = (e * z) * r := by group
      rw [hub₁] at hru
      have h2 : (r * b₁) * b' = (b₁ * r) * b' := by
        calc (r * b₁) * b' = r * (b₁ * b') := by group
          _ = (b₁ * b') * r := hru
          _ = b₁ * (b' * r) := by group
          _ = b₁ * (r * b') := by rw [hrb']
          _ = (b₁ * r) * b' := by group
      exact mul_right_cancel h2
    have := hQ.sq_eq_one_of_central hbR (fun y hy => (hbc' y hy).symm)
    rw [hbb] at this
    exact hz.ne_one this
  have hnc : ¬ ({e} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨x, -, y, -, hxy⟩ := hQ.exists_not_commute
    have hecen : e ∈ Subgroup.center G := hsub (Set.mem_singleton e)
    exact hd.he1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hecen g'))
  have hperp : KPerp Ω K = {K, K'} := hs.perp
  have hperp' : KPerp Ω K' = {K', K} := by
    rw [hs.perp_of_twin hs.hK', Set.pair_comm]
  refine Or.inr (layer_orth_six hTSF hp hq hΩ hBelow hd.he2 hnc hKt hK't hLt hz hz' hperp hperp'
    htL hzt htz hRe hR'e hRR' hb₁ (hR'e.1 hb'R') ob₁ hb'b' ?_)
  rw [← hub₁]

end CFSG.ClassicalInvolution.Asc77
