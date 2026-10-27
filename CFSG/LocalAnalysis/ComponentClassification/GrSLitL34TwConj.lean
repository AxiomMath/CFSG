module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwConjB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRADefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

theorem finiteCore_of_facts (X : Subgroup WrE) (hX : GoodX X)
    (hPw : Pw ≤ wrR) (hcardWr : Nat.card wrR = 2 * Nat.card R ^ 2)
    (hcardPw : Nat.card Pw = 2 * Nat.card RA ^ 2) (hcardRA : Nat.card RA = 256)
    (hPwS : Pw ⊓ ssS = N0w) (hcardN : Nat.card N0w = 2 ^ 12)
    (hcore : ∀ Y : Subgroup WrE, Y ≤ Pw → N0w ≤ Y → GoodX Y → ConcX Y) : ConcX X := by
  have hcardWr' : Nat.card wrR = 2 * 241920 ^ 2 := by rw [hcardWr, PSL3Four.card_R]
  have hcardPw' : Nat.card Pw = 2 ^ 17 := by rw [hcardPw, hcardRA] <;> norm_num
  have hP0card : Nat.card ↥(Pw.subgroupOf wrR) = 2 ^ 17 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPw).toEquiv, hcardPw']
  have hP0p : IsPGroup 2 ↥(Pw.subgroupOf wrR) := IsPGroup.of_card hP0card
  have hP0idx : ¬ 2 ∣ (Pw.subgroupOf wrR).index := by
    have h := (Pw.subgroupOf wrR).card_mul_index
    rw [hP0card, hcardWr'] at h
    norm_num at h
    omega
  obtain ⟨Q0, hQ0⟩ : ∃ Q : Sylow 2 ↥wrR, (Q : Subgroup ↥wrR) = Pw.subgroupOf wrR :=
    ⟨hP0p.toSylow hP0idx, rfl⟩
  have hXp : IsPGroup 2 ↥(X.subgroupOf wrR) :=
    hX.two.of_surjective (Subgroup.subgroupOfEquivOfLe hX.le_wrR).symm.toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨Q1, hQ1⟩ := IsPGroup.exists_le_sylow hXp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥wrR Q0 Q1
  have hconj : ∀ x ∈ X, (g : WrE)⁻¹ * x * (g : WrE) ∈ Pw := by
    intro x hx
    have hxQ : (⟨x, hX.le_wrR hx⟩ : ↥wrR) ∈ (Q1 : Subgroup ↥wrR) :=
      hQ1 (Subgroup.mem_subgroupOf.2 hx)
    rw [← hg, Sylow.coe_subgroup_smul] at hxQ
    obtain ⟨s, hsS, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hxQ
    rw [hQ0] at hsS
    have hs' : g * s * g⁻¹ = ⟨x, hX.le_wrR hx⟩ := hs
    have hsx : (g : WrE) * (s : WrE) * (g : WrE)⁻¹ = x := congrArg Subtype.val hs'
    have hsx' : (g : WrE)⁻¹ * x * (g : WrE) = (s : WrE) := by
      rw [← hsx]
      group
    rw [hsx']
    exact Subgroup.mem_subgroupOf.1 hsS
  have hcw : (g : WrE)⁻¹ ∈ wrR := wrR.inv_mem g.2
  have hXP : ConjCS.cs (g : WrE)⁻¹ X ≤ Pw := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := ConjCS.mem_cs_iff.1 hy
    rw [inv_inv]
    exact hconj x hx
  have hX' : GoodX (ConjCS.cs (g : WrE)⁻¹ X) := ConjCS.goodX_cs hX hcw
  have hEq : ConjCS.cs (g : WrE)⁻¹ X ⊓ ssS = N0w :=
    Subgroup.eq_of_le_of_card_ge ((inf_le_inf_right ssS hXP).trans hPwS.le)
      (hcardN.trans hX'.card_ss.symm).le
  have hN : N0w ≤ ConjCS.cs (g : WrE)⁻¹ X := by
    rw [← hEq]
    exact inf_le_left
  have hC := hcore _ hXP hN hX'
  have hback := ConjCS.concX_cs hC (wrR.inv_mem hcw)
  rwa [ConjCS.cs_inv_cs] at hback

end CFSG.ComponentClassification.GrSLit.L34Tw
