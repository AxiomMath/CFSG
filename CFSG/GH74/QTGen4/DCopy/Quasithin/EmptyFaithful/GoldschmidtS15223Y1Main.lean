module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Main
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223Stmt22
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223

theorem input15222ThreeCanon_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h11 : StageLemma15211_F4) (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4)
    (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) :
    Input15222ThreeCanon_F4 := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hii hCh h3p hnirr Y₁ hcanon hY₁eq hY₁N hSY hq
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := T_le_M152 hs
  have hC : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M ⊓ I :=
    le_inf inf_le_left ((cv_le_inf152 hs hD).trans inf_le_right)
  have hOmS : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hE9 : Nat.card (oTwoUpper (autOn M (V154 T Mc M))) = 9 :=
    (om4_card152 hOmS hii.2.2.1).2
  have hEc := (oTwoUpper_Mb_odd_comm hD hOmS).2
  have hnTS : ¬ T ≤ sOf152 T Mc M B₀ := fun h => by
    have h1 := Subgroup.relIndex_eq_one.mpr h
    rw [hD.h17.2.2] at h1
    omega
  obtain ⟨t, htT, htS⟩ := IsConcreteLE.not_le_iff_exists.mp hnTS
  obtain ⟨Z₁, hZ₁sup, hZ₁inf, hNI, -⟩ := hii.2.2.2
  obtain ⟨hZs4, hZse⟩ := card_zS152 hB₀ hD
  have hZc : ∀ a ∈ zSOf T Mc M B₀, ∀ b ∈ zSOf T Mc M B₀, a * b = b * a := by
    intro a ha b hb
    have := hZse.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : zSOf T Mc M B₀) ⟨b, hb⟩)
  have htZs : t ∈ Subgroup.normalizer (zSOf T Mc M B₀ : Set G) := by
    rw [← commutator_eq_zSOf hD.h13 hB₀ hB]
    exact (hD.h11 B hB).normal htT
  have htZ : t ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (quasithinOmegaOneCenter_le_center T hz).2 t htT).symm
  have htn : t ∉ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := fun hc => htS ⟨htT, hc⟩
  obtain ⟨hZle, hZtle⟩ := le_sup_conjSub_of_klein hZs4 hZc hD.h17.2.1 hZ₁sup hZ₁inf htZs htZ htn
  have hS2 : IsPGroup 2 (sOf152 T Mc M B₀) := hs.qtfe.sylow.1.to_le S_le_T152
  have hY₁ne : oPrimeResidualOf 3 (M ⊓ I) ≠ ⊥ := by
    rw [← hcanon]
    exact ne_bot_of_quot_perm hS2 hq
  have hD0 := autOn_oPrimeResidual_ne_bot hMV inf_le_left h3p hY₁ne
  have hnle := autOn_not_le_conjSub hs hD hNI hZle hZtle hD0 hE9
  have hres := abstract_step hMV inf_le_left hC hEc hE9 (hTM htT) hD0 hnle
  refine ⟨t, htT, htS, ?_, ?_⟩
  · rw [hcanon]
    exact hres.1
  · rw [hcanon, hres.2, hii.2.1.1.2.1]

end S15223

end CFSG.Quasithin
