module

public import CFSG.ClassicalInvolution.Q3.Q3TWBHt
public import CFSG.ClassicalInvolution.Q3.Q3TWBHz
public import CFSG.ClassicalInvolution.Q3.Q3AMBadFin
public import CFSG.ClassicalInvolution.Q3.Q3AMBadStand
public import CFSG.ClassicalInvolution.Q3.Q3DBMain
public import CFSG.ClassicalInvolution.Q3.Q3ExD

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Reduction

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem kPerp_ne_twinSet {K : Subgroup G} {z : G} (hnab : ∃ x y : G, x * y ≠ y * x)
    (hz : IsClassicalMember3 K z) (hD : DConnected (CoreAssembly.conjClass K)) :
    KPerp (CoreAssembly.conjClass K) K ≠ twinSet (CoreAssembly.conjClass K) K := by
  intro heq
  have hΩc : ConjInvariant (CoreAssembly.conjClass K) := conjInvariant_conjClass K
  have hzU : IsUniqueInvolution K z :=
    (IsClassicalMemberU.ofQ3 hz).isUniqueInvolution (MemberType.cert_sl2 3 1)
  obtain ⟨M, N, a, t, hM, hN, ha, ht, hat⟩ := Q3NH.exists_dEdge_distinct hnab hz hD
  obtain ⟨g, hg⟩ := hM
  have haU : IsUniqueInvolution M a :=
    (IsClassicalMemberU.ofQ3 ha).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have htU : IsUniqueInvolution N t :=
    (IsClassicalMemberU.ofQ3 ht).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hN' : conjSub g⁻¹ N ∈ omegaNbr (CoreAssembly.conjClass K) K := by
    have := omegaNbr_conj hΩc hN g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have hmem : conjSub g⁻¹ N ∈ twinSet (CoreAssembly.conjClass K) K :=
    heq ▸ Set.mem_insert_of_mem _ hN'
  obtain ⟨-, z₀, hz₀K, hz₀N⟩ := hmem
  have h1 : z₀ = z := (hz₀K.eq hzU).symm ▸ rfl
  have h2 : z₀ = g⁻¹ * t * g⁻¹⁻¹ := hz₀N.eq (htU.conj g⁻¹)
  have h3 : IsUniqueInvolution K (g⁻¹ * a * g⁻¹⁻¹) := by
    have := haU.conj g⁻¹
    rwa [← hg, conjSub_inv_conjSub] at this
  have h4 : g⁻¹ * a * g⁻¹⁻¹ = z := h3.eq hzU
  apply hat
  have h5 : g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * t * g⁻¹⁻¹ := h4.trans (h1.symm.trans h2)
  simpa using h5

theorem isClassicalMember3_of_mem_conjClass {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    {M : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) {a : G} (ha : IsUniqueInvolution M a) :
    IsClassicalMember3 M a := by
  obtain ⟨g, rfl⟩ := hM
  have h1 := hz.conj g
  have h2 : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) :=
    (IsClassicalMemberU.ofQ3 h1).isUniqueInvolution (MemberType.cert_sl2 3 1)
  rw [ha.eq h2]
  exact h1

theorem twinBridge3_of_inputs (hF : TwoElementsNormalizeU (.sl2 3 1))
    (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n)
    (hHu : Q3T8.Asc77.TwinFrameHyp51uC) : Q3AM.TwinBridge3 := by
  intro G _ _ _ hnab K z hz hBelowT hr hlarge hD _ _ htw
  have hz3 : IsClassicalMember3 (satU (.sl2 3 1) K z) z := (hz.satU_member).toQ3 (by norm_num)
  have hzU : IsUniqueInvolution (satU (.sl2 3 1) K z) z :=
    (IsClassicalMemberU.ofQ3 hz3).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hint : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ satU (.sl2 3 1) K z :=
    oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num))
  have hintU : IsIntrinsicU (.sl2 3 1) (satU (.sl2 3 1) K z) z := isIntrinsicU_satU (.sl2 3 1) K z
  have hBelow3 : CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelowT
  have hmod := Q3AM.bridge_hypOmegaModU hF hnab hz
  have hKt := hz.satU_member
  have htrans : ∀ J ∈ CoreAssembly.conjClass (satU (.sl2 3 1) K z),
      ∃ g : G, conjSub g (satU (.sl2 3 1) K z) = J := fun J hJ => by
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨g, rfl⟩
  have hs : Q3T8.Asc77.AscStandNA (CoreAssembly.conjClass (satU (.sl2 3 1) K z))
      (satU (.sl2 3 1) K z) :=
    { modU := hmod
      hyp := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hmod
      cls := Q3CL.classicalClause_of_modU hmod
      rank := hr
      notFour := hlarge
      below := hBelowT
      ih := hih _ hBelowT
      mem := CoreAssembly.mem_conjClass_self _
      trans := htrans
      gen := gen_conjClass _ hKt.mem hKt.ne_one }
  have hfuzzy : Q3T8.Asc77.FuzzyEdges3 (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) := by
    intro M hM N hN a ha
    exact Q3DB.actsTrivOnQuot_of_mem_omegaNbr hz3 hintU hN
      (isClassicalMember3_of_mem_conjClass hz3 hM ha)
  obtain ⟨K', hK'tw, hK'ne⟩ := htw
  have hstd : Q3T8.Asc77.Std7C (CoreAssembly.conjClass (satU (.sl2 3 1) K z))
      (satU (.sl2 3 1) K z) K' z := ⟨hs, hzU, hK'tw, hK'ne, hfuzzy⟩
  have hperp := kPerp_ne_twinSet hnab hz3 hD
  obtain ⟨u, J, t, W, h⟩ := Q3T8.Asc77.c21_setupC G _ _ K' z hstd hperp
  have hC3 : Q3T8.Asc77.C21_3C := Q3T8.Asc77.c21_3_ofC
    (Q3T8.Asc77.twinFrameHyp51_of_casesC Q3T8.Asc77.twinFrameHyp51zC_proved
      Q3T8.Asc77.twinFrameHyp51tC_proved hHu)
  have hA : Q3T8.Asc77.AlphaStepsC := ⟨hC3, Q3T8.Asc77.twinNormAlpha_ofC hC3⟩
  have hKΩ : satU (.sl2 3 1) K z ∈ CoreAssembly.conjClass (satU (.sl2 3 1) K z) :=
    CoreAssembly.mem_conjClass_self _
  have hnorm : (alphaOf (Subgroup.closure ({u, z} : Set G))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hmem : conjSub g (satU (.sl2 3 1) K z) ∈
        dComp (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (satU (.sl2 3 1) K z) :=
      hD _ hKΩ _ ⟨g, rfl⟩
    have h1 := hA.conj_alpha_of_mem_dComp h _ hmem g rfl
    have h2 : g * n * g⁻¹ ∈ conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) :=
      conj_mem_conjSub hn
    rwa [h1] at h2
  have hodd : Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set G)))) :=
    (hC3 G _ _ K' z u J t W h).1
  have hbot : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ := by
    rcases hnorm.eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exfalso
      rw [h0, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card G := hz3.orderOf_eq_two ▸ orderOf_dvd_natCard z
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hαcore : Balance.Bootstrap.alphaCore (Subgroup.closure ({z, t} : Set G)) = ⊥ :=
    Q3AM.alphaCore_eq_bot_of_alphaOf_eq_bot ((hA.alpha_zt h).trans hbot)
  have hN : J ∈ omegaNbr (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (satU (.sl2 3 1) K z) :=
    h.hJ.2 _ (mem_twinSet_self hKΩ hzU)
  have htJ : IsClassicalMember3 J t := isClassicalMember3_of_mem_conjClass hz3 h.hJ.1 h.ht
  exact Q3DB.oddCentralizerFree_of_exact_sat hz
    (Q3NH.exactMembers3_of_alphaDEdge hnab hz3 hint hBelow3 hN hz3 htJ hαcore)

end Reduction

end CFSG.ClassicalInvolution.Q3.Q3TWB
