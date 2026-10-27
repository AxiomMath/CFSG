module

public import CFSG.Quasithin.H13.NQBlockRadicalR2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQBlockRadicalR2Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem radical_le_centralizer_of_faithful_F4
    (ha : NoOddLinearThreeLStarF_F4)
    (hb : Lemma3_2_13Consumed) (hc : Lemma3_2_14HomocyclicConsumed)
    (hList : QuasithinUnique.Vol2Native.A312ListFactsCat)
    {T L : Subgroup G} (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hQ : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hL : quasithinIsLocal T L) (hLf : quasithinIsFaithfulLocal T L)
    (hLq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    (CFSG.solvableRadical ↥L).map L.subtype ≤
      centralizer (reducedAggregate (L ⊔ T) : Set G) := by
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : QuasithinUnique.LocalSQTK G := (QuasithinUnique.qtkeCore_of_cat hnab hQ).1
  have hTL := le_normalizer_of_not_isQuasisimple hs hnab hQ hL hLq
  obtain ⟨K, hKm, hLK⟩ := exists_maximalLocal_ge hL
  have hKf := local_faithfulness_upward LocDbl.local_double_embedding_exclusion hs hnab hQ hT
    hKm.1 hLK hLf
  have hO2 : pCoreOf 2 (K ⊔ T) ≠ ⊥ := hKm.1.2.2.2
  have hS : QuasithinUnique.IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKm.1.1, hKm.1.2.2.1⟩
  have hKc : K ∈ cComp (K ⊔ T) := cComp_of_isLocal hKm.1
  have hLH : L ≤ K ⊔ T := hLK.trans le_sup_left
  have hQs := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have hA := QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved _ hQs _
    (modO2Image_mem_cComp hKc)
  obtain ⟨eK, -⟩ := exists_modO2_equiv hKc
  obtain ⟨ψ, hψs, -, hψ⟩ := exists_modO2Image_surjection hLH
  have hLKb : modO2Image (K ⊔ T) L ≤ modO2Image (K ⊔ T) K :=
    Subgroup.map_mono fun x hx => hLK hx
  have h312 : QuasithinUnique.Vol2Native.A312ForSQTKCat :=
    QuasithinUnique.Vol2Native.a312ForSQTKCat_of_facts hList CFSG.Quasithin.a312SL2Fact
      QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved
      QuasithinUnique.Vol2Native.a39ForSQTKCat_proved
  have hLbq : ¬ CFSG.IsQuasisimple
      (↥(modO2Image (K ⊔ T) L) ⧸ CFSG.pCore 2 ↥(modO2Image (K ⊔ T) L)) := fun h =>
    hLq (isQuasisimple_of_modO2Image hLH h)

  have hkey : ¬ CFSG.IsQuasisimple ↥(modO2Image (K ⊔ T) K) ∧
      ∀ z, z ∈ (CFSG.solvableRadical ↥(modO2Image (K ⊔ T) L)).map
        (modO2Image (K ⊔ T) L).subtype → Odd (orderOf z) → z ∈ A7.oddBar K T := by
    rcases QuasithinUnique.Vol2Native.lemma_1_2_4_list hloc h312 hO2 hS hLH
      (mem_lFamily_of_isLocal hL) hKc hLK with heq | hcase | hnq
    · rw [heq] at hLbq ⊢
      have hnq : ¬ CFSG.IsQuasisimple ↥(modO2Image (K ⊔ T) K) := fun h =>
        hLbq (isQuasisimple_quotient_pCore h)
      refine ⟨hnq, ?_⟩
      rintro _ ⟨y, hy, rfl⟩ hodd
      have hodd' : Odd (orderOf y) := by
        rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hodd
      exact ⟨y, mem_oddCore_of_mem_solvableRadical hA hnq hy hodd', rfl⟩
    · exfalso
      have hLp : Group.IsPerfect ↥L :=
        Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp (cComp_of_isLocal hL))
      have : Group.IsPerfect ↥(modO2Image (K ⊔ T) L) := by
        rw [Group.isPerfect_def, eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := hψs y
        have hx : x ∈ commutator ↥L := hLp.commutator_eq_top ▸ mem_top x
        have h1 := mem_map_of_mem ψ hx
        rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr hψs, ← _root_.commutator_def] at h1
      rcases a312Case_quasisimple_or_linear hcase with hq | ⟨p, hp, hp3, hlin⟩
      · exact hLbq hq
      · obtain ⟨hPSL, hSL3⟩ := ha G T K hs hnab hQ hT hKm hKf p hp hp3
        rcases hlin with h | h
        · exact hPSL (IsPSL.of_mulEquiv eK.symm h)
        · exact hSL3 (IsSL3.of_mulEquiv eK.symm h)
    · have hnq' := A312.not_quasisimple_of_nonquasi hnq
      refine ⟨hnq', ?_⟩
      rintro _ ⟨y, hy, rfl⟩ hodd
      have hodd' : Odd (orderOf y) := by
        rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at hodd
      exact mem_oddCore_of_nonquasi hLKb (hA.toStrong hnq') hnq' hnq hy hodd'
  obtain ⟨hKbq, hkey⟩ := hkey

  have hKq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := fun h =>
    hKbq (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK h)
  have hTK := le_normalizer_of_not_isQuasisimple hs hnab hQ hKm.1 hKq
  have hRK := radical_le_centralizer_of_maximalLocal hb hc hs hnab hQ hT hKm hKf hTK hKq
  have hP := oddPre_le_centralizer_of_radical hQ hT hKm.1 hTK hRK
  obtain ⟨S, hS'⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH hQ.2.1 S ⟨hS' ▸ le_sup_right, hO2⟩
  have hΩ := omegaOneCenter_pCoreOf_mono hLK hchar
    (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS)

  have hodd : ∀ x ∈ (CFSG.solvableRadical ↥L).map L.subtype, Odd (orderOf x) →
      x ∈ centralizer (reducedAggregate (L ⊔ T) : Set G) := by
    rintro _ ⟨r, hr, rfl⟩ ho
    have ho' : Odd (orderOf r) := by rwa [Subgroup.coe_subtype, Subgroup.orderOf_coe] at ho
    have hz := hkey (ψ r : ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T))
      ⟨ψ r, CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le hψs
        (mem_map_of_mem ψ hr), rfl⟩
      (by
        rw [Subgroup.orderOf_coe]
        exact ho'.of_dvd_nat (orderOf_map_dvd ψ r))
    rw [hψ r] at hz
    have hmem : (r : G) ∈ A7.oddPre K T := A7.mem_oddPre.2 ⟨hLK r.2, hz⟩
    have hc := hP hmem
    rw [mem_centralizer_iff] at hc ⊢
    intro v hv
    exact hc v (hΩ (reducedAggregate_le_omegaOneCenterOf (L ⊔ T) hv))
  have hO : oTwoUpper ((CFSG.solvableRadical ↥L).map L.subtype) ≤
      centralizer (reducedAggregate (L ⊔ T) : Set G) :=
    (closure_le _).mpr fun x hx => hodd x hx.1 hx.2
  exact le_centralizer_of_oTwoUpper_le (isTwoReducedIn_reducedAggregate (L ⊔ T))
    ((map_subtype_le _).trans le_sup_left)
    ((sup_le le_normalizer hTL).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) hO

theorem stmt3_2_14_of_F4
    (ha : NoOddLinearThreeLStarF_F4) (hb : Lemma3_2_13Consumed)
    (hc : Lemma3_2_14HomocyclicConsumed) (hList : QuasithinUnique.Vol2Native.A312ListFactsCat) :
    Stmt3_2_14_F4 := by
  intro G _ _ T L hs hnab hQ hT hL hLq
  by_cases hLf : quasithinIsFaithfulLocal T L
  · exact radical_le_centralizer_of_faithful_F4 ha hb hc hList hs hnab hQ hT hL hLf hLq
  · exact (map_subtype_le _).trans (le_centralizer_of_not_faithful hQ hT hL hLf)

end CFSG.Quasithin.H13.NQBlock
