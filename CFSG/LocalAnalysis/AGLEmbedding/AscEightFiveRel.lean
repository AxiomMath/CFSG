module

public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive

public section

namespace CFSG.AGLEmbedding

namespace AscEightFive

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem charTwo_of_le_of_charTwo {H : Subgroup G} (hX : CharTwo X) (hQH : pCoreOf 2 X ≤ H)
    (hHX : H ≤ X) : CharTwo H := by
  have hQn : ((pCoreOf 2 X).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr
      (hHX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X))
  have hQle : pCoreOf 2 X ≤ pCoreOf 2 H :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQH hQn
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
  rintro g ⟨hgH, hgC⟩
  exact hQle (hX ⟨hHX hgH,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQle) hgC⟩)

theorem isSylowTwoOf_barM_inf_of_isPGroup (hS : IsPGroup 2 S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf (barM X S ⊓ barM X L) (barM X L) := by
  have h1 := isSylowTwoOf_map (isSylowTwoOf_subgroupOf hsyl hL.le)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  refine isSylowTwoOf_of_le h1 ?_ inf_le_right
    ((AscEightFour.barM_isPGroup hS).to_le inf_le_left)
  exact le_inf (Subgroup.map_mono fun x hx => hx.1) (Subgroup.map_mono fun x hx => hx.2)

theorem isSylowTwoOf_of_mem_orbitFS_of_isPGroup (hS : IsPGroup 2 S)
    (hL : IsTwoPrimeComponent X L) (hsyl : IsSylowTwoOf (S ⊓ L) L)
    {A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hA : A ∈ orbitFS X S L) :
    IsSylowTwoOf (barM X S ⊓ A) A := by
  obtain ⟨t, ht, rfl⟩ := mem_orbitFS.mp hA
  have h1 := isSylowTwoOf_map (isSylowTwoOf_barM_inf_of_isPGroup hS hL hsyl)
    (MulAut.conj t).toMonoidHom
  refine isSylowTwoOf_of_le h1 ?_ inf_le_right
    ((AscEightFour.barM_isPGroup hS).to_le inf_le_left)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ⟨x, hx.2, rfl⟩⟩
  change t * x * t⁻¹ ∈ barM X S
  exact (barM X S).mul_mem ((barM X S).mul_mem ht hx.1) ((barM X S).inv_mem ht)

theorem isSylowTwoOf_dBar_of_isPGroup (hS : IsPGroup 2 S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    IsSylowTwoOf (barM X S ⊓ dBar X S L) (dBar X S L) :=
  isSylowTwoOf_inf_iSup (AscEightFour.barM_isPGroup hS) (orbitFS X S L)
    (fun _ hA => isSylowTwoOf_of_mem_orbitFS_of_isPGroup hS hL hsyl hA)
    (fun _ hA _ hB hne => commute_of_mem_orbitFS hL hA hB hne)

theorem isSylowTwoOf_hBar_of_isPGroup (hS : IsPGroup 2 S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf (barM X S) (hBar X S L) := by
  have hN := barM_le_normalizer_dBar (X := X) (S := S) (L := L)
  have hD := isSylowTwoOf_dBar_of_isPGroup hS hL hsyl
  refine isSylowTwoOf_of_forall_normalizer_le le_sup_right
    (AscEightFour.barM_isPGroup hS) ?_
  intro U hUH hU2 hSU _ u hu
  have hu' : u ∈ ((barM X S ⊔ dBar X S L : Subgroup _) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    rw [sup_comm]; exact hUH hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hu'
  obtain ⟨s, hs, d, hd, rfl⟩ := hu'
  have hdU : d ∈ U := by
    have := U.mul_mem (U.inv_mem (hSU hs)) hu
    simpa using this
  have heq := isSylowTwoOf_eq_of_le hD (inf_le_right : U ⊓ dBar X S L ≤ dBar X S L)
    (hU2.to_le inf_le_left) (inf_le_inf_right _ hSU)
  have hdS : d ∈ barM X S ⊓ dBar X S L := heq ▸ ⟨hdU, hd⟩
  exact (barM X S).mul_mem hs hdS.1

theorem isSylowTwoOf_hGrp5_of_isPGroup (hS : IsPGroup 2 S) (hSX : S ≤ X)
    (hQS : pCoreOf 2 X ≤ S) (hL : IsTwoPrimeComponent X L) (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    IsSylowTwoOf S (hGrp5 X S L) := by
  have hSH : S ≤ hGrp5 X S L :=
    le_hGrp5_of_barM_le hSX le_sup_right
  refine isSylowTwoOf_of_forall_normalizer_le hSH hS ?_
  intro U hUH hU2 hSU _ u hu
  have hUX : U ≤ X := hUH.trans hGrp5_le
  have hUeq := isSylowTwoOf_eq_of_le (isSylowTwoOf_hBar_of_isPGroup hS hL hsyl)
    (barM_le_of_le_hGrp5 hUH)
    (AscEightFour.barM_isPGroup hU2) (Subgroup.map_mono fun x hx => hSU hx)
  have hxu : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨u, hUX hu⟩ ∈ barM X S :=
    hUeq ▸ ⟨⟨u, hUX hu⟩, hu, rfl⟩
  have h2 : (⟨u, hUX hu⟩ : ↥X) ∈ S.subgroupOf X ⊔ CFSG.pCore 2 ↥X := by
    rw [← comap_barM]; exact hxu
  have h3 : CFSG.pCore 2 ↥X ≤ S.subgroupOf X := by
    intro y hy
    exact hQS ⟨y, hy, rfl⟩
  rw [sup_eq_left.mpr h3] at h2
  exact h2

theorem barM_le_barM_inf_of_le_sup_rel {M : Subgroup G} (hS : IsPGroup 2 S) (hSX : S ≤ X)
    (hL : IsTwoPrimeComponent X L) (hsyl : IsSylowTwoOf (S ⊓ L) L) (hSM : S ≤ M)
    (hle : hGrp5 X S L ≤ nGrp5 X S L ⊔ (hGrp5 X S L ⊓ M)) :
    barM X L ≤ barM X (hGrp5 X S L ⊓ M) := by
  set Lb := barM X L with hLb
  set Cb := cBar X S L with hCb
  set Hb := hBar X S L with hHb
  set Mb := barM X (hGrp5 X S L ⊓ M) with hMb
  have hbar : Hb ≤ Cb ⊔ Mb := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
    have hx : (x : G) ∈ hGrp5 X S L := (mem_hGrp5 (x := x)).mpr hy
    have hx' : x ∈ (nGrp5 X S L ⊔ (hGrp5 X S L ⊓ M)).subgroupOf X := hle hx
    have hmap := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) hx'
    rw [Subgroup.subgroupOf_sup nGrp5_le (inf_le_left.trans hGrp5_le),
      Subgroup.map_sup] at hmap
    exact sup_le_sup barM_nGrp5_le le_rfl hmap
  have hMbH : Mb ≤ Hb := barM_le_of_le_hGrp5 inf_le_left
  have hMN : Mb ≤ Subgroup.normalizer (Cb : Set (↥X ⧸ CFSG.pCore 2 ↥X)) :=
    hMbH.trans hBar_le_normalizer_cBar
  have hdec : ∀ x ∈ Hb, ∃ m ∈ Mb, ∃ c ∈ Cb, m * c = x := by
    intro x hx
    have hx' : x ∈ ((Mb ⊔ Cb : Subgroup _) : Set _) := by
      rw [sup_comm]; exact hbar hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Mb Cb hMN] at hx'
    exact hx'
  set A := Lb ⊓ Mb with hA
  have hAn : (A.subgroupOf Lb).Normal := by
    refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr fun a ℓ ha hℓ => ?_
    obtain ⟨m, hm, c, hc, rfl⟩ := hdec ℓ (barM_le_dBar.trans le_sup_left hℓ)
    have hcomm : a * c = c * a :=
      cBar_commute hc (one_mem _) ⟨a, ha.1, by simp⟩
    have hca : c * a * c⁻¹ = a := by rw [← hcomm]; group
    refine ⟨Lb.mul_mem (Lb.mul_mem hℓ ha.1) (Lb.inv_mem hℓ), ?_⟩
    have heq : m * c * a * (m * c)⁻¹ = m * a * m⁻¹ := by
      calc m * c * a * (m * c)⁻¹ = m * (c * a * c⁻¹) * m⁻¹ := by group
        _ = m * a * m⁻¹ := by rw [hca]
    rw [heq]
    exact Mb.mul_mem (Mb.mul_mem hm ha.2) (Mb.inv_mem hm)
  have hSle : S ≤ hGrp5 X S L ⊓ M :=
    le_inf (le_hGrp5_of_barM_le hSX le_sup_right) hSM
  have hbarS : barM X S ≤ Mb := by
    rw [hMb]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X hSle)
  have hodd : ¬ 2 ∣ (A.subgroupOf Lb).index := by
    intro hd
    refine (isSylowTwoOf_barM_inf_of_isPGroup hS hL hsyl).2.2
      (hd.trans (Subgroup.index_dvd_of_le ?_))
    intro x hx
    exact ⟨hx.2, hbarS hx.1⟩
  have hLSC : Lb ≤ Mb := by
    have hperf : commutator ↥Lb = ⊤ := hL.component.2.2.1
    have hAtop := eq_top_of_perfect_of_odd_index hperf (A.subgroupOf Lb) hodd
    intro x hx
    exact (show (⟨x, hx⟩ : ↥Lb) ∈ A.subgroupOf Lb from hAtop ▸ Subgroup.mem_top _).2
  exact hLSC

theorem not_hGrp5_le_rel {M : Subgroup G} (hS : IsPGroup 2 S) (hSX : S ≤ X)
    (hL : IsTwoPrimeComponent X L) (hsyl : IsSylowTwoOf (S ⊓ L) L) (hSM : S ≤ M)
    (hQM : pCoreOf 2 X ≤ M) (hLM : ¬ L ≤ M) :
    ¬ hGrp5 X S L ≤ nGrp5 X S L ⊔ (hGrp5 X S L ⊓ M) := by
  intro hle
  have hLSC := barM_le_barM_inf_of_le_sup_rel hS hSX hL hsyl hSM hle
  apply hLM
  have hLX : L.subgroupOf X ≤ (hGrp5 X S L ⊓ M).subgroupOf X ⊔ CFSG.pCore 2 ↥X := by
    intro ℓ hℓ
    rw [← comap_barM]
    exact hLSC ⟨ℓ, hℓ, rfl⟩
  have hLle : L ≤ (hGrp5 X S L ⊓ M) ⊔ pCoreOf 2 X := by
    have h := Subgroup.map_mono (f := X.subtype) hLX
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hGrp5_le),
      Subgroup.map_subgroupOf_eq_of_le hL.le] at h
    simpa [pCoreOf] using h
  exact hLle.trans (sup_le inf_le_right hQM)

theorem inClassX_of_rel (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    {M : Subgroup G} (hK : CFSG.Open.IsKGroup ↥X) (hX : CharTwo X)
    (hL : IsTwoPrimeComponent X L) (hS : IsPGroup 2 S) (hSX : S ≤ X) (hQS : pCoreOf 2 X ≤ S)
    (hS1 : S ≠ ⊥) (hsyl : IsSylowTwoOf (S ⊓ L) L) (hSM : S ≤ M) (hLM : ¬ L ≤ M)
    (hC : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ M) :
    CFSG.RankThree.PartOne.InClassX ↥L := by
  have hHX : hGrp5 X S L ≤ X := hGrp5_le
  have hcg : cgsIn (hGrp5 X S L) S ≤ hGrp5 X S L ⊓ M := by
    refine le_inf (cgsIn_le _ _) ?_
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hCc => ?_
    exact fun x hx => hC C hCS hC0 hCc hx.2
  obtain ⟨Y, hY, hYM⟩ := hLF.relative
    (LocalCGT.kProper_of_isKGroup (AscEightFour.isKGroup_mono hK hHX))
    (LocalCGT.isCharacteristicP_of_charTwo (charTwo_of_le_of_charTwo hX twoCore_le_hGrp5 hHX))
    (LocalCGT.isSylowOf_of_isSylowTwoOf
      (isSylowTwoOf_hGrp5_of_isPGroup hS hSX hQS hL hsyl))
    ((LocalCGT.centralizer_inf_le_cgsIn hS hS1).trans (hcg.trans le_sup_right))
    (fun B hB hBS hBc =>
      (LocalCGT.normalizer_inf_le_cgsIn B hB hBS hBc).trans (hcg.trans le_sup_right))
    (not_hGrp5_le_rel hS hSX hL hsyl hSM (hQS.trans hSM) hLM)
  obtain ⟨hYH, hYs, hYx⟩ := hY
  have hYN : ¬ Y ≤ nGrp5 X S L := fun h => hYM (h.trans le_sup_left)
  obtain ⟨g, -, rfl⟩ := eq_conj_of_short hL hYH hYs
    (LocalCGT.inClassXBlock_of_inClassX hYx).1 hYN
  let e : ↥(L.map (MulAut.conj (g : G)).toMonoidHom) ≃* ↥L :=
    (L.equivMapOfInjective (MulAut.conj (g : G)).toMonoidHom
      (MulAut.conj (g : G)).injective).symm
  exact CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv e hYx

end AscEightFive

end CFSG.AGLEmbedding
