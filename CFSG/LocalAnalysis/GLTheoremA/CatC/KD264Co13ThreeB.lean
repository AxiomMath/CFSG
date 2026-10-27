module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co13

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.LieType.Multipliers.U43

open scoped commutatorElement


theorem threeB_data_center {x : GL24} (hx : MRep (rootRows3B ()) x) :
    x = kG TabCo1ThreeB.ext 90 ∧ kG TabCo1ThreeB.ext 91 ∈ GA ∧
      Nat.card ↥(Subgroup.closure ({x, kG TabCo1ThreeB.ext 91} : Set GL24)) = 9 ∧
      ∃ J : Subgroup GL24, J ≤ GA ∧ J ≤ Subgroup.centralizer ({x} : Set GL24) ∧
        J ≤ Subgroup.centralizer ({kG TabCo1ThreeB.ext 91} : Set GL24) ∧
        (∀ g ∈ Subgroup.centralizer ({x} : Set GL24) ⊓ GA, ∀ l ∈ J, g * l * g⁻¹ ∈ J) ∧
        CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card ↥J := by
  have h := (Certificates.certificate17330 : threeBCheck () = true)
  simp only [threeBCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc, List.all_eq_true] at h
  obtain ⟨hD, hwx, hw1, hxr, hx1, hx3, hz3, hxa, hxb, hza, hzb, hxz, hwab, hwba, hab, hZok, hZsz,
    hrels, hiu1, hiv1, hiu2, hiv2, hcm1, hcm2, hb1, hcnt1, hb2, hcnt2⟩ := h
  haveI : Finite GL24 := inferInstance
  have ra := rep_nd (ext := TabCo1ThreeB.ext) hD 88
  have rb := rep_nd (ext := TabCo1ThreeB.ext) hD 89
  have rx := rep_nd (ext := TabCo1ThreeB.ext) hD 90
  have rz := rep_nd (ext := TabCo1ThreeB.ext) hD 91
  have hxe : x = kG TabCo1ThreeB.ext 90 := hx.eq (by rw [← hxr]; exact rx)
  subst hxe
  have haG : kG TabCo1ThreeB.ext 88 ∈ GA := kG_mem _ 88
  have hbG : kG TabCo1ThreeB.ext 89 ∈ GA := kG_mem _ 89
  have hxG : kG TabCo1ThreeB.ext 90 ∈ GA := kG_mem _ 90
  have hzG : kG TabCo1ThreeB.ext 91 ∈ GA := kG_mem _ 91
  have ru1 := rep_evalW (ext := TabCo1ThreeB.ext) hD [88, 89, 90, 91] wu1
  have rv1 := rep_evalW (ext := TabCo1ThreeB.ext) hD [88, 89, 90, 91] wv1
  have ru2 := rep_evalW (ext := TabCo1ThreeB.ext) hD [88, 89, 90, 91] wu2
  have rv2 := rep_evalW (ext := TabCo1ThreeB.ext) hD [88, 89, 90, 91] wv2
  have ru1i := ru1.inv hiu1
  have rv1i := rv1.inv hiv1
  have ru2i := ru2.inv hiu2
  have rv2i := rv2.inv hiv2
  have hGZ := List.Forall₂.cons rx (List.Forall₂.cons rz List.Forall₂.nil)
  have cardZs := card_closure_list hGZ hZok
  rw [hZsz, setOf_mem_pair] at cardZs
  have hrels' := hrels
  have hnc : kG TabCo1ThreeB.ext 88 * kG TabCo1ThreeB.ext 89 ≠
      kG TabCo1ThreeB.ext 89 * kG TabCo1ThreeB.ext 88 := by
    intro h
    apply hab
    have h1 : MRep (Native.mul (nd (kDag TabCo1ThreeB.ext) 88) (nd (kDag TabCo1ThreeB.ext) 89))
        (kG TabCo1ThreeB.ext 89 * kG TabCo1ThreeB.ext 88) := h ▸ ra.mul rb
    exact rowsMatrix_injective_of_wf hwab hwba (h1.trans (rb.mul ra).symm)
  have cxa := (rx.mul ra).eq (by rw [hxa]; exact ra.mul rx)
  have cxb := (rx.mul rb).eq (by rw [hxb]; exact rb.mul rx)
  have cza := (rz.mul ra).eq (by rw [hza]; exact ra.mul rz)
  have czb := (rz.mul rb).eq (by rw [hzb]; exact rb.mul rz)
  have cxz := (rx.mul rz).eq (by rw [hxz]; exact rz.mul rx)
  have hx3' : kG TabCo1ThreeB.ext 90 ^ 3 = 1 := (rx.pow 3).eq (by rw [hx3]; exact MRep.one)
  have hz3' : kG TabCo1ThreeB.ext 91 ^ 3 = 1 := (rz.pow 3).eq (by rw [hz3]; exact MRep.one)
  have hgs : ∀ g ∈ [88, 89, 90, 91].map (kG TabCo1ThreeB.ext),
      g ∈ Subgroup.closure ({kG TabCo1ThreeB.ext 88, kG TabCo1ThreeB.ext 89,
        kG TabCo1ThreeB.ext 90, kG TabCo1ThreeB.ext 91} : Set GL24) := by
    intro g hg
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
    exact Subgroup.subset_closure (by rcases hg with rfl | rfl | rfl | rfl <;> simp)
  have mu1 := wordG_mem hgs wu1
  have mv1 := wordG_mem hgs wv1
  have mu2 := wordG_mem hgs wu2
  have mv2 := wordG_mem hgs wv2
  generalize wordG ([88, 89, 90, 91].map (kG TabCo1ThreeB.ext)) wu1 = u1G at ru1 ru1i mu1
  generalize wordG ([88, 89, 90, 91].map (kG TabCo1ThreeB.ext)) wv1 = v1G at rv1 rv1i mv1
  generalize wordG ([88, 89, 90, 91].map (kG TabCo1ThreeB.ext)) wu2 = u2G at ru2 ru2i mu2
  generalize wordG ([88, 89, 90, 91].map (kG TabCo1ThreeB.ext)) wv2 = v2G at rv2 rv2i mv2
  have hc1 : u1G⁻¹ * v1G⁻¹ * (u1G * v1G) = kG TabCo1ThreeB.ext 90 ^ 2 :=
    ((ru1i.mul rv1i).mul (ru1.mul rv1)).eq (by rw [hcm1]; exact rx.pow 2)
  have hc2 : u2G⁻¹ * v2G⁻¹ * (u2G * v2G) = kG TabCo1ThreeB.ext 91 :=
    ((ru2i.mul rv2i).mul (ru2.mul rv2)).eq (by rw [hcm2]; exact rz)
  clear hrels' hcm1 hcm2 hiu1 hiv1 hiu2 hiv2
  set a := kG TabCo1ThreeB.ext 88 with ha_def
  set b := kG TabCo1ThreeB.ext 89 with hb_def
  set x' := kG TabCo1ThreeB.ext 90 with hx'_def
  set z := kG TabCo1ThreeB.ext 91 with hz_def
  set J : Subgroup GL24 := Subgroup.closure ({a, b, x', z} : Set GL24) with hJdef
  have haJ : a ∈ J := Subgroup.subset_closure (by simp)
  have hbJ : b ∈ J := Subgroup.subset_closure (by simp)
  have hxJ : x' ∈ J := Subgroup.subset_closure (by simp)
  have hzJ : z ∈ J := Subgroup.subset_closure (by simp)
  have hJGA : J ≤ GA := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact haG
    · exact hbG
    · exact hxG
    · exact hzG
  have hJ1 : J ≤ Subgroup.centralizer ({x'} : Set GL24) := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl | rfl
    · exact cxa.symm
    · exact cxb.symm
    · rfl
    · exact cxz.symm
  have hJ2 : J ≤ Subgroup.centralizer ({z} : Set GL24) := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl | rfl | rfl
    · exact cza.symm
    · exact czb.symm
    · exact cxz
    · rfl
  set Zs : Subgroup GL24 := Subgroup.closure ({x', z} : Set GL24) with hZsdef
  have hZsJ : Zs ≤ J := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hxJ
    · exact hzJ
  have hZsc : Zs ≤ Subgroup.centralizer (J : Set GL24) := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rcases hy with rfl | rfl
    · intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJ1 hh)
    · intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJ2 hh)
  set Z' : Subgroup ↥J := Zs.subgroupOf J with hZ'def
  have hZc : Z' ≤ Subgroup.center ↥J := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (y : GL24) ∈ Subgroup.centralizer (J : Set GL24) :=
      hZsc (Subgroup.mem_subgroupOf.1 hy)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h1 g g.2)
  have hJtop : Subgroup.closure ({⟨a, haJ⟩, ⟨b, hbJ⟩, ⟨x', hxJ⟩, ⟨z, hzJ⟩} : Set ↥J) = ⊤ := by
    have h : Subgroup.closure ((Subtype.val : ↥J → GL24) ⁻¹' ({a, b, x', z} : Set GL24)) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hset : ((Subtype.val : ↥J → GL24) ⁻¹' ({a, b, x', z} : Set GL24)) =
        ({⟨a, haJ⟩, ⟨b, hbJ⟩, ⟨x', hxJ⟩, ⟨z, hzJ⟩} : Set ↥J) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
    rw [hset] at h
    exact h
  have hgen : Subgroup.closure ({⟨a, haJ⟩, ⟨b, hbJ⟩} : Set ↥J) ⊔ Z' = ⊤ := by
    rw [eq_top_iff, ← hJtop, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (by simp)))
    · exact Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure (by simp)))
  have hrel0 : ∀ w ∈ rels, wordG [a, b] (w.map convL) ∈ Zs := by
    intro w hw
    have hmem : w.map convL ∈ TabCo1ThreeB.relsW := by
      rw [← rels_words_eq]
      exact List.mem_map.2 ⟨w, hw, rfl⟩
    have h1 := hrels _ hmem
    have h2 := rep_evalW (ext := TabCo1ThreeB.ext) hD [88, 89] (w.map convL)
    have h3 := mem_closure_list_of_contains hGZ hZok h1 h2
    rw [setOf_mem_pair] at h3
    exact h3
  have hnc' : (⟨a, haJ⟩ : ↥J) * ⟨b, hbJ⟩ ≠ ⟨b, hbJ⟩ * ⟨a, haJ⟩ := by
    intro h
    apply hnc
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at h'
    exact h'
  have hZK : Z' ≤ commutator ↥J := by
    set Cm : Subgroup GL24 := (commutator ↥J).map J.subtype with hCm
    have hx2 : x' ^ 2 ∈ Cm := by
      refine ⟨⁅(⟨u1G, mu1⟩ : ↥J)⁻¹, (⟨v1G, mv1⟩ : ↥J)⁻¹⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
      show (((⁅(⟨u1G, mu1⟩ : ↥J)⁻¹, (⟨v1G, mv1⟩ : ↥J)⁻¹⁆ : ↥J)) : GL24) = x' ^ 2
      rw [← hc1]
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_assoc]
    have hz2 : z ∈ Cm := by
      refine ⟨⁅(⟨u2G, mu2⟩ : ↥J)⁻¹, (⟨v2G, mv2⟩ : ↥J)⁻¹⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
      show (((⁅(⟨u2G, mu2⟩ : ↥J)⁻¹, (⟨v2G, mv2⟩ : ↥J)⁻¹⁆ : ↥J)) : GL24) = z
      rw [← hc2]
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_assoc]
    have hx4 : (x' ^ 2) ^ 2 = x' := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx3', one_mul]
    have hxCm : x' ∈ Cm := by
      rw [← hx4]
      exact Cm.pow_mem hx2 2
    have hZsCm : Zs ≤ Cm := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hxCm
      · exact hz2
    intro y hy
    obtain ⟨c, hc, hcy⟩ := hZsCm (Subgroup.mem_subgroupOf.1 hy)
    have : c = y := Subtype.ext hcy
    rw [← this]
    exact hc
  obtain ⟨hq, hcen, ⟨eT⟩⟩ := u43_central_ext_gen Z' ⟨a, haJ⟩ ⟨b, hbJ⟩ hZc hgen
    (fun w hw => evalW_mem_subgroupOf a b haJ hbJ Zs w (hrel0 w hw)) hnc' hZK
  have cardZ' : Nat.card ↥Z' = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZsJ).toEquiv]
    exact cardZs
  have hcard3 : Nat.card ↥(Subgroup.center ↥J) = 9 := by
    rw [hcen]
    exact cardZ'
  have cardJ : Nat.card ↥J = 29393280 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)
    have h2 : Nat.card (↥J ⧸ Subgroup.center ↥J) = 3265920 := by
      rw [Nat.card_congr eT.toEquiv]
      exact card_X₀
    rw [h1, h2, hcard3]
  have hCcard : Nat.card ↥(Subgroup.centralizer ({x'} : Set GL24) ⊓ GA) ≤ 2 * Nat.card ↥J := by
    rw [cardJ]
    exact (card_cent_le_of_powBoundN rx 3 hb1).trans (hcnt1.trans (by norm_num))
  have hJC : J ≤ Subgroup.centralizer ({x'} : Set GL24) ⊓ GA := le_inf hJ1 hJGA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨rfl, hzG, cardZs, J, hJGA, hJ1, hJ2, conj_mem_of_card_le_two_mul hJC hCcard, hq,
    by rw [cardJ]; norm_num⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co13
