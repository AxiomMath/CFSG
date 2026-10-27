module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLocalTriple
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingReduction

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem commuting_pair_lift {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker)) {a₁ a₂ : A}
    (ha₁ : IsInvolution a₁) (ha₂ : IsInvolution a₂) (h12 : Commute a₁ a₂) {b : B}
    (hb : IsInvolution b) (hb₁ : Commute b (f a₁)) (hb₂ : Commute b (f a₂)) :
    ∃ w : A, IsInvolution w ∧ f w = b ∧ Commute w a₁ ∧ Commute w a₂ := by
  let C := Subgroup.centralizer ({a₁} : Set A)
  have hCmap : C.map f = Subgroup.centralizer ({f a₁} : Set B) :=
    CFSG.ProperTwoGeneratedCore.involution_centralizer_image f hf hodd ha₁
  let f' : C →* Subgroup.centralizer ({f a₁} : Set B) :=
    (f.comp C.subtype).codRestrict _ (fun c => hCmap ▸ ⟨c, c.property, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨c, hc, rfl⟩ := hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hodd' : Odd (Nat.card f'.ker) := by
    have hle : f'.ker.map C.subtype ≤ f.ker := by
      rintro x ⟨c, hc, rfl⟩
      exact congrArg Subtype.val hc
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective C.subtype_injective] at hdvd
    exact hodd.of_dvd_nat hdvd
  have ha₂C : a₂ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr h12.eq.symm
  have hbC : b ∈ Subgroup.centralizer ({f a₁} : Set B) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hb₁.eq
  have ha₂I : IsInvolution (⟨a₂, ha₂C⟩ : C) :=
    ⟨fun h => ha₂.ne_one (congrArg Subtype.val h), Subtype.ext ha₂.sq_eq_one⟩
  have hbI : IsInvolution (⟨b, hbC⟩ : Subgroup.centralizer ({f a₁} : Set B)) :=
    ⟨fun h => hb.ne_one (congrArg Subtype.val h), Subtype.ext hb.sq_eq_one⟩
  obtain ⟨w, hwI, hfw, hw⟩ :=
    CFSG.ProperTwoGeneratedCore.commuting_involution_lift_of_odd_kernel f' hf' hodd' ha₂I hbI
      (Subtype.ext hb₂.eq)
  refine ⟨w, ⟨fun h => hwI.ne_one (Subtype.ext h), congrArg Subtype.val hwI.sq_eq_one⟩,
    congrArg Subtype.val hfw, ?_, congrArg Subtype.val hw⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp w.property)

theorem local_embedding_of_no_central_involution
    {X : Type} [Group X] [Finite X] {M : Subgroup X} {x : X}
    (hx : orderOf x = 2) (hM : M ≠ ⊤) (huniq : ∀ g : X, x ∈ rightConjugate M g ↔ g ∈ M)
    (h2 : CentralProductCentralizer M x) (hhull : involutionPointHull x = ⊤)
    (hO : CFSG.oddCore X = ⊥) (hnc : ∀ c ∈ Subgroup.center X, orderOf c ≠ 2)
    (hIH : NormStatement (Nat.card X - 1))
    {u : X} (hu : orderOf u = 2) (hux : Commute u x)
    (hesc : ¬ Subgroup.centralizer ({u} : Set X) ≤ M) :
    fusionStronglyEmbedded (M.subgroupOf (localInvolutionPointHull x u)) := by
  have h1 := productUniqueContainment_of_centralProductCentralizer hx huniq h2
  by_contra hnse
  let T : Set X := involutionPointClass x ∩ (Subgroup.centralizer ({u} : Set X) : Set X)
  let L := localInvolutionPointHull x u
  have hT : T ⊆ involutionPointClass x := fun _ h => h.1
  have hxT : x ∈ T := ⟨distinguished_mem_pointClass x,
    Subgroup.mem_centralizer_singleton_iff.mpr hux.eq.symm⟩
  obtain ⟨c, hcC, hcM⟩ := Set.not_subset.mp hesc
  have hcC' : c ∈ Subgroup.centralizer ({u} : Set X) := hcC
  have hx'T : c⁻¹ * x * c ∈ T := by
    refine ⟨class_conj_mem (distinguished_mem_pointClass x) c, ?_⟩
    have hxC : x ∈ Subgroup.centralizer ({u} : Set X) := hxT.2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC') hxC) hcC'
  have hx'base : (c⁻¹ * x * c) • (QuotientGroup.mk 1 : X ⧸ M) ≠ QuotientGroup.mk 1 :=
    fun h => hcM ((conj_mem_iff huniq c).mp (class_mem_iff_fixes_base.mpr h))
  have hhullL : involutionPointHull (⟨x, Subgroup.subset_closure hxT⟩ : L) = ⊤ :=
    hull_closure_eq_top hx huniq h1 hT hxT hx'T hx'base
  let xL : L := ⟨x, Subgroup.subset_closure hxT⟩
  have hLM : ¬ L ≤ M := fun h => hx'base (class_mem_iff_fixes_base.mp
    (h (Subgroup.subset_closure hx'T)))
  have hxL2 : orderOf xL = 2 := (Subgroup.orderOf_mk x _).trans hx
  have huniqL := unique_subgroupOf huniq L xL.property
  have h2L := centralProduct_subgroupOf hx huniq h2 L xL.property hLM
  have hML : M.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hLM
    intro y hy
    have hmem : (⟨y, hy⟩ : L) ∈ M.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact hmem
  by_cases hiso : ∀ t ∈ involutionPointClass xL, Commute xL t → t = xL
  · exact hnse (stronglyEmbedded_of_isolated hxL2 hML huniqL h2L.1 hhullL hiso)
  obtain ⟨tL, htL, hxtL, hneL⟩ : ∃ t ∈ involutionPointClass xL, Commute xL t ∧ t ≠ xL := by
    by_contra h
    apply hiso
    intro t ht hxt
    by_contra hne
    exact h ⟨t, ht, hxt, hne⟩
  have hOL : CFSG.oddCore L ≤ M.subgroupOf L :=
    oddCore_le_of_commuting_class hxL2 huniqL h2L htL hxtL hneL
  let q := QuotientGroup.mk' (CFSG.oddCore L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = CFSG.oddCore L := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card q.ker) := by
    rw [hker]
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hkerM : q.ker ≤ M.subgroupOf L := by
    rw [hker]
    exact hOL
  have hCu : Subgroup.centralizer ({u} : Set X) ≠ ⊤ := by
    intro htop
    apply hnc u _ hu
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have hg : g ∈ Subgroup.centralizer ({u} : Set X) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hcardL : Nat.card L < Nat.card X := by
    have hle : L ≤ Subgroup.centralizer ({u} : Set X) :=
      localInvolutionPointHull_le_centralizer x u
    have hlt : Nat.card (Subgroup.centralizer ({u} : Set X)) < Nat.card X := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hCu)
      rwa [Subgroup.card_top] at this
    exact (Subgroup.card_le_of_le hle).trans_lt hlt
  have hcard : Nat.card (L ⧸ CFSG.oddCore L) ≤ Nat.card X - 1 := by
    have := Nat.card_le_card_of_surjective q hq
    omega
  have hxb2 : orderOf (q xL) = 2 := orderOf_map_of_odd q hodd hxL2
  have hN := hIH (L ⧸ CFSG.oddCore L) hcard ((M.subgroupOf L).map q) (q xL) hxb2
    (map_ne_top q hkerM hML) (unique_map q hq hkerM huniqL)
    (centralProduct_map q hq hodd hxL2 h2L)
    (hull_map_eq_top q hq hhullL) (CFSG.ComponentClassification.OddCore.quotient_corefree L)
  have hxLI := isInvolution_of_orderOf hxL2
  have htL2 : orderOf tL = 2 := class_orderOf hxL2 htL
  have htLI := isInvolution_of_orderOf htL2
  have htb : q tL ∈ involutionPointClass (q xL) :=
    (CFSG.ProperTwoGeneratedCore.involution_point_class_image_iff q hq hodd hxLI htLI).mpr htL
  have hxtb : Commute (q xL) (q tL) := hxtL.map q
  have hneb : q tL ≠ q xL := by
    intro h
    apply hneL
    have hk : xL⁻¹ * tL ∈ q.ker := by
      change q (xL⁻¹ * tL) = 1
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have hsq : (xL⁻¹ * tL) ^ 2 = 1 := by
      have hxx : xL * xL = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hxL2).1
      have htt : tL * tL = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp htL2).1
      rw [inv_eq_of_mul_eq_one_left hxx, pow_two, mul_assoc, ← mul_assoc tL xL tL,
        ← hxtL.eq, mul_assoc, htt, mul_one, hxx]
    have h1' := eq_one_of_sq_eq_one_of_odd hodd hk hsq
    have h2' := congrArg (xL * ·) h1'
    simpa only [mul_inv_cancel_left, mul_one] using h2'
  rcases hN with hrank | ⟨ub, hub2, hubc, -, -, hse, hcls⟩
  · have h2r := CFSG.TwoRankLowerBound.Helpers.two_le_twoRank_of_commuting_involutions _
      (q xL) (q tL) hxb2 (class_orderOf hxb2 htb) hneb.symm hxtb
    omega
  have hMbne : (M.subgroupOf L).map q ≠ ⊤ := map_ne_top q hkerM hML
  by_cases hub1 : ub = 1
  · apply hnse
    have hcommtop : commutator (L ⧸ CFSG.oddCore L) = ⊤ := by
      apply eq_top_iff.mpr
      rw [← hull_map_eq_top q hq hhullL]
      refine (Subgroup.closure_le _).mpr fun s hs => ?_
      have h := hcls s hs
      rwa [hub1, inv_one, one_mul] at h
    let e : commutator (L ⧸ CFSG.oddCore L) ≃* (L ⧸ CFSG.oddCore L) :=
      (MulEquiv.subgroupCongr hcommtop).trans Subgroup.topEquiv
    have hmap : (((M.subgroupOf L).map q).subgroupOf (commutator (L ⧸ CFSG.oddCore L))).map
        e.toMonoidHom = (M.subgroupOf L).map q := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hy
        refine ⟨⟨y, hcommtop ▸ Subgroup.mem_top y⟩, hy, rfl⟩
    have hseb := hse.map_mulEquiv e
    rw [hmap] at hseb
    exact stronglyEmbedded_of_map_odd_kernel q hq hodd hkerM hseb
  have hxbc : q xL ∉ Subgroup.center (L ⧸ CFSG.oddCore L) := by
    intro hc
    apply hneb
    obtain ⟨g, hg⟩ := htb
    rw [← hg]
    change g⁻¹ * q xL * g = q xL
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hc g), inv_mul_cancel_left]
  obtain ⟨bb, hbb, hxbb, htbb, hbbt, hprod⟩ :=
    exists_triple_of_split hxb2 hxbc htb hxtb hneb hubc hub2 hse hcls
  have hbbI : IsInvolution bb := isInvolution_of_orderOf (class_orderOf hxb2 hbb)
  obtain ⟨bL, hbLI, hqb, hbx, hbt⟩ :=
    commuting_pair_lift q hq hodd hxLI htLI hxtL hbbI hxbb.symm htbb.symm
  have hbL : bL ∈ involutionPointClass xL :=
    (CFSG.ProperTwoGeneratedCore.involution_point_class_image_iff q hq hodd hxLI hbLI).mp
      (hqb ▸ hbb)
  have hclsX : ∀ s : L, s ∈ involutionPointClass xL → (s : X) ∈ involutionPointClass x := by
    rintro s ⟨g, hg⟩
    exact ⟨(g : X), congrArg Subtype.val hg⟩
  have ht := hclsX tL htL
  have hb := hclsX bL hbL
  have hxt : Commute x (tL : X) := congrArg Subtype.val hxtL
  have hxb : Commute x (bL : X) := (congrArg Subtype.val hbx).symm
  have htbX : Commute (tL : X) (bL : X) := (congrArg Subtype.val hbt).symm
  have htx : (tL : X) ≠ x := fun h => hneL (Subtype.ext h)
  have hbt' : (bL : X) ≠ (tL : X) := by
    intro h
    apply hbbt
    rw [← hqb, Subtype.ext h]
  have hxx : xL * xL = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hxL2).1
  have htt : tL * tL = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp htL2).1
  have hbb2 : bL * bL = 1 := by simpa only [pow_two] using hbLI.sq_eq_one
  let wL : L := xL * tL * bL
  have hqw : q wL = ub := by
    change q (xL * tL * bL) = ub
    rw [map_mul, map_mul, hqb]
    exact hprod
  have hw1 : wL ≠ 1 := fun h => hub1 (by rw [← hqw, h, map_one])
  have hwsq : wL ^ 2 = 1 := by
    change (xL * tL * bL) ^ 2 = 1
    have hcomm : Commute (xL * tL) bL := (hbx.symm.mul_left hbt.symm)
    rw [hcomm.mul_pow, hxtL.mul_pow, pow_two, pow_two, pow_two, hxx, htt, hbb2, one_mul,
      one_mul]
  have hwLI : IsInvolution wL := ⟨hw1, hwsq⟩
  have hesc_w : ¬ Subgroup.centralizer ({x * (tL : X) * (bL : X)} : Set X) ≤ M := by
    intro hle
    apply hMbne
    have hcm := CFSG.ProperTwoGeneratedCore.involution_centralizer_image q hq hodd hwLI
    rw [hqw] at hcm
    have htopc : Subgroup.centralizer ({ub} : Set (L ⧸ CFSG.oddCore L)) = ⊤ :=
      eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hubc g)
    rw [eq_top_iff, ← htopc, ← hcm]
    apply Subgroup.map_mono
    intro g hg
    apply hle
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hwcls : x * (tL : X) * (bL : X) ∉ involutionPointClass x := by
    intro hw
    have hxw : Commute x (x * (tL : X) * (bL : X)) :=
      ((Commute.refl x).mul_right hxt).mul_right hxb
    have hwx : x * (tL : X) * (bL : X) ≠ x := by
      intro h
      apply hbt'
      have htb1 : (tL : X) * (bL : X) = 1 := by
        have h' := congrArg (x⁻¹ * ·) h
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel] using h'
      have htt' : (tL : X) * (tL : X) = 1 := congrArg Subtype.val htt
      calc (bL : X) = (tL : X) * (tL : X) * (bL : X) := by rw [htt', one_mul]
        _ = (tL : X) := by rw [mul_assoc, htb1, mul_one]
    have hC := h2.2 _ hw hxw hwx
    have hwM : x * (tL : X) * (bL : X) ∈ M := hC (Subgroup.mem_centralizer_singleton_iff.mpr
      (hxw.symm.mul_right (Commute.refl _)).eq)
    exact hesc_w (centralizer_le_of_class_mem huniq hw hwM)
  have hfix := smul_eq_of_escaping_triple hx huniq h1 ht hb hxt hxb htbX htx hbt' hesc_w hwcls
  have hcen := normalCore_le_center hx huniq h1 hM hO hhull (mem_normalCore_of_smul_eq hfix)
  apply hnc _ hcen
  have hwo : orderOf wL = 2 := orderOf_of_isInvolution hwLI
  rw [← Subgroup.orderOf_coe] at hwo
  exact hwo

end CFSG.ComponentClassification.AschbacherStrongEmbedding
