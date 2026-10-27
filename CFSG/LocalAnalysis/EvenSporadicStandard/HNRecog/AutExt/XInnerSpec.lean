module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XInnerAbs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3

theorem gens_two {a b ai bi : Table} {x y : Equiv.Perm (Fin 1408)}
    {H : Subgroup (Equiv.Perm (Fin 1408))} (ha : Rep 1408 a x) (hai : Rep 1408 ai x⁻¹)
    (hb : Rep 1408 b y) (hbi : Rep 1408 bi y⁻¹) (hx : x ∈ H) (hy : y ∈ H) :
    ∃ gg : ℕ → Equiv.Perm (Fin 1408), ∀ l < (#[a, b] : Array Table).size,
      Rep 1408 (#[a, b] : Array Table)[l]! (gg l) ∧
        Rep 1408 (#[ai, bi] : Array Table)[l]! (gg l)⁻¹ ∧ gg l ∈ H := by
  refine ⟨fun l => if l = 0 then x else y, ?_⟩
  intro l hl
  have hl2 : l < 2 := hl
  interval_cases l
  · exact ⟨ha, hai, hx⟩
  · exact ⟨hb, hbi, hy⟩

theorem gens_four {a b c d ai bi ci di : Table} {x y z w : Equiv.Perm (Fin 1408)}
    {H : Subgroup (Equiv.Perm (Fin 1408))} (ha : Rep 1408 a x) (hai : Rep 1408 ai x⁻¹)
    (hb : Rep 1408 b y) (hbi : Rep 1408 bi y⁻¹) (hc : Rep 1408 c z) (hci : Rep 1408 ci z⁻¹)
    (hd : Rep 1408 d w) (hdi : Rep 1408 di w⁻¹) (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H)
    (hw : w ∈ H) :
    ∃ gg : ℕ → Equiv.Perm (Fin 1408), ∀ l < (#[a, b, c, d] : Array Table).size,
      Rep 1408 (#[a, b, c, d] : Array Table)[l]! (gg l) ∧
        Rep 1408 (#[ai, bi, ci, di] : Array Table)[l]! (gg l)⁻¹ ∧ gg l ∈ H := by
  refine ⟨fun l => if l = 0 then x else if l = 1 then y else if l = 2 then z else w, ?_⟩
  intro l hl
  have hl4 : l < 4 := hl
  interval_cases l
  · exact ⟨ha, hai, hx⟩
  · exact ⟨hb, hbi, hy⟩
  · exact ⟨hc, hci, hz⟩
  · exact ⟨hd, hdi, hw⟩

theorem exists_conj_of_order5 {N H : Subgroup (Equiv.Perm (Fin 1408))}
    {Nl F1l gens gensInv : Array Table} {par lab : Array ℕ} {gg : ℕ → Equiv.Perm (Fin 1408)}
    {C1 : Table} {c1 : Equiv.Perm (Fin 1408)} (hN : IsEnumSet 1408 Nl (N : Set _))
    (hg : ∀ l < gens.size, Rep 1408 gens[l]! (gg l) ∧ Rep 1408 gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    (hC1 : Rep 1408 C1 c1) (hT : conjTreeOK 1408 gens gensInv C1 F1l par lab = true)
    (hF1 : xF1OK Nl F1l = true) :
    ∀ y ∈ N, y ^ 5 = 1 → y ≠ 1 → ∃ h ∈ H, h * c1 * h⁻¹ = y := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine forall_of_all hN (fun y => !ordTest 1408 5 y || memT 1408 F1l y)
    (fun y => y ^ 5 = 1 → y ≠ 1 → ∃ h ∈ H, h * c1 * h⁻¹ = y) ?_ hF1
  intro x g hx _ hb h5 h1
  rw [Bool.or_eq_true, Bool.not_eq_true'] at hb
  rcases hb with hb | hb
  · exfalso
    have hord : orderOf g = 5 := orderOf_eq_prime h5 h1
    have := (ordTest_iff_perm hx (by norm_num)).2 hord
    rw [this] at hb
    exact Bool.false_ne_true hb.symm
  · obtain ⟨c, hc, hgc⟩ := exists_conj_of_memT H hg hC1 hT hx hb
    exact ⟨c, hc, hgc.symm⟩

theorem exists_conj_of_relA {N H : Subgroup (Equiv.Perm (Fin 1408))}
    {Nl F2l gens gensInv : Array Table} {par lab : Array ℕ} {gg : ℕ → Equiv.Perm (Fin 1408)}
    {C1 C2 c1i A : Table} {c1 c2 a : Equiv.Perm (Fin 1408)}
    (hN : IsEnumSet 1408 Nl (N : Set _))
    (hg : ∀ l < gens.size, Rep 1408 gens[l]! (gg l) ∧ Rep 1408 gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ H)
    (hC1 : Rep 1408 C1 c1) (hc1i : Rep 1408 c1i c1⁻¹) (hC2 : Rep 1408 C2 c2) (hA : Rep 1408 A a)
    (hT : conjTreeOK 1408 gens gensInv C2 F2l par lab = true)
    (hF2 : xF2OK Nl F2l C1 c1i A = true) :
    ∀ v ∈ N, v ^ 3 = 1 → relA c1 v = a → ∃ d ∈ H, d * c2 * d⁻¹ = v := by
  refine forall_of_all hN
    (fun y => !(order3OK 1408 y && tblEq 1408 (relAT C1 c1i y (compT 1408 y y)) A) ||
      memT 1408 F2l y)
    (fun v => v ^ 3 = 1 → relA c1 v = a → ∃ d ∈ H, d * c2 * d⁻¹ = v) ?_ hF2
  intro x g hx _ hb h3 hrel
  rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hb
  rcases hb with (hb | hb) | hb
  · exact absurd ((order3OK_iff hx).2 h3) (by rw [hb]; exact Bool.false_ne_true)
  · exfalso
    have hinv : g⁻¹ = g * g := inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact h3)
    have hxi : Rep 1408 (compT 1408 x x) g⁻¹ := by rw [hinv]; exact Rep.compT hx hx
    have := (tblEq_iff_eq (rep_relAT hC1 hc1i hx hxi) hA).2 hrel
    rw [this] at hb
    exact Bool.false_ne_true hb.symm
  · obtain ⟨c, hc, hgc⟩ := exists_conj_of_memT H hg hC2 hT hx hb
    exact ⟨c, hc, hgc.symm⟩

theorem mem_derivedOf_of_commTab (hg : gensOK = true) {wp wq wc : List ℕ}
    (hp : wordOK wp = true) (hq : wordOK wq = true) (hc : wordOK wc = true)
    (hpZ : commTT 1408 (tabW wp) (tabW wordZ) = true)
    (hqZ : commTT 1408 (tabW wq) (tabW wordZ) = true)
    (hpi : invOK 1408 (tabW wp) (invT 1408 (tabW wp)) = true)
    (hqi : invOK 1408 (tabW wq) (invT 1408 (tabW wq)) = true)
    (he : tblEq 1408 (tabW wc) (commTab (tabW wp) (invT 1408 (tabW wp)) (tabW wq)
      (invT 1408 (tabW wq))) = true) : elemW wc ∈ derivedOf XP := by
  have rp := rep_elemW_of_gensOK hg hp
  have rq := rep_elemW_of_gensOK hg hq
  have rc := rep_elemW_of_gensOK hg hc
  have hcomm := rep_commTab rp (Rep.inv_of_invOK rp hpi) rq (Rep.inv_of_invOK rq hqi)
  rw [(tblEq_iff_eq rc hcomm).1 he]
  exact mem_derivedOf_comm (mem_XP_of_commTT hg hp hpZ) (mem_XP_of_commTT hg hq hqZ)

theorem mem_conj_pair {S : Set (Equiv.Perm (Fin 1408))} {Nl : Array Table}
    (hE : IsEnumSet 1408 Nl S) {u ui c : Table} {ug cg : Equiv.Perm (Fin 1408)}
    (hu : Rep 1408 u ug) (hui : Rep 1408 ui ug⁻¹) (hc : Rep 1408 c cg)
    (h1 : memT 1408 Nl (conjT 1408 u ui c) = true)
    (h2 : memT 1408 Nl (conjT 1408 ui u c) = true) :
    ug * cg * ug⁻¹ ∈ S ∧ ug⁻¹ * cg * ug ∈ S := by
  refine ⟨(hE.memT_iff (rep_conjT hu hui hc)).1 h1, ?_⟩
  have hu' : Rep 1408 u (ug⁻¹)⁻¹ := by rw [inv_inv]; exact hu
  have := (hE.memT_iff (rep_conjT hui hu' hc)).1 h2
  rwa [inv_inv] at this

theorem mem_cent_of_check (hg : gensOK = true) {w wc : List ℕ} (hw : wordOK w = true)
    (hwc : wordOK wc = true) (hZ : commTT 1408 (tabW w) (tabW wordZ) = true)
    (hc : commTT 1408 (tabW w) (tabW wc) = true) :
    elemW w ∈ XP ⊓ centralizer ({elemW wc} : Set (Equiv.Perm (Fin 1408))) :=
  mem_inf.2 ⟨mem_XP_of_commTT hg hw hZ, mem_centralizer_singleton_iff.2
    ((commTT_iff (rep_elemW_of_gensOK hg hw) (rep_elemW_of_gensOK hg hwc)).1 hc)⟩

structure XNFacts : Prop where
  a_mem : elemA ∈ XP
  a_central : ∀ x ∈ XP, x * elemA = elemA * x
  inner : XAutInner ↥XP ⟨elemA, a_mem⟩
  norm_N : ∀ g ∈ XP, ∀ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
    g * n * g⁻¹ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408)))
  der_le : derivedOf XP ≤ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408)))
  c1_mem : elemW xC1 ∈ derivedOf XP
  c2_mem : elemW xC2 ∈ derivedOf XP

theorem xInner_facts (hX : ClassSpec classz elemZ) (h : xInnerOK () = true) : XNFacts := by
  simp only [xInnerOK, Bool.and_eq_true, and_assoc, List.all_eq_true, List.map_toArray,
    List.map_cons, List.map_nil] at h
  obtain ⟨hg, hw, hAZ, hAu1, hAu2, hiu1, hiu2, hP1Z, hQ1Z, hP2Z, hQ2Z, hiP1, hiQ1, hiP2, hiQ2,
    hC1e, hC2e, hN, hcomm, hu1c1, hu1c2, hu2c1, hu2c2, hv1c1, hv1c2, hv2c1, hv2c2, hord5, hord3,
    hrel, hT1, hF1, hDc, hDi, hT2, hF2⟩ := h
  have wU1 : wordOK xU1 = true := hw xU1 (by simp)
  have wU2 : wordOK xU2 = true := hw xU2 (by simp)
  have wP1 : wordOK xP1 = true := hw xP1 (by simp)
  have wQ1 : wordOK xQ1 = true := hw xQ1 (by simp)
  have wP2 : wordOK xP2 = true := hw xP2 (by simp)
  have wQ2 : wordOK xQ2 = true := hw xQ2 (by simp)
  have wC1 : wordOK xC1 = true := hw xC1 (by simp)
  have wC2 : wordOK xC2 = true := hw xC2 (by simp)
  have wD1 : wordOK xD1 = true := hw xD1 (by simp)
  have wD2 : wordOK xD2 = true := hw xD2 (by simp)
  have wD3 : wordOK xD3 = true := hw xD3 (by simp)
  have wD4 : wordOK xD4 = true := hw xD4 (by simp)
  have wA : wordOK wordA = true := hw wordA (by simp)
  have rU1 := rep_elemW_of_gensOK hg wU1
  have rU2 := rep_elemW_of_gensOK hg wU2
  have rU1i := Rep.inv_of_invOK rU1 hiu1
  have rU2i := Rep.inv_of_invOK rU2 hiu2
  have rC1 := rep_elemW_of_gensOK hg wC1
  have rC2 := rep_elemW_of_gensOK hg wC2
  have rA : Rep 1408 (tabW wordA) elemA := rep_elemW_of_gensOK hg wA
  have hU1X : elemW xU1 ∈ XP := by rw [← closure_xU hX]; exact subset_closure (by simp)
  have hU2X : elemW xU2 ∈ XP := by rw [← closure_xU hX]; exact subset_closure (by simp)
  have hAX : elemA ∈ XP := mem_XP_of_commTT hg wA hAZ
  have hAc : ∀ x ∈ XP, x * elemA = elemA * x := by
    intro x hx
    rw [← closure_xU hX] at hx
    refine commute_of_mem_closure ?_ hx
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact ((commTT_iff rA rU1).1 hAu1).symm
    · exact ((commTT_iff rA rU2).1 hAu2).symm
  have hc1 := mem_derivedOf_of_commTab hg wP1 wQ1 wC1 hP1Z hQ1Z hiP1 hiQ1 hC1e
  have hc2 := mem_derivedOf_of_commTab hg wP2 wQ2 wC2 hP2Z hQ2Z hiP2 hiQ2 hC2e
  have hN' := enum_N hN
  have hconj : ∀ u ∈ ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))),
      ∀ c ∈ ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      u * c * u⁻¹ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) ∧
      u⁻¹ * c * u ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) := by
    intro u hu c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hc
    rcases hu with rfl | rfl <;> rcases hc with rfl | rfl
    · exact mem_conj_pair hN' rU1 rU1i rC1 hu1c1 hv1c1
    · exact mem_conj_pair hN' rU1 rU1i rC2 hu1c2 hv1c2
    · exact mem_conj_pair hN' rU2 rU2i rC1 hu2c1 hv2c1
    · exact mem_conj_pair hN' rU2 rU2i rC2 hu2c2 hv2c2
  have hgen : derivedOf XP ≤ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← closure_xU hX]
    exact derivedOf_le_of_gen hconj ((hN'.memT_iff (rep_commTab rU1 rU1i rU2 rU2i)).1 hcomm)
  have hnorm : ∀ g ∈ XP, ∀ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      g * n * g⁻¹ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← closure_xU hX]
    exact normalized_of_gen hconj
  have hord1 : orderOf (elemW xC1) = 5 := (ordTest_iff_perm rC1 (by norm_num)).1 hord5
  have h5 : elemW xC1 ^ 5 = 1 := by
    have := pow_orderOf_eq_one (elemW xC1)
    rwa [hord1] at this
  have h1 : elemW xC1 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord1
    exact absurd hord1 (by norm_num)
  have h3 : elemW xC2 ^ 3 = 1 := (order3OK_iff rC2).1 hord3
  have hc1inv : (elemW xC1)⁻¹ = elemW xC1 ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h5)
  have hc2inv : (elemW xC2)⁻¹ = elemW xC2 * elemW xC2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact h3)
  have rC1i : Rep 1408 (powT 1408 4 (tabW xC1)) (elemW xC1)⁻¹ := by
    rw [hc1inv]; exact Rep.powT (by norm_num) rC1 4
  have rC2i : Rep 1408 (compT 1408 (tabW xC2) (tabW xC2)) (elemW xC2)⁻¹ := by
    rw [hc2inv]; exact Rep.compT rC2 rC2
  have hrelA : relA (elemW xC1) (elemW xC2) = elemA :=
    (tblEq_iff_eq (rep_relAT rC1 rC1i rC2 rC2i) rA).1 hrel
  obtain ⟨gg1, hgg1⟩ := gens_two rU1 rU1i rU2 rU2i hU1X hU2X
  have hF1' : ∀ y ∈ derivedOf XP, y ^ 5 = 1 → y ≠ 1 → ∃ k ∈ XP, k * elemW xC1 * k⁻¹ = y :=
    fun y hy => exists_conj_of_order5 (N := closure ({elemW xC1, elemW xC2} :
      Set (Equiv.Perm (Fin 1408)))) hN' hgg1 rC1 hT1 hF1 y (hgen hy)
  have dD1 := Array.all_eq_true'.1 hDc (tabW xD1) (by simp)
  have dD2 := Array.all_eq_true'.1 hDc (tabW xD2) (by simp)
  have dD3 := Array.all_eq_true'.1 hDc (tabW xD3) (by simp)
  have dD4 := Array.all_eq_true'.1 hDc (tabW xD4) (by simp)
  have iD1 := Array.all_eq_true'.1 hDi (tabW xD1) (by simp)
  have iD2 := Array.all_eq_true'.1 hDi (tabW xD2) (by simp)
  have iD3 := Array.all_eq_true'.1 hDi (tabW xD3) (by simp)
  have iD4 := Array.all_eq_true'.1 hDi (tabW xD4) (by simp)
  rw [Bool.and_eq_true] at dD1 dD2 dD3 dD4
  have mD1 := mem_cent_of_check hg wD1 wC1 dD1.2 dD1.1
  have mD2 := mem_cent_of_check hg wD2 wC1 dD2.2 dD2.1
  have mD3 := mem_cent_of_check hg wD3 wC1 dD3.2 dD3.1
  have mD4 := mem_cent_of_check hg wD4 wC1 dD4.2 dD4.1
  have rD1 := rep_elemW_of_gensOK hg wD1
  have rD2 := rep_elemW_of_gensOK hg wD2
  have rD3 := rep_elemW_of_gensOK hg wD3
  have rD4 := rep_elemW_of_gensOK hg wD4
  obtain ⟨gg2, hgg2⟩ := gens_four rD1 (Rep.inv_of_invOK rD1 iD1) rD2 (Rep.inv_of_invOK rD2 iD2)
    rD3 (Rep.inv_of_invOK rD3 iD3) rD4 (Rep.inv_of_invOK rD4 iD4) mD1 mD2 mD3 mD4
  have hF2' : ∀ v ∈ derivedOf XP, v ^ 3 = 1 → relA (elemW xC1) v = elemA →
      ∃ d ∈ XP, d * elemW xC1 = elemW xC1 * d ∧ d * elemW xC2 * d⁻¹ = v := by
    intro v hv hv3 hvrel
    obtain ⟨d, hd, hdv⟩ := exists_conj_of_relA (N := closure ({elemW xC1, elemW xC2} :
      Set (Equiv.Perm (Fin 1408)))) hN' hgg2 rC1 rC1i rC2 rA hT2 hF2 v (hgen hv) hv3 hvrel
    exact ⟨d, (mem_inf.1 hd).1, mem_centralizer_singleton_iff.1 (mem_inf.1 hd).2, hdv⟩
  exact ⟨hAX, hAc, xAutInner_of_ambient XP hAX hAc hc1 hc2 hgen h5 h1 h3 hrelA hF1' hF2', hnorm,
    hgen, hc1, hc2⟩

theorem xInner_of_facts (F : XNFacts) :
    ∀ A : ↥XP, (A : Equiv.Perm (Fin 1408)) = elemA → XAutInner ↥XP A := by
  intro A hA
  have : A = ⟨elemA, F.a_mem⟩ := Subtype.ext hA
  rw [this]
  exact F.inner

theorem xInner_ambient (hX : ClassSpec classz elemZ) (h : xInnerOK () = true) :
    ∀ A : ↥XP, (A : Equiv.Perm (Fin 1408)) = elemA → XAutInner ↥XP A :=
  xInner_of_facts (xInner_facts hX h)

end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
