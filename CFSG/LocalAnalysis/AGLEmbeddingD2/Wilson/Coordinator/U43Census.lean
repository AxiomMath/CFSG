module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensus
public import Certificates.Certificate12640

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434RemU43
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)

attribute [local irreducible] sAt

theorem extOK_spec (hext : uExtCheck = true) {t : ℕ} (ht : t < 729) (h3 : isOrd3 t = true)
    (hz : [one4, zc, zc2].contains (uAt t) = false) :
    ∃ s < 729, isOrd3 s = true ∧ commutes4 (uAt s) (uAt t) = true ∧
      (e9Elems zc (uAt t)).contains (uAt s) = false := by
  simp only [uExtCheck, List.all_eq_true, List.mem_range] at hext
  have h := hext t ht
  simp only [extOK, h3, hz, Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨s, hs, ⟨hs3, hsc⟩, hse⟩ := h
  rw [isOrd3Arr_getD hs] at hs3
  exact ⟨s, hs, hs3, hsc, hse⟩

theorem canon4_of_mem_e9Elems {a b c : List ℕ} (hc : c ∈ e9Elems a b) : canon4 c = true := by
  simp only [e9Elems, List.mem_toArray, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨x, -, y, -, rfl⟩ := hc
  exact canon4_mul4 _ _

theorem pow_three_of_isOrd3 (hsyl : uSylCheck = true) {s : ℕ} (hs : s < 729)
    (h : isOrd3 s = true) : sAt s ^ 3 = 1 := by
  simp only [isOrd3, Bool.and_eq_true, beq_iff_eq] at h
  exact pow_three_of_cube4 hsyl hs h.2

theorem contains_zc_false (hsyl : uSylCheck = true) (hzlt : uZ < 729) {t : ℕ} (ht : t < 729)
    (ha1 : sAt t ≠ 1) (haz : sAt t ∉ Subgroup.zpowers (sAt uZ)) :
    [one4, zc, zc2].contains (uAt t) = false := by
  have hne1 : uAt t ≠ one4 := fun e =>
    ha1 (toMat_injective (by rw [toMat_sAt hsyl ht, e, dec4_one4, map_one]))
  have hne2 : uAt t ≠ zc := fun e => haz (by
    have : sAt t = sAt uZ := toMat_injective (by
      rw [toMat_sAt hsyl ht, toMat_sAt hsyl hzlt]; exact congrArg dec4 e)
    rw [this]
    exact Subgroup.mem_zpowers _)
  have hne3 : uAt t ≠ zc2 := fun e => haz (by
    have : sAt t = sAt uZ * sAt uZ := toMat_injective (by
      rw [toMat_sAt hsyl ht, map_mul, toMat_sAt hsyl hzlt, e, zc2, sq4, dec4_mul4]
      rfl)
    rw [this]
    exact mul_self_mem_zpowers _)
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne]
  exact ⟨hne1, hne2, hne3⟩

theorem not_mem_closure_of_code (hsyl : uSylCheck = true) (hzlt : uZ < 729) {s t : ℕ}
    (hs : s < 729) (ht : t < 729) (hz3 : sAt uZ ^ 3 = 1) (ha3 : sAt t ^ 3 = 1)
    (hza : sAt uZ * sAt t = sAt t * sAt uZ)
    (hse : (e9Elems zc (uAt t)).contains (uAt s) = false) :
    sAt s ∉ Subgroup.closure ({sAt uZ, sAt t} : Set SUg) := by
  intro hsU
  obtain ⟨c, hc, hcd⟩ := mem_e9Elems (a := zc) (toMat_sAt hsyl hzlt) (toMat_sAt hsyl ht) hz3 ha3
    hza hsU
  have hcs : c = uAt s :=
    dec4_injective (canon4_of_mem_e9Elems hc) (canon4_uAt hsyl hs) (by rw [hcd, toMat_sAt hsyl hs])
  rw [hcs] at hc
  have hcon : (e9Elems zc (uAt t)).contains (uAt s) = true := by simpa using hc
  rw [hse] at hcon
  exact Bool.false_ne_true hcon

theorem commute_of_mem_elemAbelian {L : Type*} [Group L] {P : Subgroup L} (hP : IsElemAbelian 3 P)
    {a b : L} (ha : a ∈ P) (hb : b ∈ P) : Commute a b :=
  congrArg Subtype.val (hP.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_ext (hsyl : uSylCheck = true) (hzc : uZCheck = true) (hext : uExtCheck = true)
    {Ut : Subgroup SUg} (hU : Ut ≤ sylS) (hUe : IsElemAbelian 3 Ut) (hU9 : Nat.card Ut = 9) :
    ∃ E : Subgroup SUg, IsElemAbelian 3 E ∧ Ut ≤ E ∧ ∃ r ∈ sylS, r ∈ E ∧ r ∉ Ut := by
  obtain ⟨hzlt, hz1, hz3, hzcen⟩ := uZ_spec hsyl hzc
  by_cases hzU : sAt uZ ∈ Ut
  swap
  · exact ⟨Subgroup.closure ((Ut : Set SUg) ∪ {sAt uZ}),
      isElemAbelian_closure_union hUe hz3 (fun x hx => hzcen x (hU hx)),
      fun x hx => Subgroup.subset_closure (Or.inl hx), sAt uZ, sAt_mem hsyl hzlt,
      Subgroup.subset_closure (Or.inr rfl), hzU⟩
  obtain ⟨a, haU, haz⟩ : ∃ a ∈ Ut, a ∉ Subgroup.zpowers (sAt uZ) := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (show Ut ≤ Subgroup.zpowers (sAt uZ) from fun x hx => hall x hx)
    rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, hU9] at h
    omega
  have ha3 : a ^ 3 = 1 := hUe.2 a haU
  obtain ⟨t, ht, rfl⟩ := exists_sAt_of_mem hsyl (hU haU)
  have ha1 : sAt t ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have h3 : isOrd3 t = true := isOrd3_of_elem hsyl ht ha1 ha3
  have hle : Subgroup.closure ({sAt uZ, sAt t} : Set SUg) ≤ Ut := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzU
    · exact haU
  have hcard : Nat.card (Subgroup.closure ({sAt uZ, sAt t} : Set SUg)) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hz3 ha3
      (commute_of_mem_elemAbelian hUe hzU haU) hz1 haz
  have heq : Subgroup.closure ({sAt uZ, sAt t} : Set SUg) = Ut :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hU9])
  have hza : sAt uZ * sAt t = sAt t * sAt uZ := hzcen _ (sAt_mem hsyl ht) |>.symm
  obtain ⟨s, hs, hs3, hsc, hse⟩ :=
    extOK_spec hext ht h3 (contains_zc_false hsyl hzlt ht ha1 haz)
  have hst : sAt s * sAt t = sAt t * sAt s := commute_of_commutes4 hsyl hs ht hsc
  refine ⟨Subgroup.closure ({sAt uZ, sAt t, sAt s} : Set SUg),
    isElemAbelian_closure_triple hza (hzcen _ (sAt_mem hsyl hs)).symm hst.symm hz3 ha3
      (pow_three_of_isOrd3 hsyl hs hs3), ?_, sAt s, sAt_mem hsyl hs,
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)), ?_⟩
  · rw [← heq]
    apply Subgroup.closure_mono
    rintro x (rfl | rfl)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · rw [← heq]
    exact not_mem_closure_of_code hsyl hzlt hs ht hz3 ha3 hza hse

theorem exists_gt_elemAbelian_UX (hsyl : uSylCheck = true) (hzc : uZCheck = true)
    (hext : uExtCheck = true) {D : Subgroup UX} (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∃ E : Subgroup UX, IsElemAbelian 3 E ∧ D ≤ E ∧ ¬ E ≤ D := by
  obtain ⟨g, Ut, hUt, hUte, hUt9, hmap⟩ := exists_conj_elemAbelian hsyl hDe hD9
  obtain ⟨E, hEe, hUE, r, hrS, hrE, hrU⟩ := exists_ext hsyl hzc hext hUt hUte hUt9
  have hback : (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = D := by
    have := Item434AltPerm.map_conj_map_conj_inv D g⁻¹
    rwa [inv_inv] at this
  refine ⟨(E.map piU).map (MulAut.conj g⁻¹).toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hEe), ?_, ?_⟩
  · rw [← hback, hmap]
    exact Subgroup.map_mono (Subgroup.map_mono hUE)
  · intro hle
    apply hrU
    have hmem : (MulAut.conj g⁻¹).toMonoidHom (piU r) ∈ D := hle ⟨piU r, ⟨r, hrE, rfl⟩, rfl⟩
    have hmem' : piU r ∈ Ut.map piU := by
      rw [← hmap]
      refine ⟨(MulAut.conj g⁻¹).toMonoidHom (piU r), hmem, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    obtain ⟨u, hu, hur⟩ := hmem'
    rw [← piU_injOn_sylS hsyl (hUt hu) hrS hur]
    exact hu

theorem exists_gt_elemAbelian_of_u43
    {X : Type} [Group X] (e : X ≃* projSU 4 3 1)
    {D : Subgroup X} (hDe : IsElemAbelian 3 D) (hD9 : Nat.card D = 9) :
    ∃ E : Subgroup X, IsElemAbelian 3 E ∧ D ≤ E ∧ ¬ E ≤ D := by
  have hsyl := uSylCheck_true
  obtain ⟨-, -, -, -, hzc⟩ := uClassCheck_parts uClassCheck_true
  have hext : uExtCheck = true := Certificates.certificate12640
  set θ : X ≃* UX := e.trans projSUEquivUX with hθ
  obtain ⟨E, hEe, hDE, hED⟩ := exists_gt_elemAbelian_UX hsyl hzc hext
    (D := D.map θ.toMonoidHom)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hDe)
    (by rw [Subgroup.card_map_of_injective θ.injective, hD9])
  refine ⟨E.map θ.symm.toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hEe, ?_, ?_⟩
  · intro x hx
    exact ⟨θ x, hDE ⟨x, hx, rfl⟩, θ.symm_apply_apply x⟩
  · intro hle
    apply hED
    intro y hy
    exact ⟨θ.symm y, hle ⟨y, hy, rfl⟩, θ.apply_symm_apply y⟩

theorem census423_of_u43
    {X : Type} [Group X] [Finite X] (e : X ≃* projSU 4 3 1) :
    Census423 X := by
  intro D hD hD9
  exfalso
  obtain ⟨E, hEe, hDE, hED⟩ := exists_gt_elemAbelian_of_u43 e hD.prop hD9
  exact hED (hD.2 hEe hDE)

theorem census423_of_quot_u43
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ⧸ Subgroup.center X ≃* projSU 4 3 1) : Census423 X :=
  census423_of_u43
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e)

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.U43
