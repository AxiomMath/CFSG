module

public import Certificates.Certificate1027001
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition

import CFSG.GroupTheory.CardLeOfSylowConj

public section

namespace CFSG.EvenSmallLie.Sp6

open CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CFSG.ComponentClassification.M12Cover

theorem sp6_sylow_check : sp6SylowCheck () = true :=
  Certificates.certificate1027001.1

theorem sp6_count_check : sp6K1Count () ≤ 7 :=
  Certificates.certificate1027001.2.1

theorem sp6_class_check : sp6K2Check () = true :=
  Certificates.certificate1027001.2.2

theorem rep_of_tblEq_symm {n : ℕ} {S T : Table} {g : Equiv.Perm (Fin n)} (hS : Rep n S g)
    (h : tblEq n S T = true) : Rep n T g :=
  fun i hi => ((tblEq_iff.1 h) i hi).symm.trans (hS i hi)

theorem sp6Q_originalSubgroup_eq_closure : sp6Q.originalSubgroup =
    Subgroup.closure {g | g ∈ sp6Gens} := by
  rw [sp6Q, certificate_originalSubgroup]

theorem sp6_class1_order_ne_four
    {c₁ c₂ : Equiv.Perm (Fin 36)} (h₁ : c₁ ∈ sp6Q.originalSubgroup)
    (h₂ : c₂ ∈ sp6Q.originalSubgroup) :
    orderOf ((c₁ * sp6Rep1 * c₁⁻¹) * (c₂ * sp6Rep1 * c₂⁻¹)) ≠ 4 := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  have h := sp6_class_check
  unfold sp6K2Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, -⟩, -⟩ := h
  set cl := sp6ClassTabs () with hcl
  set S : Set (Equiv.Perm (Fin 36)) := {u | ∃ T ∈ cl, Rep 36 T u} with hS
  have hgs := listTables_spec hn (K := sp6Q.originalSubgroup) sp6Gens_mem
  have hsize : (listTables sp6Gens).size = 2 := by simp [listTables, sp6Gens]
  have hgen : ∀ l < 2, ∀ u ∈ S, sp6Gens.getD l 1 * u * (sp6Gens.getD l 1)⁻¹ ∈ S ∧
      (sp6Gens.getD l 1)⁻¹ * u * sp6Gens.getD l 1 ∈ S := by
    intro l hl u ⟨T, hT, hTu⟩
    obtain ⟨hg, hgi, -⟩ := hgs l (by rw [hsize]; exact hl)
    obtain ⟨h1, h2⟩ := hB l (by rw [hsize]; exact hl) T hT
    obtain ⟨T₁, hT₁, hT₁e⟩ := h1
    obtain ⟨T₂, hT₂, hT₂e⟩ := h2
    refine ⟨⟨T₁, hT₁, rep_of_tblEq_symm (rep_conjT hg hgi hTu) hT₁e⟩, ⟨T₂, hT₂, ?_⟩⟩
    have hgi' : Rep 36 (listTables (sp6Gens.map (·⁻¹)))[l]! (sp6Gens.getD l 1)⁻¹ := hgi
    have := rep_conjT (G := Equiv.Perm (Fin 36)) hgi' (by simpa using hg) hTu
    exact rep_of_tblEq_symm (by simpa using this) hT₂e
  have hclosed : ∀ c ∈ sp6Q.originalSubgroup, ∀ u ∈ S, c * u * c⁻¹ ∈ S := by
    intro c hc
    rw [sp6Q_originalSubgroup_eq_closure] at hc
    induction hc using Subgroup.closure_induction_left with
    | one => intro u hu; simpa using hu
    | mul_left x hx y hy ih =>
      intro u hu
      have hx' : ∃ l < 2, sp6Gens.getD l 1 = x := by
        have : x ∈ sp6Gens := hx
        simp only [sp6Gens, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl
        · exact ⟨0, by norm_num, rfl⟩
        · exact ⟨1, by norm_num, rfl⟩
      obtain ⟨l, hl, rfl⟩ := hx'
      have := (hgen l hl _ (ih u hu)).1
      simpa [mul_assoc] using this
    | inv_mul_cancel x hx y hy ih =>
      intro u hu
      have hx' : ∃ l < 2, sp6Gens.getD l 1 = x := by
        have : x ∈ sp6Gens := hx
        simp only [sp6Gens, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl
        · exact ⟨0, by norm_num, rfl⟩
        · exact ⟨1, by norm_num, rfl⟩
      obtain ⟨l, hl, rfl⟩ := hx'
      have := (hgen l hl _ (ih u hu)).2
      simpa [mul_assoc] using this
  have hr₁ : sp6Rep1 ∈ S := by
    obtain ⟨T, hT, hTe⟩ := hA
    exact ⟨T, hT, rep_of_tblEq_symm (rep_toTable hn sp6Rep1) hTe⟩
  have h1 := hclosed c₁ h₁ _ hr₁
  have h2 := hclosed c₂ h₂ _ hr₁
  obtain ⟨T₁, hT₁, hT₁r⟩ := h1
  obtain ⟨T₂, hT₂, hT₂r⟩ := h2
  have hprod := Rep.compT hT₁r hT₂r
  have hne := hC T₁ hT₁ T₂ hT₂
  intro h4
  have := (ordTest_iff perm_faithful hprod (by norm_num : 0 < 4)).2 h4
  simp [this] at hne

theorem sp6_class3_order :
    orderOf (sp6Rep3 * (evalCodes sp6Gens sp6Wit3 * sp6Rep3 * (evalCodes sp6Gens sp6Wit3)⁻¹)) =
      5 := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  have h := sp6_class_check
  unfold sp6K2Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hD⟩, -⟩ := h
  have hrep := Rep.compT (rep_toTable hn sp6Rep3)
    (rep_conjT (rep_toTable hn (evalCodes sp6Gens sp6Wit3))
      (rep_toTable hn (evalCodes sp6Gens sp6Wit3)⁻¹) (rep_toTable hn sp6Rep3))
  exact (ordTest_iff perm_faithful hrep (by norm_num)).1 hD

theorem sp6_class4_order :
    orderOf (sp6Rep4 * (evalCodes sp6Gens sp6Wit4 * sp6Rep4 * (evalCodes sp6Gens sp6Wit4)⁻¹)) =
      6 := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  have h := sp6_class_check
  unfold sp6K2Check at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hE⟩ := h
  have hrep := Rep.compT (rep_toTable hn sp6Rep4)
    (rep_conjT (rep_toTable hn (evalCodes sp6Gens sp6Wit4))
      (rep_toTable hn (evalCodes sp6Gens sp6Wit4)⁻¹) (rep_toTable hn sp6Rep4))
  exact (ordTest_iff perm_faithful hrep (by norm_num)).1 hE

theorem exists_mulEquiv_sp6
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1) {D : Set X}
    (hcl : ∃ d₀ ∈ D, ∀ d, d ∈ D ↔ IsConj d₀ d)
    (hle : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    (h4 : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4)
    {r : X} (hr : r ∈ D) (hr2 : orderOf r = 2) :
    ∃ ψ : X ≃* ↥sp6Q.originalSubgroup, (ψ r : Equiv.Perm (Fin 36)) = sp6Rep2 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hX
  let φ : X ≃* ↥sp6Q.originalSubgroup :=
    e.trans (MulEquiv.subgroupCongr sp6Q_originalSubgroup.symm)
  have hDmem : ∀ y : X, y * r * y⁻¹ ∈ D := by
    obtain ⟨d₀, hd₀, hd⟩ := hcl
    intro y
    exact (hd _).2 (((hd r).1 hr).trans (isConj_iff.2 ⟨y, rfl⟩))
  have hcls : ∀ d ∈ D, ∃ y : X, y * r * y⁻¹ = d := by
    obtain ⟨d₀, hd₀, hd⟩ := hcl
    intro d hd'
    exact isConj_iff.mp (((hd r).1 hr).symm.trans ((hd d).1 hd'))
  have hφconj : ∀ y : X, (φ (y * r * y⁻¹) : Equiv.Perm (Fin 36)) =
      (φ y : Equiv.Perm (Fin 36)) * (φ r : Equiv.Perm (Fin 36)) *
        (φ y : Equiv.Perm (Fin 36))⁻¹ := by
    intro y
    simp [map_mul, map_inv]
  have hφord : ∀ d d' : X, orderOf (d * d') =
      orderOf ((φ d : Equiv.Perm (Fin 36)) * (φ d' : Equiv.Perm (Fin 36))) := by
    intro d d'
    rw [← MulEquiv.orderOf_eq φ, ← Subgroup.orderOf_coe, map_mul, Subgroup.coe_mul]
  have hd₀H : (φ r : Equiv.Perm (Fin 36)) ∈ sp6Q.originalSubgroup := (φ r).2
  have hd₀2 : orderOf (φ r : Equiv.Perm (Fin 36)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hr2]
  obtain ⟨hcov, -⟩ := sp6_involution_cover
  obtain ⟨ρ', hρ'mem, c, hc, hcd⟩ := hcov _ hd₀H hd₀2
  rw [sp6InvReps_eq] at hρ'mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ'mem
  have hrepsH := sp6InvReps_mem
  have hH : ∀ x y : Equiv.Perm (Fin 36), x ∈ sp6Q.originalSubgroup → y ∈ sp6Q.originalSubgroup →
      x * y ∈ sp6Q.originalSubgroup := fun x y hx hy => sp6Q.originalSubgroup.mul_mem hx hy
  rcases hρ'mem with rfl | rfl | rfl | rfl
  ·
    exfalso
    obtain ⟨d, hd, d', hd', h4'⟩ := h4
    obtain ⟨y₁, rfl⟩ := hcls d hd
    obtain ⟨y₂, rfl⟩ := hcls d' hd'
    rw [hφord, hφconj, hφconj, hcd] at h4'
    have h1 : (φ y₁ : Equiv.Perm (Fin 36)) * c ∈ sp6Q.originalSubgroup :=
      sp6Q.originalSubgroup.mul_mem (φ y₁).2 hc
    have h2 : (φ y₂ : Equiv.Perm (Fin 36)) * c ∈ sp6Q.originalSubgroup :=
      sp6Q.originalSubgroup.mul_mem (φ y₂).2 hc
    refine sp6_class1_order_ne_four h1 h2 ?_
    rw [← h4']
    congr 1 <;> group
  ·
    refine ⟨φ.trans (MulAut.conj (⟨c, hc⟩ : ↥sp6Q.originalSubgroup)⁻¹), ?_⟩
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      InvMemClass.coe_inv, hcd]
    group
  ·
    exfalso
    have hw : evalCodes sp6Gens sp6Wit3 ∈ sp6Q.originalSubgroup :=
      evalCodes_mem _ sp6Gens_mem _
    have hc' : c⁻¹ ∈ sp6Q.originalSubgroup := sp6Q.originalSubgroup.inv_mem hc
    set y₁ : X := φ.symm ⟨c⁻¹, hc'⟩ with hy₁
    set y₂ : X := φ.symm ⟨evalCodes sp6Gens sp6Wit3 * c⁻¹,
      sp6Q.originalSubgroup.mul_mem hw hc'⟩ with hy₂
    have hy₁' : (φ y₁ : Equiv.Perm (Fin 36)) = c⁻¹ := by rw [hy₁]; simp
    have hy₂' : (φ y₂ : Equiv.Perm (Fin 36)) = evalCodes sp6Gens sp6Wit3 * c⁻¹ := by
      rw [hy₂]; simp
    have := hle _ (hDmem y₁) _ (hDmem y₂)
    rw [hφord, hφconj, hφconj, hy₁', hy₂', hcd] at this
    have h5 : (c⁻¹ * (c * sp6Rep3 * c⁻¹) * c⁻¹⁻¹) *
        (evalCodes sp6Gens sp6Wit3 * c⁻¹ * (c * sp6Rep3 * c⁻¹) *
          (evalCodes sp6Gens sp6Wit3 * c⁻¹)⁻¹) =
        sp6Rep3 * (evalCodes sp6Gens sp6Wit3 * sp6Rep3 * (evalCodes sp6Gens sp6Wit3)⁻¹) := by
      group
    rw [h5, sp6_class3_order] at this
    omega
  ·
    exfalso
    have hw : evalCodes sp6Gens sp6Wit4 ∈ sp6Q.originalSubgroup :=
      evalCodes_mem _ sp6Gens_mem _
    have hc' : c⁻¹ ∈ sp6Q.originalSubgroup := sp6Q.originalSubgroup.inv_mem hc
    set y₁ : X := φ.symm ⟨c⁻¹, hc'⟩ with hy₁
    set y₂ : X := φ.symm ⟨evalCodes sp6Gens sp6Wit4 * c⁻¹,
      sp6Q.originalSubgroup.mul_mem hw hc'⟩ with hy₂
    have hy₁' : (φ y₁ : Equiv.Perm (Fin 36)) = c⁻¹ := by rw [hy₁]; simp
    have hy₂' : (φ y₂ : Equiv.Perm (Fin 36)) = evalCodes sp6Gens sp6Wit4 * c⁻¹ := by
      rw [hy₂]; simp
    have := hle _ (hDmem y₁) _ (hDmem y₂)
    rw [hφord, hφconj, hφconj, hy₁', hy₂', hcd] at this
    have h5 : (c⁻¹ * (c * sp6Rep4 * c⁻¹) * c⁻¹⁻¹) *
        (evalCodes sp6Gens sp6Wit4 * c⁻¹ * (c * sp6Rep4 * c⁻¹) *
          (evalCodes sp6Gens sp6Wit4 * c⁻¹)⁻¹) =
        sp6Rep4 * (evalCodes sp6Gens sp6Wit4 * sp6Rep4 * (evalCodes sp6Gens sp6Wit4)⁻¹) := by
      group
    rw [h5, sp6_class4_order] at this
    omega

theorem sp6CentQ2_valid : ValidSchreier sp6CentQ2 := by
  have h := sp6_cent_check₂
  simp only [centCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1

theorem mem_sp6SylowPerms_iff {q : Equiv.Perm (Fin 36)} :
    q ∈ sp6SylowPerms () ↔ ∃ i < 3, ∃ j < 3, q = sp6SylowP1 () ^ i * sp6SylowP2 () ^ j := by
  simp only [sp6SylowPerms, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, hi, j, hj, rfl⟩

theorem commT_conjT_iff {T : Table} {g q : Equiv.Perm (Fin 36)} (hT : Rep 36 T g) :
    commT 36 T (conjT 36 (toTable q) (toTable q⁻¹) T) = true ↔
      g * (q * g * q⁻¹) = (q * g * q⁻¹) * g :=
  commT_iff hT (rep_conjT (rep_toTable (by norm_num) q) (rep_toTable (by norm_num) q⁻¹) hT)

theorem sp6K1Test_iff {T : Table} {g : Equiv.Perm (Fin 36)} (hT : Rep 36 T g) :
    sp6K1Test (sp6SylowTabs ()) T = true ↔ orderOf g = 2 ∧
      ∀ q ∈ sp6SylowPerms (), g * (q * g * q⁻¹) = (q * g * q⁻¹) * g := by
  simp only [sp6K1Test, sp6SylowTabs, List.all_map, Function.comp_def, Bool.and_eq_true,
    List.all_eq_true, commT_conjT_iff hT, ordTest_iff perm_faithful hT (by norm_num : 0 < 2),
    decide_eq_true_eq]

theorem sp6_Y_ncard_le :
    {u : Equiv.Perm (Fin 36) | u ∈ sp6CentQ2.originalSubgroup ∧ orderOf u = 2 ∧
      ∀ q ∈ sp6SylowPerms (), u * (q * u * q⁻¹) = (q * u * q⁻¹) * u}.ncard ≤ 7 := by
  classical
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  have hcount := sp6_count_check
  set P : Equiv.Perm (Fin 36) → Prop := fun u => orderOf u = 2 ∧
    ∀ q ∈ sp6SylowPerms (), u * (q * u * q⁻¹) = (q * u * q⁻¹) * u with hP
  have hfP : ∀ (T : Table) (g : Equiv.Perm (Fin 36)), Rep 36 T g →
      (sp6K1Test (sp6SylowTabs ()) T = true ↔ P g) := fun T g hT => sp6K1Test_iff hT
  have hspec := countProducts_spec (P := P) (f := sp6K1Test (sp6SylowTabs ())) hfP
    (forall₂_levelTables hn sp6CentQ2) (rep_toTable hn (1 : Equiv.Perm (Fin 36)))
  have hQ := sp6CentQ2_valid
  have hL : ((products ((List.finRange sp6CentQ2.baseCount).map (levelTransversals sp6CentQ2))).map
      ((1 : Equiv.Perm (Fin 36)) * ·)) = enumeration sp6CentQ2 := by
    simp [enumeration]
  rw [hL] at hspec
  have hc : (enumeration sp6CentQ2).countP (fun h => decide (P h)) ≤ 7 := by
    rw [← hspec]
    exact hcount
  refine le_trans ?_ hc
  rw [List.countP_eq_length_filter]
  have hsub : {u : Equiv.Perm (Fin 36) | u ∈ sp6CentQ2.originalSubgroup ∧ orderOf u = 2 ∧
      ∀ q ∈ sp6SylowPerms (), u * (q * u * q⁻¹) = (q * u * q⁻¹) * u} ⊆
      ↑((enumeration sp6CentQ2).filter (fun h => decide (P h))).toFinset := by
    rintro u ⟨hu, hu2, hu3⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨(mem_enumeration_iff sp6CentQ2 hQ u).2 hu, hu2, hu3⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact List.toFinset_card_le _

theorem sp6CentGens2_mem : ∀ g ∈ sp6CentGens2, g ∈ sp6CentQ2.originalSubgroup := fun g hg => by
  rw [sp6CentQ2, certificate_originalSubgroup]
  exact Subgroup.subset_closure hg

theorem sp6SylowP1_mem : sp6SylowP1 () ∈ sp6CentQ2.originalSubgroup :=
  evalCodes_mem _ sp6CentGens2_mem _

theorem sp6SylowP2_mem : sp6SylowP2 () ∈ sp6CentQ2.originalSubgroup :=
  evalCodes_mem _ sp6CentGens2_mem _

theorem sp6Sylow_facts :
    orderOf (sp6SylowP1 ()) = 3 ∧ orderOf (sp6SylowP2 ()) = 3 ∧
      sp6SylowP1 () * sp6SylowP2 () = sp6SylowP2 () * sp6SylowP1 () := by
  have hn : (36 : ℕ) < 2 ^ 32 := by norm_num
  have h := sp6_sylow_check
  unfold sp6SylowCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨(ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 h1,
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 h2,
    (commT_iff (rep_toTable hn _) (rep_toTable hn _)).1 h3⟩

theorem sp6_A_card_le
    (P : Sylow 3 ↥sp6CentQ2.originalSubgroup) (A : Subgroup ↥sp6CentQ2.originalSubgroup)
    (hA2 : ∀ e ∈ A, e * e = 1) (hAc : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e)
    (hAP : ∀ t ∈ P, ∀ x ∈ A, t * x * t⁻¹ ∈ A) : Nat.card ↥A ≤ 8 := by
  classical
  obtain ⟨ho1, ho2, hcomm⟩ := sp6Sylow_facts
  set p₁ : ↥sp6CentQ2.originalSubgroup := ⟨sp6SylowP1 (), sp6SylowP1_mem⟩ with hp₁
  set p₂ : ↥sp6CentQ2.originalSubgroup := ⟨sp6SylowP2 (), sp6SylowP2_mem⟩ with hp₂
  have h1 : p₁ ^ 3 = 1 := Subtype.ext (by
    simpa [hp₁] using (by rw [← ho1]; exact pow_orderOf_eq_one _ : sp6SylowP1 () ^ 3 = 1))
  have h2 : p₂ ^ 3 = 1 := Subtype.ext (by
    simpa [hp₂] using (by rw [← ho2]; exact pow_orderOf_eq_one _ : sp6SylowP2 () ^ 3 = 1))
  have hc : p₁ * p₂ = p₂ * p₁ := Subtype.ext (by simpa [hp₁, hp₂] using hcomm)
  refine CFSG.GroupTheory.card_le_of_sylow_conj h1 h2 hc P A hA2 hAc hAP (n := 7) ?_
  have hY := sp6_Y_ncard_le
  refine le_trans ?_ hY
  have hinj : Function.Injective (Subtype.val : ↥sp6CentQ2.originalSubgroup →
      Equiv.Perm (Fin 36)) := Subtype.val_injective
  rw [← Set.ncard_image_of_injective _ hinj]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨u, ⟨hu2, hu1, hu3⟩, rfl⟩
  refine ⟨u.2, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · have := congrArg Subtype.val hu2
      simpa [pow_two] using this
    · intro h
      exact hu1 (Subtype.ext h)
  · intro q hq
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_sp6SylowPerms_iff.1 hq
    have := congrArg Subtype.val (hu3 i hi j hj)
    simpa [hp₁, hp₂] using this


theorem card_le_eight_of_rootClass
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1) {D : Set X}
    (hcl : ∃ d₀ ∈ D, ∀ d, d ∈ D ↔ IsConj d₀ d)
    (hle : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    (h4 : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4)
    {r : X} (hr : r ∈ D) (hr2 : orderOf r = 2)
    (P : Sylow 3 ↥(Subgroup.centralizer ({r} : Set X))) (A : Subgroup X)
    (hA2 : ∀ e ∈ A, e * e = 1) (hAc : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e)
    (hAr : ∀ x ∈ A, x * r = r * x)
    (hAP : ∀ t : ↥(Subgroup.centralizer ({r} : Set X)), t ∈ P → ∀ x ∈ A,
      (t : X) * x * (t : X)⁻¹ ∈ A) :
    Nat.card ↥A ≤ 8 := by
  haveI : Finite X := Finite.of_equiv _ (nonempty_mulEquiv_co3X36 hX).some.symm.toEquiv
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_sp6 hX hcl hle h4 hr hr2
  have hcent : centralizerIn sp6Q.originalSubgroup (ψ r : Equiv.Perm (Fin 36)) =
      sp6CentQ2.originalSubgroup := by
    rw [hψ]
    exact sp6_cent_spec₂.1
  let ε : ↥(Subgroup.centralizer ({r} : Set X)) ≃* ↥sp6CentQ2.originalSubgroup :=
    (centralizerEquiv ψ r).trans ((centralizerSubgroupEquiv sp6Q.originalSubgroup (ψ r)).trans
      (MulEquiv.subgroupCongr hcent))
  have hAC : A ≤ Subgroup.centralizer ({r} : Set X) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAr x hx)
  have key := CFSG.GroupTheory.card_le_of_mulEquiv_of_sylow ε (n := 8) (fun P' A' hA2' hAc' hAP' =>
    sp6_A_card_le P' A' hA2' hAc' hAP') P (A.subgroupOf (Subgroup.centralizer ({r} : Set X)))
    (fun e he => Subtype.ext (hA2 e he)) (fun e he f hf => Subtype.ext (hAc e he f hf))
    (fun t ht x hx => hAP t ht x hx)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv] at key

end CFSG.EvenSmallLie.Sp6
