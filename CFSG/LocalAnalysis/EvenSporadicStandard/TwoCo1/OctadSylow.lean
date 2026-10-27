module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0Mono
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OctadIsoBasic
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Certificate24514

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.B.TwoA.Census

theorem fixBad_eq_zero : fixBad = 0 :=
  Certificates.certificate24514.1

theorem sqSum_Ω : sqSum 16777215 = 6528 :=
  Certificates.certificate24514.2.1

theorem sqSum_oct : sqSum 255 = 15232 :=
  Certificates.certificate24514.2.2.1

theorem sqSum_oct_Ω : sqSum 16776960 = 10368 :=
  Certificates.certificate24514.2.2.2

theorem mul_self_gO_mul_PO (a : C) (p : AutPerm) :
    (gO a * PO p) * (gO a * PO p) = gO (a + (permC p).symm a) * PO (p * p) := by
  calc (gO a * PO p) * (gO a * PO p) = gO a * ((PO p * gO a) * PO p) := by simp only [mul_assoc]
    _ = gO a * ((gO ((permC p).symm a) * PO p) * PO p) := by rw [PO_mul_gO]
    _ = (gO a * gO ((permC p).symm a)) * (PO p * PO p) := by simp only [mul_assoc]
    _ = gO (a + (permC p).symm a) * PO (p * p) := by rw [gO_add', PO_mul]

theorem mul_self_eq_gO_iff (a : C) (p : AutPerm) (d : C) :
    (gO a * PO p) * (gO a * PO p) = gO d ↔ p * p = 1 ∧ a + (permC p).symm a = d := by
  rw [mul_self_gO_mul_PO]
  constructor
  · intro h
    have h' : gO (a + (permC p).symm a) * PO (p * p) = gO d * PO 1 := by
      rw [h, PO_one, mul_one]
    obtain ⟨h1, h2⟩ := gO_mul_PO_inj h'
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, PO_one, mul_one]

@[expose] noncomputable def monoEquiv (H : Subgroup AutPerm) : C × H ≃ monoSub H :=
  Equiv.ofBijective (fun x : C × H => (⟨gO x.1 * PO x.2, x.1, x.2, x.2.2, rfl⟩ : monoSub H))
    ⟨fun x y hxy => by
      have h := gO_mul_PO_inj (congrArg Subtype.val hxy)
      exact Prod.ext h.1 (Subtype.ext h.2), by
      rintro ⟨_, a, p, hp, rfl⟩
      exact ⟨(a, ⟨p, hp⟩), rfl⟩⟩

theorem sqCount_monoSub (H : Subgroup AutPerm) (d : C) :
    sqCount (monoSub H) (gO d) =
      Nat.card {x : C × H // (x.2 : AutPerm) * x.2 = 1 ∧ x.1 + (permC x.2).symm x.1 = d} :=
  (Nat.card_congr ((monoEquiv H).subtypeEquiv fun x => (mul_self_eq_gO_iff x.1 x.2 d).symm)).symm

theorem permC_symm_eq_of_mul_self {p : AutPerm} (hp : p * p = 1) (a : C) :
    (permC p).symm a = permC p a := by
  rw [LinearEquiv.symm_apply_eq, ← permC_mul, hp, permC_one]

section Sylow

theorem pt_mem_sylowSub {i : ℕ} (hi : i < sylowCert.pts.size) :
    pt sylowCert i ∈ sylowSub :=
  (sylowSub_facts.2 _).2 ⟨i, hi, rfl⟩

theorem mem_sylowP {p : AutPerm} :
    p ∈ (sylowP : Subgroup AutPerm) ↔ (p : Equiv.Perm (Fin 24)) ∈ sylowSub := by
  rw [coe_sylowP, Subgroup.mem_subgroupOf]

@[expose] noncomputable def sylowIdx :
    Finset.range sylowCert.pts.size ≃ (sylowP : Subgroup AutPerm) :=
  Equiv.ofBijective
    (fun i => ⟨⟨pt sylowCert i, sylowSub_le (pt_mem_sylowSub (Finset.mem_range.1 i.2))⟩,
      mem_sylowP.2 (pt_mem_sylowSub (Finset.mem_range.1 i.2))⟩)
    ⟨fun i j h => Subtype.ext (certOK_inj sylowCert_ok (Finset.mem_range.1 i.2)
        (Finset.mem_range.1 j.2) (congrArg (fun p : (sylowP : Subgroup AutPerm) =>
          (p : AutPerm).1) h)), fun p => by
      obtain ⟨i, hi, e⟩ := (sylowSub_facts.2 _).1 (mem_sylowP.1 p.2)
      exact ⟨⟨i, Finset.mem_range.2 hi⟩, Subtype.ext (Subtype.ext e)⟩⟩

theorem permWord_decode {arr : Array ℕ} (h : PermArr arr = true) (w : Fin 24 → ZMod 2) :
    permWord (decode arr) w = permWordArr arr w := by
  rw [permWordArr, permWord, ← decode_ainv h, coe_decode (PermArr_ainv h)]

theorem mul_self_eq_one_iff {i : ℕ} (hi : i < sylowCert.pts.size)
    {p : AutPerm} (hp : (p : Equiv.Perm (Fin 24)) = pt sylowCert i) :
    p * p = 1 ↔ amul sylowCert.pts[i]! sylowCert.pts[i]! = idArr := by
  have harr := certOK_perm sylowCert_ok hi
  constructor
  · intro h
    apply decode_inj (PermArr_amul harr harr) PermArr_idArr
    rw [decode_amul harr harr, decode_idArr]
    have := congrArg Subtype.val h
    simpa [hp, pt] using this
  · intro h
    apply Subtype.ext
    have := congrArg decode h
    rw [decode_amul harr harr, decode_idArr] at this
    simpa [hp, pt] using this

theorem sum_permC_eq_sumCount {i : ℕ}
    (hi : i < sylowCert.pts.size) {p : AutPerm} (hp : (p : Equiv.Perm (Fin 24)) = pt sylowCert i)
    (hpp : p * p = 1) (d : C) (m : ℕ) (hd : (d : Fin 24 → ZMod 2) = bvec 24 m) :
    ∑ a : C, (if a + (permC p).symm a = d then 1 else 0) = sumCount sylowCert.pts[i]! m := by
  classical
  have harr := certOK_perm sylowCert_ok hi
  let F : (Fin 24 → ZMod 2) → ℕ := fun x =>
    if x + permWordArr sylowCert.pts[i]! x = bvec 24 m then 1 else 0
  have h1 : sumCount sylowCert.pts[i]! m = ∑ x ∈ Finset.univ.filter (· ∈ C), F x :=
    (sum_C_eq_treeSumN F).symm
  rw [h1, Finset.sum_subtype (p := (· ∈ C)) (Finset.univ.filter (· ∈ C)) (fun x => by simp) F]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hcoe : ((permC p a : C) : Fin 24 → ZMod 2) = permWordArr sylowCert.pts[i]! a := by
    rw [coe_permC, hp, pt, permWord_decode harr]
  simp only [F]
  rw [permC_symm_eq_of_mul_self hpp, ← hd]
  have : (a + permC p a = d) ↔ ((a : Fin 24 → ZMod 2) + permWordArr sylowCert.pts[i]! a =
      (d : Fin 24 → ZMod 2)) := by
    rw [Subtype.ext_iff, Submodule.coe_add, hcoe]
  by_cases h : a + permC p a = d
  · have h' := this.1 h
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ ((a : Fin 24 → ZMod 2) + permWordArr sylowCert.pts[i]! a =
        (d : Fin 24 → ZMod 2)) := fun h'' => h (this.2 h'')
    simp only [h, h', ↓reduceIte]

theorem sqCount_monoSub_sylowP
    (d : C) (m : ℕ) (hd : (d : Fin 24 → ZMod 2) = bvec 24 m) :
    sqCount (monoSub (sylowP : Subgroup AutPerm)) (gO d) = sqSum m := by
  classical
  let _ : Fintype (sylowP : Subgroup AutPerm) := Fintype.ofFinite _
  rw [sqCount_monoSub, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type_right, sqSum]
  conv_rhs => rw [← Finset.sum_coe_sort]
  refine Fintype.sum_equiv sylowIdx.symm _ _ fun p => ?_
  obtain ⟨i, rfl⟩ := sylowIdx.surjective p
  rw [Equiv.symm_apply_apply]
  have hi := Finset.mem_range.1 i.2
  by_cases hpp : ((sylowIdx i : (sylowP : Subgroup AutPerm)) : AutPerm) * sylowIdx i = 1
  · have h2 := (mul_self_eq_one_iff hi (p := (sylowIdx i : AutPerm)) rfl).1 hpp
    simp only [h2, ↓reduceIte]
    rw [← sum_permC_eq_sumCount hi rfl hpp d m hd]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hpp]
  · have h2 : ¬ amul sylowCert.pts[(i : ℕ)]! sylowCert.pts[(i : ℕ)]! = idArr := fun h =>
      hpp ((mul_self_eq_one_iff hi (p := (sylowIdx i : AutPerm)) rfl).2 h)
    simp only [h2, ↓reduceIte]
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hpp]

theorem fixed_word_mem
    (a : C)
    (h : ∀ q ∈ (sylowP : Subgroup AutPerm), permC q a = a) :
    (a : Fin 24 → ZMod 2) = bvec 24 0 ∨ (a : Fin 24 → ZMod 2) = bvec 24 255 ∨
      (a : Fin 24 → ZMod 2) = bvec 24 16776960 ∨ (a : Fin 24 → ZMod 2) = bvec 24 16777215 := by
  have hcount : treeSumN (fun a => if fixOK a = true then 0 else 1) Bmask 12 0 = 0 :=
    fixBad_eq_zero
  have key := CFSG.Monster.B.TwoA.forall_mem_C_of_count
    (P := fun x => (∀ k : Fin 10, permWordArr sylowGens[(k : ℕ)]! x = x) →
      (x = bvec 24 0 ∨ x = bvec 24 255 ∨ x = bvec 24 16776960 ∨ x = bvec 24 16777215))
    fixOK (fun a ha => of_decide_eq_true ha) hcount a.2
  refine key fun k => ?_
  have hk : (k : ℕ) < sylowGenArr.length := by simp [sylowGenArr]
  have harr : PermArr sylowGens[(k : ℕ)]! = true := by
    rw [sylowGens, getElem!_toArray_eq_getD]
    exact sylowGenArr_perm _ (getD_mem_of_lt hk _)
  have hmem : (⟨sylowGen k, sylowGen_mem k⟩ : AutPerm) ∈ (sylowP : Subgroup AutPerm) :=
    mem_sylowP.2 (Subgroup.subset_closure ⟨k, rfl⟩)
  have := congrArg Subtype.val (h _ hmem)
  rw [← permWord_decode harr]
  convert this using 2
  rw [sylowGens, getElem!_toArray_eq_getD]
  rfl

theorem exists_basis_separating : ∀ i j : Fin 24, i ≠ j → ∃ k : Fin 12, B k i ≠ B k j := by
  decide

theorem eq_one_of_forall_permC {p : AutPerm} (h : ∀ b : C, permC p b = b) : p = 1 := by
  refine Subtype.ext (Equiv.ext fun i => ?_)
  by_contra hne
  obtain ⟨k, hk⟩ := exists_basis_separating i ((p : Equiv.Perm (Fin 24)) i) (Ne.symm hne)
  have := congrArg (fun x : C => (x : Fin 24 → ZMod 2) ((p : Equiv.Perm (Fin 24)) i))
    (h ⟨B k, B_mem_C k⟩)
  simp only [coe_permC, permWord_apply] at this
  exact hk this

theorem gO_mul_comm_iff (a b : C) (p : AutPerm) :
    gO b * (gO a * PO p) = (gO a * PO p) * gO b ↔ (permC p).symm b = b := by
  have h1 : gO b * (gO a * PO p) = gO (b + a) * PO p := by rw [← mul_assoc, gO_add']
  have h2 : (gO a * PO p) * gO b = gO (a + (permC p).symm b) * PO p := by
    rw [mul_assoc, PO_mul_gO, ← mul_assoc, gO_add']
  rw [h1, h2, mul_left_inj, gO_injective.eq_iff, add_comm b a, add_right_inj]
  exact eq_comm

theorem PO_mul_gO_eq_iff (q : AutPerm) (a : C) :
    PO q * gO a = gO a * PO q ↔ permC q a = a := by
  rw [PO_mul_gO, mul_left_inj, gO_injective.eq_iff, LinearEquiv.symm_apply_eq, eq_comm]

theorem Ω_eq_bvec : Ω = bvec 24 16777215 := by decide

theorem eq_gO_of_central
    {y : latticeO}
    (hy : y ∈ monoSub (sylowP : Subgroup AutPerm))
    (hc : ∀ s ∈ monoSub (sylowP : Subgroup AutPerm), s * y = y * s) :
    ∃ a : C, y = gO a ∧ ((a : Fin 24 → ZMod 2) = bvec 24 0 ∨
      (a : Fin 24 → ZMod 2) = bvec 24 255 ∨ (a : Fin 24 → ZMod 2) = bvec 24 16776960 ∨
      (a : Fin 24 → ZMod 2) = bvec 24 16777215) := by
  obtain ⟨a, p, hp, rfl⟩ := hy
  have hV : ∀ b : C, (permC p).symm b = b := fun b =>
    (gO_mul_comm_iff a b p).1 (hc (gO b) (gO_mem_monoSub _ b))
  have hp1 : p = 1 := eq_one_of_forall_permC fun b => by
    have := hV b
    rwa [LinearEquiv.symm_apply_eq, eq_comm] at this
  subst hp1
  refine ⟨a, by rw [PO_one, mul_one], fixed_word_mem a fun q hq => ?_⟩
  have := hc (PO q) (PO_mem_monoSub hq)
  rw [PO_one, mul_one] at this
  exact (PO_mul_gO_eq_iff q a).1 this

theorem sqCount_monoSub_ne
    {y : latticeO}
    (hy : y ∈ monoSub (sylowP : Subgroup AutPerm))
    (hc : ∀ s ∈ monoSub (sylowP : Subgroup AutPerm), s * y = y * s) (hy1 : y ≠ 1)
    (hyn : y ≠ negOneO) :
    sqCount (monoSub (sylowP : Subgroup AutPerm)) y ≠
      sqCount (monoSub (sylowP : Subgroup AutPerm)) negOneO := by
  obtain ⟨a, rfl, ha⟩ := eq_gO_of_central hy hc
  have hΩ : sqCount (monoSub (sylowP : Subgroup AutPerm)) negOneO = 6528 := by
    rw [← gO_ΩC, sqCount_monoSub_sylowP ΩC 16777215 Ω_eq_bvec]
    exact sqSum_Ω
  rcases ha with h0 | h255 | h255c | hΩ'
  · exact absurd (by rw [Subtype.ext (h0.trans (bvec_zero 24) : (a : Fin 24 → ZMod 2) = (0 : C)),
      gO_zero]) hy1
  · rw [sqCount_monoSub_sylowP a 255 h255, sqSum_oct, hΩ]
    norm_num
  · rw [sqCount_monoSub_sylowP a 16776960 h255c, sqSum_oct_Ω, hΩ]
    norm_num
  · exact absurd (by rw [Subtype.ext (hΩ'.trans Ω_eq_bvec.symm : (a : Fin 24 → ZMod 2) = ΩC),
      gO_ΩC]) hyn

theorem card_monoSub_sylowP :
    Nat.card (monoSub (sylowP : Subgroup AutPerm)) = 2 ^ 22 := by
  rw [card_monoSub, Sylow.card_eq_multiplicity, factorization_card_AutPerm]
  norm_num

end Sylow

end CFSG.EvenSporadicStandard.TwoCo1
