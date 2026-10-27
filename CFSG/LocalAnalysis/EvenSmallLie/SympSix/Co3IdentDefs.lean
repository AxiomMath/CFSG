module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentData
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3 Subgroup

@[expose] def wordOf {G : Type*} [Group G] (img : Fin 7 → G) (l : List (Fin 7)) : G :=
  (l.map img).prod

@[expose] def pos (l : List (Fin 7)) : List (Fin 7 × Bool) := l.map fun i => (i, true)

@[expose] def neg (l : List (Fin 7)) : List (Fin 7 × Bool) := l.reverse.map fun i => (i, false)

@[expose] def pw (l : List (Fin 7)) (n : ℕ) : List (Fin 7 × Bool) :=
  (List.replicate n (pos l)).flatten

@[expose] def relsC0 : List (List (Fin 7 × Bool)) :=
  [pw [0] 2, pw [1] 2, pw [2] 2, pw [4] 2, pw [5] 2, pw [6] 2,
    pw [0, 2] 2, pw [0, 4] 2, pw [2, 4] 2, pw [4, 6] 2, pw [0, 1] 3,
    pos [5] ++ pw [0, 6] 3, pos [6] ++ pw [1, 5] 3, pw [2, 5, 6] 3, pos [4] ++ pw [0, 1, 2] 3,
    pos [4] ++ pw [0, 2, 6] 4, pw [1, 2, 5, 2, 5] 3, pos [4] ++ pw [0, 1, 2, 5] 7]

@[expose] def edgePairs : List (List (Fin 7) × List (Fin 7)) :=
  [([0], [4]), ([4], [0]), ([2], [2]), ([5], [5]),
    ([1, 0, 5, 1, 6, 0, 6], [0, 1, 0, 6, 0, 1]),
    ([6, 0, 2, 1, 2, 5, 1, 6, 0, 2, 1], [6, 0, 1, 2, 5, 1, 6, 2, 6, 0, 6])]

@[expose] def kpWord : List (Fin 7) := [1, 2, 1, 5, 1, 2, 1, 6, 2, 6, 2, 1, 6, 2, 1, 5]

@[expose] def edgeRel (p : List (Fin 7) × List (Fin 7)) : List (Fin 7 × Bool) :=
  pos ([3] ++ p.1 ++ [3]) ++ neg p.2

@[expose] def planeRel (k : List (Fin 7)) : List (Fin 7 × Bool) := pw [1, 2, 1, 3] 3 ++ neg k

@[expose] def relsV : List (List (Fin 7 × Bool)) :=
  relsC0 ++ [pw [3] 2] ++ edgePairs.map edgeRel ++ [planeRel kpWord]

@[expose] def relsVw : List (List (Fin 7 × Bool)) :=
  relsC0 ++ [pw [3] 2] ++ edgePairs.map edgeRel ++ [planeRel (kpWord ++ [2])]

abbrev V : Type := CFSG.CosetTable.PG 7 relsV

abbrev Vw : Type := CFSG.CosetTable.PG 7 relsVw

section Lift

variable {G : Type*} [Group G] (img : Fin 7 → G)

theorem lift_mk_append (u v : List (Fin 7 × Bool)) :
    FreeGroup.lift img (FreeGroup.mk (u ++ v)) =
      FreeGroup.lift img (FreeGroup.mk u) * FreeGroup.lift img (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

theorem lift_mk_pos (l : List (Fin 7)) :
    FreeGroup.lift img (FreeGroup.mk (pos l)) = wordOf img l := by
  induction l with
  | nil => exact map_one (FreeGroup.lift img)
  | cons i l ih =>
    rw [show pos (i :: l) = [(i, true)] ++ pos l from rfl, lift_mk_append, ih,
      show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
    simp [wordOf]

theorem lift_mk_neg (l : List (Fin 7)) :
    FreeGroup.lift img (FreeGroup.mk (neg l)) = (wordOf img l)⁻¹ := by
  have h : neg l = FreeGroup.invRev (pos l) := by
    simp [neg, pos, FreeGroup.invRev, List.map_reverse, List.map_map, Function.comp_def]
  rw [h, ← FreeGroup.inv_mk, map_inv, lift_mk_pos]

theorem lift_mk_pw (l : List (Fin 7)) (n : ℕ) :
    FreeGroup.lift img (FreeGroup.mk (pw l n)) = wordOf img l ^ n := by
  induction n with
  | zero => exact (map_one (FreeGroup.lift img)).trans (pow_zero _).symm
  | succ n ih =>
    rw [pw, List.replicate_succ, List.flatten_cons, lift_mk_append, ← pw, ih, lift_mk_pos,
      pow_succ']

theorem lift_edgeRel (p : List (Fin 7) × List (Fin 7)) :
    FreeGroup.lift img (FreeGroup.mk (edgeRel p)) = 1 ↔
      img 3 * wordOf img p.1 * img 3 = wordOf img p.2 := by
  rw [edgeRel, lift_mk_append, lift_mk_pos, lift_mk_neg, mul_inv_eq_one]
  simp [wordOf, mul_assoc]

theorem lift_planeRel (k : List (Fin 7)) :
    FreeGroup.lift img (FreeGroup.mk (planeRel k)) = 1 ↔
      (img 1 * img 2 * img 1 * img 3) ^ 3 = wordOf img k := by
  rw [planeRel, lift_mk_append, lift_mk_pw, lift_mk_neg, mul_inv_eq_one]
  simp [wordOf, mul_assoc]

theorem lift_rels_aux (k : List (Fin 7)) :
    (∀ r ∈ relsC0 ++ [pw [3] 2] ++ edgePairs.map edgeRel ++ [planeRel k],
      FreeGroup.lift img (FreeGroup.mk r) = 1) ↔
    (∀ r ∈ relsC0, FreeGroup.lift img (FreeGroup.mk r) = 1) ∧ img 3 * img 3 = 1 ∧
      (∀ p ∈ edgePairs, img 3 * wordOf img p.1 * img 3 = wordOf img p.2) ∧
      (img 1 * img 2 * img 1 * img 3) ^ 3 = wordOf img k := by
  simp only [List.mem_append, List.mem_singleton, List.mem_map]
  constructor
  · intro h
    refine ⟨fun r hr => h r (Or.inl (Or.inl (Or.inl hr))), ?_, fun p hp => ?_, ?_⟩
    · have := h _ (Or.inl (Or.inl (Or.inr rfl)))
      rwa [lift_mk_pw, pow_two, wordOf, List.map_singleton, List.prod_singleton] at this
    · exact (lift_edgeRel img p).1 (h _ (Or.inl (Or.inr ⟨p, hp, rfl⟩)))
    · exact (lift_planeRel img k).1 (h _ (Or.inr rfl))
  · rintro ⟨h0, hs, he, hp⟩ r ((((hr | rfl) | ⟨p, hp', rfl⟩)) | rfl)
    · exact h0 r hr
    · rw [lift_mk_pw, pow_two, wordOf, List.map_singleton, List.prod_singleton, hs]
    · exact (lift_edgeRel img p).2 (he p hp')
    · exact (lift_planeRel img k).2 hp

theorem lift_rels_iff :
    (∀ r ∈ relsV, FreeGroup.lift img (FreeGroup.mk r) = 1) ↔
    (∀ r ∈ relsC0, FreeGroup.lift img (FreeGroup.mk r) = 1) ∧ img 3 * img 3 = 1 ∧
      (∀ p ∈ edgePairs, img 3 * wordOf img p.1 * img 3 = wordOf img p.2) ∧
      (img 1 * img 2 * img 1 * img 3) ^ 3 = wordOf img kpWord :=
  lift_rels_aux img kpWord

theorem lift_relsVw_iff :
    (∀ r ∈ relsVw, FreeGroup.lift img (FreeGroup.mk r) = 1) ↔
    (∀ r ∈ relsC0, FreeGroup.lift img (FreeGroup.mk r) = 1) ∧ img 3 * img 3 = 1 ∧
      (∀ p ∈ edgePairs, img 3 * wordOf img p.1 * img 3 = wordOf img p.2) ∧
      (img 1 * img 2 * img 1 * img 3) ^ 3 = wordOf img kpWord * img 2 := by
  have h := lift_rels_aux img (kpWord ++ [2])
  rw [show wordOf img (kpWord ++ [2]) = wordOf img kpWord * img 2 by simp [wordOf]] at h
  exact h

omit img in
theorem wordOf_map {K : Type*} [Group K] (f : G →* K) (img : Fin 7 → G) (l : List (Fin 7)) :
    wordOf (fun i => f (img i)) l = f (wordOf img l) := by
  simp [wordOf, map_list_prod, List.map_map, Function.comp_def]

omit img in
theorem wordOf_congr {img img' : Fin 7 → G} {l : List (Fin 7)} (h : ∀ i ∈ l, img i = img' i) :
    wordOf img l = wordOf img' l := by
  rw [wordOf, wordOf, List.map_congr_left h]

omit img in
theorem lift_mk_congr {img img' : Fin 7 → G} {r : List (Fin 7 × Bool)}
    (h : ∀ x ∈ r, img x.1 = img' x.1) :
    FreeGroup.lift img (FreeGroup.mk r) = FreeGroup.lift img' (FreeGroup.mk r) := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    rw [show x :: r = [x] ++ r from rfl, lift_mk_append, lift_mk_append,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    obtain ⟨i, b⟩ := x
    have hi := h (i, b) List.mem_cons_self
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv, map_inv,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hi]
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, hi]

theorem relsC0_letters : ∀ r ∈ relsC0, ∀ x ∈ r, x.1 ≠ 3 := by decide

theorem edgePairs_letters : ∀ p ∈ edgePairs, (∀ i ∈ p.1, i ≠ 3) ∧ ∀ i ∈ p.2, i ≠ 3 := by
  decide

theorem kpWord_letters : ∀ i ∈ kpWord, i ≠ 3 := by decide

@[expose] noncomputable def vLift (h : ∀ r ∈ relsV, FreeGroup.lift img (FreeGroup.mk r) = 1) :
    V →* G :=
  PresentedGroup.toGroup (rels := {r | r ∈ relsV.map FreeGroup.mk}) (f := img) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact h w hw)

theorem vLift_of (h : ∀ r ∈ relsV, FreeGroup.lift img (FreeGroup.mk r) = 1) (i : Fin 7) :
    vLift img h (PresentedGroup.of i) = img i := by
  rw [vLift, PresentedGroup.toGroup.of]

@[expose] noncomputable def vwLift
    (h : ∀ r ∈ relsVw, FreeGroup.lift img (FreeGroup.mk r) = 1) : Vw →* G :=
  PresentedGroup.toGroup (rels := {r | r ∈ relsVw.map FreeGroup.mk}) (f := img) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact h w hw)

theorem vwLift_of (h : ∀ r ∈ relsVw, FreeGroup.lift img (FreeGroup.mk r) = 1) (i : Fin 7) :
    vwLift img h (PresentedGroup.of i) = img i := by
  rw [vwLift, PresentedGroup.toGroup.of]

end Lift

@[expose] noncomputable def gp (i : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 (genArr i)

theorem rep_gp {i : ℕ} (hi : i < 7) : Rep 276 (genArr i) (gp i) :=
  (rep_permOfArr (gen_check.1 i hi)).1

theorem gp_four : gp 4 = co3Z := rfl

theorem gp_mem_M
    {i : ℕ} (hi : i ∈ mLetters) : gp i ∈ co3M := by
  have hi7 : i < 7 := by simp [mLetters] at hi; omega
  exact mem_co3M_of_sift (rep_gp hi7) (gen_check.2.1 i hi)

noncomputable abbrev sP : Equiv.Perm (Fin 276) := gp 3

theorem rep_g0
    : Rep 276 (genArr 0) (gp 0) := rep_gp (i := 0) (by norm_num)
theorem rep_g2
    : Rep 276 (genArr 2) (gp 2) := rep_gp (i := 2) (by norm_num)
theorem rep_g3
    : Rep 276 (genArr 3) (gp 3) := rep_gp (i := 3) (by norm_num)
theorem rep_g4
    : Rep 276 (genArr 4) (gp 4) := rep_gp (i := 4) (by norm_num)

theorem sP_mem_P
    : sP ∈ co3P := mem_co3P_of_sift rep_g3 gen_check.2.2.1

theorem sP_mul_self : sP * sP = 1 :=
  eq_of_eqA (rep_compA rep_g3 rep_g3) rep_idA gen_check.2.2.2.1

theorem sP_inv : sP⁻¹ = sP := inv_eq_of_mul_eq_one_right sP_mul_self

theorem sP_conj_z : sP * co3Z * sP = gp 0 := by
  rw [mul_assoc, ← gp_four]
  exact eq_of_eqA (rep_compA rep_g3 (rep_compA rep_g4 rep_g3)) rep_g0 gen_check.2.2.2.2.1

theorem sP_conj_a : sP * gp 0 * sP = co3Z := by
  rw [mul_assoc, ← gp_four]
  exact eq_of_eqA (rep_compA rep_g3 (rep_compA rep_g0 rep_g3)) rep_g4 gen_check.2.2.2.2.2.1

@[expose] noncomputable def mGen
    (i : Fin 7) : co3M :=
  if h : (i : ℕ) ∈ mLetters then ⟨gp i, gp_mem_M h⟩ else 1

theorem coe_mGen
    {i : Fin 7} (h : (i : ℕ) ∈ mLetters) :
    (mGen i : Equiv.Perm (Fin 276)) = gp i := by
  unfold mGen
  split_ifs
  rfl

noncomputable abbrev ma :
    co3M := mGen 0
noncomputable abbrev mb :
    co3M := mGen 1
noncomputable abbrev mc :
    co3M := mGen 2
noncomputable abbrev me :
    co3M := mGen 4
noncomputable abbrev mf :
    co3M := mGen 5
noncomputable abbrev mg :
    co3M := mGen 6

theorem me_eq :
    me = co3ZM := Subtype.ext (coe_mGen (by decide))

@[expose] noncomputable def mWord
    (l : List (Fin 7)) : co3M := wordOf mGen l

theorem wordOf_of_hom
    {G : Type*} [Group G] (f : co3M →* G) {img : Fin 7 → G}
    (himg : ∀ i, i ≠ 3 → img i = f (mGen i)) {l : List (Fin 7)} (hl : ∀ i ∈ l, i ≠ 3) :
    wordOf img l = f (mWord l) := by
  rw [wordOf_congr (img' := fun i => f (mGen i)) fun i hi => himg i (hl i hi), wordOf_map]
  rfl

theorem lift_relsC0_of_hom
    {G : Type*} [Group G] (f : co3M →* G) {img : Fin 7 → G}
    (himg : ∀ i, i ≠ 3 → img i = f (mGen i))
    (hR : ∀ r ∈ relsC0, FreeGroup.lift mGen (FreeGroup.mk r) = 1) :
    ∀ r ∈ relsC0, FreeGroup.lift img (FreeGroup.mk r) = 1 := by
  intro r hr
  rw [lift_mk_congr (img' := fun i => f (mGen i)) fun x hx => himg x.1 (relsC0_letters r hr x hx)]
  have hcomp : FreeGroup.lift (fun i => f (mGen i)) = f.comp (FreeGroup.lift mGen) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  rw [hcomp, MonoidHom.comp_apply, hR r hr, map_one]

noncomputable abbrev bcbM :
    co3M := mb * mc * mb

noncomputable abbrev kpM :
    co3M := mWord kpWord

noncomputable abbrev yM :
    co3M := ma * mc * me

noncomputable abbrev edgeGroup :
    Subgroup co3M := centralizer {ma}

@[expose] def classA :
    Set co3M := {x | IsConj ma x}

theorem me_mem_center :
    me ∈ center co3M := by
  rw [me_eq, co3M_center]
  exact mem_zpowers _

theorem me_comm
    (x : co3M) : x * me = me * x :=
  (mem_center_iff.1 me_mem_center x)

theorem mc_comm_ma :
    mc * ma = ma * mc := by
  apply Subtype.ext
  rw [coe_mul, coe_mul, coe_mGen (by decide), coe_mGen (by decide)]
  exact (eq_of_eqA (rep_compA rep_g0 rep_g2) (rep_compA rep_g2 rep_g0)
    gen_check.2.2.2.2.2.2).symm

theorem ma_mem :
    ma ∈ edgeGroup := mem_centralizer_singleton_iff.2 rfl

theorem me_mem
    : me ∈ edgeGroup := mem_centralizer_singleton_iff.2 (me_comm ma).symm

theorem mc_mem :
    mc ∈ edgeGroup := mem_centralizer_singleton_iff.2 mc_comm_ma

@[expose] noncomputable def aH :
    edgeGroup := ⟨ma, ma_mem⟩
@[expose] noncomputable def eH :
    edgeGroup := ⟨me, me_mem⟩
@[expose] noncomputable def cH :
    edgeGroup := ⟨mc, mc_mem⟩
@[expose] noncomputable def yH :
    edgeGroup := aH * cH * eH

theorem coe_yH :
    (yH : co3M) = yM := rfl

theorem coe_ma
    : ((ma : co3M) : Equiv.Perm (Fin 276)) = gp 0 := coe_mGen (by decide)

theorem coe_me
    : ((me : co3M) : Equiv.Perm (Fin 276)) = co3Z := coe_mGen (by decide)

theorem commute_gp0
    (x : edgeGroup) : Commute ((x : co3M) : Equiv.Perm (Fin 276)) (gp 0) := by
  have h := congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)
  rw [coe_mul, coe_mul, coe_ma] at h
  exact h

theorem commute_z
    (x : co3M) : Commute (x : Equiv.Perm (Fin 276)) co3Z :=
  mem_centralizer_singleton_iff.1 (co3M_le_centralizer x.2)

theorem commute_sP_conj {x u : Equiv.Perm (Fin 276)} (h : Commute x u) :
    Commute (sP * x * sP⁻¹) (sP * u * sP⁻¹) :=
  h.map (MulAut.conj sP).toMonoidHom

theorem sP_conj_z'
    : sP * co3Z * sP⁻¹ = gp 0 := by rw [sP_inv]; exact sP_conj_z

theorem sP_conj_a'
    : sP * gp 0 * sP⁻¹ = co3Z := by rw [sP_inv]; exact sP_conj_a

theorem sP_conj_mem
    (x : edgeGroup) :
    sP * ((x : co3M) : Equiv.Perm (Fin 276)) * sP⁻¹ ∈ co3M := by
  refine co3M_eq_centralizer.symm.le (Subgroup.mem_inf.2 ⟨co3P.mul_mem (co3P.mul_mem sP_mem_P
    (co3M_le_P (x : co3M).2)) (co3P.inv_mem sP_mem_P), mem_centralizer_singleton_iff.2 ?_⟩)
  have h := commute_sP_conj (commute_gp0 x)
  rw [sP_conj_a'] at h
  exact h

@[expose] noncomputable def psiM
    (x : edgeGroup) : co3M := ⟨_, sP_conj_mem x⟩

theorem psiM_mem
    (x : edgeGroup) : psiM x ∈ edgeGroup := by
  rw [mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [coe_mul, coe_mul, coe_ma]
  have h := commute_sP_conj (commute_z (x : co3M))
  rw [sP_conj_z'] at h
  exact h

@[expose] noncomputable def psiFun
    (x : edgeGroup) : edgeGroup := ⟨psiM x, psiM_mem x⟩

theorem coe_psiFun
    (x : edgeGroup) :
    (((psiFun x : edgeGroup) : co3M) : Equiv.Perm (Fin 276)) =
      sP * ((x : co3M) : Equiv.Perm (Fin 276)) * sP⁻¹ := rfl

theorem psiFun_psiFun
    (x : edgeGroup) : psiFun (psiFun x) = x := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_psiFun, coe_psiFun, sP_inv]
  rw [show sP * (sP * ((x : co3M) : Equiv.Perm (Fin 276)) * sP) * sP =
    (sP * sP) * (x : co3M) * (sP * sP) by group, sP_mul_self, one_mul, mul_one]

@[expose] noncomputable def psi :
    MulAut edgeGroup where
  toFun := psiFun
  invFun := psiFun
  left_inv := psiFun_psiFun
  right_inv := psiFun_psiFun
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext
    simp only [coe_psiFun, Subgroup.coe_mul]
    group

theorem coe_psi
    (x : edgeGroup) :
    (((psi x : edgeGroup) : co3M) : Equiv.Perm (Fin 276)) =
      sP * ((x : co3M) : Equiv.Perm (Fin 276)) * sP⁻¹ := rfl

structure ModelFacts :
    Prop where
  relsV_perm : ∀ r ∈ relsV, FreeGroup.lift (fun i : Fin 7 => gp i) (FreeGroup.mk r) = 1
  relsC0_M : ∀ r ∈ relsC0, FreeGroup.lift mGen (FreeGroup.mk r) = 1
  sP_facts : sP ∈ co3P ∧ sP ∉ co3M ∧ sP * sP = 1 ∧ sP * co3Z * sP = gp 0 ∧
    sP * gp 0 * sP = co3Z ∧ sP * gp 2 = gp 2 * sP ∧ sP * gp 5 = gp 5 * sP
  involutions : orderOf ma = 2 ∧ orderOf me = 2 ∧ ma ≠ me
  card_edgeGroup : Nat.card edgeGroup = 4608
  edgeGroup_eq_closure : edgeGroup = closure {x | ∃ p ∈ edgePairs, mWord p.1 = x}
  center_edgeGroup : ∀ x : edgeGroup,
    x ∈ center edgeGroup ↔ x = 1 ∨ x = eH ∨ x = aH ∨ x = eH * aH
  card_centralizer_y : Nat.card (centralizer {yH} : Subgroup edgeGroup) = 128 ∧
    ∀ x : edgeGroup, x * yH = yH * x ↔ x * cH = cH * x
  psi_facts : psi eH = aH ∧ psi aH = eH ∧ psi cH = cH ∧ psi yH = yH ∧
    (∀ x, psi (psi x) = x) ∧
    ∀ p ∈ edgePairs, ∃ x : edgeGroup, (x : co3M) = mWord p.1 ∧ (psi x : co3M) = mWord p.2
  bcb_facts : bcbM * bcbM = 1 ∧ bcbM * ma * bcbM⁻¹ = yM ∧ bcbM * yM * bcbM⁻¹ = ma ∧
    bcbM * mc * bcbM⁻¹ = mc
  kp_facts : kpM ∈ edgeGroup ∧ kpM * yM = yM * kpM ∧ kpM * kpM = 1 ∧ kpM ≠ 1 ∧
    ((bcbM : Equiv.Perm (Fin 276)) * sP) ^ 3 = (kpM : Equiv.Perm (Fin 276))
  classA_facts : Nat.card classA = 630 ∧ me * ma ∈ classA ∧ yM ∈ classA

@[expose] def VCardLe : Prop := Finite V ∧ Nat.card V ≤ 495766656000

@[expose] def VEquivNative : Prop := Nonempty (CFSG.Blueprint.NativeSporadic.Co3 ≃* V)

@[expose] def VwGenerated : Prop :=
  closure ((fun i : Fin 7 => (PresentedGroup.of i : Vw)) '' {i | i ≠ 3}) = ⊤

@[expose] def PlaneTest
    (σ : MulAut edgeGroup) : Prop :=
  ∀ h : edgeGroup, σ (h * yH * h⁻¹) = yH → ∃ k : edgeGroup, k * yH = yH * k ∧
    ∀ x₀ x₁ x₂ : edgeGroup, x₀ * yH = yH * x₀ →
      (x₁ : co3M) = bcbM * σ (h * x₀ * h⁻¹) * bcbM⁻¹ →
      (x₂ : co3M) = bcbM * σ (h * x₁ * h⁻¹) * bcbM⁻¹ →
      bcbM * σ (h * x₂ * h⁻¹) * bcbM⁻¹ = ((k * x₀ * k⁻¹ : edgeGroup) : co3M)

@[expose] def EdgeRigidity :
    Prop :=
  ∀ σ : MulAut edgeGroup, σ eH = aH → σ aH = eH → PlaneTest σ →
    ∃ v : edgeGroup, ∀ x, σ x = v * psi x * v⁻¹

@[expose] def CubeData :
    Prop :=
  (∀ z : edgeGroup, z * yH = yH * z →
    ((∀ x₀ x₁ x₂ : edgeGroup, x₀ * yH = yH * x₀ →
      (x₁ : co3M) = bcbM * psi x₀ * bcbM⁻¹ → (x₂ : co3M) = bcbM * psi x₁ * bcbM⁻¹ →
      bcbM * psi x₂ * bcbM⁻¹ = ((z * x₀ * z⁻¹ : edgeGroup) : co3M)) ∧
      bcbM * psi z * bcbM⁻¹ = z ↔ (z : co3M) = kpM ∨ (z : co3M) = kpM * mc)) ∧
  ∀ z ∈ center edgeGroup, psi z = z ↔ z = 1 ∨ z = eH * aH

end CFSG.EvenSmallLie.SympSix.Co3Ident
