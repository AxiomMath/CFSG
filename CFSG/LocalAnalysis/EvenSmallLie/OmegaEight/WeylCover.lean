module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Cover

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.J2Cover

structure PairFacts : Prop where
  lt : ∀ x < 240, pairArr[x]! < 120
  neg : ∀ x < 240, pairArr[negArr[x]!]! = pairArr[x]!
  inj : ∀ x < 240, ∀ y < 240, pairArr[x]! = pairArr[y]! → y = x ∨ y = negArr[x]!
  sec_lt : ∀ j < 120, pairRepArr[j]! < 240
  sec : ∀ j < 120, pairArr[pairRepArr[j]!]! = j

theorem pair_facts : PairFacts := by
  have h := pair_check
  simp only [pairCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun x hx => (h1 x hx).1, fun x hx => (h1 x hx).2, fun x hx y hy hxy => ?_,
    fun j hj => (h3 j hj).1, fun j hj => (h3 j hj).2⟩
  rcases h2 x hx y hy with (h | h) | h
  · exact absurd hxy h
  · exact Or.inl h
  · exact Or.inr h

@[expose] def pr (x : Fin 240) : Fin 120 := ⟨pairArr[(x : ℕ)]! % 120, Nat.mod_lt _ (by norm_num)⟩

@[expose] def sec (j : Fin 120) : Fin 240 := ⟨pairRepArr[(j : ℕ)]! % 240, Nat.mod_lt _ (by norm_num)⟩

theorem pr_val (x : Fin 240) : (pr x : ℕ) = pairArr[(x : ℕ)]! :=
  Nat.mod_eq_of_lt (pair_facts.lt x x.2)

theorem sec_val (j : Fin 120) : (sec j : ℕ) = pairRepArr[(j : ℕ)]! :=
  Nat.mod_eq_of_lt (pair_facts.sec_lt j j.2)

theorem pr_sec (j : Fin 120) : pr (sec j) = j :=
  Fin.ext (by rw [pr_val, sec_val, pair_facts.sec j j.2])

theorem pr_zPerm (x : Fin 240) : pr (zPerm x) = pr x := by
  apply Fin.ext
  rw [pr_val, pr_val, ← rep_negArr x]
  exact pair_facts.neg x x.2

theorem eq_or_eq_zPerm_of_pr_eq {x y : Fin 240} (h : pr x = pr y) : y = x ∨ y = zPerm x := by
  have h' : pairArr[(x : ℕ)]! = pairArr[(y : ℕ)]! := by rw [← pr_val, ← pr_val, h]
  rcases pair_facts.inj x x.2 y y.2 h' with h1 | h1
  · exact Or.inl (Fin.ext h1)
  · exact Or.inr (Fin.ext (by rw [h1, rep_negArr x]))

theorem pr_apply_sec_pr {g : Equiv.Perm (Fin 240)} (hg : g * zPerm = zPerm * g) (x : Fin 240) :
    pr (g (sec (pr x))) = pr (g x) := by
  rcases eq_or_eq_zPerm_of_pr_eq (pr_sec (pr x)).symm with h | h
  · rw [h]
  · rw [h, ← Equiv.Perm.mul_apply, hg, Equiv.Perm.mul_apply, pr_zPerm]

@[expose] def pFun (g : Equiv.Perm (Fin 240)) (j : Fin 120) : Fin 120 := pr (g (sec j))

theorem pFun_comp {g h : Equiv.Perm (Fin 240)} (hg : g * zPerm = zPerm * g) (j : Fin 120) :
    pFun g (pFun h j) = pFun (g * h) j := by
  rw [pFun, pFun, pFun, pr_apply_sec_pr hg, Equiv.Perm.mul_apply]

theorem pFun_one (j : Fin 120) : pFun 1 j = j := pr_sec j

theorem comm_zPerm_of_mem {g : Equiv.Perm (Fin 240)} (hg : g ∈ wE8) : g * zPerm = zPerm * g :=
  zPerm_comm g hg

@[expose] def pHom : wE8 →* Equiv.Perm (Fin 120) where
  toFun g :=
    { toFun := pFun g
      invFun := pFun (g : Equiv.Perm (Fin 240))⁻¹
      left_inv := fun j => by
        rw [pFun_comp (comm_zPerm_of_mem (inv_mem g.2)), inv_mul_cancel, pFun_one]
      right_inv := fun j => by
        rw [pFun_comp (comm_zPerm_of_mem g.2), mul_inv_cancel, pFun_one] }
  map_one' := Equiv.ext fun j => pFun_one j
  map_mul' g h := Equiv.ext fun j => by
    change pFun ((g : Equiv.Perm (Fin 240)) * h) j = pFun g (pFun h j)
    rw [pFun_comp (comm_zPerm_of_mem g.2)]

theorem pHom_apply (g : wE8) (j : Fin 120) : pHom g j = pr ((g : Equiv.Perm (Fin 240)) (sec j)) :=
  rfl

theorem rep_pArr {t : Array ℕ} {g : wE8} (h : Rep 240 t g) : Rep 120 (pArr t) (pHom g) := by
  intro j
  rw [pArr, getElem!_ofFn_nat _ j.2, pHom_apply, pr_val]
  congr 1
  rw [← sec_val, h (sec j)]

theorem pHom_zPerm : pHom ⟨zPerm, zPerm_mem_wE8⟩ = 1 :=
  Equiv.ext fun j => by rw [pHom_apply, pr_zPerm, pr_sec]; rfl

@[expose] def pPlus : wPlus →* Equiv.Perm (Fin 120) := pHom.comp (inclusion wPlus_le)

theorem pPlus_apply (g : wPlus) : pPlus g = pHom ⟨g, wPlus_le g.2⟩ := rfl

theorem omWords_lt {i : ℕ} (hi : i < 8) : ∀ r ∈ omWords.getD i [], r < 240 := by
  interval_cases i <;> decide

theorem omWords_length {i : ℕ} (hi : i < 8) : (omWords.getD i []).length = 4 := by
  interval_cases i <;> rfl

@[expose] def omLift (i : ℕ) : Equiv.Perm (Fin 240) := wordPerm (omWords.getD i [])

theorem omLift_mem {i : ℕ} (hi : i < 8) : omLift i ∈ wPlus :=
  wordPerm_mem_wPlus (omWords_lt hi) (by rw [omWords_length hi]; decide)

theorem pPlus_omLift {i : ℕ} (hi : i < 8) : pPlus ⟨omLift i, omLift_mem hi⟩ = gen1 i := by
  have h := allLt_spec om_check hi
  exact eq_of_eqA (rep_pArr (g := ⟨omLift i, wPlus_le (omLift_mem hi)⟩)
    (rep_wordArr _ (omWords_lt hi))) (rep_gen1 hi) h

theorem omega1T_le_range_pPlus : omega1T ≤ pPlus.range := by
  rw [omega1T_eq, closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨_, pPlus_omLift hi⟩

@[expose] def zPlus : wPlus := ⟨zPerm, zPerm_mem_wPlus⟩

theorem zPlus_ne_one : zPlus ≠ 1 := fun h => zPerm_ne_one (congrArg Subtype.val h)

theorem zPlus_mem_ker : zPlus ∈ pPlus.ker := by
  rw [MonoidHom.mem_ker, pPlus_apply]
  exact pHom_zPerm

theorem card_ker_mul_card_range : Nat.card pPlus.ker * Nat.card pPlus.range = 348364800 := by
  rw [← card_wPlus, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem two_le_card_ker : 2 ≤ Nat.card pPlus.ker := by
  have hfin : Finite pPlus.ker := inferInstance
  have hpos := Nat.card_pos (α := pPlus.ker)
  by_contra hlt
  have h1 : Nat.card pPlus.ker = 1 := by omega
  have := (Subgroup.card_eq_one).1 h1
  exact zPlus_ne_one (by
    have h := zPlus_mem_ker
    rw [this] at h
    exact h)

theorem range_pPlus : pPlus.range = omega1T := by
  symm
  refine Subgroup.eq_of_le_of_card_ge omega1T_le_range_pPlus ?_
  rw [card_omega1T]
  have h1 := card_ker_mul_card_range
  have h2 := two_le_card_ker
  nlinarith

theorem card_ker_pPlus : Nat.card pPlus.ker = 2 := by
  have h1 := card_ker_mul_card_range
  rw [range_pPlus, card_omega1T] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 174182400) (h1.trans (by norm_num))

theorem mem_ker_pPlus {g : wPlus} : g ∈ pPlus.ker ↔ g = 1 ∨ g = zPlus := by
  constructor
  · intro hg
    by_cases h1 : g = 1
    · exact Or.inl h1
    · exact Or.inr (Cover.eq_of_card_eq_two card_ker_pPlus hg h1 zPlus_mem_ker zPlus_ne_one)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact zPlus_mem_ker

@[expose] def pOnto : wPlus →* omega1T :=
  (MulEquiv.subgroupCongr range_pPlus).toMonoidHom.comp pPlus.rangeRestrict

theorem pOnto_surjective : Function.Surjective pOnto :=
  (MulEquiv.subgroupCongr range_pPlus).surjective.comp pPlus.rangeRestrict_surjective

theorem ker_pOnto : pOnto.ker = pPlus.ker := by
  rw [pOnto, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr range_pPlus).injective,
    MonoidHom.ker_rangeRestrict]

theorem lieModel_omega1T : CFSG.Blueprint.LieModel omega1T .POmegaPlus 4 2 1 :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv omegaRestrictEquiv lieModel_omegaT

theorem zPlus_mem_center : zPlus ∈ center wPlus := by
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (zPerm_comm g (wPlus_le g.2))

theorem ker_pOnto_le_center : pOnto.ker ≤ center wPlus := by
  intro g hg
  rw [ker_pOnto, mem_ker_pPlus] at hg
  rcases hg with rfl | rfl
  · exact one_mem _
  · exact zPlus_mem_center

theorem center_wPlus_eq : center wPlus = pPlus.ker := by
  rw [← ker_pOnto]
  exact Cover.center_eq_ker_of_lieModel lieModel_omega1T pOnto pOnto_surjective
    ker_pOnto_le_center

theorem mem_center_wPlus {x : wPlus} :
    x ∈ center wPlus ↔ (x : Equiv.Perm (Fin 240)) = 1 ∨ (x : Equiv.Perm (Fin 240)) = zPerm := by
  rw [center_wPlus_eq, mem_ker_pPlus]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem card_center_wPlus : Nat.card (center wPlus) = 2 := by
  rw [center_wPlus_eq, card_ker_pPlus]

@[expose] def quotientCenterEquiv : wPlus ⧸ center wPlus ≃* omega1T :=
  (QuotientGroup.quotientMulEquivOfEq (center_wPlus_eq.trans ker_pOnto.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective pOnto pOnto_surjective)

theorem lieModel_wPlus_quotient :
    CFSG.Blueprint.LieModel (wPlus ⧸ center wPlus) .POmegaPlus 4 2 1 :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv quotientCenterEquiv.symm lieModel_omega1T

@[expose] def uArr : Array ℕ := compA 240 (wordArr (omWords.getD 4 [])) (wordArr (omWords.getD 6 []))

@[expose] def yArr : Array ℕ := compA 240 (wordArr (omWords.getD 6 [])) (wordArr (omWords.getD 0 []))

theorem triality_facts : eqA 240 (compA 240 uArr uArr) (idA 240) = true ∧
    eqA 240 (compA 240 yArr yArr) (idA 240) = false ∧
      eqA 240 (compA 240 yArr yArr) negArr = true := by
  have h := triality_check
  simp only [trialityCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] def uPlus : wPlus := ⟨omLift 4 * omLift 6, mul_mem (omLift_mem (by norm_num))
  (omLift_mem (by norm_num))⟩

@[expose] def yPlus : wPlus := ⟨omLift 6 * omLift 0, mul_mem (omLift_mem (by norm_num))
  (omLift_mem (by norm_num))⟩

theorem rep_uArr : Rep 240 uArr (uPlus : Equiv.Perm (Fin 240)) :=
  rep_compA (rep_wordArr _ (omWords_lt (by norm_num))) (rep_wordArr _ (omWords_lt (by norm_num)))

theorem rep_yArr : Rep 240 yArr (yPlus : Equiv.Perm (Fin 240)) :=
  rep_compA (rep_wordArr _ (omWords_lt (by norm_num))) (rep_wordArr _ (omWords_lt (by norm_num)))

theorem uPlus_mul_self : uPlus * uPlus = 1 :=
  Subtype.ext (eq_of_eqA (rep_compA rep_uArr rep_uArr) rep_idA triality_facts.1)

theorem yPlus_mul_self_ne : yPlus * yPlus ≠ 1 := fun h => by
  have h1 := (eqA_iff (rep_compA rep_yArr rep_yArr) rep_idA).2 (congrArg Subtype.val h)
  rw [triality_facts.2.1] at h1
  exact Bool.false_ne_true h1

theorem yPlus_mul_self : yPlus * yPlus = zPlus :=
  Subtype.ext (eq_of_eqA (rep_compA rep_yArr rep_yArr) rep_negArr triality_facts.2.2)

instance isPerfect_omega1T : Group.IsPerfect omega1T :=
  haveI := Cover.isPerfect_omegaT
  Group.IsPerfect.ofSurjective (f := omegaRestrictEquiv.toMonoidHom) omegaRestrictEquiv.surjective

theorem commutator_wPlus : commutator wPlus = ⊤ := by
  set K := commutator wPlus with hK
  have hmap : K.map pPlus = omega1T := by
    rw [hK, _root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_pPlus]
    exact Subgroup.commutator_eq_self
  have hlift : ∀ g : wPlus, ∃ k ∈ K, g = k ∨ g = k * zPlus := by
    intro g
    have hg : pPlus g ∈ K.map pPlus := by
      rw [hmap, ← range_pPlus]
      exact ⟨g, rfl⟩
    obtain ⟨k, hk, hkg⟩ := hg
    have hker : k⁻¹ * g ∈ pPlus.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
    refine ⟨k, hk, ?_⟩
    rcases mem_ker_pPlus.1 hker with h | h
    · exact Or.inl (by rw [← mul_inv_cancel_left k g, h, mul_one])
    · exact Or.inr (by rw [← mul_inv_cancel_left k g, h])
  have hz : zPlus ∈ K := by
    obtain ⟨k, hk, hy⟩ := hlift yPlus
    rw [← yPlus_mul_self]
    rcases hy with hy | hy
    · rw [hy]
      exact mul_mem hk hk
    · have hc : k * zPlus * (k * zPlus) = k * k := by
        have hzc := mem_center_iff.1 zPlus_mem_center k
        have hzz : zPlus * zPlus = 1 := Subtype.ext zPerm_mul_self
        rw [show k * zPlus * (k * zPlus) = k * (zPlus * k) * zPlus by group, ← hzc,
          show k * (k * zPlus) * zPlus = k * k * (zPlus * zPlus) by group, hzz, mul_one]
      rw [hy, hc]
      exact mul_mem hk hk
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, hk, hg | hg⟩ := hlift g
  · rw [hg]
    exact hk
  · rw [hg]
    exact mul_mem hk hz

instance isPerfect_wPlus : Group.IsPerfect wPlus := ⟨commutator_wPlus⟩

@[expose] def ext0Fun (c : Equiv.Perm (Fin 120)) (q : Fin 360) : Fin 360 :=
  if h : (q : ℕ) < 120 then ⟨(c ⟨q, h⟩ : ℕ), by omega⟩ else q

theorem ext0Fun_lt (c : Equiv.Perm (Fin 120)) {q : Fin 360} (hq : (q : ℕ) < 120) :
    ext0Fun c q = ⟨(c ⟨q, hq⟩ : ℕ), by omega⟩ := by
  rw [ext0Fun, dite_eq_left_of_eq_true (eq_true hq)]

theorem ext0Fun_ge (c : Equiv.Perm (Fin 120)) {q : Fin 360} (hq : ¬ (q : ℕ) < 120) :
    ext0Fun c q = q := by
  rw [ext0Fun, dite_eq_right_of_eq_false (eq_false hq)]

theorem ext0Fun_inv (c : Equiv.Perm (Fin 120)) (q : Fin 360) : ext0Fun c⁻¹ (ext0Fun c q) = q := by
  by_cases hq : (q : ℕ) < 120
  · have h2 : ((ext0Fun c q : Fin 360) : ℕ) < 120 := by rw [ext0Fun_lt c hq]; exact (c _).2
    rw [ext0Fun_lt c⁻¹ h2]
    apply Fin.ext
    have hv : ((ext0Fun c q : Fin 360) : ℕ) = (c ⟨q, hq⟩ : ℕ) := by rw [ext0Fun_lt c hq]
    have e : (⟨((ext0Fun c q : Fin 360) : ℕ), h2⟩ : Fin 120) = c ⟨q, hq⟩ := Fin.ext hv
    simp only [e, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  · rw [ext0Fun_ge c hq, ext0Fun_ge c⁻¹ hq]

@[expose] def ext0 (c : Equiv.Perm (Fin 120)) : Equiv.Perm (Fin 360) where
  toFun := ext0Fun c
  invFun := ext0Fun c⁻¹
  left_inv := ext0Fun_inv c
  right_inv q := by
    have := ext0Fun_inv c⁻¹ q
    rwa [inv_inv] at this

theorem eq_one_of_comm_omega1T {c : Equiv.Perm (Fin 120)} (hc : ∀ g ∈ omega1T, c * g = g * c) :
    c = 1 := by
  have hmem : ext0 c ∈ centralizer (omegaT : Set (Equiv.Perm (Fin 360))) := by
    rw [mem_centralizer_iff]
    intro g hg
    ext q
    by_cases hq : (q : ℕ) < 120
    · have hgq : ((g q : Fin 360) : ℕ) < 120 := (omegaT_le_stab0 hg q).1 hq
      have hr := hc (omegaRes ⟨g, hg⟩) (by rw [← omegaRes_range]; exact ⟨⟨g, hg⟩, rfl⟩)
      have hr' : c (omegaRes ⟨g, hg⟩ ⟨q, hq⟩) = omegaRes ⟨g, hg⟩ (c ⟨q, hq⟩) := by
        have := congrArg (fun f : Equiv.Perm (Fin 120) => f ⟨q, hq⟩) hr
        simpa only [Equiv.Perm.mul_apply] using this
      have h1 : (⟨((g q : Fin 360) : ℕ), hgq⟩ : Fin 120) = omegaRes ⟨g, hg⟩ ⟨q, hq⟩ := by
        apply Fin.ext
        rw [omegaRes_apply_val]
      have h2 : ((g (⟨((c ⟨q, hq⟩ : Fin 120) : ℕ), by omega⟩ : Fin 360) : Fin 360) : ℕ) =
          ((omegaRes ⟨g, hg⟩ (c ⟨q, hq⟩) : Fin 120) : ℕ) :=
        (omegaRes_apply_val ⟨g, hg⟩ (c ⟨q, hq⟩)).symm
      change ((g (ext0Fun c q) : Fin 360) : ℕ) = ((ext0Fun c (g q) : Fin 360) : ℕ)
      rw [ext0Fun_lt c hq, ext0Fun_lt c hgq]
      show _ = ((c ⟨(g q : ℕ), hgq⟩ : Fin 120) : ℕ)
      rw [h1, h2, hr']
    · have hgq : ¬ ((g q : Fin 360) : ℕ) < 120 := fun h => hq ((omegaT_le_stab0 hg q).2 h)
      change ((g (ext0Fun c q) : Fin 360) : ℕ) = ((ext0Fun c (g q) : Fin 360) : ℕ)
      rw [ext0Fun_ge c hq, ext0Fun_ge c hgq]
  rw [centralizer_omegaT, mem_bot] at hmem
  ext j
  have h1 := congrArg (fun f : Equiv.Perm (Fin 360) => ((f ⟨j, by omega⟩ : Fin 360) : ℕ)) hmem
  change ((ext0Fun c ⟨j, by omega⟩ : Fin 360) : ℕ) = j at h1
  rw [ext0Fun_lt c (show ((⟨(j : ℕ), by omega⟩ : Fin 360) : ℕ) < 120 from j.2)] at h1
  exact h1

theorem frameRoot_zero : frameRoot 0 = 1 := by decide

theorem sZero_eq_refl : sZero = refl 1 := by rw [sZero, frameRoot_zero]

theorem sZero_mem_wE8 : sZero ∈ wE8 := by
  rw [sZero_eq_refl]
  exact refl_mem (by norm_num)

theorem sZero_not_mem_wPlus : sZero ∉ wPlus := by
  rw [sZero_eq_refl]
  exact refl_not_mem_wPlus (by norm_num)

theorem sZero_mul_self : sZero * sZero = 1 := by
  rw [sZero_eq_refl]
  exact refl_mul_self (by norm_num)

theorem pHom_sZero_not_mem : pHom ⟨sZero, sZero_mem_wE8⟩ ∉ omega1T := by
  intro h
  have hrep : Rep 120 (pArr (reflArr 1)) (pHom ⟨sZero, sZero_mem_wE8⟩) := by
    have := rep_refl (r := 1) (by norm_num)
    rw [← sZero_eq_refl] at this
    exact rep_pArr this
  have hs := (ofArrays_mem_iff (by norm_num) omega1Chain_ok.1 hrep).2 h
  have hc := sZero_check
  rw [sZeroCheck, hs] at hc
  exact Bool.false_ne_true hc

theorem sign_eq_neg_one_of_not_mem {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8) (hwp : w ∉ wPlus) :
    Equiv.Perm.sign w = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h
  · exact absurd (mem_wPlus_iff.2 ⟨hw, h⟩) hwp
  · exact h

theorem centralizer_wPlus {w : Equiv.Perm (Fin 240)} (hw : w ∈ wE8)
    (hc : ∀ x ∈ wPlus, w * x = x * w) : w = 1 ∨ w = zPerm := by
  have hp : pHom ⟨w, hw⟩ = 1 := eq_one_of_comm_omega1T fun g hg => by
    rw [← range_pPlus] at hg
    obtain ⟨x, rfl⟩ := hg
    rw [pPlus_apply, ← map_mul, ← map_mul]
    exact congrArg pHom (Subtype.ext (hc x x.2))
  by_cases hwp : w ∈ wPlus
  · have hk : (⟨w, hwp⟩ : wPlus) ∈ pPlus.ker := hp
    rcases mem_ker_pPlus.1 hk with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · exfalso
    have hws : w * sZero ∈ wPlus := mem_wPlus_iff.2 ⟨mul_mem hw sZero_mem_wE8, by
      rw [map_mul, sign_eq_neg_one_of_not_mem hw hwp, sign_eq_neg_one_of_not_mem sZero_mem_wE8
        sZero_not_mem_wPlus]
      decide⟩
    apply pHom_sZero_not_mem
    have he : pHom ⟨sZero, sZero_mem_wE8⟩ = pPlus ⟨w * sZero, hws⟩ := by
      rw [pPlus_apply]
      change _ = pHom (⟨w, hw⟩ * ⟨sZero, sZero_mem_wE8⟩)
      rw [map_mul, hp, one_mul]
    rw [he, ← range_pPlus]
    exact ⟨_, rfl⟩

theorem commutator_wE8 : ⁅wE8, wE8⁆ = wPlus := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    refine mem_wPlus_iff.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    · rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
  · calc wPlus = ⁅wPlus, wPlus⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅wE8, wE8⁆ := Subgroup.commutator_mono wPlus_le wPlus_le

theorem exists_mulEquiv_wPlus (L : Type) [Group L] (hL : commutator L = ⊤)
    (hZ : Nat.card (center L) = 2)
    (hX : CFSG.Blueprint.LieModel (L ⧸ center L) .POmegaPlus 4 2 1) :
    ∃ θ : L ≃* wPlus, (center L).map θ.toMonoidHom = center wPlus := by
  obtain ⟨θ, hθ⟩ := Cover.omega8plus_double_cover_mulEquiv L hL hZ hX lieModel_omega1T pOnto
    pOnto_surjective ker_pOnto_le_center (by rw [ker_pOnto, card_ker_pPlus])
  exact ⟨θ, hθ.trans (by rw [ker_pOnto, center_wPlus_eq])⟩
