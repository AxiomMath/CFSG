module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzChecks
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuPi7Equiv
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmDefs
public import CFSG.Certificates.CosetTableColumns
public import CFSG.Sporadic.SuzOddCore.Text

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.SuzOddCore

theorem wordProd_congr {G : Type*} [Group G] {x y : ℕ → G} {w : List (ℕ × Bool)}
    (h : ∀ l ∈ w, x l.1 = y l.1) : wordProd x w = wordProd y w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'), h l List.mem_cons_self]

theorem wordProd_append {G : Type*} [Group G] (x : ℕ → G) (v w : List (ℕ × Bool)) :
    wordProd x (v ++ w) = wordProd x v * wordProd x w := by
  simp only [wordProd, List.map_append, List.prod_append]

theorem wordProd_cons {G : Type*} [Group G] (x : ℕ → G) (l : ℕ × Bool) (w : List (ℕ × Bool)) :
    wordProd x (l :: w) = (if l.2 then x l.1 else (x l.1)⁻¹) * wordProd x w := by
  simp only [wordProd, List.map_cons, List.prod_cons]

theorem wordProd_invNatWord {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    wordProd x (invNatWord w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [invNatWord, wordProd]
  | cons l w ih =>
    unfold invNatWord at ih ⊢
    rw [List.map_cons, List.reverse_cons, wordProd_append, ih, wordProd_cons, wordProd_cons,
      mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [wordProd]

theorem wordProd_substWord {G : Type*} [Group G] (x : ℕ → G) (r : List (ℕ × Bool)) :
    wordProd x (substWord r) = wordProd (fun i => wordProd x (l10Word i)) r := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    unfold substWord at ih ⊢
    rw [List.flatMap_cons, wordProd_append, ih, wordProd_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact wordProd_invNatWord x _
    · simp only [↓reduceIte]

abbrev Pi0 : Type := PG 10 czRels

abbrev P12 : Type := PG sub9.length p12Rels

theorem card_le_of_presented {m : ℕ} {ws : List (List (Fin m × Bool))} {n : ℕ}
    (hP : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n) {G : Type*} [Group G] (x : Fin m → G)
    (hrel : ∀ r ∈ ws, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) : Nat.card G ≤ n := by
  have := hP.1
  let φ : PG m ws →* G := PresentedGroup.toGroup (f := x) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact hrel w hw
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  exact (Nat.card_le_card_of_surjective φ hsurj).trans hP.2

theorem card_p12_le : Finite P12 ∧ Nat.card P12 ≤ 49152 :=
  cz_card_p12

theorem card_pi0_le : Finite Pi0 ∧ Nat.card Pi0 ≤ 245760 := by
  obtain ⟨hfin, hcard⟩ := card_p12_le
  obtain ⟨hfi, hix⟩ := cz_sub_index
  obtain ⟨h1, h2⟩ := card_le_of_genSub_index czRels sub9 hfi hix
  have hcard' : Nat.card (PG sub9.length (restrictWords sub9 czRels)) ≤ 49152 := hcard
  exact ⟨h1, h2.trans (by omega)⟩

theorem card_le_of_eps1 {G : Type*} [Group G] (x : Fin 10 → G)
    (hrel : ∀ r ∈ czEps1Rels, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) : Nat.card G ≤ 122880 :=
  card_le_of_presented card_eps1_le x hrel hgen

theorem card_le_of_eps2 {G : Type*} [Group G] (x : Fin 10 → G)
    (hrel : ∀ r ∈ czEps2Rels, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) : Nat.card G ≤ 122880 :=
  card_le_of_presented card_eps2_le x hrel hgen

theorem card_le_of_eps3 {G : Type*} [Group G] (x : Fin 10 → G)
    (hrel : ∀ r ∈ czEps3Rels, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) : Nat.card G ≤ 122880 :=
  card_le_of_presented card_eps3_le x hrel hgen

theorem czRu_eval :
    ∀ v ∈ czRuRels, wordProd pi7Img v = 1 :=
  fun v hv => (cz_ru v hv).2

@[expose] noncomputable def pi7L (i : ℕ) : Pi7 := if h : i < 7 then PresentedGroup.of ⟨i, h⟩ else 1

theorem pi7L_of_lt {i : ℕ} (hi : i < 7) : pi7L i = PresentedGroup.of ⟨i, hi⟩ := by
  unfold pi7L
  simp only [hi, ↓reduceDIte]

theorem pi7ToJ_pi7L {i : ℕ}
    (hi : i < 7) : pi7ToJ (pi7L i) = pi7Img i := by
  rw [pi7L_of_lt hi]
  exact pi7ToJ_of _

theorem czRu_eq_one
    {v : List (ℕ × Bool)}
    (hv : v ∈ czRuRels) : wordProd pi7L v = 1 := by
  refine pi7ToJ_bijective.1 ?_
  rw [map_one, map_wordProd, wordProd_congr (y := pi7Img) fun l hl =>
    pi7ToJ_pi7L ((cz_ru v hv).1 l hl)]
  exact czRu_eval v hv

@[expose] noncomputable def czImg (i : ℕ) : Pi7 := wordProd pi7L (l10Word i)

@[expose] noncomputable def pi0ToPi7 :
    Pi0 →* Pi7 :=
  PresentedGroup.toGroup (f := fun i : Fin 10 => czImg i.val) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk_eq_wordProd]
    show wordProd (fun i => wordProd pi7L (l10Word i)) _ = 1
    rw [← wordProd_substWord]
    exact czRu_eq_one (List.mem_append_left _ (List.mem_map_of_mem hw))

theorem pi0ToPi7_of
    (i : Fin 10) :
    pi0ToPi7 (PresentedGroup.of i) = czImg i.val :=
  PresentedGroup.toGroup.of _

@[expose] noncomputable def pi0Gen (i : ℕ) : Pi0 :=
  if h : i < 10 then PresentedGroup.of ⟨i, h⟩ else 1

theorem pi0ToPi7_wordProd
    {v : List (ℕ × Bool)}
    (hv : ∀ l ∈ v, l.1 < 10) : pi0ToPi7 (wordProd pi0Gen v) = wordProd czImg v := by
  rw [map_wordProd]
  refine wordProd_congr fun l hl => ?_
  unfold pi0Gen
  simp only [hv l hl, ↓reduceDIte]
  exact pi0ToPi7_of _

theorem pi7L_eq
    {j : ℕ} (hj : j < 6) :
    pi7L j = wordProd czImg (natWord (czL6Codes.getD j [])) := by
  have h := czRu_eq_one (v := (j, false) :: substWord (natWord (czL6Codes.getD j [])))
    (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
  rw [wordProd_cons, wordProd_substWord] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact (inv_mul_eq_one.1 h)

theorem l10Word_lt : ∀ i < 10, ∀ l ∈ l10Word i, l.1 < 6 := by decide

theorem l10Word_lt5 : ∀ i < 9, ∀ l ∈ l10Word i, l.1 < 5 := by decide

theorem l6Word_lt : ∀ j < 6, ∀ l ∈ natWord (czL6Codes.getD j []), l.1 < 10 := by decide

theorem l6Word_lt9 : ∀ j < 5, ∀ l ∈ natWord (czL6Codes.getD j []), l.1 < 9 := by decide

theorem pi7L_mem_letterSub {l : List (Fin 7)} {i : ℕ} (hi : i < 7) (hl : ⟨i, hi⟩ ∈ l) :
    pi7L i ∈ letterSub l := by
  rw [pi7L_of_lt hi]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, hl, rfl⟩

theorem wordProd_mem_letterSub {l : List (Fin 7)} {w : List (ℕ × Bool)}
    (hw : ∀ e ∈ w, ∃ h : e.1 < 7, (⟨e.1, h⟩ : Fin 7) ∈ l) : wordProd pi7L w ∈ letterSub l := by
  induction w with
  | nil => exact (letterSub l).one_mem
  | cons e w ih =>
    rw [wordProd_cons]
    refine (letterSub l).mul_mem ?_ (ih fun e' he' => hw e' (List.mem_cons_of_mem _ he'))
    obtain ⟨h, hl⟩ := hw e List.mem_cons_self
    split
    · exact pi7L_mem_letterSub h hl
    · exact (letterSub l).inv_mem (pi7L_mem_letterSub h hl)

theorem czImg_mem_ruM1 {i : ℕ} (hi : i < 10) : czImg i ∈ ruM1 := by
  refine wordProd_mem_letterSub fun e he => ⟨by have := l10Word_lt i hi e he; omega, ?_⟩
  have := l10Word_lt i hi e he
  simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  omega

theorem czImg_mem_ruM12 {i : ℕ} (hi : i < 9) : czImg i ∈ ruM12 := by
  refine wordProd_mem_letterSub fun e he => ⟨by have := l10Word_lt5 i hi e he; omega, ?_⟩
  have := l10Word_lt5 i hi e he
  simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  omega

theorem range_pi0ToPi7 :
    pi0ToPi7.range = ruM1 := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [pi0ToPi7_of]
    exact czImg_mem_ruM1 i.2
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj6 : j.val < 6 := by
      simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨wordProd pi0Gen (natWord (czL6Codes.getD j.val [])), ?_⟩
    rw [pi0ToPi7_wordProd (l6Word_lt j.val hj6), ← pi7L_eq hj6, pi7L_of_lt j.2]

theorem ruM1_genSub :
    ruM1 = genSub {r : FreeGroup (Fin 7) | r ∈ pi7Rels.map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4, 5]) := by
  have h : {i : Fin 7 | i ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))} =
      {x | x ∈ subsetOf 7 [0, 1, 2, 3, 4, 5]} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    revert x
    decide
  rw [ruM1, letterSub, h]

theorem card_ruM1 :
    Nat.card ruM1 = 245760 := by
  have hfin : Finite Pi7 := card_pi7_le.1
  have hP : Nat.card Pi7 = 145926144000 :=
    (Nat.card_congr pi7EquivJ.toEquiv).trans CFSG.Sporadic.Bridge.Ru.card_J
  have hle : Nat.card ruM1 ≤ 245760 := by
    have := card_pi0_le.1
    rw [← range_pi0ToPi7]
    exact (Nat.card_le_card_of_surjective _ pi0ToPi7.rangeRestrict_surjective).trans
      card_pi0_le.2
  have hix : ruM1.index ≤ 593775 := by
    rw [ruM1_genSub]
    exact cz_m1_index.2
  have hmul : Nat.card ruM1 * ruM1.index = 145926144000 := by rw [Subgroup.card_mul_index, hP]
  have hge : 245760 ≤ Nat.card ruM1 := by
    by_contra h
    have h1 : Nat.card ruM1 * ruM1.index ≤ 245759 * 593775 :=
      Nat.mul_le_mul (by omega) hix
    omega
  omega

@[expose] noncomputable def pi0ToM1 :
    Pi0 →* ruM1 :=
  pi0ToPi7.codRestrict ruM1 fun x => range_pi0ToPi7 ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩

theorem pi0ToM1_bijective :
    Function.Bijective pi0ToM1 := by
  have := card_pi0_le.1
  have hs : Function.Surjective pi0ToM1 := by
    rintro ⟨y, hy⟩
    rw [← range_pi0ToPi7] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  exact hs.bijective_of_nat_card_le (card_pi0_le.2.trans card_ruM1.ge)

@[expose] noncomputable def pi0Equiv :
    Pi0 ≃* ruM1 :=
  MulEquiv.ofBijective pi0ToM1 pi0ToM1_bijective

theorem pi0Equiv_of
    (i : Fin 10) :
    ((pi0Equiv (PresentedGroup.of i) : ruM1) : Pi7) = czImg i.val :=
  pi0ToPi7_of i

theorem p12_rel (r : FreeGroup (Fin sub9.length))
    (hr : r ∈ {r : FreeGroup (Fin sub9.length) | r ∈ p12Rels.map FreeGroup.mk}) :
    FreeGroup.lift (fun j => (PresentedGroup.of (sub9.get j) : Pi0)) r = 1 := by
  simp only [Set.mem_ofPred_eq, List.mem_map, restrictWords, List.mem_filterMap] at hr
  obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
  have hmap : FreeGroup.lift (fun j => (PresentedGroup.of (sub9.get j) : Pi0))
      (FreeGroup.mk w') = PresentedGroup.mk _ (FreeGroup.mk w) := by
    rw [← map_renumber sub9 w w' hren]
    clear hren hw
    induction w' with
    | nil => rfl
    | cons l w' ih =>
      rw [show FreeGroup.mk (l :: w') = FreeGroup.mk [l] * FreeGroup.mk w' from rfl, map_mul,
        ih, List.map_cons, show FreeGroup.mk ((sub9.get l.1, l.2) :: List.map
          (fun l => (sub9.get l.1, l.2)) w') = FreeGroup.mk [(sub9.get l.1, l.2)] *
          FreeGroup.mk (List.map (fun l => (sub9.get l.1, l.2)) w') from rfl, map_mul]
      congr 1
      obtain ⟨j, b⟩ := l
      cases b
      · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv,
          FreeGroup.lift_apply_of]
        rfl
      · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl, FreeGroup.lift_apply_of]
        rfl
  rw [hmap]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

@[expose] noncomputable def p12ToPi0 : P12 →* Pi0 := PresentedGroup.toGroup p12_rel

theorem sub9_get (j : Fin sub9.length) : (sub9.get j).val = j.val := by
  revert j
  decide

theorem sub9_length : sub9.length = 9 := by decide

@[expose] noncomputable def p12ToPi7 :
    P12 →* Pi7 :=
  pi0ToPi7.comp p12ToPi0

theorem p12ToPi7_of
    (j : Fin sub9.length) :
    p12ToPi7 (PresentedGroup.of j) = czImg j.val := by
  rw [p12ToPi7, MonoidHom.comp_apply, p12ToPi0, PresentedGroup.toGroup.of, pi0ToPi7_of, sub9_get]

@[expose] noncomputable def p12Gen (i : ℕ) : P12 :=
  if h : i < 9 then PresentedGroup.of ⟨i, sub9_length ▸ h⟩ else 1

theorem range_p12ToPi7 :
    p12ToPi7.range = ruM12 := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [p12ToPi7_of]
    exact czImg_mem_ruM12 (lt_of_lt_of_eq j.2 sub9_length)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj5 : j.val < 5 := by
      simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    refine ⟨wordProd p12Gen (natWord (czL6Codes.getD j.val [])), ?_⟩
    rw [map_wordProd, wordProd_congr (y := czImg) fun l hl => ?_, ← pi7L_eq (by omega)]
    · rw [pi7L_of_lt j.2]
    · have := l6Word_lt9 j.val hj5 l hl
      unfold p12Gen
      simp only [this, ↓reduceDIte]
      exact p12ToPi7_of _

theorem pi0_sub_index_le :
    (genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9).index ≤ 5 :=
  cz_sub_index

theorem card_ruM12 :
    Nat.card ruM12 = 49152 := by
  set K := genSub {r : FreeGroup (Fin 10) | r ∈ czRels.map FreeGroup.mk} sub9
  have hK : K.map pi0ToPi7 = ruM12 := by
    rw [← range_p12ToPi7, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of,
      MonoidHom.map_closure, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨j, hj⟩ := List.get_of_mem hx
      exact ⟨_, ⟨j, rfl⟩, by rw [p12ToPi7_of, pi0ToPi7_of, ← hj, sub9_get]⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨_, ⟨sub9.get j, List.get_mem _ _, rfl⟩, by rw [p12ToPi7_of, pi0ToPi7_of, sub9_get]⟩
  have hinj : Function.Injective pi0ToPi7 := fun a b h =>
    pi0ToM1_bijective.1 (Subtype.ext h)
  have hcardK : Nat.card (K.map pi0ToPi7) = Nat.card K :=
    Subgroup.card_map_of_injective hinj
  have hfin := card_pi0_le.1
  have hidx := pi0_sub_index_le
  have hmul := K.index_mul_card
  have hpi0 : Nat.card Pi0 = 245760 := by
    rw [← card_ruM1]
    exact Nat.card_congr pi0Equiv.toEquiv
  rw [hpi0] at hmul
  have hle : Nat.card ruM12 ≤ 49152 := by
    have := card_p12_le.1
    rw [← range_p12ToPi7]
    exact (Nat.card_le_card_of_surjective _ p12ToPi7.rangeRestrict_surjective).trans card_p12_le.2
  rw [← hK, hcardK] at hle ⊢
  rcases Nat.lt_or_ge (Nat.card K) 49152 with h | h
  · exfalso
    have : K.index * Nat.card K ≤ 5 * 49151 := Nat.mul_le_mul hidx.2 (by omega)
    omega
  · omega

@[expose] noncomputable def p12ToM12 :
    P12 →* ruM12 :=
  p12ToPi7.codRestrict ruM12 fun x => range_p12ToPi7 ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩

@[expose] noncomputable def p12Equiv :
    P12 ≃* ruM12 :=
  MulEquiv.ofBijective p12ToM12 (by
    have := card_p12_le.1
    have hs : Function.Surjective p12ToM12 := by
      rintro ⟨y, hy⟩
      rw [← range_p12ToPi7] at hy
      obtain ⟨x, rfl⟩ := hy
      exact ⟨x, rfl⟩
    exact hs.bijective_of_nat_card_le (card_p12_le.2.trans card_ruM12.ge))

theorem p12Equiv_of
    (j : Fin sub9.length) :
    ((p12Equiv (PresentedGroup.of j) : ruM12) : Pi7) = czImg j.val :=
  p12ToPi7_of j

end CFSG.ComponentClassification.GMS78.RuCz
