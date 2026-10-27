module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Basic
public import Certificates.Certificate27580

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32
open CFSG.Quasithin (tπ)

theorem closure_subset_of_mul_mem {M : Type*} [Group M] [Finite M] {P S : Set M}
    (h1 : (1 : M) ∈ P) (hmul : ∀ a ∈ P, ∀ b ∈ P, a * b ∈ P) (hS : S ⊆ P) :
    (closure S : Set M) ⊆ P := by
  have hpow : ∀ a ∈ P, ∀ n : ℕ, a ^ n ∈ P := fun a ha n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ ha
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS hx
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x hx y hy
  | inv x _ hx =>
    have hpos := (isOfFinOrder_of_finite x).orderOf_pos
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [e]
    exact hpow x hx _

theorem elemAbelian_closure {M : Type*} [Group M] {k : Set M} (hk : k.Pairwise Commute)
    (h2 : ∀ g ∈ k, g * g = 1) :
    (∀ a ∈ closure k, ∀ b ∈ closure k, a * b = b * a) ∧ ∀ a ∈ closure k, a * a = 1 := by
  have hc := Subgroup.isMulCommutative_closure hk
  have hcomm : ∀ a ∈ closure k, ∀ b ∈ closure k, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨hcomm, fun a ha => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ihx => rw [← mul_inv_rev, ihx, inv_one]

theorem rep_of_eqA {a b : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (h : eqA 1755 a b = true) : Rep 1755 b g := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [← this]
  exact ha x

theorem map_conj_map_conj {M : Type*} [Group M] (X : Subgroup M) (a b : M) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  group

theorem map_conj_one {M : Type*} [Group M] (X : Subgroup M) :
    X.map (MulAut.conj (1 : M)).toMonoidHom = X := by
  ext x
  simp

theorem mem_map_conj_iff {M : Type*} [Group M] {X : Subgroup M} {a y : M} :
    y ∈ X.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * y * a ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group]
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem card_map_conj {M : Type*} [Group M] (X : Subgroup M) (a : M) :
    Nat.card (X.map (MulAut.conj a).toMonoidHom) = Nat.card X :=
  card_map_of_injective (MulAut.conj a).injective

@[expose] noncomputable def hElt (w : List ℕ) : Equiv.Perm (Fin 1755) :=
  (w.map (chainGen titsHArrs)).prod

theorem rep_hElt {w : List ℕ}
    (hw : hLetters w = true) : Rep 1755 (hArr w) (hElt w) ∧ hElt w ∈ titsH := by
  have hl : ∀ i ∈ w, i < 3 := fun i hi => by
    have := List.all_eq_true.1 hw i hi
    simpa using this
  exact ⟨rep_prodArr fun i hi => chainGen_H_rep (hl i hi),
    list_prod_map_mem fun i hi => chainGen_H_mem (hl i hi)⟩

@[expose] noncomputable def eElt (m : ℕ) : Equiv.Perm (Fin 1755) := ((u8Bits m).map parrottV).prod

@[expose] noncomputable def fElt (m : ℕ) : Equiv.Perm (Fin 1755) := ((fBits m).map parrottV).prod

@[expose] noncomputable def parrottF : Subgroup (Equiv.Perm (Fin 1755)) :=
  closure (parrottV '' {7, 9, 10, 11, 12})

theorem u8Bits_bound : ∀ m < 32, ∀ i ∈ u8Bits m, 8 ≤ i ∧ i ≤ 12 := by decide

theorem fBits_bound : ∀ m < 32, ∀ i ∈ fBits m, i ∈ ({7, 9, 10, 11, 12} : Set ℕ) := by
  intro m hm i hi
  have h : ∀ m < 32, ∀ i ∈ fBits m, i = 7 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by decide
  rcases h m hm i hi with rfl | rfl | rfl | rfl | rfl <;> simp

theorem eArrs_getD {m : ℕ} (hm : m < 32) : (eArrs ()).getD m #[] = vProd (u8Bits m) := by
  simp [eArrs, hm]

theorem fArrs_getD {m : ℕ} (hm : m < 32) : (fArrs ()).getD m #[] = vProd (fBits m) := by
  simp [fArrs, hm]

theorem rep_eArrs {m : ℕ}
    (hm : m < 32) : Rep 1755 ((eArrs ()).getD m #[]) (eElt m) := by
  rw [eArrs_getD hm]
  exact rep_vProd fun i hi => by have := u8Bits_bound m hm i hi; omega

theorem rep_fArrs {m : ℕ}
    (hm : m < 32) : Rep 1755 ((fArrs ()).getD m #[]) (fElt m) := by
  rw [fArrs_getD hm]
  refine rep_vProd fun i hi => ?_
  rcases fBits_bound m hm i hi with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem exists_of_mem_eArrs
    {a : Array ℕ} (ha : a ∈ eArrs ()) : ∃ m < 32, Rep 1755 a (eElt m) := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  have hm' := List.mem_range.1 hm
  refine ⟨m, hm', ?_⟩
  have := rep_eArrs hm'
  rwa [eArrs_getD hm'] at this

theorem exists_of_mem_fArrs
    {a : Array ℕ} (ha : a ∈ fArrs ()) : ∃ m < 32, Rep 1755 a (fElt m) := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
  have hm' := List.mem_range.1 hm
  refine ⟨m, hm', ?_⟩
  have := rep_fArrs hm'
  rwa [fArrs_getD hm'] at this

theorem eElt_mem_parrottU {m : ℕ} (hm : m < 32) : eElt m ∈ parrottU 8 :=
  prod_mem_parrottU (u8Bits_bound m hm)

theorem fElt_mem {m : ℕ} (hm : m < 32) : fElt m ∈ parrottF :=
  list_prod_map_mem fun i hi => subset_closure ⟨i, fBits_bound m hm i hi, rfl⟩

theorem eElt_mem
    {m : ℕ} (hm : m < 32) : eElt m ∈ hatE := by
  rw [hatE_eq_parrottU_eight]
  exact eElt_mem_parrottU hm

theorem mem_hatE_iff
    {x : Equiv.Perm (Fin 1755)} : x ∈ hatE ↔ ∃ m < 32, eElt m = x := by
  constructor
  · intro hx
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hsub : (Set.range fun m : Fin 32 => eElt m) ⊆ (hatE : Set _) \ {x} := by
      rintro _ ⟨m, rfl⟩
      exact ⟨eElt_mem m.2, hne m m.2⟩
    have hinj : Function.Injective fun m : Fin 32 => eElt m := by
      intro a b hab
      by_contra hab'
      have h := List.all_eq_true.1 (List.all_eq_true.1 genCheck_parts.2.2.2.2.2 a
        (List.mem_range.2 a.2)) b (List.mem_range.2 b.2)
      have hne' : ((a : ℕ) == (b : ℕ)) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => hab' (Fin.ext h)
      rw [hne', Bool.false_or, Bool.not_eq_true'] at h
      have ra := rep_eArrs a.2
      have rb := rep_eArrs b.2
      rw [eArrs_getD a.2] at ra
      rw [eArrs_getD b.2] at rb
      rw [(eqA_iff ra rb).2 hab] at h
      exact absurd h (by decide)
    have h1 : (Set.range fun m : Fin 32 => eElt m).ncard = 32 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ, Nat.card_fin]
    have hE32 : (hatE : Set (Equiv.Perm (Fin 1755))).ncard = 32 := by
      rw [← Nat.card_coe_set_eq]
      exact card_hatE.2.2.2
    have h2 : ((hatE : Set (Equiv.Perm (Fin 1755))) \ {x}).ncard = 31 := by
      rw [Set.ncard_sdiff_singleton_of_mem hx, hE32]
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · rintro ⟨m, hm, rfl⟩
    exact eElt_mem hm

theorem parrottF_le_titsD :
    parrottF ≤ titsD := by
  rw [parrottF, closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i ≤ 12 ∧ i ∉ ({1, 4, 5, 6} : Finset ℕ) := by
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  exact (parrottV_mem_titsD_iff hi'.1).2 hi'.2

theorem parrottF_elemAbelian :
    (∀ a ∈ parrottF, ∀ b ∈ parrottF, a * b = b * a) ∧ ∀ a ∈ parrottF, a * a = 1 := by
  apply elemAbelian_closure
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ -
    have key : ∀ i ∈ ({7, 9, 10, 11, 12} : Set ℕ), ∀ j ∈ ({7, 9, 10, 11, 12} : Set ℕ),
        1 ≤ i ∧ i ≤ 12 ∧ 1 ≤ j ∧ j ≤ 12 ∧ listed i j = false ∧ listed j i = false := by
      intro i hi j hj
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        decide
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := key i hi j hj
    exact parrottV_commute h1 h2 h3 h4 h5 h6
  · rintro _ ⟨i, hi, rfl⟩
    have hi' : 1 ≤ i ∧ i ≤ 12 ∧ i ∉ ({1, 4, 5, 6} : Finset ℕ) := by
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    exact parrott_squares.2.2.2.2 i hi'.1 hi'.2.1 hi'.2.2

theorem card_parrottF_le
    : Nat.card parrottF ≤ 32 := by
  have h := card_le_of_elemAbelian_titsA (parrottF_le_titsD.trans titsD_le_titsA)
    parrottF_elemAbelian.1 parrottF_elemAbelian.2
  simpa using h.2

theorem inJ_iff {a : Array ℕ}
    {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) : inJ a = true ↔ g ∈ titsJ := by
  rw [← titsQJ_facts.2.2.1]
  exact siftA_iff_mem_ofArrays titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by norm_num : 0 < 4) titsLocalChains_check.2.2.2.1 ha

theorem e32Check_eq_true : e32Check () = true :=
  Certificates.certificate27580

theorem e32Check_parts :
    all5 1755 titsSLevels (fun y => !isInvol y || (sInvs ()).any (eqA 1755 y)) = true ∧
      xkData.all (fun e => (if e.1 then nLetters e.2.2 else hLetters e.2.2) &&
        isInvA 1755 (xkConj e) (invCand 1755 (xkConj e))) = true ∧
      (sInvs ()).all (pivotOK (eArrs ()) (sInvs ())
        (xkData.map (xkSet (eArrs ()) (fArrs ())))) = true := by
  have h := e32Check_eq_true
  unfold e32Check at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem exists_mem_sInvs
    {y : Equiv.Perm (Fin 1755)}
    (hy : y ∈ titsS) (hy2 : y * y = 1) (hy1 : y ≠ 1) : ∃ a ∈ sInvs (), Rep 1755 a y := by
  have hyS : y ∈ titsQS.originalSubgroup := by
    rw [titsQS_facts.2.2.1]
    exact hy
  obtain ⟨a, ha, hp⟩ := all5_spec titsS_chainArrays (by norm_num : 0 < 4)
    titsLocalChains_check.2.1 CFSG.Quasithin.titsQS_baseCount e32Check_parts.1 hyS
  have hinv : isInvol a = true := by
    unfold isInvol
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨(eqA_iff (rep_compA ha ha) rep_idA).2 hy2, ?_⟩
    by_contra h
    rw [Bool.not_eq_false] at h
    exact hy1 ((eqA_iff ha rep_idA).1 h)
  rw [hinv, Bool.not_true, Bool.false_or, List.any_eq_true] at hp
  obtain ⟨b, hb, hab⟩ := hp
  exact ⟨b, hb, rep_of_eqA ha hab⟩

@[expose] noncomputable def xkElt (e : Bool × Bool × List ℕ) : Equiv.Perm (Fin 1755) :=
  if e.1 then (e.2.2.map (chainGen titsNArrs)).prod else hElt e.2.2

theorem xkElt_facts
    {e : Bool × Bool × List ℕ} (he : e ∈ xkData) :
    xkElt e ∈ titsD ∧ Rep 1755 (xkConj e) (xkElt e) ∧
      Rep 1755 (invCand 1755 (xkConj e)) (xkElt e)⁻¹ := by
  have h := List.all_eq_true.1 e32Check_parts.2.1 e he
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, hinv⟩ := h
  have hrep : Rep 1755 (xkConj e) (xkElt e) ∧ xkElt e ∈ titsD := by
    obtain ⟨n, f, w⟩ := e
    unfold xkConj xkElt
    cases n
    · rw [ite_eq_right Bool.false_ne_true] at hw
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨(rep_hElt hw).1, titsH_le_titsD (rep_hElt hw).2⟩
    · rw [ite_eq_left rfl] at hw
      simp only [ite_true]
      exact ⟨rep_nArr hw, titsN_le_titsD (nArr_mem hw)⟩
  exact ⟨hrep.2, hrep.1, rep_inv_of_isInvA hrep.1 hinv⟩

@[expose] noncomputable def xkSub
    (e : Bool × Bool × List ℕ) : Subgroup (Equiv.Perm (Fin 1755)) :=
  (if e.2.1 then parrottF else hatE).map (MulAut.conj (xkElt e)).toMonoidHom

theorem mem_xkSub_of_mem_xkSet
    {e : Bool × Bool × List ℕ} (he : e ∈ xkData) {w : Array ℕ}
    (hw : w ∈ xkSet (eArrs ()) (fArrs ()) e) {y : Equiv.Perm (Fin 1755)}
    (hy : Rep 1755 w y) : y ∈ xkSub e := by
  obtain ⟨-, hc, hci⟩ := xkElt_facts he
  unfold xkSet at hw
  simp only at hw
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
  unfold xkSub
  cases hf : e.2.1
  · rw [hf, ite_eq_right Bool.false_ne_true] at hx
    obtain ⟨m, hm, hxm⟩ := exists_of_mem_eArrs hx
    have hr := rep_compA (rep_compA hc hxm) hci
    rw [Rep.unique hy hr]
    exact ⟨eElt m, eElt_mem hm, by simp [MulAut.conj_apply]⟩
  · rw [hf, ite_eq_left rfl] at hx
    obtain ⟨m, hm, hxm⟩ := exists_of_mem_fArrs hx
    have hr := rep_compA (rep_compA hc hxm) hci
    rw [Rep.unique hy hr]
    exact ⟨fElt m, fElt_mem hm, by simp [MulAut.conj_apply]⟩

theorem card_xkSub_le
    (e : Bool × Bool × List ℕ) : Nat.card (xkSub e) ≤ 32 := by
  unfold xkSub
  rw [card_map_conj]
  cases e.2.1
  · simp only [Bool.false_eq_true, ite_false]
    rw [card_hatE.2.2.2]
  · simpa using card_parrottF_le

theorem exists_eq_conj_of_le_titsS
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXS : X ≤ titsS)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1) (h32 : Nat.card X = 32) :
    ∃ c ∈ titsD, X = hatE.map (MulAut.conj c).toMonoidHom ∨
      X = parrottF.map (MulAut.conj c).toMonoidHom := by
  by_cases hE : X ≤ hatE
  · refine ⟨1, one_mem _, Or.inl ?_⟩
    rw [map_conj_one]
    exact eq_of_le_of_card_ge hE (by rw [card_hatE.2.2.2, h32])
  obtain ⟨x, hxX, hxE, hJ⟩ : ∃ x ∈ X, x ∉ hatE ∧ (x ∈ titsJ → X ≤ titsJ) := by
    by_cases hXJ : X ≤ titsJ
    · obtain ⟨x, hx, hxE⟩ := Set.not_subset.1 hE
      exact ⟨x, hx, hxE, fun _ => hXJ⟩
    · obtain ⟨x, hx, hxJ⟩ := Set.not_subset.1 hXJ
      exact ⟨x, hx, fun h => hxJ (hatE_le_titsJ h), fun h => absurd h hxJ⟩
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ one_mem _)
  obtain ⟨a, haS, ha⟩ := exists_mem_sInvs (hXS hxX) (h2 x hxX) hx1
  have hpiv := List.all_eq_true.1 e32Check_parts.2.2 a haS
  unfold pivotOK at hpiv
  have hnE : (eArrs ()).any (eqA 1755 a) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨b, hb, hab⟩ := List.any_eq_true.1 h
    obtain ⟨m, hm, hbm⟩ := exists_of_mem_eArrs hb
    exact hxE (by rw [(eqA_iff ha hbm).1 hab]; exact eElt_mem hm)
  rw [hnE, Bool.false_or] at hpiv
  simp only at hpiv
  obtain ⟨xs, hxs, hall⟩ := List.any_eq_true.1 hpiv
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxs
  have hle : X ≤ xkSub e := by
    intro y hyX
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    obtain ⟨b, hbS, hb⟩ := exists_mem_sInvs (hXS hyX) (h2 y hyX) hy1
    have hbom : b ∈ (sInvs ()).filter fun b => commA a b && (!inJ a || inJ b) := by
      refine List.mem_filter.2 ⟨hbS, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨(eqA_iff (rep_compA ha hb) (rep_compA hb ha)).2 (hc x hxX y hyX), ?_⟩
      cases hja : inJ a
      · rfl
      · have hyJ := hJ ((inJ_iff ha).1 hja) hyX
        rw [(inJ_iff hb).2 hyJ]
        rfl
    obtain ⟨w, hw, hbw⟩ := List.any_eq_true.1 (List.all_eq_true.1 hall b hbom)
    exact mem_xkSub_of_mem_xkSet he hw (rep_of_eqA hb hbw)
  have heq : X = xkSub e := eq_of_le_of_card_ge hle (by rw [h32]; exact card_xkSub_le e)
  refine ⟨xkElt e, (xkElt_facts he).1, ?_⟩
  rw [heq]
  unfold xkSub
  cases e.2.1
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_map_conj_le_titsS
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXD : X ≤ titsD) (hp : IsPGroup 2 X) :
    ∃ d ∈ titsD, X.map (MulAut.conj d).toMonoidHom ≤ titsS := by
  obtain ⟨⟨P, hP⟩, -⟩ := AT_Tits_intrinsic_local_pair
  have hp' : IsPGroup 2 (X.subgroupOf titsD) :=
    hp.of_equiv (subgroupOfEquivOfLe hXD).symm
  obtain ⟨Q, hQ⟩ := hp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsD Q P
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : (⟨x, hXD hx⟩ : titsD) ∈ (Q : Subgroup titsD) := hQ (mem_subgroupOf.2 hx)
  have hmem : g * ⟨x, hXD hx⟩ * g⁻¹ ∈ (P : Subgroup titsD) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hxQ
  rw [hP, mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem exists_eq_conj_of_elemAbelian
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXA : X ≤ titsA)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1) (h32 : Nat.card X = 32) :
    ∃ d ∈ titsD, X = hatE.map (MulAut.conj d).toMonoidHom ∨
      X = parrottF.map (MulAut.conj d).toMonoidHom := by
  have hXD := (card_le_of_elemAbelian_titsA hXA hc h2).1
  have hp : IsPGroup 2 X := IsPGroup.of_card (n := 5) (by rw [h32]; norm_num)
  obtain ⟨d₀, hd₀, hle⟩ := exists_map_conj_le_titsS hXD hp
  set Y := X.map (MulAut.conj d₀).toMonoidHom with hY
  have hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show d₀ * a * d₀⁻¹ * (d₀ * b * d₀⁻¹) = d₀ * (a * b) * d₀⁻¹ by group, hc a ha b hb]
    group
  have hY2 : ∀ a ∈ Y, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show d₀ * a * d₀⁻¹ * (d₀ * a * d₀⁻¹) = d₀ * (a * a) * d₀⁻¹ by group, h2 a ha]
    group
  obtain ⟨c, hcD, hYc'⟩ := exists_eq_conj_of_le_titsS hle hYc hY2
    (by rw [hY, card_map_conj, h32])
  have hX : X = Y.map (MulAut.conj d₀⁻¹).toMonoidHom := by
    rw [hY, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  refine ⟨d₀⁻¹ * c, mul_mem (inv_mem hd₀) hcD, ?_⟩
  rcases hYc' with h | h
  · left
    rw [hX, h, map_conj_map_conj]
  · right
    rw [hX, h, map_conj_map_conj]

end CFSG.LocalAnalysis.EvenBN.Tits.Model
