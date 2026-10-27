module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Orbits
public import Certificates.Certificate535001

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32
open CFSG.Quasithin (tπ twoF4H twoF4N)


theorem e32NormCheck_eq_true : e32NormCheck () = true :=
  Certificates.certificate535001

theorem e32NormCheck_parts :
    xkData.all (fun e => !e.2.1 || (e.2.2 == [] && !e.1) ||
      decide (interCount (xkSet (eArrs ()) (fArrs ()) e) (fArrs ()) ≤ 8)) = true ∧
    memL (eArrs ()) (vA 7) = false ∧
    memL (xkSet (eArrs ()) (fArrs ()) (xkData.getD 4 (false, false, []))) (vA 2) = true ∧
    interCount (xkSet (eArrs ()) (fArrs ()) (xkData.getD 4 (false, false, [])))
      (eArrs ()) ≤ 8 ∧
    (xkSet (eArrs ()) (fArrs ()) (xkData.getD 4 (false, false, []))).all
      (fun x => (List.range 5).all fun i =>
        memL (eArrs ()) (compA 1755 (compA 1755 x (vA (8 + i))) x)) = true := by
  have h := e32NormCheck_eq_true
  unfold e32NormCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem card_inf_le_interCount {X Y : Subgroup (Equiv.Perm (Fin 1755))} {Xl Yl : List (Array ℕ)}
    (hX : ∀ x ∈ X, ∃ a ∈ Xl, Rep 1755 a x) (hY : ∀ y ∈ Y, ∃ b ∈ Yl, Rep 1755 b y) :
    Nat.card ↥(X ⊓ Y) ≤ interCount Xl Yl := by
  classical
  choose f hfmem hfrep using fun x : ↥(X ⊓ Y) => hX x.1 x.2.1
  have hfilt : ∀ x : ↥(X ⊓ Y), f x ∈ Xl.filter (memL Yl) := by
    intro x
    obtain ⟨b, hb, hbrep⟩ := hY x.1 x.2.2
    refine List.mem_filter.2 ⟨hfmem x, ?_⟩
    unfold memL
    rw [List.any_eq_true]
    exact ⟨b, hb, (eqA_iff (hfrep x) hbrep).2 rfl⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h1 := hfrep x
    rw [hxy] at h1
    exact h1.unique (hfrep y)
  let g : ↥(X ⊓ Y) → ↥((Xl.filter (memL Yl)).toFinset) :=
    fun x => ⟨f x, List.mem_toFinset.2 (hfilt x)⟩
  have hg : Function.Injective g := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have h1 := Nat.card_le_card_of_injective g hg
  rw [Nat.card_eq_finsetCard] at h1
  exact h1.trans (List.toFinset_card_le _)

theorem exists_rep_of_mem_xkSub {e : Bool × Bool × List ℕ} (he : e ∈ xkData)
    {x : Equiv.Perm (Fin 1755)} (hx : x ∈ xkSub e) :
    ∃ a ∈ xkSet (eArrs ()) (fArrs ()) e, Rep 1755 a x := by
  obtain ⟨-, hc, hci⟩ := xkElt_facts he
  unfold xkSub at hx
  cases hf : e.2.1
  · rw [hf, ite_eq_right Bool.false_ne_true] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 hy
    refine ⟨compA 1755 (compA 1755 (xkConj e) ((eArrs ()).getD m #[])) (invCand 1755 (xkConj e)), ?_,
      by simpa [MulAut.conj_apply] using rep_compA (rep_compA hc (rep_eArrs hm)) hci⟩
    unfold xkSet
    simp only [hf]
    exact List.mem_map.2 ⟨_, getD_mem_of_lt (by simp [eArrs, hm]), rfl⟩
  · rw [hf, ite_eq_left rfl] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨m, hm, rfl⟩ := (mem_parrottF_iff).1 hy
    refine ⟨compA 1755 (compA 1755 (xkConj e) ((fArrs ()).getD m #[])) (invCand 1755 (xkConj e)), ?_,
      by simpa [MulAut.conj_apply] using rep_compA (rep_compA hc (rep_fArrs hm)) hci⟩
    unfold xkSet
    simp only [hf]
    exact List.mem_map.2 ⟨_, getD_mem_of_lt (by simp [fArrs, hm]), rfl⟩

theorem parrottV_seven_mem_parrottF : parrottV 7 ∈ parrottF :=
  subset_closure ⟨7, by simp, rfl⟩

theorem parrottV_seven_not_mem_hatE : parrottV 7 ∉ hatE := by
  intro h
  obtain ⟨m, hm, hmx⟩ := mem_hatE_iff.1 h
  have h2 := e32NormCheck_parts.2.1
  unfold memL at h2
  rw [Bool.eq_false_iff] at h2
  apply h2
  rw [List.any_eq_true]
  refine ⟨(eArrs ()).getD m #[], getD_mem_of_lt (by simp [eArrs, hm]), ?_⟩
  exact (eqA_iff (rep_vA (by norm_num)) (rep_eArrs hm)).2 hmx.symm

theorem xkData_getD_four : xkData.getD 4 (false, false, []) = (true, false, [3]) := rfl

theorem xkSub_eq_of_false {e : Bool × Bool × List ℕ} (hf : e.2.1 = false) :
    xkSub e = hatE.map (MulAut.conj (xkElt e)).toMonoidHom := by
  unfold xkSub
  rw [hf]
  simp

theorem xkElt_empty : xkElt (false, false, []) = 1 := by
  simp [xkElt, hElt]

theorem exists_xkSub_of_le_titsS
    {X : Subgroup (Equiv.Perm (Fin 1755))} (hXS : X ≤ titsS)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (h2 : ∀ a ∈ X, a * a = 1) (h32 : Nat.card X = 32) :
    ∃ e ∈ xkData, X = xkSub e := by
  by_cases hE : X ≤ hatE
  · refine ⟨(false, false, []), by decide, ?_⟩
    rw [xkSub_eq_of_false rfl, xkElt_empty, map_conj_one]
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
  exact ⟨e, he, eq_of_le_of_card_ge hle (by rw [h32]; exact card_xkSub_le e)⟩

theorem xkElt_empty' : xkElt (false, true, []) = 1 := by
  simp [xkElt, hElt]

theorem xkData_cases : ∀ e ∈ xkData, (e.2.1 = false ∧ e.1 = true) ∨ e = (false, false, []) ∨
    e = (false, true, []) ∨ (e.2.1 = true ∧ e.1 = false ∧ e.2.2 ≠ []) := by decide

theorem xkElt_mem_titsN {e : Bool × Bool × List ℕ} (he : e ∈ xkData) (h1 : e.1 = true) :
    xkElt e ∈ titsN := by
  have h := List.all_eq_true.1 e32Check_parts.2.1 e he
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, -⟩ := h
  have hw' : nLetters e.2.2 = true := by simpa [h1] using hw
  have e1 : xkElt e = (e.2.2.map (chainGen titsNArrs)).prod := by simp [xkElt, h1]
  rw [e1]
  exact nArr_mem hw'

theorem map_conj_inf' {M : Type*} [Group M] (X Y : Subgroup M) (a : M) :
    (X ⊓ Y).map (MulAut.conj a).toMonoidHom =
      X.map (MulAut.conj a).toMonoidHom ⊓ Y.map (MulAut.conj a).toMonoidHom :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj a).injective

theorem exists_map_conj_le_titsS_of_le_titsN {Y : Subgroup (Equiv.Perm (Fin 1755))}
    (hYN : Y ≤ titsN) (hp : IsPGroup 2 Y) :
    ∃ n ∈ titsN, Y.map (MulAut.conj n).toMonoidHom ≤ titsS := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN : titsS ≤ titsN := titsS_le_titsN
  have hfac : (6144 : ℕ).factorization 2 = 11 := by
    have h : (6144 : ℕ) = 2 ^ 11 * 3 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    simp
  have hcardS : Nat.card (titsS.subgroupOf titsN) = 2 ^ (Nat.card titsN).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv, titsQS_facts.2.2.2, titsQN_facts.2.2.2,
      hfac]
    norm_num
  let P : Sylow 2 ↥titsN := Sylow.ofCard (titsS.subgroupOf titsN) hcardS
  have hp' : IsPGroup 2 (Y.subgroupOf titsN) := hp.of_equiv (subgroupOfEquivOfLe hYN).symm
  obtain ⟨Q, hQ⟩ := hp'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsN Q P
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxQ : (⟨x, hYN hx⟩ : titsN) ∈ (Q : Subgroup titsN) := hQ (mem_subgroupOf.2 hx)
  have hmem : g * ⟨x, hYN hx⟩ * g⁻¹ ∈ (P : Subgroup titsN) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hxQ
  have hP : (P : Subgroup titsN) = titsS.subgroupOf titsN := rfl
  rw [hP, mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem exists_eq_conj_of_le_twoF4N
    {Y : Subgroup (Equiv.Perm (Fin 1755))} (hY : Y ≤ twoF4N)
    (hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (h2 : ∀ a ∈ Y, a * a = 1) (h32 : Nat.card Y = 32) :
    (∃ m ∈ twoF4N, Y = hatE.map (MulAut.conj m).toMonoidHom) ∨ Y = parrottF ∨
      ∃ a ∈ titsD, Y = parrottF.map (MulAut.conj a).toMonoidHom ∧
        Nat.card (Y ⊓ parrottF : Subgroup (Equiv.Perm (Fin 1755))) ≤ 8 := by
  have hYA : Y ≤ titsA := hY.trans twoF4N_le_titsA
  have hYD : Y ≤ titsD := (card_le_of_elemAbelian_titsA hYA hc h2).1
  have hYN : Y ≤ titsN := by
    rw [← titsD_inf_normalizer_parrottF]
    exact le_inf hYD (hY.trans twoF4N_le_normalizer_parrottF)
  have hp : IsPGroup 2 Y := IsPGroup.of_card (n := 5) (by rw [h32]; norm_num)
  obtain ⟨n, hn, hle⟩ := exists_map_conj_le_titsS_of_le_titsN hYN hp
  have hYc : ∀ a ∈ Y.map (MulAut.conj n).toMonoidHom, ∀ b ∈ Y.map (MulAut.conj n).toMonoidHom,
      a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show n * a * n⁻¹ * (n * b * n⁻¹) = n * (a * b) * n⁻¹ by group,
      show n * b * n⁻¹ * (n * a * n⁻¹) = n * (b * a) * n⁻¹ by group, hc a ha b hb]
  have hY2 : ∀ a ∈ Y.map (MulAut.conj n).toMonoidHom, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show n * a * n⁻¹ * (n * a * n⁻¹) = n * (a * a) * n⁻¹ by group, h2 a ha]
    group
  obtain ⟨e, he, hYe⟩ := exists_xkSub_of_le_titsS hle hYc hY2
    (by rw [card_map_conj, h32])
  have hY_eq : Y = (xkSub e).map (MulAut.conj n⁻¹).toMonoidHom := by
    rw [← hYe, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hnM : n ∈ twoF4N := CFSG.Quasithin.le_extSub hn
  have hnN : n ∈ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) :=
    twoF4N_le_normalizer_parrottF hnM
  have hF_conj : parrottF.map (MulAut.conj n⁻¹).toMonoidHom = parrottF :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (inv_mem hnN)
  rcases xkData_cases e he with ⟨hf, h1⟩ | rfl | rfl | ⟨hf, h1, hne⟩
  ·
    left
    refine ⟨n⁻¹ * xkElt e, mul_mem (inv_mem hnM) (CFSG.Quasithin.le_extSub
      (xkElt_mem_titsN he h1)), ?_⟩
    rw [hY_eq, xkSub_eq_of_false hf, map_conj_map_conj]
  ·
    left
    refine ⟨n⁻¹, inv_mem hnM, ?_⟩
    rw [hY_eq, xkSub_eq_of_false rfl, xkElt_empty, map_conj_one]
  ·
    right
    left
    have h : xkSub (false, true, []) = parrottF := by
      unfold xkSub
      simp only [ite_true]
      rw [xkElt_empty', map_conj_one]
    rw [hY_eq, h, hF_conj]
  ·
    right
    right
    obtain ⟨hcD, -, -⟩ := xkElt_facts he
    have hxk : xkSub e = parrottF.map (MulAut.conj (xkElt e)).toMonoidHom := by
      unfold xkSub
      rw [hf]
      simp
    refine ⟨n⁻¹ * xkElt e, mul_mem (inv_mem (titsN_le_titsD hn)) hcD, ?_, ?_⟩
    · rw [hY_eq, hxk, map_conj_map_conj]
    · have hcount : interCount (xkSet (eArrs ()) (fArrs ()) e) (fArrs ()) ≤ 8 := by
        have h := List.all_eq_true.1 e32NormCheck_parts.1 e he
        simp only [hf, h1, Bool.not_true, Bool.false_or, Bool.not_false, Bool.and_true,
          Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        rcases h with h | h
        · exact absurd h hne
        · exact h
      have hinf : Y ⊓ parrottF = (xkSub e ⊓ parrottF).map (MulAut.conj n⁻¹).toMonoidHom := by
        rw [map_conj_inf', ← hY_eq, hF_conj]
      rw [hinf, card_map_conj]
      refine (card_inf_le_interCount (Xl := xkSet (eArrs ()) (fArrs ()) e) (Yl := fArrs ())
        (fun x hx => exists_rep_of_mem_xkSub he hx) ?_).trans hcount
      intro y hy
      obtain ⟨m, hm, rfl⟩ := mem_parrottF_iff.1 hy
      exact ⟨_, getD_mem_of_lt (by simp [fArrs, hm]), rep_fArrs hm⟩

theorem u8Bits_nine_twelve :
    ∀ m < 32, m.testBit 0 = false → ∀ i ∈ u8Bits m, 9 ≤ i ∧ i ≤ 12 := by decide

theorem sixteen_le_card_hatE_inf_parrottF :
    16 ≤ Nat.card (hatE ⊓ parrottF : Subgroup (Equiv.Perm (Fin 1755))) := by
  classical
  let S : Finset ℕ := (Finset.range 32).filter (fun m => m.testBit 0 = false)
  have hS : S.card = 16 := by decide
  have hmem : ∀ m ∈ S, eElt m ∈ (hatE ⊓ parrottF : Subgroup (Equiv.Perm (Fin 1755))) := by
    intro m hm
    simp only [S, Finset.mem_filter, Finset.mem_range] at hm
    refine ⟨eElt_mem hm.1, ?_⟩
    unfold eElt
    refine list_prod_map_mem fun i hi => ?_
    have := u8Bits_nine_twelve m hm.1 hm.2 i hi
    exact subset_closure ⟨i, by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega, rfl⟩
  let g : ↥S → ↥(hatE ⊓ parrottF : Subgroup (Equiv.Perm (Fin 1755))) :=
    fun m => ⟨eElt m, hmem m m.2⟩
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : eElt a = eElt b := congrArg Subtype.val hab
    have ha := (Finset.mem_filter.1 a.2).1
    have hb := (Finset.mem_filter.1 b.2).1
    exact Subtype.ext (eElt_injOn (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h1)
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_eq_finsetCard] at this
  omega

theorem mem_normalizer_map_conj_iff'' {M : Type*} [Group M] {X : Subgroup M} {k g : M} :
    g ∈ normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup M) : Set M) ↔
      k⁻¹ * g * k ∈ normalizer (X : Set M) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro H x
    have h := H (k * x * k⁻¹)
    rw [mem_map_conj_iff, mem_map_conj_iff] at h
    rw [show k⁻¹ * (k * x * k⁻¹) * k = x by group,
      show k⁻¹ * (g * (k * x * k⁻¹) * g⁻¹) * k = k⁻¹ * g * k * x * (k⁻¹ * g * k)⁻¹ by group] at h
    exact h
  · intro H x
    have h := H (k⁻¹ * x * k)
    rw [mem_map_conj_iff, mem_map_conj_iff]
    rw [show k⁻¹ * g * k * (k⁻¹ * x * k) * (k⁻¹ * g * k)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group] at h
    exact h

theorem conj_mem_titsD_iff' {a x : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) (hx : x ∈ titsA) :
    a * x * a⁻¹ ∈ titsD ↔ x ∈ titsD := by
  rw [mul_mem_titsD_iff (mul_mem ha hx) (inv_mem ha), mul_mem_titsD_iff ha hx]
  have hinv : a⁻¹ ∈ titsD ↔ a ∈ titsD :=
    ⟨fun h => by simpa using inv_mem h, fun h => inv_mem h⟩
  rw [hinv]
  by_cases h1 : a ∈ titsD <;> by_cases h2 : x ∈ titsD <;>
    simp only [h1, h2, iff_self, iff_true, iff_false, not_true_eq_false]

theorem map_conj_le_titsD {X : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsD)
    {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) :
    X.map (MulAut.conj a).toMonoidHom ≤ titsD := by
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (conj_mem_titsD_iff' ha (titsD_le_titsA (hX hx))).2 (hX hx)

theorem sixteen_le_card_conj_hatE_inf_parrottF {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA)
    (hN : ∀ y ∈ hatE.map (MulAut.conj a).toMonoidHom,
      y ∈ normalizer (parrottF : Set (Equiv.Perm (Fin 1755)))) :
    16 ≤ Nat.card (hatE.map (MulAut.conj a).toMonoidHom ⊓ parrottF :
      Subgroup (Equiv.Perm (Fin 1755))) := by
  have hED : hatE ≤ titsD := hatE_le_titsJ.trans titsJ_le_titsD
  have hYD := map_conj_le_titsD hED ha
  have hYM : hatE.map (MulAut.conj a).toMonoidHom ≤ twoF4N := by
    rw [← titsA_inf_normalizer_parrottF]
    exact le_inf (hYD.trans titsD_le_titsA) fun y hy => hN y hy
  obtain ⟨-, hE2, hEc, hE32⟩ := card_hatE
  have hYc : ∀ x ∈ hatE.map (MulAut.conj a).toMonoidHom, ∀ y ∈ hatE.map (MulAut.conj a).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show a * x * a⁻¹ * (a * y * a⁻¹) = a * (x * y) * a⁻¹ by group,
      show a * y * a⁻¹ * (a * x * a⁻¹) = a * (y * x) * a⁻¹ by group, hEc x hx y hy]
  have hY2 : ∀ x ∈ hatE.map (MulAut.conj a).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show a * x * a⁻¹ * (a * x * a⁻¹) = a * (x * x) * a⁻¹ by group, hE2 x hx]
    group
  have hY32 : Nat.card (hatE.map (MulAut.conj a).toMonoidHom) = 32 := by
    rw [card_map_conj, hE32]
  rcases exists_eq_conj_of_le_twoF4N hYM hYc hY2 hY32 with ⟨m, hm, hYm⟩ | hYF | ⟨a', ha', hYa', -⟩
  · have hmN : m ∈ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) :=
      twoF4N_le_normalizer_parrottF hm
    have hFm : parrottF.map (MulAut.conj m).toMonoidHom = parrottF :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hmN
    have hinf : hatE.map (MulAut.conj a).toMonoidHom ⊓ parrottF =
        (hatE ⊓ parrottF).map (MulAut.conj m).toMonoidHom := by
      rw [map_conj_inf', ← hYm, hFm]
    rw [hinf, card_map_conj]
    exact sixteen_le_card_hatE_inf_parrottF
  · exact absurd hYF (not_map_conj_hatE_eq_parrottF ha)
  · exfalso
    apply not_map_conj_hatE_eq_parrottF (mul_mem (inv_mem (titsD_le_titsA ha')) ha)
    have h : (hatE.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a'⁻¹).toMonoidHom =
        (parrottF.map (MulAut.conj a').toMonoidHom).map (MulAut.conj a'⁻¹).toMonoidHom :=
      congrArg (fun Z : Subgroup (Equiv.Perm (Fin 1755)) => Z.map (MulAut.conj a'⁻¹).toMonoidHom) hYa'
    rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
    exact h

theorem map_conj_parrottF_eq_of_normalizer {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA)
    (hN : ∀ f ∈ parrottF, f ∈ normalizer
      ((parrottF.map (MulAut.conj a).toMonoidHom : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))))
    (h16 : 16 ≤ Nat.card (parrottF ⊓ parrottF.map (MulAut.conj a).toMonoidHom :
      Subgroup (Equiv.Perm (Fin 1755)))) :
    parrottF.map (MulAut.conj a).toMonoidHom = parrottF := by
  have hFD : parrottF ≤ titsD := parrottF_le_titsD
  have hYD := map_conj_le_titsD hFD (inv_mem ha)
  have hYN : ∀ y ∈ parrottF.map (MulAut.conj a⁻¹).toMonoidHom,
      y ∈ normalizer (parrottF : Set (Equiv.Perm (Fin 1755))) := by
    intro y hy
    rw [mem_map_conj_iff, inv_inv] at hy
    have h := hN _ hy
    rw [mem_normalizer_map_conj_iff''] at h
    rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h
  have hYM : parrottF.map (MulAut.conj a⁻¹).toMonoidHom ≤ twoF4N := by
    rw [← titsA_inf_normalizer_parrottF]
    exact le_inf (hYD.trans titsD_le_titsA) fun y hy => hYN y hy
  obtain ⟨hFc, hF2⟩ := parrottF_elemAbelian
  have hYc : ∀ x ∈ parrottF.map (MulAut.conj a⁻¹).toMonoidHom,
      ∀ y ∈ parrottF.map (MulAut.conj a⁻¹).toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show a⁻¹ * x * a⁻¹⁻¹ * (a⁻¹ * y * a⁻¹⁻¹) = a⁻¹ * (x * y) * a⁻¹⁻¹ by group,
      show a⁻¹ * y * a⁻¹⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) = a⁻¹ * (y * x) * a⁻¹⁻¹ by group, hFc x hx y hy]
  have hY2 : ∀ x ∈ parrottF.map (MulAut.conj a⁻¹).toMonoidHom, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show a⁻¹ * x * a⁻¹⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) = a⁻¹ * (x * x) * a⁻¹⁻¹ by group, hF2 x hx]
    group
  have hY32 : Nat.card (parrottF.map (MulAut.conj a⁻¹).toMonoidHom) = 32 := by
    rw [card_map_conj, card_parrottF]
  rcases exists_eq_conj_of_le_twoF4N hYM hYc hY2 hY32 with ⟨m, hm, hYm⟩ | hYF | ⟨a', ha', hYa', hcard⟩
  · exfalso
    apply not_map_conj_hatE_eq_parrottF (mul_mem ha (twoF4N_le_titsA hm))
    have h : (parrottF.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        (hatE.map (MulAut.conj m).toMonoidHom).map (MulAut.conj a).toMonoidHom :=
      congrArg (fun Z : Subgroup (Equiv.Perm (Fin 1755)) => Z.map (MulAut.conj a).toMonoidHom) hYm
    rw [map_conj_map_conj, map_conj_map_conj, mul_inv_cancel, map_conj_one] at h
    exact h.symm
  · have h : (parrottF.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        parrottF.map (MulAut.conj a).toMonoidHom :=
      congrArg (fun Z : Subgroup (Equiv.Perm (Fin 1755)) => Z.map (MulAut.conj a).toMonoidHom) hYF
    rw [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h
    exact h.symm
  · exfalso
    have hinf : parrottF.map (MulAut.conj a⁻¹).toMonoidHom ⊓ parrottF =
        (parrottF ⊓ parrottF.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom := by
      rw [map_conj_inf', map_conj_map_conj, inv_mul_cancel, map_conj_one]
    rw [hinf, card_map_conj] at hcard
    omega

theorem conj_hatE_facts {e : Bool × Bool × List ℕ} (he : e ∈ xkData) (hf : e.2.1 = false)
    (hv2 : memL (xkSet (eArrs ()) (fArrs ()) e) (vA 2) = true)
    (hcard : interCount (xkSet (eArrs ()) (fArrs ()) e) (eArrs ()) ≤ 8)
    (hall : (xkSet (eArrs ()) (fArrs ()) e).all (fun x => (List.range 5).all fun i =>
      memL (eArrs ()) (compA 1755 (compA 1755 x (vA (8 + i))) x)) = true) :
    ∃ c ∈ titsD, parrottV 2 ∈ hatE.map (MulAut.conj c).toMonoidHom ∧
      (∀ y ∈ hatE.map (MulAut.conj c).toMonoidHom,
        y ∈ normalizer (hatE : Set (Equiv.Perm (Fin 1755)))) ∧
      Nat.card (hatE.map (MulAut.conj c).toMonoidHom ⊓ hatE :
        Subgroup (Equiv.Perm (Fin 1755))) ≤ 8 := by
  have hxk := xkSub_eq_of_false hf
  obtain ⟨hcD, -, -⟩ := xkElt_facts he
  obtain ⟨-, hE2, -, -⟩ := card_hatE
  refine ⟨xkElt e, hcD, ?_, ?_, ?_⟩
  ·
    unfold memL at hv2
    obtain ⟨w, hw, hvw⟩ := List.any_eq_true.1 hv2
    have h := mem_xkSub_of_mem_xkSet he hw (rep_of_eqA (rep_vA (by norm_num)) hvw)
    rwa [hxk] at h
  ·
    intro y hy
    rw [← hxk] at hy
    obtain ⟨a, ha, hrep⟩ := exists_rep_of_mem_xkSub he hy
    have hyy : y * y = 1 := by
      rw [hxk] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show xkElt e * x * (xkElt e)⁻¹ * (xkElt e * x * (xkElt e)⁻¹) =
          xkElt e * (x * x) * (xkElt e)⁻¹ by group, hE2 x hx]
      group
    have hgen : ∀ i < 5, y * parrottV (8 + i) * y⁻¹ ∈ hatE := by
      intro i hi
      have h1 := List.all_eq_true.1 hall a ha
      have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
      unfold memL at h2
      obtain ⟨b, hb, hab⟩ := List.any_eq_true.1 h2
      have hrep2 : Rep 1755 (compA 1755 (compA 1755 a (vA (8 + i))) a)
          (y * parrottV (8 + i) * y) :=
        rep_compA (rep_compA hrep (rep_vA (by omega))) hrep
      obtain ⟨m, hm, hbm⟩ := exists_of_mem_eArrs hb
      have h3 := (eqA_iff hrep2 hbm).1 hab
      rw [inv_eq_of_mul_eq_one_right hyy, h3]
      exact eElt_mem hm
    have hE : hatE = closure (parrottV '' Set.Icc 8 12) := hatE_eq_parrottU_eight
    rw [hE]
    apply mem_normalizer_closure
    rintro _ ⟨j, ⟨hj1, hj2⟩, rfl⟩
    rw [← hE]
    obtain ⟨i, rfl⟩ : ∃ i, j = 8 + i := ⟨j - 8, by omega⟩
    exact hgen i (by omega)
  ·
    rw [← hxk]
    refine (card_inf_le_interCount (Xl := xkSet (eArrs ()) (fArrs ()) e)
      (Yl := eArrs ()) (fun x hx => exists_rep_of_mem_xkSub he hx) ?_).trans hcard
    intro y hy
    obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 hy
    exact ⟨_, getD_mem_of_lt (by simp [eArrs, hm]), rep_eArrs hm⟩

theorem exists_conj_hatE_parrottV_two :
    ∃ c ∈ titsD, parrottV 2 ∈ hatE.map (MulAut.conj c).toMonoidHom ∧
      (∀ y ∈ hatE.map (MulAut.conj c).toMonoidHom,
        y ∈ normalizer (hatE : Set (Equiv.Perm (Fin 1755)))) ∧
      Nat.card (hatE.map (MulAut.conj c).toMonoidHom ⊓ hatE :
        Subgroup (Equiv.Perm (Fin 1755))) ≤ 8 := by
  obtain ⟨-, -, hv2, hcard, hall⟩ := e32NormCheck_parts
  rw [xkData_getD_four] at hv2 hcard hall
  exact conj_hatE_facts (by decide) rfl hv2 hcard hall

end CFSG.LocalAnalysis.EvenBN.Tits.Model
