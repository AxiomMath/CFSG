module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import Certificates.Certificate76001
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2ThreeCrit

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.Monster.B.TwoA.Census Certificates.G2ThreeMax Certificates.K76J2Max
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.G2ThreeCert CFSG.RankThree.PartTwo.Sec4.Sporadic
  CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2
open scoped Pointwise

private theorem testBit_foldl_ite (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) (j : ℕ) :
    ∀ (L : List ℕ) (a : ℕ),
      (L.foldl (fun acc i => if p i then acc ||| 2 ^ f i else acc) a).testBit j = true ↔
        a.testBit j = true ∨ ∃ i ∈ L, p i ∧ f i = j
  | [], a => by simp
  | i :: L, a => by
    rw [List.foldl_cons, testBit_foldl_ite p f j L]
    by_cases hp : p i
    · simp only [hp, if_true, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
        decide_eq_true_eq, List.mem_cons, exists_eq_or_imp, true_and]
      tauto
    · simp only [hp, if_false, List.mem_cons, exists_eq_or_imp, false_and, false_or]

private def setOfCode (n : ℕ) : Set (Fin 315) := {x | n.testBit x = true}

private theorem mem_setOfCode {n : ℕ} {x : Fin 315} : x ∈ setOfCode n ↔ n.testBit x = true :=
  Iff.rfl

private theorem setOfCode_imgSet {t : Array ℕ} {g : J2.GJ} (ht : Rep 315 t g.1) (n : ℕ) :
    setOfCode (imgSet t n) = g • setOfCode n := by
  ext x
  rw [Set.mem_smul_set, mem_setOfCode, imgSet, testBit_foldl_ite]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range, mem_setOfCode]
  constructor
  · rintro ⟨i, hi, hni, hti⟩
    refine ⟨⟨i, hi⟩, hni, Fin.ext ?_⟩
    rw [← hti, ht.apply hi]
    rfl
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, hy, ht y⟩

private theorem setOfCode_inj {a b : ℕ} (ha : a < 2 ^ 315) (hb : b < 2 ^ 315)
    (h : setOfCode a = setOfCode b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 315
  · exact Bool.eq_iff_iff.2 (Set.ext_iff.1 h ⟨j, hj⟩)
  · have h2 : 2 ^ 315 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (ha.trans_le h2), Nat.testBit_lt_two_pow (hb.trans_le h2)]

private theorem orbit_closure_eq_orbit {G X : Type*} [Group G] [MulAction G X] {S : Set G}
    (hS : Subgroup.closure S = ⊤) (x : X) :
    MulAction.orbit (Subgroup.closure S) x = MulAction.orbit G x := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.1, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, by rw [hS]; exact Subgroup.mem_top g⟩, rfl⟩

private theorem k76NTabs_get (c : NatCert) {s : ℕ} (hs : s < 3) :
    (nTabs c)[s]! = permArr c [s + 2] := by
  interval_cases s <;> rfl

private theorem k76Check_parts (h : check () = true) :
    natCertOK act 5 (fun u => decide (u < 2 ^ 315)) (root ()) (orbitCert ()) = true ∧
      (orbitCert ()).pts.size = 280 ∧ ∀ s < 3, tabOf (orbitCert ()) (s + 2) 0 = 0 := by
  unfold check at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

private theorem coatom_of_check {G X : Type*} [Group G] [MulAction G X] (x₀ : X) (gens : ℕ → G)
    (hgen : Subgroup.closure (gens '' {k | k < 5}) = ⊤) (dec : ℕ → X)
    (hroot : dec (root ()) = x₀) (hact : ∀ k < 5, ∀ a, dec (act k a) = gens k • dec a)
    (hnt : ∃ g : G, g • x₀ ≠ x₀) (hcheck : check () = true) :
    IsCoatom (MulAction.stabilizer G x₀) := by
  classical
  unfold check at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨⟨hc, hsz⟩, hfix⟩, hor⟩, htr⟩ := hcheck
  set c₁ := orbitCert () with hc₁
  set hp := nTabs c₁ with hhp
  set orbs := orbitSearch (hAct hp) 3 280 with horbs
  clear_value orbs hp c₁
  simp only [beq_iff_eq] at hsz
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hfix
  simp only [okOrbs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hor
  obtain ⟨hor1, hor2⟩ := hor
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at htr
  have hp_size : hp.size = 3 := by rw [hhp]; rfl
  set d : ℕ → X := fun i => dec c₁.pts[i]! with hd
  have hd0 : d 0 = x₀ := by
    simp only [hd]
    rw [natCertOK_root hc]
    exact hroot
  have hword : ∀ w : List ℕ, (∀ k ∈ w, k < 5) → ∀ i < 280,
      applyW c₁ w i < 280 ∧ d (applyW c₁ w i) = wordElem gens w • d i := by
    intro w hw
    have := word_spec hc (fun k hk a _ => hact k hk a) w hw
    rwa [hsz] at this
  have hα : ∀ g : G, ∃ i < 280, d i = g • x₀ := by
    intro g
    have h' := orbit_of_natCertOK hc (dec := dec) (gens := gens) (fun k hk a _ => hact k hk a)
    have hmem : g • dec (root ()) ∈ MulAction.orbit
        (Subgroup.closure (gens '' {k | k < 5})) (dec (root ())) :=
      ⟨⟨g, by rw [hgen]; exact Subgroup.mem_top g⟩, rfl⟩
    rw [h', hsz] at hmem
    obtain ⟨i, hi, hie⟩ := hmem
    refine ⟨i, hi, ?_⟩
    rw [← hroot]
    exact hie
  have hp_get : ∀ s < 3, ∀ a < 280, (hp[s]!)[a]! = applyW c₁ [s + 2] a := by
    intro s hs a ha
    rw [hhp, k76NTabs_get c₁ hs, permArr_get c₁ _ (by omega)]
  have hstab_w : ∀ s < 3, (∀ k ∈ [s + 2], k < 5) ∧ applyW c₁ [s + 2] 0 = 0 := by
    intro s hs
    refine ⟨fun k hk => ?_, hfix s hs⟩
    rw [List.mem_singleton] at hk
    omega
  set hgens : ℕ → G := fun s => wordElem gens [s + 2] with hhgens
  have hact₂ : ∀ s < hp.size, ∀ a < 280, d (hAct hp s a) = hgens s • d a := by
    intro s hs a ha
    rw [hp_size] at hs
    obtain ⟨hw5, -⟩ := hstab_w s hs
    have := (hword _ hw5 a ha).2
    unfold hAct
    rw [hp_get s hs a ha]
    exact this
  let H' : Subgroup G := Subgroup.closure (hgens '' {s | s < hp.size})
  have hH'le : H' ≤ MulAction.stabilizer G x₀ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [Set.mem_setOf_eq, hp_size] at hs
    obtain ⟨hw5, h0⟩ := hstab_w s hs
    have := (hword _ hw5 0 (by norm_num)).2
    rw [h0, hd0] at this
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact this.symm
  have hcover : ∀ i < 280, ∃ t ∈ orbs, ∃ h ∈ H', d i = h • d t.1 := by
    intro i hi
    have hmem : i ∈ List.range 280 := List.mem_range.2 hi
    rw [← hor2] at hmem
    have hmem' := (List.mergeSort_perm _ _).mem_iff.1 hmem
    obtain ⟨t, ht, hit⟩ := List.mem_flatMap.1 hmem'
    obtain ⟨m, hm, hmx⟩ := orbit_mem_of_natCertOK (hor1 t ht) hact₂ hit
    exact ⟨t, ht, m, hm, hmx⟩
  have hrep : ∀ t ∈ orbs, t.1 ≠ 0 → (∀ k ∈ pathWord c₁ 280 t.1, k < 5) ∧
      applyW c₁ (pathWord c₁ 280 t.1) 0 = t.1 ∧ ∀ i < 280, ∃ m ∈ Subgroup.closure
        ((H' : Set G) ∪ {wordElem gens (pathWord c₁ 280 t.1)}), d i = m • d 0 := by
    intro t ht ht0
    have hchk := (htr t ht).resolve_left ht0
    simp only [repOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hw5, happ⟩, hnat⟩, hsort⟩ := hchk
    set w := pathWord c₁ 280 t.1 with hw
    set rp := permArr c₁ w with hrp
    set c₃ := natBfs (repAct hp rp) 4 0 280 with hc₃
    clear_value c₃
    refine ⟨hw5, happ, ?_⟩
    set gs₃ : ℕ → G := fun s => if s < hp.size then hgens s else wordElem gens w with hgs₃
    have hact₃ : ∀ k < 4, ∀ a < 280, d (repAct hp rp k a) = gs₃ k • d a := by
      intro k hk a ha
      by_cases hkp : k < hp.size
      · simp only [repAct, hkp, ite_true, gs₃]
        exact hact₂ k hkp a ha
      · simp only [repAct, hkp, ite_false, gs₃]
        rw [hrp, permArr_get c₁ w (by omega)]
        exact (hword w hw5 a ha).2
    intro i hi
    have hmem : i ∈ List.range 280 := List.mem_range.2 hi
    rw [← hsort] at hmem
    have hmem' := (List.mergeSort_perm _ _).mem_iff.1 hmem
    obtain ⟨m, hm, hmx⟩ := orbit_mem_of_natCertOK hnat hact₃ hmem'
    refine ⟨m, ?_, hmx⟩
    refine Subgroup.closure_mono ?_ hm
    rintro _ ⟨k, hk, rfl⟩
    by_cases hkp : k < hp.size
    · left
      simp only [gs₃, hkp, ite_true]
      exact Subgroup.subset_closure ⟨k, hkp, rfl⟩
    · right
      simp only [gs₃, hkp, ite_false]
      rfl
  refine isCoatom_stabilizer_of_cover x₀ hnt H' hH'le
    {g | ∃ t ∈ orbs, t.1 ≠ 0 ∧ g = wordElem gens (pathWord c₁ 280 t.1)} ?_ ?_
  · intro g hg
    obtain ⟨i, hi, hie⟩ := hα g
    obtain ⟨t, ht, h, hh, hdi⟩ := hcover i hi
    by_cases ht0 : t.1 = 0
    · exfalso
      apply hg
      have h1 : h • x₀ = x₀ := hH'le hh
      rw [← hie, hdi, ht0, hd0, h1]
    · obtain ⟨hw5, hwa, -⟩ := hrep t ht ht0
      refine ⟨wordElem gens (pathWord c₁ 280 t.1), ⟨t, ht, ht0, rfl⟩, h, hh, ?_⟩
      have h1 := (hword _ hw5 0 (by norm_num)).2
      rw [hwa, hd0] at h1
      rw [← hie, hdi, h1, mul_smul]
  · rintro r ⟨t, ht, ht0, rfl⟩ g
    obtain ⟨-, -, hall⟩ := hrep t ht ht0
    obtain ⟨i, hi, hie⟩ := hα g
    obtain ⟨m, hm, hmx⟩ := hall i hi
    exact ⟨m, hm, by rw [← hie, hmx, hd0]⟩

private noncomputable def j2Gens :
    ℕ → J2.GJ
  | 0 => pa
  | 1 => pb
  | k + 2 => if hk : k < J2.gensNZArr.size then J2.gElt J2.gensNZArr J2.gensNZ_spec k hk else 1

private theorem gensNZArr_size : J2.gensNZArr.size = 3 := rfl

private theorem gensArr_get_add_two {k : ℕ} (hk : k < 3) : gensArr[k + 2]! = J2.gensNZArr[k]! := by
  interval_cases k <;> rfl

private theorem rep_j2Gens {k : ℕ}
    (hk : k < 5) : Rep 315 gensArr[k]! (j2Gens k).1 := by
  match k, hk with
  | 0, _ => exact rep_permA
  | 1, _ => exact rep_permB
  | k + 2, hk =>
    have hk3 : k < J2.gensNZArr.size := by rw [gensNZArr_size]; omega
    rw [j2Gens, dif_pos hk3, gensArr_get_add_two (by omega)]
    exact J2.rep_elA _

private theorem closure_j2Gens :
    Subgroup.closure (j2Gens '' {k | k < 5}) = ⊤ := by
  rw [eq_top_iff, ← closure_pa_pb, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.subset_closure ⟨0, by norm_num, rfl⟩
  · exact Subgroup.subset_closure ⟨1, by norm_num, rfl⟩

theorem isCoatom_normalizer_zJ :
    IsCoatom (Subgroup.normalizer ((Subgroup.zpowers J2.zJ : Subgroup J2.GJ) : Set J2.GJ)) := by
  have hcheck : check () = true := Certificates.certificate76001
  obtain ⟨hc, hsz, hfix⟩ := k76Check_parts hcheck
  have hact : ∀ k < 5, ∀ a, setOfCode (act k a) = j2Gens k • setOfCode a :=
    fun k hk a => setOfCode_imgSet (rep_j2Gens hk) a
  set x₀ : Set (Fin 315) := setOfCode (root ()) with hx₀
  have hcard : (MulAction.orbit J2.GJ x₀).ncard = 280 := by
    have h := ncard_orbit_of_natCertOK hc (fun k hk a _ => hact k hk a)
      (fun a b ha hb e => setOfCode_inj (of_decide_eq_true ha) (of_decide_eq_true hb) e)
    rwa [hsz, orbit_closure_eq_orbit closure_j2Gens] at h
  have hidx : (MulAction.stabilizer J2.GJ x₀).index = 280 := by
    rw [MulAction.index_stabilizer, hcard]
  have hstab : Nat.card (MulAction.stabilizer J2.GJ x₀) = 2160 := by
    have h := (MulAction.stabilizer J2.GJ x₀).card_mul_index
    rw [hidx, J2.card_GJ] at h
    omega
  have hnt : ∃ g : J2.GJ, g • x₀ ≠ x₀ := by
    by_contra h
    push_neg at h
    have htop : MulAction.stabilizer J2.GJ x₀ = ⊤ := eq_top_iff.2 fun g _ => h g
    rw [htop, Subgroup.index_top] at hidx
    omega
  have hco := coatom_of_check x₀ j2Gens closure_j2Gens setOfCode rfl hact hnt hcheck
  have hle : Subgroup.normalizer ((Subgroup.zpowers J2.zJ : Subgroup J2.GJ) : Set J2.GJ) ≤
      MulAction.stabilizer J2.GJ x₀ := by
    rw [J2.normalizer_Z, J2.subOf_eq_closure_gElt J2.gensNZArr J2.gensNZ_spec,
      Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk3 : k < 3 := by rwa [gensNZArr_size] at hk
    have hg : j2Gens (k + 2) = J2.gElt J2.gensNZArr J2.gensNZ_spec k hk := by
      rw [j2Gens, dif_pos hk]
    obtain ⟨-, e⟩ := tab_spec hc (fun k hk a _ => hact k hk a) (show k + 2 < 5 by omega)
      (natCertOK_pos hc)
    rw [hfix k hk3, natCertOK_root hc, hg] at e
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact e.symm
  have heq : Subgroup.normalizer ((Subgroup.zpowers J2.zJ : Subgroup J2.GJ) : Set J2.GJ) =
      MulAction.stabilizer J2.GJ x₀ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hstab, J2.card_normalizer_Z])
  rw [heq]
  exact hco

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
