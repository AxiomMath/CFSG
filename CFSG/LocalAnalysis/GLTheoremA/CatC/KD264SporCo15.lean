module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Co15Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo17
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporHN3
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1FiveA
public import Certificates.Certificate10145
public import Certificates.Certificate13670
public import Certificates.Certificate13671

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F Timmesfeld.Co1Five Timmesfeld.Co1FiveComp

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

theorem gtOK_valid {Gs : Array (Array ℕ)} {T : GTree} (h : gtOK Gs T = true) :
    ∀ i < T.pts.size, validRows T.pts[i]! = true := by
  unfold gtOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hall⟩, -⟩, -⟩ := h
  have hpt := CFSG.Sporadic.Th.allIn_eq_true.1 hall
  intro i hi
  have hp := hpt i (Nat.zero_le _) hi
  simp only [gtPointOK, Bool.and_eq_true] at hp
  exact hp.1

theorem comp_parts (h : compOK Native.aR Native.bR = true) :
    (gDag Native.aR Native.bR).2.2 = true ∧
      a0Row gRows (repA.getD 1 0) = CFSG.HardMathSupport.Dickson.I271.TabCo1.repD0 ∧
      (∀ j < 3, rowAt gRows (idxD.getD j 0) ∈ (qTree gRows).pts) ∧
      cenOK gRows = true ∧ a5OK gRows (gDag Native.aR Native.bR).2.1 = true := by
  unfold compOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

section Q


theorem A0_le_Q (hG : GOK) (hC : compOK Native.aR Native.bR = true) : A0 hG ≤ Qsub := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨hflag, -, hmem, -, -⟩ := comp_parts hC
  obtain ⟨hok, -, -⟩ := qOK_parts (globalOK_parts hG).2.1
  have hd : ∀ i : Fin 3, dE i ∈ Qsub := by
    intro i
    obtain ⟨k, hk, hkrow⟩ := Array.getElem_of_mem (hmem i.val i.2)
    refine CFSG.Sporadic.Co1Block.mem_closure_of_prodTree μG μG_injective hok qG (qG_rep hG)
      (i := k) hk ?_
    rw [μG_apply, getElem!_pos _ k hk, hkrow]
    exact (rep_gE hflag _).symm
  rintro _ ⟨a, rfl⟩
  rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from rfl, φ_apply, vecProd_eq]
  exact Qsub.mul_mem (Qsub.pow_mem (hd 0) _)
    (Qsub.mul_mem (Qsub.pow_mem (hd 1) _) (Qsub.pow_mem (hd 2) _))

theorem relIndex_A0_Q (hG : GOK) (hC : compOK Native.aR Native.bR = true) :
    (A0 hG).relIndex Qsub = 5 := by
  have h := Subgroup.relIndex_mul_card (A0 hG) Qsub
  rw [inf_eq_left.2 (A0_le_Q hG hC), card_A0 hG, card_Qsub hG] at h
  omega

theorem card_cen_le_of_rows (hG : GOK) {q : Rows} {r : ↥GA} (hqrep : MRep q ((r : ↥GA) : GL24))
    (hqv : validRows q = true)
    (hlen : (((List.range 125).map (a0Row gRows)).filter fun a =>
      Native.mul a q == Native.mul q a).length ≤ 5) :
    Nat.card ↥(A0 hG ⊓ Subgroup.centralizer ({r} : Set ↥GA)) ≤ 5 := by
  classical
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = ((List.range 125).filter fun k =>
      Native.mul (a0Row gRows k) q == Native.mul q (a0Row gRows k)).toFinset := ⟨_, rfl⟩
  have hScard : S.card ≤ 5 := by
    rw [hS]
    refine (List.toFinset_card_le _).trans ?_
    rw [List.filter_map] at hlen
    simpa [Function.comp_def] using hlen
  have hmem : ∀ k < 125, φ hG (Multiplicative.ofAdd (vec3 k)) * r =
      r * φ hG (Multiplicative.ofAdd (vec3 k)) → k ∈ S := by
    intro k hk hxc
    have hrk := rep_a0Row hG hk
    have he : Native.mul (a0Row gRows k) q = Native.mul q (a0Row gRows k) := by
      refine rows_eq_of_mrep (validRows_mul' (validRows_a0Row hG k) hqv)
        (validRows_mul' hqv (validRows_a0Row hG k)) (hrk.mul hqrep) ?_
      have e : ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) : GL24) * ((r : ↥GA) : GL24) =
          ((r : ↥GA) : GL24) * ((φ hG (Multiplicative.ofAdd (vec3 k)) : ↥GA) : GL24) := by
        rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hxc]
      rw [e]
      exact hqrep.mul hrk
    rw [hS, List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨hk, by rw [he]; exact beq_self_eq_true _⟩
  have hcov : ∀ x ∈ A0 hG, ∃ k < 125, φ hG (Multiplicative.ofAdd (vec3 k)) = x := by
    rintro _ ⟨a, rfl⟩
    exact ⟨idx3 (Multiplicative.toAdd a), idx3_lt _, by rw [vec3_idx3]; rfl⟩
  exact (card_inf_centralizer_le (G := ↥GA) (A0 := A0 hG) (r := r)
    (fun k => φ hG (Multiplicative.ofAdd (vec3 k))) hcov S hmem).trans hScard

theorem card_cen_le (hG : GOK) (hC : compOK Native.aR Native.bR = true) {r : ↥GA}
    (hrQ : r ∈ Qsub) (hrA : r ∉ A0 hG) :
    Nat.card ↥(A0 hG ⊓ Subgroup.centralizer ({r} : Set ↥GA)) ≤ 5 := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨-, -, -, hcen, -⟩ := comp_parts hC
  obtain ⟨hok, -, -⟩ := qOK_parts (globalOK_parts hG).2.1
  obtain ⟨f, hfrow, -, hfeq⟩ := CFSG.Sporadic.Co1Block.prodTree_closure_eq μG μG_injective hok qG
    (qG_rep hG)
  have hr : r ∈ (Subgroup.closure (qG '' {l | l < (qGens gRows).toArray.size}) : Set ↥GA) := hrQ
  rw [hfeq] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  have hi' : i < (qTree gRows).pts.size := hi
  have hqrep : MRep (qTree gRows).pts[i]! ((f i : ↥GA) : GL24) := by
    unfold MRep
    rw [← μG_apply, hfrow i hi]
  have hqv : validRows (qTree gRows).pts[i]! = true := gtOK_valid hok i hi'
  unfold cenOK at hcen
  simp only [Array.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hcen
  have hpt := hcen i hi'
  rw [← getElem!_pos (qTree gRows).pts i hi'] at hpt
  rcases hpt with hA | hlen
  · exfalso
    obtain ⟨k, hk, hkq⟩ := List.mem_map.1 hA
    have hk' : k < 125 := List.mem_range.1 hk
    apply hrA
    have hrep2 : MRep (a0Row gRows k) ((f i : ↥GA) : GL24) := by rw [hkq]; exact hqrep
    have : f i = φ hG (Multiplicative.ofAdd (vec3 k)) :=
      Subtype.ext (hrep2.eq (rep_a0Row hG hk'))
    rw [this]
    exact ⟨_, rfl⟩
  · exact card_cen_le_of_rows hG hqrep hqv hlen

theorem le_A0 (hG : GOK) (hC : compOK Native.aR Native.bR = true) {A : Subgroup ↥GA}
    (hAQ : A ≤ Qsub) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h125 : 125 ≤ Nat.card A) :
    A ≤ A0 hG := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  exact le_of_comm_of_card (relIndex_A0_Q hG hC) (by norm_num) hAQ
    (fun r hr hrA => card_cen_le hG hC hr hrA) hA (by omega)

end Q

section A5


theorem wordG_invW' (gs : List GL24) {w : List ℤ} (hw : w.all (· != 0) = true) :
    wordG gs (invW w) = (wordG gs w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordG]
  | cons j w ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hw
    have e : invW (j :: w) = invW w ++ [-j] := by simp [invW]
    rw [e, Co1Perf.wordG_append, ih (by simpa using hw.2), show (j :: w) = [j] ++ w from rfl,
      Co1Perf.wordG_append, mul_inv_rev, Co1Perf.wordG_single, Co1Perf.wordG_single,
      Co1Perf.letterG_neg gs hw.1]

theorem listRep (hG : GOK) :
    ListRep (gDag Native.aR Native.bR).1 (gDag Native.aR Native.bR).2.1 gElts := by
  have hb : List.Forall₂ MRep [Native.aR, Native.bR] [A₁, A₂] :=
    List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)
  exact dag_listRep hb (dagWords.map Native.decWord) (globalOK_parts hG).1

noncomputable def sw (w : List ℤ) : ↥GA := ⟨wordG gElts w, wordG_mem gElts_mem w⟩

noncomputable def s (i : ℕ) : ↥GA := sw sWords[i]!

theorem rep_s (hG : GOK) (i : ℕ) :
    MRep (Native.word gRows (gDag Native.aR Native.bR).2.1 sWords[i]!) ((s i : ↥GA) : GL24) :=
  MRep.word (listRep hG) _

theorem a5_parts {rs is : List Rows} (h : a5OK rs is = true) :
    gtOK (sRows rs is).toArray (gtBFS (sRows rs is).toArray 100000) = true ∧
      (gtBFS (sRows rs is).toArray 100000).pts.size = 60 ∧
      ∀ i < 5, (sIdx[i]!).1 < 5 ∧ (sIdx[i]!).2 < 5 ∧ perfAt rs is i = true := by
  unfold a5OK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun i hi => ⟨(h3 i hi).1.1, (h3 i hi).1.2, (h3 i hi).2⟩⟩

theorem s_facts (hG : GOK) (hC : compOK Native.aR Native.bR = true) (i : ℕ) (hi : i < 5) :
    (s i * g1 hG 1 = g1 hG 1 * s i ∧ s i * g2 hG 1 = g2 hG 1 * s i) ∧
      ((sIdx[i]!).1 < 5 ∧ (sIdx[i]!).2 < 5) ∧
      s i = s (sIdx[i]!).1 * s (sIdx[i]!).2 * (s (sIdx[i]!).1)⁻¹ * (s (sIdx[i]!).2)⁻¹ := by
  obtain ⟨-, -, -, -, ha5⟩ := comp_parts hC
  obtain ⟨-, -, hall⟩ := a5_parts ha5
  obtain ⟨hj, hk, h⟩ := hall i hi
  unfold perfAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hw, hc1⟩, hc2⟩, he⟩ := h
  have hpl := (planeOK_parts (globalOK_parts hG).2.2.2.2).2.2 1 (by norm_num)
  have hb1 : MRep (a0Row gRows (repA.getD 1 0)) ((g1 hG 1 : ↥GA) : GL24) := rep_a0Row hG hpl.1
  have hb2 : MRep (a0Row gRows (repB.getD 1 0)) ((g2 hG 1 : ↥GA) : GL24) :=
    rep_a0Row hG hpl.2.1
  refine ⟨⟨?_, ?_⟩, ⟨hj, hk⟩, ?_⟩
  · apply Subtype.ext
    have h1 := (rep_s hG i).mul hb1
    have h2 := hb1.mul (rep_s hG i)
    rw [hc1] at h1
    exact MRep.eq h1 h2
  · apply Subtype.ext
    have h1 := (rep_s hG i).mul hb2
    have h2 := hb2.mul (rep_s hG i)
    rw [hc2] at h1
    exact MRep.eq h1 h2
  · apply Subtype.ext
    have h1 := rep_s hG i
    rw [he] at h1
    have h2 := MRep.eq h1 (MRep.word (listRep hG) _)
    rw [h2]
    have hwj : sWords[(sIdx[i]!).1]!.all (· != 0) = true := by
      have := (hall _ hj).2.2
      unfold perfAt at this
      simp only [Bool.and_eq_true] at this
      exact this.1.1.1
    have hwk : sWords[(sIdx[i]!).2]!.all (· != 0) = true := by
      have := (hall _ hk).2.2
      unfold perfAt at this
      simp only [Bool.and_eq_true] at this
      exact this.1.1.1
    simp only [sw, s, Co1Perf.wordG_append, wordG_invW' gElts hwj, wordG_invW' gElts hwk,
      Subgroup.coe_mul, Subgroup.coe_inv]

noncomputable def L5 : Subgroup ↥GA := Subgroup.closure (s '' {l | l < 5})

theorem card_L5 (hG : GOK) (hC : compOK Native.aR Native.bR = true) : Nat.card L5 = 60 := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨-, -, -, -, ha5⟩ := comp_parts hC
  obtain ⟨hok, hsz, -⟩ := a5_parts ha5
  have hsize : (sRows gRows (gDag Native.aR Native.bR).2.1).toArray.size = 5 := by
    simp [sRows, sWords]
  have hrep : ∀ l < (sRows gRows (gDag Native.aR Native.bR).2.1).toArray.size,
      μG (s l) = rowsMatrix 24 (sRows gRows (gDag Native.aR Native.bR).2.1).toArray[l]! := by
    intro l hl
    rw [hsize] at hl
    have hl' : l < sWords.size := by rw [show sWords.size = 5 from rfl]; exact hl
    have e : (sRows gRows (gDag Native.aR Native.bR).2.1).toArray[l]! =
        Native.word gRows (gDag Native.aR Native.bR).2.1 sWords[l]! := by
      rw [getElem!_pos _ l (by rw [hsize]; exact hl), getElem!_pos sWords l hl']
      simp [sRows]
    rw [e, μG_apply]
    exact (rep_s hG l).symm
  have h := CFSG.Sporadic.Co1Block.prodTree_card μG μG_injective hok s hrep
  rw [hsize, hsz] at h
  exact h

theorem L5_perfect (hG : GOK) (hC : compOK Native.aR Native.bR = true) : L5 ≤ ⁅L5, L5⁆ := by
  rw [L5, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨-, ⟨hj, hk⟩, he⟩ := s_facts hG hC i hi
  rw [SetLike.mem_coe, he, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨_, hj, rfl⟩)
    (Subgroup.subset_closure ⟨_, hk, rfl⟩)

theorem L5_le (hG : GOK) (hC : compOK Native.aR Native.bR = true) :
    L5 ≤ Subgroup.centralizer
      ((Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA) : Subgroup ↥GA) : Set ↥GA) := by
  rw [Subgroup.centralizer_closure, L5, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨⟨h1, h2⟩, -, -⟩ := s_facts hG hC i hi
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | rfl
  · exact h1.symm
  · exact h2.symm

end A5

section Two


theorem comp_plane (hG : GOK)
    (hC : compOK Native.aR Native.bR = true) :
    GLAPComponent 5 (Subgroup.centralizer
      ((Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA) : Subgroup ↥GA) : Set ↥GA)) L5 := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have hF : Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA) ≤ A0 hG := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  have hcen : Nat.card (Subgroup.centralizer
      ((Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA) : Subgroup ↥GA) : Set ↥GA)) = 1500 := by
    rw [Subgroup.centralizer_closure]
    have h := (leaf_bot hG (τ := 1) (by norm_num)).2
    rw [show leafR.getD 1 0 = 12 from rfl] at h
    exact h
  refine comp_of_perfect_sixty (G := ↥GA)
    (F := Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA)) (L := L5)
    (fun a ha b hb => A0_comm hG _ (hF ha) _ (hF hb)) (L5_le hG hC) (L5_perfect hG hC)
    (card_L5 hG hC) ?_
  rw [hcen, card_plane_rep hG (by norm_num : 1 < 3)]

end Two

section J2gen


open CFSG.HardMathSupport.Dickson.I271.TabCo1 in
theorem comp_J2_gen {G : Type} [Group G] (P : Subgroup G) [Finite ↥P] (x : ↥P) (u v : G)
    (hu : u ∈ P) (hv : v ∈ P) (hxu : (x : G) * u = u * x) (hxv : (x : G) * v = v * x)
    (hu1 : u ≠ 1) (h1 : u * v * u * v⁻¹ * u⁻¹ * v⁻¹ = 1)
    (h2 : u * v * v * u * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ * v⁻¹ = 1)
    (h3 : (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) *
      (u * v⁻¹ * u * v⁻¹ * v⁻¹ * v⁻¹ * u * u * u * v⁻¹) * (u * u * u * u * u * u * u) = 1)
    (ho : orderOf x = 5) (hbound : Nat.card (Subgroup.centralizer ({x} : Set ↥P)) ≤ 3024000) :
    ∃ J : Subgroup ↥P,
      GLAPComponent 5 (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup ↥P) : Set ↥P)) J := by
  obtain ⟨u', hu'⟩ : ∃ u' : ↥P, (u' : G) = u := ⟨⟨u, hu⟩, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v' : ↥P, (v' : G) = v := ⟨⟨v, hv⟩, rfl⟩
  subst hu' hv'
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup ↥P, L = Subgroup.closure ({u', v'} : Set ↥P) := ⟨_, rfl⟩
  have e1 : u' * v' * u' * v'⁻¹ * u'⁻¹ * v'⁻¹ = 1 := Subtype.ext (by simpa using h1)
  have e2 : u' * v' * v' * u' * v'⁻¹ * v'⁻¹ * v'⁻¹ * v'⁻¹ * v'⁻¹ = 1 :=
    Subtype.ext (by simpa using h2)
  have e3 : (u' * v'⁻¹ * u' * v'⁻¹ * v'⁻¹ * v'⁻¹ * u' * u' * u' * v'⁻¹) *
      (u' * v'⁻¹ * u' * v'⁻¹ * v'⁻¹ * v'⁻¹ * u' * u' * u' * v'⁻¹) *
      (u' * v'⁻¹ * u' * v'⁻¹ * v'⁻¹ * v'⁻¹ * u' * u' * u' * v'⁻¹) *
      (u' * u' * u' * u' * u' * u' * u') = 1 := Subtype.ext (by simpa using h3)
  have hu1' : u' ≠ 1 := fun h => hu1 (by rw [h, Subgroup.coe_one])
  obtain ⟨eL⟩ := nonempty_mulEquiv_J2_of_relators u' v' L hLdef e1 e2
    (u' * v'⁻¹ * u' * v'⁻¹ * v'⁻¹ * v'⁻¹ * u' * u' * u' * v'⁻¹) rfl e3 hu1'
  obtain ⟨hs, hcard, hnab⟩ := J2_facts_of_equiv eL
  have hLC : L ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup ↥P) : Set ↥P) := by
    rw [Seven.centralizer_zpowers_eq, hLdef, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hxu.symm)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hxv.symm)
  refine ⟨L, glaPComponent_of_simple_bound (F := Subgroup.zpowers x) (L := L) Nat.prime_five
    ?_ ?_ hLC hs hnab ?_ (by rw [hcard]; norm_num)⟩
  · intro f hf
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
    exact (Commute.zpow_zpow_self x m n).eq
  · intro f hf c hc
    exact Subgroup.mem_centralizer_iff.1 hc f hf
  · rw [Seven.centralizer_zpowers_eq, Nat.card_zpowers, ho, hcard]
    exact hbound.trans (by norm_num)

end J2gen

section J2


open CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.HardMathSupport.Dickson.I271.TabCo1FiveA in
theorem comp_fiveA (hG : GOK) (hC : compOK Native.aR Native.bR = true) :
    orderOf (g1 hG 1) = 5 ∧ ∃ J : Subgroup ↥GA, GLAPComponent 5
      (Subgroup.centralizer ((Subgroup.zpowers (g1 hG 1) : Subgroup ↥GA) : Set ↥GA)) J := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨-, hd0, -, -, -⟩ := comp_parts hC
  have hpl := (planeOK_parts (globalOK_parts hG).2.2.2.2).2.2 1 (by norm_num)
  have hx : MRep repD0 ((g1 hG 1 : ↥GA) : GL24) := hd0 ▸ rep_a0Row hG hpl.1
  obtain ⟨hrep, -, hk1, hku, hkv, hu1, hw1, hw2, hw3, -⟩ := fiveA_data
  obtain ⟨h1, h2, h3⟩ := relators_of_wordG hw1 hw2 hw3
  have hxk : ((g1 hG 1 : ↥GA) : GL24) = kG ext 88 := hx.eq hrep
  have hx1 : g1 hG 1 ≠ 1 := fun h => hk1 (by rw [← hxk, h, Subgroup.coe_one])
  have ho : orderOf (g1 hG 1) = 5 := orderOf_eq_prime (A0_pow hG _ ⟨_, rfl⟩) hx1
  exact ⟨ho, comp_J2_gen GA (g1 hG 1) (kG ext 89) (kG ext 90) (kG_mem ext 89) (kG_mem ext 90)
    (by rw [hxk]; exact hku) (by rw [hxk]; exact hkv) hu1 h1 h2 h3 ho
    (card_cent_fiveA_le _ hx)⟩

end J2

section Row


theorem kd264RowData_Co1_five : KD264RowData 5 ↥GA := by
  haveI : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have hG : GOK := Certificates.certificate13670
  have hC : compOK Native.aR Native.bR = true := Certificates.certificate10145
  obtain ⟨ho, hJ1⟩ := comp_fiveA hG hC
  have hF2 : Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA) ≤ A0 hG := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  exact kd264RowData_of_A0 (G := ↥GA) (Q := Qsub) (A0 := A0 hG)
    (F1 := Subgroup.zpowers (g1 hG 1)) (F2 := Subgroup.closure ({g1 hG 1, g2 hG 1} : Set ↥GA))
    (by rw [card_Qsub hG, factorization_card_GA_five]; norm_num) (relIndex_A0_Q hG hC)
    (A0_elemAbelian hG) (card_A0 hG) (fun r hr hrA => card_cen_le hG hC hr hrA)
    (Subgroup.zpowers_le.2 ⟨_, rfl⟩) (by rw [Nat.card_zpowers, ho]) hJ1
    hF2 (card_plane_rep hG (by norm_num : 1 < 3)) ⟨L5, comp_plane hG hC⟩

end Row

section RowCo1


set_option maxRecDepth 100000 in
theorem kd264SporAt_Co1_five
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KD264SporAt 5 .Co1 := by
  haveI : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have e : CFSG.Blueprint.NativeSporadic.Co1 ≃* ↥GA := CFSG.Sporadic.Co1Block.co1MatEquiv
  haveI : IsSimpleGroup ↥GA :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co1.isSimpleGroup_Co1 e.symm
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  have hp : ¬ (Nat.card ↥GA).Prime := by rw [card_GA_eq]; norm_num
  have hnc : ∃ x y : ↥GA, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥GA) hp
  have hb : ↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group := e.symm.trans b
  have hrd : KD264RowData 5 ↥GA := kd264RowData_Co1_five
  refine kd264SporAt_of_model (p := 5) (s := .Co1) (Q := ↥GA) hOut Nat.prime_five (by decide) ?_
    ?_ ?_
  · exact hnc
  · exact hb
  · intro _ _ _
    exact hrd

end RowCo1

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15
