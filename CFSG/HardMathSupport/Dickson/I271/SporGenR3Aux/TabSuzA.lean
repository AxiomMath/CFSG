module

public import Certificates.Certificate17321
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzBound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzFuse
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzU43

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzA
  CFSG.LieType.Multipliers.U43 CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open CFSG.Sporadic.SuzOddCore (suzM smallChain smallChain_arrays smallChain_check smallChain_valid
  smallChain_baseCount smallChain_originalSubgroup smallStrongArrs smallBaseNat)
open scoped commutatorElement

section FixStab

@[expose] def fixStab {n : ℕ} (X : Equiv.Perm (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ q, X q = q ↔ X (g q) = g q}
  mul_mem' := fun {g h} hg hh q => (hh q).trans (hg (h q))
  one_mem' := fun q => Iff.rfl
  inv_mem' := fun {g} hg q => by
    have := (hg (g⁻¹ q)).symm
    simpa using this

theorem pow_fix_iff {n : ℕ} {X : Equiv.Perm (Fin n)} (hX : X ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (q : Fin n) : (X ^ e) q = q ↔ X q = q := by
  have h3 : ∀ s, X (X (X s)) = s := fun s => by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ s) hX
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  rcases he with rfl | rfl
  · simp
  · rw [pow_two, Equiv.Perm.mul_apply]
    constructor
    · intro h
      have := h3 q
      rw [h] at this
      exact this
    · intro h
      rw [h, h]

theorem mem_fixStab_of_conj {n : ℕ} {X g : Equiv.Perm (Fin n)} (hX : X ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : g * X * g⁻¹ = X ^ e) : g ∈ fixStab X := by
  intro q
  have h1 : g (X q) = (X ^ e) (g q) := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (g q)) h
    simpa [Equiv.Perm.mul_apply] using this
  rw [← pow_fix_iff hX he (g q), ← h1]
  constructor
  · intro hq
    rw [hq]
  · intro hq
    exact g.injective hq

end FixStab

section Facts

structure CaseAFacts : Prop where
  size : (aStrong ()).size = 11
  chain : caseChainOK3 1782 (aStrong ()) aBase aWords (aStrong ())[0]! (aStrong ())[1]!
    (aStrong ())[2]! = true
  eqx : eqA 1782 (aStrong ())[2]! (xAArr (levels ())) = true
  orbits : (rawOrbitSizes 1782 (aStrong ()) aBase).prod = 9797760
  vala : validA 1782 (aStrong ())[0]! = true
  valb : validA 1782 (aStrong ())[1]! = true
  ina : inP (levels ()) (aStrong ())[0]! = true
  inb : inP (levels ()) (aStrong ())[1]! = true
  comma : commA 1782 (aStrong ())[0]! (xAArr (levels ())) = true
  commb : commA 1782 (aStrong ())[1]! (xAArr (levels ())) = true
  relsmod : ∀ w ∈ rels, wordModX (aStrong ())[0]! (aStrong ())[1]! (xAArr (levels ())) w = true
  valu : validA 1782 (rebuild (levels ()) uTuple) = true
  valv : validA 1782 (rebuild (levels ()) vTuple) = true
  siftu : siftA 1782 (rawLevels 1782 (aStrong ()) aBase) aBase 0 (rebuild (levels ()) uTuple) =
    true
  siftv : siftA 1782 (rawLevels 1782 (aStrong ()) aBase) aBase 0 (rebuild (levels ()) vTuple) =
    true
  comm : eqA 1782 (commutatorA 1782 (rebuild (levels ()) vTuple) (rebuild (levels ()) uTuple))
    (xAArr (levels ())) = true
  valt : validA 1782 (rebuild (levels ()) tTuple) = true
  int : inP (levels ()) (rebuild (levels ()) tTuple) = true
  conjt : eqA 1782 (conjA 1782 (rebuild (levels ()) tTuple) (xAArr (levels ())))
    (compA 1782 (xAArr (levels ())) (xAArr (levels ()))) = true
  fixb : allLt 5 (fun i => (xAArr (levels ()))[aBase[i]!]! == aBase[i]!) = true
  c0 : fixLevCount 1782 (levels ()) (xAArr (levels ())) 0 = 162
  c1 : fixLevCount 1782 (levels ()) (xAArr (levels ())) 1 = 56
  c2 : fixLevCount 1782 (levels ()) (xAArr (levels ())) 2 = 10
  c3 : fixLevCount 1782 (levels ()) (xAArr (levels ())) 3 = 9
  c4 : fixLevCount 1782 (levels ()) (xAArr (levels ())) 4 = 8
  d5 : levCount 1782 (levels ()) 5 = 3

theorem caseA_facts : CaseAFacts := by
  have h : caseACheck () = true := Certificates.certificate17321
  simp only [caseACheck, Bool.and_assoc, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, c21, c22, c23, c24, c25, c26⟩ := h
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, c21, c22, c23, c24, c25, c26⟩

theorem wordModX_spec {a b xa : Array ℕ} (hva : validA 1782 a = true) (hvb : validA 1782 b = true)
    {X : Equiv.Perm (Fin 1782)} (hx : Rep 1782 xa X) {w : List (Fin 2 × Bool)}
    (h : wordModX a b xa w = true) :
    evalW ![permOfArr 1782 a, permOfArr 1782 b] w = 1 ∨
      evalW ![permOfArr 1782 a, permOfArr 1782 b] w = X ∨
      evalW ![permOfArr 1782 a, permOfArr 1782 b] w = X * X := by
  have hval : ∀ k < (#[a, b] : Array (Array ℕ)).size, validA 1782 (#[a, b] : Array (Array ℕ))[k]! =
      true := by
    intro k hk
    have hk2 : k < 2 := hk
    interval_cases k
    · exact hva
    · exact hvb
  have hrepw := rep_evalWA hval (le_refl 2) w
  have hfun : (fun i : Fin 2 => permOfArr 1782 (#[a, b] : Array (Array ℕ))[i.val]!) =
      (![permOfArr 1782 a, permOfArr 1782 b] : Fin 2 → Equiv.Perm (Fin 1782)) := by
    funext i
    fin_cases i <;> rfl
  rw [hfun] at hrepw
  unfold wordModX at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h1 | h2) | h3
  · exact Or.inl ((eqA_iff hrepw rep_idA).1 h1)
  · exact Or.inr (Or.inl ((eqA_iff hrepw hx).1 h2))
  · exact Or.inr (Or.inr ((eqA_iff hrepw (rep_compA hx hx)).1 h3))

theorem coe_evalW_two {G : Type*} [Group G] (H : Subgroup G) (a b : ↥H)
    (w : List (Fin 2 × Bool)) :
    ((evalW ![a, b] w : ↥H) : G) = evalW ![(a : G), (b : G)] w := by
  have h := map_evalW H.subtype ![a, b] w
  have h2 : (fun i => H.subtype (![a, b] i)) = (![(a : G), (b : G)] : Fin 2 → G) := by
    funext i
    fin_cases i <;> rfl
  rw [h2] at h
  exact h

end Facts

section Main

@[expose] noncomputable def aPermA : Equiv.Perm (Fin 1782) := permOfArr 1782 (aStrong ())[0]!

@[expose] noncomputable def aPermB : Equiv.Perm (Fin 1782) := permOfArr 1782 (aStrong ())[1]!

@[expose] noncomputable def aSub : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure ({aPermA, aPermB, fuseXA} : Set (Equiv.Perm (Fin 1782)))

@[expose] noncomputable def aPermT : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (rebuild (levels ()) tTuple)

@[expose] noncomputable def aPermU : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (rebuild (levels ()) uTuple)

@[expose] noncomputable def aPermV : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (rebuild (levels ()) vTuple)

@[expose] def aBs : List (Fin 1782) := [0, 1, 2, 3, 4, 8]

theorem aBs_map : (aBs.map Fin.val).toArray = aBase := by decide

theorem aBs_nodup : aBs.Nodup := by decide

theorem rep_aA : Rep 1782 (aStrong ())[0]! aPermA := rep_of_validA caseA_facts.vala

theorem rep_aB : Rep 1782 (aStrong ())[1]! aPermB := rep_of_validA caseA_facts.valb

theorem rep_aX : Rep 1782 (aStrong ())[2]! fuseXA := by
  have hF : ChainCheckFacts 1782 ((aStrong ()).extract 0 3) (aStrong ()) aBase aWords 1 :=
    chainCheckFacts (caseChainOK3_parts caseA_facts.chain).1
  have h2 : Rep 1782 (aStrong ())[2]! (permOfArr 1782 (aStrong ())[2]!) :=
    (rep_permOfArr (hF.strong_inv 2 (by rw [caseA_facts.size]; norm_num))).1
  have : permOfArr 1782 (aStrong ())[2]! = fuseXA := eq_of_eqA h2 rep_fuseXA caseA_facts.eqx
  rw [← this]
  exact h2

theorem rep_aT : Rep 1782 (rebuild (levels ()) tTuple) aPermT := rep_of_validA caseA_facts.valt

theorem rep_aU : Rep 1782 (rebuild (levels ()) uTuple) aPermU := rep_of_validA caseA_facts.valu

theorem rep_aV : Rep 1782 (rebuild (levels ()) vTuple) aPermV := rep_of_validA caseA_facts.valv

theorem card_aSub : Nat.card aSub = 9797760 := by
  have hchain := caseA_facts.chain
  rw [← aBs_map] at hchain
  have h := card_closure_three_of_chainOK (n := 1782) (S := aStrong ()) (bs := aBs)
    (W := aWords) (by norm_num) (by rw [caseA_facts.size]; norm_num) aBs_nodup rep_aA rep_aB
    rep_aX hchain
  rw [aBs_map, caseA_facts.orbits] at h
  exact h

theorem mem_aSub_of_sift {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G)
    (hs : siftA 1782 (rawLevels 1782 (aStrong ()) aBase) aBase 0 g = true) : G ∈ aSub := by
  have hchain := caseA_facts.chain
  rw [← aBs_map] at hchain hs
  exact mem_closure_three_of_siftG (n := 1782) (S := aStrong ()) (bs := aBs) (W := aWords)
    (by norm_num) (by rw [caseA_facts.size]; norm_num) aBs_nodup rep_aA rep_aB rep_aX hchain hG hs

theorem aSub_le : aSub ≤ Subgroup.centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM := by
  rw [aSub, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((commA_iff rep_aA rep_fuseXA).1 caseA_facts.comma), mem_suzM_of_inP rep_aA caseA_facts.ina⟩
  · exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((commA_iff rep_aB rep_fuseXA).1 caseA_facts.commb), mem_suzM_of_inP rep_aB caseA_facts.inb⟩
  · exact ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, fuseXA_mem⟩

theorem aPermT_mem : aPermT ∈ suzM := mem_suzM_of_inP rep_aT caseA_facts.int

theorem aPermT_conj : aPermT * fuseXA * aPermT⁻¹ = fuseXA ^ 2 := by
  have h := rep_conjA caseA_facts.valt rep_fuseXA
  have h2 := rep_compA rep_fuseXA rep_fuseXA
  rw [pow_two]
  exact eq_of_eqA h h2 caseA_facts.conjt

theorem card_fixStab_le : Nat.card (fixStab fuseXA ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782))) ≤
    19595520 := by
  have hA := smallChain_arrays
  have hF := chainCheckFacts smallChain_check.1
  have hQ := smallChain_valid
  have hbc : smallChain.baseCount = 6 := smallChain_baseCount
  set N := fixStab fuseXA with hNdef
  have hN : ∀ g ∈ N, ∀ q, fuseXA q = q → fuseXA (g q) = g q := fun g hg q hq => (hg q).1 hq
  have hlt : ∀ i, i < 6 → i < smallChain.baseCount := fun i hi => hbc ▸ hi
  have hfixi : ∀ i (hi : i < smallChain.baseCount), i < 5 →
      fuseXA (smallChain.base.get ⟨i, hi⟩) = smallChain.base.get ⟨i, hi⟩ := by
    intro i hi hi5
    have hb : (((smallChain.base.get ⟨i, hi⟩ : Fin 1782)) : ℕ) =
        smallBaseNat.toArray[i]! := hA.base_val ⟨i, hi⟩
    have h1 := allLt_spec caseA_facts.fixb hi5
    simp only [beq_iff_eq] at h1
    apply Fin.ext
    rw [← rep_fuseXA, hb]
    exact h1
  have c0 : fixLevCount 1782 (rawLevels 1782 smallStrongArrs smallBaseNat.toArray)
      (xAArr (levels ())) 0 = 162 := caseA_facts.c0
  have c1 : fixLevCount 1782 (rawLevels 1782 smallStrongArrs smallBaseNat.toArray)
      (xAArr (levels ())) 1 = 56 := caseA_facts.c1
  have c2 : fixLevCount 1782 (rawLevels 1782 smallStrongArrs smallBaseNat.toArray)
      (xAArr (levels ())) 2 = 10 := caseA_facts.c2
  have c3 : fixLevCount 1782 (rawLevels 1782 smallStrongArrs smallBaseNat.toArray)
      (xAArr (levels ())) 3 = 9 := caseA_facts.c3
  have c4 : fixLevCount 1782 (rawLevels 1782 smallStrongArrs smallBaseNat.toArray)
      (xAArr (levels ())) 4 = 8 := caseA_facts.c4
  have d5 : levCount 1782 (rawLevels 1782 smallStrongArrs smallBaseNat.toArray) 5 = 3 :=
    caseA_facts.d5
  have h0 := card_inf_levelSubgroup_le_fix hA hF hQ N rep_fuseXA hN (i := 0)
    (hlt 0 (by norm_num)) (hfixi 0 (hlt 0 (by norm_num)) (by norm_num))
  have h1 := card_inf_levelSubgroup_le_fix hA hF hQ N rep_fuseXA hN (i := 1)
    (hlt 1 (by norm_num)) (hfixi 1 (hlt 1 (by norm_num)) (by norm_num))
  have h2 := card_inf_levelSubgroup_le_fix hA hF hQ N rep_fuseXA hN (i := 2)
    (hlt 2 (by norm_num)) (hfixi 2 (hlt 2 (by norm_num)) (by norm_num))
  have h3 := card_inf_levelSubgroup_le_fix hA hF hQ N rep_fuseXA hN (i := 3)
    (hlt 3 (by norm_num)) (hfixi 3 (hlt 3 (by norm_num)) (by norm_num))
  have h4 := card_inf_levelSubgroup_le_fix hA hF hQ N rep_fuseXA hN (i := 4)
    (hlt 4 (by norm_num)) (hfixi 4 (hlt 4 (by norm_num)) (by norm_num))
  have h5 := card_inf_levelSubgroup_le_orb hA hF hQ N (i := 5) (hlt 5 (by norm_num))
  have h6 : Nat.card (N ⊓ smallChain.levelSubgroup 6 : Subgroup (Equiv.Perm (Fin 1782))) = 1 := by
    have := smallChain.levelSubgroup_terminal_eq_bot hQ
    rw [hbc] at this
    rw [this, inf_bot_eq, Subgroup.card_bot]
  rw [c0] at h0
  rw [c1] at h1
  rw [c2] at h2
  rw [c3] at h3
  rw [c4] at h4
  rw [d5] at h5
  rw [h6] at h5
  rw [smallChain.levelSubgroup_zero_eq_original hQ, smallChain_originalSubgroup] at h0
  calc Nat.card (N ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782)))
      ≤ 162 * Nat.card (N ⊓ smallChain.levelSubgroup 1 : Subgroup (Equiv.Perm (Fin 1782))) := h0
    _ ≤ 162 * (56 * Nat.card (N ⊓ smallChain.levelSubgroup 2 : Subgroup (Equiv.Perm (Fin 1782)))) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ 162 * (56 * (10 * Nat.card (N ⊓ smallChain.levelSubgroup 3 :
          Subgroup (Equiv.Perm (Fin 1782))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    _ ≤ 162 * (56 * (10 * (9 * Nat.card (N ⊓ smallChain.levelSubgroup 4 :
          Subgroup (Equiv.Perm (Fin 1782)))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3))
    _ ≤ 162 * (56 * (10 * (9 * (8 * Nat.card (N ⊓ smallChain.levelSubgroup 5 :
          Subgroup (Equiv.Perm (Fin 1782))))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ h4)))
    _ ≤ 162 * (56 * (10 * (9 * (8 * (3 * 1))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h5))))
    _ = 19595520 := by norm_num

theorem card_cent_le : Nat.card (Subgroup.centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓
    suzM : Subgroup (Equiv.Perm (Fin 1782))) ≤ 9797760 := by
  set C := (Subgroup.centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :
    Subgroup (Equiv.Perm (Fin 1782))) with hC
  set K := (fixStab fuseXA ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782))) with hK
  have hCK : C ≤ K := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨mem_fixStab_of_conj fuseXA_pow (e := 1) (Or.inl rfl) ?_, hg2⟩
    rw [pow_one]
    have := Subgroup.mem_centralizer_singleton_iff.1 hg1
    rw [this]
    group
  have htK : aPermT ∈ K :=
    ⟨mem_fixStab_of_conj fuseXA_pow (e := 2) (Or.inr rfl) aPermT_conj, aPermT_mem⟩
  have htC : aPermT ∉ C := by
    intro h
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 h.1
    have h2 : fuseXA ^ 2 = fuseXA := by
      rw [← aPermT_conj, h1]
      group
    apply fuseXA_ne_one
    have h3 : fuseXA * fuseXA = fuseXA * 1 := by rw [mul_one, ← pow_two, h2]
    exact mul_left_cancel h3
  have hlt : Nat.card C < Nat.card K := by
    by_contra hge
    push Not at hge
    exact htC ((Subgroup.eq_of_le_of_card_ge hCK hge) ▸ htK)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hCK
  have hcpos : 0 < Nat.card C := Nat.card_pos
  have hc2 : 2 ≤ c := by
    by_contra hlt2
    push Not at hlt2
    interval_cases c <;> omega
  have hKle := card_fixStab_le
  have : 2 * Nat.card C ≤ Nat.card K := by
    rw [hc]
    exact Nat.mul_le_mul_right _ hc2 |>.trans (by rw [mul_comm])
  have hKle' : Nat.card K ≤ 19595520 := hKle
  omega

theorem aSub_eq : aSub = Subgroup.centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :=
  Subgroup.eq_of_le_of_card_ge aSub_le (by rw [card_aSub]; exact card_cent_le)

theorem aA_mem : aPermA ∈ aSub := Subgroup.subset_closure (by simp)

theorem aB_mem : aPermB ∈ aSub := Subgroup.subset_closure (by simp)

theorem aX_mem : fuseXA ∈ aSub := Subgroup.subset_closure (by simp)

theorem aSub_quasisimple :
    CFSG.Open.IsQuasisimple ↥aSub ∧
      Subgroup.center ↥aSub = Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub) ∧
      Nonempty ((↥aSub ⧸ Subgroup.center ↥aSub) ≃* X₀) := by
  set z : ↥aSub := ⟨fuseXA, aX_mem⟩ with hzdef
  set a : ↥aSub := ⟨aPermA, aA_mem⟩ with hadef
  set b : ↥aSub := ⟨aPermB, aB_mem⟩ with hbdef
  have hu : aPermU ∈ aSub := mem_aSub_of_sift rep_aU caseA_facts.siftu
  have hv : aPermV ∈ aSub := mem_aSub_of_sift rep_aV caseA_facts.siftv
  set u : ↥aSub := ⟨aPermU, hu⟩ with hudef
  set v : ↥aSub := ⟨aPermV, hv⟩ with hvdef
  have hz : z ∈ Subgroup.center ↥aSub := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (aSub_le g.2).1
  have hz3 : z ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
  have hz1 : z ≠ 1 := fun h => fuseXA_ne_one (congrArg Subtype.val h)
  have hgen : Subgroup.closure ({a, b, z} : Set ↥aSub) = ⊤ := by
    have h : Subgroup.closure ((Subtype.val : ↥aSub → Equiv.Perm (Fin 1782)) ⁻¹'
        ({aPermA, aPermB, fuseXA} : Set (Equiv.Perm (Fin 1782)))) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hset : ((Subtype.val : ↥aSub → Equiv.Perm (Fin 1782)) ⁻¹'
        ({aPermA, aPermB, fuseXA} : Set (Equiv.Perm (Fin 1782)))) = ({a, b, z} : Set ↥aSub) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, hadef, hbdef, hzdef,
        Subtype.ext_iff]
    rw [hset] at h
    exact h
  have hcoe : ∀ w, ((evalW ![a, b] w : ↥aSub) : Equiv.Perm (Fin 1782)) =
      evalW ![aPermA, aPermB] w := fun w => coe_evalW_two aSub a b w
  have hrel : ∀ w ∈ rels, evalW ![a, b] w ∈ Subgroup.zpowers z := by
    intro w hw
    have hspec := wordModX_spec caseA_facts.vala caseA_facts.valb rep_fuseXA
      (caseA_facts.relsmod w hw)
    have hA : permOfArr 1782 (aStrong ())[0]! = aPermA := rfl
    have hB : permOfArr 1782 (aStrong ())[1]! = aPermB := rfl
    rw [hA, hB] at hspec
    rcases hspec with h1 | h2 | h3
    · have h4 : evalW ![a, b] w = 1 := Subtype.ext (by rw [hcoe, h1]; rfl)
      rw [h4]
      exact Subgroup.one_mem _
    · have h4 : evalW ![a, b] w = z := Subtype.ext (by rw [hcoe, h2])
      rw [h4]
      exact Subgroup.mem_zpowers z
    · have h4 : evalW ![a, b] w = z ^ 2 := Subtype.ext (by rw [hcoe, h3, pow_two]; rfl)
      rw [h4]
      exact Subgroup.npow_mem_zpowers z 2
  have huv : ⁅v, u⁆ = z := by
    apply Subtype.ext
    have h := rep_commutatorA caseA_facts.valv caseA_facts.valu
    exact eq_of_eqA h rep_fuseXA caseA_facts.comm
  exact u43_central_ext z a b u v hz hz3 hz1 hgen hrel card_aSub huv

theorem splitShapeAt_xA : SplitShapeAt 3 (⟨fuseXA, fuseXA_mem⟩ : ↥suzM) := by
  obtain ⟨hq, hcen, ⟨eT⟩⟩ := aSub_quasisimple
  set k : ↥suzM := ⟨fuseXA, fuseXA_mem⟩ with hk
  have hmap : (Subgroup.centralizer ({k} : Set ↥suzM)).map suzM.subtype = aSub := by
    rw [map_centralizer_subtype' suzM k]
    exact aSub_eq.symm
  let e : ↥(Subgroup.centralizer ({k} : Set ↥suzM)) ≃* ↥aSub :=
    ((Subgroup.centralizer ({k} : Set ↥suzM)).equivMapOfInjective suzM.subtype
      suzM.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have hz3 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
  have hz1 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ≠ 1 := fun h => fuseXA_ne_one (congrArg Subtype.val h)
  have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := orderOf_eq_prime hz3 hz1
  refine splitShapeAt_of_centralizer_equiv e hq ?_ ?_ (leafType_three_of_equiv_X₀' eT)
  · have h3 : IsPGroup 3 ↥(Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub)) := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    exact h3.of_equiv (MulEquiv.subgroupCongr hcen.symm)
  · exact ⟨3265920, by rw [card_aSub]⟩

end Main

end CFSG.HardMathSupport.Dickson.I271
