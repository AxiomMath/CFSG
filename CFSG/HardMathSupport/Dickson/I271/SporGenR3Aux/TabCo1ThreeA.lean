module

public import CFSG.Sporadic.Schreier.Co1NormalThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeBound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeASuz
public import Certificates.Certificate17620

public section

namespace CFSG.HardMathSupport.Dickson.I271

section Words

open CFSG.Sporadic.Bridge.SuzGPL.Native CFSG.Sporadic.Co1Schreier

theorem letterG_relLetter (gs : List GL24) (l : ℕ × Bool) :
    CFSG.Sporadic.Co1Schreier.letterG gs (relLetter l) =
      if l.2 then gs.getD l.1 1 else (gs.getD l.1 1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b
  · have h1 : ¬ (0 : ℤ) < -((i : ℤ) + 1) := by omega
    have h2 : (-(-((i : ℤ) + 1))).toNat - 1 = i := by omega
    simp only [CFSG.Sporadic.Co1Schreier.letterG, relLetter, h1, if_false, h2, Bool.false_eq_true]
  · have h1 : (0 : ℤ) < (i : ℤ) + 1 := by omega
    have h2 : ((i : ℤ) + 1).toNat - 1 = i := by omega
    simp only [CFSG.Sporadic.Co1Schreier.letterG, relLetter, h1, if_true, h2]

theorem wordG_map_relLetter (gs : List GL24) (v : List (ℕ × Bool)) :
    CFSG.Sporadic.Co1Schreier.wordG gs (v.map relLetter) =
      CFSG.Sporadic.Bridge.wordProd (fun i => gs.getD i 1) v := by
  have key : ∀ (v : List (ℕ × Bool)) (acc : GL24),
      (v.map relLetter).foldl (fun x j => x * CFSG.Sporadic.Co1Schreier.letterG gs j) acc =
        acc * CFSG.Sporadic.Bridge.wordProd (fun i => gs.getD i 1) v := by
    intro v
    induction v with
    | nil => intro acc; simp [CFSG.Sporadic.Bridge.wordProd]
    | cons l v ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, ih, letterG_relLetter]
      by_cases hb : l.2
      · simp [CFSG.Sporadic.Bridge.wordProd, hb, mul_assoc]
      · simp [CFSG.Sporadic.Bridge.wordProd, hb, mul_assoc]
  unfold CFSG.Sporadic.Co1Schreier.wordG
  rw [key, one_mul]

theorem rels_words_eq_suz :
    (rels ()).map (List.map relLetter) =
      CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA.relsS := by
  decide

theorem pow_three_of_mem_zpowers {G : Type} [Group G] {x : G} (hx : x ^ 3 = 1) {c : G}
    (hc : c ∈ Subgroup.zpowers x) : c ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

end Words

section Abstract

open CFSG.Sporadic.Bridge TauCeti
open scoped commutatorElement


theorem suz_centralizer_data {G : Type} [Group G] [Finite G] (A : Subgroup G) (x : G) (g : ℕ → G)
    (u w : G) (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* SporadicName.Suz.Group))
    (hxA : x ∈ A) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hgC : ∀ i, g i ∈ Subgroup.centralizer ({x} : Set G) ⊓ A)
    (huC : u ∈ Subgroup.centralizer ({x} : Set G) ⊓ A)
    (hwC : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ A) (hcomm : u⁻¹ * w⁻¹ * (u * w) = x)
    (hnc : g 0 * g 1 ≠ g 1 * g 0)
    (hrel : ∀ v ∈ SporadicName.Suz.presentation.relatorLetters,
      wordProd g v = 1 ∨ wordProd g v = x ∨ wordProd g v = x ^ 2)
    (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ A) ≤ 1345036492800) :
    ∃ J : Subgroup G, J ≤ Subgroup.centralizer ({x} : Set G) ⊓ A ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ A, ∀ l ∈ J, c * l * c⁻¹ ∈ J) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card ↥J ∧ Nat.card ↥(Subgroup.center ↥J) = 3 ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ A, (∀ l ∈ J, l * c = c * l) → c ^ 3 = 1) ∧
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 448345497600 ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* SporadicName.Suz.Group) := by
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer ({x} : Set G) ⊓ A := ⟨_, rfl⟩
  rw [← hCdef] at hgC huC hwC hC ⊢
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subgroup G, T₀ = Subgroup.closure (insert x (Set.range g)) :=
    ⟨_, rfl⟩
  have hx1C : ∀ y ∈ C, y * x = x * y := fun y hy => by
    rw [hCdef] at hy
    exact Subgroup.mem_centralizer_singleton_iff.1 hy.1
  have hxC : x ∈ C := by
    rw [hCdef]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hxA⟩
  have hTC : T₀ ≤ C := by
    rw [hT₀, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | ⟨i, rfl⟩
    · exact hxC
    · exact hgC i
  have hxT : x ∈ T₀ := by rw [hT₀]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hgT : ∀ i, g i ∈ T₀ := fun i => by
    rw [hT₀]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Subgroup G, Zs = Subgroup.zpowers x := ⟨_, rfl⟩
  have hxZs : x ∈ Zs := by rw [hZs]; exact Subgroup.mem_zpowers x
  have hZsT : Zs ≤ T₀ := by rw [hZs]; exact Subgroup.zpowers_le.2 hxT
  have hZsc : ∀ y ∈ T₀, ∀ z ∈ Zs, y * z = z * y := by
    intro y hy z hz
    rw [hZs] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((Commute.zpow_right (show Commute y x from hx1C y (hTC hy)) k)).eq
  obtain ⟨Z', hZ'⟩ : ∃ Z' : Subgroup ↥T₀, Z' = Zs.subgroupOf T₀ := ⟨_, rfl⟩
  have hZ'mem : ∀ y : ↥T₀, y ∈ Z' ↔ (y : G) ∈ Zs := fun y => by
    rw [hZ', Subgroup.mem_subgroupOf]
  have hZc : Z' ≤ Subgroup.center ↥T₀ := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro t
    exact Subtype.ext (hZsc t t.2 y ((hZ'mem y).1 hy))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have cardZs : Nat.card ↥Zs = 3 := by
    rw [hZs, Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have cardZ' : Nat.card ↥Z' = 3 := by
    rw [hZ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZsT).toEquiv]
    exact cardZs
  let gT : ℕ → ↥T₀ := fun i => ⟨g i, hgT i⟩
  have hrelT : ∀ v ∈ SporadicName.Suz.presentation.relatorLetters, wordProd gT v ∈ Z' := by
    intro v hv
    rw [hZ'mem, coe_wordProd]
    show wordProd g v ∈ Zs
    rcases hrel v hv with h | h | h
    · rw [h]; exact Zs.one_mem
    · rw [h]; exact hxZs
    · rw [h]; exact Zs.pow_mem hxZs 2
  have hncT : gT 0 * gT 1 ≠ gT 1 * gT 0 := fun h => hnc (congrArg Subtype.val h)
  have hcardT : Nat.card ↥T₀ ≤ Nat.card ↥Z' * 448345497600 := by
    have := Subgroup.card_le_of_le hTC
    rw [cardZ']
    omega
  haveI : Z'.Normal := Subgroup.normal_of_le_center hZc
  obtain ⟨hcen, hqcard, -⟩ := suz_central_quot hb Z' gT hZc hrelT hncT hcardT
  have hTcard : Nat.card ↥T₀ = 1345036492800 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z', hqcard, cardZ']
  have hTCeq : T₀ = C := Subgroup.eq_of_le_of_card_ge hTC (by rw [hTcard]; exact hC)
  have huT : u ∈ T₀ := by rw [hTCeq]; exact huC
  have hwT : w ∈ T₀ := by rw [hTCeq]; exact hwC
  have hZK : Z' ≤ commutator ↥T₀ := by
    obtain ⟨Cm, hCm⟩ : ∃ Cm : Subgroup G, Cm = (commutator ↥T₀).map T₀.subtype := ⟨_, rfl⟩
    have hxCm : x ∈ Cm := by
      rw [hCm]
      refine ⟨⁅(⟨u, huT⟩ : ↥T₀)⁻¹, (⟨w, hwT⟩ : ↥T₀)⁻¹⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
      show (((⁅(⟨u, huT⟩ : ↥T₀)⁻¹, (⟨w, hwT⟩ : ↥T₀)⁻¹⁆ : ↥T₀)) : G) = x
      rw [← hcomm]
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_assoc]
    have hZsCm : Zs ≤ Cm := by rw [hZs]; exact Subgroup.zpowers_le.2 hxCm
    intro y hy
    have hyCm : (y : G) ∈ Cm := hZsCm ((hZ'mem y).1 hy)
    rw [hCm] at hyCm
    obtain ⟨c, hc, hcy⟩ := hyCm
    have : c = y := Subtype.ext hcy
    rw [← this]
    exact hc
  obtain ⟨hq, hcen', ⟨eT⟩⟩ := suz_central_ext hb Z' gT hZc hrelT hncT hZK hcardT
  have hcard3 : Nat.card ↥(Subgroup.center ↥T₀) = 3 := by rw [hcen']; exact cardZ'
  have hqcard' : Nat.card (↥T₀ ⧸ Subgroup.center ↥T₀) = 448345497600 := by
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcen').toEquiv]
    exact hqcard
  refine ⟨T₀, hTC, ?_, hq, ⟨448345497600, by rw [hTcard]⟩, hcard3, ?_, hqcard', ⟨eT⟩⟩
  · intro c hc l hl
    have hcT : c ∈ T₀ := by rw [hTCeq]; exact hc
    exact T₀.mul_mem (T₀.mul_mem hcT hl) (T₀.inv_mem hcT)
  · intro c hc hcl
    have hcT : c ∈ T₀ := by rw [hTCeq]; exact hc
    have hcz : (⟨c, hcT⟩ : ↥T₀) ∈ Subgroup.center ↥T₀ := by
      rw [Subgroup.mem_center_iff]
      intro t
      exact Subtype.ext (hcl t t.2)
    rw [hcen'] at hcz
    have hcZs : c ∈ Zs := (hZ'mem _).1 hcz
    rw [hZs] at hcZs
    exact pow_three_of_mem_zpowers hx3 hcZs

end Abstract

end CFSG.HardMathSupport.Dickson.I271

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeA CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271

section Data


theorem threeA_data
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* TauCeti.SporadicName.Suz.Group))
    {x : GL24} (hx : MRep (rootRows3A ()) x) :
    ∃ J : Subgroup GL24, J ≤ Subgroup.centralizer ({x} : Set GL24) ⊓ GA ∧
      (∀ g ∈ Subgroup.centralizer ({x} : Set GL24) ⊓ GA, ∀ l ∈ J, g * l * g⁻¹ ∈ J) ∧
      CFSG.Open.IsQuasisimple ↥J ∧ 3 ∣ Nat.card ↥J ∧ Nat.card ↥(Subgroup.center ↥J) = 3 ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set GL24) ⊓ GA, (∀ l ∈ J, l * c = c * l) → c ^ 3 = 1) ∧
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 448345497600 ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* TauCeti.SporadicName.Suz.Group) := by
  have h := (Certificates.certificate17620 : threeACheck () = true)
  simp only [threeACheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, and_assoc, List.all_eq_true] at h
  obtain ⟨hD, hwx, hw1, hxr, hx1, hx3, hcm, hxu, hxw, hw01, hw10, hg01, hrels, hcomm, hb1,
    hcnt1⟩ := h
  haveI : Finite GL24 := inferInstance
  have rx := rep_nd (ext := TabCo1ThreeA.ext) hD 95
  have hxe : x = kG TabCo1ThreeA.ext 95 := hx.eq (by rw [← hxr]; exact rx)
  subst hxe
  have ra := rep_nd (ext := TabCo1ThreeA.ext) hD 88
  have rb := rep_nd (ext := TabCo1ThreeA.ext) hD 89
  have ru := rep_nd (ext := TabCo1ThreeA.ext) hD 96
  have rw' := rep_nd (ext := TabCo1ThreeA.ext) hD 97
  have rui := rep_ndI (ext := TabCo1ThreeA.ext) hD 96
  have rwi := rep_ndI (ext := TabCo1ThreeA.ext) hD 97
  have hx3' : kG TabCo1ThreeA.ext 95 ^ 3 = 1 := (rx.pow 3).eq (by rw [hx3]; exact MRep.one)
  have hx1' : kG TabCo1ThreeA.ext 95 ≠ 1 := by
    intro h
    apply hx1
    have h1 : MRep (nd (kDag TabCo1ThreeA.ext) 95) 1 := h ▸ rx
    exact rowsMatrix_injective_of_wf hwx hw1 (h1.trans MRep.one.symm)
  have hcomm' : (kG TabCo1ThreeA.ext 96)⁻¹ * (kG TabCo1ThreeA.ext 97)⁻¹ *
      (kG TabCo1ThreeA.ext 96 * kG TabCo1ThreeA.ext 97) = kG TabCo1ThreeA.ext 95 :=
    ((rui.mul rwi).mul (ru.mul rw')).eq (by rw [hcomm]; exact rx)
  have cxu : kG TabCo1ThreeA.ext 96 * kG TabCo1ThreeA.ext 95 =
      kG TabCo1ThreeA.ext 95 * kG TabCo1ThreeA.ext 96 :=
    (ru.mul rx).eq (by rw [← hxu]; exact rx.mul ru)
  have cxw : kG TabCo1ThreeA.ext 97 * kG TabCo1ThreeA.ext 95 =
      kG TabCo1ThreeA.ext 95 * kG TabCo1ThreeA.ext 97 :=
    (rw'.mul rx).eq (by rw [← hxw]; exact rx.mul rw')
  have hnc0 : kG TabCo1ThreeA.ext 88 * kG TabCo1ThreeA.ext 89 ≠
      kG TabCo1ThreeA.ext 89 * kG TabCo1ThreeA.ext 88 := by
    intro h
    apply hg01
    have h1 : MRep (Native.mul (nd (kDag TabCo1ThreeA.ext) 88) (nd (kDag TabCo1ThreeA.ext) 89))
        (kG TabCo1ThreeA.ext 89 * kG TabCo1ThreeA.ext 88) := h ▸ ra.mul rb
    exact rowsMatrix_injective_of_wf hw01 hw10 (h1.trans (rb.mul ra).symm)
  have hgi : ∀ i ∈ [88, 89, 90, 91, 92, 93, 94], kG TabCo1ThreeA.ext i ∈
      Subgroup.centralizer ({kG TabCo1ThreeA.ext 95} : Set GL24) ⊓ GA := by
    intro i hi
    have ri := rep_nd (ext := TabCo1ThreeA.ext) hD i
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2
      ((ri.mul rx).eq (by rw [← hcm i hi]; exact rx.mul ri)), kG_mem _ i⟩
  have hgC : ∀ i, ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD i 1 ∈
      Subgroup.centralizer ({kG TabCo1ThreeA.ext 95} : Set GL24) ⊓ GA := by
    refine fun i => getD_mem_of_forall (fun y hy => ?_) i
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact hgi j hj
  have hrelv : ∀ v ∈ TauCeti.SporadicName.Suz.presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd
        (fun i => ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD i 1) v = 1 ∨
      CFSG.Sporadic.Bridge.wordProd
        (fun i => ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD i 1) v =
          kG TabCo1ThreeA.ext 95 ∨
      CFSG.Sporadic.Bridge.wordProd
        (fun i => ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD i 1) v =
          kG TabCo1ThreeA.ext 95 ^ 2 := by
    intro v hv
    rw [suz_relatorLetters_eq] at hv
    have hmem : v.map CFSG.Sporadic.Bridge.SuzGPL.Native.relLetter ∈ TabCo1ThreeA.relsS := by
      rw [← rels_words_eq_suz]
      exact List.mem_map.2 ⟨v, hv, rfl⟩
    rw [← wordG_map_relLetter]
    have hrep := rep_evalW (ext := TabCo1ThreeA.ext) hD [88, 89, 90, 91, 92, 93, 94]
      (v.map CFSG.Sporadic.Bridge.SuzGPL.Native.relLetter)
    rcases hrels _ hmem with (h | h) | h
    · left
      exact hrep.eq (by rw [h]; exact MRep.one)
    · right; left
      exact hrep.eq (by rw [h]; exact rx)
    · right; right
      exact hrep.eq (by rw [h]; exact rx.pow 2)
  have hnc : ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD 0 1 *
      ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD 1 1 ≠
      ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD 1 1 *
      ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD 0 1 := by
    have e0 : ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD 0 1 =
        kG TabCo1ThreeA.ext 88 := by simp [List.getD_eq_getElem?_getD]
    have e1 : ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD 1 1 =
        kG TabCo1ThreeA.ext 89 := by simp [List.getD_eq_getElem?_getD]
    rw [e0, e1]
    exact hnc0
  have hCcard : Nat.card ↥(Subgroup.centralizer ({kG TabCo1ThreeA.ext 95} : Set GL24) ⊓ GA) ≤
      1345036492800 := (card_cent_le_of_powBoundN rx 3 hb1).trans hcnt1
  exact suz_centralizer_data GA (kG TabCo1ThreeA.ext 95)
    (fun i => ([88, 89, 90, 91, 92, 93, 94].map (kG TabCo1ThreeA.ext)).getD i 1)
    (kG TabCo1ThreeA.ext 96) (kG TabCo1ThreeA.ext 97) hb (kG_mem _ 95) hx3' hx1' hgC
    ⟨Subgroup.mem_centralizer_singleton_iff.2 cxu, kG_mem _ 96⟩
    ⟨Subgroup.mem_centralizer_singleton_iff.2 cxw, kG_mem _ 97⟩ hcomm' hnc hrelv hCcard

end Data

end CFSG.HardMathSupport.Dickson.I271.TabCo1
