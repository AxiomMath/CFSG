module

public import CFSG.Sporadic.Schreier.Co1NormalThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Tree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Multi
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeBound
public import Certificates.Certificate17329
public import CFSG.Sporadic.Co1Block.XFixBase
public import CFSG.Sporadic.Schreier.Co1OuterImage

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeC CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F Matrix

section Group

theorem sq_mem_of_card_le {G : Type} [Group G] [Finite G] {K Q : Subgroup G} (hQK : Q ≤ K)
    {n : ℕ} (hn : 0 < n) (hQ : Nat.card Q = n) (hK : Nat.card K ≤ 2 * n) :
    ∀ y ∈ K, y ^ 2 ∈ Q := by
  intro y hy
  set Q' : Subgroup K := Q.subgroupOf K with hQ'
  have hcard : Nat.card Q' = n := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
  have hidx : Q'.index * n = Nat.card K := by
    rw [← hcard]
    exact Subgroup.index_mul_card Q'
  have hpos : 0 < Q'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : Q'.index ≤ 2 := by
    by_contra h
    have h3 : 3 * n ≤ Q'.index * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hy' : (⟨y, hy⟩ : K) ^ 2 ∈ Q' := by
    rcases (by omega : Q'.index = 1 ∨ Q'.index = 2) with h | h
    · have : Q' = ⊤ := Subgroup.index_eq_one.1 h
      rw [this]
      exact Subgroup.mem_top _
    · exact Subgroup.sq_mem_of_index_two h _
  exact hy'

theorem mem_of_sq_mem_of_pow_eq_one {G : Type} [Group G] {Q : Subgroup G} {y : G} {m : ℕ}
    (h2 : y ^ 2 ∈ Q) (h1 : y ^ (2 * m + 1) = 1) : y ∈ Q := by
  have : y = (y ^ 2) ^ (m + 1) := by
    calc y = y ^ (2 * m + 1) * y := by rw [h1, one_mul]
      _ = (y ^ 2) ^ (m + 1) := by rw [← pow_succ, ← pow_mul]; congr 1
  rw [this]
  exact Q.pow_mem h2 _

end Group

section Fix


@[expose] def fixSub (S : Set Vec24) : Subgroup GL24 where
  carrier := {g | ∀ w ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w}
  mul_mem' := by
    intro a b ha hb w hw
    rw [mulVec_mul', hb w hw, ha w hw]
  one_mem' := by
    intro w _
    exact mulVec_one' w
  inv_mem' := by
    intro a ha w hw
    have := inv_mulVec_mulVec a w
    rw [ha w hw] at this
    exact this

theorem mem_fixSub {S : Set Vec24} {g : GL24} :
    g ∈ fixSub S ↔ ∀ w ∈ S, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w := Iff.rfl

theorem mem_xFixList_iff {R : Native.Rows} {v : ℕ} :
    v ∈ xFixList R ↔ v ∈ certVecs.toList ∧ Native.act R v = v := by
  simp [xFixList, List.mem_filter]

theorem fixesAll_iff {R : Native.Rows} {F : List ℕ} :
    fixesAll R F = true ↔ ∀ v ∈ F, Native.act R v = v := by
  simp [fixesAll, List.all_eq_true]

theorem mem_xFix_iff {R : Native.Rows} {g : GL24} (hR : MRep R g) {w : Vec24} :
    w ∈ xFix g ↔ ∃ v ∈ xFixList R, toVecD 24 v = w := by
  constructor
  · rintro ⟨hw, hfix⟩
    obtain ⟨y, hy, hyw⟩ := exists_mem_of_certX hw
    refine ⟨y, mem_xFixList_iff.2 ⟨hy, ?_⟩, hyw⟩
    rw [← hyw, hR.mulVec y] at hfix
    exact toVecD_injective (act_lt R y) (lt_of_mem_certVecs hy) hfix
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hv1, hv2⟩ := mem_xFixList_iff.1 hv
    refine ⟨toVecD_mem_certX hv1, ?_⟩
    rw [hR.mulVec v, hv2]

theorem mulVec_mem_xFix {x c : GL24} (hc : c ∈ GA) (hcx : c * x = x * c) {w : Vec24}
    (hw : w ∈ xFix x) : ((c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w ∈ xFix x := by
  refine ⟨mulVec_mem_certX hc hw.1, ?_⟩
  rw [← mulVec_mul', ← hcx, mulVec_mul', hw.2]

theorem conj_mem_fixSub {x c y : GL24}
    (hc : c ∈ Subgroup.centralizer ({x} : Set GL24) ⊓ GA) (hy : y ∈ fixSub (xFix x)) :
    c * y * c⁻¹ ∈ fixSub (xFix x) := by
  have h := Subgroup.mem_inf.1 hc
  have h0 : c⁻¹ ∈ Subgroup.centralizer ({x} : Set GL24) :=
    (Subgroup.centralizer ({x} : Set GL24)).inv_mem h.1
  have hcx' : c⁻¹ * x = x * c⁻¹ :=
    (Subgroup.mem_centralizer_singleton_iff (g := x) (k := c⁻¹)).1 h0
  rw [mem_fixSub]
  intro w hw
  have h1 := mulVec_mem_xFix (GA.inv_mem h.2) hcx' hw
  have h2 := inv_mulVec_mulVec c⁻¹ w
  rw [inv_inv] at h2
  rw [mulVec_mul', mulVec_mul', (mem_fixSub.1 hy) _ h1]
  exact h2

end Fix

section Tree

variable {Gs : List Native.Rows} {gens : List GL24}

theorem exists_rep_pts (hG : List.Forall₂ MRep Gs gens) {cap : ℕ}
    (h : gtOK Gs.toArray (gtBFS Gs.toArray cap) = true) :
    ∃ βs : List GL24, List.Forall₂ MRep (gtBFS Gs.toArray cap).pts.toList βs ∧
      ∀ β ∈ βs, β ∈ Subgroup.closure {g | g ∈ gens} := by
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq valHom valHom_injective h
    (fun l => gens.getD l 1) (rep_arr hG)
  have hsz := size_eq_of_rep hG
  rw [hsz, image_getD_lt] at heq
  set n := (gtBFS Gs.toArray cap).pts.size with hn
  refine ⟨(List.range n).map f, ?_, ?_⟩
  · rw [List.forall₂_iff_get]
    refine ⟨by simp [hn], fun i h1 h2 => ?_⟩
    have hi : i < n := by simpa [hn] using h1
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, Array.getElem_toList]
    have := hf i hi
    rw [getElem!_pos _ i hi] at this
    exact this.symm
  · intro β hβ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hβ
    have : f i ∈ (Subgroup.closure {g | g ∈ gens} : Set GL24) := by
      rw [heq]
      exact ⟨i, by simpa using hi, rfl⟩
    exact this

end Tree

section Abstract

theorem pConstrained_of_index_two {G : Type} [Group G] [Finite G] (A : Subgroup G) (x : G)
    (K Q : Subgroup G) (hKC : K ≤ Subgroup.centralizer ({x} : Set G) ⊓ A)
    (hKn : ∀ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ A, ∀ y ∈ K, c * y * c⁻¹ ∈ K)
    (hQK : Q ≤ K) (hQ : Nat.card Q = 243) (hK : Nat.card K ≤ 2 * 243) (hxQ : x ∈ Q)
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hcent : Nat.card ↥(Subgroup.centralizer (Q : Set G) ⊓ A) ≤ 3) :
    PConstrainedShape 3 (Subgroup.centralizer ({x} : Set G) ⊓ A) := by
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ A with hC
  have hsq : ∀ y ∈ K, y ^ 2 ∈ Q := sq_mem_of_card_le hQK (by norm_num) hQ hK
  have hQpow : ∀ q ∈ Q, q ^ 243 = 1 := by
    intro q hq
    have h1 : (⟨q, hq⟩ : Q) ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [hQ] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    refine mem_of_sq_mem_of_pow_eq_one (m := 121) (hsq _ (hKn c hc q (hQK hq))) ?_
    rw [conj_pow, show 2 * 121 + 1 = 243 from rfl, hQpow q hq]
    group
  have hxA : x ∈ A := (hKC (hQK hxQ)).2
  have hxc : ∀ q ∈ Q, q * x = x * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKC (hQK hq)).1
  have hxZ : x ∈ Subgroup.centralizer (Q : Set G) ⊓ A :=
    ⟨Subgroup.mem_centralizer_iff.2 fun q hq => hxc q hq, hxA⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (Q : Set G) ⊓ A :=
    Subgroup.zpowers_le.2 hxZ
  have hcard : Nat.card ↥(Subgroup.centralizer (Q : Set G) ⊓ A) ≤
      Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, hord]
    exact hcent
  have heq : Subgroup.zpowers x = Subgroup.centralizer (Q : Set G) ⊓ A :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  refine pConstrainedShape_of_normal_pgroup (fun y hy => hKC (hQK hy))
    (normalSubgroupOf_of_conj_aux hQn) (IsPGroup.of_card (n := 5) (by rw [hQ]; norm_num)) ?_
  intro g hg
  obtain ⟨hg1, hg2⟩ := hg
  have hgZ : g ∈ Subgroup.centralizer (Q : Set G) ⊓ A := ⟨hg1, (Subgroup.mem_inf.1 hg2).2⟩
  rw [← heq] at hgZ
  exact Subgroup.zpowers_le.2 hxQ hgZ

end Abstract

section Data


theorem mem_fixSub_of_fixesAll {Rg R : Native.Rows} {g y : GL24} (hg : MRep Rg g)
    (hy : MRep R y) (h : fixesAll R (xFixList Rg) = true) : y ∈ fixSub (xFix g) := by
  rw [mem_fixSub]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := (mem_xFix_iff hg).1 hw
  rw [hy.mulVec v, fixesAll_iff.1 h v hv]

theorem threeC_shape {x : GL24} (hx : MRep (rootRows3C ()) x) :
    PConstrainedShape 3 (Subgroup.centralizer ({x} : Set GL24) ⊓ GA) := by
  have h := (Certificates.certificate17329 : threeCCheck () = true)
  simp only [threeCCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc, List.all_eq_true, List.mem_range] at h
  obtain ⟨hD, hwx, hw1, hx1, hx3, hxq, hc1, hc2, hc3, hc4, hQok, hQsz, hf1, hf2, hf3, hf4, hFb,
    hb1, hcnt1, hb2, hcnt2⟩ := h
  haveI : Finite GL24 := inferInstance
  have rq1 := rep_nd (ext := TabCo1ThreeC.ext) hD 88
  have rq2 := rep_nd (ext := TabCo1ThreeC.ext) hD 89
  have rq3 := rep_nd (ext := TabCo1ThreeC.ext) hD 90
  have rq4 := rep_nd (ext := TabCo1ThreeC.ext) hD 91
  have rq1i := rep_ndI (ext := TabCo1ThreeC.ext) hD 88
  have rq2i := rep_ndI (ext := TabCo1ThreeC.ext) hD 89
  have hG := List.Forall₂.cons rq1 (List.Forall₂.cons rq2 (List.Forall₂.cons rq3
    (List.Forall₂.cons rq4 List.Forall₂.nil)))
  have hF1 := mem_fixSub_of_fixesAll hx rq1 hf1
  have hF2 := mem_fixSub_of_fixesAll hx rq2 hf2
  have hF3 := mem_fixSub_of_fixesAll hx rq3 hf3
  have hF4 := mem_fixSub_of_fixesAll hx rq4 hf4
  have cm1 := (hx.mul rq1).eq (by rw [hc1]; exact rq1.mul hx)
  have cm2 := (hx.mul rq2).eq (by rw [hc2]; exact rq2.mul hx)
  have cm3 := (hx.mul rq3).eq (by rw [hc3]; exact rq3.mul hx)
  have cm4 := (hx.mul rq4).eq (by rw [hc4]; exact rq4.mul hx)
  have hxe : x = kG TabCo1ThreeC.ext 88 * kG TabCo1ThreeC.ext 89 *
      ((kG TabCo1ThreeC.ext 88)⁻¹ * (kG TabCo1ThreeC.ext 89)⁻¹) :=
    hx.eq (by rw [hxq]; exact (rq1.mul rq2).mul (rq1i.mul rq2i))
  have hx3' : x ^ 3 = 1 := (hx.pow 3).eq (by rw [hx3]; exact MRep.one)
  have hx1' : x ≠ 1 := ne_one_of_rep hx hwx hw1 hx1
  have hpt : Nat.card ↥(Subgroup.centralizer
      (Subgroup.closure {g | g ∈ [kG TabCo1ThreeC.ext 88, kG TabCo1ThreeC.ext 89,
        kG TabCo1ThreeC.ext 90, kG TabCo1ThreeC.ext 91]} : Set GL24) ⊓ GA) ≤ 3 := by
    obtain ⟨βs, hβs, hβQ⟩ := exists_rep_pts hG hQok
    have hcomm : ∀ g ∈ Subgroup.centralizer
        (Subgroup.closure {g | g ∈ [kG TabCo1ThreeC.ext 88, kG TabCo1ThreeC.ext 89,
          kG TabCo1ThreeC.ext 90, kG TabCo1ThreeC.ext 91]} : Set GL24) ⊓ GA,
        ∀ β ∈ βs, g * β = β * g := by
      intro g hg β hβ
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).1 β (hβQ β hβ)).symm
    have hlen : (gtBFS [nd (kDag TabCo1ThreeC.ext) 88, nd (kDag TabCo1ThreeC.ext) 89,
        nd (kDag TabCo1ThreeC.ext) 90, nd (kDag TabCo1ThreeC.ext) 91].toArray 300).pts.toList.length
        = 243 := by
      simpa using hQsz
    exact (card_le_of_listBound hβs inf_le_right hcomm hlen hb2).trans hcnt2
  set K : Subgroup GL24 := Subgroup.centralizer ({x} : Set GL24) ⊓ GA ⊓ fixSub (xFix x) with hK
  set Q : Subgroup GL24 := Subgroup.closure {g | g ∈ [kG TabCo1ThreeC.ext 88,
    kG TabCo1ThreeC.ext 89, kG TabCo1ThreeC.ext 90, kG TabCo1ThreeC.ext 91]} with hQ
  have hKC : K ≤ Subgroup.centralizer ({x} : Set GL24) ⊓ GA := inf_le_left
  have hKn : ∀ c ∈ Subgroup.centralizer ({x} : Set GL24) ⊓ GA, ∀ y ∈ K, c * y * c⁻¹ ∈ K := by
    intro c hc y hy
    obtain ⟨hyC, hyF⟩ := hy
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hyC) (Subgroup.inv_mem _ hc),
      conj_mem_fixSub hc hyF⟩
  have hcm : ∀ q : GL24, x * q = q * x → q ∈ GA → q ∈ fixSub (xFix x) → q ∈ K :=
    fun q hq hA hF => ⟨⟨Subgroup.mem_centralizer_singleton_iff.2 hq.symm, hA⟩, hF⟩
  have hQK : Q ≤ K := by
    refine (Subgroup.closure_le K).2 ?_
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hcm _ cm1 (kG_mem _ 88) hF1
    · exact hcm _ cm2 (kG_mem _ 89) hF2
    · exact hcm _ cm3 (kG_mem _ 90) hF3
    · exact hcm _ cm4 (kG_mem _ 91) hF4
  have hQcard : Nat.card Q = 243 := by
    rw [hQ, card_closure_list hG hQok, hQsz]
  have hxQ : x ∈ Q := by
    have m1 : kG TabCo1ThreeC.ext 88 ∈ Q := Subgroup.subset_closure (by simp)
    have m2 : kG TabCo1ThreeC.ext 89 ∈ Q := Subgroup.subset_closure (by simp)
    rw [hxe]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m2)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ m1) (Subgroup.inv_mem _ m2))
  have hfix : ∀ g ∈ K, ∀ i < 6, ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      toVecD 24 (TabCo1ThreeC.base.getD i 0) = toVecD 24 (TabCo1ThreeC.base.getD i 0) := by
    intro g hg i hi
    have hmem : toVecD 24 (TabCo1ThreeC.base.getD i 0) ∈ xFix x :=
      (mem_xFix_iff hx).2 ⟨_, List.mem_of_elem_eq_true (hFb i hi), rfl⟩
    exact (mem_fixSub.1 hg.2) _ hmem
  have hKcard : Nat.card K ≤ 2 * 243 :=
    (card_le_of_powBoundF (H := K) (hKC.trans inf_le_right) hx 3 6 (hKC.trans inf_le_left) hfix
      hb1).trans hcnt1
  exact pConstrained_of_index_two GA x K Q hKC hKn hQK hQcard hKcard hxQ hx3' hx1' hpt

end Data

section Final


theorem tabCo1_threeC (x : ↥GA) (hx : MRep (rootRows3C ()) (x : GL24)) :
    PConstrainedShape 3 (Subgroup.centralizer ({x} : Set ↥GA)) := by
  haveI : Finite ↥GA := finite_GA
  refine pConstrainedShape_of_map_injective GA.subtype GA.subtype_injective ?_
  rw [map_centralizer_subtype' GA x]
  exact threeC_shape hx

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1
