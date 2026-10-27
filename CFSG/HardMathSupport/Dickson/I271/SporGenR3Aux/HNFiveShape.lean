module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNThreeShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveSolv
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveNoComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveKer
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFiveOrders
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.Adapters.StatedSmallProjOrders

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.HNSchreier
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open scoped commutatorElement

section Chev

theorem isChevSimple_of_statedPSU {G : Type} [Group G] {n p f : ℕ}
    (h : StatedClassicalModel G .PSU n p f) : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  letI := hfield
  letI := hfinite
  obtain ⟨hp, hf, hn, h32⟩ := hadm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = (p ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hcharP : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hKcard, ← pow_mul, mul_comm])
  have hring : ringChar K = p := ringChar.eq K p
  have hFD := suFactorFacts_holds K n (p ^ f) hKcard hn h32
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := p)
    (f := f) (n := n) hK hn h32
  have hch := hFD.chev
  rw [hring] at hch
  have e2 : ↥(StatedSU n (p ^ f) K) ⧸ Subgroup.center ↥(StatedSU n (p ^ f) K) ≃*
      StatedProj (StatedSU n (p ^ f) K) := QuotientGroup.quotientMulEquivOfEq hq.2
  exact isChevSimple_of_mulEquiv (e2.trans e.symm) hch

end Chev

section Five

open CFSG.Sporadic.HNOddCore CFSG.RankThree.PartOne.HNB


theorem leafType_five_IJ : LeafType 5 ↥IJ := by
  have hcard : Nat.card ↥IJ = 126000 := (ctuc_hn_five_centralizer_perfect_factor).2.2.2.2.2.1
  refine Or.inl ⟨isChevSimple_of_statedPSU model_IJ, ?_, ?_⟩
  · intro h
    obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := h
    have h2 : Nat.card (StatedProj (StatedSL 2 F)) = 9828 := by
      rw [CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
      norm_num
    rw [Nat.card_congr e'.toEquiv, h2] at hcard
    omega
  · rintro ⟨f⟩
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup] at hcard
    simp [Nat.factorial] at hcard

theorem shape_f : ShapeRkAt 5 (LeafType 5) (fun _ _ => True) fJ := by
  obtain ⟨hcomm, -, -, -, hC, hcardI, -, hder, -⟩ := ctuc_hn_five_centralizer_perfect_factor
  haveI hsimple : IsSimpleGroup ↥IJ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity IJ 3 5 1 model_IJ).2
  have hLC : IJ ≤ Subgroup.centralizer ({fJ} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm fJ (Subgroup.mem_zpowers _) x hx).symm
  have hnp : ¬ (Nat.card ↥IJ).Prime := by
    rw [hcardI]
    norm_num
  have hnab : ∃ a b : ↥IJ, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥IJ) hnp
  have h5 : 5 ∣ Nat.card ↥IJ := by
    rw [hcardI]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({fJ} : Set ↥JH)) = Nat.card ↥IJ * 5 ^ 1 := by
    rw [hC, hcardI]
    norm_num
  refine shapeRkAt_of_data Nat.prime_five (fun _ _ _ _ e h => LeafType.of_equiv e h)
    (fun _ _ _ _ _ h => h) fJ IJ hLC ?_ hsimple hnab h5 hk leafType_five_IJ trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈
      ⁅Subgroup.centralizer ({fJ} : Set ↥JH), Subgroup.centralizer ({fJ} : Set ↥JH)⁆ :=
    Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact IJ.mul_mem h1 hl

end Five

section General

theorem shapeRkAt'_mono {p : ℕ} {Good Rk Good' Rk' : ∀ (T : Type) [Group T], Prop}
    (hG : ∀ (T : Type) [Group T], Good T → Good' T) (hR : ∀ (T : Type) [Group T], Rk T → Rk' T)
    {Q : Type} [Group Q] {k : Q} (h : ShapeRkAt' p Good Rk k) : ShapeRkAt' p Good' Rk' k := by
  rcases h with h | ⟨J, hJ, hu, hg, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨J, hJ, hu, hG _ hg, hR _ hr⟩

theorem centShapeRk'_of_equiv_JH {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (e : S ≃* ↥JH) (h : CentShapeRk' p Good Rk ↥JH) : CentShapeRk' p Good Rk S :=
  @CentShapeRk'.of_equiv ↥JH S (inferInstance : Group ↥JH) (inferInstance : Finite ↥JH)
    (inferInstance : Group S) p hp Good Rk hGood hRk (inferInstance : Finite S) e.symm h

end General

section Rest

theorem exists_centralizerEquiv {G : Type} [Group G] {x z : G} (h : IsConj x z) :
    Nonempty (↥(Subgroup.centralizer ({x} : Set G)) ≃* ↥(Subgroup.centralizer ({z} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hmap := map_centralizer_singleton (MulAut.conj c) x
  rw [MulAut.conj_apply, hc] at hmap
  exact ⟨((Subgroup.centralizer ({x} : Set G)).equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans (MulEquiv.subgroupCongr hmap)⟩


theorem shape_rest_no3 {x : JH} (hx : orderOf x = 5) (hnot : ∀ k : ℕ, ¬ IsConj x (fJ ^ k))
    (h3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set JH))) :
    ShapeRkAt 5 (LeafType 5) (fun _ _ => True) x := by
  have hord : Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
    hnFiveOrders_holds x hx hnot
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({x} : Set JH))) 3 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3 |>.symm
  have hd : Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) ∣ 2 ^ 14 * 5 ^ 6 := by
    have e : 2 ^ 14 * 3 * 5 ^ 6 = 3 * (2 ^ 14 * 5 ^ 6) := by ring
    rw [e] at hord
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hord
  exact Or.inl (pConstrainedShape_of_solvable Nat.prime_five (isSolvable_of_card_dvd_two_five hd)
    (hnFiveRest_of_orders hnFiveOrders_holds x hx hnot))

@[expose] def HNFiveMoved : Prop :=
  ∀ x : JH, orderOf x = 5 → (∀ k : ℕ, ¬ IsConj x (fJ ^ k)) →
    3 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) →
    HNMovedIn (Subgroup.centralizer ({x} : Set JH))

theorem weak_rest_three (hR : HNFiveMoved) {x : JH} (hx : orderOf x = 5)
    (hnot : ∀ k : ℕ, ¬ IsConj x (fJ ^ k))
    (h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set JH))) :
    ShapeRkAt' 5 (LeafType 5) (fun _ _ => True) x := by
  have hord : Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
    hnFiveOrders_holds x hx hnot
  have hO := hnFiveRest_of_orders hnFiveOrders_holds x hx hnot
  have h9 : ¬ 3 ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) := fun h => by
    have := h.trans hord
    norm_num at this
  obtain ⟨Q, hQC, hQn, hQs, s, hsC, hso, hq⟩ := hR x hx hnot h3
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  exact Or.inl (hnNoComp_of_normal_solvable hQC hQn hQs hO hord
    (hnMoved_of_sylow hQC hQn h9 hsC hso hq))

end Rest

section Table


theorem hn5_centShapeRk' (hR : HNFiveMoved) :
    CentShapeRk' 5 (LeafType 5) (fun _ _ => True) ↥JH := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 5 T → LeafType 5 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  haveI : Finite JH := by
    have : Nat.card JH ≠ 0 := by rw [card_JH]; norm_num
    exact Nat.finite_of_card_ne_zero this
  intro k hk1 hkp
  have hk5 : orderOf k = 5 := orderOf_eq_prime hkp hk1
  by_cases h5A : ∃ e : ℕ, IsConj k (fJ ^ e)
  · obtain ⟨e, he⟩ := h5A
    obtain ⟨c, hc⟩ := isConj_iff.1 he
    have hko : orderOf (fJ ^ e) = 5 := by
      rw [← hc]
      exact (orderOf_conj_eq c k).trans hk5
    have hcent : Subgroup.centralizer ({fJ ^ e} : Set JH) = Subgroup.centralizer ({fJ} : Set JH) :=
      centralizer_pow_eq (by rw [hko, orderOf_fJ]) (by rw [orderOf_fJ]; norm_num)
    have hshape : ShapeRkAt 5 (LeafType 5) (fun _ _ => True) (fJ ^ e) :=
      ShapeRkAt.of_centralizer_eq hcent.symm shape_f
    have := ShapeRkAt.of_equiv Nat.prime_five hGood hRk (MulAut.conj c⁻¹) hshape
    rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k by group] at this
    exact this.toWeak Nat.prime_five
  · push Not at h5A
    by_cases h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer ({k} : Set JH))
    · exact weak_rest_three hR hk5 h5A h3
    · exact (shape_rest_no3 hk5 h5A h3).toWeak Nat.prime_five

set_option maxRecDepth 20000 in
theorem hn5_centShapeRk'_HN (hR : HNFiveMoved) :
    CentShapeRk' 5 (GoodSpor 5 []) (RkSpor 5 []) (NativeSporadic.Carrier .HN) := by
  haveI hf : Finite CFSG.Blueprint.NativeSporadic.HN :=
    Finite.of_equiv ↥JH (hnEquivJ : CFSG.Blueprint.NativeSporadic.HN ≃* JH).symm.toEquiv
  have h1 : CentShapeRk' 5 (GoodSpor 5 []) (RkSpor 5 []) ↥JH := by
    intro k hk1 hkp
    exact shapeRkAt'_mono (fun T _ h => Or.inl h)
      (fun T _ _ => by
        rintro (⟨h3, _⟩ | ⟨S, hS, _⟩)
        · omega
        · exact absurd hS (List.not_mem_nil))
      (hn5_centShapeRk' hR k hk1 hkp)
  exact @centShapeRk'_of_equiv_JH 5 Nat.prime_five CFSG.Blueprint.NativeSporadic.HN
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.HN) hf (GoodSpor 5 []) (RkSpor 5 [])
    (fun _ _ _ _ e h => GoodSpor.of_equiv e h) (fun _ _ _ _ e h => RkSpor.of_equiv e h)
    hnEquivJ h1

theorem sporStrong_HN_five_of_moved (hR : HNFiveMoved)
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds .HN 5) (hChev : ChevStrong 5) : SporStrong .HN 5 :=
  sporStrong_of_goodSporShape' (names := []) hOut hSpM hBr hP (by decide) hChev
    (fun S hS => absurd hS List.not_mem_nil) (hn5_centShapeRk'_HN hR)

end Table

end CFSG.HardMathSupport.Dickson.I271
