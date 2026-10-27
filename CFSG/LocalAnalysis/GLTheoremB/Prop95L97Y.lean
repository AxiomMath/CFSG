module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95L97Claim1

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def phiS {M S : Subgroup G} (hSM : S ≤ M) : ↥S →* ↥(tl M S) :=
  ((piM M).comp (Subgroup.inclusion hSM)).codRestrict (tl M S) fun s => piM_mem_tl s.2

theorem phiS_apply_coe {M S : Subgroup G} (hSM : S ≤ M) (s : ↥S) :
    ((phiS hSM s : ↥(tl M S)) : Mt M) = piM M ⟨(s : G), hSM s.2⟩ := rfl

theorem phiS_surjective {M S : Subgroup G} (hSM : S ≤ M) : Function.Surjective (phiS hSM) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_tl.1 hy
  exact ⟨⟨(x : G), hx⟩, Subtype.ext rfl⟩

theorem phiS_eq_one_iff {M S : Subgroup G} (hSM : S ≤ M) (s : ↥S) :
    phiS hSM s = 1 ↔ (s : G) ∈ pCoreOf 2 M := by
  have h1 : phiS hSM s = 1 ↔ piM M ⟨(s : G), hSM s.2⟩ = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [h1, piM_eq_one_iff]

theorem comap_phiS_subgroupOf {M S A : Subgroup G} (hSM : S ≤ M) (hAS : A ≤ S)
    (hOA : pCoreOf 2 M ≤ A) :
    ((tl M A).subgroupOf (tl M S)).comap (phiS hSM) = A.subgroupOf S := by
  ext y
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  rw [phiS_apply_coe]
  constructor
  · intro hy
    obtain ⟨a, haA, ha⟩ := mem_tl.1 hy
    have h1 : piM M (a⁻¹ * ⟨(y : G), hSM y.2⟩) = 1 := by
      rw [map_mul, map_inv, ha, inv_mul_cancel]
    have h2 := (piM_eq_one_iff).1 h1
    have h3 : (a : G)⁻¹ * (y : G) ∈ A := hOA h2
    have h4 : (a : G) * ((a : G)⁻¹ * (y : G)) ∈ A := A.mul_mem haA h3
    simpa using h4
  · intro hy
    exact piM_mem_tl hy

theorem index_subgroupOf_eq_tl {M S A : Subgroup G} (hSM : S ≤ M) (hAS : A ≤ S)
    (hOA : pCoreOf 2 M ≤ A) :
    (A.subgroupOf S).index = ((tl M A).subgroupOf (tl M S)).index := by
  rw [← comap_phiS_subgroupOf hSM hAS hOA, Subgroup.index_comap_of_surjective _ (phiS_surjective hSM)]

theorem isPGroup_ker_phiS {M S : Subgroup G} (hSM : S ≤ M) : IsPGroup 2 (phiS hSM).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨s, hs⟩
  have hs' : (s : G) ∈ pCoreOf 2 M := (phiS_eq_one_iff hSM s).1 hs
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨(s : G), hs'⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem isSolvable_of_tl {M S : Subgroup G} (hSM : S ≤ M) (h : Group.IsSolvable ↥(tl M S)) :
    Group.IsSolvable ↥S := by
  have h2 : IsPGroup 2 (phiS hSM).ker := isPGroup_ker_phiS hSM
  have : Group.IsSolvable ↥(phiS hSM).ker := by
    have : Group.IsNilpotent ↥(phiS hSM).ker := h2.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (phiS hSM).ker.subtype (phiS hSM)
    (by rw [Subgroup.range_subtype])

theorem not_dvd_card_of_tl {M S : Subgroup G} (hSM : S ≤ M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ¬ p ∣ Nat.card ↥(tl M S)) : ¬ p ∣ Nat.card ↥S := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : orderOf (phiS hSM y) ∣ p := by
    rw [← hy]; exact orderOf_map_dvd _ _
  have h2 : orderOf (phiS hSM y) ∣ Nat.card ↥(tl M S) := orderOf_dvd_natCard _
  have h3 : orderOf (phiS hSM y) = 1 := by
    rcases (Nat.dvd_prime hp).1 h1 with h4 | h4
    · exact h4
    · exact absurd (h4 ▸ h2) h
  have h4 : phiS hSM y = 1 := orderOf_eq_one_iff.1 h3
  have h5 : (y : G) ∈ pCoreOf 2 M := (phiS_eq_one_iff hSM y).1 h4
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨(y : G), h5⟩
  have h6 : orderOf y ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    refine Subtype.ext ?_
    have := congrArg Subtype.val hk
    simpa using this
  rw [hy] at h6
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h6)
  exact hp2 this

theorem tl_sup {M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    tl M (A ⊔ B) = tl M A ⊔ tl M B := by
  unfold tl
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

@[expose] def yGrp (D W : Subgroup G) : Subgroup G := gammaD D ⊔ ⁅gammaD D, W⁆

section YData

variable {m p : ℕ} {M D X W : Subgroup G}

theorem not_dvd_card_of_isPGroup_two {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ Nat.card H := by
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn]
  intro hdvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))

theorem yGrp_le_M (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W) : yGrp D W ≤ M :=
  sup_le (gammaD_le_of_hyp hD) (commutator_le_of_le (gammaD_le_of_hyp hD) (chief_le_M h))

theorem gammaD_le_yGrp : gammaD D ≤ yGrp D W := le_sup_left

theorem commutator_le_yGrp : ⁅gammaD D, W⁆ ≤ yGrp D W := le_sup_right

theorem pCoreOf_le_yGrp (hD : Prop95Hyp p M D) : pCoreOf 2 M ≤ yGrp D W :=
  hD.clause_c.trans gammaD_le_yGrp

theorem tl_yGrp (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W) :
    tl M (yGrp D W) = tl M (gammaD D) ⊔ ⁅tl M (gammaD D), tl M W⁆ := by
  have hΓM := gammaD_le_of_hyp hD
  unfold yGrp
  rw [tl_sup hΓM (commutator_le_of_le hΓM (chief_le_M h)), tl_commutator hΓM (chief_le_M h)]

theorem isSylowTwoOf_gammaD_yGrp (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W)
    (hab : ⁅W, W⁆ ≤ X) : CFSG.QuasithinUnique.IsSylowTwoOf (gammaD D) (yGrp D W) := by
  obtain ⟨hT, hWn, hXn, hXWt, hTX⟩ := lemma97_Qdata hD h
  have hab' : ⁅tl M W, tl M W⁆ ≤ tl M X := by
    rw [← tl_commutator (chief_le_M h) (chief_le_M h)]
    exact tl_mono hab
  have hS := QGroup.isSylowTwoOf_sup_commutator (hO_Mt M) hT hWn hXn hXWt hTX hab'
  refine ⟨gammaD_le_yGrp, isPGroup_gammaD D, ?_⟩
  rw [index_subgroupOf_eq_tl (yGrp_le_M hD h) gammaD_le_yGrp hD.clause_c, tl_yGrp hD h]
  exact hS.2.2

theorem isSolvable_yGrp (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W)
    (hab : ⁅W, W⁆ ≤ X) : Group.IsSolvable ↥(yGrp D W) := by
  obtain ⟨hT, hWn, hXn, hXWt, hTX⟩ := lemma97_Qdata hD h
  have hab' : ⁅tl M W, tl M W⁆ ≤ tl M X := by
    rw [← tl_commutator (chief_le_M h) (chief_le_M h)]
    exact tl_mono hab
  refine isSolvable_of_tl (yGrp_le_M hD h) ?_
  rw [tl_yGrp hD h]
  exact QGroup.isSolvable_sup_commutator (hO_Mt M) hT hWn hXn hXWt hTX hab'

theorem not_dvd_card_yGrp (hS : GLStanding G m p) (hD : Prop95Hyp p M D)
    (h : Lemma97Chief p M D X W) : ¬ p ∣ Nat.card ↥(yGrp D W) := by
  refine not_dvd_card_of_tl (yGrp_le_M hD h) hS.prime hS.ne_two ?_
  rw [tl_yGrp hD h]
  refine QGroup.not_dvd_card_sup_commutator (tl_normal h.normalW) hS.prime ?_ ?_
  · exact not_dvd_card_of_isPGroup_two (isPGroup_tl (isPGroup_gammaD D)) hS.prime hS.ne_two
  · have hWM : W ≤ M := (chief_le_M h)
    have h1 : Nat.card ↥(tl M W) ∣ Nat.card ↥(W.subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(W.subgroupOf M) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
    have h3 : Nat.card ↥W ∣ Nat.card ↥(GLAPPrimeCoreOf p M) := Subgroup.card_dvd_of_le h.le_core
    intro hdvd
    exact not_dvd_card_glaPPrimeCoreOf hS.prime M (hdvd.trans (h1.trans (h2 ▸ h3)))

theorem charTwo_yGrp (hS : GLStanding G m p) (hD : Prop95Hyp p M D)
    (h : Lemma97Chief p M D X W) : CFSG.QuasithinUnique.CharTwo (yGrp D W) := by
  have hYM := yGrp_le_M hD h
  have hOY : pCoreOf 2 M ≤ yGrp D W := pCoreOf_le_yGrp hD
  have hnormal : ((pCoreOf 2 M).subgroupOf (yGrp D W)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOY]
    exact hYM.trans (le_normalizer_pCoreOf 2 M)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOle : pCoreOf 2 M ≤ pCoreOf 2 (yGrp D W) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 hOY hnormal
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  rintro y ⟨hyY, hyC⟩
  have hyM : y ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    ⟨hYM hyY, Subgroup.centralizer_le hOle hyC⟩
  exact hOle (hS.charTwo M hD.twoLocal hyM)

theorem mem_normalizer_yGrp (hD : Prop95Hyp p M D) (h : Lemma97Chief p M D X W) {g : G}
    (hgM : g ∈ M) (hgΓ : g ∈ Subgroup.normalizer (gammaD D : Set G)) :
    g ∈ Subgroup.normalizer (yGrp D W : Set G) := by
  have hWN : M ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (chief_le_M h)).1 h.normalW
  have hgW := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hWN hgM)
  have hgΓ' := Subgroup.mem_normalizer_iff_map_conj_eq.1 hgΓ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold yGrp
  rw [Subgroup.map_sup, Subgroup.map_commutator, hgΓ', hgW]

end YData

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.L97
