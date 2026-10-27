module

public import CFSG.ClassicalInvolution.Q3.TL3Weak
public import CFSG.ClassicalInvolution.Q3.TL3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section Split

@[expose] def TightThreeAct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) ∧ x ^ 3 ^ k = 1 ∧
      ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R

@[expose] def TightDiagonalFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∀ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) → x ^ 3 ^ k = 1 →
      (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) →
      ∃ (x' : G) (k' : ℕ), x' ∈ Subgroup.centralizer ({t} : Set G) ∧ x' ^ 3 ^ k' = 1 ∧
        (∃ r ∈ R, ⁅x', r⁆ ∉ oddCoreImg R) ∧
        ∀ y ∈ Subgroup.centralizer ({t} : Set G), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
          ⁅x', y⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set G))

theorem tightThreeElementLarge_of_split (hA : TightThreeAct) (hD : TightDiagonalFree) :
    TightThreeElementLarge := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨x, k, hxC, hx3, hxR⟩ := hA G hnab hlarge R S hS t ht hto hRC hRn h2
  exact hD G hnab hlarge R S hS t ht hto hRC hRn h2 x k hxC hx3 hxR

theorem tightThreeAct_of_tightThreeElementLarge (h : TightThreeElementLarge) : TightThreeAct := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨x, k, hxC, hx3, hxR, -⟩ := h G hnab hlarge R S hS t ht hto hRC hRn h2
  exact ⟨x, k, hxC, hx3, hxR⟩

theorem tightDiagonalFree_of_tightThreeElementLarge (h : TightThreeElementLarge) :
    TightDiagonalFree := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2 _ _ _ _ _
  exact h G hnab hlarge R S hS t ht hto hRC hRn h2

theorem tightThreeElementLarge_iff_split :
    TightThreeElementLarge ↔ TightThreeAct ∧ TightDiagonalFree :=
  ⟨fun h => ⟨tightThreeAct_of_tightThreeElementLarge h,
    tightDiagonalFree_of_tightThreeElementLarge h⟩,
    fun h => tightThreeElementLarge_of_split h.1 h.2⟩

theorem tightLift3_of_split (hA : TightThreeAct) (hD : TightDiagonalFree) : TightLift3 :=
  tightLift3_of_tightThreeElementLarge (tightThreeElementLarge_of_split hA hD)

theorem tightHasMember3Large_of_split (hA : TightThreeAct) (hD : TightDiagonalFree) :
    TightHasMember3Large :=
  tightHasMember3Large_of_tightLift3 (tightLift3_of_split hA hD)

end Split

section Saturation

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {t : G}

theorem sup_oddCoreImg_le_centralizer (hRC : R ≤ Subgroup.centralizer ({t} : Set G)) :
    R ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G)) ≤ Subgroup.centralizer ({t} : Set G) :=
  sup_le hRC (oddCoreImg_le _)

theorem le_normalizer_oddCoreImg (C : Subgroup G) :
    C ≤ Subgroup.normalizer (oddCoreImg C : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun ho => conj_mem_oddCoreImg (Subgroup.le_normalizer hg) ho, fun ho => ?_⟩
  have := conj_mem_oddCoreImg (Subgroup.le_normalizer (C.inv_mem hg)) ho
  simpa [mul_assoc] using this

theorem sup_oddCoreImg_normal (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) :
    ((R ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G))).subgroupOf
      (Subgroup.centralizer ({t} : Set G))).Normal := by
  set C := Subgroup.centralizer ({t} : Set G) with hC
  have hOn : ((oddCoreImg C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreImg_le C)).mpr
      (le_normalizer_oddCoreImg C)
  rw [Subgroup.subgroupOf_sup hRC (oddCoreImg_le C)]
  have := hRn
  have := hOn
  infer_instance

theorem isPGroup_two_quotient_sup_oddCoreImg
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (h2 : IsPGroup 2 (R ⧸ oddCore R)) :
    IsPGroup 2 (↥(R ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G))) ⧸
      oddCore ↥(R ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G)))) := by
  set C := Subgroup.centralizer ({t} : Set G) with hC
  set R' := R ⊔ oddCoreImg C with hR'
  have hRR' : R ≤ R' := le_sup_left
  have hOR' : oddCoreImg C ≤ R' := le_sup_right
  have hR'C : R' ≤ C := sup_oddCoreImg_le_centralizer hRC
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hOn : ((oddCoreImg C).subgroupOf R').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOR').mpr
      (hR'C.trans (le_normalizer_oddCoreImg C))
  have hOodd : Odd (Nat.card ((oddCoreImg C).subgroupOf R')) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOR').toEquiv]
    exact odd_natCard_oddCoreImg C
  have hOQ : (oddCoreImg C).subgroupOf R' ≤ oddCore ↥R' := le_sSup ⟨hOn, hOodd⟩
  have hPn : ((oddCoreImg R).subgroupOf R').Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer ((oddCoreImg_le R).trans hRR')).mpr ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hgR : g ∈ Subgroup.normalizer (R : Set G) := hCR (hR'C hg)
    refine ⟨fun ho => conj_mem_oddCoreImg hgR ho, fun ho => ?_⟩
    have hgR' : g⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      (Subgroup.normalizer (R : Set G)).inv_mem hgR
    have := conj_mem_oddCoreImg hgR' ho
    simpa [mul_assoc] using this
  have hPodd : Odd (Nat.card ((oddCoreImg R).subgroupOf R')) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((oddCoreImg_le R).trans hRR')).toEquiv]
    exact odd_natCard_oddCoreImg R
  have hPQ : (oddCoreImg R).subgroupOf R' ≤ oddCore ↥R' := le_sSup ⟨hPn, hPodd⟩
  let φ : R →* ↥R' ⧸ oddCore ↥R' :=
    (QuotientGroup.mk' (oddCore ↥R')).comp (Subgroup.inclusion hRR')
  have hker : oddCore R ≤ φ.ker := by
    intro x hx
    have hx' : (x : G) ∈ oddCoreImg R := (mem_oddCore_iff_coe_mem_oddCoreImg R x).mp hx
    have hmem : (⟨x, hRR' x.2⟩ : ↥R') ∈ (oddCoreImg R).subgroupOf R' := hx'
    exact (QuotientGroup.eq_one_iff _).mpr (hPQ hmem)
  let φ' : R ⧸ oddCore R →* ↥R' ⧸ oddCore ↥R' := QuotientGroup.lift (oddCore R) φ hker
  have hsurj : Function.Surjective φ' := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have htop : (R.subgroupOf R' ⊔ (oddCoreImg C).subgroupOf R') = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hRR' hOR', ← hR', Subgroup.subgroupOf_self]
      have hy : y ∈ R.subgroupOf R' ⊔ (oddCoreImg C).subgroupOf R' := by
        rw [htop]
        exact Subgroup.mem_top y
      have := hOn
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
      refine ⟨QuotientGroup.mk ⟨(a : G), ha⟩, ?_⟩
      have hb' : (QuotientGroup.mk b : ↥R' ⧸ oddCore ↥R') = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (hOQ hb)
      simp only [φ', φ, QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, hb', mul_one]
      rfl
  exact h2.of_surjective φ' hsurj

end Saturation

end CFSG.ClassicalInvolution.Q3
