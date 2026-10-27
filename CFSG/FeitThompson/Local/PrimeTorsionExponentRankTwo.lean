module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsOfPGroups
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Local.PGroupTripleCommutatorCentral
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube
import CFSG.FeitThompson.Local.PrimePowerMapHomClassThree
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

universe u

variable {p : ℕ} {G : Type*} [Group G]

theorem map_omega1_subtype_eq_omega1Subgroup (p : ℕ) (R : Subgroup G) :
    (omega1 p ↥R).map R.subtype = omega1Subgroup p R := by
  rw [omega1_eq_closure, omega1Subgroup_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg (Subgroup.subtype R) hy⟩
  · rintro ⟨hxR, hx⟩
    exact ⟨⟨x, hxR⟩, Subtype.ext (by simpa using hx), rfl⟩

private theorem pow_eq_one_of_mem_omega1_of_mul_closed {C : Type*} [Group C]
    (h : ∀ a b : C, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1) {z : C}
    (hz : z ∈ omega1 p C) : z ^ p = 1 := by
  rw [omega1_eq_closure] at hz
  induction hz using Subgroup.closure_induction with
  | mem a ha => exact ha
  | one => exact one_pow p
  | mul a b _ _ ha hb => exact h a b ha hb
  | inv a _ ha => rw [inv_pow, ha, inv_one]

private theorem mul_pow_eq_one_aux (hp : p.Prime) (hp3 : 3 < p) (n : ℕ) :
    ∀ {R : Type u} [Group R] [Finite R], Nat.card R < n → IsPGroup p R →
      elementaryAbelianPRank p R ≤ 2 → ∀ x y : R, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
  induction n with
  | zero => intro R _ _ hcard; exact absurd hcard (Nat.not_lt_zero _)
  | succ n ih =>
    intro R _ _ hcard hR hrank x y hx hy
    have := Fact.mk hp
    by_contra hxy
    have hclosure : Subgroup.closure ({x, y} : Set R) = ⊤ := by
      by_contra hne
      have hcard' : Nat.card (Subgroup.closure ({x, y} : Set R)) < n := by
        have h := natCard_lt_natCard_of_ne_top (G := R) hne
        omega
      have hxH : x ∈ Subgroup.closure ({x, y} : Set R) := Subgroup.subset_closure (by simp)
      have hyH : y ∈ Subgroup.closure ({x, y} : Set R) := Subgroup.subset_closure (by simp)
      have hkey := ih hcard' (hR.to_subgroup _)
        ((elementaryAbelianPRank_subgroup_le hp.one_lt _).trans hrank)
        ⟨x, hxH⟩ ⟨y, hyH⟩ (Subtype.ext (by simpa using hx)) (Subtype.ext (by simpa using hy))
      exact hxy (by simpa using congrArg (Subgroup.subtype _) hkey)
    have hxtop : Subgroup.zpowers x ≠ ⊤ := by
      intro htop
      obtain ⟨m, rfl⟩ : y ∈ Subgroup.zpowers x := htop ▸ Subgroup.mem_top y
      have hcomm : Commute x (x ^ m) := (Commute.refl x).zpow_right m
      exact hxy (by rw [hcomm.mul_pow, hx, hy, one_mul])
    obtain ⟨S, hScoatom, hxS⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hxtop
    have hxS' : x ∈ S := hxS (Subgroup.mem_zpowers x)
    have hSnormal : S.Normal := normal_of_isCoatom_of_isPGroup hp hR hScoatom
    have hSlt : Nat.card ↥S < n := by
      have h := natCard_lt_natCard_of_ne_top (G := R) hScoatom.1
      omega
    have hIHS : ∀ a b : ↥S, a ^ p = 1 → b ^ p = 1 → (a * b) ^ p = 1 :=
      ih hSlt (hR.to_subgroup S) ((elementaryAbelianPRank_subgroup_le hp.one_lt S).trans hrank)
    set N : Subgroup R := (omega1 p ↥S).map S.subtype with hN
    have hNtor : ∀ z ∈ N, z ^ p = 1 := by
      rintro z ⟨w, hw, rfl⟩
      simpa using congrArg (Subgroup.subtype S) (pow_eq_one_of_mem_omega1_of_mul_closed hIHS hw)
    have hNnormal : N.Normal := ConjAct.normal_of_characteristic_of_normal
    have hxN : x ∈ N :=
      ⟨⟨x, hxS'⟩, mem_omega1_of_pow_eq_one (Subtype.ext (by simpa using hx)), rfl⟩
    have hsup : N ⊔ Subgroup.zpowers y = ⊤ := by
      refine top_le_iff.1 ?_
      rw [← hclosure]
      refine (Subgroup.closure_le _).2 ?_
      intro z hz
      rcases hz with h | h
      · exact h ▸ Subgroup.mem_sup_left hxN
      · simp only [Set.mem_singleton_iff] at h
        subst h
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have hNcard : Nat.card ↥N ≤ p ^ 3 :=
      card_le_pow_three_of_elementaryAbelianPRank_le_two hp
        ((elementaryAbelianPRank_subgroup_le hp.one_lt N).trans hrank)
        (fun z => Subtype.ext (by simpa using hNtor z.1 z.2))
    have hyord : Nat.card ↥(Subgroup.zpowers y) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hy)
    have hRcard : Nat.card R ≤ p ^ 4 := by
      have hcoe : ((N ⊔ Subgroup.zpowers y : Subgroup R) : Set R)
          = (N : Set R) * (Subgroup.zpowers y : Set R) := Subgroup.normal_mul _ _
      have h1 : Nat.card R = Nat.card ((N : Set R) * (Subgroup.zpowers y : Set R)) := by
        rw [← Nat.card_congr (Set.equivOfEq hcoe), hsup]
        simp
      have h2 := natCard_mul_mul_natCard_inf N (Subgroup.zpowers y)
      have h3 : Nat.card ((N : Set R) * (Subgroup.zpowers y : Set R))
          ≤ Nat.card ↥N * Nat.card ↥(Subgroup.zpowers y) := by
        rw [← h2]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      calc Nat.card R ≤ Nat.card ↥N * Nat.card ↥(Subgroup.zpowers y) := h1 ▸ h3
        _ ≤ p ^ 3 * p := Nat.mul_le_mul hNcard hyord
        _ = p ^ 4 := by ring
    have hZ : ⁅_root_.commutator R, (⊤ : Subgroup R)⁆ ≤ Subgroup.center R :=
      commutator_commutator_le_center hp hR hRcard
    have hquot : IsCyclic (R ⧸ N) := by
      refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨QuotientGroup.mk' N y, ?_⟩
      have h1 : Subgroup.map (QuotientGroup.mk' N) (N ⊔ Subgroup.zpowers y) = ⊤ := by
        rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, MonoidHom.map_zpowers, bot_sup_eq] at h1
    have hcomm : _root_.commutator R ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance
    have hexp : ∀ c ∈ _root_.commutator R, c ^ p = 1 := fun c hc => hNtor c (hcomm hc)
    exact hxy (by
      rw [mul_pow_eq_pow_mul_pow_of_triple_commutator_le_center hp hp3 hZ hexp x y, hx, hy,
        one_mul])

variable {R : Type*} [Group R]

theorem mul_pow_eq_one_of_elementaryAbelianPRank_le_two [Finite R] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hrank : elementaryAbelianPRank p R ≤ 2) {x y : R}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : (x * y) ^ p = 1 :=
  mul_pow_eq_one_aux hp hp3 (Nat.card R + 1) (Nat.lt_succ_self _) hR hrank x y hx hy

theorem pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two [Finite R] (hp : p.Prime)
    (hp3 : 3 < p) (hR : IsPGroup p R) (hrank : elementaryAbelianPRank p R ≤ 2) {x : R}
    (hx : x ∈ omega1 p R) : x ^ p = 1 :=
  pow_eq_one_of_mem_omega1_of_mul_closed
    (fun _ _ ha hb => mul_pow_eq_one_of_elementaryAbelianPRank_le_two hp hp3 hR hrank ha hb) hx

theorem coe_omega1_of_elementaryAbelianPRank_le_two [Finite R] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hrank : elementaryAbelianPRank p R ≤ 2) :
    (omega1 p R : Set R) = {x : R | x ^ p = 1} :=
  Set.Subset.antisymm
    (fun _ hx => pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank hx)
    fun _ hx => mem_omega1_of_pow_eq_one hx

theorem mem_omega1_iff_of_elementaryAbelianPRank_le_two [Finite R] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hrank : elementaryAbelianPRank p R ≤ 2) {x : R} :
    x ∈ omega1 p R ↔ x ^ p = 1 :=
  Set.ext_iff.1 (coe_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank) x

theorem exponent_omega1_dvd_of_elementaryAbelianPRank_le_two [Finite R] (hp : p.Prime)
    (hp3 : 3 < p) (hR : IsPGroup p R) (hrank : elementaryAbelianPRank p R ≤ 2) :
    Monoid.exponent (omega1 p R) ∣ p :=
  Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
    simpa using pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank g.2)

theorem coe_omega1Subgroup_of_elementaryAbelianPRank_le_two (R : Subgroup G) [Finite ↥R]
    (hp : p.Prime) (hp3 : 3 < p) (hR : IsPGroup p ↥R)
    (hrank : elementaryAbelianPRank p ↥R ≤ 2) :
    (omega1Subgroup p R : Set G) = {x ∈ (R : Set G) | x ^ p = 1} := by
  ext x
  rw [← map_omega1_subtype_eq_omega1Subgroup]
  simp only [SetLike.mem_coe, Subgroup.mem_map, Subgroup.coe_subtype, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank hy
    exact ⟨y.2, by simpa using congrArg (Subgroup.subtype R) h⟩
  · rintro ⟨hxR, hx⟩
    exact ⟨⟨x, hxR⟩, mem_omega1_of_pow_eq_one (Subtype.ext (by simpa using hx)), rfl⟩

end

end CFSG.FeitThompson
