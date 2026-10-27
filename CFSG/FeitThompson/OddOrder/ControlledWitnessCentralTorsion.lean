module

public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.OddOrder.SharedSylowNormalizedByIntersection
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ} {M L H P Q : Subgroup G} {x : G}

theorem mem_normalizer_zpowers_of_commute {z x : G} (h : Commute z x) :
    z ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  rintro y hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
  exact (h.zpow_right n).symm.eq

theorem map_center_subtype_le_inf (hxQ : x ∈ Q)
    (hxM : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    (center ↥Q).map Q.subtype ≤ Q ⊓ M := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_map.1 hz
  have hcomm : Commute ((w : ↥Q) : G) x := by
    have h := congrArg (fun t : ↥Q => (t : G)) (mem_center_iff.1 hw ⟨x, hxQ⟩)
    simpa [Commute, SemiconjBy] using h.symm
  exact mem_inf.2 ⟨w.2, hxM (mem_normalizer_zpowers_of_commute hcomm)⟩

theorem subgroupCenterTorsionBy_le_map_center (Q : Subgroup G) (n : ℕ) :
    subgroupCenterTorsionBy Q n ≤ (center ↥Q).map Q.subtype := by
  intro z hz
  obtain ⟨hzQ, hcomm, -⟩ := mem_subgroupCenterTorsionBy.1 hz
  refine mem_map.2 ⟨⟨z, hzQ⟩, mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
  simpa using hcomm y y.2

theorem isElementaryAbelianSubgroup_subgroupCenterTorsionBy (Q : Subgroup G) (p : ℕ) :
    IsElementaryAbelianSubgroup p (subgroupCenterTorsionBy Q p) where
  mul_comm _ ha b hb :=
    ((mem_subgroupCenterTorsionBy.1 ha).2.1 b (mem_subgroupCenterTorsionBy.1 hb).1).symm
  pow_eq_one _ ha := (mem_subgroupCenterTorsionBy.1 ha).2.2

theorem subgroupCenterTorsionBy_subgroupOf_characteristic (hQH : Q ≤ H)
    (hQchar : (Q.subgroupOf H).Characteristic) (n : ℕ) :
    ((subgroupCenterTorsionBy Q n).subgroupOf H).Characteristic := by
  have hQmap : ∀ φ : ↥H ≃* ↥H, (Q.subgroupOf H).map (φ : ↥H →* ↥H) = Q.subgroupOf H :=
    characteristic_iff_map_eq.1 hQchar
  refine characteristic_iff_map_le.2 fun φ y hy => ?_
  obtain ⟨w, hw, rfl⟩ := mem_map.1 hy
  obtain ⟨hwQ, hwcomm, hwn⟩ := mem_subgroupCenterTorsionBy.1 (mem_subgroupOf.1 hw)
  have hwQH : w ∈ Q.subgroupOf H := mem_subgroupOf.2 hwQ
  refine mem_subgroupOf.2 (mem_subgroupCenterTorsionBy.2 ⟨?_, ?_, ?_⟩)
  · have : φ w ∈ Q.subgroupOf H := by rw [← hQmap φ]; exact mem_map_of_mem _ hwQH
    exact mem_subgroupOf.1 this
  ·
    intro g hg
    have hg' : (⟨g, hQH hg⟩ : ↥H) ∈ Q.subgroupOf H := mem_subgroupOf.2 hg
    rw [← hQmap φ] at hg'
    obtain ⟨v, hv, hvg⟩ := mem_map.1 hg'
    have hvg' : ((φ v : ↥H) : G) = g := congrArg Subtype.val hvg
    have hcomm : v * w = w * v :=
      Subtype.ext (by push_cast; exact hwcomm _ (mem_subgroupOf.1 hv))
    have h2 := congrArg (fun z : ↥H => ((z : ↥H) : G)) (congrArg φ hcomm)
    simp only [map_mul, Subgroup.coe_mul, hvg'] at h2
    exact h2
  · have hwn' : w ^ n = 1 := Subtype.ext (by simpa using hwn)
    have : φ w ^ n = 1 := by rw [← map_pow, hwn', map_one]
    simpa [Subtype.ext_iff] using this

private theorem dvd_card_of_orderOf_eq {T : Subgroup G} {z : G} (hz : z ∈ T) (n : ℕ)
    (hzo : orderOf z = n) : n ∣ Nat.card T := by
  have h := orderOf_dvd_natCard (⟨z, hz⟩ : ↥T)
  rwa [Subgroup.orderOf_mk, hzo] at h

variable [Finite G] [Fact p.Prime]

theorem exists_mem_subgroupCenterTorsionBy_orderOf_eq (hHnil : Group.IsNilpotent H)
    (hPnt : P ≠ ⊥) (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) :
    ∃ z ∈ subgroupCenterTorsionBy Q p, orderOf z = p := by
  have hPQ : P ≤ Q := le_of_isPGroup_le_nilpotent hHnil hQH hQ hPH (IsPGroup.of_card hP)
  have hfac : 1 ≤ (Nat.card H).factorization p := by
    by_contra h
    have h0 : (Nat.card H).factorization p = 0 := by omega
    rw [h0, pow_zero] at hQ
    exact hPnt (le_bot_iff.1 ((Subgroup.eq_bot_of_card_eq Q hQ) ▸ hPQ))
  obtain ⟨z, hzc, hz⟩ := exists_mem_center_orderOf_eq (P := ↥Q) Fact.out hQ hfac
  refine ⟨(z : G), mem_subgroupCenterTorsionBy.2 ⟨z.2, fun y hy => ?_, ?_⟩, ?_⟩
  · exact congrArg Subtype.val (mem_center_iff.1 hzc ⟨y, hy⟩)
  · have : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    simpa [Subtype.ext_iff] using this
  · rwa [Subgroup.orderOf_coe]

theorem subgroupCenterTorsionBy_ne_bot (hHnil : Group.IsNilpotent H)
    (hPnt : P ≠ ⊥) (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) :
    subgroupCenterTorsionBy Q p ≠ ⊥ := by
  obtain ⟨z, hz, hzo⟩ :=
    exists_mem_subgroupCenterTorsionBy_orderOf_eq (M := M) hHnil hPnt hP hPH hQH hQ
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    exact (Fact.out : p.Prime).one_lt.ne hzo
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hz
  exact hz1 hz

theorem dvd_natCard_subgroupCenterTorsionBy (hHnil : Group.IsNilpotent H)
    (hPnt : P ≠ ⊥) (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) :
    p ∣ Nat.card (subgroupCenterTorsionBy Q p) := by
  obtain ⟨z, hz, hzo⟩ :=
    exists_mem_subgroupCenterTorsionBy_orderOf_eq (M := M) hHnil hPnt hP hPH hQH hQ
  exact dvd_card_of_orderOf_eq hz p hzo

theorem subgroupCenterTorsionBy_le_sylow (hHnil : Group.IsNilpotent H)
    (hPM : P ≤ M) (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    (hxP : x ∈ P) (hxM : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    subgroupCenterTorsionBy Q p ≤ P := by
  have hPQ : P ≤ Q := le_of_isPGroup_le_nilpotent hHnil hQH hQ hPH (IsPGroup.of_card hP)
  have hQM : Q ⊓ M = P := inf_eq_of_le_nilpotent hHnil hPM hP hPH hQH hQ
  exact (subgroupCenterTorsionBy_le_map_center Q p).trans
    (hQM ▸ map_center_subtype_le_inf (hPQ hxP) hxM)

theorem characteristic_subgroupOf_subgroupCenterTorsionBy (hHnil : Group.IsNilpotent H)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) :
    ((subgroupCenterTorsionBy Q p).subgroupOf H).Characteristic := by
  have := hHnil
  have hc : Nat.card (Q.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQH).toEquiv, hQ]
  exact subgroupCenterTorsionBy_subgroupOf_characteristic hQH
    (characteristic_of_natCard_eq_pow_factorization hc) p

theorem le_normalizer_subgroupCenterTorsionBy (hHnil : Group.IsNilpotent H) (hHL : H ≤ L)
    (hHnorm : (H.subgroupOf L).Normal)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) {K : Subgroup G}
    (hKL : K ≤ L) :
    K ≤ normalizer ((subgroupCenterTorsionBy Q p : Subgroup G) : Set G) := by
  have hchar := characteristic_subgroupOf_subgroupCenterTorsionBy hHnil hQH hQ
  have hTH : subgroupCenterTorsionBy Q p ≤ H := subgroupCenterTorsionBy_le.trans hQH
  have hLN : L ≤ normalizer (H : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (hK := hHnorm) hHL
  have h := le_normalizer_map_subtype_of_characteristic
    ((subgroupCenterTorsionBy Q p).subgroupOf H) (hKL.trans hLN)
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hTH] at h

theorem elementaryAbelianPRank_subgroupCenterTorsionBy_eq_one_or_two
    (hHnil : Group.IsNilpotent H) (hPM : P ≤ M)
    (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hrank : elementaryAbelianPRank p ↥P ≤ 2)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    (hxP : x ∈ P) (hx1 : x ≠ 1)
    (hxM : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    elementaryAbelianPRank p ↥(subgroupCenterTorsionBy Q p) = 1 ∨
      elementaryAbelianPRank p ↥(subgroupCenterTorsionBy Q p) = 2 := by
  have hp : p.Prime := Fact.out
  have hPnt : P ≠ ⊥ := fun h => hx1 (by simpa [h] using hxP)
  have hTP : subgroupCenterTorsionBy Q p ≤ P :=
    subgroupCenterTorsionBy_le_sylow hHnil hPM hP hPH hQH hQ hxP hxM
  have hle : elementaryAbelianPRank p ↥(subgroupCenterTorsionBy Q p) ≤ 2 :=
    (elementaryAbelianPRank_le_of_le hp.one_lt hTP).trans hrank
  have hge : 1 ≤ elementaryAbelianPRank p ↥(subgroupCenterTorsionBy Q p) :=
    (one_le_elementaryAbelianPRank_iff hp).2
      (dvd_natCard_subgroupCenterTorsionBy (M := M) hHnil hPnt hP hPH hQH hQ)
  omega

theorem controlled_witness_central_torsion (hHnil : Group.IsNilpotent H) (hHL : H ≤ L)
    (hHnorm : (H.subgroupOf L).Normal) (hPM : P ≤ M)
    (hP : Nat.card P = p ^ (Nat.card M).factorization p) (hPH : P ≤ H)
    (hrank : elementaryAbelianPRank p ↥P ≤ 2)
    (hQH : Q ≤ H) (hQ : Nat.card Q = p ^ (Nat.card H).factorization p)
    (hxP : x ∈ P) (hx1 : x ≠ 1)
    (hxM : normalizer ((zpowers x : Subgroup G) : Set G) ≤ M) :
    Q ⊓ M = P ∧ subgroupCenterTorsionBy Q p ≠ ⊥ ∧
      ((subgroupCenterTorsionBy Q p).subgroupOf H).Characteristic ∧
      subgroupCenterTorsionBy Q p ≤ P ∧
      IsElementaryAbelianSubgroup p (subgroupCenterTorsionBy Q p) ∧
      (elementaryAbelianPRank p ↥(subgroupCenterTorsionBy Q p) = 1 ∨
        elementaryAbelianPRank p ↥(subgroupCenterTorsionBy Q p) = 2) ∧
      ∀ K : Subgroup G, K ≤ L →
        K ≤ normalizer ((subgroupCenterTorsionBy Q p : Subgroup G) : Set G) :=
  have hPnt : P ≠ ⊥ := fun h => hx1 (by simpa [h] using hxP)
  ⟨inf_eq_of_le_nilpotent hHnil hPM hP hPH hQH hQ,
    subgroupCenterTorsionBy_ne_bot (M := M) hHnil hPnt hP hPH hQH hQ,
    characteristic_subgroupOf_subgroupCenterTorsionBy hHnil hQH hQ,
    subgroupCenterTorsionBy_le_sylow hHnil hPM hP hPH hQH hQ hxP hxM,
    isElementaryAbelianSubgroup_subgroupCenterTorsionBy Q p,
    elementaryAbelianPRank_subgroupCenterTorsionBy_eq_one_or_two hHnil hPM hP hPH hrank hQH hQ
      hxP hx1 hxM,
    fun _ hKL => le_normalizer_subgroupCenterTorsionBy hHnil hHL hHnorm hQH hQ hKL⟩

end

end CFSG.FeitThompson
