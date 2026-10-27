module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Stmt813
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoCov

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSection_of_injective {Y D B : Type*} [Group Y] [Group D] [Group B] (g : D →* B)
    (hg : Function.Injective g) (h : IsSection Y D) : IsSection Y B := by
  obtain ⟨U, φ, hφ⟩ := h
  exact ⟨U.map g, φ.comp (U.equivMapOfInjective g hg).symm.toMonoidHom,
    hφ.comp (U.equivMapOfInjective g hg).symm.surjective⟩

theorem simple_le_of_odd {Y : Type*} [Group Y] [Finite Y] (T D : Subgroup Y) [IsSimpleGroup ↥T]
    (hns : ¬ Group.IsSolvable ↥T) (hD : ∀ t ∈ T, Odd (orderOf t) → t ∈ D) : T ≤ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq, hq2, hqd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card ↥T := by
    by_contra hcon
    push Not at hcon
    apply hns
    have hn : Nat.card ↥T ≠ 0 := Nat.card_pos.ne'
    have hu : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card ↥T → d = 2 := fun {d} hd hdd => by
      by_contra hd2
      exact hcon d hd hd2 hdd
    have hp2 : IsPGroup 2 ↥T := IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hn hu)
    have := hp2.isNilpotent
    infer_instance
  have := Fact.mk hq
  obtain ⟨t0, ht0⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) q hqd
  have hnc : Subgroup.normalClosure ({t0} : Set ↥T) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({t0} : Set ↥T)) with h | h
    · exfalso
      have h0 : t0 ∈ Subgroup.normalClosure ({t0} : Set ↥T) := Subgroup.subset_normalClosure rfl
      rw [h, Subgroup.mem_bot] at h0
      rw [h0, orderOf_one] at ht0
      exact hq.one_lt.ne ht0
    · exact h
  intro t ht
  have htmem : (⟨t, ht⟩ : ↥T) ∈ Subgroup.normalClosure ({t0} : Set ↥T) := by rw [hnc]; trivial
  have hle : Subgroup.normalClosure ({t0} : Set ↥T) ≤ D.subgroupOf T := by
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    rw [Group.mem_conjugatesOfSet_iff] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [Set.mem_singleton_iff] at hb
    subst hb
    obtain ⟨c, hc⟩ := isConj_iff.mp hba
    have hord : orderOf (a : Y) = q := by
      rw [Subgroup.orderOf_coe, ← hc, ← ht0]
      exact (MulAut.conj c).orderOf_eq b
    exact hD (a : Y) a.2 (by rw [hord]; exact hq.odd_of_ne_two hq2)
  exact hle htmem


theorem kfixok_of_invsec [Finite G] {J : Subgroup G} {z : G} (hz : z ∈ normalizer (J : Set G))
    (hz2 : z * z = 1) {k : Kind}
    (hinv : ∀ (T : Type) [Group T] [IsSimpleGroup T], ¬ Group.IsSolvable T →
      IsSection T ↥(centralizer ({z} : Set G)) → KindFactorAll k T) :
    KFixOK k (alphaZ J hz) := by
  intro T hTfix hTs hTna
  have hns : ¬ Group.IsSolvable ↥T := by
    obtain ⟨a, b, hab⟩ := hTna
    intro hsol
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)
  apply hinv ↥T hns
  let D₀ : Subgroup ↥J := (centralizer ({z} : Set G)).subgroupOf J
  let f : ↥D₀ →* ↥J ⧸ center ↥J := (QuotientGroup.mk' (center ↥J)).comp D₀.subtype
  have hTf : T ≤ f.range := by
    refine simple_le_of_odd T f.range hns ?_
    intro t htT hodd
    obtain ⟨y, hy, hyt⟩ := lift_fixed_odd J hz hz2 (hTfix htT) hodd
    refine ⟨⟨y, ?_⟩, hyt⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hy
  have hsec : IsSection ↥T ↥D₀ := by
    refine ⟨T.comap f, (f.comp (T.comap f).subtype).codRestrict T fun x => x.2, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨d, hd⟩ := hTf ht
    exact ⟨⟨d, by simpa [hd] using ht⟩, Subtype.ext hd⟩
  refine isSection_of_injective (B := ↥(centralizer ({z} : Set G)))
    ((J.subtype.comp D₀.subtype).codRestrict (centralizer ({z} : Set G)) fun d =>
      Subgroup.mem_subgroupOf.mp d.2) ?_ hsec
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun w : ↥(centralizer ({z} : Set G)) => (w : G)) hab))

theorem odd_center_of_l34 (hMin : MinIndexL34) [Finite G]
    {J : Subgroup G} (hq : IsQuasisimple ↥J) {k : Kind}
    (hinv : ∀ x : G, orderOf x = 2 → ∀ (T : Type) [Group T] [IsSimpleGroup T],
      ¬ Group.IsSolvable T → IsSection T ↥(centralizer ({x} : Set G)) → KindFactorAll k T)
    (hLie : LieModel (↥J ⧸ center ↥J) .PSL 3 2 2) : Odd (Nat.card (center ↥J)) := by
  by_contra hnodd
  have h2 : 2 ∣ Nat.card (center ↥J) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥J)) 2 h2
  have hd2 : orderOf (((d : ↥J)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hd]
  have hJd : J ≤ centralizer ({((d : ↥J) : G)} : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp d.2 ⟨j, hj⟩)
  obtain ⟨hs, hns⟩ := Gen.quasisimple_quot hq
  have hsec : IsSection (↥J ⧸ center ↥J) ↥(centralizer ({((d : ↥J) : G)} : Set G)) :=
    ⟨J.subgroupOf _, (QuotientGroup.mk' (center ↥J)).comp
      (Subgroup.subgroupOfEquivOfLe hJd).toMonoidHom,
      (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hJd).surjective⟩
  have := hs
  exact not_kindFactorAll_l34 hMin k hLie (hinv _ hd2 _ hns hsec)



end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
