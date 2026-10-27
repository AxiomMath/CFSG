module

public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.PartTwo.Sec4.Census

section Lifts

variable {G : Type} {X : Type*} [Group G] [Group X] {φ : G →* X}

theorem add_le_pRank_of_lift [Finite G] {p : ℕ} (hp : p.Prime) {Z : Subgroup G}
    (hZk : Z ≤ φ.ker) (hZp : ∀ z ∈ Z, z ^ p = 1) {s : ℕ} (hs : p ^ s ≤ Nat.card Z)
    {E : Subgroup X} (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ E, ∃ y : G, φ y = e ∧ y ^ p = 1) {r : ℕ} (hr : p ^ r ≤ Nat.card E) :
    r + s ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set U := TripleCoverLift.powOneSubgroup φ E p hcomm with hUdef
  have hUab : CFSG.Open.IsElemAbelian p U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup p U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X := φ.comp U.subtype
  have hψr : ψ.range = E := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := hlift e he
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun z hz => TripleCoverLift.mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hz)]; exact E.one_mem, hZp z hz⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : p ^ s ≤ Nat.card ψ.ker := by
    calc p ^ s ≤ Nat.card Z := hs
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have hrk : r + s ≤ k := by
    have h1 : p ^ (r + s) ≤ p ^ k := by
      rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr, pow_add, mul_comm]
      exact Nat.mul_le_mul hψk hr
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  exact hrk.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp ⊤)
    ⟨U, le_top, hUab, hk⟩)

theorem succ_le_pRank_of_lift [Finite G] {p : ℕ} (hp : p.Prime) (hpk : p ∣ Nat.card φ.ker)
    {E : Subgroup X} (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ E, ∃ y : G, φ y = e ∧ y ^ p = 1) {r : ℕ} (hr : p ^ r ≤ Nat.card E) :
    r + 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
  refine add_le_pRank_of_lift hp (Z := Subgroup.zpowers (z : G)) ?_ ?_ ?_
    hcomm hlift hr
  · rw [Subgroup.zpowers_le]
    exact z.2
  · rintro _ ⟨j, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzo,
      pow_orderOf_eq_one, one_zpow]
  · rw [Nat.card_zpowers, hzo, pow_one]

end Lifts

@[expose] def HasLiftableTriple (X : Type) [Group X] : Prop :=
  ∃ y : Fin 3 → X, (∀ i, y i ^ 3 = 1) ∧ (∀ i j, Commute (y i) (y j)) ∧
    27 ≤ Nat.card (Subgroup.closure (Set.range y)) ∧
    (∀ i, ∃ n : X, n * y i * n⁻¹ = (y i)⁻¹) ∧
    ∀ i j : Fin 3, i < j → ∃ n : X,
      (n * y i * n⁻¹ = y i ∧ n * y j * n⁻¹ = (y j)⁻¹) ∨
      (n * y j * n⁻¹ = y j ∧ n * y i * n⁻¹ = (y i)⁻¹) ∨
      (n * y i * n⁻¹ = y j ∧ n * y j * n⁻¹ = y i)

theorem HasLiftableTriple.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : HasLiftableTriple X) : HasLiftableTriple Y := by
  obtain ⟨y, hy3, hcomm, hcard, hinv, hpair⟩ := h
  refine ⟨fun i => e (y i), fun i => by rw [← map_pow, hy3, map_one],
    fun i j => (hcomm i j).map e.toMonoidHom, ?_, ?_, ?_⟩
  · have hmap : Subgroup.closure (Set.range fun i => e (y i)) =
        (Subgroup.closure (Set.range y)).map e.toMonoidHom := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [hmap, Subgroup.card_map_of_injective e.injective]
    exact hcard
  · intro i
    obtain ⟨n, hn⟩ := hinv i
    exact ⟨e n, by rw [← map_mul, ← map_inv, ← map_mul, hn, map_inv]⟩
  · intro i j hij
    obtain ⟨n, hn⟩ := hpair i j hij
    refine ⟨e n, ?_⟩
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← map_mul, ← map_inv, ← map_mul, h1],
        by rw [← map_mul, ← map_inv, ← map_mul, h2, map_inv]⟩
    · exact Or.inr (Or.inl ⟨by rw [← map_mul, ← map_inv, ← map_mul, h1],
        by rw [← map_mul, ← map_inv, ← map_mul, h2, map_inv]⟩)
    · exact Or.inr (Or.inr ⟨by rw [← map_mul, ← map_inv, ← map_mul, h1],
        by rw [← map_mul, ← map_inv, ← map_mul, h2]⟩)

theorem HasLiftableTriple.four_le_pRank {G X : Type} [Group G] [Finite G] [Group X]
    (h : HasLiftableTriple X) {φ : G →* X} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) (h3 : 3 ∣ Nat.card φ.ker) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  obtain ⟨y, hy3, hcommy, hE, hinv, hpair⟩ := h
  set E := Subgroup.closure (Set.range y)
  have hodd : Odd 3 := by decide
  have key : ∀ (a b : G) (i j : Fin 3), φ a = y i → φ b = y j → i < j → a * b = b * a := by
    intro a b i j hi hj hlt
    have hc : Commute (φ a) (φ b) := by
      rw [hi, hj]
      exact hcommy i j
    obtain ⟨n, hn | hn | hn⟩ := hpair i j hlt
    · exact TripleCoverLift.commute_of_conj hφ hker hodd hc (by rw [hj]; exact hy3 j)
        (n := n) (Or.inl ⟨by rw [hi]; exact hn.1, by rw [hj]; exact hn.2⟩)
    · exact (TripleCoverLift.commute_of_conj hφ hker hodd hc.symm (by rw [hi]; exact hy3 i)
        (n := n) (Or.inl ⟨by rw [hj]; exact hn.1, by rw [hi]; exact hn.2⟩)).symm
    · exact TripleCoverLift.commute_of_conj hφ hker hodd hc (by rw [hj]; exact hy3 j)
        (n := n) (Or.inr ⟨by rw [hi, hj]; exact hn.1, by rw [hi, hj]; exact hn.2⟩)
  have hS : ∀ a b : G, φ a ∈ Set.range y → φ b ∈ Set.range y → φ a ≠ φ b → a * b = b * a := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩ hab
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key a b i j hi.symm hj.symm hlt
    · exact (key b a j i hj.symm hi.symm hlt).symm
  have hcomm : ∀ x ∈ E.comap φ, ∀ z ∈ E.comap φ, x * z = z * x := fun x hx z hz =>
    TripleCoverLift.commute_of_mem_closure hφ hker hS hx hz
  have hlift : ∀ e ∈ E, ∃ g : G, φ g = e ∧ g ^ 3 = 1 := by
    intro e he
    refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure hcomm Subgroup.subset_closure
      ?_ he
    rintro s ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hinv i
    exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker hodd (hy3 i) hn
  exact succ_le_pRank_of_lift Nat.prime_three h3 hcomm hlift (r := 3)
    (by norm_num; exact hE)

theorem HasLiftableTriple.four_le_pRank_of_cover {K X : Type} [Group K] [Finite K] [Group X]
    (h : HasLiftableTriple X) (e : K ⧸ Subgroup.center K ≃* X)
    (h3 : 3 ∣ Nat.card (Subgroup.center K)) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  refine h.four_le_pRank (CFSG.GH74.Generic.centralQuotientMap_surjective e)
    (CFSG.GH74.Generic.centralQuotientMap_ker e).le ?_
  rw [CFSG.GH74.Generic.centralQuotientMap_ker]
  exact h3

end CFSG.LocalAnalysis.RankThreeTheoremC
