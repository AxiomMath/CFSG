module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Monster.Existence.Defs
public import CFSG.Sporadic.Co1Block.PermBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open

section Generic

variable {X C K : Type*} [Group X] [Group C] [instK : Group K]

theorem isElemAbelian_card_map_quot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup C}
    [N.Normal] (hN : IsPGroup 2 N) (e : C ⧸ N ≃* K) {E : Subgroup C} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map (e.toMonoidHom.comp (QuotientGroup.mk' N))) ∧
      Nat.card (E.map (e.toMonoidHom.comp (QuotientGroup.mk' N))) = Nat.card E := by
  refine ⟨hE.map _, ?_⟩
  have hinj : Function.Injective ((e.toMonoidHom.comp (QuotientGroup.mk' N)).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h0 : e (QuotientGroup.mk (x : C)) = 1 := hx
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h0
    obtain ⟨k, hk⟩ := hN ⟨(x : C), h0⟩
    have h1 : orderOf (x : C) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    have h2 : orderOf (x : C) ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 x x.2)
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have h3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact Subgroup.mem_bot.2 (Subtype.ext h3)
  have hrange : E.map (e.toMonoidHom.comp (QuotientGroup.mk' N)) =
      ((e.toMonoidHom.comp (QuotientGroup.mk' N)).comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_le_of_le_quot {p b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup X}
    {N : Subgroup D} [N.Normal] (hN : IsPGroup 2 N)
    (hK : ∀ E : Subgroup K, IsElemAbelian p E → Nat.card E ≤ b) (e : D ⧸ N ≃* K) {E : Subgroup X}
    (hED : E ≤ D) (hE : IsElemAbelian p E) : Nat.card E ≤ b := by
  obtain ⟨h1, h2⟩ := isElemAbelian_card_map_quot hp hp2 hN e (hE.subgroupOf D)
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv, ← h2]
  exact hK _ h1

theorem card_le_two_of_quot [Finite C] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N : Subgroup C}
    [N.Normal] (hN : IsPGroup 2 N) (P : K → Prop)
    (hKinv : ∀ s : K, orderOf s = 2 → ¬ p ^ n ∣ Nat.card (Subgroup.centralizer ({s} : Set K)))
    (hKfix : ∀ E : Subgroup K, IsElemAbelian p E → Nat.card E = p ^ n → ∃ j ∈ E, P j)
    (e : C ⧸ N ≃* K)
    (hfix : ∀ k : C, P (e (QuotientGroup.mk k)) →
      Nat.card ↥(N ⊓ Subgroup.centralizer ({k} : Set C)) ≤ 2)
    {F W : Subgroup C} (hF : IsElemAbelian p F) (hFc : Nat.card F = p ^ n)
    (hW : IsElemAbelian 2 W) (hFW : ∀ f ∈ F, ∀ w ∈ W, f * w = w * f) : Nat.card W ≤ 2 := by
  obtain ⟨hFe, hFcard⟩ := isElemAbelian_card_map_quot hp hp2 hN e hF
  rw [hFc] at hFcard
  have hWN : W ≤ N := by
    intro w hw
    by_contra hwN
    have hs1 : e (QuotientGroup.mk w) ≠ 1 := fun h1 =>
      hwN ((QuotientGroup.eq_one_iff w).1 ((MulEquiv.map_eq_one_iff e).1 h1))
    have hs2 : e (QuotientGroup.mk w) ^ 2 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hW.2 w hw, QuotientGroup.mk_one, map_one]
    apply hKinv _ (orderOf_eq_prime hs2 hs1)
    have hle : F.map (e.toMonoidHom.comp (QuotientGroup.mk' N)) ≤
        Subgroup.centralizer ({e (QuotientGroup.mk w)} : Set K) := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      show e (QuotientGroup.mk f) * e (QuotientGroup.mk w) =
        e (QuotientGroup.mk w) * e (QuotientGroup.mk f)
      rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hFW f hf w hw]
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [hFcard] at hdvd
  obtain ⟨j, hj, hjP⟩ := hKfix _ hFe hFcard
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hj
  have hle : W ≤ N ⊓ Subgroup.centralizer ({k} : Set C) := fun w hw =>
    ⟨hWN hw, Subgroup.mem_centralizer_singleton_iff.2 (hFW k hk w hw).symm⟩
  exact (Subgroup.card_le_of_le hle).trans (hfix k hjP)

end Generic

section Involution

open CFSG.Monster.Existence


theorem card_le_of_involution (hE : MonsterExistenceStatement MGriess) (hb : Co1FiveCubeFacts)
    (hc : BabyFiveRankFact) (t : MGriess) (ht : orderOf t = 2) (E : Subgroup MGriess)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set MGriess)) (hEe : IsElemAbelian 5 E) :
    Nat.card E ≤ 5 ^ 3 := by
  obtain ⟨-, a, z, -, -, -, hcls, hA, hZ, -⟩ := id hE
  rcases hcls t ht with h | h
  · obtain ⟨-, hz, ⟨e⟩⟩ := hA t h
    have hZ2 : Nat.card (Subgroup.center (cent t)) = 2 ^ 1 := by
      rw [← Subgroup.card_map_of_injective (cent t).subtype_injective, hz, Nat.card_zpowers, ht,
        pow_one]
    exact card_le_of_le_quot Nat.prime_five (by norm_num) (IsPGroup.of_card hZ2) hc e hEt hEe
  · obtain ⟨-, -, -, ⟨e⟩, -, -⟩ := hZ t h
    exact card_le_of_le_quot Nat.prime_five (by norm_num) CFSG.pCore_isPGroup hb.1
      (e.trans CFSG.Sporadic.Co1Block.co1MatEquiv) hEt hEe

end Involution

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5
