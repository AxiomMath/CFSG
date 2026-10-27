module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {p : ℕ}

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem card_sup_of_coprime [Fact p.Prime] {N Q : Subgroup G} [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hQ : IsPGroup p Q) :
    Nat.card (N ⊔ Q : Subgroup G) = Nat.card Q * Nat.card N := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hdisj : N ⊓ Q = ⊥ := by
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hk]
    exact (Nat.Coprime.pow_left k hN).symm
  have h1 := Subgroup.relIndex_mul_card N (N ⊔ Q)
  rw [inf_eq_left.mpr le_sup_left, Subgroup.relIndex_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card N Q
  rw [hdisj, Subgroup.card_bot, mul_one] at h2
  rw [← h1, h2]

theorem isSylowOf_sup_of_coprime [Fact p.Prime] {N Q : Subgroup G} [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hQ : IsPGroup p Q) : IsSylowOf p Q (N ⊔ Q) := by
  apply isSylowOf_of_card le_sup_right
  rw [card_sup_of_coprime hN hQ]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hp : p.Prime := Fact.out
  have hNp : ¬ p ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd hp).mp hN
  rw [hk, Nat.factorization_mul (pow_ne_zero k hp.ne_zero) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hNp, add_zero]

end Sylow

section Bridges

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem card_Op_p'p :
    Nat.card (Op_p'p p H) = Nat.card (pCore p (H ⧸ pPrimeCore p H)) *
      Nat.card (pPrimeCore p H) := by
  have h := Subgroup.relIndex_mul_card (pPrimeCore p H) (Op_p'p p H)
  rw [inf_eq_left.mpr pPrimeCore_le_Op_p'p] at h
  rw [← h]
  congr 1
  let f : Op_p'p p H →* H ⧸ pPrimeCore p H :=
    (QuotientGroup.mk' (pPrimeCore p H)).comp (Op_p'p p H).subtype
  have hker : f.ker = (pPrimeCore p H).subgroupOf (Op_p'p p H) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hrange : f.range = pCore p (H ⧸ pPrimeCore p H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Op_p'p,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]

theorem sup_eq_Op_p'p_iff_isSylowOf [Fact p.Prime] {Q : Subgroup H} (hQ : IsPGroup p Q) :
    pPrimeCore p H ⊔ Q = Op_p'p p H ↔ IsSylowOf p Q (Op_p'p p H) := by
  have hcop : Nat.Coprime p (Nat.card (pPrimeCore p H)) := pPrimeCore_coprime_card
  have hsyl := isSylowOf_sup_of_coprime hcop hQ
  constructor
  · intro h
    rwa [h] at hsyl
  · intro h
    have hle : pPrimeCore p H ⊔ Q ≤ Op_p'p p H := sup_le pPrimeCore_le_Op_p'p h.le
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_sup_of_coprime hcop hQ, card_Op_p'p, h.card_eq]
    apply Nat.mul_le_mul_right
    have hP := (pCore_isPGroup (G := H ⧸ pPrimeCore p H) (p := p))
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    have hdvd : Nat.card (pCore p (H ⧸ pPrimeCore p H)) ∣ Nat.card (Op_p'p p H) := by
      rw [card_Op_p'p]
      exact Dvd.intro _ rfl
    rw [hk] at hdvd ⊢
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd)

theorem isPConstrained_iff_pConstrainedGroup [Fact p.Prime] :
    IsPConstrained p H ↔ PConstrainedGroup (G := H) p := by
  constructor
  · intro h Q hQ hsup
    exact h Q ((sup_eq_Op_p'p_iff_isSylowOf hQ).mp hsup)
  · intro h P hP
    exact h P hP.isPGroup ((sup_eq_Op_p'p_iff_isSylowOf hP.isPGroup).mpr hP)

omit [Finite H] in
theorem IsPStable.pStableGroup' [Fact p.Prime] (h : IsPStable p H) :
    PStableGroup' (G := H) p := by
  intro Q A hn hQ hA hAN hcomm
  dsimp only
  by_cases hQ1 : Q = ⊥
  · subst hQ1
    rintro _ ⟨a, -, rfl⟩
    have ha : (QuotientGroup.mk' ((centralizer ((⊥ : Subgroup H) : Set H)).subgroupOf
        (normalizer ((⊥ : Subgroup H) : Set H)))) a = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hx
      simp [hx]
    rw [ha]
    exact one_mem _
  · have hA' := h.2 Q A hQ1 hQ hn hA hAN hcomm
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n, hn', hna⟩ := hA' ha
    have : n = a := Subtype.ext hna
    rw [← this]
    exact hn'

end Bridges

section ZJ

variable {G : Type*} [Group G] [Finite G] [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem thompsonCenter_le_self (P : Subgroup G) : thompsonCenter (G := G) P ≤ P :=
  inf_le_left.trans (sSup_le fun _ hA => hA.1)

theorem zj_factorization (hp : p ≠ 2) (hcon : IsPConstrained p G) (hst : IsPStable p G)
    (P : Sylow p G) :
    pPrimeCore p G ⊔ normalizer (thompsonCenter (P : Subgroup G) : Set G) = ⊤ := by
  set Z : Subgroup G := thompsonCenter (G := G) (P : Subgroup G) with hZ
  have hN : (Z ⊔ pPrimeCore p G).Normal :=
    G_theorem_8_2_11 (G := G) (p := p) hp hst.1
      (isPConstrained_iff_pConstrainedGroup.mp hcon) hst.pStableGroup' P
  have hZp : IsPGroup p Z := P.isPGroup'.to_le (thompsonCenter_le_self _)
  have hM : (pPrimeCore p G ⊔ Z).Normal := by rwa [sup_comm]
  have hsyl : IsSylowOf p Z (pPrimeCore p G ⊔ Z) :=
    isSylowOf_sup_of_coprime pPrimeCore_coprime_card hZp
  obtain ⟨T, hT⟩ := hsyl
  have hfr := Sylow.normalizer_sup_eq_top (N := pPrimeCore p G ⊔ Z) T
  rw [hT] at hfr
  apply top_le_iff.mp
  rw [← hfr]
  apply sup_le le_sup_right (sup_le le_sup_left (le_sup_of_le_right Subgroup.le_normalizer))

theorem zj_factorization_mul (hp : p ≠ 2) (hcon : IsPConstrained p G) (hst : IsPStable p G)
    (P : Sylow p G) :
    (pPrimeCore p G : Set G) * (normalizer (thompsonCenter (P : Subgroup G) : Set G) : Set G) =
      Set.univ := by
  rw [← Subgroup.normal_mul, zj_factorization hp hcon hst P, Subgroup.coe_top]

end ZJ

universe u

end CFSG.ABGLocalTools
