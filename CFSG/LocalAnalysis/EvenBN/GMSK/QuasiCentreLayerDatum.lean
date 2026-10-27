module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRoot

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

@[expose] def qcConjAut {H : Type} [Group H] (L : Subgroup H) {a : H}
    (haL : a ∈ normalizer (L : Set H)) : MulAut ↥L where
  toFun x := ⟨a * x * a⁻¹, (mem_set_normalizer_iff.1 haL x).1 x.2⟩
  invFun x := ⟨a⁻¹ * x * a, (mem_set_normalizer_iff''.1 haL x).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem qcConjAut_apply_coe {H : Type} [Group H] (L : Subgroup H) {a : H}
    (haL : a ∈ normalizer (L : Set H)) (x : ↥L) :
    ((qcConjAut L haL x : ↥L) : H) = a * x * a⁻¹ := rfl

theorem quasi_datum_of_component {H : Type} [Group H] [Finite H] {L : Subgroup H} {a : H}
    (ha : orderOf a = 2) (haL : a ∈ normalizer (L : Set H)) {J : Subgroup H} (hJL : J ≤ L)
    (haJ : a ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal)
    (hrank : ∀ P : Subgroup H, P ≤ centralizer (J : Set H) → IsPGroup 2 P → Nat.card P ≤ 2)
    (hnt : ∃ d ∈ L, a⁻¹ * d * a ≠ d) :
    ∃ α : MulAut ↥L, orderOf α = 2 ∧
      J.subgroupOf L ≤ α.toMonoidHom.eqLocus (MonoidHom.id ↥L) ∧
      ((J.subgroupOf L).subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id ↥L))).Normal ∧
      FixedRootRankOne α (J.subgroupOf L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by rw [← sq]; exact ha2
  have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one]; exact haa
  set α : MulAut ↥L := qcConjAut L haL
  have hαx : ∀ x : ↥L, ((α x : ↥L) : H) = a * x * a⁻¹ := fun x => rfl
  have hmem : ∀ x : ↥L, x ∈ α.toMonoidHom.eqLocus (MonoidHom.id ↥L) ↔
      a * (x : H) = x * a := by
    intro x
    change α x = x ↔ _
    rw [← Subtype.coe_inj, hαx, mul_inv_eq_iff_eq_mul]
  have h1 : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [sq, MulAut.mul_apply]
      change a * (a * (x : H) * a⁻¹) * a⁻¹ = x
      calc a * (a * (x : H) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x := by rw [haa]; group
    · intro h1
      obtain ⟨d, hd, hdne⟩ := hnt
      apply hdne
      have h := congrArg (fun β : MulAut ↥L => ((β ⟨d, hd⟩ : ↥L) : H)) h1
      change a * d * a⁻¹ = d at h
      rw [hainv] at h ⊢
      exact h
  have h2 : J.subgroupOf L ≤ α.toMonoidHom.eqLocus (MonoidHom.id ↥L) := by
    intro x hx
    rw [hmem]
    exact (mem_centralizer_iff.1 haJ _ (mem_subgroupOf.1 hx)).symm
  have h3 : ((J.subgroupOf L).subgroupOf
      (α.toMonoidHom.eqLocus (MonoidHom.id ↥L))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
    have hxc : ((x : ↥L) : H) ∈ centralizer ({a} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      exact ((hmem x).1 x.2).symm
    have hgc : ((g : ↥L) : H) ∈ centralizer ({a} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      exact ((hmem g).1 g.2).symm
    exact hJn.conj_mem ⟨((x : ↥L) : H), hxc⟩ (mem_subgroupOf.2 hx) ⟨((g : ↥L) : H), hgc⟩
  have h4 : FixedRootRankOne α (J.subgroupOf L) := by
    intro P hP hP2
    set P' := P.map L.subtype with hP'
    have hP'J : P' ≤ centralizer (J : Set H) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [mem_centralizer_iff]
      intro j hj
      have h := mem_centralizer_iff.1 (hP hp).2 ⟨j, hJL hj⟩ (mem_subgroupOf.2 hj)
      exact congrArg Subtype.val h
    have hP'a : P' ≤ centralizer ({a} : Set H) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [mem_centralizer_singleton_iff]
      exact ((hmem p).1 (hP hp).1).symm
    have hz2 : IsPGroup 2 (zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    have hzN : P' ≤ normalizer (zpowers a : Set H) := by
      refine le_trans ?_ (centralizer_le_normalizer _)
      rw [le_centralizer_iff, zpowers_le, mem_centralizer_iff]
      intro p hp
      exact mem_centralizer_singleton_iff.1 (hP'a hp)
    have hQ := IsPGroup.to_sup_of_normal_right' (hP2.map L.subtype) hz2 hzN
    have hQJ : P' ⊔ zpowers a ≤ centralizer (J : Set H) := sup_le hP'J (zpowers_le.2 haJ)
    have hQa : zpowers a = P' ⊔ zpowers a :=
      eq_of_le_of_card_ge le_sup_right (by rw [Nat.card_zpowers, ha]; exact hrank _ hQJ hQ)
    have hP'le : P' ≤ zpowers a := hQa ▸ le_sup_left
    have hcard : Nat.card P = Nat.card P' := (card_map_of_injective L.subtype_injective).symm
    refine ⟨?_, fun hout => ?_⟩
    · rw [hcard]
      calc Nat.card P' ≤ Nat.card (zpowers a) := card_le_of_le hP'le
        _ = 2 := by rw [Nat.card_zpowers, ha]
    · by_contra hne
      obtain ⟨⟨p, hp⟩, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      have hpt := hP'le ⟨p, hp, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hpt
      change a ^ k = (p : H) at hk
      have hpz : (p : H) = 1 ∨ (p : H) = a := by
        rw [← hk, ← zpow_mod_orderOf, ha]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          rw [Nat.cast_ofNat, h, zpow_zero]
        · right
          rw [Nat.cast_ofNat, h, zpow_one]
      rcases hpz with h1 | hap
      · exact hp1 (Subtype.ext (Subtype.ext h1))
      · have haLmem : a ∈ L := hap ▸ p.2
        refine hout ⟨⟨a, haLmem⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
        rw [hαx, MulAut.conj_apply]
        rfl
  exact ⟨α, h1, h2, h3, h4⟩

end CFSG.LocalAnalysis.EvenBN.GMSK
