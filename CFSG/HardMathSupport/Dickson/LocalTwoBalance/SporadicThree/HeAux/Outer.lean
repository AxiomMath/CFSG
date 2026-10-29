module

public import CFSG.Sporadic.HeldB.OuterCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux

open CFSG.Sporadic.HeldB

theorem le_of_relIndex_two_of_odd' {G : Type*} [Group G] [Finite G] {C D O : Subgroup G}
    (hOC : O ≤ C) (hD : D.relIndex C = 2) (hO : Odd (Nat.card O)) : O ≤ D := by
  intro o ho
  have hi : (D.subgroupOf C).index = 2 := hD
  have hsq : (⟨o, hOC ho⟩ : ↥C) ^ 2 ∈ D.subgroupOf C := Subgroup.sq_mem_of_index_two hi _
  have hsq' : o ^ 2 ∈ D := by
    rw [Subgroup.mem_subgroupOf] at hsq
    simpa using hsq
  obtain ⟨k, hk⟩ := hO
  have hm : orderOf o ∣ 2 * k + 1 := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard O ho
  have hpow : o ^ (2 * k + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 hm
  have : o = (o ^ 2) ^ (k + 1) := by
    calc o = o ^ (2 * k + 1) * o := by rw [hpow, one_mul]
      _ = (o ^ 2) ^ (k + 1) := by rw [← pow_mul, ← pow_succ]; ring_nf
  rw [this]
  exact D.pow_mem hsq' _


theorem heOuterQuot_class_ge {q : ↥heOuterD ⧸ Subgroup.center ↥heOuterD} (hq : q ≠ 1) :
    70 ≤ (ConjClasses.mk q).carrier.ncard := by
  obtain ⟨e, he⟩ := heOuterQuot_classes
  have h0 : e 0 = ConjClasses.mk 1 := by
    obtain ⟨i, hi⟩ := e.surjective (ConjClasses.mk (1 : ↥heOuterD ⧸ Subgroup.center ↥heOuterD))
    have h1 : (e i).carrier.ncard = 1 := by
      rw [hi, ConjClasses.carrier_eq_preimage_mk]
      have : ConjClasses.mk ⁻¹' {ConjClasses.mk (1 : ↥heOuterD ⧸ Subgroup.center ↥heOuterD)} =
          {1} := by
        ext x
        simp [ConjClasses.mk_eq_mk_iff_isConj]
      rw [this, Set.ncard_singleton]
    rw [he] at h1
    have key : ∀ j : Fin 9, heOuterClassSizes j = 1 → j = 0 := by decide
    rw [← key i h1, hi]
  obtain ⟨i, hi⟩ := e.surjective (ConjClasses.mk q)
  by_contra hlt
  push Not at hlt
  have hsz : heOuterClassSizes i < 70 := by rw [← he i, hi]; exact hlt
  have key : ∀ j : Fin 9, heOuterClassSizes j < 70 → j = 0 := by decide
  rw [key i hsz, h0] at hi
  exact hq (isConj_one_right.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hi))

theorem heOuterD_central_of_centralizer_le {d : Equiv.Perm (Fin 8330)} (hdP : d ∈ heP)
    (hd3 : orderOf d = 3)
    (h2 : 504 ≤ Nat.card ↥(Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP))
    (hcent : ∀ x ∈ heP, x * d = d * x → x * heAutU = heAutU * x) :
    d ∈ Subgroup.map heOuterD.subtype (Subgroup.center ↥heOuterD) := by
  have hCeq : heOuterC = heP ⊓ Subgroup.centralizer {heAutU} := heOuterC_eq
  have hDC : heOuterD ≤ heOuterC := heOuterD_le_C
  have hDP : heOuterD ≤ heP := fun x hx => by
    have := hDC hx
    rw [hCeq] at this
    exact this.1
  have hdC : d ∈ heOuterC := by
    rw [hCeq]
    exact ⟨hdP, Subgroup.mem_centralizer_singleton_iff.2 (hcent d hdP rfl)⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers d)) := by
    rw [Nat.card_zpowers, hd3]
    exact ⟨1, rfl⟩
  have hdD : d ∈ heOuterD :=
    le_of_relIndex_two_of_odd' ((Subgroup.zpowers_le).2 hdC) heOuterD_relIndex hodd
      (Subgroup.mem_zpowers d)
  have hXC : Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP ≤ heOuterC := by
    intro x hx
    rw [hCeq]
    exact ⟨hx.2, Subgroup.mem_centralizer_singleton_iff.2
      (hcent x hx.2 (Subgroup.mem_centralizer_singleton_iff.1 hx.1))⟩
  have hrel : heOuterD.relIndex
      (Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := heOuterD) hXC
      (by rw [heOuterD_relIndex]; norm_num)
    rwa [heOuterD_relIndex] at this
  have hmul := Subgroup.relIndex_mul_card (H := heOuterD)
    (K := Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP)
  have hT : 252 ≤ Nat.card ↥(heOuterD ⊓
      (Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP)) := by
    have h3 : Nat.card ↥(Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) ≤
        2 * Nat.card ↥(heOuterD ⊓
          (Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP)) := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hrel
    omega
  have hTmap : (Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD)).map
      heOuterD.subtype =
      heOuterD ⊓ (Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.2, Subgroup.mem_centralizer_singleton_iff.2 ?_, hDP t.2⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 ht)
    · rintro ⟨hyD, hyc, -⟩
      exact ⟨⟨y, hyD⟩, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hyc)), rfl⟩
  have hTcard : 252 ≤
      Nat.card ↥(Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD)) := by
    have := Subgroup.card_map_of_injective
      (K := Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD))
      heOuterD.subtype_injective
    rw [hTmap] at this
    omega
  have hidx : (Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD)).index ≤ 30 := by
    have h1 := Subgroup.card_mul_index
      (Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD))
    rw [card_heOuterD] at h1
    by_contra hgt
    push Not at hgt
    nlinarith
  have hq1 : (QuotientGroup.mk (⟨d, hdD⟩ : ↥heOuterD) : ↥heOuterD ⧸ Subgroup.center ↥heOuterD) =
      1 := by
    by_contra hq
    have h70 := heOuterQuot_class_ge hq
    have hcls : (ConjClasses.mk (QuotientGroup.mk (⟨d, hdD⟩ : ↥heOuterD) :
        ↥heOuterD ⧸ Subgroup.center ↥heOuterD)).carrier.ncard =
        (Subgroup.centralizer ({(QuotientGroup.mk (⟨d, hdD⟩ : ↥heOuterD) :
          ↥heOuterD ⧸ Subgroup.center ↥heOuterD)} : Set _)).index := by
      rw [Subgroup.index_centralizer_eq_ncard]
      rfl
    have h1 : (Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD)).map
        (QuotientGroup.mk' (Subgroup.center ↥heOuterD)) ≤
        Subgroup.centralizer ({(QuotientGroup.mk (⟨d, hdD⟩ : ↥heOuterD) :
          ↥heOuterD ⧸ Subgroup.center ↥heOuterD)} : Set _) := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_singleton_iff.1 ht
      change QuotientGroup.mk t * QuotientGroup.mk (⟨d, hdD⟩ : ↥heOuterD) =
        QuotientGroup.mk (⟨d, hdD⟩ : ↥heOuterD) * QuotientGroup.mk t
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
    have h2 := Subgroup.index_map_dvd
      (H := Subgroup.centralizer ({(⟨d, hdD⟩ : ↥heOuterD)} : Set ↥heOuterD))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥heOuterD))
    have h3 := Subgroup.index_dvd_of_le h1
    have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (h3.trans h2)
    omega
  have hzc : (⟨d, hdD⟩ : ↥heOuterD) ∈ Subgroup.center ↥heOuterD :=
    (QuotientGroup.eq_one_iff _).1 hq1
  exact ⟨⟨d, hdD⟩, hzc, rfl⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.HeAux
