module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_isOmega7Group [Finite G] {t : G} {L : Subgroup G} (h : Sec4Setting G t L) :
    IsOmega7Group L :=
  ⟨h.component.isQuasisimple, h.omega7⟩

theorem sec4_nonabelian [Finite G] {t : G} {L : Subgroup G} (h : Sec3Setting G t L) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h.component.isQuasisimple.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨(a' : G), (b' : G), fun hc => hab ?_⟩
  have h1 : a' * b' = b' * a' := Subtype.ext hc
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]

theorem sec4_t_mem_centralizer [Finite G] {t : G} {L : Subgroup G} (h : Sec3Setting G t L) :
    t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := Subgroup.mem_centralizer_iff.mp (h.component.le hl) t (Set.mem_singleton t)
  exact this.symm

theorem sec4_isSimpleGroup_quotient_oddCore [Finite G] {L : Subgroup G} (hL : IsOmega7Group L) :
    IsSimpleGroup (L ⧸ oddCore L) := by
  have hmodel := hL.2.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
  exact (CFSG.LieType.Simplicity.fam_classical_converse (L ⧸ oddCore L)
    ⟨.POmegaOdd, 3, 3, 1, hmodel⟩).2.2

private theorem sec4Struct_odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem sec4_odd_orderOf_of_mem_centralizer [Finite G] {L : Subgroup G} (hL : IsOmega7Group L)
    {x : G} (hxL : x ∈ L) (hxc : x ∈ centralizer (L : Set G)) : Odd (orderOf x) := by
  have hs := sec4_isSimpleGroup_quotient_oddCore hL
  have hx' : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro a
    exact Subtype.ext (hxc a a.2)
  have hxO : (⟨x, hxL⟩ : ↥L) ∈ oddCore ↥L := by
    rw [← center_eq_oddCore_of_simple hL.1 hs]
    exact hx'
  have hdvd : orderOf (⟨x, hxL⟩ : ↥L) ∣ Nat.card (oddCore ↥L) :=
    (oddCore ↥L).orderOf_dvd_natCard hxO
  have hodd : Odd (orderOf (⟨x, hxL⟩ : ↥L)) :=
    (sec4Struct_odd_card_oddCore ↥L).of_dvd_nat hdvd
  rwa [Subgroup.orderOf_mk x hxL] at hodd

theorem sec4_not_mem_of_mem_centralizer [Finite G] {L : Subgroup G} (hL : IsOmega7Group L)
    {x : G} (hx : orderOf x = 2) (hxc : x ∈ centralizer (L : Set G)) : x ∉ L := by
  intro hxL
  have h := sec4_odd_orderOf_of_mem_centralizer hL hxL hxc
  rw [hx] at h
  exact absurd h (by decide)

theorem sec4_t_not_mem [Finite G] {t : G} {L : Subgroup G} (h : Sec4Setting G t L) : t ∉ L :=
  sec4_not_mem_of_mem_centralizer (sec4_isOmega7Group h) h.involution
    (sec4_t_mem_centralizer h.toSec3Setting)

theorem sec4_mem_normalizer [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
  fun c hc => mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS c hc)

theorem sec4_t_mem_S [Finite G] {t : G} {S : Subgroup G}
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (ht : orderOf t = 2) : t ∈ S := by
  let H : Subgroup G := centralizer ({t} : Set G)
  have hS' : IsSylow2Of S H := hS
  have htH : t ∈ H := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  let t' : ↥H := ⟨t, htH⟩
  obtain ⟨P, hP⟩ := hS'.exists_sylow
  have ht'center : t' ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    show (a : G) * t = t * (a : G)
    exact (Subgroup.mem_centralizer_iff.mp a.2 t (Set.mem_singleton t)).symm
  haveI hnorm : (Subgroup.zpowers t').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ht'center)
  have ht'ord : orderOf t' = 2 := by
    change orderOf (⟨t, htH⟩ : ↥H) = 2
    rw [Subgroup.orderOf_mk t htH, ht]
  have hcard : Nat.card (Subgroup.zpowers t') = 2 := by
    rw [Nat.card_zpowers, ht'ord]
  have hp : IsPGroup 2 (Subgroup.zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have ht'P : t' ∈ (P : Subgroup ↥H) := hp.le_sylow_of_normal P (Subgroup.mem_zpowers t')
  have htmap : t ∈ (P : Subgroup ↥H).map H.subtype := ⟨t', ht'P, rfl⟩
  rwa [hP] at htmap

theorem sec4_isSylow2Of_inf [Finite G] {t : G} {L S : Subgroup G}
    (hL : L ≤ centralizer ({t} : Set G))
    (hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G))
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) : IsSylow2Of (S ⊓ L) L := by
  have hSH : S ≤ centralizer ({t} : Set G) := hS.1
  have hSnorm : S ≤ Subgroup.normalizer (L : Set G) := fun c hc => hN c (hSH hc)
  have hsup : S ⊔ L ≤ centralizer ({t} : Set G) := sup_le hSH hL
  have hSp : IsPGroup 2 ↥(S ⊓ L) :=
    hS.2.1.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  refine ⟨inf_le_right, hSp, ?_⟩
  have hE : L.relIndex (S ⊔ L) = L.relIndex S := by
    haveI : (L.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hSnorm
    haveI : (L.subgroupOf (S ⊔ L)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hSnorm
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient S L hSnorm
    simpa only [Subgroup.relIndex, Subgroup.index] using (Nat.card_congr e.toEquiv).symm
  have hii : S.relIndex L * L.relIndex S = (S ⊓ L).relIndex (S ⊔ L) := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := S) (K := L) (L := S ⊔ L)
    rw [inf_eq_left.mpr le_sup_right, hE] at h
    exact h
  have hiii : (S ⊓ L).relIndex L * L.relIndex S = (S ⊓ L).relIndex (S ⊔ L) := by
    rw [Subgroup.inf_relIndex_right (H := S) (K := L)]
    exact hii
  have hiv : L.relIndex S * S.relIndex (S ⊔ L) = (S ⊓ L).relIndex (S ⊔ L) := by
    have h := Subgroup.relIndex_mul_relIndex (H := S ⊓ L) (K := S) (L := S ⊔ L)
      inf_le_left le_sup_left
    rw [Subgroup.inf_relIndex_left (H := S) (K := L)] at h
    exact h
  have hLne : L.relIndex S ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := L) (K := S)
    rw [h0, zero_mul] at h
    haveI : Nonempty ↥S := ⟨1⟩
    exact Nat.card_pos.ne' h.symm
  have heq : (S ⊓ L).relIndex L = S.relIndex (S ⊔ L) := by
    refine Nat.mul_right_cancel (Nat.pos_of_ne_zero hLne) ?_
    rw [mul_comm (S.relIndex (S ⊔ L)) (L.relIndex S), hiii, hiv]
  have hdvd : S.relIndex (S ⊔ L) ∣ S.relIndex (centralizer ({t} : Set G)) := by
    have h := Subgroup.relIndex_mul_relIndex (H := S) (K := S ⊔ L)
      (L := centralizer ({t} : Set G)) le_sup_left hsup
    exact ⟨(S ⊔ L).relIndex (centralizer ({t} : Set G)), h.symm⟩
  rw [heq]
  exact fun h2 => hS.2.2 (dvd_trans h2 hdvd)

theorem sec4_eq_of_commute [Finite G] {H : Subgroup G}
    (hcyc : ∀ P : Sylow 2 H, IsCyclic (P : Subgroup H)) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a * a = 1) (hb2 : orderOf b = 2) (hab : a * b = b * a) : a = 1 ∨ a = b := by
  by_cases h1 : a = 1
  · exact Or.inl h1
  refine Or.inr ?_
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
  have ha' : orderOf a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have := eq_of_commuting_involutions_of_cyclic_sylow hcyc
    (a := (⟨a, ha⟩ : H)) (b := (⟨b, hb⟩ : H))
    (by rw [Subgroup.orderOf_mk]; exact ha') (by rw [Subgroup.orderOf_mk]; exact hb2)
    (Subtype.ext hab)
  exact congrArg Subtype.val this

end CFSG.OddStandard.SmallF3.Omega
