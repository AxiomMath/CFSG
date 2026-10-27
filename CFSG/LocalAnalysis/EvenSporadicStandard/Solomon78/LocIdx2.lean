module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.MRowExistence
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

structure IsIdx2Cover (H : Type) [Group H] (E : Subgroup H) : Prop where
  normal : E.Normal
  index_eq : E.index = 2
  quasisimple : CFSG.Open.IsQuasisimple E
  card_center : Nat.card (center E) = 2
  centralizer_le : centralizer (E : Set H) ≤ E

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem central_eq_of_idx2Cover {L K : Subgroup G} {u : G} (huL : u ∈ L) (hu2 : orderOf u = 2)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set G))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set G)))) :
    u ∈ K ∧ ∀ c ∈ L, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = u := by
  set Cu : Subgroup G := L ⊓ centralizer ({u} : Set G) with hCu
  set E : Subgroup ↥Cu := K.subgroupOf Cu with hE
  let u' : ↥Cu := ⟨u, huL, mem_centralizer_singleton_iff.2 rfl⟩
  have hu'1 : u' ≠ 1 := fun h => by
    have h1 : u = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hu'c : ∀ y : ↥Cu, y * u' = u' * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2.2)
  have hu'E : u' ∈ E := hcov.centralizer_le (mem_centralizer_iff.2 fun y _ => hu'c y)
  have hcenU : (⟨u', hu'E⟩ : ↥E) ∈ center ↥E :=
    Subgroup.mem_center_iff.2 fun y => Subtype.ext (hu'c y)
  have hx1 : (⟨⟨u', hu'E⟩, hcenU⟩ : ↥(center ↥E)) ≠ 1 := fun h => hu'1
    (congrArg (fun w : ↥(center ↥E) => ((w : ↥E) : ↥Cu)) h)
  refine ⟨mem_subgroupOf.1 hu'E, fun c hcL hc => ?_⟩
  have hcu : c * u = u * c := hc u (mem_subgroupOf.1 hu'E)
  have hcC : c ∈ Cu := ⟨hcL, mem_centralizer_singleton_iff.2 hcu⟩
  have hcE : (⟨c, hcC⟩ : ↥Cu) ∈ E := by
    refine hcov.centralizer_le (mem_centralizer_iff.2 fun y hy => ?_)
    exact Subtype.ext (hc _ (mem_subgroupOf.1 hy)).symm
  have hcen : (⟨⟨c, hcC⟩, hcE⟩ : ↥E) ∈ center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subtype.ext (hc _ (mem_subgroupOf.1 y.2)).symm)
  rcases eq_one_or_eq_of_card_eq_two hcov.card_center hx1 ⟨⟨⟨c, hcC⟩, hcE⟩, hcen⟩ with h | h
  · left
    exact congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : G)) h
  · right
    exact congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : G)) h

theorem card_le_two_mul_card_inf {H : Type*} [Group H] [Finite H] (E P : Subgroup H) [E.Normal]
    (hi : E.index = 2) : Nat.card P ≤ 2 * Nat.card ↥(P ⊓ E) := by
  have h1 : E.relIndex P ∣ 2 := hi ▸ Subgroup.relIndex_dvd_index_of_normal E P
  have h2 := Subgroup.relIndex_mul_card (H := E) (K := P)
  rw [inf_comm] at h2
  have h3 : E.relIndex P ≤ 2 := Nat.le_of_dvd (by norm_num) h1
  calc Nat.card P = E.relIndex P * Nat.card ↥(P ⊓ E) := h2.symm
    _ ≤ 2 * Nat.card ↥(P ⊓ E) := Nat.mul_le_mul_right _ h3

theorem solomonLocal_of_idx2Cover {L K : Subgroup G} {u : G} (hsimple : IsSimpleGroup L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hout : OutTwo ↥L) (hu : u ∈ L) (hu2 : orderOf u = 2)
    (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set G))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set G)))) : SolomonLocal L K u := by
  obtain ⟨huK, hC⟩ := central_eq_of_idx2Cover hu hu2 hcov
  set Cu : Subgroup G := L ⊓ centralizer ({u} : Set G) with hCu
  have hKC : K ≤ Cu := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  let u' : ↥L := ⟨u, hu⟩
  have hz2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hxk : ∀ x : ↥L, (∀ k ∈ (K.subgroupOf L : Subgroup ↥L), k * x = x * k) → x ∈ zpowers u' := by
    intro x hx
    have h1 : ∀ k ∈ K, (x : G) * k = k * (x : G) := fun k hk =>
      (congrArg Subtype.val (hx ⟨k, hKL hk⟩ (mem_subgroupOf.2 hk))).symm
    rcases hC (x : G) x.2 h1 with h | h
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = u' from Subtype.ext h]
      exact mem_zpowers u'
  have hq : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv'
      ((Subgroup.subgroupOfEquivOfLe hKL).trans (Subgroup.subgroupOfEquivOfLe hKC).symm).symm
      hcov.quasisimple
  have hcentC : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2 := by
    calc Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L))
        ≤ Nat.card ↥(zpowers u') := Subgroup.card_le_of_le fun x hx =>
          hxk x fun k hk => (mem_centralizer_iff.1 hx k hk)
      _ = 2 := by rw [Nat.card_zpowers, hz2]
  have hKz : K.subgroupOf L ≤ centralizer ({u'} : Set ↥L) := fun k hk =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (hKu k (mem_subgroupOf.1 hk)))
  have hHn : ((K.subgroupOf L).subgroupOf (centralizer ({u'} : Set ↥L))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : ↥L) : G) ∈ K := mem_subgroupOf.1 (mem_subgroupOf.1 hn)
    have hgC : (((g : ↥L) : G)) ∈ Cu := ⟨(g : ↥L).2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 g.2))⟩
    have hnC : (((n : ↥L) : G)) ∈ Cu := hKC hn'
    have := hcov.normal
    have h1 := this.conj_mem ⟨((n : ↥L) : G), hnC⟩ (mem_subgroupOf.2 hn')
      ⟨((g : ↥L) : G), hgC⟩
    exact mem_subgroupOf.2 (mem_subgroupOf.2 (mem_subgroupOf.1 h1))
  have hsyl : ∀ U : Subgroup ↥L, IsPGroup 2 U →
      U ≤ centralizer ({u'} : Set ↥L) ⊓ centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) →
        Nat.card U ≤ 2 := by
    intro U _ hU
    calc Nat.card U ≤ Nat.card ↥(zpowers u') := Subgroup.card_le_of_le fun x hx =>
          hxk x fun k hk => (mem_centralizer_iff.1 (hU hx).2 k hk)
      _ = 2 := by rw [Nat.card_zpowers, hz2]
  have hstd : CFSG.Open.standardComponentIsStandard (K.subgroupOf L) :=
    (M24Std.standardComponentIsStandard_of_normal hz2 hq hKz hHn hsyl).1
  exact
  { simpleL := hsimple
    nonabelianL := hnab
    u_order := hu2
    u_mem := hu
    K_le := hKL
    u_mem_centralizer_K := mem_centralizer_iff.2 hKu
    standard_in_L := hstd
    autCentralizer_two := twoAdic_autCentralizer_le hout hcentC }

end CFSG.EvenSporadicStandard.Solomon78
