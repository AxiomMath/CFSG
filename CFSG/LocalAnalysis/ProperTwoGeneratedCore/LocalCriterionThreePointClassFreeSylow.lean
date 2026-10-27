module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowIndex

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G] [Finite G]

theorem odd_kernel_noncentral_invariant_sylow
    (B J : Subgroup G) [B.Normal] [J.Normal] (t : G) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hJB : J ≤ B)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (G ⧸ J))
    (hnoncentral : ¬ B ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ P : Sylow p B,
      t ∈ Subgroup.normalizer (((P : Subgroup B).map B.subtype : Subgroup G) : Set G) ∧
      ¬ (P : Subgroup B).map B.subtype ≤ Subgroup.centralizer ({t} : Set G) := by
  let C := Subgroup.centralizer ({t} : Set G)
  have hindexne : C.relIndex B ≠ 1 := fun heq => hnoncentral (Subgroup.relIndex_eq_one.mp heq)
  have hindexodd : Odd (C.relIndex B) :=
    odd_central_quotient_subgroup_centralizer_index_odd J B t ht hJodd hJB hcentral
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hindexne
  have hpodd : Odd p := hindexodd.of_dvd_nat hpdvd
  obtain ⟨P, hPnorm⟩ := odd_central_quotient_invariant_sylow_exists
    p hp B J t ht hJodd hJB hcentral
  have hformula := odd_central_quotient_invariant_sylow_index
    p hp B J t ht hJodd hJB hcentral P hPnorm
  have hindexpos : C.relIndex B ≠ 0 := by
    change (C.subgroupOf B).index ≠ 0
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hfactorpos : 0 < (C.relIndex B).factorization p :=
    hp.factorization_pos_of_dvd hindexpos hpdvd
  have hpartgt : 1 < p ^ (C.relIndex B).factorization p :=
    Nat.one_lt_pow (Nat.ne_of_gt hfactorpos) hp.one_lt
  refine ⟨p, hp, hpodd, P, hPnorm, ?_⟩
  intro hPC
  have heq := Subgroup.relIndex_eq_one.mpr hPC
  rw [heq] at hformula
  exact (Nat.ne_of_gt hpartgt) hformula.symm

theorem internal_noncentral_sylow_transport
    (X L : Subgroup G) (hXL : X ≤ L) (t : G) (htL : t ∈ L)
    (p : ℕ) (hp : p.Prime) (P₀ : Sylow p (X.subgroupOf L))
    (hPnorm : (⟨t, htL⟩ : L) ∈ Subgroup.normalizer
      (((P₀ : Subgroup (X.subgroupOf L)).map (X.subgroupOf L).subtype : Subgroup L) : Set L))
    (hPnoncentral : ¬ (P₀ : Subgroup (X.subgroupOf L)).map (X.subgroupOf L).subtype ≤
      Subgroup.centralizer ({(⟨t, htL⟩ : L)} : Set L)) :
    ∃ P : Sylow p X,
      (P : Subgroup X).map X.subtype =
        ((P₀ : Subgroup (X.subgroupOf L)).map (X.subgroupOf L).subtype).map L.subtype ∧
      t ∈ Subgroup.normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) ∧
      ¬ (P : Subgroup X).map X.subtype ≤ Subgroup.centralizer ({t} : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let e := Subgroup.subgroupOfEquivOfLe hXL
  let P : Sylow p X := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have himage : (P : Subgroup X).map X.subtype =
      ((P₀ : Subgroup (X.subgroupOf L)).map (X.subgroupOf L).subtype).map L.subtype := by
    change ((P₀ : Subgroup (X.subgroupOf L)).map e.toMonoidHom).map X.subtype = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine ⟨P, himage, ?_, ?_⟩
  · rw [himage]
    exact Subgroup.le_normalizer_map L.subtype
      (Subgroup.mem_map_of_mem L.subtype hPnorm)
  · intro hPC
    apply hPnoncentral
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply Subgroup.mem_centralizer_singleton_iff.mp
    apply hPC
    rw [himage]
    exact Subgroup.mem_map_of_mem L.subtype hx

theorem normalized_subgroup_noncentral_invariant_sylow
    (J X : Subgroup G) [J.Normal] (t : G) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set G))
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (G ⧸ J))
    (hnoncentral : ¬ X ≤ Subgroup.centralizer ({t} : Set G)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ P : Sylow p X,
      t ∈ Subgroup.normalizer (((P : Subgroup X).map X.subtype : Subgroup G) : Set G) ∧
      ¬ (P : Subgroup X).map X.subtype ≤ Subgroup.centralizer ({t} : Set G) := by
  let L := X ⊔ Subgroup.zpowers t
  let B := X.subgroupOf L
  let A := B ⊓ J.subgroupOf L
  have htL : t ∈ L := (show Subgroup.zpowers t ≤ L from le_sup_right)
    (Subgroup.mem_zpowers t)
  let tL : L := ⟨t, htL⟩
  have hXL : X ≤ L := le_sup_left
  obtain ⟨hBnormal, hAnormal, hAodd, hAB, _, hAcentral⟩ :=
    normalized_subgroup_odd_central_quotient J X t hJodd hXnorm hcentral
  let : B.Normal := hBnormal
  let : A.Normal := hAnormal
  have hBnoncentral : ¬ B ≤ Subgroup.centralizer ({tL} : Set L) := by
    intro hBC
    apply hnoncentral
    intro x hx
    let xL : L := ⟨x, hXL hx⟩
    have hxB : xL ∈ B := hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hBC hxB)))
  have htorder : orderOf tL = 2 := (Subgroup.orderOf_coe tL).symm.trans ht
  obtain ⟨p, hp, hpodd, P₀, hPnorm, hPnoncentral⟩ :=
    odd_kernel_noncentral_invariant_sylow B A tL htorder hAodd hAB hAcentral hBnoncentral
  obtain ⟨P, _, hPnormG, hPnoncentralG⟩ :=
    internal_noncentral_sylow_transport X L hXL t htL p hp P₀ hPnorm hPnoncentral
  exact ⟨p, hp, hpodd, P, hPnormG, hPnoncentralG⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
