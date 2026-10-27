module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem oddBarConj_eq_one_of_mem_coreActionKernel' {L : Subgroup G}
    {g : ↥(normalizer (L : Set G))} (hg : (g : G) ∈ coreActionKernel L) :
    oddBarConj L g = 1 := by
  obtain ⟨-, hc⟩ := mem_coreActionKernel.mp hg
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  have hj : (g : G) * y * (g : G)⁻¹ ∈ L := (mem_normalizer_iff.mp g.2 y).mp y.2
  obtain ⟨o, ho, hoe⟩ := mem_map.mp (hc _ hj)
  convert ho using 1
  apply Subtype.ext
  rw [subtype_apply] at hoe
  rw [hoe]
  simp only [coe_mul, coe_inv]
  group

theorem exists_mul_of_mem_sup_coreActionKernel' {K : Subgroup G} {x : G}
    (hx : x ∈ K ⊔ coreActionKernel K) : ∃ k ∈ K, ∃ c ∈ coreActionKernel K, k * c = x := by
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hCN : coreActionKernel K ≤ normalizer (K : Set G) := fun c hc =>
    (mem_coreActionKernel.mp hc).1
  have hxN : x ∈ normalizer (K : Set G) := (sup_le hKN hCN) hx
  have h1 : (K ⊔ coreActionKernel K).subgroupOf (normalizer (K : Set G)) =
      K.subgroupOf (normalizer (K : Set G)) ⊔
        (coreActionKernel K).subgroupOf (normalizer (K : Set G)) := by
    apply map_injective (normalizer (K : Set G)).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hKN hCN), map_subgroupOf_eq_of_le hKN,
      map_subgroupOf_eq_of_le hCN]
  have h2 : (⟨x, hxN⟩ : ↥(normalizer (K : Set G))) ∈
      ((K.subgroupOf (normalizer (K : Set G)) ⊔
        (coreActionKernel K).subgroupOf (normalizer (K : Set G)) : Subgroup _) : Set _) := by
    rw [SetLike.mem_coe, ← h1]
    exact hx
  have : (K.subgroupOf (normalizer (K : Set G))).Normal := normal_in_normalizer
  rw [normal_mul] at h2
  obtain ⟨k, hk, c, hc, hkc⟩ := h2
  exact ⟨k, hk, c, hc, congrArg Subtype.val hkc⟩

theorem le_pPrimeCore_of_normal {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) : N ≤ pPrimeCore 2 X :=
  le_sSup ⟨inferInstance, hN⟩

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] noncomputable def imJB : Subgroup (OddBar h.K) :=
  ((GSLit.fixedLayer h.J h.B).subgroupOf h.K).map (QuotientGroup.mk' (pPrimeCore 2 h.K))

theorem imJB_commutator_eq (hKa : conjugate h.K h.a = h.K) : ⁅imJB h, imJB h⁆ = imJB h := by
  have hle := fixedLayer_le_K h hKa
  have h1 : ⁅(GSLit.fixedLayer h.J h.B).subgroupOf h.K,
      (GSLit.fixedLayer h.J h.B).subgroupOf h.K⁆ =
      (GSLit.fixedLayer h.J h.B).subgroupOf h.K := by
    apply map_injective h.K.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hle, fixedLayer_commutator_eq]
  rw [imJB, ← map_commutator, h1]

theorem a_mem_normalizer_K (hKa : conjugate h.K h.a = h.K) :
    h.a ∈ normalizer (h.K : Set H) :=
  mem_normalizer_of_conjugate_eq hKa

theorem oddBarConj_a_apply_of_mem_imJB (hKa : conjugate h.K h.a = h.K) {x : OddBar h.K}
    (hx : x ∈ imJB h) : oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ x = x := by
  obtain ⟨j, hj, rfl⟩ := hx
  have hja : (j : H) * h.a = h.a * j :=
    mem_centralizer_singleton_iff.mp (fixedLayer_le_centralizer_a h (mem_subgroupOf.mp hj))
  rw [QuotientGroup.mk'_apply, oddBarConj_apply_mk]
  congr 1
  apply Subtype.ext
  show h.a * (j : H) * h.a⁻¹ = j
  rw [← hja, mul_inv_cancel_right]

theorem oddBarConj_a_ne_one (hKa : conjugate h.K h.a = h.K) :
    oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ ≠ 1 := by
  intro h1
  have haK : h.a ∈ coreActionKernel h.K := mem_coreActionKernel_of_oddBarConj_eq_one h1
  have hle : ⁅h.K, zpowers h.a⁆ ≤ (pPrimeCore 2 h.K).map h.K.subtype := by
    rw [commutator_le]
    intro k hk g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    exact commutatorElement_mem_oddCoreIn hk (zpow_mem haK n)
  have hcomm := h.commutator_eq
  have hV : layerIn (normalizer (h.B : Set H)) = h.K := h.V_eq_K hKa
  rw [hV] at hcomm
  rw [hcomm] at hle
  have htop : pPrimeCore 2 h.K = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨o, ho, hoe⟩ := mem_map.mp (hle k.2)
    rwa [show o = k from Subtype.ext hoe] at ho
  obtain ⟨-, hsimp, -⟩ := h.isQuasisimple_K
  have hsub : Subsingleton (OddBar h.K) := by
    rw [subsingleton_iff]
    intro x y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq, htop]
    exact mem_top _
  have : Nontrivial (OddBar h.K ⧸ center (OddBar h.K)) := IsSimpleGroup.toNontrivial
  obtain ⟨u, v, huv⟩ := exists_pair_ne (OddBar h.K ⧸ center (OddBar h.K))
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  exact huv (by rw [Subsingleton.elim u v])

theorem exists_oddBarConj_a_eq_conj (hKa : conjugate h.K h.a = h.K)
    (hin : h.a ∈ h.K ⊔ coreActionKernel h.K) :
    ∃ l : OddBar h.K, oddBarConj h.K ⟨h.a, a_mem_normalizer_K h hKa⟩ = MulAut.conj l := by
  obtain ⟨k, hk, c, hc, hkc⟩ := exists_mul_of_mem_sup_coreActionKernel' hin
  have hkN : k ∈ normalizer (h.K : Set H) := le_normalizer hk
  have hcN : c ∈ normalizer (h.K : Set H) := (mem_coreActionKernel.mp hc).1
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, ?_⟩
  have e1 : (⟨h.a, a_mem_normalizer_K h hKa⟩ : ↥(normalizer (h.K : Set H))) =
      ⟨k, hkN⟩ * ⟨c, hcN⟩ := Subtype.ext hkc.symm
  rw [e1, map_mul, oddBarConj_eq_one_of_mem_coreActionKernel' (g := ⟨c, hcN⟩) hc, mul_one,
    oddBarConj_mk_eq_conj h.K hk]

end CFSG.ComponentClassification.CatFactsL4U4
