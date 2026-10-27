module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3CenterFree

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

theorem card_iSup_eq_prod_of_pairwise_commute {Q : Type*} [Group Q] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (K : ι → Subgroup Q)
    (hcomm : Pairwise fun i j : ι => ∀ x y : Q, x ∈ K i → y ∈ K j → Commute x y)
    (hZ : ∀ i, center (K i) = ⊥) : Nat.card ↥(⨆ i, K i) = ∏ i, Nat.card ↥(K i) := by
  have hind : iSupIndep K := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    have hcen : ⨆ (j : ι) (_ : j ≠ i), K j ≤ centralizer (K i : Set Q) := by
      refine iSup₂_le fun j hj y hy => ?_
      rw [mem_centralizer_iff]
      intro z hz
      exact (hcomm hj y z hy hz).eq.symm
    have hxZ : (⟨x, hx⟩ : K i) ∈ center (K i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp (hcen hx') g g.2)
    rw [hZ i, Subgroup.mem_bot] at hxZ
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hxZ)
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), ← Nat.card_pi]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

section Product

variable {G : Type*} [Group G] [Finite G]

private theorem map_pPrimeCore_eq_inf_of_isSubnormal {A : Subgroup G} (hA : A.IsSubnormal) :
    (pPrimeCore 2 A).map A.subtype = A ⊓ pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCore_eq_piCore, pPrimeCore_eq_piCore]
  exact LocalCores.prime_set_core_subnormal_intersection _ hA

private theorem pPrimeCore_eq_subgroupOf_of_isSubnormal {A : Subgroup G} (hA : A.IsSubnormal) :
    pPrimeCore 2 A = (pPrimeCore 2 G).subgroupOf A := by
  have h := congrArg (Subgroup.comap A.subtype) (map_pPrimeCore_eq_inf_of_isSubnormal hA)
  rw [Subgroup.comap_map_eq_self_of_injective A.subtype_injective] at h
  rw [h]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem nonempty_quot_pPrimeCore_mulEquiv_map {A : Subgroup G} (hA : A.IsSubnormal) :
    Nonempty ((↥A ⧸ pPrimeCore 2 ↥A) ≃* ↥(A.map (QuotientGroup.mk' (pPrimeCore 2 G)))) := by
  let φ : ↥A →* G ⧸ pPrimeCore 2 G := (QuotientGroup.mk' (pPrimeCore 2 G)).comp A.subtype
  have hker : pPrimeCore 2 ↥A = φ.ker := by
    rw [pPrimeCore_eq_subgroupOf_of_isSubnormal hA]
    ext x
    simp [φ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hrange : φ.range = A.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem commute_of_mem_map_of_isPComponent {L L' : Subgroup G} (hL : IsPComponent 2 L)
    (hL' : IsPComponent 2 L') (hne : L ≠ L') {x y : G ⧸ pPrimeCore 2 G}
    (hx : x ∈ L.map (QuotientGroup.mk' (pPrimeCore 2 G)))
    (hy : y ∈ L'.map (QuotientGroup.mk' (pPrimeCore 2 G))) : Commute x y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hc := (ComponentClassification.CatalogueBPrimeJoin.mutual_normalization_core_commutation
    2 L L' hL hL' hne).2.2
  have hcore : ∀ a ∈ L, ∀ b ∈ L', ⁅a, b⁆ ∈ pPrimeCore 2 G := by
    intro a ha b hb
    have h1 := (hc (Subgroup.commutator_mem_commutator ha hb)).1
    rw [map_pPrimeCore_eq_inf_of_isSubnormal hL.choose_spec.2.1] at h1
    exact h1.2
  have h := inv_mem (hcore a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb))
  simp only [Commute, SemiconjBy]
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  convert h using 1
  simp only [commutatorElement_def]
  group

theorem card_quot_pPrimeCore_iSup_of_isPComponent {ι : Type*} (s : Finset ι)
    (L : ι → Subgroup G) (hL : ∀ i ∈ s, IsPComponent 2 (L i)) (hinj : Set.InjOn L s)
    (hZ : ∀ i ∈ s, center (↥(L i) ⧸ pPrimeCore 2 ↥(L i)) = ⊥) :
    Nat.card (↥(⨆ i ∈ s, L i) ⧸ pPrimeCore 2 ↥(⨆ i ∈ s, L i)) =
      ∏ i ∈ s, Nat.card (↥(L i) ⧸ pPrimeCore 2 ↥(L i)) := by
  classical
  have hsub : ∀ i ∈ s, (L i).IsSubnormal := fun i hi => (hL i hi).choose_spec.2.1
  have hJ : (⨆ i ∈ s, L i).IsSubnormal :=
    GroupTheory.isSubnormal_finset_iSup_of_pair
      (fun _ _ hA hB => GroupTheory.isSubnormal_sup hA hB) s L hsub
  obtain ⟨eJ⟩ := nonempty_quot_pPrimeCore_mulEquiv_map hJ
  rw [Nat.card_congr eJ.toEquiv]
  have hmap : (⨆ i ∈ s, L i).map (QuotientGroup.mk' (pPrimeCore 2 G)) =
      ⨆ i : s, (L i).map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
    simp only [Subgroup.map_iSup]
    exact iSup_subtype'
  have hcomm : Pairwise fun i j : s => ∀ x y : G ⧸ pPrimeCore 2 G,
      x ∈ (L i).map (QuotientGroup.mk' (pPrimeCore 2 G)) →
        y ∈ (L j).map (QuotientGroup.mk' (pPrimeCore 2 G)) → Commute x y :=
    fun i j hij _ _ hx hy => commute_of_mem_map_of_isPComponent (hL i i.2) (hL j j.2)
      (fun h => hij (Subtype.ext (hinj i.2 j.2 h))) hx hy
  have hZK : ∀ i : s, center ↥((L i).map (QuotientGroup.mk' (pPrimeCore 2 G))) = ⊥ := by
    intro i
    obtain ⟨e⟩ := nonempty_quot_pPrimeCore_mulEquiv_map (hsub i i.2)
    rw [← Subgroup.map_center_eq e, hZ i i.2, Subgroup.map_bot]
  rw [hmap, card_iSup_eq_prod_of_pairwise_commute _ hcomm hZK,
    ← Finset.prod_coe_sort s (fun i => Nat.card (↥(L i) ⧸ pPrimeCore 2 ↥(L i)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨e⟩ := nonempty_quot_pPrimeCore_mulEquiv_map (hsub i i.2)
  exact (Nat.card_congr e.toEquiv).symm

end Product

section Subgroup

variable {X : Type} [Group X] [Finite X]

private theorem card_quot_pPrimeCore_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ pPrimeCore 2 A) = Nat.card (B ⧸ pPrimeCore 2 B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).toEquiv

private theorem center_quot_pPrimeCore_eq_bot_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center (A ⧸ pPrimeCore 2 A) = ⊥) : center (B ⧸ pPrimeCore 2 B) = ⊥ := by
  rw [← Subgroup.map_center_eq (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)), h,
    Subgroup.map_bot]

private theorem iSup_subgroupOf_eq {H : Subgroup X} (S : Finset (Subgroup X))
    (hle : ∀ L ∈ S, L ≤ H) : ⨆ L ∈ S, L.subgroupOf H = (⨆ L ∈ S, L).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le (iSup₂_le hle)]
  simp only [Subgroup.map_iSup]
  exact iSup_congr fun L => iSup_congr fun hL => Subgroup.map_subgroupOf_eq_of_le (hle L hL)

theorem modOddCard_iSup_of_isPCompIn {H : Subgroup X} (S : Finset (Subgroup X))
    (hS : ∀ L ∈ S, IsPCompIn 2 H L) (hZ : ∀ L ∈ S, center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) :
    modOddCard (⨆ L ∈ S, L) = ∏ L ∈ S, modOddCard L := by
  have hle : ∀ L ∈ S, L ≤ H := fun L hL => (hS L hL).1
  have hinj : Set.InjOn (fun L : Subgroup X => L.subgroupOf H) S := by
    intro L hL M hM h
    have h' := congrArg (Subgroup.map H.subtype) h
    simp only [Subgroup.map_subgroupOf_eq_of_le (hle L hL),
      Subgroup.map_subgroupOf_eq_of_le (hle M hM)] at h'
    exact h'
  have h := card_quot_pPrimeCore_iSup_of_isPComponent S (fun L => L.subgroupOf H)
    (fun L hL => (hS L hL).2) hinj
    (fun L hL => center_quot_pPrimeCore_eq_bot_congr (subgroupOfEquivOfLe (hle L hL)).symm
      (hZ L hL))
  beta_reduce at h
  rw [iSup_subgroupOf_eq S hle] at h
  unfold modOddCard
  rw [← card_quot_pPrimeCore_congr (subgroupOfEquivOfLe (iSup₂_le hle)), h]
  exact Finset.prod_congr rfl fun L hL =>
    card_quot_pPrimeCore_congr (subgroupOfEquivOfLe (hle L hL))

theorem modOddCard_iSup_of_sec6MComp_of_centerFree (hcf : McLLyCenterFree) {n : ℕ}
    {H : Subgroup X} (S : Finset (Subgroup X)) (hS : ∀ L ∈ S, Sec6MComp X n H L) :
    modOddCard (⨆ L ∈ S, L) = ∏ L ∈ S, modOddCard L :=
  modOddCard_iSup_of_isPCompIn S (fun L hL => (hS L hL).1.1)
    (fun L hL => hcf (↥L ⧸ pPrimeCore 2 ↥L) (hS L hL).1.2.1)

theorem modOddCard_iSup_of_sec6MComp
    {n : ℕ} {H : Subgroup X} (S : Finset (Subgroup X))
    (hS : ∀ L ∈ S, Sec6MComp X n H L) :
    modOddCard (⨆ L ∈ S, L) = ∏ L ∈ S, modOddCard L :=
  modOddCard_iSup_of_sec6MComp_of_centerFree mcLLyCenterFree S hS

private theorem exists_finset_sec6MComp (n : ℕ) (H : Subgroup X) :
    ∃ S : Finset (Subgroup X), (∀ L, L ∈ S ↔ Sec6MComp X n H L) ∧ Sec6M X n H = ⨆ L ∈ S, L := by
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  refine ⟨(Set.toFinite {L | Sec6MComp X n H L}).toFinset, fun L => Set.Finite.mem_toFinset _,
    ?_⟩
  unfold Sec6M
  rw [sSup_eq_iSup]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem modOddCard_Sec6M_eq_prod_of_centerFree (hcf : McLLyCenterFree) {n : ℕ}
    (H : Subgroup X) :
    ∃ S : Finset (Subgroup X), (∀ L, L ∈ S ↔ Sec6MComp X n H L) ∧ Sec6M X n H = ⨆ L ∈ S, L ∧
      modOddCard (Sec6M X n H) = ∏ L ∈ S, modOddCard L := by
  obtain ⟨S, hS, hM⟩ := exists_finset_sec6MComp n H
  refine ⟨S, hS, hM, ?_⟩
  rw [hM]
  exact modOddCard_iSup_of_sec6MComp_of_centerFree hcf S fun L hL => (hS L).1 hL

theorem modOddCard_eq_of_sec6MComp {n : ℕ} {H L : Subgroup X} {Q : Type} [Group Q]
    (hQ : IsSec6MType n Q) (hL : Sec6MComp X n H L) : modOddCard L = Nat.card Q := by
  unfold modOddCard
  rcases hL.2 with ⟨h8, ⟨e⟩⟩ | ⟨h11, ⟨e⟩⟩ <;> rcases hQ with ⟨h8', ⟨f⟩⟩ | ⟨h11', ⟨f⟩⟩
  · exact Nat.card_congr (e.trans f.symm).toEquiv
  · omega
  · omega
  · exact Nat.card_congr (e.trans f.symm).toEquiv

theorem modOddCard_iSup_of_sec6MComp_eq_pow
    {n : ℕ} {H : Subgroup X} {Q : Type} [Group Q]
    (hQ : IsSec6MType n Q) (S : Finset (Subgroup X)) (hS : ∀ L ∈ S, Sec6MComp X n H L) :
    (∀ L ∈ S, modOddCard L = Nat.card Q) ∧ modOddCard (⨆ L ∈ S, L) = Nat.card Q ^ S.card := by
  have h : ∀ L ∈ S, modOddCard L = Nat.card Q := fun L hL => modOddCard_eq_of_sec6MComp hQ (hS L hL)
  refine ⟨h, ?_⟩
  rw [modOddCard_iSup_of_sec6MComp S hS, Finset.prod_congr rfl h, Finset.prod_const]

theorem modOddCard_Sec6M_eq_pow
    {n : ℕ} (H : Subgroup X) {Q : Type} [Group Q] (hQ : IsSec6MType n Q) :
    modOddCard (Sec6M X n H) = Nat.card Q ^ {L | Sec6MComp X n H L}.ncard := by
  obtain ⟨S, hS, hM⟩ := exists_finset_sec6MComp n H
  have hset : {L | Sec6MComp X n H L} = ↑S := by
    ext L
    simp [hS]
  rw [hM, (modOddCard_iSup_of_sec6MComp_eq_pow hQ S fun L hL => (hS L).1 hL).2, hset,
    Set.ncard_coe_finset]

private theorem one_lt_card_of_isSec6MType
    {n : ℕ} {Q : Type} [Group Q] (hQ : IsSec6MType n Q) :
    1 < Nat.card Q := by
  rcases hQ with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Sporadic.McL.card_McL]
    norm_num
  · rw [Nat.card_congr e.toEquiv, Sporadic.Ly.card_Ly']
    norm_num

theorem modOddCard_Sec6M_le_iff
    {n : ℕ} (hn : n = 8 ∨ n = 11) (H H' : Subgroup X) :
    modOddCard (Sec6M X n H) ≤ modOddCard (Sec6M X n H') ↔
      {L | Sec6MComp X n H L}.ncard ≤ {L | Sec6MComp X n H' L}.ncard := by
  obtain ⟨Q, _, hQ⟩ : ∃ (Q : Type) (_ : Group Q), IsSec6MType n Q := by
    rcases hn with h | h
    · exact ⟨Blueprint.NativeSporadic.McL, inferInstance, Or.inl ⟨h, ⟨MulEquiv.refl _⟩⟩⟩
    · exact ⟨Blueprint.NativeSporadic.Ly, inferInstance, Or.inr ⟨h, ⟨MulEquiv.refl _⟩⟩⟩
  rw [modOddCard_Sec6M_eq_pow H hQ, modOddCard_Sec6M_eq_pow H' hQ]
  exact Nat.pow_le_pow_iff_right (one_lt_card_of_isSec6MType hQ)

end Subgroup

end CFSG.OddStandard.Solomon75
