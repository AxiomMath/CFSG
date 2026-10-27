module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.TransvectionIrreducible
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM blockV)
open CFSG.Open (pCoreOf)
open CFSG.RankThreeCoreUniqueness.Helpers (pCoreOf_isPGroup localGroup_le_normalizer_pCoreOf
  normal_pGroup_le_pCoreOf)
open CFSG.HardMathSupport.Cooperstein.Coordinator (twoCore_sup_le pCoreOf_le_centralizer_blockV
  barM_inf_le_center_of_core_le exists_pow_mem_sup)
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub ker_barMHomSub subgroupOf_barM_eq_map)
open CFSG.HardMathSupport.Cooperstein.StructureLie (isF2Transvection_mul_self)
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection)
open Subgroup

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

structure PLRep (M S L : Subgroup G) (s : G)
    (ρ : ↥(L ⊔ S) →* LinearMap.GeneralLinearGroup (ZMod 2) W) : Prop where
  hA : Asc81bHyp M S
  hL : IsWeakSBlock M S L
  hSL : S ≤ normalizer (L : Set G)
  hZ : center ↥(barM M L) = ⊥
  hC : ∀ c : ↥(L ⊔ S), (c : G) ∈ centralizer (blockV S L : Set G) → ρ c = 1
  hL1 : ¬ L.subgroupOf (L ⊔ S) ≤ ρ.ker
  hsS : s ∈ S
  hgen : S ≤ zpowers s ⊔ (L ⊔ S) ⊓ centralizer (blockV S L : Set G)
  htr : IsF2Transvection (ρ ⟨s, mem_sup_right hsS⟩)

variable {s : G} {ρ : ↥(L ⊔ S) →* LinearMap.GeneralLinearGroup (ZMod 2) W}

namespace PLRep

theorem rho_eq_one_of_mem_pCoreOf (h : PLRep M S L s ρ) {l : G} (hl : l ∈ L)
    (hp : l ∈ pCoreOf 2 M) : ρ ⟨l, mem_sup_left hl⟩ = 1 :=
  h.hC _ (pCoreOf_le_centralizer_blockV h.hA h.hL
    (h.hL.toIsTwoPrimeComponent.inf_twoCore.le ⟨hl, hp⟩))

theorem mem_pCoreOf_of_rho_eq_one (h : PLRep M S L s ρ) {l : G} (hl : l ∈ L)
    (h1 : ρ ⟨l, mem_sup_left hl⟩ = 1) : l ∈ pCoreOf 2 M := by
  set K : Subgroup G := ρ.ker.map (L ⊔ S).subtype with hK
  have hKmem : ∀ (g : G) (hg : g ∈ L ⊔ S), g ∈ K ↔ ρ ⟨g, hg⟩ = 1 := by
    intro g hg
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h'
      exact ⟨⟨g, hg⟩, h', rfl⟩
  have hLC : L ≤ normalizer (K : Set G) := by
    refine CFSG.HardMathSupport.Cooperstein.StructureLie.TransvIrr.le_normalizer_of_conj_mem
      fun g hg k hk => ?_
    obtain ⟨y, hy, rfl⟩ := hk
    have hy' : ρ y = 1 := hy
    refine ⟨⟨g, mem_sup_left hg⟩ * y * ⟨g, mem_sup_left hg⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, hy', mul_one, map_inv,
      mul_inv_cancel]
  have hnle : ¬ L ≤ K := by
    intro hle
    apply h.hL1
    intro x hx
    exact (hKmem _ (mem_sup_left (mem_subgroupOf.mp hx))).mp (hle (mem_subgroupOf.mp hx))
  have hcore : L ⊓ pCoreOf 2 M ≤ K := fun l hl =>
    (hKmem _ (mem_sup_left hl.1)).mpr (h.rho_eq_one_of_mem_pCoreOf hl.1 hl.2)
  have hcen := barM_inf_le_center_of_core_le h.hL.toIsTwoPrimeComponent hLC hcore hnle
  have hmem : barMHomSub h.hL.le ⟨l, hl⟩ ∈ (barM M (L ⊓ K)).subgroupOf (barM M L) := by
    rw [subgroupOf_barM_eq_map h.hL.le inf_le_left]
    exact ⟨⟨l, hl⟩, mem_subgroupOf.mpr ⟨hl, (hKmem l _).mpr h1⟩, rfl⟩
  obtain ⟨z, hz, hzy⟩ := hcen (mem_subgroupOf.mp hmem)
  rw [SetLike.mem_coe, h.hZ, mem_bot] at hz
  subst hz
  have h2 : barMHomSub h.hL.le ⟨l, hl⟩ = 1 := Subtype.ext (by rw [← hzy]; rfl)
  have h3 : (⟨l, hl⟩ : ↥L) ∈ (barMHomSub h.hL.le).ker := h2
  rw [ker_barMHomSub] at h3
  exact mem_subgroupOf.mp h3

theorem rho_eq_one_iff_mem_pCoreOf (h : PLRep M S L s ρ) {l : G} (hl : l ∈ L) :
    ρ ⟨l, mem_sup_left hl⟩ = 1 ↔ l ∈ pCoreOf 2 M :=
  ⟨h.mem_pCoreOf_of_rho_eq_one hl, h.rho_eq_one_of_mem_pCoreOf hl⟩

theorem mem_pCoreOf_sup_of_rho_eq_one (h : PLRep M S L s ρ) (y : ↥(L ⊔ S)) (hy : ρ y = 1) :
    (y : G) ∈ pCoreOf 2 (L ⊔ S) := by
  set K : Subgroup G := ρ.ker.map (L ⊔ S).subtype with hK
  have hKle : K ≤ L ⊔ S := map_subtype_le _
  have hKnormal : (K.subgroupOf (L ⊔ S)).Normal := by
    rw [hK, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (L ⊔ S).subtype_injective]
    exact MonoidHom.normal_ker ρ
  have hKp : IsPGroup 2 K := by
    rintro ⟨k, y', hy', rfl⟩
    have hy1 : ρ y' = 1 := hy'
    obtain ⟨e, he⟩ := exists_pow_mem_sup h.hA.twoRadical.isPGroup h.hSL y'.2
    have h1 : ρ ⟨(y' : G) ^ 2 ^ e, mem_sup_left he⟩ = 1 := by
      have : (⟨(y' : G) ^ 2 ^ e, mem_sup_left he⟩ : ↥(L ⊔ S)) = y' ^ 2 ^ e := rfl
      rw [this, map_pow, hy1, one_pow]
    have h2 := h.mem_pCoreOf_of_rho_eq_one he h1
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 M ⟨_, h2⟩
    refine ⟨e + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  exact normal_pGroup_le_pCoreOf 2 K (L ⊔ S) hKle hKnormal hKp ⟨y, hy, rfl⟩

omit [Finite G] in
theorem rho_mem_zpowers_of_mem (h : PLRep M S L s ρ) {z : G} (hz : z ∈ S) :
    ρ ⟨z, mem_sup_right hz⟩ ∈ zpowers (ρ ⟨s, mem_sup_right h.hsS⟩) := by
  set t := ρ ⟨s, mem_sup_right h.hsS⟩ with ht
  let T : Subgroup G := ((zpowers t).comap ρ).map (L ⊔ S).subtype
  have h1 : zpowers s ≤ T := by
    rw [zpowers_le]
    exact ⟨⟨s, mem_sup_right h.hsS⟩, mem_zpowers t, rfl⟩
  have h2 : (L ⊔ S) ⊓ centralizer (blockV S L : Set G) ≤ T := by
    rintro c ⟨hcM, hcV⟩
    refine ⟨⟨c, hcM⟩, ?_, rfl⟩
    show ρ ⟨c, hcM⟩ ∈ zpowers t
    rw [h.hC _ hcV]
    exact one_mem _
  obtain ⟨y, hy, hyz⟩ := (sup_le h1 h2) (h.hgen hz)
  have : (⟨z, mem_sup_right hz⟩ : ↥(L ⊔ S)) = y := Subtype.ext hyz.symm
  rw [this]
  exact hy

end PLRep

theorem eq_one_or_eq_of_mem_zpowers {K : Type*} [Group K] {t g : K} (ht : t * t = 1)
    (hg : g ∈ zpowers t) : g = 1 ∨ g = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_two, ht, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, ht, one_zpow, one_mul]

namespace PLRep

omit [Finite G] in
theorem rho_comm_of_mem_normalizer (h : PLRep M S L s ρ) {x : G} (hxL : x ∈ L)
    (hxN : x ∈ normalizer (S : Set G)) :
    ρ ⟨x, mem_sup_left hxL⟩ * ρ ⟨s, mem_sup_right h.hsS⟩ =
      ρ ⟨s, mem_sup_right h.hsS⟩ * ρ ⟨x, mem_sup_left hxL⟩ := by
  set t := ρ ⟨s, mem_sup_right h.hsS⟩ with ht
  set a := ρ ⟨x, mem_sup_left hxL⟩ with ha
  have hz : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.mp hxN s).mp h.hsS
  have hmem := h.rho_mem_zpowers_of_mem hz
  have e : ρ ⟨x * s * x⁻¹, mem_sup_right hz⟩ = a * t * a⁻¹ := by
    have : (⟨x * s * x⁻¹, mem_sup_right hz⟩ : ↥(L ⊔ S)) =
        ⟨x, mem_sup_left hxL⟩ * ⟨s, mem_sup_right h.hsS⟩ * ⟨x, mem_sup_left hxL⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  rw [e] at hmem
  rcases eq_one_or_eq_of_mem_zpowers (isF2Transvection_mul_self h.htr) hmem with h1 | h1
  · exfalso
    apply h.htr.1
    have h' := mul_inv_eq_one.mp h1
    exact mul_left_cancel (a := a) (h'.trans (mul_one _).symm)
  · exact mul_inv_eq_iff_eq_mul.mp h1

theorem conj_mem_of_rho_comm (h : PLRep M S L s ρ) {y : ↥(L ⊔ S)}
    (hy : ρ y * ρ ⟨s, mem_sup_right h.hsS⟩ = ρ ⟨s, mem_sup_right h.hsS⟩ * ρ y) {z : G}
    (hz : z ∈ S) : (y : G) * z * (y : G)⁻¹ ∈ S := by
  have hQS := twoCore_sup_le h.hA h.hL h.hSL
  have hQC : (L ⊔ S) ⊓ centralizer (blockV S L : Set G) ≤ pCoreOf 2 (L ⊔ S) := fun c hc =>
    h.mem_pCoreOf_sup_of_rho_eq_one ⟨c, hc.1⟩ (h.hC _ hc.2)
  have hSle : S ≤ zpowers s ⊔ pCoreOf 2 (L ⊔ S) := h.hgen.trans (sup_le_sup_left hQC _)
  let T : Subgroup G := S.comap (MulAut.conj (y : G)).toMonoidHom
  have h1 : zpowers s ≤ T := by
    rw [zpowers_le]
    show (y : G) * s * (y : G)⁻¹ ∈ S
    have hc : ρ (y * ⟨s, mem_sup_right h.hsS⟩ * y⁻¹ * ⟨s, mem_sup_right h.hsS⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_iff_eq_mul.mpr hy,
        mul_inv_cancel]
    have hc' := hQS (h.mem_pCoreOf_sup_of_rho_eq_one _ hc)
    have e : (y : G) * s * (y : G)⁻¹ = ((y : G) * s * (y : G)⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact S.mul_mem hc' h.hsS
  have h2 : pCoreOf 2 (L ⊔ S) ≤ T := fun q hq => by
    show (y : G) * q * (y : G)⁻¹ ∈ S
    exact hQS ((mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 (L ⊔ S) y.2) q).mp hq)
  exact (sup_le h1 h2) (hSle hz)

theorem rho_comm_iff_mem_normalizer (h : PLRep M S L s ρ) {y : G} (hyL : y ∈ L) :
    ρ ⟨y, mem_sup_left hyL⟩ * ρ ⟨s, mem_sup_right h.hsS⟩ =
      ρ ⟨s, mem_sup_right h.hsS⟩ * ρ ⟨y, mem_sup_left hyL⟩ ↔ y ∈ normalizer (S : Set G) := by
  refine ⟨fun hy => ?_, h.rho_comm_of_mem_normalizer hyL⟩
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h.conj_mem_of_rho_comm hy, fun hx => ?_⟩
  have hy' : ρ (⟨y, mem_sup_left hyL⟩ : ↥(L ⊔ S))⁻¹ * ρ ⟨s, mem_sup_right h.hsS⟩ =
      ρ ⟨s, mem_sup_right h.hsS⟩ * ρ (⟨y, mem_sup_left hyL⟩ : ↥(L ⊔ S))⁻¹ := by
    rw [map_inv]
    exact (Commute.inv_left hy)
  have := h.conj_mem_of_rho_comm hy' hx
  have e : ((⟨y, mem_sup_left hyL⟩ : ↥(L ⊔ S))⁻¹ : ↥(L ⊔ S)).1 * (y * x * y⁻¹) *
      ((⟨y, mem_sup_left hyL⟩ : ↥(L ⊔ S))⁻¹ : ↥(L ⊔ S)).1⁻¹ = x := by
    show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x
    group
  rwa [e] at this

end PLRep

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
