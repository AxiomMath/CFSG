module

public import CFSG.LocalAnalysis.GH72.Vocabulary
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outer_mul_comm_of_mulEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M)
    (h : ∀ a b : Outer M, a * b = b * a) (a b : Outer L) : a * b = b * a := by
  let E := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
  apply E.injective
  rw [map_mul, map_mul, h]

theorem outer_mul_comm_of_mulEquiv_psl2 {L : Type*} [Group L] {F : Type} [Field F] [Finite F]
    (e : L ≃* CFSG.GorensteinWalter.PSL2 F) (a b : Outer L) : a * b = b * a :=
  outer_mul_comm_of_mulEquiv e
    (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm F) a b

theorem outer_alternatingGroup_seven_mul_comm (a b : Outer (alternatingGroup (Fin 7))) :
    a * b = b * a := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨s, rfl⟩ := hbij.2 σ
  obtain ⟨t, rfl⟩ := hbij.2 τ
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hc : (s * t)⁻¹ * (t * s) ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv]
    rw [mul_comm (Equiv.Perm.sign s) (Equiv.Perm.sign t)]
    group
  refine ⟨⟨_, hc⟩, ?_⟩
  rw [← MulAut.conjNormal_val (h := ⟨_, hc⟩)]
  simp only [map_mul, map_inv]

theorem outer_mul_comm_of_mulEquiv_alternatingGroup_seven {L : Type*} [Group L]
    (e : L ≃* alternatingGroup (Fin 7)) (a b : Outer L) : a * b = b * a :=
  outer_mul_comm_of_mulEquiv e outer_alternatingGroup_seven_mul_comm a b

theorem isL2OrA7_of_mulEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M) {qmin : ℕ}
    (h : IsL2OrA7 M qmin) : IsL2OrA7 L qmin := by
  rcases h with ⟨⟨f⟩⟩ | ⟨p, k, hp, hp2, hq, ⟨f⟩⟩
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨p, k, hp, hp2, hq, ⟨e.trans f⟩⟩

theorem outer_mul_comm_of_isL2OrA7 {L : Type*} [Group L] {qmin : ℕ} (h : IsL2OrA7 L qmin)
    (a b : Outer L) : a * b = b * a := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, _, -, -, ⟨e⟩⟩
  · exact outer_mul_comm_of_mulEquiv_alternatingGroup_seven e a b
  · exact outer_mul_comm_of_mulEquiv_psl2 e a b

section Ambient

variable {X : Type*} [Group X]

theorem ker_outer_conjNormal (L : Subgroup X) [L.Normal] :
    ((QuotientGroup.mk' (inner L)).comp (MulAut.conjNormal : X →* MulAut L)).ker =
      L ⊔ centralizer (L : Set X) := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    obtain ⟨y, hy⟩ := hx
    have hd : x * (y : X)⁻¹ ∈ centralizer (L : Set X) := by
      rw [mem_centralizer_iff]
      intro l hl
      have hl' : (y : X)⁻¹ * l * y ∈ L := L.mul_mem (L.mul_mem (L.inv_mem y.2) hl) y.2
      have h1 : (MulAut.conj y ⟨_, hl'⟩ : X) = (MulAut.conjNormal x ⟨_, hl'⟩ : X) := by rw [hy]
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        MulAut.conjNormal_apply] at h1
      have h2 : l = x * (y : X)⁻¹ * l * (y : X) * x⁻¹ :=
        calc l = (y : X) * ((y : X)⁻¹ * l * y) * (y : X)⁻¹ := by group
          _ = x * ((y : X)⁻¹ * l * y) * x⁻¹ := h1
          _ = x * (y : X)⁻¹ * l * (y : X) * x⁻¹ := by group
      calc l * (x * (y : X)⁻¹) = x * (y : X)⁻¹ * l * (y : X) * x⁻¹ * (x * (y : X)⁻¹) := by
            rw [← h2]
        _ = x * (y : X)⁻¹ * l := by group
    have hxy : x = x * (y : X)⁻¹ * y := by group
    rw [hxy, sup_comm]
    exact mul_mem_sup hd y.2
  · rw [sup_le_iff]
    constructor
    · intro l hl
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      refine ⟨⟨l, hl⟩, ?_⟩
      ext m
      simp
    · intro c hc
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      refine ⟨1, ?_⟩
      ext m
      simp only [map_one, MulAut.one_apply, MulAut.conjNormal_apply]
      rw [mem_centralizer_iff] at hc
      rw [← hc m m.2]
      group

theorem commutator_le_sup_centralizer_of_outer_mul_comm (L : Subgroup X) [L.Normal]
    (h : ∀ a b : Outer L, a * b = b * a) : commutator X ≤ L ⊔ centralizer (L : Set X) := by
  rw [← ker_outer_conjNormal, commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact h _ _

theorem commutator_le_sup_centralizer_of_isL2OrA7 (L : Subgroup X) [L.Normal] {qmin : ℕ}
    (h : IsL2OrA7 L qmin) : commutator X ≤ L ⊔ centralizer (L : Set X) :=
  commutator_le_sup_centralizer_of_outer_mul_comm L (outer_mul_comm_of_isL2OrA7 h)

end Ambient

theorem commutator_le_sup_inf_centralizer_of_isL2OrA7 {G : Type*} [Group G] {H L : Subgroup G}
    (hLH : L ≤ H) (hH : H ≤ normalizer (L : Set G)) {qmin : ℕ} (h : IsL2OrA7 L qmin) :
    ⁅H, H⁆ ≤ L ⊔ (H ⊓ centralizer (L : Set G)) := by
  haveI : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hH
  have h' : IsL2OrA7 (L.subgroupOf H) qmin := isL2OrA7_of_mulEquiv (subgroupOfEquivOfLe hLH) h
  have hmap := Subgroup.map_mono (f := H.subtype)
    (commutator_le_sup_centralizer_of_isL2OrA7 (X := H) (L.subgroupOf H) h')
  have hl : (commutator H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rw [hl, Subgroup.map_sup, subgroupOf_map_subtype] at hmap
  refine hmap.trans (sup_le_sup inf_le_left ?_)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.2, ?_⟩
  change (x : G) ∈ centralizer (L : Set G)
  rw [mem_centralizer_iff]
  intro l hl
  have hm : (⟨l, hLH hl⟩ : H) ∈ L.subgroupOf H := by simpa [mem_subgroupOf] using hl
  have hx' : x ∈ centralizer ((L.subgroupOf H : Subgroup H) : Set H) := hx
  exact congrArg Subtype.val (mem_centralizer_iff.mp hx' _ hm)

theorem center_eq_bot_of_isL2OrA7 {L : Type*} [Group L] {qmin : ℕ} (h : IsL2OrA7 L qmin) :
    center L = ⊥ := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, k, _, -, -, ⟨e⟩⟩
  · exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simp))
  · exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)

theorem inf_centralizer_eq_bot_of_isL2OrA7 {X : Type*} [Group X] (L : Subgroup X) {qmin : ℕ}
    (h : IsL2OrA7 L qmin) : L ⊓ centralizer (L : Set X) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hz : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hxC l l.2)
  rw [center_eq_bot_of_isL2OrA7 h, mem_bot] at hz
  exact (mem_bot).2 (congrArg Subtype.val hz)

end CFSG.GH72
