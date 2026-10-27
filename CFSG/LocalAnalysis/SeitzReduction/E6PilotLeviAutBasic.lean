module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup

section Conj

variable {G : Type*} [Group G]

theorem map_conj_map_conj_eq_conj_mul (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_map_conj_eq_map_conj {G' : Type*} [Group G'] (f : G →* G') (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map f =
      (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem centralizer_map_conj_eq_map_centralizer (H : Subgroup G) (g : G) :
    centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · intro x hx
    refine ⟨g⁻¹ * x * g, mem_centralizer_iff.2 fun h hh => ?_, ?_⟩
    · have := mem_centralizer_iff.1 hx (g * h * g⁻¹) ⟨h, hh, rfl⟩
      calc h * (g⁻¹ * x * g) = g⁻¹ * ((g * h * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * h * g⁻¹)) * g := by rw [this]
        _ = g⁻¹ * x * g * h := by group
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨h, hh, rfl⟩
    have := mem_centralizer_iff.1 hy h hh
    change g * h * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * h * g⁻¹)
    calc g * h * g⁻¹ * (g * y * g⁻¹) = g * (h * y) * g⁻¹ := by group
      _ = g * (y * h) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * (g * h * g⁻¹) := by group

theorem subgroupOf_map_conj_eq_map_conj_subgroupOf {G : Type*} [Group G] {C H : Subgroup G}
    (hHC : H ≤ C) (n : C) :
    (H.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf C =
      (H.subgroupOf C).map (MulAut.conj n).toMonoidHom := by
  ext x
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨h, hh, hx⟩
    refine ⟨⟨h, hHC hh⟩, mem_subgroupOf.2 hh, Subtype.ext ?_⟩
    rw [← hx]
    rfl
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, mem_subgroupOf.1 hh, rfl⟩

theorem nonempty_centralizer_map_conj_mulEquiv (H : Subgroup G) (g : G) :
    Nonempty (centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≃*
      centralizer (H : Set G)) :=
  ⟨(MulEquiv.subgroupCongr (centralizer_map_conj_eq_map_centralizer H g)).trans
    ((centralizer (H : Set G)).equivMapOfInjective _ (MulAut.conj g).injective).symm⟩

end Conj

section AutConj

variable {P : Type*} [Group P]

@[expose] def IsAutConj (H : Subgroup P) : Prop :=
  ∀ α : MulAut P, ∃ p : P, H.map α.toMonoidHom = H.map (MulAut.conj p).toMonoidHom

theorem IsAutConj.map_conj {H : Subgroup P} (h : IsAutConj H) (g : P) :
    IsAutConj (H.map (MulAut.conj g).toMonoidHom) := by
  intro α
  obtain ⟨p, hp⟩ := h α
  refine ⟨α g * p * g⁻¹, ?_⟩
  rw [map_map_conj_eq_map_conj, MulEquiv.coe_toMonoidHom, ← MulEquiv.coe_toMonoidHom, hp,
    map_conj_map_conj_eq_conj_mul, map_conj_map_conj_eq_conj_mul]
  rw [inv_mul_cancel_right]

end AutConj

section AutConjIn

variable {C : Type*} [Group C]

@[expose] def IsAutConjIn (M J : Subgroup C) : Prop :=
  ∀ ι : M ≃* M, ∃ m ∈ M,
    ((J.subgroupOf M).map ι.toMonoidHom).map M.subtype = J.map (MulAut.conj m).toMonoidHom

theorem IsAutConj.isAutConjIn_map {P : Type*} [Group P] {H : Subgroup P} (h : IsAutConj H)
    {M : Subgroup C} (E : P ≃* M) :
    IsAutConjIn M ((H.map E.toMonoidHom).map M.subtype) := by
  intro ι
  obtain ⟨p, hp⟩ := h ((E.trans ι).trans E.symm)
  refine ⟨(E p : C), (E p).2, ?_⟩
  have hsub : ((H.map E.toMonoidHom).map M.subtype).subgroupOf M = H.map E.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have hι : (H.map E.toMonoidHom).map ι.toMonoidHom =
      (H.map ((E.trans ι).trans E.symm).toMonoidHom).map E.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  rw [hsub, hι, hp, map_map_conj_eq_map_conj, map_map_conj_eq_map_conj]
  rfl

theorem IsAutConjIn.map_conj {M J : Subgroup C} (h : IsAutConjIn M J) (hJM : J ≤ M) {m₀ : C}
    (hm₀ : m₀ ∈ M) : IsAutConjIn M (J.map (MulAut.conj m₀).toMonoidHom) := by
  intro ι
  obtain ⟨m, hm, hmJ⟩ := h ι
  refine ⟨(ι ⟨m₀, hm₀⟩ : C) * m * m₀⁻¹,
    mul_mem (mul_mem (ι ⟨m₀, hm₀⟩).2 hm) (inv_mem hm₀), ?_⟩
  have e := subgroupOf_map_conj_eq_map_conj_subgroupOf hJM (⟨m₀, hm₀⟩ : M)
  rw [show ((⟨m₀, hm₀⟩ : M) : C) = m₀ from rfl] at e
  rw [e, map_map_conj_eq_map_conj, map_map_conj_eq_map_conj, hmJ, map_conj_map_conj_eq_conj_mul,
    map_conj_map_conj_eq_conj_mul]
  congr 2
  rw [inv_mul_cancel_right]
  rfl

theorem nonempty_centralizer_map_mulEquiv_of_isAutConjIn {M J : Subgroup C}
    (h : IsAutConjIn M J) (ι : M ≃* M) :
    Nonempty (centralizer ((((J.subgroupOf M).map ι.toMonoidHom).map M.subtype : Subgroup C) :
      Set C) ≃* centralizer (J : Set C)) := by
  obtain ⟨m, -, hm⟩ := h ι
  rw [hm]
  exact nonempty_centralizer_map_conj_mulEquiv J m

end AutConjIn

section Factor

variable {G : Type*} [Group G]

theorem map_eq_self_of_sup_eq_top [Finite G] {J S : Subgroup G} (hJS : J ⊔ S = ⊤)
    (hSJ : S ≤ centralizer (J : Set G)) (hS : IsSimpleGroup S) (hZ : center S = ⊥)
    (hcard : Nat.card J < Nat.card S) (α : MulAut G) :
    J.map α.toMonoidHom = J := by
  have hJS' : J ≤ centralizer (S : Set G) := le_centralizer_iff.1 hSJ
  have hJn : J.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hJS]
    exact sup_le le_normalizer (hSJ.trans (centralizer_le_normalizer _))
  have hSn : S.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hJS]
    exact sup_le (hJS'.trans (centralizer_le_normalizer _)) le_normalizer
  set N := J.map α.toMonoidHom with hNdef
  have hNn : N.Normal := hJn.map α.toMonoidHom α.surjective
  have hNcard : Nat.card N = Nat.card J := card_map_of_injective α.injective
  have hNS : Disjoint N S := by
    have hNSn : (N ⊓ S).Normal := by
      have := hNn
      have := hSn
      infer_instance
    have hn : ((N ⊓ S).subgroupOf S).Normal := hNSn.subgroupOf S
    rcases hS.eq_bot_or_eq_top_of_normal ((N ⊓ S).subgroupOf S) with h | h
    · rw [subgroupOf_eq_bot] at h
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have hx' : x ∈ (N ⊓ S) ⊓ S := mem_inf.2 ⟨hx, (mem_inf.1 hx).2⟩
      rwa [disjoint_iff.1 h] at hx'
    · exfalso
      rw [subgroupOf_eq_top] at h
      have hle : S ≤ N := h.trans inf_le_left
      have := Subgroup.card_le_of_le hle
      omega
  have hCS : centralizer (S : Set G) ≤ J := by
    intro g hg
    have hgtop : g ∈ J ⊔ S := hJS ▸ mem_top g
    obtain ⟨j, hj, s, hs, rfl⟩ := mem_sup_of_normal_left.1 hgtop
    have hsc : s ∈ centralizer (S : Set G) := by
      have := mul_mem (inv_mem (hJS' hj)) hg
      rwa [inv_mul_cancel_left] at this
    have hsZ : (⟨s, hs⟩ : S) ∈ center S := by
      rw [mem_center_iff]
      intro t
      exact Subtype.ext (mem_centralizer_iff.1 hsc t t.2)
    rw [hZ, mem_bot] at hsZ
    have hs1 : s = 1 := congrArg Subtype.val hsZ
    rw [hs1, mul_one]
    exact hj
  have hNC : N ≤ centralizer (S : Set G) := fun n hn => mem_centralizer_iff.2 fun s hs =>
    (commute_of_normal_of_disjoint N S hNn hSn hNS n s hn hs).eq.symm
  exact eq_of_le_of_card_ge (hNC.trans hCS) hNcard.ge

@[expose] def IsSimpleCentralizingFactor {C : Type*} [Group C] (M J : Subgroup C) : Prop :=
  ∃ S : Subgroup C, J ⊔ S = M ∧ S ≤ centralizer (J : Set C) ∧ IsSimpleGroup S ∧
    center S = ⊥ ∧ Nat.card J < Nat.card S

end Factor

section FactorIn

variable {C : Type*} [Group C] [Finite C]

theorem map_subgroupOf_eq_self_of_isSimpleCentralizingFactor {M J : Subgroup C}
    (h : IsSimpleCentralizingFactor M J) (ι : M ≃* M) :
    (J.subgroupOf M).map ι.toMonoidHom = J.subgroupOf M := by
  obtain ⟨S, hJS, hSJ, hS, hZ, hcard⟩ := h
  have hJM : J ≤ M := hJS ▸ le_sup_left
  have hSM : S ≤ M := hJS ▸ le_sup_right
  let eS : S.subgroupOf M ≃* S := subgroupOfEquivOfLe hSM
  have hS' : IsSimpleGroup (S.subgroupOf M) := eS.isSimpleGroup
  have hZ' : center (S.subgroupOf M) = ⊥ := by
    rw [← map_center_eq eS.symm, hZ, Subgroup.map_bot]
  have hcard' : Nat.card (J.subgroupOf M) < Nat.card (S.subgroupOf M) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv, Nat.card_congr eS.toEquiv]
  refine map_eq_self_of_sup_eq_top ?_ ?_ hS' hZ' hcard' ι
  · rw [← subgroupOf_sup hJM hSM, hJS, subgroupOf_self]
  · intro s hs
    rw [mem_centralizer_iff]
    intro j hj
    exact Subtype.ext (mem_centralizer_iff.1 (hSJ (mem_subgroupOf.1 hs)) j (mem_subgroupOf.1 hj))

theorem isAutConjIn_of_isSimpleCentralizingFactor {M J : Subgroup C}
    (h : IsSimpleCentralizingFactor M J) : IsAutConjIn M J := by
  intro ι
  have hJM : J ≤ M := by
    obtain ⟨S, hJS, -⟩ := h
    exact hJS ▸ le_sup_left
  refine ⟨1, one_mem M, ?_⟩
  rw [map_subgroupOf_eq_self_of_isSimpleCentralizingFactor h ι, subgroupOf_map_subtype,
    inf_of_le_left hJM]
  ext x
  simp

theorem not_isSimpleGroup_of_isSimpleCentralizingFactor {M J : Subgroup C}
    (h : IsSimpleCentralizingFactor M J) (hJ : J ≠ ⊥) : ¬ IsSimpleGroup M := by
  intro hM
  obtain ⟨S, hJS, hSJ, -, -, hcard⟩ := h
  have hJM : J ≤ M := hJS ▸ le_sup_left
  have hSM : S ≤ M := hJS ▸ le_sup_right
  have hJS' : J ≤ centralizer (S : Set C) := le_centralizer_iff.1 hSJ
  have hn : (J.subgroupOf M).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJM, ← hJS]
    exact sup_le le_normalizer (hSJ.trans (centralizer_le_normalizer _))
  rcases hM.eq_bot_or_eq_top_of_normal (J.subgroupOf M) with h1 | h1
  · rw [subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hJM] at h1
    exact hJ h1
  · rw [subgroupOf_eq_top] at h1
    have h2 := Subgroup.card_le_of_le (hSM.trans h1)
    omega

end FactorIn

end CFSG.SeitzReduction.E6Pilot
