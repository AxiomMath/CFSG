module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Spec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Act
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44FrameG

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {L E : Subgroup G} {t : G}

theorem ker_actN_eq (hCE : centralizer (E : Set G) = E) :
    (actN E).ker = E.subgroupOf (normalizer (E : Set G)) := by
  ext n
  rw [mem_ker_actN_iff_mem_centralizer, hCE, mem_subgroupOf]

theorem card_image_mul (hCE : centralizer (E : Set G) = E) {S : Subgroup G}
    (hS : S ≤ normalizer (E : Set G)) (hES : E ≤ S) :
    Nat.card ↥((S.subgroupOf (normalizer (E : Set G))).map (actN E)) * Nat.card E =
      Nat.card S := by
  have hker : (actN E).ker ≤ S.subgroupOf (normalizer (E : Set G)) := by
    rw [ker_actN_eq hCE]
    intro n hn
    exact hES hn
  have h1 := card_map_mul_card_ker (actN E) _ hker
  have h2 : Nat.card (actN E).ker = Nat.card E := by
    rw [ker_actN_eq hCE]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_normalizer).toEquiv
  have h3 : Nat.card ↥(S.subgroupOf (normalizer (E : Set G))) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  rw [h2, h3] at h1
  exact h1

@[expose, instance_reducible] def commE (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : CommGroup ↥E :=
  { (inferInstance : Group ↥E) with mul_comm := fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2) }

@[expose] def XE (E : Subgroup G) : Subgroup (MulAut ↥E) := (actN E).range

@[expose] def MXE (E L : Subgroup G) : Subgroup (MulAut ↥E) :=
  ((normalizer (E : Set G) ⊓ L).subgroupOf (normalizer (E : Set G))).map (actN E)

theorem MXE_le_XE : MXE E L ≤ XE E := Subgroup.map_le_range _ _

theorem mem_orbit_MXE_iff (x v : ↥E) :
    v ∈ orbit (MXE E L) x ↔
      ∃ n ∈ normalizer (E : Set G) ⊓ L, (v : G) = n * x * n⁻¹ := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, hmv⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
    refine ⟨n, hn, ?_⟩
    rw [← hmv]
    rfl
  · rintro ⟨n, hn, hv⟩
    have hnN : n ∈ normalizer (E : Set G) := hn.1
    refine ⟨⟨actN E ⟨n, hnN⟩, Subgroup.mem_map.2 ⟨⟨n, hnN⟩, hn, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rw [hv]
    rfl

theorem mem_MXE_iff {m : MulAut ↥E} :
    m ∈ MXE E L ↔ ∃ n : ↥(normalizer (E : Set G)), (n : G) ∈ L ∧ actN E n = m := by
  constructor
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hm
    exact ⟨n, hn.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact Subgroup.mem_map.2 ⟨n, ⟨n.2, hn⟩, rfl⟩

theorem frame_subset {O : Fin 5 → Set G} (F : FrameModelG G L E t O) (i : Fin 5) :
    O i ⊆ E := by
  obtain ⟨x, hxE, hO⟩ := F.isOrbit i
  rintro y hy
  rw [hO] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact (mem_normalizer_iff.1 hn.1 x).1 hxE

theorem orbitData_of_frame (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hLt : L ≤ centralizer ({t} : Set G)) {O : Fin 5 → Set G} (F : FrameModelG G L E t O) :
    @OrbitData ↥E (commE hcomm) (MXE E L) ⟨t, F.t_mem⟩ (fun i => {v : ↥E | (v : G) ∈ O i}) := by
  let _ := commE hcomm
  have hOE := frame_subset F
  refine
  { ne_one := fun h => F.t_ne_one (congrArg Subtype.val h)
    isOrbit := fun i => ?_
    ncard := fun i => ?_
    disjoint := fun i j hij => Set.disjoint_left.2 fun v hv1 hv2 =>
      Set.disjoint_left.1 (F.disjoint i j hij) hv1 hv2
    not_mem_one := fun i h => F.not_mem_one i h
    not_mem_t := fun i h => F.not_mem_t i h
    cover := fun v hv => ?_
    fix := fun m hm => ?_
    swap := ?_
    prod := fun u hu u' hu' hne => F.prod u hu u' hu' (fun h => hne (Subtype.ext h))
    gen := ?_ }
  · obtain ⟨x, hxE, hO⟩ := F.isOrbit i
    refine ⟨⟨x, hxE⟩, ?_⟩
    ext v
    rw [mem_orbit_MXE_iff]
    simp only [Set.mem_ofPred_eq]
    rw [hO]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, h.symm⟩
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, h.symm⟩
  · have h := Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
      (s := O i) (fun y hy => ⟨⟨y, hOE i hy⟩, rfl⟩)
    exact h.trans (F.ncard i)
  · have h1 : v ≠ 1 := hv
    rcases F.cover v.1 v.2 (fun h => h1 (Subtype.ext h)) with h | ⟨i, hi⟩
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr ⟨i, hi⟩
  · obtain ⟨n, hn, rfl⟩ := mem_MXE_iff.1 hm
    apply Subtype.ext
    show (n : G) * t * (n : G)⁻¹ = t
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.1 (hLt hn)
  · ext v
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    rw [F.swap]
    constructor
    · rintro ⟨w, hw, hwv⟩
      refine ⟨⟨w, hOE 0 hw⟩, hw, Subtype.ext ?_⟩
      exact hwv
    · rintro ⟨u, hu, hv⟩
      exact ⟨u, hu, congrArg Subtype.val hv⟩
  · apply Subgroup.map_injective E.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have : E.subtype '' insert (⟨t, F.t_mem⟩ : ↥E) {v : ↥E | (v : G) ∈ O 0} = insert t (O 0) := by
      rw [Set.image_insert_eq]
      congr 1
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact hv
      · intro hy
        exact ⟨⟨y, hOE 0 hy⟩, hy, rfl⟩
    rw [this]
    exact F.gen

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
