module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURank

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)
open scoped commutatorElement

local instance e7ClassURankClassNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section General

variable {G : Type*} [Group G]

@[expose] def commMap (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (g : G)
    (hg : g ∈ normalizer (H : Set G)) : H →* G where
  toFun h := ⁅(h : G), g⁆
  map_one' := by simp
  map_mul' a b := by
    have hx : g * (a : G)⁻¹ * g⁻¹ ∈ H := (mem_normalizer_iff.1 hg _).1 (inv_mem a.2)
    have hy : g * (b : G)⁻¹ * g⁻¹ ∈ H := (mem_normalizer_iff.1 hg _).1 (inv_mem b.2)
    have h1 := hH _ hy _ hx
    have h2 := hH _ b.2 _ hx
    simp only [Subgroup.coe_mul, commutatorElement_def]
    calc (a : G) * b * g * ((a : G) * b)⁻¹ * g⁻¹ =
          (a : G) * b * ((g * (b : G)⁻¹ * g⁻¹) * (g * (a : G)⁻¹ * g⁻¹)) := by group
      _ = (a : G) * (b * (g * (a : G)⁻¹ * g⁻¹)) * (g * (b : G)⁻¹ * g⁻¹) := by
          rw [h1]; group
      _ = (a : G) * ((g * (a : G)⁻¹ * g⁻¹) * b) * (g * (b : G)⁻¹ * g⁻¹) := by rw [h2]
      _ = (a : G) * g * (a : G)⁻¹ * g⁻¹ * ((b : G) * g * (b : G)⁻¹ * g⁻¹) := by group

theorem commMap_apply {H : Subgroup G} {hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a} {g : G}
    {hg : g ∈ normalizer (H : Set G)} (h : H) : commMap H hH g hg h = ⁅(h : G), g⁆ := rfl

theorem commutator_zpowers_eq_range {H : Subgroup G} (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {g : G} (hg : g ∈ normalizer (H : Set G)) (hg2 : g ^ 2 = 1) :
    ⁅H, zpowers g⁆ = (commMap H hH g hg).range := by
  refine le_antisymm ((commutator_le).2 fun h hh k hk => ?_) ?_
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hk
    rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have e : g ^ (m + m) = 1 := by
        rw [← two_mul, zpow_mul, show (g ^ (2 : ℤ)) = g ^ 2 from zpow_natCast g 2, hg2, one_zpow]
      rw [e, commutatorElement_one_right]
      exact one_mem _
    · have e : g ^ (2 * m + 1) = g := by
        rw [zpow_add, zpow_mul, show (g ^ (2 : ℤ)) = g ^ 2 from zpow_natCast g 2, hg2, one_zpow,
          one_mul, zpow_one]
      rw [e]
      exact ⟨⟨h, hh⟩, rfl⟩
  · rintro _ ⟨h, rfl⟩
    exact commutator_mem_commutator h.2 (mem_zpowers g)

theorem mem_commutator_zpowers_iff {H : Subgroup G} (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    {g : G} (hg : g ∈ normalizer (H : Set G)) (hg2 : g ^ 2 = 1) {x : G} :
    x ∈ ⁅H, zpowers g⁆ ↔ ∃ h ∈ H, ⁅h, g⁆ = x := by
  rw [commutator_zpowers_eq_range hH hg hg2]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, hh⟩, rfl⟩

theorem card_commutator_zpowers_le_mul [Finite G] {H Q : Subgroup G} (hQH : Q ≤ H)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {g : G} (hg : g ∈ normalizer (H : Set G))
    (hg2 : g ^ 2 = 1) {ι : Type*} [Finite ι] (t : ι → G) (htH : ∀ i, t i ∈ H)
    (hdec : ∀ h ∈ H, ∃ q ∈ Q, ∃ i, h = q * t i) :
    Nat.card (⁅H, zpowers g⁆ : Subgroup G) ≤
      Nat.card (⁅Q, zpowers g⁆ : Subgroup G) * Nat.card ι := by
  have hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => hH a (hQH ha) b (hQH hb)
  let F : ↥(⁅Q, zpowers g⁆ : Subgroup G) × ι → G := fun p => (p.1 : G) * ⁅t p.2, g⁆
  have hsub : ((⁅H, zpowers g⁆ : Subgroup G) : Set G) ⊆ Set.range F := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := (mem_commutator_zpowers_iff hH hg hg2).1 hx
    obtain ⟨q, hq, i, rfl⟩ := hdec h hh
    have e := (commMap H hH g hg).map_mul ⟨q, hQH hq⟩ ⟨t i, htH i⟩
    simp only [commMap_apply, MulMemClass.mk_mul_mk] at e
    refine ⟨(⟨⁅q, g⁆, commutator_mem_commutator hq (mem_zpowers g)⟩, i), ?_⟩
    simp only [F]
    exact e.symm
  calc Nat.card ↥(⁅H, zpowers g⁆ : Subgroup G) =
        Nat.card ((⁅H, zpowers g⁆ : Subgroup G) : Set G) := rfl
    _ ≤ Nat.card (Set.range F) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (↥(⁅Q, zpowers g⁆ : Subgroup G) × ι) := Finite.card_range_le F
    _ = Nat.card ↥(⁅Q, zpowers g⁆ : Subgroup G) * Nat.card ι := Nat.card_prod _ _

end General

@[expose] def uYFrame : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 2, 2, 1, 1, 0], ![1, 1, 1, 2, 2, 1, 0]]

@[expose] def uZFrame : List (Fin Tag.E7.rank → ℤ) :=
  [![0, 1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 1, 1, 0], ![1, 1, 2, 2, 1, 0, 0]]

@[expose] def uYPivots : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 0, 0, 0, 0, 1, 1], ![1, 1, 1, 2, 2, 1, 0]),
   (![0, 0, 0, 0, 1, 1, 1], ![1, 1, 2, 2, 1, 1, 0]),
   (![0, 0, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 1, 0]),
   (![0, 0, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 0]),
   (![0, 1, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 1, 0]),
   (![0, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 0]),
   (![0, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 0]),
   (![0, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 0]),
   (![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 0])]

@[expose] def uZPivots : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 0, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 0, 0]),
   (![0, 0, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 0]),
   (![0, 1, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 0, 0]),
   (![0, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1, 0]),
   (![0, 1, 1, 2, 2, 1, 1], ![1, 1, 1, 2, 1, 1, 0]),
   (![0, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 0, 0]),
   (![1, 0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 0]),
   (![1, 1, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 2, 1, 0]),
   (![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 0, 0])]

@[expose] def PivotData (T : List (Fin Tag.E7.rank → ℤ))
    (P : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))) : Prop :=
  T.Nodup ∧ (∀ g ∈ T, isRootB .E7 g = true ∧ uLevel g = 0) ∧
    (∀ p ∈ P, p.1 ∈ uPsi ∧ p.2 ∈ T ∧ isRootB .E7 (p.1 + p.2) = true ∧
      ∀ g ∈ T, g ≠ p.2 → isRootB .E7 (p.1 + g) = false ∧ isRootB .E7 (p.1 + p.2 + g) = false) ∧
    (P.map fun p => p.1 + p.2).Nodup

instance (T : List (Fin Tag.E7.rank → ℤ))
    (P : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))) : Decidable (PivotData T P) := by
  unfold PivotData
  infer_instance

theorem uYPivots_check : PivotData uYFrame uYPivots ∧ uYPivots.length = 9 := by
  decide +kernel

theorem uZPivots_check : PivotData uZFrame uZPivots ∧ uZPivots.length = 9 := by
  decide +kernel

section Count

variable {K : Type} [Field K]


@[expose] def listCoeff {τ : Tag} (l : List (Fin τ.rank → ℤ)) (c : Fin l.length → K) :
    (Fin τ.rank → ℤ) → K :=
  fun β => ∑ i, if l.get i = β then c i else 0

theorem listCoeff_get {τ : Tag} {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup) (c : Fin l.length → K)
    (j : Fin l.length) : listCoeff l c (l.get j) = c j := by
  simp only [listCoeff, hnd.get_inj_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem pow_length_le_card_of_pinnedX_mem [Finite K] {τ : Tag} {S : Subgroup (ModGL τ K)}
    {l : List (Fin τ.rank → ℤ)} (hnd : l.Nodup) (hpos : ∀ β ∈ l, IsRoot τ β ∧ 0 < height β)
    (hS : ∀ β ∈ l, ∀ s : K, pinnedX τ K β s ∈ S) : Nat.card K ^ l.length ≤ Nat.card S := by
  have : Finite (ModGL τ K) := finite_modGL
  let F : (Fin l.length → K) → S := fun c => ⟨rootProd τ K l (listCoeff l c),
    list_prod_mem fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact hS β hβ _⟩
  have hF : Function.Injective F := by
    intro c d h
    have h' := E6Pilot.rootProd_injective hnd hpos (congrArg Subtype.val h)
    funext j
    rw [← listCoeff_get hnd c j, ← listCoeff_get hnd d j]
    exact h' _ (List.get_mem l j)
  calc Nat.card K ^ l.length = Nat.card (Fin l.length → K) := by
        rw [Nat.card_fun, Nat.card_fin]
    _ ≤ Nat.card S := Nat.card_le_card_of_injective F hF

theorem card_rootSpan_le_pow_length [Finite K] {τ : Tag} {l : List (Fin τ.rank → ℤ)}
    (hnd : l.Nodup) (hl : RootCommFamily τ K l) :
    Nat.card (rootSpan τ K {β | β ∈ l}) ≤ Nat.card K ^ l.length := by
  have : Finite (ModGL τ K) := finite_modGL
  let F : (Fin l.length → K) → rootSpan τ K {β | β ∈ l} := fun c =>
    ⟨rootProd τ K l (listCoeff l c), list_prod_mem fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      exact pinnedX_mem_rootSpan (show β ∈ {β | β ∈ l} from hβ) _⟩
  have hF : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨d, rfl⟩ := exists_rootProd_eq_of_mem_rootSpan hnd hl hg
    refine ⟨fun i => d (l.get i), Subtype.ext ?_⟩
    refine E6Pilot.rootProd_congr fun β hβ => ?_
    obtain ⟨j, rfl⟩ := List.get_of_mem hβ
    exact listCoeff_get hnd _ j
  calc Nat.card (rootSpan τ K {β | β ∈ l}) ≤ Nat.card (Fin l.length → K) :=
        Nat.card_le_card_of_surjective F hF
    _ = Nat.card K ^ l.length := by rw [Nat.card_fun, Nat.card_fin]

theorem conj_frame_pinnedX_uPsi [CharP K 2] {T : List (Fin Tag.E7.rank → ℤ)}
    (hT : ∀ g ∈ T, IsRoot .E7 g ∧ uLevel g = 0) (hnd : T.Nodup) {b g₀ : Fin Tag.E7.rank → ℤ}
    (hb : b ∈ uPsi) (hg₀0 : uLevel g₀ = 0) (hbg : IsRoot .E7 (b + g₀))
    (hother : ∀ g ∈ T, g ≠ g₀ → ¬IsRoot .E7 (b + g) ∧ ¬IsRoot .E7 (b + g₀ + g)) (s : K) :
    (T.map fun g => pinnedX .E7 K g 1).prod * pinnedX .E7 K b s *
        ((T.map fun g => pinnedX .E7 K g 1).prod)⁻¹ =
      pinnedX .E7 K b s * (if g₀ ∈ T then pinnedX .E7 K (b + g₀) s else 1) := by
  classical
  have hρ : b + g₀ ∈ uPsi := mem_uPsi_of_level hbg (by
    rw [uLevel_add, hg₀0, add_zero, level_of_mem_uPsi hb])
  induction T with
  | nil => simp
  | cons g T ih =>
    rw [List.nodup_cons] at hnd
    have ih' := ih (fun g' hg' => hT g' (List.mem_cons_of_mem _ hg')) hnd.2
      (fun g' hg' hne => hother g' (List.mem_cons_of_mem _ hg') hne)
    obtain ⟨hgr, hg0⟩ := hT g List.mem_cons_self
    have hsplit : ((g :: T).map fun g => pinnedX .E7 K g 1).prod * pinnedX .E7 K b s *
        (((g :: T).map fun g => pinnedX .E7 K g 1).prod)⁻¹ =
        pinnedX .E7 K g 1 * ((T.map fun g => pinnedX .E7 K g 1).prod * pinnedX .E7 K b s *
          ((T.map fun g => pinnedX .E7 K g 1).prod)⁻¹) * (pinnedX .E7 K g 1)⁻¹ := by
      rw [List.map_cons, List.prod_cons]
      group
    rw [hsplit, ih']
    by_cases hgg : g = g₀
    · subst hgg
      rw [ite_eq_right hnd.1, mul_one, ite_eq_left List.mem_cons_self]
      have hcomm := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced (R := K)
        CharTwo.two_eq_zero
        (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl))))
        hgr (isRoot_of_mem_uPsi hb) (ne_of_uLevel_zero hg0 hb).1 (ne_of_uLevel_zero hg0 hb).2
        (by rw [add_comm]; exact hbg) (1 : K) s
      rw [one_mul, commutatorElement_def, add_comm] at hcomm
      have hc : Commute (pinnedX .E7 K b s) (pinnedX .E7 K (b + g) s) := uPsi_comm b hb _ hρ s s
      calc pinnedX .E7 K g 1 * pinnedX .E7 K b s * (pinnedX .E7 K g 1)⁻¹ =
            (pinnedX .E7 K g 1 * pinnedX .E7 K b s * (pinnedX .E7 K g 1)⁻¹ *
              (pinnedX .E7 K b s)⁻¹) * pinnedX .E7 K b s := by group
        _ = pinnedX .E7 K (b + g) s * pinnedX .E7 K b s := by rw [hcomm]
        _ = pinnedX .E7 K b s * pinnedX .E7 K (b + g) s := hc.eq.symm
    · obtain ⟨h1, h2⟩ := hother g List.mem_cons_self hgg
      have hc1 : Commute (pinnedX .E7 K g 1) (pinnedX .E7 K b s) :=
        CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hgr (isRoot_of_mem_uPsi hb)
          (ne_of_uLevel_zero hg0 hb).2 (by rw [add_comm]; exact h1) 1 s
      have hmem : (g₀ ∈ g :: T) ↔ g₀ ∈ T :=
        ⟨fun h => (List.mem_cons.1 h).resolve_left (Ne.symm hgg), List.mem_cons_of_mem _⟩
      by_cases h₀ : g₀ ∈ T
      · rw [ite_eq_left h₀, ite_eq_left (hmem.2 h₀)]
        have hc2 : Commute (pinnedX .E7 K g 1) (pinnedX .E7 K (b + g₀) s) :=
          CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv hgr (isRoot_of_mem_uPsi hρ)
            (ne_of_uLevel_zero hg0 hρ).2 (by rw [add_comm]; exact h2) 1 s
        rw [(hc1.mul_right hc2).eq, mul_inv_cancel_right]
      · rw [ite_eq_right h₀, ite_eq_right (fun h => h₀ (hmem.1 h)), mul_one, hc1.eq,
          mul_inv_cancel_right]

theorem pinnedX_add_mem_commutator_frame [CharP K 2] {T : List (Fin Tag.E7.rank → ℤ)}
    (hT : ∀ g ∈ T, IsRoot .E7 g ∧ uLevel g = 0) (hnd : T.Nodup) {b g₀ : Fin Tag.E7.rank → ℤ}
    (hb : b ∈ uPsi) (hg₀T : g₀ ∈ T) (hbg : IsRoot .E7 (b + g₀))
    (hother : ∀ g ∈ T, g ≠ g₀ → ¬IsRoot .E7 (b + g) ∧ ¬IsRoot .E7 (b + g₀ + g)) (s : K) :
    pinnedX .E7 K (b + g₀) s ∈ ⁅parabolicRadical .E7 K uNodes,
      zpowers (T.map fun g => pinnedX .E7 K g 1).prod⁆ := by
  have h := conj_frame_pinnedX_uPsi hT hnd hb (hT g₀ hg₀T).2 hbg hother s
  rw [ite_eq_left hg₀T] at h
  have hρ : b + g₀ ∈ uPsi := mem_uPsi_of_level hbg (by
    rw [uLevel_add, (hT g₀ hg₀T).2, add_zero, level_of_mem_uPsi hb])
  have e : pinnedX .E7 K (b + g₀) s =
      ⁅(T.map fun g => pinnedX .E7 K g 1).prod, pinnedX .E7 K b s⁆ := by
    rw [commutatorElement_def, h, (uPsi_comm b hb _ hρ s s).eq, mul_inv_cancel_right]
  rw [e, commutator_comm]
  exact commutator_mem_commutator (mem_zpowers _)
    (pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_of_mem_uPsi hb) s)

theorem pow_length_le_card_commutator_frame [Finite K] [CharP K 2]
    {T : List (Fin Tag.E7.rank → ℤ)} {P : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))}
    (h : PivotData T P) :
    Nat.card K ^ P.length ≤ Nat.card (⁅parabolicRadical .E7 K uNodes,
      zpowers (T.map fun g => pinnedX .E7 K g 1).prod⁆ : Subgroup (ModGL .E7 K)) := by
  obtain ⟨hnd, hT, hP, hPnd⟩ := h
  have hT' : ∀ g ∈ T, IsRoot .E7 g ∧ uLevel g = 0 := fun g hg =>
    ⟨isRootB_iff.1 (hT g hg).1, (hT g hg).2⟩
  have hmemΨ : ∀ p ∈ P, p.1 + p.2 ∈ uPsi := fun p hp =>
    mem_uPsi_of_level (isRootB_iff.1 (hP p hp).2.2.1) (by
      rw [uLevel_add, (hT' _ (hP p hp).2.1).2, add_zero, level_of_mem_uPsi (hP p hp).1])
  have hlen : (P.map fun p => p.1 + p.2).length = P.length := List.length_map _
  rw [← hlen]
  refine pow_length_le_card_of_pinnedX_mem hPnd (fun β hβ => ?_) (fun β hβ s => ?_)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hβ
    exact pos_of_mem_uPsi (hmemΨ p hp)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hβ
    obtain ⟨hb, hg₀T, hbg, hother⟩ := hP p hp
    exact pinnedX_add_mem_commutator_frame hT' hnd hb hg₀T (isRootB_iff.1 hbg)
      (fun g hg hne => ⟨not_isRoot_of_isRootB_false (hother g hg hne).1,
        not_isRoot_of_isRootB_false (hother g hg hne).2⟩) s

theorem pow_nine_le_card_commutator_frame [Finite K] [CharP K 2] {T : List (Fin Tag.E7.rank → ℤ)}
    (hT : T = uYFrame ∨ T = uZFrame) :
    Nat.card K ^ 9 ≤ Nat.card (⁅parabolicRadical .E7 K uNodes,
      zpowers (T.map fun g => pinnedX .E7 K g 1).prod⁆ : Subgroup (ModGL .E7 K)) := by
  rcases hT with rfl | rfl
  · rw [← uYPivots_check.2]
    exact pow_length_le_card_commutator_frame uYPivots_check.1
  · rw [← uZPivots_check.2]
    exact pow_length_le_card_commutator_frame uZPivots_check.1

theorem card_uTopGroup_le [Finite K] : Nat.card (uTopGroup K) ≤ Nat.card K ^ 6 := by
  have h := card_rootSpan_le_pow_length (K := K) uTop_check.1 uTop_comm
  rwa [show uTop.length = 6 from rfl] at h

end Count

end CFSG.SeitzReduction.E7Pilot
