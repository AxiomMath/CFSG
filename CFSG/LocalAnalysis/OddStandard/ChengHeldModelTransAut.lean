module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelTables

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.OddStandard.ChengHeld.M1b (evalE)

namespace AutAux

variable {G : Type} [Group G]

@[expose] def conjHom (S : Subgroup G) (y : G) (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) : ↥S →* ↥S where
  toFun s := ⟨y⁻¹ * s * y, hy s s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjHom_coe {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) (s : ↥S) :
    ((conjHom S y hy s : ↥S) : G) = y⁻¹ * s * y := rfl

theorem actTable_conjHom {S : Subgroup G} (x : Fin 7 → ↥S) {y : G}
    (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) {α k : ℕ}
    (hact : ∀ e ∈ tableRels α k,
      y⁻¹ * ((natFam x e.1 : ↥S) : G) * y = ((evalE (natFam x) e.2 : ↥S) : G)) :
    ActTable α k (conjHom S y hy) x :=
  fun e he => Subtype.ext (hact e he)

theorem map_fixedSub (S : Subgroup G) (k : ℕ) (x : Fin 7 → ↥S) :
    (fixedSub k x).map S.subtype = fixedSubG k (fun j => ((x j : ↥S) : G)) := by
  unfold fixedSub fixedSubG
  split_ifs <;> simp [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]

theorem mem_fixedSubG_iff {S : Subgroup G} (k : ℕ) (x : Fin 7 → ↥S) (s : ↥S) :
    (s : G) ∈ fixedSubG k (fun j => ((x j : ↥S) : G)) ↔ s ∈ fixedSub k x := by
  rw [← map_fixedSub]
  exact Subgroup.mem_map_iff_mem S.subtype_injective

theorem fixed_set_eq {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) :
    {s : G | s ∈ S ∧ y⁻¹ * s * y = s} = Subtype.val '' {h : ↥S | conjHom S y hy h = h} := by
  ext s
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨⟨s, hs⟩, Subtype.ext h, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, congrArg Subtype.val hh⟩

theorem fixedFacts {S : Subgroup G} (x : Fin 7 → ↥S) {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    {α k : ℕ} (hF : AutFacts α k (conjHom S y hy) x) :
    (∀ s ∈ S, y⁻¹ * (y⁻¹ * s * y) * y = s) ∧
      {s : G | s ∈ S ∧ y⁻¹ * s * y = s}.ncard = (autData α k).1 ∧
      (α ≤ 1 → ∀ s ∈ S, y⁻¹ * s * y = s → s ∈ fixedSubG k (fun j => ((x j : ↥S) : G))) ∧
      (α = 2 → ∀ s ∈ S, (y⁻¹ * s * y = s ↔ s ∈ fixedSubG k (fun j => ((x j : ↥S) : G)))) := by
  refine ⟨fun s hs => congrArg Subtype.val (hF.invol ⟨s, hs⟩), ?_, ?_, ?_⟩
  · rw [fixed_set_eq hy, Set.ncard_image_of_injective _ Subtype.val_injective,
      ← Nat.card_coe_set_eq]
    exact hF.fixed_card
  · intro hα s hs h
    refine (mem_fixedSubG_iff k x ⟨s, hs⟩).2 ?_
    exact hF.fixed_le hα (show conjHom S y hy ⟨s, hs⟩ = ⟨s, hs⟩ from Subtype.ext h)
  · intro hα s hs
    have hE := hF.fixed_eq hα
    rw [show s = ((⟨s, hs⟩ : ↥S) : G) from rfl, mem_fixedSubG_iff k x ⟨s, hs⟩]
    constructor
    · intro h
      have hm : (⟨s, hs⟩ : ↥S) ∈ {h : ↥S | conjHom S y hy h = h} := Subtype.ext h
      rw [hE] at hm
      exact hm
    · intro h
      have hm : (⟨s, hs⟩ : ↥S) ∈ (fixedSub k x : Set ↥S) := h
      rw [← hE] at hm
      exact congrArg Subtype.val hm

theorem sq_coset {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) (hy2 : y * y = 1)
    (s : ↥S) : (s : G) * y * ((s : G) * y) = ((s * conjHom S y hy s : ↥S) : G) := by
  rw [Subgroup.coe_mul, conjHom_coe, inv_eq_of_mul_eq_one_right hy2]
  simp only [mul_assoc]

theorem sq_coset_iff {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    (hy2 : y * y = 1) (s : ↥S) :
    (s : G) * y * ((s : G) * y) = 1 ↔ s * conjHom S y hy s = 1 := by
  rw [sq_coset hy hy2 s]
  exact OneMemClass.coe_eq_one

theorem conj_coset {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) (hy2 : y * y = 1)
    (s u : ↥S) :
    (u : G)⁻¹ * ((s : G) * y) * u = ((u⁻¹ * s * conjHom S y hy u : ↥S) : G) * y := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, conjHom_coe,
    inv_eq_of_mul_eq_one_right hy2]
  simp only [mul_assoc, hy2, mul_one]

theorem conj_iff {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) (hy2 : y * y = 1)
    (s q : ↥S) :
    (∃ u ∈ S, (q : G) * y = u⁻¹ * ((s : G) * y) * u) ↔ q ∈ twClass (conjHom S y hy) s := by
  constructor
  · rintro ⟨u, hu, h⟩
    have h2 : (q : G) * y = ((⟨u, hu⟩⁻¹ * s * conjHom S y hy ⟨u, hu⟩ : ↥S) : G) * y :=
      h.trans (conj_coset hy hy2 s ⟨u, hu⟩)
    exact ⟨⟨u, hu⟩, Subtype.ext (mul_right_cancel h2)⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, u.2, (conj_coset hy hy2 s u).symm⟩

theorem coe_mul_right_injective (S : Subgroup G) (y : G) :
    Function.Injective (fun q : ↥S => (q : G) * y) :=
  fun _ _ h => Subtype.ext (mul_right_cancel h)

theorem class_eq_image {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    (hy2 : y * y = 1) (s : ↥S) :
    {z' : G | ∃ u ∈ S, z' = u⁻¹ * ((s : G) * y) * u} =
      (fun q : ↥S => (q : G) * y) '' twClass (conjHom S y hy) s := by
  ext z'
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, hu⟩⁻¹ * s * conjHom S y hy ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, ?_⟩
    exact (conj_coset hy hy2 s ⟨u, hu⟩).symm
  · rintro ⟨q, hq, rfl⟩
    exact (conj_iff hy hy2 s q).2 hq

theorem class_ncard {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    (hy2 : y * y = 1) (s : ↥S) :
    {z' : G | ∃ u ∈ S, z' = u⁻¹ * ((s : G) * y) * u}.ncard =
      (twClass (conjHom S y hy) s).ncard := by
  rw [class_eq_image hy hy2 s, Set.ncard_image_of_injective _ (coe_mul_right_injective S y)]

theorem coset_set_eq {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    (hy2 : y * y = 1) :
    {z : G | (∃ s ∈ S, z = s * y) ∧ z * z = 1} =
      (fun q : ↥S => (q : G) * y) '' {s : ↥S | s * conjHom S y hy s = 1} := by
  ext z
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, h⟩
    exact ⟨⟨s, hs⟩, (sq_coset_iff hy hy2 ⟨s, hs⟩).1 h, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, q.2, rfl⟩, (sq_coset_iff hy hy2 q).2 hq⟩

theorem classSizes_of {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    (hy2 : y * y = 1) {sizes : List ℕ} (h : TwSizes (conjHom S y hy) sizes) :
    ClassSizes S y sizes := by
  obtain ⟨reps, hmap, hinv, hpw, hcov⟩ := h
  refine ⟨reps.map (fun q : ↥S => (q : G) * y), ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hz
    exact ⟨⟨q, q.2, rfl⟩, (sq_coset_iff hy hy2 q).2 (hinv q hq)⟩
  · rw [List.map_map, ← hmap]
    exact List.map_congr_left fun q _ => class_ncard hy hy2 q
  · rw [List.pairwise_map]
    refine hpw.imp fun {a b} hab => ?_
    rintro ⟨u, hu, h⟩
    exact hab ((conj_iff hy hy2 a b).1 ⟨u, hu, h⟩)
  · rintro z ⟨s, hs, rfl⟩ hz
    obtain ⟨q, hq, hmem⟩ := hcov _ ((sq_coset_iff hy hy2 ⟨s, hs⟩).1 hz)
    obtain ⟨u, hu, h⟩ := (conj_iff hy hy2 q ⟨s, hs⟩).2 hmem
    exact ⟨_, List.mem_map_of_mem hq, u, hu, h⟩

theorem conj_one_iff {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S)
    (hy2 : y * y = 1) (q : ↥S) :
    (∃ s ∈ S, s⁻¹ * y * s = (q : G) * y) ↔ q ∈ twClass (conjHom S y hy) 1 := by
  rw [← conj_iff hy hy2 1 q]
  simp only [OneMemClass.coe_one, one_mul, eq_comm]

theorem qOfG_eq {S : Subgroup G} (α : ℕ) (x : Fin 7 → ↥S) :
    qOfG α (fun j => ((x j : ↥S) : G)) = ((qOf α x : ↥S) : G) := by
  unfold qOfG qOf
  split_ifs <;> simp

end AutAux

section Generic

variable {G : Type} [Group G]

theorem autFactsG_of {S : Subgroup G} (x : Fin 7 → ↥S) {y : G}
    (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) {α k : ℕ}
    (hAut : ∀ σ : ↥S →* ↥S, ActTable α k σ x → AutFacts α k σ x)
    (hact : ∀ e ∈ tableRels α k,
      y⁻¹ * ((natFam x e.1 : ↥S) : G) * y = ((evalE (natFam x) e.2 : ↥S) : G)) :
    AutFactsG S (fun j => ((x j : ↥S) : G)) α k y := by
  have hF := hAut _ (AutAux.actTable_conjHom x hy hact)
  obtain ⟨h1, h2, h3, h4⟩ := AutAux.fixedFacts x hy hF
  refine ⟨h1, h2, h3, h4, fun hy2 => ?_, fun hy2 => AutAux.classSizes_of hy hy2 hF.classes,
    fun hy2 => ?_, fun hy2 hα hk => ?_⟩
  · rw [AutAux.coset_set_eq hy hy2,
      Set.ncard_image_of_injective _ (AutAux.coe_mul_right_injective S y)]
    exact hF.T_card
  · rw [AutAux.qOfG_eq, AutAux.conj_one_iff hy hy2]
    exact hF.flag
  · obtain ⟨g1, g2, g3⟩ := hF.graph_orbit hα hk
    refine ⟨(AutAux.conj_one_iff hy hy2 _).2 g1, ?_, ?_⟩
    · rw [← Subgroup.coe_mul]
      exact (AutAux.conj_one_iff hy hy2 _).2 g2
    · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
      exact (AutAux.conj_one_iff hy hy2 _).2 g3

end Generic

end CFSG.OddStandard.ChengHeld
