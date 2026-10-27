module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G]

theorem conj_mem_list_iff {M : Type*} [Group M] [DecidableEq M] {l : List M} {p : M}
    (h : ∀ a ∈ l, p * a * p⁻¹ ∈ l) (q : M) : p * q * p⁻¹ ∈ l ↔ q ∈ l := by
  refine ⟨fun hq => ?_, h q⟩
  obtain ⟨a, ha, hpa⟩ := Finset.surj_on_of_inj_on_of_card_le (s := l.toFinset)
    (t := l.toFinset) (fun a _ => p * a * p⁻¹)
    (fun a ha => List.mem_toFinset.2 (h a (List.mem_toFinset.1 ha)))
    (fun a b _ _ hab => by simpa using hab) le_rfl (p * q * p⁻¹) (List.mem_toFinset.2 hq)
  have hqa : q = a := by simpa using hpa
  exact hqa ▸ List.mem_toFinset.1 ha

theorem conj_inv_mem_list {M : Type*} [Group M] [DecidableEq M] {l : List M} {p : M}
    (h : ∀ a ∈ l, p * a * p⁻¹ ∈ l) (q : M) (hq : q ∈ l) : p⁻¹ * q * p ∈ l := by
  rw [← conj_mem_list_iff h]
  simpa [mul_assoc] using hq

theorem m24Elt4_mem {H : Subgroup S24} {bs : List S24} (hb : ∀ b ∈ bs, b ∈ H) (n : ℕ) :
    m24Elt4 bs n ∈ H := by
  have hget : ∀ k, bs.getD k 1 ∈ H := by
    intro k
    rw [List.getD_eq_getElem?_getD]
    cases hk : bs[k]? with
    | none => exact H.one_mem
    | some b => exact hb b (List.mem_of_getElem? hk)
  have key : ∀ (ks : List ℕ) (acc : S24), acc ∈ H →
      ks.foldl (fun acc k => if n.testBit k then acc * bs.getD k 1 else acc) acc ∈ H := by
    intro ks
    induction ks with
    | nil => exact fun acc h => h
    | cons k ks ih =>
      intro acc hacc
      apply ih
      dsimp only
      split_ifs
      · exact H.mul_mem hacc (hget k)
      · exact hacc
  exact key _ 1 H.one_mem

@[expose] def pinV {L : Subgroup G} (e : L ≃* NativeSporadic.M24) : S24 →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem finite_of_mulEquiv {L : Subgroup G} (e : L ≃* NativeSporadic.M24) : Finite L :=
  Finite.of_equiv _ e.symm.toEquiv

section Pin

variable {L : Subgroup G} (e : L ≃* NativeSporadic.M24)

theorem pinV_apply (q : S24) : pinV e q = ((e.symm q : L) : G) := rfl

theorem pinV_injective : Function.Injective (pinV e) := fun _ _ h =>
  e.symm.injective (Subtype.ext h)

theorem pinV_mem (q : S24) : pinV e q ∈ L := (e.symm q).2

theorem exists_pinV_eq {g : G} (hg : g ∈ L) : ∃ q, pinV e q = g :=
  ⟨e ⟨g, hg⟩, by simp [pinV_apply]⟩

theorem orderOf_pinV (q : S24) : orderOf (pinV e q) = orderOf q :=
  orderOf_injective (pinV e) (pinV_injective e) q

end Pin

@[expose] def ListImage (L : Subgroup G) (e : L ≃* NativeSporadic.M24) (X : Subgroup G)
    (l : List S24) : Prop :=
  X ≤ L ∧ ∀ x : L, (x : G) ∈ X ↔ e x ∈ l

namespace ListImage

variable {L X Y : Subgroup G} {e : L ≃* NativeSporadic.M24} {l l' : List S24}

theorem pinV_mem_iff (h : ListImage L e X l) (q : S24) : pinV e q ∈ X ↔ q ∈ l := by
  rw [pinV_apply, h.2, MulEquiv.apply_symm_apply]

theorem exists_eq (h : ListImage L e X l) {g : G} (hg : g ∈ X) : ∃ q ∈ l, pinV e q = g := by
  obtain ⟨q, rfl⟩ := exists_pinV_eq e (h.1 hg)
  exact ⟨q, (h.pinV_mem_iff q).1 hg, rfl⟩

theorem mem_iff (h : ListImage L e X l) (g : G) : g ∈ X ↔ ∃ q ∈ l, pinV e q = g :=
  ⟨h.exists_eq, fun ⟨q, hq, hg⟩ => hg ▸ (h.pinV_mem_iff q).2 hq⟩

theorem card (h : ListImage L e X l) (hl : l.Nodup) : Nat.card X = l.length := by
  classical
  have hset : (X : Set G) = pinV e '' (l.toFinset : Set S24) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_image, List.mem_toFinset]
    exact h.mem_iff g
  have h1 : Nat.card X = (X : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_image_of_injective _ (pinV_injective e), Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hl]

theorem elemAb (h : ListImage L e X l) (hc : ∀ a ∈ l, ∀ b ∈ l, a * b = b * a)
    (hs : ∀ a ∈ l, a * a = 1) : EgElemAb X := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := h.exists_eq hx
    obtain ⟨r, hr, rfl⟩ := h.exists_eq hy
    rw [← map_mul, ← map_mul, hc q hq r hr]
  · obtain ⟨q, hq, rfl⟩ := h.exists_eq hx
    rw [← map_mul, hs q hq, map_one]

theorem pinV_mem_normalizer (h : ListImage L e X l) {p : S24}
    (hp : ∀ a ∈ l, p * a * p⁻¹ ∈ l) : pinV e p ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  by_cases hg : g ∈ L
  · obtain ⟨q, rfl⟩ := exists_pinV_eq e hg
    rw [← map_inv, ← map_mul, ← map_mul, h.pinV_mem_iff, h.pinV_mem_iff, conj_mem_list_iff hp]
  · have h1 : g ∉ X := fun hx => hg (h.1 hx)
    have h2 : pinV e p * g * (pinV e p)⁻¹ ∉ X := by
      intro hx
      apply hg
      have hp' := pinV_mem e p
      have hgeq : g = (pinV e p)⁻¹ * (pinV e p * g * (pinV e p)⁻¹) * pinV e p := by group
      rw [hgeq]
      exact L.mul_mem (L.mul_mem (L.inv_mem hp') (h.1 hx)) hp'
    exact iff_of_false h1 h2

theorem pinV_mem_egNL (h : ListImage L e X l) {p : S24} (hp : ∀ a ∈ l, p * a * p⁻¹ ∈ l) :
    pinV e p ∈ egNL L X :=
  Subgroup.mem_inf.2 ⟨h.pinV_mem_normalizer hp, pinV_mem e p⟩

theorem inf (hX : ListImage L e X l) (hY : ListImage L e Y l') :
    ListImage L e (X ⊓ Y) (l.filter fun q => decide (q ∈ l')) := by
  refine ⟨inf_le_left.trans hX.1, fun x => ?_⟩
  rw [mem_inf, hX.2, hY.2, List.mem_filter, decide_eq_true_iff]

theorem le_closure (h : ListImage L e X l) {S : Set G} {bs : List S24}
    (hl : ∀ q ∈ l, ∃ n, q = m24Elt4 bs n) (hb : ∀ b ∈ bs, pinV e b ∈ S) :
    X ≤ closure S := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := h.exists_eq hg
  obtain ⟨n, rfl⟩ := hl q hq
  have hmem : m24Elt4 bs n ∈ (closure S).comap (pinV e) :=
    m24Elt4_mem (H := (closure S).comap (pinV e))
      (fun b hb' => (subset_closure (hb b hb') : pinV e b ∈ closure S)) n
  exact hmem

theorem closure_eq (h : ListImage L e X l) {S : Set G} {bs : List S24}
    (hS : S ⊆ X) (hl : ∀ q ∈ l, ∃ n, q = m24Elt4 bs n) (hb : ∀ b ∈ bs, pinV e b ∈ S) :
    closure S = X :=
  le_antisymm ((closure_le X).2 hS) (h.le_closure hl hb)

end ListImage

theorem exists_listImage {L : Subgroup G} (e : L ≃* NativeSporadic.M24) {l : List S24}
    (h1 : (1 : S24) ∈ l) (hmul : ∀ x ∈ l, ∀ y ∈ l, x * y ∈ l) :
    ∃ X : Subgroup G, ListImage L e X l := by
  obtain ⟨R, hR⟩ := exists_subgroup_of_list l h1 hmul
  refine ⟨R.map (pinV e), ?_, fun x => ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    exact pinV_mem e q
  · rw [← hR]
    constructor
    · rintro ⟨q, hq, hqx⟩
      have hqe : q = e x := by
        apply e.symm.injective
        apply Subtype.ext
        rw [MulEquiv.symm_apply_apply]
        exact hqx
      rw [← hqe]
      exact hq
    · intro hx
      exact ⟨e x, hx, by simp [pinV_apply]⟩

theorem PairType.exists_listImage {L A B : Subgroup G} (h : PairType L A B) :
    ∃ e : L ≃* NativeSporadic.M24, ListImage L e A m24E1l ∧ ListImage L e B m24B0l := by
  obtain ⟨hA, hB, e, he⟩ := h
  exact ⟨e, ⟨hA, he.1⟩, ⟨hB, he.2⟩⟩

theorem OctadType.exists_listImage {L B : Subgroup G} (h : OctadType L B) :
    ∃ e : L ≃* NativeSporadic.M24, ListImage L e B m24B0l := by
  obtain ⟨hB, e, he⟩ := h
  exact ⟨e, ⟨hB, he⟩⟩

theorem pairType_of_listImage {L A B : Subgroup G} {e : L ≃* NativeSporadic.M24}
    (hA : ListImage L e A m24E1l) (hB : ListImage L e B m24B0l) : PairType L A B :=
  ⟨hA.1, hB.1, e, hA.2, hB.2⟩

end CFSG.EvenSporadicStandard.M24Std
