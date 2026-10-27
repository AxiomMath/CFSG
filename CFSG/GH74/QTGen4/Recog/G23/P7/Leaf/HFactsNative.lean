module

public import CFSG.GH74.QTGen4.Recog.G23.GlueExt
public import Certificates.Data.G23RecogHFactsInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData

@[expose] def clsub (ss : List ↥Hc) : Subgroup ↥Hc := Subgroup.closure {s | s ∈ ss}

theorem clsub_nil : clsub [] = ⊥ := by simp [clsub]

theorem clsub_cons (a : ↥Hc) (ss : List ↥Hc) :
    clsub (a :: ss) = Subgroup.zpowers a ⊔ clsub ss := by
  have h : {s | s ∈ a :: ss} = {a} ∪ {s | s ∈ ss} := by
    ext s; simp
  rw [clsub, h, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  rfl

theorem clsub_append (ss ts : List ↥Hc) : clsub (ss ++ ts) = clsub ss ⊔ clsub ts := by
  have h : {s | s ∈ ss ++ ts} = {s | s ∈ ss} ∪ {s | s ∈ ts} := by
    ext s; simp
  rw [clsub, h, Subgroup.closure_union]
  rfl

theorem clsub_singleton (a : ↥Hc) : clsub [a] = Subgroup.zpowers a := by
  rw [clsub_cons, clsub_nil, sup_bot_eq]

theorem subset_clsub {ss : List ↥Hc} {s : ↥Hc} (hs : s ∈ ss) : s ∈ clsub ss :=
  Subgroup.subset_closure hs

theorem closure_eq_clsub {S : Set ↥Hc} {ss : List ↥Hc} (h : ∀ x, x ∈ S ↔ x ∈ ss) :
    Subgroup.closure S = clsub ss := by
  have : S = {s | s ∈ ss} := Set.ext h
  rw [clsub, this]

theorem Lx_mul (x y : ↥Hc) : Lx (x * y) = mulL (Lx x) (Lx y) := Lst_mul x.1 y.1

theorem Lx_one : Lx (1 : ↥Hc) = idL := glue_idL_eq.symm

theorem Lx_inj : Function.Injective Lx := fun _ _ h => Subtype.ext (Lst_injective h)

section Elts

theorem Lx_mem_elts (x : ↥Hc) : Lx x ∈ elts := Hc_sub_elts x.1 x.2

theorem exists_Lx {l : List ℕ} (hl : l ∈ elts) : ∃ x : ↥Hc, Lx x = l := by
  obtain ⟨σ, hσ, rfl⟩ := elts_sound l hl
  exact ⟨⟨σ, hσ⟩, rfl⟩

theorem card_top_Hc : Nat.card ↥(⊤ : Subgroup ↥Hc) = 576 :=
  Subgroup.card_top.trans Hc_card

theorem card_eq_filter (A : Subgroup ↥Hc) (p : List ℕ → Bool)
    (h : ∀ x : ↥Hc, x ∈ A ↔ p (Lx x) = true) : Nat.card ↥A = (elts.filter p).length := by
  have himg : Lx '' (A : Set ↥Hc) =
      (((elts.filter p).toFinset : Finset (List ℕ)) : Set (List ℕ)) := by
    ext l
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨Lx_mem_elts x, (h x).mp hx⟩)
    · intro hl
      obtain ⟨hl1, hl2⟩ := List.mem_filter.mp (List.mem_toFinset.mp hl)
      obtain ⟨x, rfl⟩ := exists_Lx hl1
      exact ⟨x, (h x).mpr hl2, rfl⟩
  show Nat.card (A : Set ↥Hc) = _
  rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Lx_inj, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (elts_nodup.filter p)]

end Elts

theorem cl_sound (ss : List ↥Hc) : ∀ l ∈ cl ss, ∃ x ∈ clsub ss, Lx x = l := by
  have hmul : ∀ x g, (∃ a ∈ clsub ss, Lx a = x) → (∃ b ∈ clsub ss, Lx b = g) →
      ∃ c ∈ clsub ss, Lx c = mulL x g := by
    rintro x g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Subgroup.mul_mem _ ha hb, Lx_mul a b⟩
  have hgs : ∀ g ∈ gensOf ss, ∃ b ∈ clsub ss, Lx b = g := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
      exact ⟨s, subset_clsub hs, rfl⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
      exact ⟨s⁻¹, Subgroup.inv_mem _ (subset_clsub hs), rfl⟩
  have hs : ∀ y ∈ [idL], ∃ a ∈ clsub ss, Lx a = y := by
    intro y hy
    rw [List.mem_singleton.mp hy]
    exact ⟨1, Subgroup.one_mem _, Lx_one⟩
  intro l hl
  exact bfsAux_sub (fun l => ∃ a ∈ clsub ss, Lx a = l) 576 mulL hmul (gensOf ss) hgs 600 [idL]
    [idL] hs hs l hl

theorem mem_clsub_of_mem_cl {ss : List ↥Hc} {x : ↥Hc} (h : Lx x ∈ cl ss) : x ∈ clsub ss := by
  obtain ⟨y, hy, hxy⟩ := cl_sound ss _ h
  rwa [← Lx_inj hxy]

theorem mem_cl_of_mem_closure {ss : List ↥Hc} (hc : ClosedAt ss) {x : ↥Hc}
    (hx : x ∈ Subgroup.closure {s | s ∈ ss}) : Lx x ∈ cl ss := by
  induction hx using Subgroup.closure_induction_right with
  | one => rw [Lx_one]; exact hc.1
  | mul_right x _ y hy ih =>
    rw [Lx_mul]
    exact hc.2 _ ih _ (List.mem_append_left _ (List.mem_map_of_mem (f := Lx) hy))
  | mul_inv_cancel x _ y hy ih =>
    rw [Lx_mul]
    exact hc.2 _ ih _ (List.mem_append_right _
      (List.mem_map_of_mem (f := fun s : ↥Hc => Lx s⁻¹) hy))

theorem mem_cl_of_mem_clsub {ss : List ↥Hc} (hc : ClosedAt ss) {x : ↥Hc} (hx : x ∈ clsub ss) :
    Lx x ∈ cl ss :=
  mem_cl_of_mem_closure hc hx

theorem eq_clsub_of {A : Subgroup ↥Hc} (ss : List ↥Hc) (h1 : ∀ s ∈ ss, s ∈ A)
    (h2 : ∀ x ∈ A, Lx x ∈ cl ss) : A = clsub ss :=
  le_antisymm (fun x hx => mem_clsub_of_mem_cl (h2 x hx))
    ((Subgroup.closure_le A).2 fun s hs => h1 s hs)

theorem card_clsub {ss : List ↥Hc} (hc : ClosedAt ss) (hnd : (cl ss).Nodup) :
    Nat.card ↥(clsub ss) = (cl ss).length := by
  have himg : Lx '' (clsub ss : Set ↥Hc) = ((cl ss).toFinset : Set (List ℕ)) := by
    ext l
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact List.mem_toFinset.mpr (mem_cl_of_mem_clsub hc hx)
    · intro hl
      obtain ⟨x, hx, rfl⟩ := cl_sound ss l (List.mem_toFinset.mp hl)
      exact ⟨x, hx, rfl⟩
  show Nat.card (clsub ss : Set ↥Hc) = _
  rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Lx_inj, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem comm_iff (u s : ↥Hc) : s * u = u * s ↔ mulL (Lx u) (Lx s) = mulL (Lx s) (Lx u) := by
  rw [← Lx_mul, ← Lx_mul]
  exact ⟨fun h => by rw [h], fun h => (Lx_inj h).symm⟩

theorem mem_cent_iff (u s : ↥Hc) :
    s ∈ Subgroup.centralizer ({u} : Set ↥Hc) ↔ mulL (Lx u) (Lx s) = mulL (Lx s) (Lx u) :=
  Subgroup.mem_centralizer_singleton_iff.trans (comm_iff u s)

theorem conj_mem_closure {G : Type*} [Group G] {S : Set G} (s : G)
    (h : ∀ p ∈ S, s * p * s⁻¹ ∈ Subgroup.closure S) :
    ∀ n ∈ Subgroup.closure S, s * n * s⁻¹ ∈ Subgroup.closure S := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have : s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem mem_normalizer_clsub_iff {sA : List ↥Hc} (hc : ClosedAt sA) (s : ↥Hc) :
    s ∈ Subgroup.normalizer (clsub sA : Set ↥Hc) ↔
      ∀ p ∈ sA, ∃ d ∈ cl sA, mulL (Lx s) (Lx p) = mulL d (Lx s) := by
  constructor
  · intro hs p hp
    have h1 : s * p * s⁻¹ ∈ clsub sA :=
      (Subgroup.mem_normalizer_iff.mp hs p).mp (subset_clsub hp)
    refine ⟨Lx (s * p * s⁻¹), mem_cl_of_mem_clsub hc h1, ?_⟩
    rw [← Lx_mul, ← Lx_mul, inv_mul_cancel_right]
  · intro h
    have hgen : ∀ p ∈ {x | x ∈ sA}, s * p * s⁻¹ ∈ Subgroup.closure {x | x ∈ sA} := by
      intro p hp
      obtain ⟨d, hd, hdp⟩ := h p hp
      obtain ⟨q, hq, rfl⟩ := cl_sound sA d hd
      have hsp : s * p = q * s := Lx_inj (by rw [Lx_mul, Lx_mul]; exact hdp)
      have hq' : s * p * s⁻¹ = q := by rw [hsp, mul_inv_cancel_right]
      rw [hq']
      exact hq
    have hall := conj_mem_closure s hgen
    exact Subgroup.mem_normalizer_fintype (fun n hn => hall n hn)

end CFSG.GH74.QTGen4.Recog.G23.P7.HFactsAux
