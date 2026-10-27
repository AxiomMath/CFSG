module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6STri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SAE8Proof

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

@[expose] noncomputable def ae6Amb {H : Subgroup AE6Om} (α : MulAut H) (g : AE6Om) : AE6Om := by
  classical exact if hg : g ∈ H then (α ⟨g, hg⟩ : AE6Om) else g

theorem ae6Amb_of_mem {H : Subgroup AE6Om} (α : MulAut H) {g : AE6Om} (hg : g ∈ H) :
    ae6Amb α g = α ⟨g, hg⟩ := by
  unfold ae6Amb; exact dif_pos hg

theorem ae6Amb_coe {H : Subgroup AE6Om} (α : MulAut H) (x : H) : ae6Amb α (x : AE6Om) = α x :=
  ae6Amb_of_mem α x.2

theorem ae6Amb_mem {H : Subgroup AE6Om} (α : MulAut H) {g : AE6Om} (hg : g ∈ H) : ae6Amb α g ∈ H := by
  rw [ae6Amb_of_mem α hg]; exact (α _).2

theorem ae6Amb_mul {H : Subgroup AE6Om} (α : MulAut H) {g g' : AE6Om} (hg : g ∈ H) (hg' : g' ∈ H) :
    ae6Amb α (g * g') = ae6Amb α g * ae6Amb α g' := by
  rw [ae6Amb_of_mem α hg, ae6Amb_of_mem α hg', ae6Amb_of_mem α (mul_mem hg hg')]
  exact congrArg Subtype.val (map_mul α ⟨g, hg⟩ ⟨g', hg'⟩)

theorem ae6Amb_one {H : Subgroup AE6Om} (α : MulAut H) : ae6Amb α 1 = 1 := by
  rw [ae6Amb_of_mem α (one_mem H)]; exact congrArg Subtype.val (map_one α)

theorem ae6Amb_inv {H : Subgroup AE6Om} (α : MulAut H) {g : AE6Om} (hg : g ∈ H) :
    ae6Amb α g⁻¹ = (ae6Amb α g)⁻¹ := by
  rw [ae6Amb_of_mem α hg, ae6Amb_of_mem α (inv_mem hg)]
  exact congrArg Subtype.val (map_inv α ⟨g, hg⟩)

theorem ae6Amb_mul_aut {H : Subgroup AE6Om} (α β : MulAut H) {g : AE6Om} (hg : g ∈ H) :
    ae6Amb (α * β) g = ae6Amb α (ae6Amb β g) := by
  rw [ae6Amb_of_mem _ hg, ae6Amb_of_mem β hg, ae6Amb_of_mem α (β ⟨g, hg⟩).2]
  rfl

theorem ae6Amb_one_aut {H : Subgroup AE6Om} (g : AE6Om) : ae6Amb (1 : MulAut H) g = g := by
  unfold ae6Amb; split <;> rfl

theorem ae6Amb_conj {H : Subgroup AE6Om} {m : AE6Om} (hm : m ∈ H) {g : AE6Om} (hg : g ∈ H) :
    ae6Amb (MulAut.conj (⟨m, hm⟩ : H)) g = m * g * m⁻¹ := by
  rw [ae6Amb_of_mem _ hg]; rfl

theorem ae6Amb_inv_aut {H : Subgroup AE6Om} (α : MulAut H) {g : AE6Om} (hg : g ∈ H) :
    ae6Amb α⁻¹ (ae6Amb α g) = g := by
  rw [ae6Amb_of_mem α hg, ae6Amb_of_mem _ (α ⟨g, hg⟩).2]
  exact congrArg Subtype.val (MulEquiv.symm_apply_apply α ⟨g, hg⟩)

theorem ae6Amb_aut_inv {H : Subgroup AE6Om} (α : MulAut H) {g : AE6Om} (hg : g ∈ H) :
    ae6Amb α (ae6Amb α⁻¹ g) = g := by
  rw [ae6Amb_of_mem α⁻¹ hg, ae6Amb_of_mem _ (α⁻¹ ⟨g, hg⟩).2]
  exact congrArg Subtype.val (MulEquiv.apply_symm_apply α ⟨g, hg⟩)

theorem ae6Amb_injOn {H : Subgroup AE6Om} (α : MulAut H) {g g' : AE6Om} (hg : g ∈ H) (hg' : g' ∈ H)
    (he : ae6Amb α g = ae6Amb α g') : g = g' := by
  rw [ae6Amb_of_mem α hg, ae6Amb_of_mem α hg'] at he
  exact congrArg Subtype.val (α.injective (Subtype.ext he))

theorem ae6Amb_closure {H : Subgroup AE6Om} (α : MulAut H) {S : Set AE6Om} {T : Subgroup AE6Om} (hSH : S ⊆ H)
    (hS : ∀ s ∈ S, ae6Amb α s ∈ T) : ∀ g ∈ Subgroup.closure S, ae6Amb α g ∈ T := by
  have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 hSH
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => rw [ae6Amb_one]; exact one_mem T
  | mul x y hx hy ihx ihy => rw [ae6Amb_mul α (hle hx) (hle hy)]; exact mul_mem ihx ihy
  | inv x hx ihx => rw [ae6Amb_inv α (hle hx)]; exact inv_mem ihx

theorem ae6_aut_iff {G : Type*} [Group G] [Finite G] (α : MulAut G) {S T : Subgroup G}
    (hST : ∀ x ∈ S, α x ∈ T) (hc : Nat.card T ≤ Nat.card S) (x : G) : x ∈ S ↔ α x ∈ T := by
  have hle : S.map α.toMonoidHom ≤ T := by rintro _ ⟨y, hy, rfl⟩; exact hST y hy
  have heq : S.map α.toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α.injective]; exact hc)
  rw [← heq]
  exact (Subgroup.mem_map_iff_mem (f := α.toMonoidHom) α.injective).symm

theorem ae6Amb_iff {H : Subgroup AE6Om} (α : MulAut H) {S T : Subgroup AE6Om} (hS : S ≤ H) (hT : T ≤ H)
    (hST : ∀ x ∈ S, ae6Amb α x ∈ T) (hc : Nat.card T ≤ Nat.card S) {g : AE6Om} (hg : g ∈ H) :
    g ∈ S ↔ ae6Amb α g ∈ T := by
  have key := ae6_aut_iff α (S := S.subgroupOf H) (T := T.subgroupOf H)
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf, ← ae6Amb_of_mem α x.2]
      exact hST x (Subgroup.mem_subgroupOf.1 hx))
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv]
      exact hc) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← ae6Amb_of_mem α hg] at key
  exact key

theorem mem_conjSub_mul {a c x : AE6Om} {K : Subgroup AE6Om} :
    x ∈ conjSub (a * c) K ↔ a⁻¹ * x * a ∈ conjSub c K := by
  simp only [mem_conjSub_iff, mul_inv_rev, mul_assoc]

theorem conjSub_le_of_mem {c : AE6Om} {K H : Subgroup AE6Om} (hc : c ∈ H) (hK : K ≤ H) : conjSub c K ≤ H := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hc (hK hx)) (inv_mem hc)

theorem card_conjSub (c : AE6Om) (K : Subgroup AE6Om) : Nat.card (conjSub c K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem ae6ModelM_le (k : Fin 3) : ae6ModelM ≤ ae6ModelV k := by
  intro g hg
  simp only [ae6ModelM, Subgroup.mem_inf] at hg
  fin_cases k
  exacts [hg.1.1, hg.1.2, hg.2]

theorem mem_ae6ModelM {g : AE6Om} : g ∈ ae6ModelM ↔ ∀ l, g ∈ ae6ModelV l := by
  refine ⟨fun hg l => ae6ModelM_le l hg, fun hg => ?_⟩
  simp only [ae6ModelM, Subgroup.mem_inf]
  exact ⟨⟨hg 0, hg 1⟩, hg 2⟩

theorem ae6ModelM_le_E (a b : Fin 3) : ae6ModelM ≤ ae6ModelV a ⊓ ae6ModelV b :=
  le_inf (ae6ModelM_le a) (ae6ModelM_le b)

theorem ae6V_closure (k : Fin 3) :
    Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) => A6.curtisGen (i : Fin 8)) = ae6ModelV k := by
  rw [ae6ModelV_eq, ae6LetterSub, Set.image_eq_range]
  rfl

theorem ae6Word_vertex {k : Fin 3} {w : List (Fin 8)} (hw : ∀ i ∈ w, i ∈ ae6VertexLetters k) :
    ae6Word w ∈ ae6ModelV k := by
  rw [ae6ModelV_eq]; exact ae6Word_mem fun i hi => Finset.mem_coe.2 (hw i hi)

theorem ae6TriK_eq_words :
    ae6ModelK = Subgroup.closure {ae6Word (ae6KWord 0), ae6Word (ae6KWord 1)} := by
  simp only [ae6ModelK, ae6KWord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem ae6Word_singleton (i : Fin 8) : ae6Word [i] = A6.curtisGen i := by
  simp [ae6Word]

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem hMl : ae6ModelM = ae6LetterSub ↑ae6MLetters := h.1

theorem hEl {k l : Fin 3} (hkl : k ≠ l) : ae6ModelE k l = ae6LetterSub ↑(ae6EdgeLetters k l) := h.2.1 k l hkl

theorem hZ : ∀ m ∈ ae6ModelM, (∀ i ∈ ae6MLetters, m * A6.curtisGen i = A6.curtisGen i * m) → m = 1 := h.2.2.1

theorem hDl (k : Fin 3) : Nat.card (ae6ModelV k) = 1290240 ∧
    Nat.card (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
      (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta k i)))) = 1290240 ∧
    Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) => ae6Word (ae6Delta k i)) = ae6ModelV k ∧
    (∀ i ∈ ae6VertexLetters k, ∀ j ∈ ae6Delta k i, j ∈ ae6VertexLetters k ∧ (i ∈ ae6MLetters → j ∈ ae6MLetters) ∧
      ∀ l : Fin 3, l ≠ k → i ∈ ae6EdgeLetters k l → j ∈ ae6EdgeLetters k l) ∧
    ∀ s : Fin 3, ae6Word (ae6DeltaW k (ae6KWord s)) ∈ conjSub (ae6Word (ae6TriMemC k)) ae6ModelK :=
  h.2.2.2.1 k

theorem hQw : ∀ x : Fin 4, ∀ w ∈ ae6TriQWords x, (∀ i ∈ w, i ∈ ae6MLetters) ∧
    ∀ i ∈ ae6MLetters, A6.curtisGen i * ae6Word w * A6.curtisGen i ∈ ae6TriQ x := h.2.2.2.2.1

theorem hQd : ∀ x y : Fin 4, x ≠ y → ae6TriQ x ≠ ae6TriQ y := h.2.2.2.2.2.1

theorem hQδ : ∀ (k : Fin 3) (x : Fin 4), ∀ w ∈ ae6TriQWords x,
    ae6Word (ae6DeltaW k w) ∈ ae6TriQ (ae6DeltaQ k x) := h.2.2.2.2.2.2.1

theorem hA (e : Fin 3) :
    Subgroup.closure (Set.range fun i => ae6Word (ae6TriGen e i)) = ae6ModelE (ae6EdgeK e) (ae6EdgeL e) ∧
    (∀ i, ae6Word (ae6TriGen e i) ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) ∧
    ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e)) →
      (∀ u ∈ ae6TriProf,
        orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen e i)).prod ∧
        ((u.map y).prod ∈ ae6ModelM ↔ (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6ModelM) ∧
        ((u.map y).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e) ↔
          (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈ ae6EdgeQuat (ae6EdgeK e) (ae6EdgeL e))) →
      ∃ m ∈ ae6ModelM, ∃ j : Fin 6, ∀ i, y i = m * ae6Word (ae6TriRep e j (ae6TriGen e i)) * m⁻¹ :=
  h.2.2.2.2.2.2.2 e

theorem K_le_M : ae6ModelK ≤ ae6ModelM := by
  rw [ae6TriK_eq_words, Subgroup.closure_le, h.hMl]
  rintro _ (rfl | rfl) <;> exact ae6Word_mem fun i hi => by revert i; decide

theorem K_le_V (k : Fin 3) : ae6ModelK ≤ ae6ModelV k := h.K_le_M.trans (ae6ModelM_le k)

end AE6TriFin

theorem ae6TriGraph_word (k : Fin 3) {w : List (Fin 8)} (hw : ∀ i ∈ w, i ∈ ae6VertexLetters k) :
    (ae6Word w, ae6Word (ae6DeltaW k w)) ∈ Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
      (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta k i))) := by
  induction w with
  | nil =>
    have e : (ae6Word [], ae6Word (ae6DeltaW k [])) = 1 := by simp [ae6Word, ae6DeltaW]
    rw [e]; exact one_mem _
  | cons a w ih =>
    have e : (ae6Word (a :: w), ae6Word (ae6DeltaW k (a :: w))) =
        (A6.curtisGen a, ae6Word (ae6Delta k a)) * (ae6Word w, ae6Word (ae6DeltaW k w)) := by
      simp [ae6Word, ae6DeltaW, List.flatMap_cons]
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨⟨a, hw a (by simp)⟩, rfl⟩)
      (ih fun i hi => hw i (by simp [hi]))

theorem AE6TriFin.exists_delta (h : AE6TriFin) (k : Fin 3) :
    ∃ δ : MulAut ↥(ae6ModelV k), ∀ g ∈ Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
      (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta k i))), ∀ hg : g.1 ∈ ae6ModelV k,
        (δ ⟨g.1, hg⟩ : AE6Om) = g.2 :=
  ae6_graph_iso _ _ (ae6V_closure k) (h.hDl k).2.2.1 (by rw [(h.hDl k).2.1, (h.hDl k).1])
    (by rw [(h.hDl k).2.1, (h.hDl k).1])

@[expose] noncomputable def ae6TriDl (h : AE6TriFin) (k : Fin 3) : MulAut ↥(ae6ModelV k) :=
  (h.exists_delta k).choose

@[expose] noncomputable def ae6TriD (h : AE6TriFin) (k : Fin 3) : AE6Om → AE6Om := ae6Amb (ae6TriDl h k)

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem D_word (k : Fin 3) {w : List (Fin 8)} (hw : ∀ i ∈ w, i ∈ ae6VertexLetters k) :
    ae6TriD h k (ae6Word w) = ae6Word (ae6DeltaW k w) := by
  rw [ae6TriD, ae6Amb_of_mem _ (ae6Word_vertex hw)]
  exact (h.exists_delta k).choose_spec _ (ae6TriGraph_word k hw) _

theorem D_gen (k : Fin 3) {i : Fin 8} (hi : i ∈ ae6VertexLetters k) :
    ae6TriD h k (A6.curtisGen i) = ae6Word (ae6Delta k i) := by
  have := h.D_word k (w := [i]) (by simpa using hi)
  rwa [ae6Word_singleton, ae6DeltaW, List.flatMap_cons, List.flatMap_nil, List.append_nil] at this

theorem D_letterSub_iff (k : Fin 3) {A : Finset (Fin 8)} (hAV : A ⊆ ae6VertexLetters k)
    (hA : ∀ i ∈ A, ∀ j ∈ ae6Delta k i, j ∈ A) {g : AE6Om} (hg : g ∈ ae6ModelV k) :
    g ∈ ae6LetterSub ↑A ↔ ae6TriD h k g ∈ ae6LetterSub ↑A := by
  have hle : ae6LetterSub ↑A ≤ ae6ModelV k := by
    rw [ae6ModelV_eq]; exact ae6LetterSub_mono (Finset.coe_subset.2 hAV)
  refine ae6Amb_iff _ hle hle (ae6Amb_closure _ (fun _ ⟨i, hi, e⟩ => e ▸ hle (gen_mem_letterSub hi)) ?_) le_rfl hg
  rintro _ ⟨i, hi, rfl⟩
  have := h.D_gen k (hAV hi)
  rw [ae6TriD] at this
  rw [this]
  exact ae6Word_mem fun j hj => Finset.mem_coe.2 (hA i hi j hj)

end AE6TriFin

@[expose] def ae6TriGood (k : Fin 3) (α : MulAut ↥(ae6ModelV k)) : Prop :=
  (∀ l, ∀ g ∈ ae6ModelV k, g ∈ ae6ModelV l ↔ ae6Amb α g ∈ ae6ModelV l) ∧
    ∃ c ∈ ae6ModelM, ∀ g ∈ ae6ModelV k, g ∈ ae6ModelK ↔ ae6Amb α g ∈ conjSub c ae6ModelK

theorem ae6TriGood.M_iff {k : Fin 3} {α : MulAut ↥(ae6ModelV k)} (hα : ae6TriGood k α) {g : AE6Om}
    (hg : g ∈ ae6ModelV k) : g ∈ ae6ModelM ↔ ae6Amb α g ∈ ae6ModelM := by
  simp only [mem_ae6ModelM]
  exact forall_congr' fun l => hα.1 l g hg

theorem ae6TriGood.inv_V {k : Fin 3} {α : MulAut ↥(ae6ModelV k)} (hα : ae6TriGood k α) (l : Fin 3) {g : AE6Om}
    (hg : g ∈ ae6ModelV k) : g ∈ ae6ModelV l ↔ ae6Amb α⁻¹ g ∈ ae6ModelV l := by
  have := hα.1 l _ (ae6Amb_mem α⁻¹ hg)
  rw [ae6Amb_aut_inv α hg] at this
  exact this.symm

theorem ae6TriGood_one (k : Fin 3) : ae6TriGood k 1 := by
  refine ⟨fun l g _ => by rw [ae6Amb_one_aut], 1, one_mem _, fun g _ => ?_⟩
  rw [ae6Amb_one_aut, mem_conjSub_iff]; simp

theorem ae6TriGood_conj (k : Fin 3) {m : AE6Om} (hm : m ∈ ae6ModelM) :
    ae6TriGood k (MulAut.conj (⟨m, ae6ModelM_le k hm⟩ : ↥(ae6ModelV k))) := by
  refine ⟨fun l g hg => ?_, m, hm, fun g hg => ?_⟩
  · rw [ae6Amb_conj _ hg]
    have hml := ae6ModelM_le l hm
    constructor
    · intro h1; exact mul_mem (mul_mem hml h1) (inv_mem hml)
    · intro h1
      have e : g = m⁻¹ * (m * g * m⁻¹) * m := by group
      rw [e]; exact mul_mem (mul_mem (inv_mem hml) h1) hml
  · rw [ae6Amb_conj _ hg, mem_conjSub_iff]
    have e : m⁻¹ * (m * g * m⁻¹) * m = g := by group
    rw [e]

theorem ae6TriGood.mul {k : Fin 3} {α β : MulAut ↥(ae6ModelV k)} (hα : ae6TriGood k α) (hβ : ae6TriGood k β) :
    ae6TriGood k (α * β) := by
  obtain ⟨cα, hcα, hKα⟩ := hα.2
  obtain ⟨cβ, hcβ, hKβ⟩ := hβ.2
  have hcβV := ae6ModelM_le k hcβ
  refine ⟨fun l g hg => ?_, ae6Amb α cβ * cα, mul_mem ((hα.M_iff hcβV).1 hcβ) hcα, fun g hg => ?_⟩
  · rw [ae6Amb_mul_aut _ _ hg]
    exact (hβ.1 l g hg).trans (hα.1 l _ (ae6Amb_mem β hg))
  · have hx := ae6Amb_mem β hg
    rw [ae6Amb_mul_aut _ _ hg, mem_conjSub_mul, hKβ g hg, mem_conjSub_iff,
      hKα _ (mul_mem (mul_mem (inv_mem hcβV) hx) hcβV), ae6Amb_mul α (mul_mem (inv_mem hcβV) hx) hcβV,
      ae6Amb_mul α (inv_mem hcβV) hx, ae6Amb_inv α hcβV]

theorem ae6TriMemC_letters : ∀ k : Fin 3, ∀ i ∈ ae6TriMemC k, i ∈ ae6MLetters := by decide

theorem ae6KWord_letters : ∀ k s : Fin 3, ∀ i ∈ ae6KWord s, i ∈ ae6VertexLetters k := by decide

theorem ae6EdgeLetters_sub {k l : Fin 3} : ae6EdgeLetters k l ⊆ ae6VertexLetters k := by
  intro i hi
  simp only [ae6EdgeLetters, ae6VertexLetters, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.1

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem memC_mem (k : Fin 3) : ae6Word (ae6TriMemC k) ∈ ae6ModelM := by
  rw [h.hMl]; exact ae6Word_mem fun i hi => Finset.mem_coe.2 (ae6TriMemC_letters k i hi)

theorem D_good (k : Fin 3) : ae6TriGood k (ae6TriDl h k) := by
  refine ⟨fun l g hg => ?_, _, h.memC_mem k, fun g hg => ?_⟩
  · by_cases hlk : l = k
    · subst hlk; exact ⟨fun _ => ae6Amb_mem _ hg, fun _ => hg⟩
    have key := h.D_letterSub_iff k (A := ae6EdgeLetters k l) ae6EdgeLetters_sub
      (fun i hi j hj => ((h.hDl k).2.2.2.1 i (ae6EdgeLetters_sub hi) j hj).2.2 l hlk hi) hg
    rw [← h.hEl (Ne.symm hlk), ae6TriD] at key
    simp only [ae6ModelE, Subgroup.mem_inf] at key
    exact ⟨fun h1 => (key.1 ⟨hg, h1⟩).2, fun h1 => (key.2 ⟨ae6Amb_mem _ hg, h1⟩).2⟩
  · have hcV := ae6ModelM_le k (h.memC_mem k)
    refine ae6Amb_iff _ (h.K_le_V k) (conjSub_le_of_mem hcV (h.K_le_V k)) ?_ (card_conjSub _ _).le hg
    rw [ae6TriK_eq_words]
    refine ae6Amb_closure _ ?_ ?_
    · rintro _ (rfl | rfl) <;> exact ae6Word_vertex (ae6KWord_letters k _)
    · rintro _ (rfl | rfl)
      · change ae6TriD h k _ ∈ _
        rw [h.D_word k (ae6KWord_letters k 0)]; exact (h.hDl k).2.2.2.2 0
      · change ae6TriD h k _ ∈ _
        rw [h.D_word k (ae6KWord_letters k 1)]; exact (h.hDl k).2.2.2.2 1

end AE6TriFin

@[expose] noncomputable def ae6TriP (h : AE6TriFin) (k : Fin 3) (b : Bool) : MulAut ↥(ae6ModelV k) :=
  if b then ae6TriDl h k else 1

theorem AE6TriFin.P_good (h : AE6TriFin) (k : Fin 3) (b : Bool) : ae6TriGood k (ae6TriP h k b) := by
  cases b
  · exact ae6TriGood_one k
  · exact h.D_good k

@[expose] def ae6TriAut (E : Subgroup AE6Om) (f : AE6Om → AE6Om) : Prop :=
  (∀ g ∈ E, f g ∈ E) ∧ (∀ g ∈ E, ∀ g' ∈ E, f (g * g') = f g * f g') ∧ Set.InjOn f E ∧
    (∀ g ∈ E, g ∈ ae6ModelM ↔ f g ∈ ae6ModelM) ∧
    ∀ J ∈ ae6ConjIn E ae6ModelK, ∃ J' ∈ ae6ConjIn E ae6ModelK, ∀ g ∈ E, g ∈ J ↔ f g ∈ J'

theorem ae6TriGood.triAut {k a b : Fin 3} {α : MulAut ↥(ae6ModelV k)} (hα : ae6TriGood k α)
    (hk : ae6ModelE a b ≤ ae6ModelV k) : ae6TriAut (ae6ModelE a b) (ae6Amb α) := by
  obtain ⟨c, hc, hK⟩ := hα.2
  have hmaps : ∀ g ∈ ae6ModelE a b, ae6Amb α g ∈ ae6ModelE a b := fun g hg =>
    Subgroup.mem_inf.2 ⟨(hα.1 a g (hk hg)).1 (Subgroup.mem_inf.1 hg).1,
      (hα.1 b g (hk hg)).1 (Subgroup.mem_inf.1 hg).2⟩
  refine ⟨hmaps, fun g hg g' hg' => ae6Amb_mul α (hk hg) (hk hg'),
    fun g hg g' hg' he => ae6Amb_injOn α (hk hg) (hk hg') he, fun g hg => hα.M_iff (hk hg), ?_⟩
  rintro J ⟨x, hx, rfl⟩
  refine ⟨conjSub (ae6Amb α x * c) ae6ModelK, ⟨_, mul_mem (hmaps x hx) (ae6ModelM_le_E a b hc), rfl⟩,
    fun g hg => ?_⟩
  have hxk := hk hx
  rw [mem_conjSub_iff, hK _ (mul_mem (mul_mem (inv_mem hxk) (hk hg)) hxk), mem_conjSub_mul,
    ae6Amb_mul α (mul_mem (inv_mem hxk) (hk hg)) hxk, ae6Amb_mul α (inv_mem hxk) (hk hg), ae6Amb_inv α hxk]

theorem AE6EdgeAut.triAut {k l : Fin 3} {θ : MulAut ↥(ae6ModelE k l)} (hθ : AE6EdgeAut k l θ) :
    ae6TriAut (ae6ModelE k l) (ae6Amb θ) := by
  refine ⟨fun g hg => ae6Amb_mem θ hg, fun g hg g' hg' => ae6Amb_mul θ hg hg',
    fun g hg g' hg' he => ae6Amb_injOn θ hg hg' he,
    fun g hg => by rw [ae6Amb_of_mem θ hg]; exact hθ.1 ⟨g, hg⟩, fun J hJ => ?_⟩
  obtain ⟨J', hJ', hJJ⟩ := hθ.2 J hJ
  exact ⟨J', hJ', fun g hg => by rw [ae6Amb_of_mem θ hg]; exact hJJ ⟨g, hg⟩⟩

section TriAut

variable {E : Subgroup AE6Om} {f f' : AE6Om → AE6Om}

theorem ae6TriAut.comp (hf : ae6TriAut E f) (hf' : ae6TriAut E f') : ae6TriAut E (f' ∘ f) := by
  refine ⟨fun g hg => hf'.1 _ (hf.1 g hg), fun g hg g' hg' => ?_,
    fun g hg g' hg' he => hf.2.2.1 hg hg' (hf'.2.2.1 (hf.1 g hg) (hf.1 g' hg') he),
    fun g hg => (hf.2.2.2.1 g hg).trans (hf'.2.2.2.1 _ (hf.1 g hg)), fun J hJ => ?_⟩
  · simp only [Function.comp_apply, hf.2.1 g hg g' hg', hf'.2.1 _ (hf.1 g hg) _ (hf.1 g' hg')]
  · obtain ⟨J', hJ', hJJ⟩ := hf.2.2.2.2 J hJ
    obtain ⟨J'', hJ'', hJJ'⟩ := hf'.2.2.2.2 J' hJ'
    exact ⟨J'', hJ'', fun g hg => (hJJ g hg).trans (hJJ' _ (hf.1 g hg))⟩

theorem ae6TriAut.map_one (hf : ae6TriAut E f) : f 1 = 1 := by
  have := hf.2.1 1 (one_mem E) 1 (one_mem E)
  rw [mul_one] at this
  simpa using this

theorem ae6TriAut.map_inv (hf : ae6TriAut E f) {g : AE6Om} (hg : g ∈ E) : f g⁻¹ = (f g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hf.2.1 _ (inv_mem hg) _ hg, inv_mul_cancel, hf.map_one]

theorem ae6TriAut.map_prod (hf : ae6TriAut E f) :
    ∀ l : List AE6Om, (∀ x ∈ l, x ∈ E) → f l.prod = (l.map f).prod
  | [], _ => by simpa using hf.map_one
  | x :: l, hl => by
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      hf.2.1 x (hl x (by simp)) _ (E.list_prod_mem fun y hy => hl y (by simp [hy])),
      hf.map_prod l fun y hy => hl y (by simp [hy])]

theorem ae6TriAut.orderOf_eq (hf : ae6TriAut E f) {x : AE6Om} (hx : x ∈ E) : orderOf (f x) = orderOf x := by
  let φ : ↥E →* AE6Om :=
    { toFun := fun g => f g, map_one' := hf.map_one, map_mul' := fun g g' => hf.2.1 g g.2 g' g'.2 }
  have hφ : Function.Injective φ := fun g g' he => Subtype.ext (hf.2.2.1 g.2 g'.2 he)
  exact (orderOf_injective φ hφ ⟨x, hx⟩).trans (Subgroup.orderOf_coe _).symm

theorem ae6TriAut.surjOn (hf : ae6TriAut E f) : Set.SurjOn f E E :=
  (((Set.toFinite (E : Set AE6Om)).injOn_iff_bijOn_of_mapsTo fun g hg => hf.1 g hg).1 hf.2.2.1).surjOn

theorem ae6TriAut.surj_M (hf : ae6TriAut E f) (hM : ae6ModelM ≤ E) {y : AE6Om} (hy : y ∈ ae6ModelM) :
    ∃ x ∈ ae6ModelM, f x = y := by
  obtain ⟨x, hx, rfl⟩ := hf.surjOn (hM hy)
  exact ⟨x, (hf.2.2.2.1 x hx).2 hy, rfl⟩

theorem ae6TriAut.member_surj (hf : ae6TriAut E f) (hKE : ae6ModelK ≤ E) {J' : Subgroup AE6Om}
    (hJ' : J' ∈ ae6ConjIn E ae6ModelK) : ∃ J ∈ ae6ConjIn E ae6ModelK, ∀ g ∈ E, g ∈ J ↔ f g ∈ J' := by
  classical
  have hle : ∀ J ∈ ae6ConjIn E ae6ModelK, J ≤ E := by
    rintro _ ⟨x, hx, rfl⟩; exact conjSub_le_of_mem hx hKE
  have hfin : (ae6ConjIn E ae6ModelK).Finite :=
    ((Set.toFinite (E : Set AE6Om)).image fun g => conjSub g ae6ModelK).subset
      (by rintro _ ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩)
  haveI := hfin.to_subtype
  let Φ : ↥(ae6ConjIn E ae6ModelK) → ↥(ae6ConjIn E ae6ModelK) := fun J =>
    ⟨(hf.2.2.2.2 J J.2).choose, (hf.2.2.2.2 J J.2).choose_spec.1⟩
  have hΦ : Function.Injective Φ := by
    intro J₁ J₂ he
    have h1 := (hf.2.2.2.2 J₁ J₁.2).choose_spec.2
    have h2 := (hf.2.2.2.2 J₂ J₂.2).choose_spec.2
    have he' : (hf.2.2.2.2 J₁ J₁.2).choose = (hf.2.2.2.2 J₂ J₂.2).choose := congrArg Subtype.val he
    rw [he'] at h1
    apply Subtype.ext
    ext g
    constructor
    · intro hg; have hgE := hle _ J₁.2 hg; exact (h2 g hgE).2 ((h1 g hgE).1 hg)
    · intro hg; have hgE := hle _ J₂.2 hg; exact (h1 g hgE).2 ((h2 g hgE).1 hg)
  obtain ⟨J, hJ⟩ := (Finite.injective_iff_surjective.1 hΦ) ⟨J', hJ'⟩
  refine ⟨J, J.2, fun g hg => ?_⟩
  have := (hf.2.2.2.2 J J.2).choose_spec.2 g hg
  rwa [show (hf.2.2.2.2 J J.2).choose = J' from congrArg Subtype.val hJ] at this

theorem ae6TriAut.quat_iff (hf : ae6TriAut E f) (hKE : ae6ModelK ≤ E) {x : AE6Om} (hx : x ∈ E) :
    (∃ J ∈ ae6ConjIn E ae6ModelK, x ∈ J ∧ orderOf x = 4) ↔
      ∃ J ∈ ae6ConjIn E ae6ModelK, f x ∈ J ∧ orderOf (f x) = 4 := by
  rw [hf.orderOf_eq hx]
  constructor
  · rintro ⟨J, hJ, hxJ, ho⟩
    obtain ⟨J', hJ', hJJ⟩ := hf.2.2.2.2 J hJ
    exact ⟨J', hJ', (hJJ x hx).1 hxJ, ho⟩
  · rintro ⟨J', hJ', hxJ, ho⟩
    obtain ⟨J, hJ, hJJ⟩ := hf.member_surj hKE hJ'
    exact ⟨J, hJ, (hJJ x hx).2 hxJ, ho⟩

end TriAut

theorem ae6TriAut_id (E : Subgroup AE6Om) : ae6TriAut E id :=
  ⟨fun _ hg => hg, fun _ _ _ _ => rfl, fun _ _ _ _ he => he, fun _ _ => Iff.rfl,
    fun J hJ => ⟨J, hJ, fun _ _ => Iff.rfl⟩⟩

@[expose] noncomputable def ae6TriR (h : AE6TriFin) (e : Fin 3) : Fin 6 → AE6Om → AE6Om :=
  ![id, ae6TriD h (ae6EdgeK e), ae6TriD h (ae6EdgeL e), ae6TriD h (ae6EdgeL e) ∘ ae6TriD h (ae6EdgeK e),
    ae6TriD h (ae6EdgeK e) ∘ ae6TriD h (ae6EdgeL e),
    ae6TriD h (ae6EdgeK e) ∘ ae6TriD h (ae6EdgeL e) ∘ ae6TriD h (ae6EdgeK e)]

theorem ae6EdgeLetters_comm (k l : Fin 3) : ae6EdgeLetters k l = ae6EdgeLetters l k := by
  ext i; simp [ae6EdgeLetters, and_comm]

theorem ae6EdgeK_ne_L : ∀ e : Fin 3, ae6EdgeK e ≠ ae6EdgeL e := by decide

theorem ae6TriGen_letters : ∀ e : Fin 3, ∀ i : Fin 6, ∀ a ∈ ae6TriGen e i,
    a ∈ ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e) := by decide

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem R_triAut (e : Fin 3) (j : Fin 6) : ae6TriAut (ae6ModelE (ae6EdgeK e) (ae6EdgeL e)) (ae6TriR h e j) := by
  have hK : ae6TriAut (ae6ModelE (ae6EdgeK e) (ae6EdgeL e)) (ae6TriD h (ae6EdgeK e)) :=
    (h.D_good _).triAut inf_le_left
  have hL : ae6TriAut (ae6ModelE (ae6EdgeK e) (ae6EdgeL e)) (ae6TriD h (ae6EdgeL e)) :=
    (h.D_good _).triAut inf_le_right
  fin_cases j
  exacts [ae6TriAut_id _, hK, hL, hK.comp hL, hL.comp hK, (hK.comp hL).comp hK]

theorem DeltaW_letters {k l : Fin 3} (hlk : l ≠ k) {w : List (Fin 8)} (hw : ∀ i ∈ w, i ∈ ae6EdgeLetters k l) :
    ∀ j ∈ ae6DeltaW k w, j ∈ ae6EdgeLetters k l := by
  intro j hj
  obtain ⟨i, hi, hj⟩ := List.mem_flatMap.1 hj
  exact ((h.hDl k).2.2.2.1 i (ae6EdgeLetters_sub (hw i hi)) j hj).2.2 l hlk (hw i hi)

theorem edge_word {k l : Fin 3} (hkl : k ≠ l) {w : List (Fin 8)} (hw : ∀ i ∈ w, i ∈ ae6EdgeLetters k l) :
    (ae6TriD h k (ae6Word w) = ae6Word (ae6DeltaW k w) ∧ ∀ i ∈ ae6DeltaW k w, i ∈ ae6EdgeLetters k l) ∧
      (ae6TriD h l (ae6Word w) = ae6Word (ae6DeltaW l w) ∧ ∀ i ∈ ae6DeltaW l w, i ∈ ae6EdgeLetters k l) := by
  have hw' : ∀ i ∈ w, i ∈ ae6EdgeLetters l k := fun i hi => ae6EdgeLetters_comm k l ▸ hw i hi
  refine ⟨⟨h.D_word k fun i hi => ae6EdgeLetters_sub (hw i hi), h.DeltaW_letters (Ne.symm hkl) hw⟩,
    ⟨h.D_word l fun i hi => ae6EdgeLetters_sub (hw' i hi), fun i hi => ?_⟩⟩
  rw [ae6EdgeLetters_comm]
  exact h.DeltaW_letters hkl hw' i hi

theorem R_word (e : Fin 3) (j : Fin 6) {w : List (Fin 8)}
    (hw : ∀ i ∈ w, i ∈ ae6EdgeLetters (ae6EdgeK e) (ae6EdgeL e)) :
    ae6TriR h e j (ae6Word w) = ae6Word (ae6TriRep e j w) := by
  have hkl := ae6EdgeK_ne_L e
  obtain ⟨⟨hK1, hK2⟩, ⟨hL1, hL2⟩⟩ := h.edge_word hkl hw
  fin_cases j
  · rfl
  · exact hK1
  · exact hL1
  · show ae6TriD h _ (ae6TriD h _ (ae6Word w)) = ae6Word (ae6DeltaW _ (ae6DeltaW _ w))
    rw [hK1, (h.edge_word hkl hK2).2.1]
  · show ae6TriD h _ (ae6TriD h _ (ae6Word w)) = ae6Word (ae6DeltaW _ (ae6DeltaW _ w))
    rw [hL1, (h.edge_word hkl hL2).1.1]
  · show ae6TriD h _ (ae6TriD h _ (ae6TriD h _ (ae6Word w))) =
      ae6Word (ae6DeltaW _ (ae6DeltaW _ (ae6DeltaW _ w)))
    obtain ⟨⟨-, -⟩, ⟨hL1', hL2'⟩⟩ := h.edge_word hkl hK2
    rw [hK1, hL1', (h.edge_word hkl hL2').1.1]

theorem stepA (e : Fin 3) {f : AE6Om → AE6Om} (hf : ae6TriAut (ae6ModelE (ae6EdgeK e) (ae6EdgeL e)) f) :
    ∃ m ∈ ae6ModelM, ∃ j : Fin 6, ∀ g ∈ ae6ModelE (ae6EdgeK e) (ae6EdgeL e),
      f g = m * ae6TriR h e j g * m⁻¹ := by
  obtain ⟨hgen, hq, hTA⟩ := h.hA e
  have hKE : ae6ModelK ≤ ae6ModelE (ae6EdgeK e) (ae6EdgeL e) := h.K_le_M.trans (ae6ModelM_le_E _ _)
  have htE : ∀ i, ae6Word (ae6TriGen e i) ∈ ae6ModelE (ae6EdgeK e) (ae6EdgeL e) := fun i =>
    hgen ▸ Subgroup.subset_closure (Set.mem_range_self i)
  have hprodE : ∀ u : List (Fin 6), (u.map fun i => ae6Word (ae6TriGen e i)).prod ∈
      ae6ModelE (ae6EdgeK e) (ae6EdgeL e) := fun u =>
    Subgroup.list_prod_mem _ (by simp only [List.mem_map]; rintro _ ⟨i, -, rfl⟩; exact htE i)
  have hprod : ∀ u : List (Fin 6), (u.map fun i => f (ae6Word (ae6TriGen e i))).prod =
      f (u.map fun i => ae6Word (ae6TriGen e i)).prod := by
    intro u
    rw [hf.map_prod _ (by simp only [List.mem_map]; rintro _ ⟨i, -, rfl⟩; exact htE i), List.map_map]
    rfl
  obtain ⟨m, hm, j, hj⟩ := hTA (fun i => f (ae6Word (ae6TriGen e i)))
    (fun i => (hf.quat_iff hKE (htE i)).1 (hq i))
    (fun u _ => by
      rw [hprod u]
      exact ⟨hf.orderOf_eq (hprodE u), (hf.2.2.2.1 _ (hprodE u)).symm, (hf.quat_iff hKE (hprodE u)).symm⟩)
  refine ⟨m, hm, j, ?_⟩
  have hR := h.R_triAut e j
  intro g hg
  rw [← hgen] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [hj i, h.R_word e j (ae6TriGen_letters e i)]
  | one => rw [hf.map_one, hR.map_one]; group
  | mul x y hx hy ihx ihy =>
    have hx' := hgen ▸ hx
    have hy' := hgen ▸ hy
    rw [hf.2.1 x hx' y hy', ihx, ihy, hR.2.1 x hx' y hy']; group
  | inv x hx ihx =>
    have hx' := hgen ▸ hx
    rw [hf.map_inv hx', ihx, hR.map_inv hx']; group

end AE6TriFin

@[expose] def ae6TriSig (f : AE6Om → AE6Om) (σ : Fin 4 → Fin 4) : Prop :=
  ∀ g ∈ ae6ModelM, ∀ x, g ∈ ae6TriQ x ↔ f g ∈ ae6TriQ (σ x)

@[expose] def ae6TriRQ (e : Fin 3) : Fin 6 → Fin 4 → Fin 4 :=
  ![id, ae6DeltaQ (ae6EdgeK e), ae6DeltaQ (ae6EdgeL e), ae6DeltaQ (ae6EdgeL e) ∘ ae6DeltaQ (ae6EdgeK e),
    ae6DeltaQ (ae6EdgeK e) ∘ ae6DeltaQ (ae6EdgeL e),
    ae6DeltaQ (ae6EdgeK e) ∘ ae6DeltaQ (ae6EdgeL e) ∘ ae6DeltaQ (ae6EdgeK e)]

theorem ae6TriSig.comp {f f' : AE6Om → AE6Om} {σ σ' : Fin 4 → Fin 4} (hf : ae6TriSig f σ)
    (hf' : ae6TriSig f' σ') (hM : ∀ g ∈ ae6ModelM, f g ∈ ae6ModelM) : ae6TriSig (f' ∘ f) (σ' ∘ σ) :=
  fun g hg x => (hf g hg x).trans (hf' _ (hM g hg) (σ x))

theorem ae6TriSig.congr {f f' : AE6Om → AE6Om} {σ : Fin 4 → Fin 4} (hf : ae6TriSig f σ)
    (he : ∀ g ∈ ae6ModelM, f g = f' g) : ae6TriSig f' σ :=
  fun g hg x => he g hg ▸ hf g hg x

theorem ae6TriSig_id : ae6TriSig id id := fun _ _ _ => Iff.rfl

theorem ae6DeltaQ_invol : ∀ (k : Fin 3) (x : Fin 4), ae6DeltaQ k (ae6DeltaQ k x) = x := by decide

theorem ae6MLetters_sub : ∀ i ∈ ae6MLetters, ∀ k : Fin 3, i ∈ ae6VertexLetters k := by decide

theorem ae6TriQWords_letters (x : Fin 4) (k : Fin 3) (h : AE6TriFin) :
    ∀ w ∈ ae6TriQWords x, ∀ i ∈ w, i ∈ ae6VertexLetters k := fun w hw i hi =>
  ae6MLetters_sub i ((h.hQw x w hw).1 i hi) k

section Certified

theorem ae6_gen_mul_self (i : Fin 8) : A6.curtisGen i * A6.curtisGen i = 1 := by
  have h := A6.curtisRelations_curtisGen.rank_one
  rw [← pow_two]
  have hi : (List.ofFn A6.curtisGen).getD i 1 = A6.curtisGen i := by
    fin_cases i <;> rfl
  rw [← hi]
  obtain ⟨j, hj, he | he⟩ : ∃ j < 4, (i : ℕ) = 2 * j ∨ (i : ℕ) = 2 * j + 1 := ⟨i / 2, by omega, by omega⟩
  · rw [he]; exact (h j hj).1
  · rw [he]; exact (h j hj).2.1

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem Q_normal (x : Fin 4) {m : AE6Om} (hm : m ∈ ae6ModelM) (g : AE6Om) :
    g ∈ ae6TriQ x ↔ m * g * m⁻¹ ∈ ae6TriQ x := by
  rw [h.hMl, ae6LetterSub] at hm
  revert g
  induction hm using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨i, hi, rfl⟩ := hc
    have hcc := ae6_gen_mul_self i
    have hinv : (A6.curtisGen i)⁻¹ = A6.curtisGen i := inv_eq_of_mul_eq_one_right hcc
    have hfwd : ∀ g ∈ ae6TriQ x, A6.curtisGen i * g * A6.curtisGen i ∈ ae6TriQ x := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        exact (h.hQw x w hw).2 i (Finset.mem_coe.1 hi)
      | one => rw [mul_one, hcc]; exact one_mem _
      | mul a b _ _ iha ihb =>
        have e : A6.curtisGen i * (a * b) * A6.curtisGen i =
            (A6.curtisGen i * a * A6.curtisGen i) * (A6.curtisGen i * b * A6.curtisGen i) := by
          rw [show A6.curtisGen i * a * A6.curtisGen i * (A6.curtisGen i * b * A6.curtisGen i) =
            A6.curtisGen i * a * (A6.curtisGen i * A6.curtisGen i) * b * A6.curtisGen i by group, hcc]
          group
        rw [e]; exact mul_mem iha ihb
      | inv a _ iha =>
        have e : A6.curtisGen i * a⁻¹ * A6.curtisGen i = (A6.curtisGen i * a * A6.curtisGen i)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hinv]; group
        rw [e]; exact inv_mem iha
    intro g
    rw [hinv]
    refine ⟨hfwd g, fun hg => ?_⟩
    have e : g = A6.curtisGen i * (A6.curtisGen i * g * A6.curtisGen i) * A6.curtisGen i := by
      rw [show A6.curtisGen i * (A6.curtisGen i * g * A6.curtisGen i) * A6.curtisGen i =
        (A6.curtisGen i * A6.curtisGen i) * g * (A6.curtisGen i * A6.curtisGen i) by group, hcc]
      group
    rw [e]; exact hfwd _ hg
  | one => intro g; simp
  | mul a b _ _ iha ihb =>
    intro g
    have e : a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group
    rw [e, ihb g, iha (b * g * b⁻¹)]
  | inv a _ iha =>
    intro g
    rw [iha (a⁻¹ * g * a⁻¹⁻¹)]
    have e : a * (a⁻¹ * g * a⁻¹⁻¹) * a⁻¹ = g := by group
    rw [e]

theorem Q_le_M (x : Fin 4) : ae6TriQ x ≤ ae6ModelM := by
  rw [ae6TriQ, Subgroup.closure_le, h.hMl]
  rintro _ ⟨w, hw, rfl⟩
  exact ae6Word_mem fun i hi => Finset.mem_coe.2 ((h.hQw x w hw).1 i hi)

theorem D_Q_into (k : Fin 3) (x : Fin 4) : ∀ y ∈ ae6TriQ x, ae6TriD h k y ∈ ae6TriQ (ae6DeltaQ k x) := by
  refine ae6Amb_closure _ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩; exact ae6Word_vertex (ae6TriQWords_letters x k h w hw)
  · rintro _ ⟨w, hw, rfl⟩
    change ae6TriD h k _ ∈ _
    rw [h.D_word k (ae6TriQWords_letters x k h w hw)]
    exact h.hQδ k x w hw

theorem D_sig (k : Fin 3) : ae6TriSig (ae6TriD h k) (ae6DeltaQ k) := by
  intro g hg x
  have hQV : ∀ y, ae6TriQ y ≤ ae6ModelV k := fun y => (h.Q_le_M y).trans (ae6ModelM_le k)
  refine ae6Amb_iff _ (hQV x) (hQV _) (h.D_Q_into k x) ?_ (ae6ModelM_le k hg)
  have hinj : Function.Injective fun y : ↥(ae6TriQ (ae6DeltaQ k x)) =>
      (⟨ae6TriD h k y, by
        have := h.D_Q_into k (ae6DeltaQ k x) y y.2
        rwa [ae6DeltaQ_invol] at this⟩ : ↥(ae6TriQ x)) := by
    intro y y' he
    exact Subtype.ext (ae6Amb_injOn _ (hQV _ y.2) (hQV _ y'.2) (congrArg Subtype.val he))
  exact Nat.card_le_card_of_injective _ hinj

theorem D_maps_M (k : Fin 3) {g : AE6Om} (hg : g ∈ ae6ModelM) : ae6TriD h k g ∈ ae6ModelM :=
  ((h.D_good k).M_iff (ae6ModelM_le k hg)).1 hg

theorem R_sig (e : Fin 3) (j : Fin 6) : ae6TriSig (ae6TriR h e j) (ae6TriRQ e j) := by
  have hK := h.D_sig (ae6EdgeK e)
  have hL := h.D_sig (ae6EdgeL e)
  have mK : ∀ g ∈ ae6ModelM, ae6TriD h (ae6EdgeK e) g ∈ ae6ModelM := fun g hg => h.D_maps_M _ hg
  have mL : ∀ g ∈ ae6ModelM, ae6TriD h (ae6EdgeL e) g ∈ ae6ModelM := fun g hg => h.D_maps_M _ hg
  fin_cases j
  exacts [ae6TriSig_id, hK, hL, hK.comp hL mK, hL.comp hK mL,
    (hK.comp hL mK).comp hK fun g hg => mL _ (mK g hg)]

theorem sig_conj {f : AE6Om → AE6Om} {σ : Fin 4 → Fin 4} (hf : ae6TriSig f σ)
    (hM : ∀ g ∈ ae6ModelM, f g ∈ ae6ModelM) {m : AE6Om} (hm : m ∈ ae6ModelM) :
    ae6TriSig (fun g => m * f g * m⁻¹) σ :=
  fun g hg x => (hf g hg x).trans (h.Q_normal (σ x) hm _)

theorem sig_eq {f f' : AE6Om → AE6Om} {σ σ' : Fin 4 → Fin 4} (hfe : ∀ g ∈ ae6ModelM, f g = f' g)
    (hs : ∀ y ∈ ae6ModelM, ∃ g ∈ ae6ModelM, f g = y) (hσ : ae6TriSig f σ) (hσ' : ae6TriSig f' σ') : σ = σ' := by
  funext x
  by_contra hne
  apply h.hQd _ _ hne
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, rfl⟩ := hs y (h.Q_le_M _ hy)
    rw [hfe g hg]
    exact (hσ' g hg x).1 ((hσ g hg x).2 hy)
  · intro hy
    obtain ⟨g, hg, rfl⟩ := hs y (h.Q_le_M _ hy)
    rw [hfe g hg] at hy
    exact (hσ g hg x).1 ((hσ' g hg x).2 hy)

end AE6TriFin

end Certified

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem inn_eq {b n : AE6Om} (hb : b ∈ ae6ModelM) (hn : n ∈ ae6ModelM)
    (he : ∀ g ∈ ae6ModelM, b * g * b⁻¹ = n * g * n⁻¹) : b = n := by
  have := h.hZ (n⁻¹ * b) (mul_mem (inv_mem hn) hb) fun i hi => by
    have hc : A6.curtisGen i ∈ ae6ModelM := h.hMl ▸ gen_mem_letterSub (Finset.mem_coe.2 hi)
    have e1 := he _ hc
    calc n⁻¹ * b * A6.curtisGen i = n⁻¹ * (b * A6.curtisGen i * b⁻¹) * b := by group
      _ = n⁻¹ * (n * A6.curtisGen i * n⁻¹) * b := by rw [e1]
      _ = A6.curtisGen i * (n⁻¹ * b) := by group
  exact (inv_mul_eq_one.1 this).symm

end AE6TriFin

theorem ae6Tri_F1 : ∀ j1 j2 j3 : Fin 6, ae6TriRQ 1 j2 = ae6TriRQ 2 j3 ∘ ae6TriRQ 0 j1 → j1.val < 4 := by decide

theorem ae6Tri_F2 : ∀ (j2 j : Fin 6) (ε : Bool),
    ae6TriRQ 1 j2 = ae6TriRQ 2 j ∘ (if ε then ae6DeltaQ 0 else id) → j = 0 ∨ j = 2 := by decide

theorem ae6Tri_F3 : ∀ j2 j : Fin 6, ae6TriRQ 1 j2 = ae6TriRQ 1 j → j2 = j := by decide

@[expose] def ae6TriTuple (β₀ : MulAut ↥(ae6ModelV 0)) (β₁ : MulAut ↥(ae6ModelV 1))
    (β₂ : MulAut ↥(ae6ModelV 2)) : ∀ k : Fin 3, MulAut ↥(ae6ModelV k)
  | ⟨0, _⟩ => β₀
  | ⟨1, _⟩ => β₁
  | ⟨2, _⟩ => β₂
  | ⟨n + 3, hn⟩ => absurd hn (by omega)

namespace AE6TriFin

variable (h : AE6TriFin)
include h

theorem P_false (k : Fin 3) : ae6TriP h k false = 1 := rfl

theorem R01_split (j : Fin 6) (hj : j.val < 4) :
    ∃ η ε : Bool, ∀ g, ae6TriR h 0 j g = ae6Amb (ae6TriP h 1 η) (ae6Amb (ae6TriP h 0 ε) g) := by
  fin_cases j
  · exact ⟨false, false, fun g => by rw [h.P_false, h.P_false, ae6Amb_one_aut, ae6Amb_one_aut]; rfl⟩
  · exact ⟨false, true, fun g => by rw [h.P_false, ae6Amb_one_aut]; rfl⟩
  · exact ⟨true, false, fun g => by rw [h.P_false, ae6Amb_one_aut]; rfl⟩
  · exact ⟨true, true, fun g => rfl⟩
  · exact absurd hj (by decide)
  · exact absurd hj (by decide)

theorem R12_split (j : Fin 6) (hj : j = 0 ∨ j = 2) : ∃ ζ : Bool, ∀ g, ae6TriR h 2 j g = ae6Amb (ae6TriP h 2 ζ) g := by
  rcases hj with rfl | rfl
  · exact ⟨false, fun g => by rw [h.P_false, ae6Amb_one_aut]; rfl⟩
  · exact ⟨true, fun g => rfl⟩

theorem R02_join (ζ ε : Bool) :
    ∃ j : Fin 6, ∀ g, ae6Amb (ae6TriP h 2 ζ) (ae6Amb (ae6TriP h 0 ε) g) = ae6TriR h 1 j g := by
  cases ζ <;> cases ε
  · exact ⟨0, fun g => by rw [h.P_false, h.P_false, ae6Amb_one_aut, ae6Amb_one_aut]; rfl⟩
  · exact ⟨1, fun g => by rw [h.P_false, ae6Amb_one_aut]; rfl⟩
  · exact ⟨2, fun g => by rw [h.P_false, ae6Amb_one_aut]; rfl⟩
  · exact ⟨3, fun g => rfl⟩

section Certified

theorem P_sig (k : Fin 3) (b : Bool) :
    ae6TriSig (ae6Amb (ae6TriP h k b)) (if b then ae6DeltaQ k else id) := by
  cases b
  · exact ae6TriSig_id.congr fun g _ => (ae6Amb_one_aut g).symm
  · exact h.D_sig k

theorem stepA_sig (e : Fin 3) {f : AE6Om → AE6Om} {m : AE6Om} (hm : m ∈ ae6ModelM) {j : Fin 6}
    (H : ∀ g ∈ ae6ModelE (ae6EdgeK e) (ae6EdgeL e), f g = m * ae6TriR h e j g * m⁻¹) :
    ae6TriSig f (ae6TriRQ e j) :=
  (h.sig_conj (h.R_sig e j) (fun g hg => ((h.R_triAut e j).2.2.2.1 g (ae6ModelM_le_E _ _ hg)).1 hg) hm).congr
    fun g hg => (H g (ae6ModelM_le_E _ _ hg)).symm

end Certified

end AE6TriFin

theorem ae6ModelTri_of_fin (h : AE6TriFin) : AE6ModelTri := by
  intro θ₀₁ θ₀₂ θ₁₂ h01 h02 h12 hcomp
  have t01 := h01.triAut
  have t02 := h02.triAut
  have t12 := h12.triAut
  have hM : ∀ g ∈ ae6ModelM, ae6Amb θ₀₂ g = ae6Amb θ₁₂ (ae6Amb θ₀₁ g) := by
    intro g hg
    have g01 : g ∈ ae6ModelE 0 1 := ae6ModelM_le_E 0 1 hg
    have g02 : g ∈ ae6ModelE 0 2 := ae6ModelM_le_E 0 2 hg
    have g12 : ae6Amb θ₀₁ g ∈ ae6ModelE 1 2 := ae6ModelM_le_E 1 2 ((t01.2.2.2.1 g g01).1 hg)
    rw [ae6Amb_of_mem θ₀₂ g02, ae6Amb_of_mem θ₁₂ g12]
    exact hcomp ⟨g, g01⟩ ⟨g, g02⟩ ⟨_, g12⟩ hg rfl (ae6Amb_of_mem θ₀₁ g01)
  have s02surj : ∀ y ∈ ae6ModelM, ∃ g ∈ ae6ModelM, ae6Amb θ₀₂ g = y := fun y hy =>
    t02.surj_M (ae6ModelM_le_E 0 2) hy
  obtain ⟨a, ha, j1, H1⟩ := h.stepA 0 t01
  obtain ⟨b, hb, j2, H2⟩ := h.stepA 1 t02
  obtain ⟨c, hc, j3, H3⟩ := h.stepA 2 t12
  have hj1 : j1.val < 4 := ae6Tri_F1 j1 j2 j3 (h.sig_eq hM s02surj (h.stepA_sig 1 hb H2)
    ((h.stepA_sig 0 ha H1).comp (h.stepA_sig 2 hc H3) fun g hg =>
      (t01.2.2.2.1 g (ae6ModelM_le_E 0 1 hg)).1 hg))
  obtain ⟨η, ε, hR1⟩ := h.R01_split j1 hj1
  set γ1 : MulAut ↥(ae6ModelV 1) :=
    MulAut.conj (⟨a, ae6ModelM_le 1 ha⟩ : ↥(ae6ModelV 1)) * ae6TriP h 1 η with hγ1def
  have gγ1 : ae6TriGood 1 γ1 := (ae6TriGood_conj 1 ha).mul (h.P_good 1 η)
  have gP0 := h.P_good 0 ε
  have hγ1 : ∀ x ∈ ae6ModelV 1, ae6Amb γ1 x = a * ae6Amb (ae6TriP h 1 η) x * a⁻¹ := fun x hx => by
    rw [hγ1def, ae6Amb_mul_aut _ _ hx, ae6Amb_conj _ (ae6Amb_mem _ hx)]
  have hP01 : ∀ g ∈ ae6ModelE 0 1, ae6Amb (ae6TriP h 0 ε) g ∈ ae6ModelV 1 := fun g hg =>
    (gP0.1 1 g (Subgroup.mem_inf.1 hg).1).1 (Subgroup.mem_inf.1 hg).2
  have H1' : ∀ g ∈ ae6ModelE 0 1, ae6Amb θ₀₁ g = ae6Amb γ1 (ae6Amb (ae6TriP h 0 ε) g) := fun g hg => by
    rw [H1 g hg, hR1, hγ1 _ (hP01 g hg)]
  have tf : ae6TriAut (ae6ModelE 1 2) (ae6Amb θ₁₂ ∘ ae6Amb γ1) :=
    (gγ1.triAut (a := 1) (b := 2) inf_le_left).comp t12
  obtain ⟨n, hn, j, H⟩ := h.stepA 2 tf
  have hMf : ∀ g ∈ ae6ModelM, ae6Amb θ₀₂ g = ae6Amb θ₁₂ (ae6Amb γ1 (ae6Amb (ae6TriP h 0 ε) g)) :=
    fun g hg => by rw [hM g hg, H1' g (ae6ModelM_le_E 0 1 hg)]
  have hj : j = 0 ∨ j = 2 := ae6Tri_F2 j2 j ε (h.sig_eq hMf s02surj (h.stepA_sig 1 hb H2)
    ((h.P_sig 0 ε).comp (h.stepA_sig 2 hn H) fun g hg => (gP0.M_iff (ae6ModelM_le 0 hg)).1 hg))
  obtain ⟨ζ, hR2⟩ := h.R12_split j hj
  set γ2 : MulAut ↥(ae6ModelV 2) :=
    MulAut.conj (⟨n, ae6ModelM_le 2 hn⟩ : ↥(ae6ModelV 2)) * ae6TriP h 2 ζ with hγ2def
  have gγ2 : ae6TriGood 2 γ2 := (ae6TriGood_conj 2 hn).mul (h.P_good 2 ζ)
  have hγ2 : ∀ x ∈ ae6ModelV 2, ae6Amb γ2 x = n * ae6Amb (ae6TriP h 2 ζ) x * n⁻¹ := fun x hx => by
    rw [hγ2def, ae6Amb_mul_aut _ _ hx, ae6Amb_conj _ (ae6Amb_mem _ hx)]
  have H' : ∀ g ∈ ae6ModelE 1 2, ae6Amb θ₁₂ (ae6Amb γ1 g) = ae6Amb γ2 g := fun g hg => by
    rw [hγ2 g (Subgroup.mem_inf.1 hg).2, ← hR2]; exact H g hg
  have hP02 : ∀ g ∈ ae6ModelE 0 2, ae6Amb (ae6TriP h 0 ε) g ∈ ae6ModelV 2 := fun g hg =>
    (gP0.1 2 g (Subgroup.mem_inf.1 hg).1).1 (Subgroup.mem_inf.1 hg).2
  obtain ⟨j'', hR3⟩ := h.R02_join ζ ε
  have hF : ∀ g ∈ ae6ModelE 0 2, ae6Amb γ2 (ae6Amb (ae6TriP h 0 ε) g) = n * ae6TriR h 1 j'' g * n⁻¹ :=
    fun g hg => by rw [hγ2 _ (hP02 g hg), hR3]
  have hMF : ∀ g ∈ ae6ModelM, ae6Amb θ₀₂ g = n * ae6TriR h 1 j'' g * n⁻¹ := fun g hg => by
    have hPM : ae6Amb (ae6TriP h 0 ε) g ∈ ae6ModelM := (gP0.M_iff (ae6ModelM_le 0 hg)).1 hg
    rw [hM g hg, H1' g (ae6ModelM_le_E 0 1 hg), H' _ (ae6ModelM_le_E 1 2 hPM), hF g (ae6ModelM_le_E 0 2 hg)]
  have hjj : j2 = j'' := ae6Tri_F3 j2 j'' (h.sig_eq hMF s02surj (h.stepA_sig 1 hb H2)
    (h.stepA_sig 1 (f := fun g => n * ae6TriR h 1 j'' g * n⁻¹) hn fun g _ => rfl))
  have hbn : b = n := h.inn_eq hb hn fun y hy => by
    obtain ⟨g, hg, rfl⟩ := (h.R_triAut 1 j2).surj_M (ae6ModelM_le_E _ _) hy
    rw [← H2 g (ae6ModelM_le_E _ _ hg), hMF g hg, hjj]
  have H02 : ∀ g ∈ ae6ModelE 0 2, ae6Amb θ₀₂ g = ae6Amb γ2 (ae6Amb (ae6TriP h 0 ε) g) := fun g hg => by
    rw [H2 g hg, hF g hg, hjj, hbn]
  refine ⟨ae6TriTuple (ae6TriP h 0 ε) γ1⁻¹ γ2⁻¹, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · intro l g; rw [← ae6Amb_coe]; exact gP0.1 l g g.2
    · intro l g; rw [← ae6Amb_coe]; exact gγ1.inv_V l g.2
    · intro l g; rw [← ae6Amb_coe]; exact gγ2.inv_V l g.2
  · intro g x y hx hy
    show ((γ1⁻¹ y : ↥(ae6ModelV 1)) : AE6Om) = ((ae6TriP h 0 ε x : ↥(ae6ModelV 0)) : AE6Om)
    rw [← ae6Amb_coe γ1⁻¹ y, ← ae6Amb_coe (ae6TriP h 0 ε) x, hy, ← ae6Amb_coe θ₀₁ g, H1' _ g.2, hx]
    exact ae6Amb_inv_aut γ1 (hP01 _ g.2)
  · intro g x y hx hy
    show ((γ2⁻¹ y : ↥(ae6ModelV 2)) : AE6Om) = ((ae6TriP h 0 ε x : ↥(ae6ModelV 0)) : AE6Om)
    rw [← ae6Amb_coe γ2⁻¹ y, ← ae6Amb_coe (ae6TriP h 0 ε) x, hy, ← ae6Amb_coe θ₀₂ g, H02 _ g.2, hx]
    exact ae6Amb_inv_aut γ2 (hP02 _ g.2)
  · intro g x y hx hy
    show ((γ2⁻¹ y : ↥(ae6ModelV 2)) : AE6Om) = ((γ1⁻¹ x : ↥(ae6ModelV 1)) : AE6Om)
    have hxV2 : (x : AE6Om) ∈ ae6ModelV 2 := hx ▸ (Subgroup.mem_inf.1 g.2).2
    have hz2 : ae6Amb γ1⁻¹ (x : AE6Om) ∈ ae6ModelV 2 := (gγ1.inv_V 2 x.2).1 hxV2
    have hzE : ae6Amb γ1⁻¹ (x : AE6Om) ∈ ae6ModelE 1 2 := Subgroup.mem_inf.2 ⟨ae6Amb_mem _ x.2, hz2⟩
    rw [← ae6Amb_coe γ2⁻¹ y, ← ae6Amb_coe γ1⁻¹ x, hy, ← ae6Amb_coe θ₁₂ g, ← hx]
    calc ae6Amb γ2⁻¹ (ae6Amb θ₁₂ ↑x) = ae6Amb γ2⁻¹ (ae6Amb θ₁₂ (ae6Amb γ1 (ae6Amb γ1⁻¹ ↑x))) := by
          rw [ae6Amb_aut_inv γ1 x.2]
      _ = ae6Amb γ2⁻¹ (ae6Amb γ2 (ae6Amb γ1⁻¹ ↑x)) := by rw [H' _ hzE]
      _ = ae6Amb γ1⁻¹ ↑x := ae6Amb_inv_aut γ2 hz2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
