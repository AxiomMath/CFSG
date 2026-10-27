module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertBAE8
public import Certificates.Certificate517532

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

namespace CertB

open CFSG.ClassicalInvolution.Generic CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.EvenSmallLie.OmegaEight Certificates.AE6CertB Certificates.AE6Model
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Twin
open scoped Pointwise

@[expose] def stabSub (mB : Array Bool) : Subgroup (Equiv.Perm (Fin 360)) where
  carrier := {p | ∀ x : Fin 360, mB[(p x).val]! = mB[x.val]!}
  mul_mem' {a b} ha hb x := by
    rw [Equiv.Perm.mul_apply, ha (b x), hb x]
  one_mem' _ := rfl
  inv_mem' {a} ha x := by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from a.apply_symm_apply x] at h
    exact h.symm

@[expose] noncomputable def stabB (l : Fin 3) : Subgroup AE6Om :=
  (stabSub (triBArr l)).comap omegaT.subtype

theorem triBArr_get (l : Fin 3) (x : Fin 360) : (triBArr l)[x.val]! = (triB l).contains x.val := by
  rw [triBArr, getElem!_pos _ x.val (by simp)]
  simp

theorem mem_stabSub_triB {l : Fin 3} {p : Equiv.Perm (Fin 360)} :
    p ∈ stabSub (triBArr l) ↔ ∀ x : Fin 360, (p x).val ∈ triB l ↔ x.val ∈ triB l := by
  have hc : ∀ a : ℕ, (triB l).contains a = true ↔ a ∈ triB l := fun a => by simp
  change (∀ x : Fin 360, _ = _) ↔ _
  refine forall_congr' fun x => ?_
  rw [triBArr_get, triBArr_get, Bool.eq_iff_iff, hc, hc]

theorem stabB_eq (l : Fin 3) : stabB l = Certificates.ae6TriStab l := by
  ext g
  change (g : Equiv.Perm (Fin 360)) ∈ stabSub (triBArr l) ↔
    (g : Equiv.Perm (Fin 360)) ∈ MulAction.stabilizer (Equiv.Perm (Fin 360))
      ({x : Fin 360 | x.val ∈ triB l} : Set (Fin 360))
  rw [mem_stabSub_triB, MulAction.mem_stabilizer_iff]
  generalize (g : Equiv.Perm (Fin 360)) = p
  constructor
  · intro h
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [Set.mem_setOf_eq, Equiv.Perm.smul_def]
    rw [← h (p⁻¹ y)]
    simp
  · intro h x
    have hx : (p x ∈ p • ({x : Fin 360 | x.val ∈ triB l} : Set (Fin 360))) ↔ x.val ∈ triB l := by
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp [Equiv.Perm.smul_def]
    rw [h] at hx
    exact hx

section Transport

@[expose] def ConjLetters (x : Equiv.Perm (Fin 360)) (σ : Fin 8 → Fin 8) : Prop :=
  ∀ i, x * (A6.curtisGen i : Equiv.Perm (Fin 360)) * x⁻¹ = A6.curtisGen (σ i)

theorem ConjLetters.one : ConjLetters 1 id := fun i => by simp

theorem ConjLetters.of_eq {x : Equiv.Perm (Fin 360)} {σ τ : Fin 8 → Fin 8} (h : ConjLetters x σ)
    (e : ∀ i, σ i = τ i) : ConjLetters x τ := fun i => by rw [h i, e i]

theorem ConjLetters.comp {x y : Equiv.Perm (Fin 360)} {σ τ : Fin 8 → Fin 8} (hx : ConjLetters x σ)
    (hy : ConjLetters y τ) : ConjLetters (y * x) (τ ∘ σ) := by
  intro i
  have e : y * x * (A6.curtisGen i : Equiv.Perm (Fin 360)) * (y * x)⁻¹ =
      y * (x * (A6.curtisGen i : Equiv.Perm (Fin 360)) * x⁻¹) * y⁻¹ := by group
  simp only [e, hx i, hy (σ i), Function.comp_apply]

theorem ConjLetters.inv {x : Equiv.Perm (Fin 360)} {σ τ : Fin 8 → Fin 8} (hx : ConjLetters x σ)
    (h : ∀ j, σ (τ j) = j) : ConjLetters x⁻¹ τ := by
  intro j
  have e := hx (τ j)
  rw [h j] at e
  rw [inv_inv, ← e]
  group

theorem ConjLetters.mem {x : Equiv.Perm (Fin 360)} {σ : Fin 8 → Fin 8} (hx : ConjLetters x σ)
    {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) : x * g * x⁻¹ ∈ omegaT := by
  rw [omegaT_eq] at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    have e := hx ⟨i, hi⟩
    change x * ((A6.curtisGen ⟨i, hi⟩ : AE6Om) : Equiv.Perm (Fin 360)) * x⁻¹ ∈ _
    rw [e]
    exact Subgroup.subset_closure ⟨_, (σ ⟨i, hi⟩).2, rfl⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

@[expose] noncomputable def conjAut {x : Equiv.Perm (Fin 360)} {σ τ : Fin 8 → Fin 8}
    (hx : ConjLetters x σ) (hy : ConjLetters x⁻¹ τ) : AE6Om ≃* AE6Om where
  toFun g := ⟨x * g * x⁻¹, hx.mem g.2⟩
  invFun g := ⟨x⁻¹ * g * x, by simpa using hy.mem g.2⟩
  left_inv g := Subtype.ext (by
    change x⁻¹ * (x * (g : Equiv.Perm (Fin 360)) * x⁻¹) * x = g
    group)
  right_inv g := Subtype.ext (by
    change x * (x⁻¹ * (g : Equiv.Perm (Fin 360)) * x) * x⁻¹ = g
    group)
  map_mul' a b := Subtype.ext (by
    change x * ((a : Equiv.Perm (Fin 360)) * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
    group)

variable {x : Equiv.Perm (Fin 360)} {σ τ : Fin 8 → Fin 8} (hx : ConjLetters x σ)
  (hy : ConjLetters x⁻¹ τ)

theorem conjAut_gen (i : Fin 8) : conjAut hx hy (A6.curtisGen i) = A6.curtisGen (σ i) :=
  Subtype.ext (hx i)

theorem conjAut_word (w : List (Fin 8)) : conjAut hx hy (ae6Word w) = ae6Word (w.map σ) := by
  unfold ae6Word
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => conjAut_gen hx hy i

theorem map_letterSub_conj (A : Finset (Fin 8)) :
    (ae6LetterSub ↑A).map (conjAut hx hy).toMonoidHom = ae6LetterSub ↑(A.image σ) := by
  rw [ae6LetterSub, MonoidHom.map_closure, ae6LetterSub, Set.image_image, Finset.coe_image,
    Set.image_image]
  congr 1
  exact Set.image_congr fun i _ => conjAut_gen hx hy i

theorem card_map_conj (H : Subgroup AE6Om) :
    Nat.card (H.map (conjAut hx hy).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (conjAut hx hy).injective

end Transport

section Conj

theorem conj_diag (c : Fin 2) : ∃ x, ConjLetters x (ae6Diag c) ∧ ConjLetters x⁻¹ (ae6Diag c) := by
  obtain ⟨x, hx⟩ := Certificates.certificate517532.1 c
  have hx' : ConjLetters x (ae6Diag c) := hx
  have hinv : ∀ c : Fin 2, ∀ j, ae6Diag c (ae6Diag c j) = j := by decide
  exact ⟨x, hx', hx'.inv (hinv c)⟩

theorem conj_vertex (k : Fin 3) :
    ∃ x, ConjLetters x (ae6VertexSwap k) ∧ ConjLetters x⁻¹ (ae6VertexSwap k) := by
  obtain ⟨x0, h0, h0'⟩ := conj_diag 0
  obtain ⟨x1, h1, h1'⟩ := conj_diag 1
  fin_cases k
  · refine ⟨1, ConjLetters.one.of_eq (by decide), ?_⟩
    rw [inv_one]
    exact ConjLetters.one.of_eq (by decide)
  · exact ⟨x1, h1.of_eq (by decide), h1'.of_eq (by decide)⟩
  · exact ⟨x0, h0.of_eq (by decide), h0'.of_eq (by decide)⟩

theorem conj_edge (e : Fin 3) :
    ∃ x τ, ConjLetters x (ae6EdgeMap e) ∧ ConjLetters x⁻¹ τ := by
  obtain ⟨x0, h0, h0'⟩ := conj_diag 0
  obtain ⟨x1, h1, h1'⟩ := conj_diag 1
  fin_cases e
  · refine ⟨1, id, ConjLetters.one.of_eq (by decide), ?_⟩
    rw [inv_one]
    exact ConjLetters.one
  · refine ⟨x1 * x0, ae6Diag 0 ∘ ae6Diag 1, (h0.comp h1).of_eq (by decide), ?_⟩
    rw [mul_inv_rev]
    exact h1'.comp h0'
  · exact ⟨x0, ae6Diag 0, h0.of_eq (by decide), h0'⟩

end Conj

section Orders

theorem vertexLetters_image (k : Fin 3) :
    (ae6VertexLetters 0).image (ae6VertexSwap k) = ae6VertexLetters k := by
  revert k
  decide

theorem edgeLetters_image (e : Fin 3) :
    (ae6EdgeLetters 0 1).image (ae6EdgeMap e) = ae6EdgeLetters (triEK e) (triEL2 e) := by
  revert e
  decide

theorem map_V (k : Fin 3) {x : Equiv.Perm (Fin 360)} (hx : ConjLetters x (ae6VertexSwap k))
    (hy : ConjLetters x⁻¹ (ae6VertexSwap k)) :
    (ae6ModelV 0).map (conjAut hx hy).toMonoidHom = ae6ModelV k := by
  rw [ae6ModelV_eq, ae6ModelV_eq, map_letterSub_conj, vertexLetters_image]

theorem card_V
    (k : Fin 3) : Nat.card (ae6ModelV k) = 1290240 := by
  obtain ⟨x, hx, hy⟩ := conj_vertex k
  rw [← map_V k hx hy, card_map_conj, card_ae6ModelV0]

theorem card_edgeLetters_ge (e : Fin 3) :
    86016 ≤ Nat.card (ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e))) := by
  obtain ⟨x, τ, hx, hy⟩ := conj_edge e
  rw [← edgeLetters_image, ← map_letterSub_conj hx hy, card_map_conj]
  exact Certificates.certificate517532.2.2.2.1

theorem card_mLetters : Nat.card (ae6LetterSub ↑ae6MLetters) = 12288 :=
  Certificates.certificate517532.2.1

end Orders

section Stab

theorem V_le_stabB (l : Fin 3) : ae6ModelV l ≤ stabB l := by
  rw [stabB_eq]
  exact Certificates.certificate517532.2.2.2.2.1 l

theorem card_V_inf_stab_le
    (e : Fin 3) :
    Nat.card ↥(ae6ModelV (triEK e) ⊓ stabB (triEL2 e)) ≤ 86016 := by
  have h := Certificates.certificate517532.2.2.2.2.2.1 e
  rw [← stabB_eq] at h
  have hV := card_V (triEK e)
  change 15 * Nat.card ↥(ae6ModelV (triEK e) ⊓ stabB (triEL2 e)) ≤
    Nat.card (ae6ModelV (triEK e)) at h
  rw [hV] at h
  omega

end Stab

section TM

theorem edgeLetters_le_V (e : Fin 3) : ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) ≤
    ae6ModelV (triEK e) ⊓ ae6ModelV (triEL2 e) := by
  have h1 : ∀ e : Fin 3, ae6EdgeLetters (triEK e) (triEL2 e) ⊆ ae6VertexLetters (triEK e) := by
    decide
  have h2 : ∀ e : Fin 3, ae6EdgeLetters (triEK e) (triEL2 e) ⊆ ae6VertexLetters (triEL2 e) := by
    decide
  rw [ae6ModelV_eq, ae6ModelV_eq]
  exact le_inf (ae6LetterSub_mono (Finset.coe_subset.mpr (h1 e)))
    (ae6LetterSub_mono (Finset.coe_subset.mpr (h2 e)))

theorem card_edgeLetters (e : Fin 3) :
    Nat.card (ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e))) = 86016 := by
  have h1 : Nat.card ↥(ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e))) ≤
      Nat.card ↥(ae6ModelV (triEK e) ⊓ stabB (triEL2 e)) :=
    Subgroup.card_le_of_le ((edgeLetters_le_V e).trans (inf_le_inf_left _ (V_le_stabB _)))
  have h2 := card_V_inf_stab_le e
  have h3 := card_edgeLetters_ge e
  omega

theorem card_edge_inf_stab_le (e : Fin 3) :
    Nat.card ↥(ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) ⊓ stabB (triEM e)) ≤ 12288 := by
  have h := Certificates.certificate517532.2.2.2.2.2.2.1 e
  rw [← stabB_eq] at h
  change 7 * Nat.card ↥(ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) ⊓ stabB (triEM e)) ≤
    Nat.card (ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e))) at h
  rw [card_edgeLetters] at h
  omega

theorem edge_eq (e : Fin 3) : ae6ModelV (triEK e) ⊓ ae6ModelV (triEL2 e) =
    ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) := by
  refine (Subgroup.eq_of_le_of_card_ge (edgeLetters_le_V e) ?_).symm
  rw [card_edgeLetters]
  exact (Subgroup.card_le_of_le (inf_le_inf_left _ (V_le_stabB _))).trans (card_V_inf_stab_le e)

theorem tri_TM_edges (k l : Fin 3) (hkl : k ≠ l) :
    ae6ModelE k l = ae6LetterSub ↑(ae6EdgeLetters k l) := by
  have hsymm : ∀ k l : Fin 3, ae6EdgeLetters k l = ae6EdgeLetters l k := by decide
  rw [ae6ModelE]
  fin_cases k <;> fin_cases l
  · exact absurd rfl hkl
  · exact edge_eq 0
  · exact edge_eq 1
  · rw [inf_comm, hsymm]
    exact edge_eq 0
  · exact absurd rfl hkl
  · exact edge_eq 2
  · rw [inf_comm, hsymm]
    exact edge_eq 1
  · rw [inf_comm, hsymm]
    exact edge_eq 2
  · exact absurd rfl hkl

theorem M_le_V (k : Fin 3) : ae6ModelM ≤ ae6ModelV k := by
  fin_cases k
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right

theorem mLetters_le_M : ae6LetterSub ↑ae6MLetters ≤ ae6ModelM := by
  have h : ∀ k : Fin 3, ae6MLetters ⊆ ae6VertexLetters k := by decide
  refine le_inf (le_inf ?_ ?_) ?_ <;> rw [ae6ModelV_eq] <;>
    exact ae6LetterSub_mono (Finset.coe_subset.mpr (h _))

theorem M_le_edge_stab (e : Fin 3) :
    ae6ModelM ≤ ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) ⊓ stabB (triEM e) := by
  rw [← edge_eq e]
  exact le_inf (le_inf (M_le_V _) (M_le_V _)) ((M_le_V _).trans (V_le_stabB _))

theorem card_M : Nat.card ae6ModelM = 12288 := by
  have h1 := Subgroup.card_le_of_le (M_le_edge_stab 0)
  have h2 := card_edge_inf_stab_le 0
  have h3 := Subgroup.card_le_of_le mLetters_le_M
  rw [card_mLetters] at h3
  omega

theorem tri_TM_M : ae6ModelM = ae6LetterSub ↑ae6MLetters :=
  (Subgroup.eq_of_le_of_card_ge mLetters_le_M (by rw [card_M, card_mLetters])).symm

theorem M_eq_edge_stab (e : Fin 3) :
    ae6ModelM = ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) ⊓ stabB (triEM e) :=
  Subgroup.eq_of_le_of_card_ge (M_le_edge_stab e) (by rw [card_M]; exact card_edge_inf_stab_le e)

theorem tri_TZ : ∀ m ∈ ae6ModelM,
    (∀ i ∈ ae6MLetters, m * A6.curtisGen i = A6.curtisGen i * m) → m = 1 := by
  rw [tri_TM_M]
  exact Certificates.certificate517532.2.2.2.2.2.2.2.1

end TM

section TD

theorem delta_swap : ∀ k : Fin 3, ∀ i ∈ ae6VertexLetters 0,
    ae6Delta k (ae6VertexSwap k i) = (ae6Delta 0 i).map (ae6VertexSwap k) := by
  decide

theorem swap_invol : ∀ k : Fin 3, ∀ i, ae6VertexSwap k (ae6VertexSwap k i) = i := by
  decide

theorem range_vertex {α : Type*} (k : Fin 3) (f : Fin 8 → α) :
    Set.range (fun i : ↥(ae6VertexLetters k) => f i) =
      Set.range (fun i : ↥(ae6VertexLetters 0) => f (ae6VertexSwap k i)) := by
  ext a
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    refine ⟨⟨ae6VertexSwap k j, ?_⟩, by simp only [swap_invol]⟩
    rw [← vertexLetters_image k, Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rwa [swap_invol]
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨⟨ae6VertexSwap k i, ?_⟩, rfl⟩
    rw [← vertexLetters_image k]
    exact Finset.mem_image_of_mem _ hi

theorem tri_TD_graph (k : Fin 3) :
    Nat.card (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
      (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta k i)))) = 1290240 := by
  obtain ⟨x, hx, hy⟩ := conj_vertex k
  have hmap : (Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters 0) =>
      (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta 0 i)))).map
        ((conjAut hx hy).toMonoidHom.prodMap (conjAut hx hy).toMonoidHom) =
      Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
        (A6.curtisGen (i : Fin 8), ae6Word (ae6Delta k i))) := by
    rw [MonoidHom.map_closure, range_vertex k (fun i => (A6.curtisGen i, ae6Word (ae6Delta k i))),
      ← Set.range_comp]
    refine congrArg Subgroup.closure (congrArg Set.range (funext fun i => ?_))
    change ((conjAut hx hy (A6.curtisGen (i : Fin 8)), conjAut hx hy (ae6Word (ae6Delta 0 i))) :
      AE6Om × AE6Om) = (A6.curtisGen (ae6VertexSwap k i), ae6Word (ae6Delta k (ae6VertexSwap k i)))
    rw [conjAut_gen, conjAut_word, delta_swap k i i.2]
  have hinj : Function.Injective
      ((conjAut hx hy).toMonoidHom.prodMap (conjAut hx hy).toMonoidHom) :=
    (conjAut hx hy).injective.prodMap (conjAut hx hy).injective
  rw [← hmap, Subgroup.card_map_of_injective hinj]
  exact Certificates.certificate517532.2.2.2.2.2.2.2.2.1

theorem tri_TD_letters (k : Fin 3) : ∀ i ∈ ae6VertexLetters k, ∀ j ∈ ae6Delta k i,
    j ∈ ae6VertexLetters k ∧ (i ∈ ae6MLetters → j ∈ ae6MLetters) ∧
      ∀ l : Fin 3, l ≠ k → i ∈ ae6EdgeLetters k l → j ∈ ae6EdgeLetters k l := by
  revert k
  decide +kernel

theorem tri_TD_gen (k : Fin 3) : Subgroup.closure (Set.range fun i : ↥(ae6VertexLetters k) =>
    ae6Word (ae6Delta k i)) = ae6ModelV k := by
  obtain ⟨x, hx, hy⟩ := conj_vertex k
  rw [← map_V k hx hy, ← Certificates.certificate517532.2.2.2.2.2.2.2.2.2.1,
    MonoidHom.map_closure, range_vertex k (fun i => ae6Word (ae6Delta k i)), ← Set.range_comp]
  refine congrArg Subgroup.closure (congrArg Set.range (funext fun i => ?_))
  change ae6Word (ae6Delta k (ae6VertexSwap k i)) = conjAut hx hy (ae6Word (ae6Delta 0 i))
  rw [conjAut_word, delta_swap k i i.2]

theorem tri_TD_K0 (k : Fin 3) (s : Fin 3) :
    ae6Word (ae6DeltaW k (ae6KWord s)) ∈ conjSub (ae6Word (ae6TriMemC k)) ae6ModelK :=
  Certificates.certificate517532.2.2.2.2.2.2.2.2.2.2.1 k s

end TD

section TQ

theorem tri_TQ_norm (x : Fin 4) : ∀ w ∈ ae6TriQWords x, (∀ i ∈ w, i ∈ ae6MLetters) ∧
    ∀ i ∈ ae6MLetters, A6.curtisGen i * ae6Word w * A6.curtisGen i ∈ ae6TriQ x := by
  have hl : ∀ x : Fin 4, ∀ w ∈ ae6TriQWords x, ∀ i ∈ w, i ∈ ae6MLetters := by decide +kernel
  intro w hw
  exact ⟨hl x w hw, Certificates.certificate517532.2.2.2.2.2.2.2.2.2.2.2.1 x w hw⟩

theorem tri_TQ_dist (x y : Fin 4) (hxy : x ≠ y) : ae6TriQ x ≠ ae6TriQ y :=
  Certificates.certificate517532.2.2.2.2.2.2.2.2.2.2.2.2.1 x y hxy

theorem tri_TQ_delta (k : Fin 3) (x : Fin 4) :
    ∀ w ∈ ae6TriQWords x, ae6Word (ae6DeltaW k w) ∈ ae6TriQ (ae6DeltaQ k x) :=
  Certificates.certificate517532.2.2.2.2.2.2.2.2.2.2.2.2.2.1 k x

end TQ

section Edges

theorem edge_model_eq (e : Fin 3) :
    ae6ModelE (ae6EdgeK e) (ae6EdgeL e) = ae6LetterSub ↑(ae6EdgeLetters (triEK e) (triEL2 e)) :=
  edge_eq e

theorem tri_TA_gen (e : Fin 3) : Subgroup.closure (Set.range fun i => ae6Word (ae6TriGen e i)) =
    ae6ModelE (ae6EdgeK e) (ae6EdgeL e) := by
  obtain ⟨x, τ, hx, hy⟩ := conj_edge e
  have h0 : ∀ e : Fin 3, ∀ i, ae6TriGen e i = (ae6TriGen 0 i).map (ae6EdgeMap e) := by
    decide
  rw [edge_model_eq, ← edgeLetters_image, ← map_letterSub_conj hx hy,
    ← Certificates.certificate517532.2.2.2.2.2.2.2.2.2.2.2.2.2.2, MonoidHom.map_closure,
    ← Set.range_comp]
  refine congrArg Subgroup.closure (congrArg Set.range (funext fun i => ?_))
  change ae6Word (ae6TriGen e i) = conjAut hx hy (ae6Word (ae6TriGen 0 i))
  rw [conjAut_word, h0]

end Edges

end CertB

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
