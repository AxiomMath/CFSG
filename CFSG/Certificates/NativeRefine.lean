module

public import CFSG.Certificates.NativeSetOrbit
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Certificates

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem perm_apply_inv_self {β : Type*} (σ : Equiv.Perm β) (x : β) : σ (σ⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem perm_inv_apply_self {β : Type*} (σ : Equiv.Perm β) (x : β) : σ⁻¹ (σ x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

section Refine

variable {n : ℕ} {nbr : Array (List ℕ)}

@[expose] def NbrInv (nbr : Array (List ℕ)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ x y : Fin n, (y : ℕ) ∈ nbr[(x : ℕ)]! ↔ ((σ y : Fin n) : ℕ) ∈ nbr[((σ x : Fin n) : ℕ)]!

@[expose] def ColInv (n : ℕ) (c : Array ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ v : Fin n, c[((σ v : Fin n) : ℕ)]! = c[(v : ℕ)]!

@[expose] def permNat (σ : Equiv.Perm (Fin n)) (y : ℕ) : ℕ :=
  if h : y < n then ((σ ⟨y, h⟩ : Fin n) : ℕ) else y

theorem permNat_lt (σ : Equiv.Perm (Fin n)) {y : ℕ} (h : y < n) :
    permNat σ y = ((σ ⟨y, h⟩ : Fin n) : ℕ) := by
  simp [permNat, h]

theorem sorted_mergeSort_le (l : List ℕ) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  exact this.imp fun h => by simpa using h

theorem mergeSort_eq_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    (l₁.mergeSort fun a b => decide (a ≤ b)) = l₂.mergeSort fun a b => decide (a ≤ b) :=
  List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (sorted_mergeSort_le l₁) (sorted_mergeSort_le l₂)
    ((List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm))

section Facts

variable {σ : Equiv.Perm (Fin n)} (hnbr : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!)
  (hσ : NbrInv nbr σ)
include hnbr hσ

theorem nbr_perm (v : Fin n) :
    (nbr[((σ v : Fin n) : ℕ)]!).Perm ((nbr[(v : ℕ)]!).map (permNat σ)) := by
  have hl := hnbr v
  have hl' := hnbr (σ v)
  rw [List.perm_ext_iff_of_nodup hl'.sorted.nodup]
  · intro z
    rw [List.mem_map]
    constructor
    · intro hz
      have hzn := hl'.lt z hz
      refine ⟨((σ⁻¹ ⟨z, hzn⟩ : Fin n) : ℕ), ?_, ?_⟩
      · rw [hσ v (σ⁻¹ ⟨z, hzn⟩), perm_apply_inv_self]
        exact hz
      · rw [permNat_lt σ (σ⁻¹ ⟨z, hzn⟩).2, Fin.eta, perm_apply_inv_self]
    · rintro ⟨y, hy, rfl⟩
      have hyn := hl.lt y hy
      rw [permNat_lt σ hyn]
      exact (hσ v ⟨y, hyn⟩).1 hy
  · refine hl.sorted.nodup.map_on fun a ha b hb hab => ?_
    rw [permNat_lt σ (hl.lt a ha), permNat_lt σ (hl.lt b hb)] at hab
    exact congrArg Fin.val (σ.injective (Fin.ext hab))

theorem nbrColours_inv {c : Array ℕ} (hc : ColInv n c σ) (v : Fin n) :
    nbrColours nbr c ((σ v : Fin n) : ℕ) = nbrColours nbr c (v : ℕ) := by
  unfold nbrColours
  apply mergeSort_eq_of_perm
  refine ((nbr_perm hnbr hσ v).map _).trans ?_
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun y hy => ?_)
  have hyn := (hnbr v).lt y hy
  simp only [Function.comp_apply]
  rw [permNat_lt σ hyn]
  exact hc ⟨y, hyn⟩

theorem refineStep_inv {c : Array ℕ} (hc : ColInv n c σ) : ColInv n (refineStep n nbr c) σ := by
  intro v
  rw [refineStep, getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  rw [hc v, nbrColours_inv hnbr hσ hc v]

theorem refineIter_inv {c : Array ℕ} (hc : ColInv n c σ) :
    ∀ k, ColInv n (refineIter n nbr c k) σ
  | 0 => hc
  | k + 1 => refineStep_inv hnbr hσ (refineIter_inv hc k)

end Facts

theorem individualize_inv {b : List ℕ} {s : ℕ} {σ : Equiv.Perm (Fin n)}
    (hfix : ∀ v : Fin n, (v : ℕ) ∈ b.take s → σ v = v) : ColInv n (individualize n b s) σ := by
  intro v
  rw [individualize, getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  by_cases hv : (v : ℕ) ∈ b.take s
  · rw [hfix v hv]
  · have hσv : ((σ v : Fin n) : ℕ) ∉ b.take s := fun h => by
      have := hfix (σ v) h
      rw [σ.injective this] at h
      exact hv h
    rw [List.idxOf?_eq_none_iff.2 hv, List.idxOf?_eq_none_iff.2 hσv]

end Refine

theorem strictIncr_pairwise : ∀ {l : List ℕ}, strictIncr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := strictIncr_pairwise h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

section Adj

variable {n : ℕ}

structure AdjFacts (n : ℕ) (gens : Array (Array ℕ)) (nbr : Array (List ℕ)) (root : List ℕ) :
    Prop where
  root : nbr[0]! = root
  point : ∀ x : Fin n, PointList n nbr[(x : ℕ)]!
  root_symm : ∀ y ∈ nbr[0]!, 0 ∈ nbr[y]!
  img : ∀ k < gens.size, ∀ x < n, nbr[(gens[k]!)[x]!]! = imgSorted gens[k]! nbr[x]!

theorem adjFacts_of_adjOK {gens : Array (Array ℕ)} {nbr : Array (List ℕ)} {root : List ℕ}
    (h : adjOK n gens nbr root = true) : AdjFacts n gens nbr root := by
  simp only [adjOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, h0⟩, hpt⟩, hsym⟩, himg⟩ := h
  refine ⟨beq_iff_eq.1 h0, fun x => ?_, fun y hy => ?_, fun k hk x hx => ?_⟩
  · have := allLt_spec hpt x.2
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1, strictIncr_pairwise this.2⟩
  · have := List.all_eq_true.1 hsym y hy
    simpa using this
  · have := allLt_spec (allLt_spec himg hk) hx
    simpa using this

namespace AdjFacts

variable {gens : Array (Array ℕ)} {nbr : Array (List ℕ)} {root : List ℕ}
  {Gs : ℕ → Equiv.Perm (Fin n)}

theorem inv_gen (hA : AdjFacts n gens nbr root) (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k))
    {k : ℕ} (hk : k < gens.size) : NbrInv nbr (Gs k) := by
  intro x y
  rw [← (hrep k hk) x, hA.img k hk x x.2, mem_imgSorted]
  constructor
  · intro hy
    exact ⟨y, hy, (hrep k hk) y⟩
  · rintro ⟨p, hp, hpy⟩
    have hpn := (hA.point x).lt p hp
    rw [(hrep k hk).apply hpn] at hpy
    have : (⟨p, hpn⟩ : Fin n) = y := (Gs k).injective (Fin.ext hpy)
    rw [← this]
    exact hp

theorem nbrInv_mul {σ τ : Equiv.Perm (Fin n)} (hσ : NbrInv nbr σ) (hτ : NbrInv nbr τ) :
    NbrInv nbr (σ * τ) := fun x y => (hτ x y).trans (hσ (τ x) (τ y))

theorem nbrInv_inv {σ : Equiv.Perm (Fin n)} (hσ : NbrInv nbr σ) : NbrInv nbr σ⁻¹ := by
  intro x y
  rw [hσ (σ⁻¹ x) (σ⁻¹ y), perm_apply_inv_self, perm_apply_inv_self]

theorem inv_of_mem_closure (hA : AdjFacts n gens nbr root)
    (hrep : ∀ k < gens.size, Rep n gens[k]! (Gs k)) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ Subgroup.closure {g | ∃ k < gens.size, Gs k = g}) : NbrInv nbr σ := by
  induction hσ using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := hg
    exact hA.inv_gen hrep hk
  | one => exact fun x y => Iff.rfl
  | mul g h _ _ hg hh => exact nbrInv_mul hg hh
  | inv g _ hg => exact nbrInv_inv hg

end AdjFacts

end Adj

section StabChain

variable {G α : Type*} [Group G] [MulAction G α]

@[expose] def stabChain (b : ℕ → α) : ℕ → Subgroup G
  | 0 => ⊤
  | s + 1 => stabChain b s ⊓ MulAction.stabilizer G (b s)

theorem mem_stabChain {b : ℕ → α} : ∀ {s : ℕ} {g : G}, g ∈ stabChain b s ↔ ∀ j < s, g • b j = b j
  | 0, g => by simp [stabChain]
  | s + 1, g => by
    rw [stabChain, Subgroup.mem_inf, mem_stabChain, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨h, hs⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h j hj
      · exact hs
    · intro h
      exact ⟨fun j hj => h j (by omega), h s (by omega)⟩

theorem card_inf_eq_card_subgroupOf' (H K : Subgroup G) :
    Nat.card (H ⊓ K : Subgroup G) = Nat.card (K.subgroupOf H) := by
  rw [← Subgroup.inf_subgroupOf_left]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

theorem card_stabChain_succ [Finite G] (b : ℕ → α) (s : ℕ) :
    Nat.card (stabChain (G := G) b s) =
      (MulAction.orbit (stabChain (G := G) b s) (b s)).ncard *
        Nat.card (stabChain (G := G) b (s + 1)) := by
  have h := (MulAction.stabilizer (stabChain (G := G) b s) (b s)).card_mul_index
  rw [MulAction.index_stabilizer, ← MulAction.stabilizer_subgroupOf,
    ← card_inf_eq_card_subgroupOf'] at h
  rw [← h, mul_comm]
  rfl

theorem card_le_prod_of_stabChain [Finite G] (b : ℕ → α) (bound : ℕ → ℕ) (m : ℕ)
    (horb : ∀ s < m, (MulAction.orbit (stabChain (G := G) b s) (b s)).ncard ≤ bound s)
    (htriv : stabChain (G := G) b m = ⊥) :
    Nat.card G ≤ ∏ s ∈ Finset.range m, bound s := by
  have key : ∀ s ≤ m, Nat.card G ≤
      (∏ t ∈ Finset.range s, bound t) * Nat.card (stabChain (G := G) b s) := by
    intro s
    induction s with
    | zero =>
      intro _
      simp [stabChain]
    | succ s ih =>
      intro hs
      refine (ih (by omega)).trans ?_
      rw [card_stabChain_succ b s, Finset.prod_range_succ, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (horb s (by omega)))
  have := key m le_rfl
  rwa [htriv, Subgroup.card_bot, mul_one] at this

end StabChain

end CFSG.Certificates
