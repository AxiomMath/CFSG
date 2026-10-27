module

public import CFSG.LargeExtraspecial.SMod20RhoT46
public import Certificates.Certificate21267

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.SmithE CFSG.F4.Native CFSG.Fischer

theorem f4mul_lt_four (x y : ℕ) : f4mul x y < 4 := by
  dsimp only [f4mul]
  generalize x % 2 * (y % 2) + x / 2 * (y / 2) = a
  generalize x % 2 * (y / 2) + x / 2 * (y % 2) + x / 2 * (y / 2) = b
  omega

theorem wedgeCode_foldl_lt (W : ℕ × ℕ × ℕ) (n : ℕ) :
    (List.range n).foldl (fun acc k => acc + f4mul (wedgeScalar W) (pluck W k) * 4 ^ k) 0 <
      4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ]
    have h := f4mul_lt_four (wedgeScalar W) (pluck W n)
    have h4 : f4mul (wedgeScalar W) (pluck W n) * 4 ^ n ≤ 3 * 4 ^ n :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem wt_lt {i : ℕ} (_hi : i < 891) : wt i < 2 ^ 20 := by
  have h := wedgeCode_foldl_lt (wB i) 10
  have e : (4 : ℕ) ^ 10 = 2 ^ 20 := by norm_num
  rw [e] at h
  exact h

section Step


theorem planeImg_lt {k i : ℕ} (hk : k < 693) (hi : i < 891) : planeImg k i < 891 :=
  (tw_parts hk hi).1

theorem map_map_tvP (k : Fin 693) (X : Finset (Fin 693)) :
    (X.map (tvP k).toEmbedding).map (tvP k).toEmbedding = X := by
  rw [Finset.map_map]
  convert Finset.map_refl
  refine Function.Embedding.ext fun a => ?_
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Function.Embedding.refl_apply]
  rw [← Equiv.Perm.mul_apply, tvP_mul_self, Equiv.Perm.one_apply]

theorem planeImg_planeImg {k i : ℕ} (hk : k < 693) (hi : i < 891) :
    planeImg k (planeImg k i) = i := by
  refine planeSet_injective (planeImg_lt hk (planeImg_lt hk hi)) hi ?_
  rw [← map_planeSet_tvP hk (planeImg_lt hk hi), ← map_planeSet_tvP hk hi, map_map_tvP]

theorem planeSet_inter_planeImg {k a b : ℕ} (hk : k < 693) (ha : a < 891) (hb : b < 891) :
    planeSet (planeImg k a) ∩ planeSet (planeImg k b) =
      (planeSet a ∩ planeSet b).map (tvP ⟨k, hk⟩).toEmbedding := by
  rw [Finset.map_inter, map_planeSet_tvP hk ha, map_planeSet_tvP hk hb]

theorem opp_planeImg {k a b : ℕ} (hk : k < 693) (ha : a < 891) (hb : b < 891) :
    Opp (planeImg k a) (planeImg k b) ↔ Opp a b := by
  rw [Opp, Opp, ← map_planeSet_tvP hk ha, ← map_planeSet_tvP hk hb, Finset.disjoint_map]

theorem adjW_planeImg {k a b : ℕ} (hk : k < 693) (ha : a < 891)
    (hb : b < 891) : adjW (planeImg k a) (planeImg k b) = adjW a b := by
  have hm : meetCard (planeImg k a) (planeImg k b) = meetCard a b := by
    rw [meetCard_eq_card (planeImg_lt hk ha), meetCard_eq_card ha,
      planeSet_inter_planeImg hk ha hb, Finset.card_map]
  have hd : distB (planeImg k a) (planeImg k b) = distB a b := by
    simp only [distB, hm]
  rw [Bool.eq_iff_iff, adjW_iff (planeImg_lt hk ha) (planeImg_lt hk hb), adjW_iff ha hb, hd]

theorem tvEquiv_tvEquiv {k : ℕ} (hk : k < 693) (v : V) : tvEquiv k (tvEquiv k v) = v :=
  congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) (tvEquiv_mul_self hk)

theorem tvEquiv_comm_tvP {k : ℕ} (hk : k < 693) (p : Fin 693) (v : V) :
    tvEquiv k (tvEquiv p.val v) = tvEquiv (tvP ⟨k, hk⟩ p).val (tvEquiv k v) := by
  have e : (tvP ⟨k, hk⟩ p).val = ptImg k p.val := tvP_val _ _
  rw [e, ← tvEquiv_conj hk p.2, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    tvEquiv_tvEquiv hk]

end Step

@[expose] def QaAt (i : ℕ) : Prop :=
  ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
    (∀ s, ∃ p : Fin 693, p ∈ planeSet i ∧ ∃ k : Fin 891, ¬ Opp i k ∧
      v s = tvEquiv p (wtV k) + wtV k) ∧
    ∀ j : Fin 891, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW i j = true

@[expose] def CvAt (i : ℕ) : Prop :=
  ∀ v : V, (∀ p ∈ planeSet i, tvEquiv p.val v = v) ↔ v = 0 ∨ v = wtV i

section Transport


theorem qaAt_step {k i : ℕ} (hk : k < 693) (hi : i < 891)
    (h : QaAt i) : QaAt (planeImg k i) := by
  obtain ⟨v, hli, hv, hadj⟩ := h
  refine ⟨fun s => tvEquiv k (v s), hli.map' _ (tvEquiv k).ker, fun s => ?_, fun j => ?_⟩
  · obtain ⟨p, hp, l, hl, he⟩ := hv s
    refine ⟨tvP ⟨k, hk⟩ p, ?_, ⟨planeImg k l, planeImg_lt hk l.2⟩, ?_, ?_⟩
    · rw [← map_planeSet_tvP hk hi]
      exact Finset.mem_map_of_mem _ hp
    · rwa [opp_planeImg hk hi l.2]
    · simp only
      rw [he, map_add, tvEquiv_comm_tvP hk, tvEquiv_wtV hk l.2]
  · have hj' := planeImg_lt hk j.2
    have e : wtV j = tvEquiv k (wtV (planeImg k j)) := by
      rw [tvEquiv_wtV hk hj', planeImg_planeImg hk j.2]
    have hr : Set.range (fun s => tvEquiv k (v s)) = (tvEquiv k) '' Set.range v := by
      rw [← Set.range_comp]
      rfl
    have hs : Submodule.span (ZMod 2) ((tvEquiv k) '' Set.range v) =
        (Submodule.span (ZMod 2) (Set.range v)).map (tvEquiv k : V →ₗ[ZMod 2] V) :=
      (Submodule.map_span _ _).symm
    have ha : adjW (planeImg k i) j = adjW i (planeImg k j) := by
      conv_lhs => rw [← planeImg_planeImg hk j.2]
      exact adjW_planeImg hk hi hj'
    rw [e, hr, hs, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, ha]
    exact hadj ⟨planeImg k j, hj'⟩

theorem cvAt_step {k i : ℕ} (hk : k < 693) (hi : i < 891) (h : CvAt i) :
    CvAt (planeImg k i) := by
  have hmem : ∀ p ∈ planeSet i, tvP ⟨k, hk⟩ p ∈ planeSet (planeImg k i) := fun p hp => by
    rw [← map_planeSet_tvP hk hi]
    exact Finset.mem_map_of_mem _ hp
  intro v
  constructor
  · intro hv
    have hfix : ∀ p ∈ planeSet i, tvEquiv p.val (tvEquiv k v) = tvEquiv k v := fun p hp => by
      rw [← tvEquiv_tvEquiv hk (tvEquiv p.val _), tvEquiv_comm_tvP hk, tvEquiv_tvEquiv hk,
        hv _ (hmem p hp)]
    rcases (h _).1 hfix with h0 | h0
    · left
      rw [← tvEquiv_tvEquiv hk v, h0, map_zero]
    · right
      rw [← tvEquiv_tvEquiv hk v, h0, tvEquiv_wtV hk hi]
  · intro hv q hq
    rw [← map_planeSet_tvP hk hi] at hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hq
    have hw := (h (wtV i)).2 (Or.inr rfl)
    rcases hv with rfl | rfl
    · exact map_zero _
    · rw [Equiv.toEmbedding_apply, ← tvEquiv_wtV hk hi, ← tvEquiv_comm_tvP hk, hw p hp]

theorem of_planeWord {P : ℕ → Prop} (hstep : ∀ {k i}, k < 693 → i < 891 → P i → P (planeImg k i))
    {w : List ℕ} (hw : ∀ k ∈ w, k < 693) {i : ℕ} (hi : i < 891) (h : P (planeWordImg w i)) :
    P i := by
  induction w generalizing i with
  | nil => rwa [planeWordImg_nil] at h
  | cons k w ih =>
    have hk := hw k List.mem_cons_self
    rw [planeWordImg_cons] at h
    have h' := hstep hk (planeImg_lt hk hi)
      (ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) (planeImg_lt hk hi) h)
    rwa [planeImg_planeImg hk hi] at h'

end Transport

theorem qaAt_zero : QaAt 0 := by
  obtain ⟨v, hli, hv, hadj⟩ := Certificates.certificate21267.1
  refine ⟨v, hli, fun s => ?_, hadj⟩
  obtain ⟨p, hp, k, hk, he⟩ := hv s
  exact ⟨p, hp, k, hk, by rw [he, tvEquiv_apply p.2]⟩

theorem cvAt_zero : CvAt 0 := by
  intro v
  rw [← Certificates.certificate21267.2 v]
  refine forall₂_congr fun p _ => ?_
  rw [tvEquiv_apply p.2]

section Planes

variable
  {i : ℕ}

theorem exists_qaBasis (hi : i < 891) :
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 693, p ∈ planeSet i ∧ ∃ k : Fin 891, ¬ Opp i k ∧
        v s = tvEquiv p (wtV k) + wtV k) ∧
      ∀ j : Fin 891, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW i j = true := by
  obtain ⟨w, hw, h0⟩ := exists_planeWord hi
  exact of_planeWord (P := QaAt) (fun hk hi h => qaAt_step hk hi h) hw hi (by rw [h0]; exact qaAt_zero)

theorem fixed_iff (hi : i < 891) (v : V) :
    (∀ p ∈ planeSet i, tvEquiv p.val v = v) ↔ v = 0 ∨ v = wtV i := by
  obtain ⟨w, hw, h0⟩ := exists_planeWord hi
  exact of_planeWord (P := CvAt) (fun hk hi h => cvAt_step hk hi h) hw hi
    (by rw [h0]; exact cvAt_zero) v

theorem tvEquiv_wtV_self (hi : i < 891) {p : Fin 693} (hp : p ∈ planeSet i) :
    tvEquiv p.val (wtV i) = wtV i :=
  (fixed_iff hi (wtV i)).2 (Or.inr rfl) p hp

end Planes

end CFSG.LargeExtraspecial.SMod20
