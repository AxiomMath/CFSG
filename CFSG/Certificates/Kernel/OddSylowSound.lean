module

public import Certificates.Data.Kernel.OddSylowTwin
public import CFSG.GroupTheory.SylowOddClasses
public import CFSG.Sporadic.Schreier.Enumeration
import Mathlib.Data.List.GetD

public section

namespace CFSG.KS.OddSyl

open CFSG.KD.OddSyl CFSG.Sporadic.Schreier CFSG.GroupTheory.SylowOddClasses

variable {n : ℕ}

@[expose] def Img (n : ℕ) (σ : Equiv.Perm (Fin n)) (l : List ℕ) : Prop :=
  l.length = n ∧ ∀ i : Fin n, l.getD i 0 = σ i

theorem img_one : Img n 1 (List.range n) :=
  ⟨List.length_range, fun i => by simp [List.getD_eq_getElem?_getD, i.isLt]⟩

theorem img_mul {f g : Equiv.Perm (Fin n)} {lf lg : List ℕ} (hf : Img n f lf) (hg : Img n g lg) :
    Img n (f * g) (ilMul lf lg) := by
  refine ⟨by simp [ilMul, hg.1], fun i => ?_⟩
  have hi : (i : ℕ) < lg.length := hg.1 ▸ i.isLt
  have e1 := hg.2 i
  have e2 := hf.2 (g i)
  rw [List.getD_eq_getElem _ _ hi] at e1
  unfold ilMul
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, e1, e2]
  rfl

theorem img_eq {f g : Equiv.Perm (Fin n)} {l : List ℕ} (hf : Img n f l) (hg : Img n g l) :
    f = g :=
  Equiv.ext fun i => Fin.ext ((hf.2 i).symm.trans (hg.2 i))

theorem img_unique {f : Equiv.Perm (Fin n)} {l l' : List ℕ} (h : Img n f l) (h' : Img n f l') :
    l = l' := by
  refine List.ext_getElem (h.1.trans h'.1.symm) fun i h1 h2 => ?_
  have a := h.2 ⟨i, h.1 ▸ h1⟩
  have b := h'.2 ⟨i, h.1 ▸ h1⟩
  rw [List.getD_eq_getElem _ _ h1] at a
  rw [List.getD_eq_getElem _ _ h2] at b
  exact a.trans b.symm

theorem img_pow {σ : Equiv.Perm (Fin n)} {l : List ℕ} (h : Img n σ l) :
    ∀ k, Img n (σ ^ k) (ilPow n l k)
  | 0 => img_one
  | k + 1 => by
    rw [pow_succ']
    exact img_mul h (img_pow h k)

theorem img_evW {S : List (Equiv.Perm (Fin n))} {L Li : List (List ℕ)}
    (hL : ∀ j, Img n (S.getD j 1) (L.getD j (List.range n)))
    (hLi : ∀ j, Img n (S.getD j 1)⁻¹ (Li.getD j (List.range n))) :
    ∀ w, Img n (evalCodes S w) (evW n L Li w)
  | [] => img_one
  | z :: w => by
    unfold evalCodes evW
    refine img_mul ?_ (img_evW hL hLi w)
    rcases z with (_ | k) | k
    · exact hLi 0
    · simpa [ilLetter] using hL k
    · have e : (-Int.negSucc k).toNat - 1 = k := by omega
      simpa [ilLetter, e, Int.negSucc_lt_zero] using hLi k

theorem fixL_eq {σ : Equiv.Perm (Fin n)} {l : List ℕ} (h : Img n σ l) : fixL l = fixCard σ := by
  unfold fixL fixCard
  rw [h.1, List.countP_eq_length_filter]
  have e : (Finset.univ.filter fun x : Fin n => σ x = x).map Fin.valEmbedding =
      (Finset.range n).filter fun i => (l.getD i 0 == i) = true := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.isLt, by rw [h.2 x, hx]⟩
    · rintro ⟨hi, e⟩
      refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
      rw [← h.2 ⟨i, hi⟩]
      exact e
  rw [← Finset.card_map Fin.valEmbedding, e]
  rfl

theorem nodupB_sound : ∀ {l : List (List ℕ)}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    unfold nodupB at h
    rw [Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodupB_sound h.2⟩
    have hc : xs.contains x = true := by simpa using hm
    rw [hc] at h
    exact absurd h.1 (by decide)

@[expose] def sylElts (S : List (Equiv.Perm (Fin n))) (W : List (List ℤ × List ℤ × ℕ)) :
    List (Equiv.Perm (Fin n)) :=
  ([] :: W.map (·.1)).map (evalCodes S)

theorem mem_sylElts {S : List (Equiv.Perm (Fin n))} {W : List (List ℤ × List ℤ × ℕ)}
    {x : Equiv.Perm (Fin n)} : x ∈ sylElts S W ↔ x = 1 ∨ ∃ t ∈ W, x = evalCodes S t.1 := by
  simp only [sylElts, List.map_cons, List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨w, ⟨t, ht, rfl⟩, rfl⟩)
    · exact Or.inl (h.trans rfl)
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl (h.trans rfl)
    · exact Or.inr ⟨t.1, ⟨t, ht, rfl⟩, rfl⟩

theorem sylOK_sound {S : List (Equiv.Perm (Fin n))} {L Li : List (List ℕ)}
    (hL : ∀ j, Img n (S.getD j 1) (L.getD j (List.range n)))
    (hLi : ∀ j, Img n (S.getD j 1)⁻¹ (Li.getD j (List.range n)))
    {reps : List (List ℤ)} {p card : ℕ} {W : List (List ℤ × List ℤ × ℕ)}
    (h : sylOK n L Li reps p card W = true) :
    (1 : Equiv.Perm (Fin n)) ∈ sylElts S W ∧
      (∀ x ∈ sylElts S W, ∀ y ∈ sylElts S W, x * y ∈ sylElts S W) ∧ (sylElts S W).Nodup ∧
      (sylElts S W).length = card ∧ (∀ x ∈ sylElts S W, x ^ p = 1) ∧
      ∀ t ∈ W, ∃ r ∈ reps.map (evalCodes S), evalCodes S t.1 * evalCodes S t.2.1 =
        evalCodes S t.2.1 * r := by
  have hI := img_evW hL hLi
  unfold sylOK subOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hnd, hlen⟩, hcl⟩, hexp⟩, hw⟩ := h
  set ws : List (List ℤ) := [] :: W.map (·.1)
  have hV : sylElts S W = ws.map (evalCodes S) := rfl
  have hiff : ∀ a b, evW n L Li a = evW n L Li b ↔ evalCodes S a = evalCodes S b := fun a b =>
    ⟨fun e => img_eq (hI a) (e ▸ hI b), fun e => img_unique (hI a) (e ▸ hI b)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_sylElts.2 (Or.inl rfl)
  · intro x hx y hy
    rw [hV, List.mem_map] at hx hy ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hc := hcl _ (List.mem_map_of_mem ha) _ (List.mem_map_of_mem hb)
    obtain ⟨c, hc, he⟩ := List.mem_map.1 (by simpa using hc)
    exact ⟨c, hc, img_eq (he ▸ hI c) (img_mul (hI a) (hI b))⟩
  · have h1 := nodupB_sound hnd
    rw [hV]
    unfold List.Nodup at h1 ⊢
    rw [List.pairwise_map] at h1 ⊢
    exact h1.imp fun {a b} hab e => hab ((hiff a b).2 e)
  · rw [hV, List.length_map]
    simpa using hlen
  · intro x hx
    rw [hV, List.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have e := hexp _ (List.mem_map_of_mem ha)
    exact img_eq (e ▸ img_pow (hI a) p) img_one
  · intro t ht
    have h2 := hw t ht
    simp only [witOK, Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h2
    refine ⟨evalCodes S (reps.getD t.2.2 []), ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ h2.1]
      exact List.mem_map_of_mem (List.getElem_mem _)
    · exact img_eq (img_mul (hI _) (hI _)) (h2.2 ▸ img_mul (hI _) (hI _))

theorem repOK_sound {S : List (Equiv.Perm (Fin n))} {L Li : List (List ℕ)}
    (hL : ∀ j, Img n (S.getD j 1) (L.getD j (List.range n)))
    (hLi : ∀ j, Img n (S.getD j 1)⁻¹ (Li.getD j (List.range n)))
    {w : List ℤ} {m f : ℕ} (hm : m.Prime) (h : repOK n L Li w m f = true) :
    orderOf (evalCodes S w) = m ∧ fixCard (evalCodes S w) = f := by
  have hI := img_evW hL hLi w
  unfold repOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨hp, hne⟩, hf⟩ := h
  have : Fact m.Prime := ⟨hm⟩
  refine ⟨orderOf_eq_prime (img_eq (hp ▸ img_pow hI m) img_one) fun e => hne ?_, ?_⟩
  · exact img_unique hI (e ▸ img_one)
  · rw [← fixL_eq hI, hf]

end CFSG.KS.OddSyl

end
