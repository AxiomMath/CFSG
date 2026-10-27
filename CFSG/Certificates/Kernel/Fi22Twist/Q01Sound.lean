module

public import Certificates.Data.Kernel.Fi22Twist.Q01
public import CFSG.Certificates.Kernel.Fi22Twist.ConjSound

public section

namespace CFSG.KS.Fi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KS.E27Lie
open CFSG.HardMathSupport.Foote.E27 Subgroup

theorem tmF_succ_ne {L : ℕ → ℕ → ℕ} {pp pj : ℕ → ℕ} {f a : ℕ} (b : ℕ) (h : a ≠ 0) :
    tmF L pp pj (f + 1) a b = L (pj a) (tmF L pp pj f (pp a) b) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  change strictN (tmF L pp pj f (pp (a + 1)) b) (L (pj (a + 1))) = _
  generalize tmF L pp pj f (pp (a + 1)) b = y
  cases y <;> rfl

theorem cntR_eq (f : ℕ → Bool) (n : ℕ) :
    cntR f n = ((Finset.range n).filter fun y => f y = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.card_filter, Finset.sum_range_succ, ← Finset.card_filter, ← ih]
    change Bool.rec (motive := fun _ => ℕ) (cntR f n) (Nat.succ (cntR f n)) (f n) = _
    cases f n <;> simp

theorem q01C_spec {K T DF : ℕ → ℕ} {Gk j n i : ℕ} (h : q01C K T DF Gk j n i = true) :
    treeC q01M K (q01P T) (q01J T) (fun t => K (Nat.succ t)) (pidn 3510 12) 3 i = true ∧
    (∀ t < 3, leftC q01M K (q01L T) (fun t => K (Nat.succ t)) n t i = true) ∧
    sortC K (q01S T) n i = true ∧
    (qpE (T i) 3 = 1 → qpE (T i) 4 < 27 ∧ cjFull Gk (K i) (DF (27 * j + qpE (T i) 4)) = true) ∧
    (qpE (T i) 3 ≠ 1 → q01Cube T n i = true →
      cntR (fun y => bAnd(q01Cube T n y, Nat.beq (q01T T n i y) (q01T T n y i))) n < 27) := by
  unfold q01C at h
  rw [sB_eq] at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨h1, fun t ht => CFSG.KS.allN_spec h2 t ht, h3, fun hf => ?_, fun hf hc => ?_⟩
  · have e : Nat.beq (qpE (T i) 3) 1 = true := Eq.mpr Nat.beq_eq hf
    rw [bRec_eq, if_pos e, sB_eq] at h4
    obtain ⟨h5, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h4
    exact ⟨blt_of h5, h6⟩
  · have e : ¬ (Nat.beq (qpE (T i) 3) 1 = true) := by
      rw [Nat.beq_eq]
      exact hf
    rw [bRec_eq, if_neg e, bRec_eq, if_pos hc] at h4
    exact blt_of h4

variable {g : ℕ → Equiv.Perm (Fin 3510)} {pp pj : ℕ → ℕ} {lt : ℕ → ℕ → ℕ} {n m : ℕ}

theorem tmF_spec (hT : TabData g (parOf n pp pj) (ltOf m n lt) n m) :
    ∀ f a b, a ≤ f → a < n → b < n → tmF lt pp pj f a b < n ∧
      tabElt g (parOf n pp pj) a * tabElt g (parOf n pp pj) b =
        tabElt g (parOf n pp pj) (tmF lt pp pj f a b) := by
  intro f
  induction f with
  | zero =>
    intro a b ha _ hb
    obtain rfl : a = 0 := by omega
    refine ⟨hb, ?_⟩
    rw [tabElt_zero, one_mul]
    rfl
  | succ f ih =>
    intro a b ha han hb
    by_cases h0 : a = 0
    · subst h0
      refine ⟨hb, ?_⟩
      rw [tabElt_zero, one_mul]
      rfl
    · obtain ⟨hp0, hj0⟩ := hT.par_lt a (Nat.pos_of_ne_zero h0) han
      have hpar : (parOf n pp pj)[a]! = (pp a, pj a) := ofFnG (fun i => (pp i, pj i)) han
      have hp : pp a < a := by
        rw [hpar] at hp0
        exact hp0
      have hj : pj a < m := by
        rw [hpar] at hj0
        exact hj0
      obtain ⟨h1, h2⟩ := ih (pp a) b (by omega) (by omega) hb
      obtain ⟨h3, h4⟩ := hT.left (pj a) hj _ h1
      have hL : ((ltOf m n lt)[pj a]!)[tmF lt pp pj f (pp a) b]! =
          lt (pj a) (tmF lt pp pj f (pp a) b) := by
        rw [ofFnG (fun j => Array.ofFn (n := n) fun i => lt j i.val) hj,
          ofFnG (fun i => lt (pj a) i) h1]
      rw [hL] at h3 h4
      rw [tmF_succ_ne b h0]
      refine ⟨h3, ?_⟩
      rw [tabElt_succ g _ hp0, hpar, mul_assoc, h2]
      exact h4

theorem q01_sound {K T DF : ℕ → ℕ} {Gk j : ℕ} {h : Equiv.Perm (Fin 3510)}
    {D : Subgroup (Equiv.Perm (Fin 3510))} (hn : 0 < n)
    (hg : ∀ t < 3, PRep 3510 12 (MonoidHom.id _) (K (Nat.succ t)) (g t))
    (hh : PRep 3510 12 (MonoidHom.id _) Gk h)
    (hD : ∀ e < 27, ∃ y ∈ D, ∀ z < 3510, ap (DF (27 * j + e)) z = pt (MonoidHom.id _) y z)
    (hq : ∀ i < n, q01C K T DF Gk j n i = true) :
    Nat.card (closure (Set.range fun t : Fin 3 => g t)) = n ∧
    ∀ A ≤ closure (Set.range fun t : Fin 3 => g t), Nat.card A = 27 →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 3 = 1) → ∀ x ∈ A, h * x * h⁻¹ ∈ D := by
  classical
  have hR := permRep (G := Equiv.Perm (Fin 3510)) (n := 3510) (w := 12) (by norm_num)
    (by norm_num) (ψ := MonoidHom.id _) Function.injective_id
  have hR' : KeyRep (PRep 3510 12 (MonoidHom.id _)) q01M (pidn 3510 12) := hR
  have hs := fun i hi => q01C_spec (hq i hi)
  have ht := fun i hi => (hs i hi).1
  have hT := tabData_ofR hR' hg ht (fun i hi t ht => (hs i hi).2.1 t ht)
    (fun q hq => (hs q hq).2.2.1)
  have hE := tree_specR hR' hg ht
  obtain ⟨S, hSmem, hSg⟩ := hT.exists_subgroup hn
  have hmul : ∀ a < n, ∀ b < n, q01T T n a b < n ∧
      tabElt g (parOf n (q01P T) (q01J T)) a * tabElt g (parOf n (q01P T) (q01J T)) b =
        tabElt g (parOf n (q01P T) (q01J T)) (q01T T n a b) :=
    fun a ha b hb => tmF_spec hT n a b (le_of_lt ha) ha hb
  refine ⟨by rw [← hSg]; exact hT.card_subgroup hSmem, fun A hA hcard hcomm hexp x hx => ?_⟩
  set E := tabElt g (parOf n (q01P T) (q01J T)) with hEdef
  have hAS : ∀ a ∈ A, a ∈ S := fun a ha => by rw [hSg]; exact hA ha
  obtain ⟨i, hi, rfl⟩ := (hSmem x).1 (hAS x hx)
  obtain ⟨-, -, -, hf1, hf0⟩ := hs i hi
  by_cases hfl : qpE (T i) 3 = 1
  · obtain ⟨he, hc⟩ := hf1 hfl
    obtain ⟨y, hy, hyz⟩ := hD _ he
    rw [conj_of_full Function.injective_id hh (hE i hi).2 hyz hc]
    exact hy
  · exfalso
    have hcube : ∀ y < n, E y ∈ A → q01Cube T n y = true := by
      intro y hy hyA
      obtain ⟨r1, e1⟩ := hmul y hy y hy
      obtain ⟨r2, e2⟩ := hmul y hy _ r1
      have e3 : E (q01T T n y (q01T T n y y)) = E 0 := by
        rw [← e2, ← e1, ← pow_three, hexp _ hyA, hEdef, tabElt_zero]
      have e4 := hT.inj _ r2 0 hn e3
      unfold q01Cube
      exact Eq.mpr Nat.beq_eq e4
    have hc0 := hf0 hfl (hcube i hi hx)
    have hpair : ∀ y < n, E y ∈ A →
        bAnd(q01Cube T n y, Nat.beq (q01T T n i y) (q01T T n y i)) = true := by
      intro y hy hyA
      rw [hcube y hy hyA]
      change Nat.beq (q01T T n i y) (q01T T n y i) = true
      have e := hT.inj _ (hmul i hi y hy).1 _ (hmul y hy i hi).1
        (by rw [← hEdef, ← (hmul i hi y hy).2, ← (hmul y hy i hi).2]; exact hcomm _ hx _ hyA)
      exact Eq.mpr Nat.beq_eq e
    set s := (Finset.range n).filter fun y => E y ∈ A
    have h27 : 27 ≤ s.card := by
      let F : s → A := fun y => ⟨E y.1, (Finset.mem_filter.1 y.2).2⟩
      have hF : Function.Surjective F := by
        rintro ⟨a, ha⟩
        obtain ⟨k, hk, rfl⟩ := (hSmem a).1 (hAS a ha)
        exact ⟨⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ha⟩⟩, rfl⟩
      have := Nat.card_le_card_of_surjective F hF
      rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe] at this
      exact this
    have hsub : s ⊆ (Finset.range n).filter fun y =>
        bAnd(q01Cube T n y, Nat.beq (q01T T n i y) (q01T T n y i)) = true := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨hy1, hpair y (Finset.mem_range.1 hy1) hy2⟩
    have := Finset.card_le_card hsub
    rw [cntR_eq] at hc0
    omega

end CFSG.KS.Fi22Twist

end
