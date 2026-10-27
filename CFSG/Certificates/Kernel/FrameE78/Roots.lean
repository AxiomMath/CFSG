module

public import CFSG.Certificates.Kernel.FrameE78.Refl

public section

namespace CFSG.KC.FrameE78.Refl

open Matrix

variable {n : ℕ} {C : Matrix (Fin n) (Fin n) (ZMod 3)}

abbrev ev (i : Fin n) : Fin n → ZMod 3 := Pi.single i 1

abbrev sS (C : Matrix (Fin n) (Fin n) (ZMod 3)) (i : Fin n) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  rf C (ev i)

abbrev sR (C : Matrix (Fin n) (Fin n) (ZMod 3)) (i : Fin n) (c : Fin n → ZMod 3) :
    Fin n → ZMod 3 :=
  c - bf C (ev i) c • ev i

structure RootData (C : Matrix (Fin n) (Fin n) (ZMod 3)) (m : ℕ) (R : ℕ → Fin n → ZMod 3) :
    Prop where
  norm : ∀ a < m, bf C (R a) (R a) = 2
  simple : ∀ i : Fin n, i.val < m ∧ R i = ev i
  clos : ∀ a < m, ∀ i : Fin n, ∃ b < m, sR C i (R a) = R b ∨ sR C i (R a) = -R b
  par : ∀ a < m, n ≤ a → ∃ p < a, ∃ i : Fin n, sR C i (R p) = R a ∨ sR C i (R p) = -R a
  dist : ∀ a < m, ∀ b < a, R a ≠ R b ∧ R a ≠ -R b

variable {m : ℕ} {R : ℕ → Fin n → ZMod 3}

theorem RootData.ev_norm (hR : RootData C m R) (i : Fin n) : bf C (ev i) (ev i) = 2 := by
  have h := hR.norm i (hR.simple i).1
  rwa [(hR.simple i).2] at h

theorem RootData.sS_sq (hR : RootData C m R) (i : Fin n) : sS C i * sS C i = 1 :=
  rf_mul_self (hR.ev_norm i)

theorem RootData.ne_of_ne (hR : RootData C m R) {a b : ℕ} (ha : a < m) (hb : b < m)
    (hab : a ≠ b) : R a ≠ R b ∧ R a ≠ -R b := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · obtain ⟨h1, h2⟩ := hR.dist b hb a h
    refine ⟨fun e => h1 e.symm, fun e => h2 ?_⟩
    rw [e, neg_neg]
  · exact hR.dist a ha b h

theorem RootData.rf_inj (hR : RootData C m R) {a b : ℕ} (ha : a < m) (hb : b < m)
    (h : rf C (R a) = rf C (R b)) : a = b := by
  by_contra hab
  obtain ⟨h1, h2⟩ := hR.ne_of_ne ha hb hab
  rcases Refl.rf_inj (hR.norm a ha) (hR.norm b hb) h with e | e
  · exact h1 e
  · exact h2 e

private theorem rf_pm {c d : Fin n → ZMod 3} (h : c = d ∨ c = -d) : rf C c = rf C d := by
  rcases h with rfl | rfl
  · rfl
  · exact rf_neg d

theorem conjDer_iff (hC : C.IsSymm) (hR : RootData C m R) (r : Matrix (Fin n) (Fin n) (ZMod 3)) :
    ConjDer (sS C) r ↔ ∃ a < m, r = rf C (R a) := by
  constructor
  · intro h
    induction h with
    | base i =>
      refine ⟨i, (hR.simple i).1, ?_⟩
      rw [(hR.simple i).2]
    | @conj i r _ ih =>
      obtain ⟨a, ha, rfl⟩ := ih
      obtain ⟨b, hb, e⟩ := hR.clos a ha i
      exact ⟨b, hb, by rw [rf_conj hC (hR.ev_norm i), rf_pm e]⟩
  · rintro ⟨a, ha, rfl⟩
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      by_cases hna : n ≤ a
      · obtain ⟨p, hp, i, e⟩ := hR.par a ha hna
        have h1 := ConjDer.conj i (ih p hp (by omega))
        rwa [rf_conj hC (hR.ev_norm i), rf_pm e] at h1
      · have h1 := ConjDer.base (S := sS C) ⟨a, by omega⟩
        rwa [sS, ← (hR.simple ⟨a, by omega⟩).2] at h1

theorem conjDer_braid (hC : C.IsSymm) (hR : RootData C m R) {r t : Matrix (Fin n) (Fin n) (ZMod 3)}
    (hr : ConjDer (sS C) r) (ht : ConjDer (sS C) t) :
    r = t ∨ r * t = t * r ∨ r * t * r = t * r * t := by
  obtain ⟨a, ha, rfl⟩ := (conjDer_iff hC hR r).1 hr
  obtain ⟨b, hb, rfl⟩ := (conjDer_iff hC hR t).1 ht
  by_cases h : bf C (R a) (R b) = 0
  · exact Or.inr (Or.inl (rf_comm_of_bf h (by rw [bf_symm hC]; exact h)))
  · exact Or.inr (Or.inr (rf_braid hC (hR.norm a ha) (hR.norm b hb) h))

@[expose] def fixSet (C : Matrix (Fin n) (Fin n) (ZMod 3)) (x : Fin n → ZMod 3) :
    Set (Matrix (Fin n) (Fin n) (ZMod 3)) :=
  {r | ConjDer (sS C) r ∧ r *ᵥ x = x}

theorem fixSet_eq (hC : C.IsSymm) (hR : RootData C m R) (x : Fin n → ZMod 3) :
    fixSet C x = (fun a => rf C (R a)) '' {a | a < m ∧ R a ⬝ᵥ x = 0} := by
  ext r
  constructor
  · rintro ⟨hr, hx⟩
    obtain ⟨a, ha, rfl⟩ := (conjDer_iff hC hR r).1 hr
    exact ⟨a, ⟨ha, (rf_fix (hR.norm a ha) x).1 hx⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hx⟩, rfl⟩
    exact ⟨(conjDer_iff hC hR _).2 ⟨a, ha, rfl⟩, (rf_fix (hR.norm a ha) x).2 hx⟩

theorem fixSet_neg (x : Fin n → ZMod 3) : fixSet C (-x) = fixSet C x := by
  ext r
  simp only [fixSet, Set.mem_setOf_eq, mulVec_neg, neg_inj]

theorem fixSet_smul (hR : RootData C m R) (i : Fin n) (x : Fin n → ZMod 3) :
    fixSet C (sS C i *ᵥ x) = conjEquiv (hR.sS_sq i) '' fixSet C x := by
  have hs := hR.sS_sq i
  ext r
  constructor
  · rintro ⟨hr, hx⟩
    refine ⟨sS C i * r * sS C i, ⟨ConjDer.conj i hr, ?_⟩, ?_⟩
    · rw [← mulVec_mulVec, ← mulVec_mulVec, hx, mulVec_mulVec, hs, one_mulVec]
    · change sS C i * (sS C i * r * sS C i) * sS C i = r
      simp only [← mul_assoc, hs, one_mul]
      rw [mul_assoc, hs, mul_one]
  · rintro ⟨r', ⟨hr, hx⟩, rfl⟩
    refine ⟨ConjDer.conj i hr, ?_⟩
    change (sS C i * r' * sS C i) *ᵥ (sS C i *ᵥ x) = sS C i *ᵥ x
    have hSS : sS C i *ᵥ (sS C i *ᵥ x) = x := by rw [mulVec_mulVec, hs, one_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hSS, hx]

theorem part_closed {M : Type*} [Monoid M] {P Q T : Set M} (hU : P ∪ Q = T) (hD : Disjoint P Q)
    (hinv : ∀ t ∈ T, t * t = 1) (hT : ∀ r ∈ T, ∀ t ∈ T, t * r * t ∈ T)
    (hPQ : ∀ r ∈ P, ∀ t ∈ Q, r * t = t * r) : ∀ r ∈ P, ∀ t ∈ P, t * r * t ∈ P := by
  intro r hr t ht
  have hrT : r ∈ T := hU ▸ Or.inl hr
  have htT : t ∈ T := hU ▸ Or.inl ht
  have h1 := hT r hrT t htT
  rw [← hU] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exfalso
    have hc := hPQ t ht _ h1
    have htt := hinv t htT
    have e : t * r = r * t := by
      calc t * r = t * r * (t * t) := by rw [htt, mul_one]
        _ = t * r * t * t := by simp only [mul_assoc]
        _ = t * (t * r * t) := hc.symm
        _ = t * t * (r * t) := by simp only [mul_assoc]
        _ = r * t := by rw [htt, one_mul]
    have e2 : t * r * t = r := by rw [e, mul_assoc, htt, mul_one]
    rw [e2] at h1
    exact Set.disjoint_left.1 hD hr h1

theorem fixSet_inv (hR : RootData C m R) (x : Fin n → ZMod 3) :
    ∀ t ∈ fixSet C x, t * t = 1 := fun t ht => conjDer_mul_self hR.sS_sq ht.1

theorem fixSet_conj (hR : RootData C m R) (x : Fin n → ZMod 3) :
    ∀ r ∈ fixSet C x, ∀ t ∈ fixSet C x, t * r * t ∈ fixSet C x := by
  rintro r ⟨hr, hrx⟩ t ⟨ht, htx⟩
  refine ⟨conjDer_conj hR.sS_sq ht hr, ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, htx, hrx, htx]

private theorem ncard_image_roots (hR : RootData C m R) (s : Set ℕ) (hs : ∀ a ∈ s, a < m) :
    ((fun a => rf C (R a)) '' s).ncard = s.ncard :=
  Set.InjOn.ncard_image fun a ha b hb e => hR.rf_inj (hs a ha) (hs b hb) e

private theorem ncard_eq_card (p : ℕ → Prop) [DecidablePred p] :
    {a | a < m ∧ p a}.ncard = ((Finset.range m).filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

theorem dich_unif (hC : C.IsSymm) (hR : RootData C m R) {x : Fin n → ZMod 3} {A : ℕ → ℕ → Prop}
    {t d : ℕ} (ht : ((Finset.range m).filter fun a => R a ⬝ᵥ x = 0).card = t)
    (hd : ∀ a < m, R a ⬝ᵥ x = 0 → ((Finset.range m).filter fun b =>
      R b ⬝ᵥ x = 0 ∧ b ≠ a ∧ bf C (R a) (R b) ≠ 0).card = d) (hA : A t d) :
    Dich A (fixSet C x) := by
  rw [fixSet_eq hC hR]
  refine Or.inr ⟨d, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, hax⟩, rfl⟩
    have e : {u | u ∈ (fun a => rf C (R a)) '' {a | a < m ∧ R a ⬝ᵥ x = 0} ∧
        rf C (R a) * u ≠ u * rf C (R a)} = (fun a => rf C (R a)) ''
          {b | b < m ∧ (R b ⬝ᵥ x = 0 ∧ b ≠ a ∧ bf C (R a) (R b) ≠ 0)} := by
      ext u
      constructor
      · rintro ⟨⟨b, ⟨hb, hbx⟩, rfl⟩, hne⟩
        refine ⟨b, ⟨hb, hbx, fun e => hne (by rw [e]), fun h0 => hne ?_⟩, rfl⟩
        exact rf_comm_of_bf h0 (by rw [bf_symm hC]; exact h0)
      · rintro ⟨b, ⟨hb, hbx, hba, h0⟩, rfl⟩
        refine ⟨⟨b, ⟨hb, hbx⟩, rfl⟩, fun hc => h0 ?_⟩
        obtain ⟨h1, h2⟩ := hR.ne_of_ne ha hb (Ne.symm hba)
        exact rf_ne_comm hC (hR.norm a ha) (hR.norm b hb) h1 h2 hc
    rw [e, ncard_image_roots hR _ (fun b hb => hb.1), ncard_eq_card]
    exact hd a ha hax
  · rw [ncard_image_roots hR _ (fun b hb => hb.1), ncard_eq_card]
    rw [ht]
    exact hA

theorem dich_split (hC : C.IsSymm) (hR : RootData C m R) {x : Fin n → ZMod 3} {A : ℕ → ℕ → Prop}
    (P : ℕ → Prop) (hP : ∃ a < m, R a ⬝ᵥ x = 0 ∧ P a) (hQ : ∃ a < m, R a ⬝ᵥ x = 0 ∧ ¬ P a)
    (hPQ : ∀ a < m, ∀ b < m, R a ⬝ᵥ x = 0 → R b ⬝ᵥ x = 0 → P a → ¬ P b → bf C (R a) (R b) = 0) :
    Dich A (fixSet C x) := by
  set P' := (fun a => rf C (R a)) '' {a | a < m ∧ R a ⬝ᵥ x = 0 ∧ P a} with hP'
  set Q' := (fun a => rf C (R a)) '' {a | a < m ∧ R a ⬝ᵥ x = 0 ∧ ¬ P a} with hQ'
  have hU : P' ∪ Q' = fixSet C x := by
    rw [fixSet_eq hC hR, hP', hQ', ← Set.image_union]
    congr 1
    ext a
    simp only [Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hD : Disjoint P' Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ⟨ha, -, hPa⟩, rfl⟩ ⟨b, ⟨hb, -, hPb⟩, e⟩
    rw [hR.rf_inj hb ha e] at hPb
    exact hPb hPa
  have hc : ∀ r ∈ P', ∀ t ∈ Q', r * t = t * r := by
    rintro _ ⟨a, ⟨ha, hax, hPa⟩, rfl⟩ _ ⟨b, ⟨hb, hbx, hPb⟩, rfl⟩
    have h0 := hPQ a ha b hb hax hbx hPa hPb
    exact rf_comm_of_bf h0 (by rw [bf_symm hC]; exact h0)
  have hinv := fixSet_inv hR x
  have hT := fixSet_conj hR x
  refine Or.inl ⟨P', Q', hU, hD, ?_, ?_, part_closed hU hD hinv hT hc, ?_, hc⟩
  · obtain ⟨a, ha, hax, hPa⟩ := hP
    exact ⟨_, a, ⟨ha, hax, hPa⟩, rfl⟩
  · obtain ⟨a, ha, hax, hPa⟩ := hQ
    exact ⟨_, a, ⟨ha, hax, hPa⟩, rfl⟩
  · rw [Set.union_comm] at hU
    exact part_closed hU hD.symm hinv hT fun r hr t ht => (hc t ht r hr).symm

end CFSG.KC.FrameE78.Refl

end
