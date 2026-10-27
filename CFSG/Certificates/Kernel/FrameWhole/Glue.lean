module

public import CFSG.Certificates.Kernel.FrameE78.Glue
public import Certificates.Data.Kernel.FrameWholeK
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CFSG.KC.FrameWhole

open CFSG.KC.Enum CFSG.KC.FrameE78 CFSG.KC.FrameE78.Refl CFSG.KS.PK Matrix

theorem connK_sound {n m RP LV : ℕ} (h : connK n m RP LV = true) :
    ∀ a < m, a = 0 ∨ ∃ p < m, vget LV p < vget LV a ∧ FrameE78.bf n RP p a ≠ 0 := by
  intro a ha
  have h1 := allN_iff.1 h a ha
  rw [orB_eq, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl (beqT.1 h1)
  · right
    rw [strictB_eq] at h1
    by_contra hc
    push Not at hc
    have h2 : allN m (fun p => notB (bAnd(Nat.blt (vget LV p) (vget LV a),
        notB (Nat.beq (FrameE78.bf n RP p a) 0)))) = true := by
      refine allN_iff.2 fun p hp => ?_
      cases e1 : Nat.blt (vget LV p) (vget LV a)
      · rfl
      · rw [beqT.2 (hc p hp (bltT.1 e1))]
        rfl
    have h3 : notB (allN m (fun p => notB (bAnd(Nat.blt (vget LV p) (vget LV a),
        notB (Nat.beq (FrameE78.bf n RP p a) 0))))) = true := h1
    rw [h2] at h3
    exact absurd h3 (by decide)

theorem fullM_testBit {m a : ℕ} (ha : a < m) : (fullM m).testBit a = true := by
  change (2 ^ m - 1).testBit a = true
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true ha

private theorem bf_zero_iff {n C m RP : ℕ} (hn : n ≤ 8) (h1 : rootOK n C m RP = true) (a : ℕ)
    {c : ℕ} (hc : c < m) :
    FrameE78.bf n RP a c = 0 ↔ Refl.bf (Cm n C) (Rv n RP a) (Rv n RP c) = 0 := by
  have hr := rootOK_sound hn h1
  change dot3 n (rc RP a) (rC RP c) = 0 ↔ _
  rw [dot3_zero_iff, (hr c hc).2.1, dec_cvec]
  rfl

private theorem ncard_lt_and (m : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    {a | a < m ∧ p a}.ncard = ((Finset.range m).filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  simp

theorem whole_facts {n C m RP CL PT d LV : ℕ} (hn : n ≤ 8) (hnm : n ≤ m)
    (hC : (Cm n C).IsSymm)
    (h1 : rootOK n C m RP = true) (h2 : simpleOK n RP = true) (h3 : closOK n m RP CL = true)
    (h4 : parOK n m CL PT = true) (h5 : distOK m RP = true)
    (hu : unifK n m RP (fullM m) m d = true) (hk : connK n m RP LV = true) :
    {r | ConjDer (sS (Cm n C)) r}.ncard = m ∧
      (∀ r, ConjDer (sS (Cm n C)) r →
        {t | ConjDer (sS (Cm n C)) t ∧ r * t ≠ t * r}.ncard = d) ∧
      ∀ r t, ConjDer (sS (Cm n C)) r → ConjDer (sS (Cm n C)) t →
        Relation.ReflTransGen (fun a b => ConjDer (sS (Cm n C)) a ∧ ConjDer (sS (Cm n C)) b ∧
          a * b ≠ b * a) r t := by
  have hR := rootData_of hn hnm h1 h2 h3 h4 h5
  have hinj : ∀ s : Set ℕ, (∀ a ∈ s, a < m) →
      ((fun a => rf (Cm n C) (Rv n RP a)) '' s).ncard = s.ncard :=
    fun s hs => Set.InjOn.ncard_image fun a ha b hb e => hR.rf_inj (hs a ha) (hs b hb) e
  have hmem : ∀ b < m, ConjDer (sS (Cm n C)) (rf (Cm n C) (Rv n RP b)) :=
    fun b hb => (conjDer_iff hC hR _).2 ⟨b, hb, rfl⟩
  obtain ⟨-, hdeg⟩ := unifK_sound hu
  refine ⟨?_, fun r hr => ?_, fun r t hr ht => ?_⟩
  · have e : {r | ConjDer (sS (Cm n C)) r} =
        (fun a => rf (Cm n C) (Rv n RP a)) '' {a | a < m ∧ True} := by
      ext r
      rw [Set.mem_setOf_eq, conjDer_iff hC hR r]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ⟨ha, trivial⟩, rfl⟩
      · rintro ⟨a, ⟨ha, -⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
    rw [e, hinj _ (fun a ha => ha.1), ncard_lt_and m (fun _ => True), Finset.filter_true_of_mem
      (fun _ _ => trivial), Finset.card_range]
  · obtain ⟨a, ha, rfl⟩ := (conjDer_iff hC hR r).1 hr
    have e : {t | ConjDer (sS (Cm n C)) t ∧ rf (Cm n C) (Rv n RP a) * t ≠
        t * rf (Cm n C) (Rv n RP a)} = (fun b => rf (Cm n C) (Rv n RP b)) ''
          {b | b < m ∧ (b ≠ a ∧ Refl.bf (Cm n C) (Rv n RP a) (Rv n RP b) ≠ 0)} := by
      ext u
      constructor
      · rintro ⟨hu, hne⟩
        obtain ⟨b, hb, rfl⟩ := (conjDer_iff hC hR u).1 hu
        refine ⟨b, ⟨hb, fun e => hne (by rw [e]), fun h0 => hne ?_⟩, rfl⟩
        exact rf_comm_of_bf h0 (by rw [bf_symm hC]; exact h0)
      · rintro ⟨b, ⟨hb, hba, h0⟩, rfl⟩
        refine ⟨hmem b hb, fun hc => h0 ?_⟩
        obtain ⟨e1, e2⟩ := hR.ne_of_ne ha hb (Ne.symm hba)
        exact rf_ne_comm hC (hR.norm a ha) (hR.norm b hb) e1 e2 hc
    rw [e, hinj _ (fun b hb => hb.1),
      ncard_lt_and m (fun b => b ≠ a ∧ Refl.bf (Cm n C) (Rv n RP a) (Rv n RP b) ≠ 0),
      ← hdeg a ha (fullM_testBit ha)]
    congr 1
    refine Finset.filter_congr fun b hb => ?_
    have hb' := Finset.mem_range.1 hb
    rw [ne_eq (Refl.bf _ _ _), ← bf_zero_iff hn h1 a hb', fullM_testBit hb']
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  · have hsymm : ∀ x y, (ConjDer (sS (Cm n C)) x ∧ ConjDer (sS (Cm n C)) y ∧ x * y ≠ y * x) →
        ConjDer (sS (Cm n C)) y ∧ ConjDer (sS (Cm n C)) x ∧ y * x ≠ x * y :=
      fun x y h => ⟨h.2.1, h.1, fun e => h.2.2 e.symm⟩
    have hrev : ∀ {x y}, Relation.ReflTransGen (fun a b => ConjDer (sS (Cm n C)) a ∧
        ConjDer (sS (Cm n C)) b ∧ a * b ≠ b * a) x y → Relation.ReflTransGen
          (fun a b => ConjDer (sS (Cm n C)) a ∧ ConjDer (sS (Cm n C)) b ∧ a * b ≠ b * a) y x := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.head (hsymm _ _ hbc)
    have hpath : ∀ k a, vget LV a = k → a < m → Relation.ReflTransGen (fun a b =>
        ConjDer (sS (Cm n C)) a ∧ ConjDer (sS (Cm n C)) b ∧ a * b ≠ b * a)
          (rf (Cm n C) (Rv n RP 0)) (rf (Cm n C) (Rv n RP a)) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro a hka ha
        rcases connK_sound hk a ha with rfl | ⟨p, hpm, hlt, hbf⟩
        · exact Relation.ReflTransGen.refl
        · refine (ih (vget LV p) (by omega) p rfl hpm).tail
            ⟨hmem p hpm, hmem a ha, fun hc => hbf ?_⟩
          obtain ⟨e1, e2⟩ := hR.ne_of_ne hpm ha (fun e => by rw [e] at hlt; exact lt_irrefl _ hlt)
          exact (bf_zero_iff hn h1 p ha).2 (rf_ne_comm hC (hR.norm p hpm) (hR.norm a ha) e1 e2 hc)
    obtain ⟨a, ha, rfl⟩ := (conjDer_iff hC hR r).1 hr
    obtain ⟨b, hb, rfl⟩ := (conjDer_iff hC hR t).1 ht
    exact (hrev (hpath _ a rfl ha)).trans (hpath _ b rfl hb)

end CFSG.KC.FrameWhole

end
