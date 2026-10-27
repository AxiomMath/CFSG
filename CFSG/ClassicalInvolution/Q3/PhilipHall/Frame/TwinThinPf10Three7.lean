module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Perm

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem ofVec_comm (u v : Fin n → ZMod 2) : ofVec u * ofVec v = ofVec v * ofVec u := by
  refine Wr.ext (funext fun x => ?_) rfl
  show u x + v ((1 : Equiv.Perm (Fin n)).symm x) = v x + u ((1 : Equiv.Perm (Fin n)).symm x)
  show u x + v x = v x + u x
  ring

@[expose] def pairVec (p q : Fin n) : Fin n → ZMod 2 :=
  fun x => (if x = p then 1 else 0) + (if x = q then 1 else 0)

theorem ofVec_pairVec_mem (p q : Fin n) : ofVec (pairVec p q) ∈ aeSub n := by
  classical
  refine ⟨?_, by simp [ofVec]⟩
  unfold wsum ofVec pairVec
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  exact zmod_two_add_self _

theorem ofVec_inv_mul (u v : Fin n → ZMod 2) :
    (ofVec u)⁻¹ * ofVec v = ofVec (fun x => u x + v x) := by
  refine Wr.ext (funext fun x => ?_) rfl
  rfl

theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

theorem pairVec_eq_one {p q y : Fin n} (h : pairVec p q y = 1) : y = p ∨ y = q := by
  classical
  by_contra hne
  push Not at hne
  unfold pairVec at h
  simp [hne.1, hne.2] at h

theorem perm_pair (α : Finset (Fin n)) (hα : α.card = 4) (w : Wr n)
    (hw : ∀ x, x ∈ Set.range (emb α hα) → w.perm x = x) {p q : Fin n} (hpq : p ≠ q)
    (hp : p ∉ Set.range (emb α hα)) (hq : q ∉ Set.range (emb α hα))
    (hC : mkQ n w * mkQ n (ofVec (pairVec p q)) * (mkQ n w)⁻¹ = mkQ n (ofVec (pairVec p q))) :
    w.perm.symm p = p ∨ w.perm.symm p = q := by
  classical
  have h1 : mkQ n (w * ofVec (pairVec p q) * w⁻¹) = mkQ n (ofVec (pairVec p q)) := by
    simpa only [map_mul, map_inv] using hC
  rw [conj_ofVec] at h1
  rcases mkQ_eq_iff.mp h1 with h2 | h2
  · rw [ofVec_inv_mul] at h2
    have h3 : ∀ x, pairVec p q (w.perm.symm x) + pairVec p q x = 0 := fun x => by
      have := congrFun (congrArg Wr.vec h2) x
      exact this
    have h4 := zmod_two_eq_of_add_eq_zero (h3 p)
    have h5 : pairVec p q p = 1 := by
      unfold pairVec; simp [hpq]
    rw [h5] at h4
    exact pairVec_eq_one h4
  · exfalso
    rw [ofVec_inv_mul] at h2
    have h3 := congrFun (congrArg Wr.vec h2) (emb α hα 0)
    have hx : emb α hα 0 ∈ Set.range (emb α hα) := Set.mem_range_self 0
    have hs : w.perm.symm (emb α hα 0) = emb α hα 0 := by
      apply w.perm.injective
      rw [Equiv.apply_symm_apply, hw _ hx]
    have h0 : pairVec p q (emb α hα 0) = 0 := by
      unfold pairVec
      have e1 : emb α hα 0 ≠ p := fun h => hp (h ▸ hx)
      have e2 : emb α hα 0 ≠ q := fun h => hq (h ▸ hx)
      simp [e1, e2]
    change pairVec p q (w.perm.symm (emb α hα 0)) + pairVec p q (emb α hα 0) = 1 at h3
    rw [hs, h0] at h3
    exact absurd h3 (by decide)

theorem core_seven (α : Finset (Fin 7)) (hα : α.card = 4) (w : Wr 7)
    (hA : ∃ a : ℕ, ∀ x ∈ TwinThinPf8.Hn 7, mkQ 7 (w ^ 3 ^ a) * x * (mkQ 7 (w ^ 3 ^ a))⁻¹ = x)
    (hB : ∀ c : Bool, ∀ x ∈ memBar α hα c, mkQ 7 w * x * (mkQ 7 w)⁻¹ = x)
    (hC : ∀ x ∈ TwinThinPf8.Hn 7, x * zBar α hα = zBar α hα * x → mkQ 7 w * x * (mkQ 7 w)⁻¹ = x) :
    ∀ x ∈ TwinThinPf8.Hn 7, mkQ 7 w * x * (mkQ 7 w)⁻¹ = x := by
  classical
  obtain ⟨a, hA⟩ := hA
  obtain ⟨c, e, hw, he, hc⟩ := exists_split (by norm_num) (by norm_num) α hα w hB
  have hep : e.perm = 1 := by
    rcases he with rfl | rfl
    · rfl
    · exact zOf_perm _
  have hwp : w.perm = c.perm := by rw [hw, mul_perm, hep, mul_one]
  have hwS : ∀ x, x ∈ Set.range (emb α hα) → w.perm x = x := fun x hx => by
    rw [hwp]; exact (hc x (by simpa using hx)).2
  have hcard : (Finset.univ.filter fun t : Fin 7 => t ∉ Set.range (emb α hα)).card = 3 := by
    rw [card_off]
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp hcard
  have hmem : ∀ t, t ∉ Set.range (emb α hα) ↔ t = x ∨ t = y ∨ t = z := fun t => by
    have : t ∈ (Finset.univ.filter fun t : Fin 7 => t ∉ Set.range (emb α hα)) ↔
        t ∈ ({x, y, z} : Finset (Fin 7)) := by rw [hT]
    simpa using this
  have hxS : x ∉ Set.range (emb α hα) := (hmem x).mpr (Or.inl rfl)
  have hyS : y ∉ Set.range (emb α hα) := (hmem y).mpr (Or.inr (Or.inl rfl))
  have hzS : z ∉ Set.range (emb α hα) := (hmem z).mpr (Or.inr (Or.inr rfl))
  have hpair : ∀ p q : Fin 7, p ≠ q → p ∉ Set.range (emb α hα) → q ∉ Set.range (emb α hα) →
      w.perm.symm p = p ∨ w.perm.symm p = q := by
    intro p q hpq hp hq
    refine perm_pair α hα w hwS hpq hp hq ?_
    refine hC _ ⟨ofVec (pairVec p q), ofVec_pairVec_mem p q, rfl⟩ ?_
    show mkQ 7 (ofVec (pairVec p q)) * mkQ 7 (zOf (emb α hα)) =
      mkQ 7 (zOf (emb α hα)) * mkQ 7 (ofVec (pairVec p q))
    rw [← map_mul, ← map_mul, zOf_eq_ofVec, ofVec_comm]
  have hfix : ∀ t, t ∉ Set.range (emb α hα) → w.perm.symm t = t := by
    intro t ht
    rcases (hmem t).mp ht with rfl | rfl | rfl
    · rcases hpair t y hxy hxS hyS with h1 | h1
      · exact h1
      · rcases hpair t z hxz hxS hzS with h2 | h2
        · exact h2
        · exact absurd (h1.symm.trans h2) hyz
    · rcases hpair t x hxy.symm hyS hxS with h1 | h1
      · exact h1
      · rcases hpair t z hyz hyS hzS with h2 | h2
        · exact h2
        · exact absurd (h1.symm.trans h2) hxz
    · rcases hpair t x hxz.symm hzS hxS with h1 | h1
      · exact h1
      · rcases hpair t y hyz.symm hzS hyS with h2 | h2
        · exact h2
        · exact absurd (h1.symm.trans h2) hxy
  have hw1 : w.perm = 1 := by
    refine Equiv.ext fun t => ?_
    by_cases ht : t ∈ Set.range (emb α hα)
    · exact hwS t ht
    · have := hfix t ht
      have h2 : w.perm t = t := by
        have := congrArg w.perm this
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
      exact h2
  have hw2 : w ^ 2 = 1 := by
    rw [sq]
    refine Wr.ext (funext fun t => ?_) (by rw [mul_perm, hw1]; rfl)
    show w.vec t + w.vec (w.perm.symm t) = 0
    have : w.perm.symm t = t := by rw [hw1]; rfl
    rw [this]
    exact zmod_two_add_self _
  have hpow : w ^ 3 ^ a = w := by
    rw [pow_eq_pow_mod _ hw2]
    have : 3 ^ a % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    rw [this, pow_one]
  intro t ht
  have := hA t ht
  rwa [hpow] at this

theorem aeThreeC_seven (hA : TwinThinPf8.AEAut 7) : TwinThinPf8.AEThreeC 7 := by
  intro α hα H hH σ ⟨a, ha⟩ hperm hcent hextra
  have hk : 3 ^ a = (3 ^ a - 1) + 1 := by
    have : 0 < 3 ^ a := Nat.pow_pos (by norm_num)
    omega
  have hid : (⇑σ)^[3 ^ a] = id := funext ha
  have hid1 : (⇑σ)^[3 ^ a - 1] ∘ ⇑σ = id := by
    rw [← Function.iterate_succ, Nat.succ_eq_add_one, ← hk]; exact hid
  have hid2 : ⇑σ ∘ (⇑σ)^[3 ^ a - 1] = id := by
    rw [← Function.iterate_succ', Nat.succ_eq_add_one, ← hk]; exact hid
  have hbij : Function.Bijective σ :=
    ⟨Function.Injective.of_comp (f := (⇑σ)^[3 ^ a - 1]) (by rw [hid1]; exact Function.injective_id),
     Function.Surjective.of_comp (g := (⇑σ)^[3 ^ a - 1]) (by rw [hid2]; exact Function.surjective_id)⟩
  obtain ⟨w, hw⟩ := hA H hH σ hbij hperm
  have hit : ∀ (k : ℕ) (x : ↥H), (((⇑σ)^[k] x : ↥H) : AEQ 7) =
      mkQ 7 (w ^ k) * (x : AEQ 7) * (mkQ 7 (w ^ k))⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', hw, ih, pow_succ', map_mul]
      group
  have hmem : ∀ x : AEQ 7, ∀ β : Finset (Fin 7), ∀ (hβ : β.card = 4), ∀ c : Bool,
      x ∈ memBar β hβ c → x ∈ H := by
    intro x β hβ c hx
    rw [hH]; exact TwinThinPf8.memBar_le_Hn β hβ c hx
  have hcent' : ∀ (c : Bool), ∀ x ∈ memBar α hα c, mkQ 7 w * x * (mkQ 7 w)⁻¹ = x := by
    intro c x hx
    have := hcent α hα c (Or.inr rfl) ⟨x, hmem x α hα c hx⟩ hx
    have h2 := congrArg Subtype.val this
    rw [hw] at h2
    exact h2
  have hC' : ∀ x ∈ TwinThinPf8.Hn 7, x * zBar α hα = zBar α hα * x →
      mkQ 7 w * x * (mkQ 7 w)⁻¹ = x := by
    intro x hx hxz
    have hxH : x ∈ H := by rw [hH]; exact hx
    have := hextra ⟨x, hxH⟩ hxz
    have h2 := congrArg Subtype.val this
    rw [hw] at h2
    exact h2
  have hall := core_seven α hα w ⟨a, fun x hx => by
      have hxH : x ∈ H := by rw [hH]; exact hx
      have h1 := hit (3 ^ a) ⟨x, hxH⟩
      rw [ha ⟨x, hxH⟩] at h1
      exact h1.symm⟩ hcent' hC'
  intro r
  apply Subtype.ext
  rw [hw]
  exact hall r (by rw [← hH]; exact r.2)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
