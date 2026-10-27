module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermDefs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Equiv Equiv.Perm Nat

private abbrev pt (m i : ℕ) : Fin (m + 1) := Fin.ofNat (m + 1) i

private def CentQ (m : ℕ) (σ : Perm (Fin (m + 1))) : Prop :=
  σ * ub m = ub m * σ ∧ σ * vb m = vb m * σ ∧ σ * xb1 m = xb1 m * σ ∧ σ * xb2 m = xb2 m * σ ∧
    σ * tb m = tb m * σ

private theorem eq_pt (m : ℕ) (i : Fin (m + 1)) : i = pt m i.val := by
  ext
  simp [pt]

private theorem apply_comm {α : Type*} {σ g : Perm α} (h : σ * g = g * σ) (a : α) :
    σ (g a) = g (σ a) := by
  have := congrArg (fun f : Perm α => f a) h
  simpa using this

private theorem exists_resHom {α : Type*} (P : Subgroup (Perm α)) (p : α → Prop)
    (hp : ∀ g ∈ P, ∀ a, p (g a) ↔ p a) :
    ∃ ψ : P →* Perm (Subtype p),
      ∀ (g : P) (a : Subtype p), ((ψ g a : Subtype p) : α) = (g : Perm α) a :=
  ⟨⟨⟨fun g => (g : Perm α).subtypePerm (hp g g.2), by ext; rfl⟩, by intro g h; ext; rfl⟩,
    fun _ _ => rfl⟩

private theorem hk2 : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide

private theorem pt_val_zero (m : ℕ) : (pt m 0).val = 0 := by
  simp [pt]

section Qbar

variable (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10)

include h7 h10

private theorem pts :
    tb m (pt m 0) = pt m 1 ∧ xb1 m (pt m 0) = pt m 2 ∧ vb m (pt m 0) = pt m 3 ∧
    xb2 m (pt m 0) = pt m 4 ∧ ub m (pt m 0) = pt m 5 ∧ xb1 m (pt m 4) = pt m 6 ∧
    tb m (pt m 6) = pt m 7 ∧ ub m (pt m 1) = pt m 4 ∧ xb1 m (pt m 1) = pt m 3 := by
  interval_cases m <;> decide

private theorem zero_cases :
    ∀ j : Fin (m + 1), tb m j ≠ j → xb2 m j = ub m (tb m j) → vb m j = xb1 m (tb m j) →
      j = pt m 0 ∨ j = pt m 1 := by
  interval_cases m <;> decide

private theorem tb_comm_gens :
    tb m * ub m = ub m * tb m ∧ tb m * vb m = vb m * tb m ∧ tb m * xb1 m = xb1 m * tb m ∧
    tb m * xb2 m = xb2 m * tb m ∧ tb m * tb m = tb m * tb m := by
  interval_cases m <;> decide

private theorem pt_ne : pt m 1 ≠ pt m 0 := by
  interval_cases m <;> decide

private theorem fix_of_zero (σ : Perm (Fin (m + 1))) (hσ : CentQ m σ) (h0 : σ (pt m 0) = pt m 0) :
    ∀ i : Fin (m + 1), i.val < 8 → σ i = i := by
  obtain ⟨hub, hvb, hxb1, hxb2, htb⟩ := hσ
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, -, -⟩ := pts m h7 h10
  have e1 : σ (pt m 1) = pt m 1 := by
    have := apply_comm htb (pt m 0); rwa [p1, h0, p1] at this
  have e2 : σ (pt m 2) = pt m 2 := by
    have := apply_comm hxb1 (pt m 0); rwa [p2, h0, p2] at this
  have e3 : σ (pt m 3) = pt m 3 := by
    have := apply_comm hvb (pt m 0); rwa [p3, h0, p3] at this
  have e4 : σ (pt m 4) = pt m 4 := by
    have := apply_comm hxb2 (pt m 0); rwa [p4, h0, p4] at this
  have e5 : σ (pt m 5) = pt m 5 := by
    have := apply_comm hub (pt m 0); rwa [p5, h0, p5] at this
  have e6 : σ (pt m 6) = pt m 6 := by
    have := apply_comm hxb1 (pt m 4); rwa [p6, e4, p6] at this
  have e7 : σ (pt m 7) = pt m 7 := by
    have := apply_comm htb (pt m 6); rwa [p7, e6, p7] at this
  intro i hi
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨
      i.val = 6 ∨ i.val = 7 := by omega
  have hi' : i = pt m i.val := eq_pt m i
  rcases hcases with h | h | h | h | h | h | h | h <;> rw [h] at hi' <;> rw [hi'] <;> assumption

private theorem zero_eq (σ : Perm (Fin (m + 1))) (hσ : CentQ m σ) :
    σ (pt m 0) = pt m 0 ∨ σ (pt m 0) = pt m 1 := by
  obtain ⟨hub, hvb, hxb1, hxb2, htb⟩ := hσ
  obtain ⟨p1, -, p3, p4, -, -, -, p8, p9⟩ := pts m h7 h10
  have e1 : σ (pt m 1) = tb m (σ (pt m 0)) := by
    have := apply_comm htb (pt m 0); rwa [p1] at this
  have e3 : σ (pt m 3) = vb m (σ (pt m 0)) := by
    have := apply_comm hvb (pt m 0); rwa [p3] at this
  have e4 : σ (pt m 4) = xb2 m (σ (pt m 0)) := by
    have := apply_comm hxb2 (pt m 0); rwa [p4] at this
  have f1 : σ (pt m 4) = ub m (σ (pt m 1)) := by
    have := apply_comm hub (pt m 1); rwa [p8] at this
  have f2 : σ (pt m 3) = xb1 m (σ (pt m 1)) := by
    have := apply_comm hxb1 (pt m 1); rwa [p9] at this
  have hne : tb m (σ (pt m 0)) ≠ σ (pt m 0) := by
    rw [← e1]
    exact fun h => pt_ne m h7 h10 (σ.injective h)
  exact zero_cases m h7 h10 (σ (pt m 0)) hne (by rw [← e4, f1, e1]) (by rw [← e3, f2, e1])

private theorem centQ_tb_mul (σ : Perm (Fin (m + 1))) (hσ : CentQ m σ) : CentQ m (tb m * σ) := by
  obtain ⟨hub, hvb, hxb1, hxb2, htb⟩ := hσ
  obtain ⟨c1, c2, c3', c4, c5⟩ := tb_comm_gens m h7 h10
  exact ⟨(Commute.mul_left c1 hub).eq, (Commute.mul_left c2 hvb).eq,
    (Commute.mul_left c3' hxb1).eq, (Commute.mul_left c4 hxb2).eq,
    (Commute.mul_left c5 htb).eq⟩

theorem cent_Qbar (σ : Perm (Fin (m + 1)))
    (h : ∀ g ∈ ({ub m, vb m, xb1 m, xb2 m, tb m} : Set (Perm (Fin (m + 1)))), σ * g = g * σ) :
    ∃ (k : ZMod 2) (σ' : Perm (Fin (m + 1))), (∀ i : Fin (m + 1), i.val < 8 → σ' i = i) ∧
      σ = zpow2 (tb m) k * σ' := by
  have hσ : CentQ m σ := ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp),
    h _ (by simp)⟩
  rcases zero_eq m h7 h10 σ hσ with h0 | h0
  · refine ⟨0, σ, fix_of_zero m h7 h10 σ hσ h0, ?_⟩
    simp [zpow2]
  · have hsq : tb m * tb m = 1 := by interval_cases m <;> decide
    have hz : tb m (pt m 1) = pt m 0 := by interval_cases m <;> decide
    refine ⟨1, tb m * σ, fix_of_zero m h7 h10 _ (centQ_tb_mul m h7 h10 σ hσ) ?_, ?_⟩
    · rw [Perm.mul_apply, h0, hz]
    · have h1 : zpow2 (tb m) (1 : ZMod 2) = tb m := by
        simp [zpow2]
      rw [h1, ← mul_assoc, hsq, one_mul]

private theorem tb_facts :
    (∀ a : Fin (m + 1), a.val < 8 → (tb m a).val < 8) ∧
    (∀ a : Fin (m + 1), 8 ≤ a.val → tb m a = a) ∧
    (∀ a : Fin (m + 1), a.val < 8 → ((tb m a).val < 2 ↔ a.val < 2)) ∧
    tb m (pt m 0) ≠ pt m 0 := by
  interval_cases m <;> decide

private theorem zpow2_tb_facts (k : ZMod 2) :
    (∀ a : Fin (m + 1), a.val < 8 → (zpow2 (tb m) k a).val < 8) ∧
    (∀ a : Fin (m + 1), 8 ≤ a.val → zpow2 (tb m) k a = a) ∧
    (∀ a : Fin (m + 1), a.val < 8 → ((zpow2 (tb m) k a).val < 2 ↔ a.val < 2)) ∧
    (zpow2 (tb m) k (pt m 0) = pt m 0 → zpow2 (tb m) k = 1) := by
  obtain ⟨t1, t2, t3, t4⟩ := tb_facts m h7 h10
  rcases hk2 k with rfl | rfl
  · simp [zpow2]
  · have h1 : zpow2 (tb m) (1 : ZMod 2) = tb m := by simp [zpow2]
    rw [h1]
    exact ⟨t1, t2, t3, fun h => absurd h t4⟩

private theorem good_of_cent (g : Perm (Fin (m + 1)))
    (hg : ∀ q ∈ ({ub m, vb m, xb1 m, xb2 m, tb m} : Set (Perm (Fin (m + 1)))), g * q = q * g) :
    (∀ a : Fin (m + 1), 8 ≤ (g a).val ↔ 8 ≤ a.val) ∧
    (∀ a : Fin (m + 1), (g a).val < 2 ↔ a.val < 2) ∧
    (g (pt m 0) = pt m 0 → (∀ a : Fin (m + 1), 8 ≤ a.val → g a = a) → g = 1) := by
  obtain ⟨k, σ', hσ', rfl⟩ := cent_Qbar m h7 h10 g hg
  obtain ⟨t1, t2, t3, t4⟩ := zpow2_tb_facts m h7 h10 k
  have hs2 : ∀ a : Fin (m + 1), 8 ≤ a.val → 8 ≤ (σ' a).val := by
    intro a ha
    by_contra hlt
    have hlt := not_le.mp hlt
    have h1 : σ' (σ' a) = σ' a := hσ' _ hlt
    have h2 : σ' a = a := σ'.injective h1
    rw [h2] at hlt
    omega
  refine ⟨fun a => ?_, fun a => ?_, fun h0 hS => ?_⟩
  · by_cases ha : a.val < 8
    · rw [Perm.mul_apply, hσ' a ha]
      have := t1 a ha
      omega
    · have ha := not_lt.mp ha
      rw [Perm.mul_apply, t2 _ (hs2 a ha)]
      have := hs2 a ha
      omega
  · by_cases ha : a.val < 8
    · rw [Perm.mul_apply, hσ' a ha]
      exact t3 a ha
    · have ha := not_lt.mp ha
      rw [Perm.mul_apply, t2 _ (hs2 a ha)]
      have := hs2 a ha
      omega
  · have h00 : σ' (pt m 0) = pt m 0 := hσ' _ (by rw [pt_val_zero m]; omega)
    rw [Perm.mul_apply, h00] at h0
    have ht1 := t4 h0
    rw [ht1, one_mul]
    rw [ht1, one_mul] at hS
    refine Equiv.ext fun a => ?_
    by_cases ha : a.val < 8
    · exact hσ' a ha
    · have ha := not_lt.mp ha
      exact hS a ha

private theorem card_perm_S :
    Nat.card (Perm {a : Fin (m + 1) // 8 ≤ a.val}) = (m - 7)! := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have : Fintype.card {a : Fin (m + 1) // 8 ≤ a.val} = m - 7 := by
    interval_cases m <;> decide
  rw [this]

private theorem card_perm_T :
    Nat.card (Perm {a : Fin (m + 1) // a.val < 2}) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have : Fintype.card {a : Fin (m + 1) // a.val < 2} = 2 := by
    interval_cases m <;> decide
  rw [this]
  rfl

private theorem exists_inj (P : Subgroup (Perm (Fin (m + 1))))
    (hc : ∀ g ∈ P, ∀ q ∈ ({ub m, vb m, xb1 m, xb2 m, tb m} : Set (Perm (Fin (m + 1)))),
      g * q = q * g) :
    ∃ (ψS : ↥P →* Perm {a : Fin (m + 1) // 8 ≤ a.val})
      (ψT : ↥P →* Perm {a : Fin (m + 1) // a.val < 2}), Function.Injective (ψS.prod ψT) := by
  have hgood := fun g (hg : g ∈ P) => good_of_cent m h7 h10 g (hc g hg)
  obtain ⟨ψS, hψS⟩ := exists_resHom P (fun a : Fin (m + 1) => 8 ≤ a.val)
    (fun g hg a => (hgood g hg).1 a)
  obtain ⟨ψT, hψT⟩ := exists_resHom P (fun a : Fin (m + 1) => a.val < 2)
    (fun g hg a => (hgood g hg).2.1 a)
  have hinj : Function.Injective (ψS.prod ψT) := by
    rw [injective_iff_map_eq_one]
    intro g hg1
    rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hg1
    obtain ⟨hS1, hT1⟩ := hg1
    have hS : ∀ a : Fin (m + 1), 8 ≤ a.val → (g : Perm (Fin (m + 1))) a = a := by
      intro a ha
      have := hψS g ⟨a, ha⟩
      rw [hS1] at this
      exact this.symm
    have h0 : (g : Perm (Fin (m + 1))) (pt m 0) = pt m 0 := by
      have hl : (pt m 0).val < 2 := by rw [pt_val_zero m]; omega
      have := hψT g ⟨pt m 0, hl⟩
      rw [hT1] at this
      exact this.symm
    exact Subtype.ext ((hgood g g.2).2.2 h0 hS)
  exact ⟨ψS, ψT, hinj⟩

theorem card_dvd_cent_Qbar (P : Subgroup (Perm (Fin (m + 1))))
    (hc : ∀ g ∈ P, ∀ q ∈ ({ub m, vb m, xb1 m, xb2 m, tb m} : Set (Perm (Fin (m + 1)))),
      g * q = q * g) :
    Nat.card P ∣ (m - 7)! * 2 := by
  obtain ⟨ψS, ψT, hinj⟩ := exists_inj m h7 h10 P hc
  have := Subgroup.card_dvd_of_injective (ψS.prod ψT) hinj
  rwa [Nat.card_prod, card_perm_S m h7 h10, card_perm_T m h7 h10] at this

end Qbar

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
