module

public import CFSG.GH74.GLS.Stage1.Thm6.M12Facts.NF

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.M12Facts

open Subgroup CFSG.GH74.GLS.Stage1.Thm6.Sec13

structure NFClosed (P : NF → Prop) : Prop where
  zero : P (0, 0, 0, 0)
  mul : ∀ p q, P p → P q → P (nfMul p q)
  inv : ∀ p, P p → P (nfInv p)

section
variable {G : Type*} [Group G] {S : Subgroup G} {a b y x : G}

@[expose] def nfSub (h : M12Data S a b y x) (P : NF → Prop) (hP : NFClosed P) : Subgroup G where
  carrier := {g | ∃ p, P p ∧ g = nu a b y x p}
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨nfMul p q, hP.mul p q hp hq, nu_mul h p q⟩
  one_mem' := ⟨(0, 0, 0, 0), hP.zero, nu_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨nfInv p, hP.inv p hp, nu_inv h p⟩

variable (h : M12Data S a b y x) {P : NF → Prop} (hP : NFClosed P)

theorem nu_mem_nfSub (p : NF) : nu a b y x p ∈ nfSub h P hP ↔ P p := by
  constructor
  · rintro ⟨q, hq, hpq⟩
    rw [nu_injective h hpq]; exact hq
  · intro hp; exact ⟨p, hp, rfl⟩

theorem nfSub_le_S : nfSub h P hP ≤ S := by
  rintro _ ⟨p, _, rfl⟩
  exact nu_mem h p

theorem nfSub_le_nfSub {P' : NF → Prop} (hP' : NFClosed P') (hle : ∀ p, P p → P' p) :
    nfSub h P hP ≤ nfSub h P' hP' := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, hle p hp, rfl⟩

theorem card_nfSub : Nat.card (nfSub h P hP) = Nat.card {p : NF // P p} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {p : NF // P p} => (⟨nu a b y x p.1, ⟨p.1, p.2, rfl⟩⟩ : nfSub h P hP)) ⟨?_, ?_⟩)
  · intro p q hpq
    exact Subtype.ext (nu_injective h (congrArg Subtype.val hpq))
  · rintro ⟨g, p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

@[expose] def pH0 (p : NF) : Prop := p.2.2.1 = 0 ∧ p.2.2.2 = 0

@[expose] def pU (p : NF) : Prop :=
  p.2.2.1 = 0 ∧ p.2.2.2 = 0 ∧ p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0

@[expose] def pQ0 (p : NF) : Prop := p.2.2.1 = 0

@[expose] def pQ1 (p : NF) : Prop := p.2.2.1 = p.2.2.2

@[expose] def pQ2 (p : NF) : Prop := p.2.2.2 = 0

@[expose] def pR (p : NF) : Prop := (p.1.val + p.2.1.val) % 2 = 0

@[expose] def pD (p : NF) : Prop := p.2.2.1 = 0 ∧ p.2.2.2 = 0 ∧ (p.1.val + p.2.1.val) % 2 = 0

@[expose] def zNF : NF := (2, 2, 0, 0)

instance : DecidablePred pH0 := fun p => by unfold pH0; infer_instance
instance : DecidablePred pU := fun p => by unfold pU; infer_instance
instance : DecidablePred pQ0 := fun p => by unfold pQ0; infer_instance
instance : DecidablePred pQ1 := fun p => by unfold pQ1; infer_instance
instance : DecidablePred pQ2 := fun p => by unfold pQ2; infer_instance
instance : DecidablePred pR := fun p => by unfold pR; infer_instance
instance : DecidablePred pD := fun p => by unfold pD; infer_instance

theorem closed_pH0 : NFClosed pH0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem closed_pU : NFClosed pU :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem closed_pQ0 : NFClosed pQ0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem closed_pQ1 : NFClosed pQ1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem closed_pR : NFClosed pR :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
@[expose] def rootsZ : List NF :=
  [(0, 2, 1, 0), (0, 2, 1, 1), (1, 1, 0, 0), (1, 1, 1, 0), (1, 3, 0, 0), (1, 3, 1, 1),
   (2, 0, 1, 0), (2, 0, 1, 1), (3, 1, 0, 0), (3, 1, 1, 1), (3, 3, 0, 0), (3, 3, 1, 0)]

theorem sq_eq_z_iff : ∀ c : NF, nfMul c c = zNF ↔ c ∈ rootsZ := by decide +kernel

theorem pR_of_mem_rootsZ : ∀ c ∈ rootsZ, pR c := by decide +kernel

theorem pR_gen : ∀ p : NF, pR p → p = (0, 0, 0, 0) ∨ p ∈ rootsZ ∨
    ∃ q ∈ rootsZ, ∃ r ∈ rootsZ, nfMul q r = p := by decide +kernel

theorem zG_eq : a ^ 2 * b ^ 2 = nu a b y x zNF := by simp [nu, zNF]

theorem H0_eq : Subgroup.closure ({a, b} : Set G) = nfSub h pH0 closed_pH0 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(1, 0, 0, 0), by decide, by simp [nu]⟩
    · exact ⟨(0, 1, 0, 0), by decide, by simp [nu]⟩
  · rintro _ ⟨p, hp, rfl⟩
    have h0 : p.2.2.1 = 0 := hp.1
    have h1 : p.2.2.2 = 0 := hp.2
    simp only [nu, h0, h1, Fin.val_zero, pow_zero, mul_one]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem U_eq : Subgroup.closure ({a * a, b * b} : Set G) = nfSub h pU closed_pU := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(2, 0, 0, 0), by decide, by simp [nu, pow_two]⟩
    · exact ⟨(0, 2, 0, 0), by decide, by simp [nu, pow_two]⟩
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨h0, h1, hi, hj⟩ := hp
    have ea : a ^ p.1.val = (a * a) ^ (p.1.val / 2) := by
      rw [← pow_two, ← pow_mul]; congr 1; omega
    have eb : b ^ p.2.1.val = (b * b) ^ (p.2.1.val / 2) := by
      rw [← pow_two, ← pow_mul]; congr 1; omega
    simp only [nu, h0, h1, Fin.val_zero, pow_zero, mul_one, ea, eb]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

theorem R_eq : Subgroup.closure {c : G | c ∈ S ∧ c * c = a ^ 2 * b ^ 2} =
    nfSub h pR closed_pR := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro c ⟨hcS, hcz⟩
    obtain ⟨p, rfl⟩ := exists_nf h hcS
    rw [nu_mul h, zG_eq] at hcz
    exact ⟨p, pR_of_mem_rootsZ p ((sq_eq_z_iff p).1 (nu_injective h hcz)), rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hroot : ∀ c ∈ rootsZ, nu a b y x c ∈
        Subgroup.closure {c : G | c ∈ S ∧ c * c = a ^ 2 * b ^ 2} := by
      intro c hc
      refine Subgroup.subset_closure ⟨nu_mem h c, ?_⟩
      rw [nu_mul h, zG_eq, (sq_eq_z_iff c).2 hc]
    rcases pR_gen p hp with rfl | hp1 | ⟨q, hq, r, hr, rfl⟩
    · rw [nu_zero]; exact one_mem _
    · exact hroot p hp1
    · rw [← nu_mul h]
      exact mul_mem (hroot q hq) (hroot r hr)

theorem conj_mem_nfSub {P : NF → Prop} (hP : NFClosed P)
    (hc : ∀ p q, P q → P (nfMul (nfMul p q) (nfInv p))) :
    ∀ s ∈ S, ∀ r ∈ nfSub h P hP, s * r * s⁻¹ ∈ nfSub h P hP := by
  intro s hs r hr
  obtain ⟨p, rfl⟩ := exists_nf h hs
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨_, hc p q hq, ?_⟩
  rw [← nu_mul h, ← nu_mul h, nu_inv h]

theorem exists_cyc_nfSub {P : NF → Prop} (hP : NFClosed P) (b₀ : NF)
    (hb : ∀ p, ¬ P p → P (nfMul (nfInv b₀) p)) :
    nu a b y x b₀ ∈ S ∧ ∀ t ∈ S, ∃ k : ℤ, ((nu a b y x b₀) ^ k)⁻¹ * t ∈ nfSub h P hP := by
  refine ⟨nu_mem h b₀, fun t ht => ?_⟩
  obtain ⟨p, rfl⟩ := exists_nf h ht
  by_cases hp : P p
  · exact ⟨0, by rw [zpow_zero, inv_one, one_mul]; exact ⟨p, hp, rfl⟩⟩
  · refine ⟨1, ?_⟩
    rw [zpow_one, nu_inv h, nu_mul h]
    exact ⟨_, hb p hp, rfl⟩

theorem conj_pH0 : ∀ p q : NF, pH0 q → pH0 (nfMul (nfMul p q) (nfInv p)) := by decide +kernel
theorem conj_pU : ∀ p q : NF, pU q → pU (nfMul (nfMul p q) (nfInv p)) := by decide +kernel
theorem conj_pQ0 : ∀ p q : NF, pQ0 q → pQ0 (nfMul (nfMul p q) (nfInv p)) := by decide +kernel
theorem conj_pQ1 : ∀ p q : NF, pQ1 q → pQ1 (nfMul (nfMul p q) (nfInv p)) := by decide +kernel

@[expose] def nfPow (p : NF) : ℕ → NF
  | 0 => (0, 0, 0, 0)
  | n + 1 => nfMul (nfPow p n) p

include h in
theorem nu_pow (p : NF) (n : ℕ) : nu a b y x p ^ n = nu a b y x (nfPow p n) := by
  induction n with
  | zero => simp [nfPow, nu_zero]
  | succ n ih => rw [pow_succ, ih, nu_mul h]; rfl

end

end CFSG.GH74.GLS.Stage1.Thm6.M12Facts
