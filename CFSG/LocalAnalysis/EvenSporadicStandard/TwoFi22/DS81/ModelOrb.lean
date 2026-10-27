module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelOrbTrans

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

@[expose] def clsCard (i : Fin 6) : ℕ := i.val / 2 + 1

@[expose] def clsZero (i : Fin 6) : Bool := i.val % 2 == 0

@[expose] def InCls (i : Fin 6) (t : Finset (Fin 23)) : Prop :=
  t.card = clsCard i ∧ ((0 : Fin 23) ∈ t ↔ clsZero i = true)

@[expose] def clsRep : Fin 6 → Finset (Fin 23) :=
  ![{0}, {1}, {0, 1}, {1, 2}, {0, 1, 2}, {1, 2, 3}]

theorem clsCard_le (i : Fin 6) : clsCard i ≤ 3 := by
  revert i
  decide

theorem one_le_clsCard (i : Fin 6) : 1 ≤ clsCard i := Nat.le_add_left 1 _

theorem inCls_rep (i : Fin 6) : InCls i (clsRep i) := by
  unfold InCls
  revert i
  decide

theorem cls_unique {i j : Fin 6} {t : Finset (Fin 23)} (hi : InCls i t) (hj : InCls j t) :
    i = j := by
  have key : ∀ i j : Fin 6, clsCard i = clsCard j → clsZero i = clsZero j → i = j := by decide
  refine key i j (hi.1.symm.trans hj.1) ?_
  have h := hi.2.symm.trans hj.2
  revert h
  cases clsZero i <;> cases clsZero j <;> simp

theorem exists_cls {t : Finset (Fin 23)} (h1 : 1 ≤ t.card) (h3 : t.card ≤ 3) :
    ∃ i, InCls i t := by
  have hc : t.card = 1 ∨ t.card = 2 ∨ t.card = 3 := by omega
  by_cases h0 : (0 : Fin 23) ∈ t <;> rcases hc with hc | hc | hc
  · exact ⟨0, hc, by simp [clsZero, h0]⟩
  · exact ⟨2, hc, by simp [clsZero, h0]⟩
  · exact ⟨4, hc, by simp [clsZero, h0]⟩
  · exact ⟨1, hc, by simp [clsZero, h0]⟩
  · exact ⟨3, hc, by simp [clsZero, h0]⟩
  · exact ⟨5, hc, by simp [clsZero, h0]⟩

def idxP : Finset (Fin 23) := Finset.univ.erase 0

theorem card_idxP : idxP.card = 22 := by decide

theorem ncard_notMem (k : ℕ) :
    {t : Finset (Fin 23) | t.card = k ∧ (0 : Fin 23) ∉ t}.ncard = Nat.choose 22 k := by
  have : {t : Finset (Fin 23) | t.card = k ∧ (0 : Fin 23) ∉ t} = ↑(idxP.powersetCard k) := by
    ext t
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_powersetCard, idxP]
    constructor
    · rintro ⟨hk, h0⟩
      exact ⟨fun x hx => Finset.mem_erase.2 ⟨fun h => h0 (h ▸ hx), Finset.mem_univ x⟩, hk⟩
    · rintro ⟨hsub, hk⟩
      exact ⟨hk, fun h0 => (Finset.mem_erase.1 (hsub h0)).1 rfl⟩
  rw [this, Set.ncard_coe_finset, Finset.card_powersetCard, card_idxP]

theorem ncard_mem (k : ℕ) :
    {t : Finset (Fin 23) | t.card = k + 1 ∧ (0 : Fin 23) ∈ t}.ncard = Nat.choose 22 k := by
  have himg : {t : Finset (Fin 23) | t.card = k + 1 ∧ (0 : Fin 23) ∈ t} =
      (fun u => insert (0 : Fin 23) u) '' ↑(idxP.powersetCard k) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, Finset.mem_powersetCard, idxP]
    constructor
    · rintro ⟨hk, h0⟩
      refine ⟨t.erase 0, ⟨fun x hx => ?_, ?_⟩, Finset.insert_erase h0⟩
      · exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hx).1, Finset.mem_univ x⟩
      · have := Finset.card_erase_add_one h0
        omega
    · rintro ⟨u, ⟨hu, hk⟩, rfl⟩
      have h0u : (0 : Fin 23) ∉ u := fun h => (Finset.mem_erase.1 (hu h)).1 rfl
      exact ⟨by rw [Finset.card_insert_of_notMem h0u, hk], Finset.mem_insert_self _ _⟩
  have hinj : Set.InjOn (fun u => insert (0 : Fin 23) u)
      (↑(idxP.powersetCard k) : Set (Finset (Fin 23))) := by
    intro u hu v hv h
    have hu' : (0 : Fin 23) ∉ u := fun h0 =>
      (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hu).1 h0)).1 rfl
    have hv' : (0 : Fin 23) ∉ v := fun h0 =>
      (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hv).1 h0)).1 rfl
    have h2 := congrArg (fun w => w.erase 0) h
    simpa only [Finset.erase_insert hu', Finset.erase_insert hv'] using h2
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, Finset.card_powersetCard, card_idxP]

theorem ncard_cls (i : Fin 6) :
    {t : Finset (Fin 23) | InCls i t}.ncard = ![1, 22, 22, 231, 231, 1540] i := by
  have h0 : {t : Finset (Fin 23) | InCls 0 t} = {t | t.card = 0 + 1 ∧ (0 : Fin 23) ∈ t} := by
    ext t
    simp [InCls, clsCard, clsZero]
  have h1 : {t : Finset (Fin 23) | InCls 1 t} = {t | t.card = 1 ∧ (0 : Fin 23) ∉ t} := by
    ext t
    simp [InCls, clsCard, clsZero]
  have h2 : {t : Finset (Fin 23) | InCls 2 t} = {t | t.card = 1 + 1 ∧ (0 : Fin 23) ∈ t} := by
    ext t
    simp [InCls, clsCard, clsZero]
  have h3 : {t : Finset (Fin 23) | InCls 3 t} = {t | t.card = 2 ∧ (0 : Fin 23) ∉ t} := by
    ext t
    simp [InCls, clsCard, clsZero]
  have h4 : {t : Finset (Fin 23) | InCls 4 t} = {t | t.card = 2 + 1 ∧ (0 : Fin 23) ∈ t} := by
    ext t
    simp [InCls, clsCard, clsZero]
  have h5 : {t : Finset (Fin 23) | InCls 5 t} = {t | t.card = 3 ∧ (0 : Fin 23) ∉ t} := by
    ext t
    simp [InCls, clsCard, clsZero]
  fin_cases i
  · show {t : Finset (Fin 23) | InCls 0 t}.ncard = ![1, 22, 22, 231, 231, 1540] 0
    rw [h0, ncard_mem]
    decide
  · show {t : Finset (Fin 23) | InCls 1 t}.ncard = ![1, 22, 22, 231, 231, 1540] 1
    rw [h1, ncard_notMem]
    decide
  · show {t : Finset (Fin 23) | InCls 2 t}.ncard = ![1, 22, 22, 231, 231, 1540] 2
    rw [h2, ncard_mem]
    decide
  · show {t : Finset (Fin 23) | InCls 3 t}.ncard = ![1, 22, 22, 231, 231, 1540] 3
    rw [h3, ncard_notMem]
    decide
  · show {t : Finset (Fin 23) | InCls 4 t}.ncard = ![1, 22, 22, 231, 231, 1540] 4
    rw [h4, ncard_mem]
    decide
  · show {t : Finset (Fin 23) | InCls 5 t}.ncard = ![1, 22, 22, 231, 231, 1540] 5
    rw [h5, ncard_notMem]
    decide

theorem inCls_one_iff {t : Finset (Fin 23)} :
    InCls 1 t ↔ ∃ j : Fin 23, j ≠ 0 ∧ t = {j} := by
  have e : InCls 1 t ↔ t.card = 1 ∧ (0 : Fin 23) ∉ t := by
    simp [InCls, clsCard, clsZero]
  rw [e]
  constructor
  · rintro ⟨hc, h0⟩
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hc
    exact ⟨j, fun h => h0 (by rw [h]; exact Finset.mem_singleton_self 0), rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finset.card_singleton j, by simpa using hj.symm⟩

theorem inCls_two_iff {t : Finset (Fin 23)} :
    InCls 2 t ↔ ∃ j : Fin 23, j ≠ 0 ∧ t = {0, j} := by
  have e : InCls 2 t ↔ t.card = 2 ∧ (0 : Fin 23) ∈ t := by
    simp [InCls, clsCard, clsZero]
  rw [e]
  constructor
  · rintro ⟨hc, h0⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
    rcases Finset.mem_insert.1 h0 with h | h
    · subst h
      exact ⟨b, hab.symm, rfl⟩
    · have hb : (0 : Fin 23) = b := Finset.mem_singleton.1 h
      subst hb
      exact ⟨a, hab, Finset.pair_comm a 0⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finset.card_pair hj.symm, Finset.mem_insert_self _ _⟩

section

theorem exists_perm_image_cls {s t : Finset (Fin 23)} (hk : s.card = t.card) (h3 : s.card ≤ 3)
    (h0 : (0 : Fin 23) ∈ s ↔ (0 : Fin 23) ∈ t) :
    ∃ (n : Cd) (σ : Equiv.Perm (Fin 23)), n ∈ normalizer (E0 : Set Cd) ∧ IsPerm n σ ∧
      s.image σ = t := by
  by_cases hs : (0 : Fin 23) ∈ s
  · have ht : (0 : Fin 23) ∈ t := h0.1 hs
    have c1 := Finset.card_erase_add_one hs
    have c2 := Finset.card_erase_add_one ht
    obtain ⟨n, σ, hn, hσ, himg⟩ := exists_perm_image (S := s.erase 0) (S' := t.erase 0)
      (fun j hj => (Finset.mem_erase.1 hj).1) (fun j hj => (Finset.mem_erase.1 hj).1)
      (by omega) (by omega)
    refine ⟨n, σ, hn, hσ, ?_⟩
    calc s.image σ = (insert 0 (s.erase 0)).image σ := by rw [Finset.insert_erase hs]
      _ = insert (σ 0) ((s.erase 0).image σ) := Finset.image_insert _ _ _
      _ = insert 0 (t.erase 0) := by rw [hσ.zero, himg]
      _ = t := Finset.insert_erase ht
  · have ht : (0 : Fin 23) ∉ t := fun h => hs (h0.2 h)
    exact exists_perm_image (fun j hj h => hs (by rw [h] at hj; exact hj))
      (fun j hj h => ht (by rw [h] at hj; exact hj)) hk h3

theorem orbit_clsRep (i : Fin 6) :
    {y : Cd | ∃ n ∈ normalizer (E0 : Set Cd), n * evC (clsRep i) * n⁻¹ = y} =
      {y | ∃ t : Finset (Fin 23), InCls i t ∧ evC t = y} := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_perm hn
    refine ⟨(clsRep i).image σ, ⟨?_, ?_⟩, (hσ.conj_evC _).symm⟩
    · rw [hσ.card_image]
      exact (inCls_rep i).1
    · rw [hσ.zero_mem_image]
      exact (inCls_rep i).2
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨n, σ, hn, hσ, himg⟩ := exists_perm_image_cls (s := clsRep i) (t := t)
      ((inCls_rep i).1.trans ht.1.symm) ((inCls_rep i).1.trans_le (clsCard_le i))
      ((inCls_rep i).2.trans ht.2.symm)
    exact ⟨n, hn, by rw [hσ.conj_evC, himg]⟩

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ Gen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.EvenSporadicStandard.TwoFi22.DS81
