module

public import Certificates.Certificate27273
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CountBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model

public section

namespace CFSG.EvenSporadicStandard.HSStd.U43

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore
  CFSG.EvenSporadicStandard.M24Std.CU43

theorem card_inf_centralizer_eq_comm_of (H : Subgroup (Equiv.Perm (Fin 820)))
    (y : Equiv.Perm (Fin 820)) :
    Nat.card ↥(H ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card {g : H // (g : Equiv.Perm (Fin 820)) * y = y * g} := by
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, by
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
      invFun := fun y' => ⟨y'.1.1, mem_inf.2 ⟨y'.1.2, mem_centralizer_singleton_iff.2 y'.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y' => rfl }

theorem cosetCheck8_facts :
    dihedralCheck = true ∧ centCosetCounts = true := by
  have h := Certificates.certificate27273
  simpa only [cosetCheck8, Bool.and_eq_true] using h

theorem mulIdx_lt (k k' : ℕ) : mulIdx k k' < 8 := by
  unfold mulIdx
  split_ifs <;> omega

theorem tP_mul_mulIdx {k k' : ℕ}
    (hk : k < 8) (hk' : k' < 8) : tP k * tP k' = tP (mulIdx k k') := by
  have h := cosetCheck8_facts.1
  simp only [dihedralCheck, List.all_eq_true, List.mem_range] at h
  exact (eqA_iff (rep_compA (rep_tArr k) (rep_tArr k')) (rep_tArr _)).1 (h k hk k' hk')

theorem card_comm_cos8
    {k : ℕ} (hk : k < 8) :
    Nat.card {g : P // (g : Equiv.Perm (Fin 820)) * tP k * rP 8 =
      rP 8 * ((g : Equiv.Perm (Fin 820)) * tP k)} = 720 := by
  have h := cosetCheck8_facts.2
  simp only [centCosetCounts, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [card_eq_countW_P (f := commW (tArr k) [reps[8]!])
    (Pr := fun g => g * tP k * rP 8 = rP 8 * (g * tP k))]
  · exact h k hk
  · intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
    exact allLt_comm_iff hH (rep_rP (by norm_num : 8 < 9))

open Classical in
@[expose] noncomputable def cosSet (X' : Subgroup (Equiv.Perm (Fin 820))) : Finset ℕ :=
  (Finset.range 8).filter fun k => tP k ∈ X'

theorem mem_cosSet {X' : Subgroup (Equiv.Perm (Fin 820))} {k : ℕ} :
    k ∈ cosSet X' ↔ k < 8 ∧ tP k ∈ X' := by
  simp [cosSet]

section Between

variable
  {X' : Subgroup (Equiv.Perm (Fin 820))}

theorem mem_iff_cosSet (hP : P ≤ X') (hR : X' ≤ R) {x : Equiv.Perm (Fin 820)} :
    x ∈ X' ↔ ∃ g ∈ P, ∃ k ∈ cosSet X', x = g * tP k := by
  constructor
  · intro hx
    obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 (hR hx)
    refine ⟨g, hg, k, mem_cosSet.2 ⟨hk, ?_⟩, rfl⟩
    have := X'.mul_mem (X'.inv_mem (hP hg)) hx
    simpa using this
  · rintro ⟨g, hg, k, hk, rfl⟩
    exact X'.mul_mem (hP hg) (mem_cosSet.1 hk).2

theorem cosSet_unique {g g' : Equiv.Perm (Fin 820)} (hg : g ∈ P) (hg' : g' ∈ P) {k k' : ℕ}
    (hk : k < 8) (hk' : k' < 8) (h : g * tP k = g' * tP k') : k = k' ∧ g = g' := by
  have hkk : k = k' := by
    by_contra hne
    apply tP_mul_inv_not_mem hk hk' hne
    have : tP k * (tP k')⁻¹ = g⁻¹ * g' := by
      calc tP k * (tP k')⁻¹ = g⁻¹ * (g * tP k) * (tP k')⁻¹ := by group
        _ = g⁻¹ * (g' * tP k') * (tP k')⁻¹ := by rw [h]
        _ = g⁻¹ * g' := by group
    rw [this]
    exact P.mul_mem (P.inv_mem hg) hg'
  subst hkk
  exact ⟨rfl, mul_right_cancel h⟩

theorem card_filter_cos (hP : P ≤ X') (hR : X' ≤ R) (Q : Equiv.Perm (Fin 820) → Prop) :
    Nat.card {x : X' // Q x} = ∑ k ∈ cosSet X', Nat.card {g : P // Q (g * tP k)} := by
  classical
  let F : (Σ k : ↥(cosSet X'), {g : P // Q (g * tP k)}) → {x : X' // Q x} := fun s =>
    ⟨⟨(s.2.1 : Equiv.Perm (Fin 820)) * tP s.1,
      (mem_iff_cosSet hP hR).2 ⟨s.2.1, s.2.1.2, s.1, s.1.2, rfl⟩⟩, s.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨k, hk⟩, ⟨g, hgQ⟩⟩ ⟨⟨k', hk'⟩, ⟨g', hgQ'⟩⟩ h
      have h1 : (g : Equiv.Perm (Fin 820)) * tP k = (g' : Equiv.Perm (Fin 820)) * tP k' :=
        congrArg (fun x : {x : X' // Q x} => (x.1 : Equiv.Perm (Fin 820))) h
      obtain ⟨rfl, hgg⟩ := cosSet_unique g.2 g'.2 (mem_cosSet.1 hk).1 (mem_cosSet.1 hk').1 h1
      have : g = g' := Subtype.ext hgg
      subst this
      rfl
    · rintro ⟨⟨x, hx⟩, hxQ⟩
      obtain ⟨g, hg, k, hk, rfl⟩ := (mem_iff_cosSet hP hR).1 hx
      exact ⟨⟨⟨k, hk⟩, ⟨⟨g, hg⟩, hxQ⟩⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_sigma]
  exact Finset.sum_coe_sort (cosSet X') (fun k => Nat.card {g : P // Q (g * tP k)})

theorem card_eq_cosSet (hP : P ≤ X') (hR : X' ≤ R) :
    Nat.card X' = Nat.card P * (cosSet X').card := by
  have h := card_filter_cos hP hR (fun _ => True)
  have e1 : Nat.card {x : X' // True} = Nat.card X' := Nat.card_congr (Equiv.subtypeUnivEquiv
    fun _ => trivial)
  have e2 : Nat.card {g : P // True} = Nat.card P :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  rw [e1] at h
  rw [h, Finset.sum_congr rfl fun _ _ => e2, Finset.sum_const, smul_eq_mul, mul_comm]

theorem cosSet_closed {a b : ℕ} (ha : a ∈ cosSet X')
    (hb : b ∈ cosSet X') : mulIdx a b ∈ cosSet X' := by
  obtain ⟨ha8, haX⟩ := mem_cosSet.1 ha
  obtain ⟨hb8, hbX⟩ := mem_cosSet.1 hb
  refine mem_cosSet.2 ⟨mulIdx_lt a b, ?_⟩
  rw [← tP_mul_mulIdx ha8 hb8]
  exact X'.mul_mem haX hbX

theorem card_inf_centralizer_rP8 (hP : P ≤ X') (hR : X' ≤ R) :
    Nat.card ↥(X' ⊓ centralizer ({rP 8} : Set (Equiv.Perm (Fin 820)))) =
      720 * (cosSet X').card := by
  rw [card_inf_centralizer_eq_comm_of, card_filter_cos hP hR (fun x => x * rP 8 = rP 8 * x)]
  rw [Finset.sum_congr rfl fun k hk => card_comm_cos8 (mem_cosSet.1 hk).1, Finset.sum_const,
    smul_eq_mul, mul_comm]

end Between

theorem cosSet_cases (K : Finset ℕ) (hK8 : ∀ k ∈ K, k < 8) (h0 : 0 ∈ K) (h2 : 2 ∈ K)
    (hcl : ∀ a ∈ K, ∀ b ∈ K, mulIdx a b ∈ K) (hcard : K.card = 4) :
    K = {0, 2, 4, 6} ∨ K = {0, 1, 2, 3} ∨ K = {0, 2, 5, 7} := by
  have hlt : ({0, 2} : Finset ℕ).card < K.card := by rw [hcard]; decide
  obtain ⟨a, haK, haN⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have ha8 := hK8 a haK
  have hsub : ∀ S : Finset ℕ, S ⊆ K → S.card = 4 → K = S := fun S hS hSc =>
    (Finset.eq_of_subset_of_card_le hS (by rw [hSc, hcard])).symm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haN
  interval_cases a
  · exact absurd rfl haN.1
  · right; left
    have h3 : (3 : ℕ) ∈ K := by simpa [mulIdx] using hcl 1 haK 2 h2
    exact hsub {0, 1, 2, 3} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by decide)
  · exact absurd rfl haN.2
  · right; left
    have h1 : (1 : ℕ) ∈ K := by simpa [mulIdx] using hcl 3 haK 2 h2
    exact hsub {0, 1, 2, 3} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by decide)
  · left
    have h6 : (6 : ℕ) ∈ K := by simpa [mulIdx] using hcl 4 haK 2 h2
    exact hsub {0, 2, 4, 6} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by decide)
  · right; right
    have h7 : (7 : ℕ) ∈ K := by simpa [mulIdx] using hcl 5 haK 2 h2
    exact hsub {0, 2, 5, 7} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by decide)
  · left
    have h4 : (4 : ℕ) ∈ K := by simpa [mulIdx] using hcl 6 haK 2 h2
    exact hsub {0, 2, 4, 6} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by decide)
  · right; right
    have h5 : (5 : ℕ) ∈ K := by simpa [mulIdx] using hcl 7 haK 2 h2
    exact hsub {0, 2, 5, 7} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption) (by decide)

end CFSG.EvenSporadicStandard.HSStd.U43
