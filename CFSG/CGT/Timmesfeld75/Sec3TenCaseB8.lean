module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB7

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem mem_normalizer_of_commute {K : Subgroup G} {e : G} (h : ∀ y ∈ K, e * y = y * e) :
    e ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [mul_inv_eq_iff_eq_mul.2 (h x hx)]
    exact hx
  · intro hx
    have h1 := h _ hx
    have : x = e * x * e⁻¹ := by
      have h2 : e⁻¹ * (e * x * e⁻¹) * e = e * x * e⁻¹ := by
        calc e⁻¹ * (e * x * e⁻¹) * e = e⁻¹ * ((e * x * e⁻¹) * e) := by group
          _ = e⁻¹ * (e * (e * x * e⁻¹)) := by rw [← h1]
          _ = e * x * e⁻¹ := by group
      calc x = e⁻¹ * (e * x * e⁻¹) * e := by group
        _ = e * x * e⁻¹ := h2
    rw [this]
    exact hx

theorem Sec3.false_of_caseB [Finite G] [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput) (hExc : Sec3TenExceptional)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (hD : Sec3Dih T T₁ n) {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    (hgB : ∃ x ∈ conjSubgroup g (normIn T₁ T), ∃ l ∈ normIn T T₁, x * l ≠ l * x) : False := by
  obtain ⟨a, u, ha, ha1, hu, hvals, hnc⟩ := hS.exists_a hn hn3 hD hg hgB
  have hLa := hS.isLElt_conj hg ha ha1
  have haN : a ∈ Subgroup.normalizer (T : Set G) := hLa.transv.1
  have haa : a * a = 1 := hLa.transv.2.1
  have haL : ∀ t ∈ T, ⁅t, a⁆ ∈ normIn T T₁ := fun t ht => by
    rcases hvals t ht with h0 | h0
    · rw [h0]
      exact (normIn T T₁).one_mem
    · rw [h0]
      exact hu
  have haNL : a ∈ Subgroup.normalizer (normIn T T₁ : Set G) :=
    mem_normalizer_of_values haa haL (normIn_le T T₁)
  let Nsub : Subgroup G :=
    Subgroup.normalizer (T : Set G) ⊓ Subgroup.normalizer (normIn T T₁ : Set G)
  have hL₁N : normIn T₁ T ≤ Nsub := by
    intro e he
    refine ⟨(mem_normIn.1 he).2, mem_normalizer_of_commute fun l hl => ?_⟩
    exact (hS.cfg.comm_L_L₁ hl he).symm
  have haA : Subgroup.zpowers a ≤ Nsub := Subgroup.zpowers_le.2 ⟨haN, haNL⟩
  obtain ⟨k, hkN, S, hS2, hSN, hAS, hBS⟩ := exists_two_group_conj_le
    (isPGroup_two_zpowers_of_mul_self haa)
    (isPGroup_two_of_isElemAbelian (isElemAbelian_of_le hS.cfg.wc₁.1 (normIn_le T₁ T)))
    haA hL₁N
  have hkT : k ∈ Subgroup.normalizer (T : Set G) := (hkN : k ∈ Nsub).1
  have hkL : k ∈ Subgroup.normalizer (normIn T T₁ : Set G) := (hkN : k ∈ Nsub).2
  have hLk : conjSubgroup k (normIn T T₁) = normIn T T₁ :=
    mem_normalizer_iff_conjSubgroup_eq.1 hkL
  have hS' := hS.conj_of_mem_normalizer hkT
  have hD' := hD.conj_of_mem_normalizer hkT
  have hL' : normIn T (conjSubgroup k T₁) = normIn T T₁ := by
    rw [normIn_conj_left_of_mem_normalizer hkT T₁, hLk]
  have hL₁' : normIn (conjSubgroup k T₁) T = conjSubgroup k (normIn T₁ T) :=
    normIn_conj_right_of_mem_normalizer hkT T₁
  have hg' : g * k⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer _).mul_mem hg ((Subgroup.normalizer _).inv_mem hkT)
  refine hS'.false_of_caseB_core h214 hInv hSz hExc hnab hn hn3 hD' (S := S) hS2
    (fun x hx => (hSN hx).1) (by rw [hL']; exact fun x hx => (hSN hx).2)
    (by rw [hL₁']; exact hBS) hg' ?_ ha1 (by rw [hL']; exact hu) hvals
    (hAS (Subgroup.mem_zpowers a)) (by rw [hL']; exact hnc)
  rw [hL₁', conjSubgroup_conjSubgroup, show g * k⁻¹ * k = g by group]
  exact ha

end CFSG.CGT.Timmesfeld75
