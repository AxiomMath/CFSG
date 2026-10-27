module

public import CFSG.ClassicalInvolution.Asc77.AscT7G2Idx4
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Bsub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7G2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


section Frat

open T7F2

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem inf_R_R'_eq : R ⊓ R' = Subgroup.zpowers z := by
  have hzmem : z ∈ R ⊓ R' := Subgroup.mem_inf.mpr ⟨h.hzR.mem, h.hzR'.mem⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzmem) ?_).symm
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  rw [Nat.card_zpowers, hz2, h.inf_R_R']

theorem eq_one_or_z_of_mem_zpowers {w : G} (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, hk⟩ := hw
  simp only at hk
  subst hk
  have hzz : z * z = 1 := h.hz.sq
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  obtain ⟨m, hm⟩ := Int.even_or_odd' k
  rcases hm with rfl | rfl
  · left
    rw [zpow_mul, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

theorem exists_conj_form {y w : G} (hw : w ∈ R ⊔ R') (hy : y = w * t') (hy2 : y * y = 1) :
    ∃ q ∈ R, y = q * t' * q⁻¹ ∨ y = q * t' * q⁻¹ * z := by
  have ht2 := h.ht'2
  have hti := h.ht'inv
  obtain ⟨q, hq, q', hq', rfl⟩ := Out.exists_mul_of_mem_sup_of_commute h.hcomm hw
  subst hy
  have hq''R : t' * q' * t' ∈ R := by
    have := conj_mem_conjSub (n := t') hq'
    rw [h.ht'R', hti] at this
    exact this
  have hqsR' : t' * q * t' ∈ R' := by
    have := conj_mem_conjSub (n := t') hq
    rw [h.ht'R, hti] at this
    exact this
  have hc2 : (t' * q' * t') * q' = q' * (t' * q' * t') := h.hcomm _ hq''R q' hq'
  have hc3 : (t' * q' * t') * (t' * q * t') = (t' * q * t') * (t' * q' * t') :=
    h.hcomm _ hq''R _ hqsR'
  have e1 : (q * q' * t') * (q * q' * t') = q * q' * ((t' * q * t') * (t' * q' * t')) := by
    calc (q * q' * t') * (q * q' * t') = q * q' * (t' * q * q' * t') := by group
      _ = q * q' * (t' * q * (t' * t') * q' * t') := by rw [ht2, mul_one]
      _ = q * q' * ((t' * q * t') * (t' * q' * t')) := by group
  have e2 : q * q' * ((t' * q * t') * (t' * q' * t')) =
      (q * (t' * q' * t')) * (q' * (t' * q * t')) := by
    calc q * q' * ((t' * q * t') * (t' * q' * t'))
        = q * (q' * ((t' * q * t') * (t' * q' * t'))) := by group
      _ = q * (q' * ((t' * q' * t') * (t' * q * t'))) := by rw [← hc3]
      _ = q * ((q' * (t' * q' * t')) * (t' * q * t')) := by group
      _ = q * (((t' * q' * t') * q') * (t' * q * t')) := by rw [← hc2]
      _ = (q * (t' * q' * t')) * (q' * (t' * q * t')) := by group
  have hab : (q * (t' * q' * t')) * (q' * (t' * q * t')) = 1 := by rw [← e2, ← e1]; exact hy2
  have ha₁ : q * (t' * q' * t') ∈ R ⊓ R' := by
    refine Subgroup.mem_inf.mpr ⟨R.mul_mem hq hq''R, ?_⟩
    have : q * (t' * q' * t') = (q' * (t' * q * t'))⁻¹ := eq_inv_of_mul_eq_one_left hab
    rw [this]
    exact R'.inv_mem (R'.mul_mem hq' hqsR')
  have hq'eq : q' = t' * (t' * q' * t') * t' := by
    calc q' = (t' * t') * q' * (t' * t') := by rw [ht2]; group
      _ = t' * (t' * q' * t') * t' := by group
  refine ⟨q, hq, ?_⟩
  rcases eq_one_or_z_of_mem_zpowers h (by rw [← inf_R_R'_eq h]; exact ha₁) with h0 | h0
  · left
    have hq'' : t' * q' * t' = q⁻¹ := eq_inv_of_mul_eq_one_right h0
    rw [hq''] at hq'eq
    rw [hq'eq]
    calc q * (t' * q⁻¹ * t') * t' = q * t' * q⁻¹ * (t' * t') := by group
      _ = q * t' * q⁻¹ := by rw [ht2, mul_one]
  · right
    have hq'' : t' * q' * t' = q⁻¹ * z := by
      rw [← h0]; group
    rw [hq''] at hq'eq
    rw [hq'eq]
    calc q * (t' * (q⁻¹ * z) * t') * t' = q * t' * q⁻¹ * z * (t' * t') := by group
      _ = q * t' * q⁻¹ * z := by rw [ht2, mul_one]


variable (h11 : C25_11 p f) (h16 : C25_16 p f)
  (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R'))

include h11 h16 h4

theorem commutator_mem_RR {x : G} (hx : x ∈ (S : Subgroup G)) :
    x⁻¹ * t' * x * t'⁻¹ ∈ R ⊔ R' := by
  obtain ⟨-, -, -, -, hidx⟩ := struct h h11 h16 h4
  have ht2 := h.ht'2
  have hti := h.ht'inv
  have hN : ∀ n ∈ Nsub S R, n⁻¹ * t' * n * t'⁻¹ ∈ R ⊔ R' := by
    intro n hn
    have hy : t' * n * t'⁻¹ ∈ Nsub S R := h.N_conj hn
    have hinv : n⁻¹ ∈ Nsub S R := (Nsub S R).inv_mem hn
    have hiff : (n⁻¹ ∈ R ⊔ R' ↔ t' * n * t'⁻¹ ∈ R ⊔ R') := by
      constructor
      · intro h1
        have h2 : n ∈ R ⊔ R' := by simpa using (R ⊔ R').inv_mem h1
        exact conj_mem_RR h h.ht'S h2
      · intro h1
        have h2 := conj_mem_RR h h.ht'S h1
        have e : t' * (t' * n * t'⁻¹) * t'⁻¹ = n := by
          calc t' * (t' * n * t'⁻¹) * t'⁻¹ = (t' * t') * n * (t'⁻¹ * t'⁻¹) := by group
            _ = n := by rw [ht2, hti, ht2]; group
        rw [e] at h2
        exact (R ⊔ R').inv_mem h2
    have key := (mul_mem_iff_of_relIndex_two hidx hinv hy).mpr hiff
    have e : n⁻¹ * (t' * n * t'⁻¹) = n⁻¹ * t' * n * t'⁻¹ := by group
    rw [e] at key
    exact key
  rcases h.S_cover hx with hxN | htxN
  · exact hN x hxN
  · have := hN (t' * x) htxN
    have e : (t' * x)⁻¹ * t' * (t' * x) * t'⁻¹ = x⁻¹ * t' * x * t'⁻¹ := by group
    rw [e] at this
    exact this

variable {g : G} (hg : g * z * g⁻¹ = t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z)

include hg hnf

theorem exists_mul_centralizer {x : G} (hx : x ∈ (S : Subgroup G)) :
    ∃ c ∈ (S : Subgroup G), c * t' = t' * c ∧ ∃ q ∈ R, x = c * q⁻¹ := by
  have ht2 := h.ht'2
  have hti := h.ht'inv
  have hw := commutator_mem_RR h h11 h16 h4 hx
  have hy2 : (x⁻¹ * t' * x) * (x⁻¹ * t' * x) = 1 := by
    calc (x⁻¹ * t' * x) * (x⁻¹ * t' * x) = x⁻¹ * (t' * t') * x := by group
      _ = 1 := by rw [ht2]; group
  have hy : x⁻¹ * t' * x = (x⁻¹ * t' * x * t'⁻¹) * t' := by group
  obtain ⟨q, hq, hcase⟩ := exists_conj_form h hw hy hy2
  have hqS : q ∈ (S : Subgroup G) := h.hRS hq
  have hxqS : x * q ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hx hqS
  have hxq : x = (x * q) * q⁻¹ := by group
  rcases hcase with h0 | h0
  · refine ⟨x * q, hxqS, ?_, q, hq, hxq⟩
    calc x * q * t' = x * (q * t' * q⁻¹) * q := by group
      _ = x * (x⁻¹ * t' * x) * q := by rw [← h0]
      _ = t' * (x * q) := by group
  · exfalso
    apply hnf
    refine ⟨(x * q)⁻¹ * g, ?_⟩
    have hzq : q⁻¹ * z * q = z := by
      have := h.hyp.hzS q hqS
      calc q⁻¹ * z * q = q⁻¹ * (z * q) := by group
        _ = q⁻¹ * (q * z) := by rw [this]
        _ = z := by group
    calc (x * q)⁻¹ * g * z * ((x * q)⁻¹ * g)⁻¹ = (x * q)⁻¹ * (g * z * g⁻¹) * (x * q) := by group
      _ = (x * q)⁻¹ * t' * (x * q) := by rw [hg]
      _ = q⁻¹ * (x⁻¹ * t' * x) * q := by group
      _ = q⁻¹ * (q * t' * q⁻¹ * z) * q := by rw [h0]
      _ = t' * (q⁻¹ * z * q) := by group
      _ = t' * z := by rw [hzq]

theorem exists_s : ∃ s ∈ Nsub S R, s ∉ R ⊔ R' ∧ s * t' = t' * s := by
  obtain ⟨-, -, -, -, hidx⟩ := struct h h11 h16 h4
  have hRRN : R ⊔ R' ≤ Nsub S R := sup_le h.R_le_N h.R'_le_N
  have hex : ∃ x₀ ∈ Nsub S R, x₀ ∉ R ⊔ R' := by
    by_contra hcon
    push Not at hcon
    have h1 : Nsub S R ≤ R ⊔ R' := fun x hx => hcon x hx
    have := Subgroup.relIndex_eq_one.mpr h1
    omega
  obtain ⟨x₀, hx₀N, hx₀⟩ := hex
  obtain ⟨c, hcS, hct, q, hq, hxq⟩ := exists_mul_centralizer h h11 h16 h4 hg hnf
    (mem_Nsub.mp hx₀N).1
  have hqN : q ∈ Nsub S R := h.R_le_N hq
  have hcN : c ∈ Nsub S R := by
    have e : c = x₀ * q := by rw [hxq]; group
    rw [e]
    exact (Nsub S R).mul_mem hx₀N hqN
  refine ⟨c, hcN, fun hc => hx₀ ?_, hct⟩
  rw [hxq]
  exact (R ⊔ R').mul_mem hc ((R ⊔ R').inv_mem ((le_sup_left : R ≤ R ⊔ R') hq))

end Frat

end T7G2

end CFSG.ClassicalInvolution.Asc77
