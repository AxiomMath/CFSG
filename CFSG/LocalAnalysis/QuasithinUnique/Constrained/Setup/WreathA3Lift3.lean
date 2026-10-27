module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Lift2

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

namespace A3LiftHyp

variable {H Q : Subgroup G} {r : ℕ} {L : Fin r → Subgroup G} (h : A3LiftHyp H Q L)

include h

omit [Finite G] in
theorem two_elt_mem_U (i : Fin r) {x : G} (hx : x ∈ L i) (hx2 : ∃ a : ℕ, x ^ 2 ^ a = 1) :
    x ∈ blockQ (L i) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hx2
  have h3 : ¬ 3 ∣ orderOf x := by
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans (orderOf_dvd_of_pow_eq_one ha))
    omega
  obtain ⟨k, hk⟩ := h.three x (h.L_le i hx)
  have hxQ : x ∈ Q := mem_of_not_dvd_orderOf_of_pow_mem h3 hk
  rw [← h.Q_inf_L i]
  exact ⟨hxQ, hx⟩

theorem inf_L_eq_bot (i j : Fin r) (hij : i ≠ j) : L i ⊓ L j = ⊥ := by
  have hdisj := h.comm_and_disjoint.2.2
  rw [eq_bot_iff]
  rintro z ⟨hzi, hzj⟩
  rw [Subgroup.mem_bot]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  set z' : G := z ^ 2 ^ a with hz'
  have hz'i : z' ∈ L i := (L i).pow_mem hzi _
  have hz'j : z' ∈ L j := (L j).pow_mem hzj _
  have hord : orderOf z' = b := by
    have hdvd : 2 ^ a ∣ orderOf z := ⟨b, hab⟩
    rw [hz', orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hab]
    exact Nat.mul_div_cancel_left b (pow_pos two_pos a)
  have hb1 : b = 1 := by
    by_contra hb1
    have hdvd : b ∣ 12 := by
      rw [← hord, ← h.card_L i]
      exact Subgroup.orderOf_dvd_natCard _ hz'i
    have hb3 : b ∣ 3 := by
      have hcop : Nat.Coprime b 4 := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hb)
      exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
    have hb3' : b = 3 := ((Nat.dvd_prime Nat.prime_three).1 hb3).resolve_left hb1
    have h3i := h.gen3 i hz'i (hord.trans hb3')
    have h3j := h.gen3 j hz'j (hord.trans hb3')
    have hLQ : L j ≤ Q ⊔ L i := by
      rw [h3j]
      refine sup_le ?_ ((h.U_le_Q j).trans le_sup_left)
      exact (Subgroup.zpowers_le.2 hz'i).trans le_sup_right
    have hLQ' : L i ≤ Q ⊔ L j := by
      rw [h3i]
      refine sup_le ?_ ((h.U_le_Q i).trans le_sup_left)
      exact (Subgroup.zpowers_le.2 hz'j).trans le_sup_right
    exact hij (h.inj (le_antisymm (h.L_le_of_le_sup j i hLQ') (h.L_le_of_le_sup i j hLQ)))
  have hz2 : z ^ 2 ^ a = 1 := by
    have : orderOf z' = 1 := hord.trans hb1
    exact orderOf_eq_one_iff.1 this
  have hzi' := h.two_elt_mem_U i hzi ⟨a, hz2⟩
  have hzj' := h.two_elt_mem_U j hzj ⟨a, hz2⟩
  have := hdisj i j hij
  have hmem : z ∈ blockQ (L i) ⊓ blockQ (L j) := ⟨hzi', hzj'⟩
  rw [this] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem L_le_normalizer (i j : Fin r) : L j ≤ normalizer (L i : Set G) := by
  by_cases hij : i = j
  · rw [hij]; exact Subgroup.le_normalizer
  intro y hy
  have hQc := h.comm_and_disjoint.1
  have hY : Q ⊔ L i ≤ normalizer (L i : Set G) :=
    sup_le (h.Q_norm_L i) Subgroup.le_normalizer
  have key : ∀ y ∈ L j, ∀ x ∈ L i, y * x * y⁻¹ ∈ L i := by
    intro y hy x hx
    have hcl := NoPQuotient.closure_eq_ambient (p := 2) (h.short i).1
    rw [← hcl] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      have hxodd : Odd (orderOf x) :=
        Nat.not_even_iff_odd.1 fun he => hx.2 (even_iff_two_dvd.1 he)
      have hc : y * x * y⁻¹ * x⁻¹ ∈ Q := hQc y (h.L_le j hy) x (h.L_le i hx.1)
      have hyx : y * x * y⁻¹ ∈ Q ⊔ L i := by
        have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hx.1)
      have hodd' : Odd (orderOf (y * x * y⁻¹)) := by
        have := orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective x
        have e : (MulAut.conj y).toMonoidHom x = y * x * y⁻¹ := rfl
        rw [e] at this
        rw [this]
        exact hxodd
      exact mem_of_odd_of_sup_eq (Y := Q ⊔ L i) (J := L i) (T := Q) hY le_sup_left h.Q_two
        (by rw [sup_comm]) hyx hodd'
    | one => simp
    | mul a b _ _ ha hb =>
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e]
      exact (L i).mul_mem ha hb
    | inv a _ ha =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact (L i).inv_mem ha
  exact mem_normalizer_of_conj_mem (fun x hx => key y hy x hx)
    (fun x hx => by simpa using key y⁻¹ ((L j).inv_mem hy) x hx)

theorem H_le_normalizer_L (i : Fin r) : H ≤ normalizer (L i : Set G) := by
  rw [h.gen]
  exact sup_le (h.Q_norm_L i) (iSup_le fun j => h.L_le_normalizer i j)

theorem L_commute (i j : Fin r) (hij : i ≠ j) : ⁅L i, L j⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ L i := by
    have := (Subgroup.mem_normalizer_iff.mp (h.L_le_normalizer i j hy) x⁻¹).mp ((L i).inv_mem hx)
    exact this
  have h2 : x * y * x⁻¹ ∈ L j := by
    have := (Subgroup.mem_normalizer_iff.mp (h.L_le_normalizer j i hx) y).mp hy
    exact this
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ L i ⊓ L j := by
    refine ⟨?_, ?_⟩
    · have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact (L i).mul_mem hx h1
    · exact (L j).mul_mem h2 ((L j).inv_mem hy)
  rw [h.inf_L_eq_bot i j hij] at hmem
  have := Subgroup.mem_bot.1 hmem
  calc y * x = (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [this]; group

theorem L_indep : iSupIndep L := by
  intro i
  rw [Subgroup.disjoint_def]
  intro z hzi hzP
  have hcent : (⨆ (j) (_ : j ≠ i), L j) ≤ Subgroup.centralizer (L i : Set G) := by
    refine iSup₂_le fun j hj => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 (h.L_commute i j (Ne.symm hj))
    have h1 := Subgroup.mem_centralizer_iff.1 (this hx) y hy
    exact h1.symm
  have hz : ∀ x ∈ L i, z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (hcent hzP) x hx).symm
  have hzU : z ∈ blockQ (L i) := (h.short i).2.1 ⟨hzi, Subgroup.mem_centralizer_iff.mpr fun u hu =>
    (hz u (U_le_L i hu)).symm⟩
  obtain ⟨c, hc, hord⟩ := h.exists_order3 i
  exact h.fix_eq_one i hc hord hzU (hz c hc).symm

theorem U_indep : iSupIndep (fun i => blockQ (L i)) :=
  h.L_indep.mono fun i => U_le_L i

end A3LiftHyp

end CFSG.QuasithinUnique.Setup.Wreath
