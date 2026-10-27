module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalData
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalInputs

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem sq_mem_C_of_mem_D_conj (hσ : σ.IsValid) (Δ : Data σ r) (i : Fin 3) {z : G}
    (hz : z ∈ conjSub (Δ.a ^ (i : ℕ)) σ.D) : z * z ∈ σ.C := by
  obtain ⟨d', hd', rfl⟩ := hz
  have hd'N : d' ∈ σ.N := σ.D_le_N hσ hd'
  have hdx : d' * σ.x * d'⁻¹ = σ.x := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hd'N, mul_inv_cancel_right]
  have hsq : d' * d' ∈ σ.C := by
    apply mem_C_of_conj
    · calc d' * d' * σ.x * (d' * d')⁻¹ = d' * (d' * σ.x * d'⁻¹) * d'⁻¹ := by group
        _ = σ.x := by rw [hdx, hdx]
    · obtain ⟨j, hj⟩ := exists_conj_xs_eq hσ hd'.2 1
      have hj' : d' * σ.x₂ * d'⁻¹ = σ.xs j := hj
      match j, hj' with
      | 0, hj' =>
        exfalso
        apply hσ.x_ne_x₂
        have : d' * σ.x₂ * d'⁻¹ = d' * σ.x * d'⁻¹ := by rw [hj', hdx]; rfl
        simpa using this.symm
      | 1, hj' =>
        calc d' * d' * σ.x₂ * (d' * d')⁻¹ = d' * (d' * σ.x₂ * d'⁻¹) * d'⁻¹ := by group
          _ = σ.x₂ := by rw [hj']; exact hj'
      | 2, hj' =>
        have h3 : d' * σ.xs 2 * d'⁻¹ = σ.x₂ := by
          change d' * (σ.x * σ.x₂) * d'⁻¹ = σ.x₂
          calc d' * (σ.x * σ.x₂) * d'⁻¹ = (d' * σ.x * d'⁻¹) * (d' * σ.x₂ * d'⁻¹) := by group
            _ = σ.x * (σ.x * σ.x₂) := by rw [hdx, hj']; rfl
            _ = σ.x₂ := by rw [← mul_assoc, x_mul_x hσ, one_mul]
        calc d' * d' * σ.x₂ * (d' * d')⁻¹ = d' * (d' * σ.x₂ * d'⁻¹) * d'⁻¹ := by group
          _ = σ.x₂ := by rw [hj', h3]
  set f := (MulAut.conj (Δ.a ^ (i : ℕ))).toMonoidHom
  have e : f d' * f d' = f (d' * d') := (map_mul _ _ _).symm
  rw [e, ← conjSub_a_pow_C Δ (i : ℕ)]
  exact ⟨d' * d', hsq, rfl⟩

@[expose] def Data.swapQ (hσ : σ.IsValid) (Δ : Data σ r) : Data σ r where
  prime := Δ.prime
  ne_two := Δ.ne_two
  dvd := Δ.dvd
  exceptional := Δ.exceptional
  totallyInverted := Δ.totallyInverted
  a := Δ.a
  a_mem := Δ.a_mem
  a_three := Δ.a_three
  a_cycle := Δ.a_cycle
  d := Δ.d
  d_mem := Δ.d_mem
  d_x := Δ.d_x
  d_x₂ := Δ.d_x₂
  M_eq := Δ.M_eq
  F₀_sylow := Δ.F₀_sylow
  F₀_abelian := Δ.F₀_abelian
  F₀_omega := Δ.F₀_omega
  L_normal := Δ.L_normal
  T_le_L := Δ.T_le_L
  J := Δ.J
  J_le := Δ.J_le
  L₀_eq := Δ.L₀_eq
  J_centralizes := Δ.J_centralizes
  J_normal := Δ.J_normal
  J_inf := Δ.J_inf
  J_sl2 := Δ.J_sl2
  W := Δ.W
  W_eq := Δ.W_eq
  W_cyclic := Δ.W_cyclic
  W_coprime := Δ.W_coprime
  Op_C := Δ.Op_C
  P_conj := Δ.P_conj
  P_abelian := Δ.P_abelian
  P_centralized := Δ.P_centralized
  P_inverted := Δ.P_inverted
  P_sylow := Δ.P_sylow
  Q := Δ.Qs
  Qs := Δ.Q
  Q_trivial := fun h i => (Δ.Q_trivial h i).symm
  Q_le := fun i => (Δ.Q_le i).symm
  Q_pgroup := fun i => (Δ.Q_pgroup i).symm
  Q_C := fun i => (Δ.Q_C i).symm
  Q_conj := fun i => (Δ.Q_conj i).symm
  Q_cases := fun h i => by
    obtain ⟨h1, h2, h3, h4, ⟨z, hz, hzQ⟩, h6, h7, h8, h9, h10⟩ := Δ.Q_cases h i
    refine ⟨h1.symm, h3, h2, by rw [h4, sup_comm], ⟨z, hz, ?_⟩,
      fun X hX hp hC => (h6 X hX hp hC).symm, h8, h7, h10, h9⟩
    rw [← hzQ, conjSub_conjSub,
      conjSub_eq_self_iff.mpr ((Δ.Q_C i).1 (sq_mem_C_of_mem_D_conj hσ Δ i hz))]
  P := Δ.P
  P_sylowC := Δ.P_sylowC
  P_D := Δ.P_D
  P_L := Δ.P_L
  lemma71 := fun i => by
    rw [Δ.lemma71 i]
    split_ifs
    · exact Set.pair_comm _ _
    · rfl
  lemma72 := fun i R hR => by
    rw [Δ.lemma72 i R hR]
    split_ifs
    · exact Set.pair_comm _ _
    · rfl

variable (hσ : σ.IsValid) (Δ : Data σ r)

@[simp] theorem swapQ_Q (i : Fin 3) : (Data.swapQ hσ Δ).Q i = Δ.Qs i := rfl

@[simp] theorem swapQ_Qs (i : Fin 3) : (Data.swapQ hσ Δ).Qs i = Δ.Q i := rfl

theorem R_swapQ (i : Fin 3) : R (Data.swapQ hσ Δ) i = Rs Δ i := rfl

theorem Rs_swapQ (i : Fin 3) : Rs (Data.swapQ hσ Δ) i = R Δ i := rfl

theorem omnibus_swapQ (homni : Omnibus Δ) : Omnibus (Data.swapQ hσ Δ) := by
  intro H hCH U hU
  have h := homni H hCH U hU
  exact
    { part_i_a := h.part_i_a
      part_i_b := fun i => by
        obtain ⟨V, h1, h2, h3⟩ := h.part_i_b i
        refine ⟨V, h1, h2, ?_⟩
        rw [R_swapQ, Rs_swapQ]
        rcases h3 with h3 | h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inr h3)
        · exact Or.inr (Or.inl h3)
      part_ii_a := h.part_ii_a
      part_ii_b := h.part_ii_b
      part_iii_a := h.part_iii_a
      part_iii_b := h.part_iii_b
      part_iv := h.part_iv
      part_v := h.part_v
      part_vi := h.part_vi }

theorem inputs_swapQ (hI : Inputs Δ) : Inputs (Data.swapQ hσ Δ) where
  ii_4_4 := fun hδq Y hYN hY hYQ => hI.ii_4_4 hδq Y hYN hY hYQ.symm
  ii_4_10_iii := fun hδq => (hI.ii_4_10_iii hδq).symm
  ii_4_18 := fun hδq Y Z hZY hYZ hJY hJZ hcomm hpow hcard hfaith Q hQ =>
    hI.ii_4_18 hδq Y Z hZY hYZ hJY hJZ hcomm hpow hcard hfaith Q (by
      rw [Set.pair_comm]
      exact hQ)

end CFSG.ABGTheoremB.TotallyInverted.Sec11
