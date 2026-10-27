module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem exists_z_commutator_mem_zpowers {Q N Pg U : Subgroup G} (hP2 : IsPGroup 2 Pg)
    (hQP : Q ≤ Pg) (hU : IsUGroup 2 Pg U) (hUN : U ≤ N)
    (hC : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ Q ∧ ∀ u ∈ U, ∀ q ∈ Q, u * q * u⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨hUP, hPU, hplane, -⟩ := hU
  have hUne : U ≠ ⊥ := by
    intro h
    have := hplane.2
    rw [h, Subgroup.card_bot] at this
    have h4 : (1 : ℕ) < 2 ^ 2 := by norm_num
    omega
  obtain ⟨z, hzU, hz1, hzc⟩ := Lemma85Aux.exists_mem_inf_centerOf hP2 hUP hPU hUne
  obtain ⟨z', hz', rfl⟩ := hzc
  have hzcenter : ∀ c ∈ Pg, c * (z' : G) * c⁻¹ = z' := by
    intro c hc
    have := Subgroup.mem_center_iff.1 hz' ⟨c, hc⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [mul_inv_eq_iff_eq_mul]
    exact h2
  have hzQ : (z' : G) ∈ Q := by
    refine hC ⟨hUN hzU, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro q hq
    have := hzcenter q (hQP hq)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  refine ⟨z', hzU, hz1, hzQ, ?_⟩
  intro u hu q hq
  have hcU : ∀ w ∈ U, q * w * q⁻¹ ∈ U := fun w hw =>
    (Subgroup.mem_normalizer_iff.1 (hPU (hQP hq)) w).1 hw
  have := Lemma85Aux.inv_mul_conj_mem_zpowers hplane.1 (by simpa using hplane.2 : Nat.card U = 4)
    hzU hz1 hcU (hzcenter q (hQP hq)) (inv_mem hu : u⁻¹ ∈ U)
  simpa [mul_assoc] using this

namespace LinPkg

variable {Q N : Subgroup G} (P : LinPkg Q N)

omit [Finite G] in
theorem isTransvection_of_commutator_mem {z : G} (hzQ : z ∈ Q) {u : N} (hu1 : P.ρ u ≠ 1)
    (h : ∀ q ∈ Q, (u : G) * q * (u : G)⁻¹ * q⁻¹ ∈ Subgroup.zpowers z) :
    IsTransvection (P.ρ u) := by
  refine ⟨hu1, ?_⟩
  set z0 : Q := ⟨z, hzQ⟩
  have hz2 : (P.π z0) * (P.π z0) = 1 := P.elem _
  have hsub : Subgroup.closure (Set.range fun v : P.V => P.ρ u v * v⁻¹) ≤
      Subgroup.zpowers (P.π z0) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨q, rfl⟩ := P.π_surj v
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (h q q.2)
    have h1 : P.ρ u (P.π q) = P.π ⟨(u : G) * q * (u : G)⁻¹, P.norm u q⟩ := P.ρ_π u q _ rfl
    have h2 : (⟨(u : G) * q * (u : G)⁻¹ * (q : G)⁻¹, Q.mul_mem (P.norm u q) (Q.inv_mem q.2)⟩ : Q)
        = z0 ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    have h3 : P.ρ u (P.π q) * (P.π q)⁻¹ = P.π (z0 ^ k) := by
      rw [h1, ← h2, ← map_inv, ← map_mul]
      congr 1
    show P.ρ u (P.π q) * (P.π q)⁻¹ ∈ _
    rw [h3, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hle2 : Nat.card (Subgroup.zpowers (P.π z0)) ≤ 2 := by
    rw [Nat.card_zpowers]
    have : orderOf (P.π z0) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
    exact Nat.le_of_dvd (by norm_num) this
  have hle : Nat.card (Subgroup.closure (Set.range fun v : P.V => P.ρ u v * v⁻¹)) ≤ 2 :=
    (Subgroup.card_le_of_le hsub).trans hle2
  have hne : Subgroup.closure (Set.range fun v : P.V => P.ρ u v * v⁻¹) ≠ ⊥ := by
    intro hbot
    apply hu1
    ext v
    have hmem : P.ρ u v * v⁻¹ ∈ Subgroup.closure (Set.range fun v : P.V => P.ρ u v * v⁻¹) :=
      Subgroup.subset_closure ⟨v, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    simpa using hmem
  have hgt : 1 < Nat.card (Subgroup.closure (Set.range fun v : P.V => P.ρ u v * v⁻¹)) :=
    Subgroup.one_lt_card_iff_ne_bot _ |>.2 hne
  omega

end LinPkg

omit [Finite G] in
theorem mul_mem_zpowers_of_not_mem {U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hcard : Nat.card U = 4) {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {a b : G} (ha : a ∈ U)
    (hb : b ∈ U) (ha' : a ∉ Subgroup.zpowers z) (hb' : b ∉ Subgroup.zpowers z) :
    a * b ∈ Subgroup.zpowers z := by
  have hz2 : z ^ 2 = 1 := hU.2 z hzU
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hCcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hord]
  have hCU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).2 hzU
  have hcardCU : Nat.card ((Subgroup.zpowers z).subgroupOf U) = 2 := by
    rw [← hCcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCU).toEquiv
  have hidx : ((Subgroup.zpowers z).subgroupOf U).index = 2 := by
    have := Subgroup.card_mul_index ((Subgroup.zpowers z).subgroupOf U)
    rw [hcardCU, hcard] at this
    omega
  exact (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2
    (iff_of_false ha' hb')

variable {Q N : Subgroup G} (P : LinPkg Q N)

theorem LinPkg.stage2 {Pg U : Subgroup G} (hP2 : IsPGroup 2 Pg) (hQP : Q ≤ Pg)
    (hU : IsUGroup 2 Pg U) (hUN : U ≤ N) (hC : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    U ≤ Q ∨ ∃ u₀ : N, (u₀ : G) ∈ U ∧ (u₀ : G) ∉ Q ∧
      (∀ u ∈ U, u ∈ Q ∨ (u₀ : G)⁻¹ * u ∈ Q) ∧ IsTransvection (P.ρ u₀) := by
  obtain ⟨z, hzU, hz1, hzQ, hz⟩ := exists_z_commutator_mem_zpowers hP2 hQP hU hUN hC
  by_cases hUQ : U ≤ Q
  · exact Or.inl hUQ
  right
  obtain ⟨u₀, hu₀U, hu₀Q⟩ := Set.not_subset.1 hUQ
  refine ⟨⟨u₀, hUN hu₀U⟩, hu₀U, hu₀Q, ?_, ?_⟩
  · intro u hu
    by_cases hu' : u ∈ Subgroup.zpowers z
    · exact Or.inl ((Subgroup.zpowers_le.2 hzQ) hu')
    · right
      refine (Subgroup.zpowers_le.2 hzQ) (mul_mem_zpowers_of_not_mem hU.2.2.1.1
        (by simpa using hU.2.2.1.2) hzU hz1 (inv_mem hu₀U) hu ?_ hu')
      intro h
      exact hu₀Q ((Subgroup.zpowers_le.2 hzQ) (inv_mem_iff.1 h))
  · refine P.isTransvection_of_commutator_mem hzQ ?_ (hz u₀ hu₀U)
    intro h1
    exact hu₀Q ((P.ker_iff ⟨u₀, hUN hu₀U⟩).1 h1)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
