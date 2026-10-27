module

public import CFSG.HardMathSupport.Solomon.Coordinator.U38Outer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.U38

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Lang.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

local notation "ρ" => primeFormConjHom h (idGram K 3)

theorem u38_uω_pow_three {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : uω hω ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, uω, Units.val_mk0, u38_omega_pow_three hω,
    Units.val_one])

include h in
theorem u38_uω_ne_one {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : uω hω ≠ 1 := fun e =>
  u38_omega_ne_one h hω (by have := congrArg Units.val e; simpa [uω] using this)

theorem u38_heis {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {g : MulAut (primeFormP h (idGram K 3))}
    (hgA : g * ρ (uA h hω) = ρ (uA h hω) * g) (hgP : g * ρ (uP h hω) = ρ (uP h hω) * g)
    (hcop : Nat.Coprime 3 (orderOf g)) : g = 1 :=
  eq_one_of_commute_heisenberg h (u38_uω_pow_three hω) (u38_uω_ne_one h hω) (uA_mul_uP h hω)
    (rho_uA_pow_three h hω) (rho_uP_pow_three h hω) (rho_uA_comm_uP h hω) hgA hgP hcop

theorem u38_E₀_le_inner {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    E₀ h hω ≤ innerAut (primeFormP h (idGram K 3)) := by
  refine (Subgroup.closure_le _).2 ?_
  have key : ∀ X : primeFormUnitary h (idGram K 3),
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 →
      ρ X ∈ innerAut (primeFormP h (idGram K 3)) := by
    intro X hX
    have hg : (X : GL (Fin 3) K) ∈ gramSU h (idGram K 3) := (mem_gramSU_iff_unitary h).2 ⟨X.2, hX⟩
    refine ⟨((⟨X, hg⟩ : gramSU h (idGram K 3)) : primeFormP h (idGram K 3)), ?_⟩
    exact (u38_rho_eq_conj h ⟨X, hg⟩ X.2).symm
  rintro _ (rfl | hx)
  · exact key _ (by rw [coe_uA]; exact det_mA ω hω (u38_two_eq_zero h))
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact key _ (by rw [coe_uP]; exact det_mP)

theorem oPrimeCore_centralizer_outer_eq_bot {x : MulAut (primeFormP h (idGram K 3))}
    (hxl : x ∉ primeFormD h (idGram K 3)) (hx3 : x ^ 3 = 1)
    {H : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    (hH : innerAut (primeFormP h (idGram K 3)) ≤ H) :
    GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut (primeFormP h (idGram K 3))))) =
      ⊥ := by
  classical
  have := h.finite
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (primeFormP h (idGram K 3)) := finite_primeFormP
  obtain ⟨ω, hω⟩ := exists_omega h
  set Fσ := primeFormFieldFactor h isPrimeFormGram_one le_rfl u38_hne with hFσ
  have hx1 : x ≠ 1 := fun e => hxl (e ▸ Subgroup.one_mem _)
  have hxp : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hσ1 : Fσ x ≠ 1 := fun e => hxl (by
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one le_rfl u38_hne]
    exact e)
  have hσ : orderOf (Fσ x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ := unitary_prime_semilinear_field_descent' h le_rfl u38_hne
    Nat.prime_three (by norm_num) x hxp (Fσ x) rfl hσ
  set σ := Fσ x with hσdef
  set c := ρ M with hc
  set fσ := primeFormFieldHom h isPrimeFormGram_one σ with hfσ
  have hxc : x = c * fσ * c⁻¹ := by
    rw [← hM]
    group
  have hE₀f : ∀ e ∈ E₀ h hω, e * fσ = fσ * e := by
    intro e he
    have hle : E₀ h hω ≤ Subgroup.centralizer ({fσ} : Set (MulAut (primeFormP h (idGram K 3)))) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | hy)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (u38_fieldHom_comm h (uA h hω) (fun i j => by
            rw [coe_uA]; exact u38_sigma_mA h hω hσ i j)).symm
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_centralizer_singleton_iff.2
          (u38_fieldHom_comm h (uP h hω) (fun i j => by
            rw [coe_uP]; exact u38_sigma_mP σ i j)).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  set E := (E₀ h hω).map (MulAut.conj c).toMonoidHom with hE
  have hmemE : ∀ e ∈ E, ∃ e₀ ∈ E₀ h hω, e = c * e₀ * c⁻¹ := by
    rintro _ ⟨e₀, he₀, rfl⟩
    exact ⟨e₀, he₀, rfl⟩
  refine glaPPrimeCoreOf_eq_bot_of_plane (I := innerAut (primeFormP h (idGram K 3))) (E := E)
    (u38_innerAut_normal h) hH ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := hmemE e he
    exact u38_innerAut_normal h c e₀ (u38_E₀_le_inner h hω he₀)
  ·
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := hmemE e he
    rw [hxc]
    have := hE₀f e₀ he₀
    calc c * e₀ * c⁻¹ * (c * fσ * c⁻¹) = c * (e₀ * fσ) * c⁻¹ := by group
      _ = c * (fσ * e₀) * c⁻¹ := by rw [this]
      _ = c * fσ * c⁻¹ * (c * e₀ * c⁻¹) := by group
  ·
    intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := hmemE a ha
    obtain ⟨b₀, hb₀, rfl⟩ := hmemE b hb
    have := u38_E₀_comm h hω ha₀ hb₀
    calc c * a₀ * c⁻¹ * (c * b₀ * c⁻¹) = c * (a₀ * b₀) * c⁻¹ := by group
      _ = c * (b₀ * a₀) * c⁻¹ := by rw [this]
      _ = c * b₀ * c⁻¹ * (c * a₀ * c⁻¹) := by group
  ·
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := hmemE a ha
    rw [conj_pow, u38_E₀_pow_three h hω ha₀]
    group
  ·
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact u38_three_lt_card_E₀ h hω
  ·
    intro b hb hb1 r hr hcop hrb
    obtain ⟨b₀, hb₀, rfl⟩ := hmemE b hb
    have hb₀1 : b₀ ≠ 1 := by
      rintro rfl
      exact hb1 (by group)
    have hr' : c⁻¹ * r * c⁻¹⁻¹ ∈ innerAut (primeFormP h (idGram K 3)) :=
      u38_innerAut_normal h c⁻¹ r hr
    obtain ⟨s, hs⟩ := u38_innerAut_le h hr'
    have hs' : ρ s = c⁻¹ * r * c := by rw [hs, inv_inv]
    have hcomm : ρ s * b₀ = b₀ * ρ s := by
      rw [hs']
      calc c⁻¹ * r * c * b₀ = c⁻¹ * (r * (c * b₀ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * b₀ * c⁻¹) * r) * c := by rw [hrb]
        _ = b₀ * (c⁻¹ * r * c) := by group
    have hcop' : Nat.Coprime 3 (orderOf (ρ s)) := by
      rw [hs']
      have := u38_orderOf_conj c⁻¹ r
      rw [inv_inv] at this
      rw [this]
      exact hcop
    have h1 := torus_plane h hω hb₀ hb₀1 s hcomm hcop'
    rw [hs'] at h1
    calc r = c * (c⁻¹ * r * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  ·
    intro g hg hcop
    set g' := c⁻¹ * g * c with hg'
    have hcomm : ∀ e₀ ∈ E₀ h hω, g' * e₀ = e₀ * g' := by
      intro e₀ he₀
      have := hg (c * e₀ * c⁻¹) ⟨e₀, he₀, rfl⟩
      calc c⁻¹ * g * c * e₀ = c⁻¹ * (g * (c * e₀ * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * e₀ * c⁻¹) * g) * c := by rw [this]
        _ = e₀ * (c⁻¹ * g * c) := by group
    have hcop' : Nat.Coprime 3 (orderOf g') := by
      rw [hg']
      have := u38_orderOf_conj c⁻¹ g
      rw [inv_inv] at this
      rw [this]
      exact hcop
    have h1 := u38_heis h hω (hcomm _ (Subgroup.subset_closure (Set.mem_insert _ _)))
      (hcomm _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) hcop'
    rw [hg'] at h1
    calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem u38_isLocallyBalancedAbs : IsLocallyBalancedAbs 3 2 (primeFormP h (idGram K 3)) := by
  classical
  have := h.finite
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (primeFormP h (idGram K 3)) := finite_primeFormP
  intro D hDe hDc H hH hDH
  by_cases hDl : D ≤ primeFormD h (idGram K 3)
  swap
  · obtain ⟨x, hx, hxl⟩ := Set.not_subset.1 hDl
    have hx1 : x ≠ 1 := fun e => hxl (e ▸ Subgroup.one_mem _)
    rw [eq_bot_iff]
    intro g hg
    have := w3_mem_core_of_mem_localDeltaIn hx hx1 hg
    rw [oPrimeCore_centralizer_outer_eq_bot h hxl (hDe.2 x hx) hH] at this
    exact this
  obtain ⟨x, hx, y, hy, hx1, hyx, hgen⟩ := exists_gen_pair Nat.prime_three hDe hDc
  obtain ⟨A0, rfl⟩ := hDl hx
  obtain ⟨B0, rfl⟩ := hDl hy
  have hxy : ρ A0 * ρ B0 = ρ B0 * ρ A0 :=
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
  by_cases hAB : A0 * B0 = B0 * A0
  · rw [← hgen]
    exact localDeltaIn_eq_bot_of_unitary_plane le_rfl u38_hne (by norm_num) Nat.prime_three
      (by norm_num) (by norm_num) hAB (hDe.2 _ hx) (hDe.2 _ hy) hx1 hyx hH
  obtain ⟨z, hz⟩ := primeFormUnitary_exists_comm_scalar h le_rfl u38_hne hxy
  obtain ⟨b0, -, hb0⟩ := exists_pow_scalar_unitary le_rfl u38_hne (hDe.2 _ hy)
  have hz3 : z ^ 3 = 1 := comm_scalar_pow_eq_one le_rfl hz hb0
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hAB
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz, map_one, one_mul]
  have hAB' : (A0 : GL (Fin 3) K) * B0 = B0 * A0 * GeneralLinearGroup.scalar (Fin 3) z := by
    rw [hz, GeneralLinearGroup.scalar_commute]
  have hy1 : ρ B0 ≠ 1 := fun e => hyx (e ▸ Subgroup.one_mem _)
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact eq_one_of_commute_heisenberg h hz3 hz1 hAB' (hDe.2 _ hx) (hDe.2 _ hy) hxy
    (w3_commute_of_mem_localDeltaIn hx hx1 hg) (w3_commute_of_mem_localDeltaIn hy hy1 hg)
    (w3_coprime_orderOf_of_mem_localDeltaIn Nat.prime_three hx hx1 hg)

end CFSG.HardMathSupport.Solomon.Coordinator.U38
