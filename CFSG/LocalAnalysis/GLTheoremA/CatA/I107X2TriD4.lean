module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.Open
  CFSG.SectionRank CFSG.GH74.Filter.Lie


@[expose] def d4W : SepWitness TwistTag.D4.tag 5 where
  word := ![([2] : List (Fin 4)), ([2] : List (Fin 4)), ([2] : List (Fin 4)), ([] : List (Fin 4)),
    ([2, 3, 1, 2] : List (Fin 4))]
  simple := ![(0 : Fin 4), (1 : Fin 4), (3 : Fin 4), (2 : Fin 4), (0 : Fin 4)]
  sep := ![([2, 0] : List (Fin 4)), ([2, 1] : List (Fin 4)), ([2, 3] : List (Fin 4)),
    ([2] : List (Fin 4)), ([2, 1, 0, 2, 3, 2, 1, 0] : List (Fin 4))]

theorem d4W_check : d4W.check = true := by decide +kernel

@[expose] def d4π : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem d4π_symm_apply (j : Fin 5) : d4π.symm j = ![2, 0, 1, 3, 4] j := by
  revert j
  decide +kernel

theorem d4_vec_rho : ∀ i : Fin 5,
    permLattice TwistTag.D4.perm (d4W.vec i) = d4W.vec (d4π i) := by
  decide +kernel

theorem d4_root_rho (i : Fin 5) :
    rootTwist TwistTag.D4 (d4W.root i) = d4W.root (d4π i) := by
  apply Subtype.ext
  rw [coe_rootTwist, RootWitness.root_val, RootWitness.root_val]
  exact d4_vec_rho i

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def d4Param (σ : K →+* K) (c f3 f4 : K) : Fin 5 → Multiplicative K :=
  ![Multiplicative.ofAdd c, Multiplicative.ofAdd (σ c), Multiplicative.ofAdd (σ (σ c)),
    Multiplicative.ofAdd f3, Multiplicative.ofAdd f4]

theorem d4Param_mem (σ : K →+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) (c f3 f4 : K) (h3 : σ f3 = f3)
    (h4 : σ f4 = f4) :
    d4Param σ c f3 f4 ∈ MonoidHom.eqLocus (paramTwist σ d4π) (MonoidHom.id _) := by
  show paramTwist σ d4π (d4Param σ c f3 f4) = d4Param σ c f3 f4
  funext j
  simp only [paramTwist, MonoidHom.coe_mk, OneHom.coe_mk, d4π_symm_apply]
  fin_cases j <;> simp [d4Param, h3, h4, hσ3]


theorem triD4_rank {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ (3 * n))
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hσsurj : Function.Surjective σ)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) (hu : ∃ u : Kˣ, (u : K) ^ 2 ≠ 1) :
    5 * n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (commutator (twistFixed TwistTag.D4 K σ))) := by
  classical
  obtain ⟨u, hu⟩ := hu
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσ'3 : σ' ^ 3 = 1 := by
    ext c
    show σ' (σ' (σ' c)) = c
    exact hσ3 c
  have hcardV := card_fixed_ge (e := 3 * n) (m := 3) (n := n) hK σ' hσ'3 rfl (by norm_num)
  set V := FixedPoints.subfield (Subgroup.zpowers σ') K with hVdef
  have hVσ : ∀ x : V, σ x.1 = x.1 := by
    intro x
    have hx : ∀ g : Subgroup.zpowers σ', g • x.1 = x.1 := x.2
    exact hx ⟨σ', Subgroup.mem_zpowers σ'⟩
  let E := MonoidHom.eqLocus (paramTwist σ d4π) (MonoidHom.id (Fin 5 → Multiplicative K))
  let ι : K × V × V → E := fun p =>
    ⟨d4Param σ p.1 p.2.1 p.2.2, d4Param_mem σ hσ3 _ _ _ (hVσ p.2.1) (hVσ p.2.2)⟩
  have hι : Function.Injective ι := by
    rintro ⟨c, f3, f4⟩ ⟨c', f3', f4'⟩ h
    have h' : d4Param σ c f3 f4 = d4Param σ c' f3' f4' := congrArg Subtype.val h
    have hc : c = c' := by simpa [d4Param] using congrFun h' 0
    have hf3 : (f3 : K) = (f3' : K) := by simpa [d4Param] using congrFun h' 3
    have hf4 : (f4 : K) = (f4' : K) := by simpa [d4Param] using congrFun h' 4
    subst hc
    have e3 : f3 = f3' := Subtype.ext hf3
    have e4 : f4 = f4' := Subtype.ext hf4
    subst e3
    subst e4
    rfl
  have hcardD : Nat.card (K × V × V) = Nat.card K * Nat.card V * Nat.card V := by
    rw [Nat.card_prod, Nat.card_prod, mul_assoc]
  have hEge : 2 ^ (5 * n) ≤ Nat.card E := by
    calc 2 ^ (5 * n) = 2 ^ (3 * n) * 2 ^ n * 2 ^ n := by
          rw [← pow_add, ← pow_add]
          congr 1
          ring
      _ ≤ Nat.card K * Nat.card V * Nat.card V := by
          rw [hK]
          exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl hcardV) hcardV
      _ = Nat.card (K × V × V) := hcardD.symm
      _ ≤ Nat.card E := Nat.card_le_card_of_injective ι hι
  have hEdvd : Nat.card E ∣ 2 ^ (15 * n) := by
    have h1 := Subgroup.card_subgroup_dvd_card E
    have h2 : Nat.card (Fin 5 → Multiplicative K) = 2 ^ (15 * n) := by
      rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K), hK,
        ← pow_mul, Nat.card_eq_fintype_card, Fintype.card_fin]
      congr 1
      ring
    rw [h2] at h1
    exact h1
  obtain ⟨B', hB'⟩ := exists_subgroup_card_two_pow hEdvd hEge
  let B : Subgroup (Fin 5 → Multiplicative K) := B'.map E.subtype
  have hBcard : Nat.card B = 2 ^ (5 * n) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hB'
  have hBle : B ≤ E := Subgroup.map_subtype_le B'
  exact le_pRank_of_twistedWitness (t := TwistTag.D4) σ
    (d4_U_le_twistDerived hσsurj hσ3 hu) d4W d4W_check d4π d4_root_rho B hBle hBcard

end Count

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
