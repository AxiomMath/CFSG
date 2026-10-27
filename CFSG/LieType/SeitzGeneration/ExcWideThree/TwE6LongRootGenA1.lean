module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootStd
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootGenAbs

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Rank1


variable (t : TwistTag) {K : Type} [Field K] (σ : K →+* K)

theorem orbitN_one_conj_orbitX (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitN t K σ a 1 * orbitX t K σ a (-c) * (orbitN t K σ a 1)⁻¹ = orbitY t K σ a c := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    ← canonicalRep_orbitReflection_eq_orbitN t σ a]
  exact canonicalRep_orbitReflection_conj_orbitX t σ a c

theorem orbitN_one_conj_orbitY (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    orbitN t K σ a 1 * orbitY t K σ a c * (orbitN t K σ a 1)⁻¹ = orbitX t K σ a (-c) := by
  set n := orbitN t K σ a 1 with hn
  have hR1 : ∀ d : orbitField t K σ a, n * orbitX t K σ a (-d) * n⁻¹ = orbitY t K σ a d :=
    orbitN_one_conj_orbitX t σ a
  have hY : (orbitY t K σ a (-1))⁻¹ = orbitY t K σ a 1 := by
    rw [← hR1 (-1), ← hR1 1, neg_neg]
    simp [orbitX_neg, mul_assoc]
  have e1 : n = orbitX t K σ a 1 * orbitY t K σ a (-1) * orbitX t K σ a 1 := by
    rw [hn, orbitN]
    simp
  have e2 : orbitN t K σ a (-1) =
      orbitX t K σ a (-1) * orbitY t K σ a 1 * orbitX t K σ a (-1) := by
    rw [orbitN]
    simp
  have hinv : n⁻¹ = orbitN t K σ a (-1) := by
    rw [e2, e1, mul_inv_rev, mul_inv_rev, hY, ← orbitX_neg, mul_assoc]
  have hc : n⁻¹ * n⁻¹ * orbitX t K σ a (-c) * (n⁻¹ * n⁻¹)⁻¹ = orbitX t K σ a (-c) := by
    have h := orbitH_mul_orbitX_mul_inv t σ a (-1) (-c)
    rw [orbitH, ← hn, ← hinv] at h
    simpa using h
  rw [← hR1 c]
  calc n * (n * orbitX t K σ a (-c) * n⁻¹) * n⁻¹ = n * n * orbitX t K σ a (-c) * n⁻¹ * n⁻¹ := by
        group
    _ = n * n * (n⁻¹ * n⁻¹ * orbitX t K σ a (-c) * (n⁻¹ * n⁻¹)⁻¹) * n⁻¹ * n⁻¹ := by rw [hc]
    _ = orbitX t K σ a (-c) := by group

end Rank1

section A1


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem nG_mul_xG_neg_mul_inv (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    nG σ a * xG σ a (-c) * (nG σ a)⁻¹ = yG σ a c := by
  apply Subtype.ext
  have h := congrArg Subtype.val (orbitN_one_conj_orbitX TwistTag.E6 σ.toRingHom a c)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_nG, coe_xG, coe_yG,
    canonicalRep_orbitReflection_eq_orbitN TwistTag.E6 σ.toRingHom a] using h

private theorem nG_mul_yG_mul_inv (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    nG σ a * yG σ a c * (nG σ a)⁻¹ = xG σ a (-c) := by
  apply Subtype.ext
  have h := congrArg Subtype.val (orbitN_one_conj_orbitY TwistTag.E6 σ.toRingHom a c)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_nG, coe_xG, coe_yG,
    canonicalRep_orbitReflection_eq_orbitN TwistTag.E6 σ.toRingHom a] using h

private theorem nG_a2 : nG σ a2 = xG σ a2 1 * yG σ a2 (-1) * xG σ a2 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_nG, coe_xG, coe_yG,
    canonicalRep_orbitReflection_eq_orbitN TwistTag.E6 σ.toRingHom a2]
  rw [orbitN]
  simp only [Units.val_one, inv_one, Subgroup.coe_mul]

@[expose] def nSL2 : twistedE6RootGroup K σ := n0G σ * nG σ a2 * (n0G σ)⁻¹

private theorem nSL2_mul_x (c : orbitField TwistTag.E6 K σ.toRingHom a2) :
    nSL2 σ * (n0G σ * xG σ a2 c * (n0G σ)⁻¹) * (nSL2 σ)⁻¹ =
      n0G σ * yG σ a2 (-c) * (n0G σ)⁻¹ := by
  have h := nG_mul_xG_neg_mul_inv σ a2 (-c)
  rw [neg_neg] at h
  rw [← h]
  simp only [nSL2]
  group

private theorem nSL2_mul_y (c : orbitField TwistTag.E6 K σ.toRingHom a2) :
    nSL2 σ * (n0G σ * yG σ a2 c * (n0G σ)⁻¹) * (nSL2 σ)⁻¹ =
      n0G σ * xG σ a2 (-c) * (n0G σ)⁻¹ := by
  rw [← nG_mul_yG_mul_inv σ a2 c]
  simp only [nSL2]
  group

theorem nSL2_mem_SL2 :
    nSL2 σ ∈ twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) := by
  have hx : n0G σ * xG σ a2 1 * (n0G σ)⁻¹ ∈ twE6RootSubgroup K σ e6HighestRoot :=
    (mem_X0_iff' σ _).2 ⟨1, rfl⟩
  have hy : n0G σ * yG σ a2 (-1) * (n0G σ)⁻¹ ∈ twE6RootSubgroup K σ (-e6HighestRoot) :=
    (mem_X0m_iff' σ _).2 ⟨-1, rfl⟩
  have e : nSL2 σ = (n0G σ * xG σ a2 1 * (n0G σ)⁻¹) * (n0G σ * yG σ a2 (-1) * (n0G σ)⁻¹) *
      (n0G σ * xG σ a2 1 * (n0G σ)⁻¹) := by
    simp only [nSL2]
    rw [nG_a2]
    group
  rw [e]
  exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inl hx))
    (Subgroup.subset_closure (Or.inr hy))) (Subgroup.subset_closure (Or.inl hx))

theorem map_conj_X0 :
    (twE6RootSubgroup K σ e6HighestRoot).map (MulAut.conj (nSL2 σ)).toMonoidHom =
      twE6RootSubgroup K σ (-e6HighestRoot) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_X0_iff' σ y).1 hy
    have h := nSL2_mul_x σ c
    refine (mem_X0m_iff' σ _).2 ⟨-c, ?_⟩
    simpa [MulAut.conj_apply] using h
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_X0m_iff' σ x).1 hx
    refine ⟨n0G σ * xG σ a2 (-c) * (n0G σ)⁻¹, (mem_X0_iff' σ _).2 ⟨-c, rfl⟩, ?_⟩
    have h := nSL2_mul_x σ (-c)
    rw [neg_neg] at h
    simpa [MulAut.conj_apply] using h

theorem map_conj_X0m :
    (twE6RootSubgroup K σ (-e6HighestRoot)).map (MulAut.conj (nSL2 σ)).toMonoidHom =
      twE6RootSubgroup K σ e6HighestRoot := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_X0m_iff' σ y).1 hy
    have h := nSL2_mul_y σ c
    refine (mem_X0_iff' σ _).2 ⟨-c, ?_⟩
    simpa [MulAut.conj_apply] using h
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_X0_iff' σ x).1 hx
    refine ⟨n0G σ * yG σ a2 (-c) * (n0G σ)⁻¹, (mem_X0m_iff' σ _).2 ⟨-c, rfl⟩, ?_⟩
    have h := nSL2_mul_y σ (-c)
    rw [neg_neg] at h
    simpa [MulAut.conj_apply] using h

theorem nSL2_mul_self_mem_parabolic :
    nSL2 σ * nSL2 σ ∈ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) := by
  rw [twE6LongRootParabolic, Subgroup.mem_normalizer_iff]
  intro h
  have h1 : ∀ z, z ∈ twE6RootSubgroup K σ e6HighestRoot ↔
      (nSL2 σ)⁻¹ * z * nSL2 σ ∈ twE6RootSubgroup K σ (-e6HighestRoot) := fun z => by
    rw [← map_conj_X0m σ, mem_map_conj_iff]
  have h2 : ∀ z, z ∈ twE6RootSubgroup K σ (-e6HighestRoot) ↔
      (nSL2 σ)⁻¹ * z * nSL2 σ ∈ twE6RootSubgroup K σ e6HighestRoot := fun z => by
    rw [← map_conj_X0 σ, mem_map_conj_iff]
  have e : (nSL2 σ)⁻¹ * ((nSL2 σ)⁻¹ * (nSL2 σ * nSL2 σ * h * (nSL2 σ * nSL2 σ)⁻¹) * nSL2 σ) *
      nSL2 σ = h := by group
  rw [h1 (nSL2 σ * nSL2 σ * h * (nSL2 σ * nSL2 σ)⁻¹),
    h2 ((nSL2 σ)⁻¹ * (nSL2 σ * nSL2 σ * h * (nSL2 σ * nSL2 σ)⁻¹) * nSL2 σ), e]

theorem nSL2_not_mem_parabolic :
    nSL2 σ ∉ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) := by
  intro hn
  rw [twE6LongRootParabolic, Subgroup.mem_normalizer_iff] at hn
  have hx : n0G σ * xG σ a2 1 * (n0G σ)⁻¹ ∈ twE6RootSubgroup K σ e6HighestRoot :=
    (mem_X0_iff' σ _).2 ⟨1, rfl⟩
  have h1 := (hn _).1 hx
  rw [nSL2_mul_x σ 1] at h1
  obtain ⟨c, hc⟩ := (mem_X0_iff' σ _).1 h1
  have hyx : yG σ a2 (-1) = xG σ a2 c := by
    have h2 : n0G σ * yG σ a2 (-1) = n0G σ * xG σ a2 c := mul_right_cancel hc
    exact mul_left_cancel h2
  have hB : ((yG σ a2 (-1) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootBorel TwistTag.E6 K σ.toRingHom ⊓
        graphFixedNegUnipotent TwistTag.E6 K σ.toRingHom := by
    refine Subgroup.mem_inf.2 ⟨?_, orbitY_mem_graphFixedNegUnipotent TwistTag.E6 σ.toRingHom a2 _⟩
    rw [hyx]
    exact graphFixedPosUnipotent_le_graphFixedRootBorel
      (orbitX_mem_graphFixedPosUnipotent TwistTag.E6 σ.toRingHom a2 c)
  rw [graphFixedRootBorel_inf_graphFixedNegUnipotent, Subgroup.mem_bot] at hB
  have hy1 : yG σ a2 (-1) = 1 := Subtype.ext hB
  have h3 := nG_mul_xG_neg_mul_inv σ a2 (-1)
  rw [neg_neg, hy1] at h3
  have hx1 : xG σ a2 1 = 1 := by
    have h4 : nG σ a2 * xG σ a2 1 = nG σ a2 := by
      rw [mul_inv_eq_one] at h3
      exact h3
    simpa using h4
  have h6 : (orbitX TwistTag.E6 K σ.toRingHom a2 1 : ModGL TwistTag.E6.tag K) = 1 := by
    have h7 := congrArg (Subtype.val : twistedE6RootGroup K σ → ModGL TwistTag.E6.tag K) hx1
    simpa using h7
  have h5 : orbitX TwistTag.E6 K σ.toRingHom a2 1 = orbitX TwistTag.E6 K σ.toRingHom a2 0 := by
    rw [orbitX_zero]
    exact Subtype.ext h6
  exact one_ne_zero (orbitX_injective σ.toRingHom a2 h5)

end A1

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen
