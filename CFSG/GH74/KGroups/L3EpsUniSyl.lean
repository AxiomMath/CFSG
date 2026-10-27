module

public import CFSG.GH74.KGroups.L3EpsOrder
public import CFSG.GH74.KGroups.SDPres
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.GH74.KGroups.L3Eps

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

section General

noncomputable def projCongr {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] {H₁ H₂ : Subgroup G}
    (h : H₁ = H₂) : (H₁ ⧸ Z.subgroupOf H₁) ≃* (H₂ ⧸ Z.subgroupOf H₂) := by
  subst h
  exact MulEquiv.refl _

theorem nonempty_mulEquiv_of_sylow {Q : Type*} [Group Q] [Finite Q] {R W : Subgroup Q}
    (hR : IsPGroup 2 R) (hRmax : ∀ T : Subgroup Q, IsPGroup 2 T → R ≤ T → T ≤ R)
    (hW : IsPGroup 2 W) (hWcard : Nat.card W = ordProj[2] (Nat.card Q)) :
    Nonempty (R ≃* W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SR : Sylow 2 Q := ⟨R, hR, fun {T} hT hRT => le_antisymm (hRmax T hT hRT) hRT⟩
  let SW : Sylow 2 Q := ⟨W, hW, fun {T} hT hWT => le_antisymm (isMax_of_card hWcard T hT hWT) hWT⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Q SR SW
  have hgR : (g • SR).toSubgroup = W := congrArg Sylow.toSubgroup hg
  exact ⟨(SR.equivSMul g).trans (MulEquiv.subgroupCongr hgR)⟩

noncomputable def equivMapOfInjOn {A B : Type*} [Group A] [Group B] (f : A →* B) (W : Subgroup A)
    (h : Set.InjOn f (W : Set A)) : W ≃* W.map f :=
  (MonoidHom.ofInjective (f := f.domRestrict W) (fun x y hxy => Subtype.ext (h x.2 y.2 hxy))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.domRestrict_range]))

end General

section Uni

variable {X : Type} [Group X] {p f : ℕ}

theorem exists_unitary_quotient_equiv (hX : StatedClassicalModel X .PSU 3 p f) :
    ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData p f K),
      Nonempty (X ≃* (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K) ⧸
        (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)))) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have := hU.finite
  have : CharP K p := hU.charP
  have hF := card_eq_sq_of_unitaryFieldData hU
  have hEq : SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K) = StatedSU 3 (p ^ f) K :=
    (SUgram_bar_one hU 3).trans (SUid_eq_statedSU hF 3)
  exact ⟨K, inferInstance, hU, ⟨e.trans (projCongr (StatedScalars (Fin 3) K) hEq.symm)⟩⟩

end Uni

section UniSylowThree

variable {X : Type} [Group X] {p f : ℕ}

theorem bar_one_apply' {K : Type} [Field K] (h : UnitaryFieldData p f K) (i j : Fin 3) :
    h.bar ((1 : Matrix (Fin 3) (Fin 3) K) j i) = (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

theorem uni_sylow_three (hp2 : p ≠ 2) (h3 : p ^ f % 4 = 3) (hX : StatedClassicalModel X .PSU 3 p f)
    {R : Subgroup X} (hR : IsPGroup 2 R) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → R ≤ T → T ≤ R) :
    ∃ z : R, (∀ y : R, y * z = z * y) ∧ orderOf z = ordProj[2] (p ^ f + 1) := by
  obtain ⟨K, _, hU, ⟨ψ⟩⟩ := exists_unitary_quotient_equiv hX
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : CharP K p := hU.charP
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  set D := (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)) with hD
  have hmodels := odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2 (G₀ := 1)
    (bar_one_apply' hU) hdet D le_rfl
  obtain ⟨⟨P, hP⟩, -, -, -, h3part, -⟩ := hmodels
  obtain ⟨⟨l, hl, hlo⟩, hall⟩ := h3part h3
  obtain ⟨u, v, τ, -, -, -, hvu, huv, hou, hov, hτ2, -, -, hφ, hnf, hW2, -, hinj, hWbar2, hWbarcard⟩ :=
    hall P hP l hl hlo
  set W := Subgroup.closure ({u, v, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))) with hW
  set s := ordProj[2] (p ^ f + 1) with hs
  have hs0 : 0 < s := Nat.ordProj_pos _ _
  have hmaxQ := isMaxPGroup_map ψ hR hmax
  obtain ⟨e1⟩ := nonempty_mulEquiv_of_sylow hmaxQ.1 hmaxQ.2 hWbar2 hWbarcard
  let e : R ≃* W := (ψ.subgroupMap R).trans
    (e1.trans (equivMapOfInjOn (QuotientGroup.mk' D) W hinj).symm)
  have huW : u ∈ W := Subgroup.subset_closure (by simp)
  have hvW : v ∈ W := Subgroup.subset_closure (by simp)
  have hτW : τ ∈ W := Subgroup.subset_closure (by simp)
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left (by rw [← sq, hτ2])
  have hτu : τ * u = v * τ := by
    calc τ * u = τ⁻¹ * u := by rw [hτi]
      _ = τ⁻¹ * u * (τ * τ) := by rw [← sq, hτ2, mul_one]
      _ = (τ⁻¹ * u * τ) * τ := by group
      _ = v * τ := by rw [hvu]
  have hτv : τ * v = u * τ := by rw [hvu]; group
  have hcentral : ∀ y ∈ W, (u * v) * y = y * (u * v) := by
    intro y hy
    have hle : W ≤ Subgroup.centralizer
        ({u * v} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))) := by
      rw [hW, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rcases hx with hx | hx | hx <;> rw [hx]
      · calc u * v * u = u * (v * u) := by rw [mul_assoc]
          _ = u * (u * v) := by rw [← huv.eq]
      · calc u * v * v = v * u * v := by rw [huv.eq]
          _ = v * (u * v) := by rw [mul_assoc]
      · calc u * v * τ = v * u * τ := by rw [huv.eq]
          _ = v * (u * τ) := by rw [mul_assoc]
          _ = v * (τ * v) := by rw [hτv]
          _ = (v * τ) * v := by rw [mul_assoc]
          _ = (τ * u) * v := by rw [hτu]
          _ = τ * (u * v) := by rw [mul_assoc]
    exact Subgroup.mem_centralizer_iff.1 (hle hy) _ (Set.mem_singleton _)
  have hpowuv : ∀ t : ℕ, (u * v) ^ t = u ^ t * v ^ t := fun t => huv.mul_pow t
  have hus : u ^ s = 1 := by rw [← hou]; exact pow_orderOf_eq_one u
  have hvs : v ^ s = 1 := by rw [← hov]; exact pow_orderOf_eq_one v
  have hord : orderOf (u * v) = s := by
    rw [orderOf_eq_iff hs0]
    refine ⟨by rw [hpowuv, hus, hvs, one_mul], fun t ht ht0 h => ?_⟩
    rw [hpowuv] at h
    have h' : (fun x : Fin s × Fin s × Fin 2 => u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ))
        (⟨t, ht⟩, ⟨t, ht⟩, 0) = (fun x : Fin s × Fin s × Fin 2 =>
          u ^ (x.1 : ℕ) * v ^ (x.2.1 : ℕ) * τ ^ (x.2.2 : ℕ)) (⟨0, hs0⟩, ⟨0, hs0⟩, 0) := by
      simp [h]
    have := hφ h'
    simp at this
    omega
  refine ⟨e.symm ⟨u * v, W.mul_mem huW hvW⟩, fun y => ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcentral (e y).1 (e y).2).symm
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hord]

end UniSylowThree

section UniSylowOne

variable {X : Type} [Group X] {p f : ℕ}

theorem uni_sylow_one (hp2 : p ≠ 2) (h1 : p ^ f % 4 = 1) (hX : StatedClassicalModel X .PSU 3 p f)
    {R : Subgroup X} (hR : IsPGroup 2 R) (hmax : ∀ T : Subgroup X, IsPGroup 2 T → R ≤ T → T ≤ R) :
    SD.Pres R ((p ^ f - 1).factorization 2 + 1) (-(p ^ f : ℤ)) := by
  obtain ⟨K, _, hU, ⟨ψ⟩⟩ := exists_unitary_quotient_equiv hX
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : CharP K p := hU.charP
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  set D := (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)) with hD
  have hmodels := odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2 (G₀ := 1)
    (bar_one_apply' hU) hdet D le_rfl
  obtain ⟨-, -, -, -, -, h1part⟩ := hmodels
  obtain ⟨⟨z, hz⟩, ⟨M, hM⟩, hall⟩ := h1part h1
  obtain ⟨u, τ, -, -, hou, hτ2, hτu, hφ, hnf, hW2, -, hinj, hWbar2, hWbarcard⟩ := hall M hM z hz
  set W := Subgroup.closure ({u, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))) with hW
  have huW : u ∈ W := Subgroup.subset_closure (by simp)
  have hτW : τ ∈ W := Subgroup.subset_closure (by simp)
  have hPW : SD.Pres W ((p ^ f - 1).factorization 2 + 1) (-(p ^ f : ℤ)) := by
    refine ⟨⟨⟨u, huW⟩, ⟨τ, hτW⟩, ?_, ?_, ?_, fun x => ?_⟩⟩
    · rw [Subgroup.orderOf_mk, hou, pow_succ, mul_comm]
    · exact Subtype.ext (by simpa using hτ2)
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      exact hτu
    · obtain ⟨i, e, -, he, hx⟩ := hnf x.1 x.2
      exact ⟨i, e, he, Subtype.ext (by simpa using hx)⟩
  have hPbar := hPW.congr (equivMapOfInjOn (QuotientGroup.mk' D) W hinj)
  have hmaxQ := isMaxPGroup_map ψ hR hmax
  obtain ⟨e1⟩ := nonempty_mulEquiv_of_sylow hmaxQ.1 hmaxQ.2 hWbar2 hWbarcard
  exact hPbar.congr ((ψ.subgroupMap R).trans e1).symm

end UniSylowOne

section Numeric

theorem sd_numeric {q : ℕ} (hq : q % 4 = 1) (hq2 : 2 ≤ q) :
    3 ≤ (q - 1).factorization 2 + 1 ∧
      ¬ (2 : ℤ) ^ ((q - 1).factorization 2 + 1) ∣ (-(q : ℤ) - 1) ^ 2 ∧
      ¬ (2 : ℤ) ^ ((q - 1).factorization 2 + 1) ∣ 2 * (-(q : ℤ) - 1) := by
  have hq1 : q - 1 ≠ 0 := by omega
  have hv : 2 ≤ (q - 1).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hq1).1 (by
      have : 4 ∣ q - 1 := by omega
      simpa using this)
  have h8 : (8 : ℤ) ∣ (2 : ℤ) ^ ((q - 1).factorization 2 + 1) := by
    have : (2 : ℤ) ^ 3 ∣ (2 : ℤ) ^ ((q - 1).factorization 2 + 1) := pow_dvd_pow 2 (by omega)
    simpa using this
  obtain ⟨a, ha⟩ : ∃ a : ℤ, (q : ℤ) = 4 * a + 1 := ⟨q / 4, by omega⟩
  refine ⟨Nat.succ_le_succ hv, fun h => ?_, fun h => ?_⟩
  · obtain ⟨c, hc⟩ := h8.trans h
    rw [ha] at hc
    ring_nf at hc
    omega
  · obtain ⟨c, hc⟩ := h8.trans h
    rw [ha] at hc
    ring_nf at hc
    omega

end Numeric

section UniCard

variable {X : Type} [Group X] {p f : ℕ}

theorem uni_model_card (hp2 : p ≠ 2) (hX : StatedClassicalModel X .PSU 3 p f) :
    Finite X ∧ ordProj[2] (Nat.card X) = ordProj[2] (p ^ f - 1) * ordProj[2] (p ^ f + 1) ^ 2 := by
  obtain ⟨K, _, hU, ⟨ψ⟩⟩ := exists_unitary_quotient_equiv hX
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : CharP K p := hU.charP
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  set D := (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)) with hD
  obtain ⟨-, -, -, ⟨-, hcard⟩, -, -⟩ := odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2
    (G₀ := 1) (bar_one_apply' hU) hdet D le_rfl
  exact ⟨Finite.of_equiv _ ψ.symm.toEquiv, by rw [Nat.card_congr ψ.toEquiv]; exact hcard⟩

end UniCard

end CFSG.GH74.KGroups.L3Eps
