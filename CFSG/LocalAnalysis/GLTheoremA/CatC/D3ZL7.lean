module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL6

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped Pointwise


section Alg

variable {K : Type} [Field K]

theorem coeff_zero_of_three {c₁ c₂ c₃ p₀ r₀ p₁ r₁ p₂ r₂ : K}
    (h₀ : c₁ * p₀ ^ 2 + c₂ * (p₀ * r₀) + c₃ * r₀ ^ 2 = 0)
    (h₁ : c₁ * p₁ ^ 2 + c₂ * (p₁ * r₁) + c₃ * r₁ ^ 2 = 0)
    (h₂ : c₁ * p₂ ^ 2 + c₂ * (p₂ * r₂) + c₃ * r₂ ^ 2 = 0)
    (d01 : p₀ * r₁ - p₁ * r₀ ≠ 0) (d02 : p₀ * r₂ - p₂ * r₀ ≠ 0) (d12 : p₁ * r₂ - p₂ * r₁ ≠ 0) :
    c₁ = 0 := by
  have key : c₁ * ((p₀ * r₁ - p₁ * r₀) * (p₀ * r₂ - p₂ * r₀) * (p₁ * r₂ - p₂ * r₁)) = 0 := by
    linear_combination (r₁ * r₂ * (p₁ * r₂ - p₂ * r₁)) * h₀ - (r₀ * r₂ * (p₀ * r₂ - p₂ * r₀)) * h₁ +
      (r₀ * r₁ * (p₀ * r₁ - p₁ * r₀)) * h₂
  rcases mul_eq_zero.1 key with h | h
  · exact h
  · exact absurd h (mul_ne_zero (mul_ne_zero d01 d02) d12)

end Alg

section Two

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem rho_mem_normalizer_iff (hK2 : ringChar K ≠ 2) (X : SL2 K) :
    ρ 2 X ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) ↔
      (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  constructor
  · intro h
    have h1 : ρ 2 X * xUnit Tag.D4 K 2 1 * (ρ 2 X)⁻¹ ∈ Uk K 2 :=
      (Subgroup.mem_normalizer_iff.1 h _).1 (xUnit_mem_Uk 2 1)
    obtain ⟨c, hc⟩ := mem_Uk.1 h1
    have h2 : ρ 2 (uSL c) = ρ 2 (X * uSL 1 * X⁻¹) := by
      rw [map_mul, map_mul, map_inv, simpleRootSL2_uSL, simpleRootSL2_uSL]; exact hc
    have h3 := simpleRootSL2_injective hK2 2 h2
    have h4 : uSL c * X = X * uSL 1 := by
      rw [h3, inv_mul_cancel_right]
    have h5 := congrArg (fun Z : SL2 K => (Z : Matrix (Fin 2) (Fin 2) K) 1 1) h4
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two] using h5
  · intro h
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    have e : ρ 2 X * xUnit Tag.D4 K 2 c * (ρ 2 X)⁻¹ = ρ 2 (X * uSL c * X⁻¹) := by
      rw [map_mul, map_mul, map_inv, simpleRootSL2_uSL]
    rw [e, sl2_upper_conj h c, simpleRootSL2_uSL]
    exact xUnit_mem_Uk _ _

theorem conj_rho_two (b : Fin Tag.D4.rank → Kˣ) (A e : SL2 K) :
    (ρ 2 e)⁻¹ * (rootDiagUnit Tag.D4 b * ρ 2 A) * ρ 2 e =
      rootDiagUnit Tag.D4 b * ρ 2 (dconj ((b 2)⁻¹) e⁻¹ * A * e) := by
  set h : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b with hh
  have e2 : (ρ 2 e)⁻¹ * h = h * ρ 2 (dconj ((b 2)⁻¹) e⁻¹) := by
    have := conj_inv_rho b 2 e⁻¹
    rw [map_inv] at this
    calc (ρ 2 e)⁻¹ * h = h * (h⁻¹ * (ρ 2 e)⁻¹ * h) := by group
      _ = h * ρ 2 (dconj ((b 2)⁻¹) e⁻¹) := by rw [hh, this]
  rw [map_mul, map_mul]
  calc (ρ 2 e)⁻¹ * (h * ρ 2 A) * ρ 2 e = ((ρ 2 e)⁻¹ * h) * ρ 2 A * ρ 2 e := by group
    _ = h * ρ 2 (dconj ((b 2)⁻¹) e⁻¹) * ρ 2 A * ρ 2 e := by rw [e2]
    _ = _ := by group

theorem coe_X10 (a : Kˣ) (A e : SL2 K) :
    ((dconj a⁻¹ e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (e : Matrix (Fin 2) (Fin 2) K) 0 0 * ((A : Matrix (Fin 2) (Fin 2) K) 1 0 *
        (e : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 *
        (e : Matrix (Fin 2) (Fin 2) K) 1 0) -
      (e : Matrix (Fin 2) (Fin 2) K) 1 0 * ((a : K) * ((A : Matrix (Fin 2) (Fin 2) K) 0 0 *
        (e : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
        (e : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_dconj,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, inv_inv]
  ring

theorem coe_det10 (e₀ e₁ : SL2 K) :
    ((e₀⁻¹ * e₁ : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (e₀ : Matrix (Fin 2) (Fin 2) K) 0 0 * (e₁ : Matrix (Fin 2) (Fin 2) K) 1 0 -
        (e₁ : Matrix (Fin 2) (Fin 2) K) 0 0 * (e₀ : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons]
  ring

theorem rootDiagUnit_mem_normalizer_Uk (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank) :
    rootDiagUnit Tag.D4 b ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  refine mem_normalizer_of_forall_conj_mem (Uk K k) fun u hu => ?_
  obtain ⟨c, rfl⟩ := mem_Uk.1 hu
  rw [(root_diagonal_conjugation Tag.D4 K b).1 k c]
  exact xUnit_mem_Uk k _

theorem three_stable_normalizes (hK2 : ringChar K ≠ 2) {m : ModGL Tag.D4 K}
    (hm : m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank))) {s₀ s₁ s₂ : ModGL Tag.D4 K}
    (h₀ : s₀ ∈ Lk K 2) (h₁ : s₁ ∈ Lk K 2) (h₂ : s₂ ∈ Lk K 2)
    (m₀ : s₀⁻¹ * m * s₀ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)))
    (m₁ : s₁⁻¹ * m * s₁ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)))
    (m₂ : s₂⁻¹ * m * s₂ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)))
    (d01 : s₀⁻¹ * s₁ ∉ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)))
    (d02 : s₀⁻¹ * s₂ ∉ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)))
    (d12 : s₁⁻¹ * s₂ ∉ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K))) :
    m ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
  obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hm
  have hl' : l ∈ (ρ 2).range := by
    rw [range_simpleRootSL2, ← leviRoot_singleton]; exact hl
  obtain ⟨A, rfl⟩ := hl'
  obtain ⟨e₀, rfl⟩ := mem_Lk.1 h₀
  obtain ⟨e₁, rfl⟩ := mem_Lk.1 h₁
  obtain ⟨e₂, rfl⟩ := mem_Lk.1 h₂
  have hT := rootDiagUnit_mem_normalizer_Uk (K := K) b 2
  have hmem : ∀ X : SL2 K, rootDiagUnit Tag.D4 b * ρ 2 X ∈
      Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) ↔
        (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := fun X =>
    ⟨fun h => (rho_mem_normalizer_iff hK2 X).1 (by
        have := mul_mem (inv_mem hT) h
        simpa using this),
      fun h => mul_mem hT ((rho_mem_normalizer_iff hK2 X).2 h)⟩
  rw [conj_rho_two, hmem] at m₀ m₁ m₂
  have hd : ∀ x y : SL2 K, (ρ 2 x)⁻¹ * ρ 2 y ∉
      Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) →
      ((x⁻¹ * y : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    intro x y h h0
    apply h
    rw [← map_inv, ← map_mul]
    exact (rho_mem_normalizer_iff hK2 _).2 h0
  have d01' := hd _ _ d01
  have d02' := hd _ _ d02
  have d12' := hd _ _ d12
  rw [coe_det10] at d01' d02' d12'
  rw [coe_X10] at m₀ m₁ m₂
  have hA : ((A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    refine coeff_zero_of_three (c₂ := (A : Matrix (Fin 2) (Fin 2) K) 1 1 -
      ((b 2 : Kˣ) : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 0)
      (c₃ := -(((b 2 : Kˣ) : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 1))
      (p₀ := (e₀ : Matrix (Fin 2) (Fin 2) K) 0 0) (r₀ := (e₀ : Matrix (Fin 2) (Fin 2) K) 1 0)
      (p₁ := (e₁ : Matrix (Fin 2) (Fin 2) K) 0 0) (r₁ := (e₁ : Matrix (Fin 2) (Fin 2) K) 1 0)
      (p₂ := (e₂ : Matrix (Fin 2) (Fin 2) K) 0 0) (r₂ := (e₂ : Matrix (Fin 2) (Fin 2) K) 1 0)
      ?_ ?_ ?_ d01' d02' d12'
    · linear_combination m₀
    · linear_combination m₁
    · linear_combination m₂
  exact mul_mem hT ((rho_mem_normalizer_iff hK2 A).2 hA)

end Two

section Key2

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

variable {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ}
  {σ : K ≃+* K} {ε : ℕ}

theorem bar_mem_normalizer (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J)
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K J, phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K J)
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K J, phiG g a σ ε q ∈ parabolicRadical Tag.D4 K J)
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K J, phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {k : Fin Tag.D4.rank} (hk : k ∈ J) {x : ModGL Tag.D4 K} (hx : x ∈ parabolicLevi Tag.D4 K J)
    (hxk : x ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K))) :
    (semiDirect_levi (K := K) J).bar (phiG g a σ ε) x ∈
      Subgroup.normalizer (Uk K ((d4Rho ^ ε) k) : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hS := semiDirect_levi (K := K) J
  refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := bar_Uk_surj hJ hg hJρ hφP hφQ hφ3 hk u hu
  have hx₀' : x * x₀ * x⁻¹ ∈ Uk K k := (Subgroup.mem_normalizer_iff.1 hxk x₀).1 hx₀
  have hx₀M : x₀ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk (Uk_le_Lk _ hx₀)
  have := hS.bar_conj (phiG g a σ ε) hφP (hS.M_le hx) (hS.M_le hx₀M)
  rw [← this]
  exact bar_Uk_le hJ hg hJρ hk hx₀'

theorem levi_key_two (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K)
    (hJρ : ∀ i, i ∈ ({2} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({2} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {y : ModGL Tag.D4 K} (hy : y ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hy2 : y * y = 1) (hφy : phiG g a σ ε y = y) :
    ∃ s ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {2} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inl rfl
  have h2J : (2 : Fin Tag.D4.rank) ∈ J := rfl
  have hρ2 : (d4Rho ^ ε) 2 = 2 := (hJρ 2).1 h2J
  have hS := semiDirect_levi (K := K) J
  have hmM : hS.proj y ∈ parabolicLevi Tag.D4 K J := hS.proj_mem hy
  have hmP : hS.proj y ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hmM
  have hm2 : hS.proj y * hS.proj y = 1 := by
    rw [← hS.proj_mul hy hy, hy2, hS.proj_of_mem_M (one_mem _)]
  have hbarm : hS.bar (phiG g a σ ε) (hS.proj y) = hS.proj y := by
    rw [hS.bar_proj _ hφP hφQ hy]
    unfold IsSemiDirect.bar
    rw [hφy]
  obtain ⟨e, he⟩ := split_two hK2 hmM hm2
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀ : ModGL Tag.D4 K, s₀ = ρ 2 e := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁def⟩ : ∃ s₁ : ModGL Tag.D4 K, s₁ = hS.bar (phiG g a σ ε) s₀ := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂def⟩ : ∃ s₂ : ModGL Tag.D4 K, s₂ = hS.bar (phiG g a σ ε) s₁ := ⟨_, rfl⟩
  have hs₀ : s₀ ∈ Lk K 2 := ⟨e, hs₀def.symm⟩
  have hs₁ : s₁ ∈ Lk K 2 := by
    rw [hs₁def]
    have := bar_Lk_le hJ hg hJρ hφP h2J hs₀
    rwa [hρ2] at this
  have hs₂ : s₂ ∈ Lk K 2 := by
    rw [hs₂def]
    have := bar_Lk_le hJ hg hJρ hφP h2J hs₁
    rwa [hρ2] at this
  have hbar3 : hS.bar (phiG g a σ ε) s₂ = s₀ := by
    rw [hs₂def, hs₁def]
    exact hS.bar_bar_bar _ hφP hφQ hφ3 (Lk_le_levi h2J hs₀)
  have hs₀M : s₀ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi h2J hs₀
  have hs₁M : s₁ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi h2J hs₁
  have hs₂M : s₂ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi h2J hs₂
  have hn₀ : s₀⁻¹ * hS.proj y * s₀ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    obtain ⟨c', hc'⟩ := he c
    rw [hs₀def, hc']
    exact xUnit_mem_Uk _ _
  have hbarN : ∀ x ∈ parabolicLevi Tag.D4 K J,
      x ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) →
        hS.bar (phiG g a σ ε) x ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
    intro x hx hxN
    have := bar_mem_normalizer hJ hg hJρ hφP hφQ hφ3 h2J hx hxN
    rwa [hρ2] at this
  have hbar_mul : ∀ {x x' : ModGL Tag.D4 K}, x ∈ parabolicSubgroup Tag.D4 K J →
      x' ∈ parabolicSubgroup Tag.D4 K J →
      hS.bar (phiG g a σ ε) (x * x') = hS.bar (phiG g a σ ε) x * hS.bar (phiG g a σ ε) x' :=
    fun hx hx' => hS.bar_mul _ hφP hx hx'
  have hbar_conj : ∀ x ∈ parabolicLevi Tag.D4 K J,
      hS.bar (phiG g a σ ε) (x⁻¹ * hS.proj y * x) =
        (hS.bar (phiG g a σ ε) x)⁻¹ * hS.proj y * hS.bar (phiG g a σ ε) x := by
    intro x hx
    have hxP := hS.M_le hx
    rw [hbar_mul (mul_mem (inv_mem hxP) hmP) hxP, hbar_mul (inv_mem hxP) hmP,
      hS.bar_inv _ hφP hxP, hbarm]
  have hbar_div : ∀ x x' : ModGL Tag.D4 K, x ∈ parabolicLevi Tag.D4 K J →
      x' ∈ parabolicLevi Tag.D4 K J →
      hS.bar (phiG g a σ ε) (x⁻¹ * x') =
        (hS.bar (phiG g a σ ε) x)⁻¹ * hS.bar (phiG g a σ ε) x' := by
    intro x x' hx hx'
    rw [hbar_mul (inv_mem (hS.M_le hx)) (hS.M_le hx'), hS.bar_inv _ hφP (hS.M_le hx)]
  by_cases hc : s₀⁻¹ * s₁ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K))
  · refine ⟨s₀, hs₀M, key_of_split hJ hφP hy hs₀M (fun j hj => ?_) (fun j hj => ?_)⟩
    · have hj2 : j = 2 := hj
      subst hj2; exact hn₀
    · have hj2 : j = 2 := hj
      subst hj2; rw [← hs₁def]; exact hc
  · have m₁ : s₁⁻¹ * hS.proj y * s₁ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
      have := hbarN _ (mul_mem (mul_mem (inv_mem hs₀M) hmM) hs₀M) hn₀
      rwa [hbar_conj s₀ hs₀M, ← hs₁def] at this
    have m₂ : s₂⁻¹ * hS.proj y * s₂ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
      have := hbarN _ (mul_mem (mul_mem (inv_mem hs₁M) hmM) hs₁M) m₁
      rwa [hbar_conj s₁ hs₁M, ← hs₂def] at this
    have e12 : hS.bar (phiG g a σ ε) (s₁⁻¹ * s₂) = s₂⁻¹ * s₀ := by
      rw [hbar_div s₁ s₂ hs₁M hs₂M, ← hs₂def, hbar3]
    have e20 : hS.bar (phiG g a σ ε) (s₂⁻¹ * s₀) = s₀⁻¹ * s₁ := by
      rw [hbar_div s₂ s₀ hs₂M hs₀M, hbar3, ← hs₁def]
    have d12 : s₁⁻¹ * s₂ ∉ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
      intro h
      have h1 := hbarN _ (mul_mem (inv_mem hs₁M) hs₂M) h
      rw [e12] at h1
      have h2 := hbarN _ (mul_mem (inv_mem hs₂M) hs₀M) h1
      rw [e20] at h2
      exact hc h2
    have d02 : s₀⁻¹ * s₂ ∉ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
      intro h
      have h1 : s₂⁻¹ * s₀ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
        have := inv_mem h
        simpa using this
      have h2 := hbarN _ (mul_mem (inv_mem hs₂M) hs₀M) h1
      rw [e20] at h2
      exact hc h2
    have hmN := three_stable_normalizes hK2 hmM hs₀ hs₁ hs₂ hn₀ m₁ m₂ hc d02 d12
    refine ⟨1, one_mem _, key_of_split hJ hφP hy (one_mem _) (fun j hj => ?_) (fun j hj => ?_)⟩
    · have hj2 : j = 2 := hj
      subst hj2; simpa using hmN
    · rw [hS.bar_one]; simpa using one_mem _

end Key2

end CFSG.LocalAnalysis.GLTheoremA
