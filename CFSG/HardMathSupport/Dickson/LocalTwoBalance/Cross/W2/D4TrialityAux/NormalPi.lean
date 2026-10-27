module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Faithful

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial

section NormalPi


variable {K : Type} [Field K] [Finite K]

theorem normalGraph_mem (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε ∈ unipotentPairAut Tag.D4 K :=
  mul_mem (exactNormalAut_mem _ _ _) (d4Graph_mem ε)

theorem simplePermHom_normalGraph (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    simplePermHom Tag.D4 K ⟨exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε, normalGraph_mem a σ ε⟩ =
      d4Rho ^ ε :=
  perm_map_simple_unique
    (α := exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)
    (fun i => (simplePerm_spec (τ := Tag.D4) (K := K)
      ⟨exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε, normalGraph_mem a σ ε⟩ i).1)
    (fun i => map_simplePosSubgroup_of_adjX
      (f := fun c => (a ((d4Rho ^ ε) i) : K) * σ c)
      (fun d => ⟨σ.symm ((((a ((d4Rho ^ ε) i))⁻¹ : Kˣ) : K) * d), by simp⟩)
      (fun c => normalGraph_apply_adjX a σ ε i c))

theorem simplePermHom_conj {h : adjointGroup Tag.D4 K}
    (hA : MulAut.conj h ∈ unipotentPairAut Tag.D4 K) :
    simplePermHom Tag.D4 K ⟨MulAut.conj h, hA⟩ = 1 := by
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
  refine perm_map_simple_unique (α := MulAut.conj h)
    (fun i => (simplePerm_spec (τ := Tag.D4) (K := K) ⟨MulAut.conj h, hA⟩ i).1)
    (fun i => ?_)
  rw [hb, map_simplePosSubgroup_exactNormalAut b 1 0 i]
  rfl

theorem pow_conj_mul {G : Type*} [Group G] (c : G) (β : MulAut G) (n : ℕ) :
    ∃ c' : G, (MulAut.conj c * β) ^ n = MulAut.conj c' * β ^ n := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨c', hc'⟩ := ih
    refine ⟨c' * (β ^ n) c, ?_⟩
    rw [pow_succ, hc', pow_succ, map_mul, mul_assoc, mul_assoc, ← mul_assoc (β ^ n),
      mul_conj_eq]
    simp only [mul_assoc]

theorem exists_normalAut_of_commute_graphOne (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (Ξ : MulAut (adjointGroup Tag.D4 K))
    (hcop : Nat.Coprime 3 (orderOf Ξ))
    (hcomm : Ξ * (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) =
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) * Ξ) :
    ∃ (c : adjointGroup Tag.D4 K) (a' : Fin Tag.D4.rank → Kˣ) (σ' : K ≃+* K),
      Ξ = MulAut.conj c * exactNormalAut Tag.D4 K a' σ' 0 := by
  classical
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, hΞ⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 Ξ
  have hβA : β ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  set ν : MulAut (adjointGroup Tag.D4 K) := exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1 with hν
  have hνA : ν ∈ unipotentPairAut Tag.D4 K := normalGraph_mem a 1 1
  have hπν : simplePermHom Tag.D4 K ⟨ν, hνA⟩ = d4Rho := by
    have := simplePermHom_normalGraph a (1 : K ≃+* K) 1
    rwa [pow_one] at this
  obtain ⟨h, hh⟩ : ∃ h : adjointGroup Tag.D4 K, h = (g * ν c)⁻¹ * (c * β g) := ⟨_, rfl⟩
  rw [hΞ] at hcomm
  have e1 : (MulAut.conj c * β) * (MulAut.conj g * ν) = MulAut.conj (c * β g) * (β * ν) := by
    calc _ = MulAut.conj c * ((β * MulAut.conj g) * ν) := by simp only [mul_assoc]
      _ = MulAut.conj c * ((MulAut.conj (β g) * β) * ν) := by rw [mul_conj_eq]
      _ = MulAut.conj (c * β g) * (β * ν) := by rw [map_mul]; simp only [mul_assoc]
  have e2 : (MulAut.conj g * ν) * (MulAut.conj c * β) = MulAut.conj (g * ν c) * (ν * β) := by
    calc _ = MulAut.conj g * ((ν * MulAut.conj c) * β) := by simp only [mul_assoc]
      _ = MulAut.conj g * ((MulAut.conj (ν c) * ν) * β) := by rw [mul_conj_eq]
      _ = MulAut.conj (g * ν c) * (ν * β) := by rw [map_mul]; simp only [mul_assoc]
  have e3 : MulAut.conj (c * β g) * (β * ν) = MulAut.conj (g * ν c) * (ν * β) := by
    rw [← e1, ← e2]
    exact hcomm
  have hrel : ν * β = MulAut.conj h * (β * ν) := by
    calc ν * β = (MulAut.conj (g * ν c))⁻¹ * (MulAut.conj (g * ν c) * (ν * β)) := by group
      _ = (MulAut.conj (g * ν c))⁻¹ * (MulAut.conj (c * β g) * (β * ν)) := by rw [e3]
      _ = MulAut.conj h * (β * ν) := by rw [hh]; simp only [map_mul, map_inv, mul_assoc]
  have hνβA : ν * β ∈ unipotentPairAut Tag.D4 K := mul_mem hνA hβA
  have hβνA : β * ν ∈ unipotentPairAut Tag.D4 K := mul_mem hβA hνA
  have hhA : MulAut.conj h ∈ unipotentPairAut Tag.D4 K := by
    have : MulAut.conj h = (ν * β) * (β * ν)⁻¹ := by rw [hrel]; group
    rw [this]
    exact mul_mem hνβA (inv_mem hβνA)
  have hπcomm : d4Rho * simplePermHom Tag.D4 K ⟨β, hβA⟩ = simplePermHom Tag.D4 K ⟨β, hβA⟩ * d4Rho := by
    have h1 : (⟨ν * β, hνβA⟩ : unipotentPairAut Tag.D4 K) =
        ⟨MulAut.conj h, hhA⟩ * ⟨β * ν, hβνA⟩ := Subtype.ext hrel
    have h2 := congrArg (simplePermHom Tag.D4 K) h1
    have h3 : (⟨ν * β, hνβA⟩ : unipotentPairAut Tag.D4 K) = ⟨ν, hνA⟩ * ⟨β, hβA⟩ := rfl
    have h4 : (⟨β * ν, hβνA⟩ : unipotentPairAut Tag.D4 K) = ⟨β, hβA⟩ * ⟨ν, hνA⟩ := rfl
    have hI : simplePermHom Tag.D4 K ⟨MulAut.conj h, hhA⟩ = 1 := simplePermHom_conj hhA
    rw [h3, h4, map_mul, map_mul, map_mul, hI, one_mul, hπν] at h2
    exact h2
  have hπ1 : simplePermHom Tag.D4 K ⟨β, hβA⟩ = 1 := by
    set n := orderOf Ξ with hn
    obtain ⟨c', hc'⟩ := pow_conj_mul c β n
    have hΞn : (MulAut.conj c * β) ^ n = 1 := by rw [← hΞ]; exact pow_orderOf_eq_one Ξ
    have hβn : β ^ n = MulAut.conj c'⁻¹ := by
      rw [hc'] at hΞn
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right hΞn
    have hAn : MulAut.conj c'⁻¹ ∈ unipotentPairAut Tag.D4 K := hβn ▸ pow_mem hβA n
    have h1 : simplePermHom Tag.D4 K ⟨β, hβA⟩ ^ n = 1 := by
      rw [← map_pow]
      have : (⟨β, hβA⟩ : unipotentPairAut Tag.D4 K) ^ n = ⟨MulAut.conj c'⁻¹, hAn⟩ :=
        Subtype.ext (by simpa using hβn)
      rw [this]
      exact simplePermHom_conj hAn
    have hdvd : orderOf (simplePermHom Tag.D4 K ⟨β, hβA⟩) ∣ n := orderOf_dvd_of_pow_eq_one h1
    rcases perm_commute_d4Rho _ hπcomm.symm with h | h | h
    · exact h
    · exfalso
      rw [h, orderOf_d4Rho] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)
    · exfalso
      rw [h, orderOf_d4Rho_sq] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)
  have hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have h := simplePerm_spec (τ := Tag.D4) (K := K) ⟨β, hβA⟩ i
    have h1 : simplePerm Tag.D4 K ⟨β, hβA⟩ = 1 := hπ1
    rw [h1] at h
    simpa using h
  obtain ⟨a', σ', hβ⟩ := exists_normalAut_mul_graph hε
  rw [d4Graph_zero_f, mul_one] at hβ
  exact ⟨c, a', σ', by rw [hΞ, hβ]⟩

end NormalPi

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
