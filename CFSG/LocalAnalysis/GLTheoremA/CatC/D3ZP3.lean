module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZP1
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZP2

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Pair

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem torus_rho_mem_iff (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (X : SL2 K) :
    rootDiagUnit Tag.D4 b * ρ 2 X ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) ↔
      (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have hT := rootDiagUnit_mem_normalizer_Uk (K := K) b 2
  exact ⟨fun h => (rho_mem_normalizer_iff hK2 X).1 (by
        have := mul_mem (inv_mem hT) h
        simpa using this),
      fun h => mul_mem hT ((rho_mem_normalizer_iff hK2 X).2 h)⟩

theorem normalizes_of_X10 (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (A e : SL2 K) :
    (ρ 2 e)⁻¹ * (rootDiagUnit Tag.D4 b * ρ 2 A) * ρ 2 e ∈
        Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) ↔
      ((dconj ((b 2)⁻¹) e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [conj_rho_two, torus_rho_mem_iff hK2]

theorem common_split_two (hK2 : ringChar K ≠ 2) {m m' : ModGL Tag.D4 K}
    (hm : m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hm' : m' ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hm2 : m * m = 1) (hm'2 : m' * m' = 1) (hcomm : m * m' = m' * m) :
    ∃ e : SL2 K, (ρ 2 e)⁻¹ * m * ρ 2 e ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) ∧
      (ρ 2 e)⁻¹ * m' * ρ 2 e ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨e₀, he₀⟩ := split_two hK2 hm hm2
  obtain ⟨e₀', he₀'⟩ := split_two hK2 hm' hm'2
  have hn₀ : (ρ 2 e₀)⁻¹ * m * ρ 2 e₀ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    obtain ⟨c', hc'⟩ := he₀ c
    rw [hc']
    exact xUnit_mem_Uk _ _
  have hn₀' : (ρ 2 e₀')⁻¹ * m' * ρ 2 e₀' ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    obtain ⟨c', hc'⟩ := he₀' c
    rw [hc']
    exact xUnit_mem_Uk _ _
  clear he₀ he₀'
  obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hm
  have hl' : l ∈ (ρ 2).range := by
    rw [range_simpleRootSL2, ← leviRoot_singleton]; exact hl
  obtain ⟨A, rfl⟩ := hl'
  obtain ⟨b', l', hl'', rfl⟩ := exists_eq_rootDiagUnit_mul hm'
  have hl3 : l' ∈ (ρ 2).range := by
    rw [range_simpleRootSL2, ← leviRoot_singleton]; exact hl''
  obtain ⟨A', rfl⟩ := hl3
  rw [normalizes_of_X10 hK2] at hn₀ hn₀'
  obtain ⟨lam, hlam⟩ := eigen_of_X10 (b 2) A e₀ hn₀
  obtain ⟨lam', hlam'⟩ := eigen_of_X10 (b' 2) A' e₀' hn₀'
  have hXeq : dconj ((b' 2)⁻¹) A * A' = dconj ((b 2)⁻¹) A' * A := by
    have e1 : (rootDiagUnit Tag.D4 b * ρ 2 A) * (rootDiagUnit Tag.D4 b' * ρ 2 A') =
        rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b' * ρ 2 (dconj ((b' 2)⁻¹) A * A') := by
      have := conj_inv_rho b' 2 A
      rw [map_mul, ← this]; group
    have e2 : (rootDiagUnit Tag.D4 b' * ρ 2 A') * (rootDiagUnit Tag.D4 b * ρ 2 A) =
        rootDiagUnit Tag.D4 b' * rootDiagUnit Tag.D4 b * ρ 2 (dconj ((b 2)⁻¹) A' * A) := by
      have := conj_inv_rho b 2 A'
      rw [map_mul, ← this]; group
    have e3 : rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b' =
        rootDiagUnit Tag.D4 b' * rootDiagUnit Tag.D4 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b b']
    rw [e1, e2, e3] at hcomm
    exact simpleRootSL2_injective hK2 2 (mul_left_cancel hcomm)
  have hg := gmat_comm (b 2) (b' 2) A A' hXeq
  obtain ⟨w, hw0, ⟨μ, hμ⟩, ⟨μ', hμ'⟩⟩ := common_eigen hg (col0_ne_zero e₀) (col0_ne_zero e₀') hlam hlam'
  obtain ⟨e, he0, he1⟩ := exists_SL2_firstCol w hw0
  have hcol : col0 e = w := by
    funext i
    fin_cases i
    · exact he0
    · exact he1
  refine ⟨e, ?_, ?_⟩
  · rw [normalizes_of_X10 hK2]
    exact X10_of_eigen (b 2) A e (l := μ) (by rw [hcol]; exact hμ)
  · rw [normalizes_of_X10 hK2]
    exact X10_of_eigen (b' 2) A' e (l := μ') (by rw [hcol]; exact hμ')

variable {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ}
  {σ : K ≃+* K} {ε : ℕ}

theorem levi_key_two_pair (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K)
    (hJρ : ∀ i, i ∈ ({2} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({2} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {y y' : ModGL Tag.D4 K} (hy : y ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hy' : y' ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hy2 : y * y = 1) (hy'2 : y' * y' = 1) (hcomm : y * y' = y' * y)
    (hφy : phiG g a σ ε y = y) (hφy' : phiG g a σ ε y' = y') :
    ∃ s ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * y' * s ∈ borelGroup Tag.D4 K ∧
        s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {2} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inl rfl
  have hS := semiDirect_levi (K := K) J
  have hmM : hS.proj y ∈ parabolicLevi Tag.D4 K J := hS.proj_mem hy
  have hm'M : hS.proj y' ∈ parabolicLevi Tag.D4 K J := hS.proj_mem hy'
  have hm2 : hS.proj y * hS.proj y = 1 := by
    rw [← hS.proj_mul hy hy, hy2, hS.proj_of_mem_M (one_mem _)]
  have hm'2 : hS.proj y' * hS.proj y' = 1 := by
    rw [← hS.proj_mul hy' hy', hy'2, hS.proj_of_mem_M (one_mem _)]
  have hmcomm : hS.proj y * hS.proj y' = hS.proj y' * hS.proj y := by
    rw [← hS.proj_mul hy hy', ← hS.proj_mul hy' hy, hcomm]
  have hbarm : hS.bar (phiG g a σ ε) (hS.proj y) = hS.proj y := by
    rw [hS.bar_proj _ hφP hφQ hy]
    unfold IsSemiDirect.bar
    rw [hφy]
  have hbarm' : hS.bar (phiG g a σ ε) (hS.proj y') = hS.proj y' := by
    rw [hS.bar_proj _ hφP hφQ hy']
    unfold IsSemiDirect.bar
    rw [hφy']
  obtain ⟨e, hn, hn'⟩ := common_split_two hK2 hmM hm'M hm2 hm'2 hmcomm
  obtain ⟨s, hsM, hs1, hs2⟩ := levi_two_s hK2 hg hJρ hφP hφQ hφ3 (s₀ := ρ 2 e) ⟨e, rfl⟩
  have hjJ : ∀ j ∈ J, j = 2 := fun j hj => hj
  have h1 : ∀ j ∈ J, s⁻¹ * hS.proj y * s ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
    intro j hj
    rw [hjJ j hj]; exact hs2 _ hmM hbarm hn
  have h1' : ∀ j ∈ J, s⁻¹ * hS.proj y' * s ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
    intro j hj
    rw [hjJ j hj]; exact hs2 _ hm'M hbarm' hn'
  have h2 : ∀ j ∈ J, s⁻¹ * hS.bar (phiG g a σ ε) s ∈
      Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
    intro j hj
    rw [hjJ j hj]; exact hs1
  exact ⟨s, hsM, (key_of_split hJ hφP hy hsM h1 h2).1, (key_of_split hJ hφP hy' hsM h1' h2).1,
    (key_of_split hJ hφP hy hsM h1 h2).2⟩

end Pair

end CFSG.LocalAnalysis.GLTheoremA
