module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZP5
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL8

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Pair3

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

variable {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}

theorem common_split_three (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K) (hε : ε = 1 ∨ ε = 2)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {m m' : ModGL Tag.D4 K} (hm : m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hm' : m' ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hm2 : m * m = 1) (hm'2 : m' * m' = 1) (hcomm : m * m' = m' * m)
    (hbm : (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m = m)
    (hbm' : (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m' = m') :
    ∃ k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)), ∃ e : SL2 K,
      (ρ k e)⁻¹ * m * ρ k e ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) ∧
      (ρ k e)⁻¹ * m' * ρ k e ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hsp := split_all_factors hK2 hg hε hJρ hφP hφQ hφ3 hm hm2 hbm
  have hsp' := split_all_factors hK2 hg hε hJρ hφP hφQ hφ3 hm' hm'2 hbm'
  obtain ⟨b, A₀, A₁, A₃, hmdef⟩ := levi_outer_decomp hm
  obtain ⟨b', A₀', A₁', A₃', hm'def⟩ := levi_outer_decomp hm'
  have hX : ρ 0 (dconj ((b' 0)⁻¹) A₀ * A₀') *
      (ρ 1 (dconj ((b' 1)⁻¹) A₁ * A₁') * ρ 3 (dconj ((b' 3)⁻¹) A₃ * A₃')) =
      ρ 0 (dconj ((b 0)⁻¹) A₀' * A₀) *
        (ρ 1 (dconj ((b 1)⁻¹) A₁' * A₁) * ρ 3 (dconj ((b 3)⁻¹) A₃' * A₃)) := by
    have e1 := prod_mul b b' A₀ A₁ A₃ A₀' A₁' A₃'
    have e2 := prod_mul b' b A₀' A₁' A₃' A₀ A₁ A₃
    have e3 : rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b' =
        rootDiagUnit Tag.D4 b' * rootDiagUnit Tag.D4 b := by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b b']
    rw [hmdef, hm'def, e1, e2, e3] at hcomm
    exact mul_left_cancel hcomm
  rcases exists_factor_eq hK2 _ _ _ _ _ _ hX with e0 | e1 | e3
  · obtain ⟨R, hR, hmR⟩ := (three_form b A₀ A₁ A₃).1
    obtain ⟨R', hR', hm'R⟩ := (three_form b' A₀' A₁' A₃').1
    obtain ⟨e₁, h₁⟩ := hsp 0 mem_outer0
    obtain ⟨e₂, h₂⟩ := hsp' 0 mem_outer0
    rw [hmdef, hmR] at h₁
    rw [hm'def, hm'R] at h₂
    obtain ⟨e, he1, he2⟩ := common_at_factor hK2 b b' A₀ A₀' R R' hR hR' e0 h₁ h₂
    exact ⟨0, mem_outer0, e, by rw [hmdef, hmR]; exact he1, by rw [hm'def, hm'R]; exact he2⟩
  · obtain ⟨R, hR, hmR⟩ := (three_form b A₀ A₁ A₃).2.1
    obtain ⟨R', hR', hm'R⟩ := (three_form b' A₀' A₁' A₃').2.1
    obtain ⟨e₁, h₁⟩ := hsp 1 mem_outer1
    obtain ⟨e₂, h₂⟩ := hsp' 1 mem_outer1
    rw [hmdef, hmR] at h₁
    rw [hm'def, hm'R] at h₂
    obtain ⟨e, he1, he2⟩ := common_at_factor hK2 b b' A₁ A₁' R R' hR hR' e1 h₁ h₂
    exact ⟨1, mem_outer1, e, by rw [hmdef, hmR]; exact he1, by rw [hm'def, hm'R]; exact he2⟩
  · obtain ⟨R, hR, hmR⟩ := (three_form b A₀ A₁ A₃).2.2
    obtain ⟨R', hR', hm'R⟩ := (three_form b' A₀' A₁' A₃').2.2
    obtain ⟨e₁, h₁⟩ := hsp 3 mem_outer3
    obtain ⟨e₂, h₂⟩ := hsp' 3 mem_outer3
    rw [hmdef, hmR] at h₁
    rw [hm'def, hm'R] at h₂
    obtain ⟨e, he1, he2⟩ := common_at_factor hK2 b b' A₃ A₃' R R' hR hR' e3 h₁ h₂
    exact ⟨3, mem_outer3, e, by rw [hmdef, hmR]; exact he1, by rw [hm'def, hm'R]; exact he2⟩

theorem levi_key_three_pair (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K) (hε : ε = 1 ∨ ε = 2)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {y y' : ModGL Tag.D4 K} (hy : y ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hy' : y' ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hy2 : y * y = 1) (hy'2 : y' * y' = 1) (hcomm : y * y' = y' * y)
    (hφy : phiG g a σ ε y = y) (hφy' : phiG g a σ ε y' = y') :
    ∃ s ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * y' * s ∈ borelGroup Tag.D4 K ∧
        s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {0, 1, 3} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inr rfl
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
  obtain ⟨k₀, hk₀, e, hn, hn'⟩ :=
    common_split_three hK2 hg hε hJρ hφP hφQ hφ3 hmM hm'M hm2 hm'2 hmcomm hbarm hbarm'
  obtain ⟨s, hsM, hsbar, hs2⟩ := levi_three_s hg hε hJρ hφP hφQ hφ3 hk₀ (t₀ := ρ k₀ e) ⟨e, rfl⟩
  have h1 : ∀ j ∈ J, s⁻¹ * hS.proj y * s ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) :=
    fun j hj => hs2 _ hmM hbarm hn j hj
  have h1' : ∀ j ∈ J, s⁻¹ * hS.proj y' * s ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) :=
    fun j hj => hs2 _ hm'M hbarm' hn' j hj
  have h2 : ∀ j ∈ J, s⁻¹ * hS.bar (phiG g a σ ε) s ∈
      Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
    intro j hj
    rw [hsbar, inv_mul_cancel]
    exact one_mem _
  exact ⟨s, hsM, (key_of_split hJ hφP hy hsM h1 h2).1, (key_of_split hJ hφP hy' hsM h1' h2).1,
    (key_of_split hJ hφP hy hsM h1 h2).2⟩

end Pair3

section Level

variable {K : Type} [Field K] [Finite K]

theorem levi_c_level_pair (hK2 : ringChar K ≠ 2) {g : ModGL Tag.D4 K} (hg : g ∈ borelGroup Tag.D4 K)
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hφ3 : ∀ x ∈ adjointGroup Tag.D4 K,
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε x)) = x)
    {A : Subgroup (ModGL Tag.D4 K)} (hB : borelGroup Tag.D4 K ≤ A) (hAC : A ≤ adjointGroup Tag.D4 K)
    (hAne : A ≠ adjointGroup Tag.D4 K) (hφA : ∀ x ∈ A, phiG g a σ ε x ∈ A)
    {y y' : ModGL Tag.D4 K} (hy : y ∈ A) (hy' : y' ∈ A) (hy2 : y * y = 1) (hy'2 : y' * y' = 1)
    (hcomm : y * y' = y' * y) (hφy : phiG g a σ ε y = y) (hφy' : phiG g a σ ε y' = y') :
    ∃ s ∈ A, s⁻¹ * y * s ∈ borelGroup Tag.D4 K ∧ s⁻¹ * y' * s ∈ borelGroup Tag.D4 K ∧
      s⁻¹ * phiG g a σ ε s ∈ borelGroup Tag.D4 K := by
  have hAP := eq_parabolicSubgroup_of_borelGroup_le hB hAC
  have hcells := standard_parabolic_cells Tag.D4 K
  set J : Set (Fin Tag.D4.rank) := {i | weylElt Tag.D4 K i 1 ∈ A} with hJ
  have hfwd : ∀ i, i ∈ J → (d4Rho ^ ε) i ∈ J := fun i hi => jstable hg a σ ε hB hφA hi
  have hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J := fun i =>
    ⟨hfwd i, fun h => by
      have := hfwd _ (hfwd _ h)
      rwa [rho_pow_thrice] at this⟩
  rcases jclass hε hJρ with h0 | h2 | h013 | huniv
  · have hAB : A = borelGroup Tag.D4 K := by rw [hAP, h0]; exact hcells.2.2.2.2.1
    refine ⟨1, one_mem _, ?_, ?_, ?_⟩
    · simpa [hAB] using (hAB ▸ hy : y ∈ borelGroup Tag.D4 K)
    · simpa [hAB] using (hAB ▸ hy' : y' ∈ borelGroup Tag.D4 K)
    · simpa using one_mem (borelGroup Tag.D4 K)
  · have hA2 : A = parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)) := by rw [hAP, h2]
    have hJρ' : ∀ i, i ∈ ({2} : Set (Fin Tag.D4.rank)) ↔
        (d4Rho ^ ε) i ∈ ({2} : Set (Fin Tag.D4.rank)) := by rw [h2] at hJρ; exact hJρ
    rw [hA2] at hy hy' hφA
    obtain ⟨s, hsM, hs1, hs1', hs2⟩ := levi_key_two_pair hK2 hg hJρ' hφA
      (phi_radical_le hg a σ hJρ')
      (fun m hm => hφ3 m (parabolicLevi_le_adjointGroup _ _ _ hm)) hy hy' hy2 hy'2 hcomm hφy hφy'
    exact ⟨s, hA2 ▸ parabolicLevi_le_parabolicSubgroup _ hsM, hs1, hs1', hs2⟩
  · have hA3 : A = parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
      rw [hAP, h013]
    have hJρ' : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
        (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by rw [h013] at hJρ; exact hJρ
    rw [hA3] at hy hy' hφA
    obtain ⟨s, hsM, hs1, hs1', hs2⟩ := levi_key_three_pair hK2 hg hε hJρ' hφA
      (phi_radical_le hg a σ hJρ')
      (fun m hm => hφ3 m (parabolicLevi_le_adjointGroup _ _ _ hm)) hy hy' hy2 hy'2 hcomm hφy hφy'
    exact ⟨s, hA3 ▸ parabolicLevi_le_parabolicSubgroup _ hsM, hs1, hs1', hs2⟩
  · exfalso
    apply hAne
    rw [hAP, huniv]
    exact hcells.2.2.2.2.2.1

end Level

end CFSG.LocalAnalysis.GLTheoremA
