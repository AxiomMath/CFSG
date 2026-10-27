module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL7

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped Pointwise


section Cores

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

variable {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ}
  {σ : K ≃+* K} {ε : ℕ}

theorem levi_two_s (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K)
    (hJρ : ∀ i, i ∈ ({2} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({2} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({2} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {s₀ : ModGL Tag.D4 K} (hs₀ : s₀ ∈ Lk K 2) :
    ∃ s ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
      s⁻¹ * (semiDirect_levi (K := K) ({2} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) s ∈
        Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) ∧
      ∀ m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank)),
        (semiDirect_levi (K := K) ({2} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m = m →
        s₀⁻¹ * m * s₀ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) →
          s⁻¹ * m * s ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {2} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inl rfl
  have h2J : (2 : Fin Tag.D4.rank) ∈ J := rfl
  have hρ2 : (d4Rho ^ ε) 2 = 2 := (hJρ 2).1 h2J
  have hS := semiDirect_levi (K := K) J
  obtain ⟨s₁, hs₁def⟩ : ∃ s₁ : ModGL Tag.D4 K, s₁ = hS.bar (phiG g a σ ε) s₀ := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂def⟩ : ∃ s₂ : ModGL Tag.D4 K, s₂ = hS.bar (phiG g a σ ε) s₁ := ⟨_, rfl⟩
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
  have hbar_div : ∀ x x' : ModGL Tag.D4 K, x ∈ parabolicLevi Tag.D4 K J →
      x' ∈ parabolicLevi Tag.D4 K J →
      hS.bar (phiG g a σ ε) (x⁻¹ * x') =
        (hS.bar (phiG g a σ ε) x)⁻¹ * hS.bar (phiG g a σ ε) x' := by
    intro x x' hx hx'
    rw [hbar_mul (inv_mem (hS.M_le hx)) (hS.M_le hx'), hS.bar_inv _ hφP (hS.M_le hx)]
  by_cases hc : s₀⁻¹ * s₁ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K))
  · refine ⟨s₀, hs₀M, ?_, fun m _ _ h => h⟩
    rw [← hs₁def]; exact hc
  · have e12 : hS.bar (phiG g a σ ε) (s₁⁻¹ * s₂) = s₂⁻¹ * s₀ := by
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
    refine ⟨1, one_mem _, ?_, fun m hmM hbm hm₀ => ?_⟩
    · rw [hS.bar_one]; simpa using one_mem _
    · have hmP : m ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hmM
      have hbar_conj : ∀ x ∈ parabolicLevi Tag.D4 K J,
          hS.bar (phiG g a σ ε) (x⁻¹ * m * x) =
            (hS.bar (phiG g a σ ε) x)⁻¹ * m * hS.bar (phiG g a σ ε) x := by
        intro x hx
        have hxP := hS.M_le hx
        rw [hbar_mul (mul_mem (inv_mem hxP) hmP) hxP, hbar_mul (inv_mem hxP) hmP,
          hS.bar_inv _ hφP hxP, hbm]
      have m₁ : s₁⁻¹ * m * s₁ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
        have := hbarN _ (mul_mem (mul_mem (inv_mem hs₀M) hmM) hs₀M) hm₀
        rwa [hbar_conj s₀ hs₀M, ← hs₁def] at this
      have m₂ : s₂⁻¹ * m * s₂ ∈ Subgroup.normalizer (Uk K 2 : Set (ModGL Tag.D4 K)) := by
        have := hbarN _ (mul_mem (mul_mem (inv_mem hs₁M) hmM) hs₁M) m₁
        rwa [hbar_conj s₁ hs₁M, ← hs₂def] at this
      have hmN := three_stable_normalizes hK2 hmM hs₀ hs₁ hs₂ hm₀ m₁ m₂ hc d02 d12
      simpa using hmN

theorem levi_three_s (hg : g ∈ borelGroup Tag.D4 K) (hε : ε = 1 ∨ ε = 2)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {k₀ : Fin Tag.D4.rank} (hk₀ : k₀ ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    {t₀ : ModGL Tag.D4 K} (ht₀ : t₀ ∈ Lk K k₀) :
    ∃ s ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) s = s ∧
      ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
        (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m = m →
        t₀⁻¹ * m * t₀ ∈ Subgroup.normalizer (Uk K k₀ : Set (ModGL Tag.D4 K)) →
          ∀ j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)),
            s⁻¹ * m * s ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {0, 1, 3} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inr rfl
  have hS := semiDirect_levi (K := K) J
  obtain ⟨hk₁, hne1, hne2, hne12, hcyc, -⟩ := rho_cycle hε hk₀ hk₀
  have hk₁J : (d4Rho ^ ε) k₀ ∈ J := hk₁
  have hk₂J : (d4Rho ^ ε) ((d4Rho ^ ε) k₀) ∈ J := (hJρ _).1 hk₁J
  have hbar_mul : ∀ {x x' : ModGL Tag.D4 K}, x ∈ parabolicSubgroup Tag.D4 K J →
      x' ∈ parabolicSubgroup Tag.D4 K J →
      hS.bar (phiG g a σ ε) (x * x') = hS.bar (phiG g a σ ε) x * hS.bar (phiG g a σ ε) x' :=
    fun hx hx' => hS.bar_mul _ hφP hx hx'
  obtain ⟨t₁, ht₁def⟩ : ∃ t₁ : ModGL Tag.D4 K, t₁ = hS.bar (phiG g a σ ε) t₀ := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂def⟩ : ∃ t₂ : ModGL Tag.D4 K, t₂ = hS.bar (phiG g a σ ε) t₁ := ⟨_, rfl⟩
  have ht₁ : t₁ ∈ Lk K ((d4Rho ^ ε) k₀) := by
    rw [ht₁def]; exact bar_Lk_le hJ hg hJρ hφP hk₀ ht₀
  have ht₂ : t₂ ∈ Lk K ((d4Rho ^ ε) ((d4Rho ^ ε) k₀)) := by
    rw [ht₂def]; exact bar_Lk_le hJ hg hJρ hφP hk₁J ht₁
  have hbar3 : hS.bar (phiG g a σ ε) t₂ = t₀ := by
    rw [ht₂def, ht₁def]
    exact hS.bar_bar_bar _ hφP hφQ hφ3 (Lk_le_levi hk₀ ht₀)
  have ht₀M : t₀ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk₀ ht₀
  have ht₁M : t₁ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk₁J ht₁
  have ht₂M : t₂ ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk₂J ht₂
  have c01 : Commute t₀ t₁ := commute_Lk hk₀ hk₁ (Ne.symm hne1) ht₀ ht₁
  have c02 : Commute t₀ t₂ := commute_Lk hk₀ hk₂J (Ne.symm hne2) ht₀ ht₂
  have c12 : Commute t₁ t₂ := commute_Lk hk₁ hk₂J (Ne.symm hne12) ht₁ ht₂
  have hsM : t₀ * t₁ * t₂ ∈ parabolicLevi Tag.D4 K J := mul_mem (mul_mem ht₀M ht₁M) ht₂M
  have hsP : t₀ * t₁ * t₂ ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hsM
  have hbs : hS.bar (phiG g a σ ε) (t₀ * t₁ * t₂) = t₀ * t₁ * t₂ := by
    rw [hbar_mul (hS.M_le (mul_mem ht₀M ht₁M)) (hS.M_le ht₂M),
      hbar_mul (hS.M_le ht₀M) (hS.M_le ht₁M), ← ht₁def, ← ht₂def, hbar3]
    calc t₁ * t₂ * t₀ = t₁ * (t₂ * t₀) := by group
      _ = t₁ * (t₀ * t₂) := by rw [c02.symm.eq]
      _ = (t₁ * t₀) * t₂ := by group
      _ = (t₀ * t₁) * t₂ := by rw [c01.symm.eq]
  refine ⟨t₀ * t₁ * t₂, hsM, hbs, fun m hmM hbm hme j hj => ?_⟩
  have hmP : m ∈ parabolicSubgroup Tag.D4 K J := hS.M_le hmM
  have hnM : (t₀ * t₁ * t₂)⁻¹ * m * (t₀ * t₁ * t₂) ∈ parabolicLevi Tag.D4 K J :=
    mul_mem (mul_mem (inv_mem hsM) hmM) hsM
  have hbn : hS.bar (phiG g a σ ε) ((t₀ * t₁ * t₂)⁻¹ * m * (t₀ * t₁ * t₂)) =
      (t₀ * t₁ * t₂)⁻¹ * m * (t₀ * t₁ * t₂) := by
    rw [hbar_mul (mul_mem (inv_mem hsP) hmP) hsP, hbar_mul (inv_mem hsP) hmP,
      hS.bar_inv _ hφP hsP, hbs, hbm]
  have hn0 : (t₀ * t₁ * t₂)⁻¹ * m * (t₀ * t₁ * t₂) ∈
      Subgroup.normalizer (Uk K k₀ : Set (ModGL Tag.D4 K)) := by
    have e1 : (t₀ * t₁ * t₂)⁻¹ * m * (t₀ * t₁ * t₂) =
        (t₁ * t₂)⁻¹ * (t₀⁻¹ * m * t₀) * (t₁ * t₂) := by group
    rw [e1]
    refine normalizer_conj_of_commute _ hme fun u hu => ?_
    exact (commute_Lk hk₁ hk₀ hne1 ht₁ (Uk_le_Lk _ hu)).mul_left
      (commute_Lk hk₂J hk₀ hne2 ht₂ (Uk_le_Lk _ hu))
  have hn1 := bar_normalizes hJ hg hJρ hφP hφQ hφ3 hk₀ hnM hbn hn0
  have hn2 := bar_normalizes hJ hg hJρ hφP hφQ hφ3 hk₁J hnM hbn hn1
  rcases (rho_cycle hε hk₀ hj).2.2.2.2.2 with rfl | rfl | rfl
  · exact hn0
  · exact hn1
  · exact hn2

end Cores

end CFSG.LocalAnalysis.GLTheoremA
