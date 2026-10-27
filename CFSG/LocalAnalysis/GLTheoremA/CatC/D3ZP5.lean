module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZP4

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Split

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

variable {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}

theorem bar_step (hg : g ∈ borelGroup Tag.D4 K)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {m : ModGL Tag.D4 K} (hm : m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hbm : (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m = m)
    {k : Fin Tag.D4.rank} (hk : k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) {t : ModGL Tag.D4 K}
    (ht : t ∈ Lk K k) (hn : t⁻¹ * m * t ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K))) :
    (d4Rho ^ ε) k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ∧
      (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) t ∈
        Lk K ((d4Rho ^ ε) k) ∧
      ((semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) t)⁻¹ * m *
        (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) t ∈
        Subgroup.normalizer (Uk K ((d4Rho ^ ε) k) : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set J : Set (Fin Tag.D4.rank) := {0, 1, 3} with hJdef
  have hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Or.inr rfl
  have hS := semiDirect_levi (K := K) J
  have htM : t ∈ parabolicLevi Tag.D4 K J := Lk_le_levi hk ht
  have htP := hS.M_le htM
  have hmP := hS.M_le hm
  refine ⟨(hJρ k).1 hk, bar_Lk_le hJ hg hJρ hφP hk ht, ?_⟩
  have h1 := bar_mem_normalizer hJ hg hJρ hφP hφQ hφ3 hk (mul_mem (mul_mem (inv_mem htM) hm) htM) hn
  have hbar_mul : ∀ {x x' : ModGL Tag.D4 K}, x ∈ parabolicSubgroup Tag.D4 K J →
      x' ∈ parabolicSubgroup Tag.D4 K J →
      hS.bar (phiG g a σ ε) (x * x') = hS.bar (phiG g a σ ε) x * hS.bar (phiG g a σ ε) x' :=
    fun hx hx' => hS.bar_mul _ hφP hx hx'
  rwa [hbar_mul (mul_mem (inv_mem htP) hmP) htP, hbar_mul (inv_mem htP) hmP,
    hS.bar_inv _ hφP htP, hbm] at h1

theorem split_at_all (hg : g ∈ borelGroup Tag.D4 K) (hε : ε = 1 ∨ ε = 2)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {m : ModGL Tag.D4 K} (hm : m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hbm : (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m = m)
    {k₀ : Fin Tag.D4.rank} (hk₀ : k₀ ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) {t₀ : ModGL Tag.D4 K}
    (ht₀ : t₀ ∈ Lk K k₀)
    (hn : t₀⁻¹ * m * t₀ ∈ Subgroup.normalizer (Uk K k₀ : Set (ModGL Tag.D4 K))) :
    ∀ j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)), ∃ t ∈ Lk K j,
      t⁻¹ * m * t ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
  intro j hj
  rcases (rho_cycle hε hk₀ hj).2.2.2.2.2 with rfl | rfl | rfl
  · exact ⟨t₀, ht₀, hn⟩
  · obtain ⟨-, ht₁, hn₁⟩ := bar_step hg hJρ hφP hφQ hφ3 hm hbm hk₀ ht₀ hn
    exact ⟨_, ht₁, hn₁⟩
  · obtain ⟨hk₁, ht₁, hn₁⟩ := bar_step hg hJρ hφP hφQ hφ3 hm hbm hk₀ ht₀ hn
    obtain ⟨-, ht₂, hn₂⟩ := bar_step hg hJρ hφP hφQ hφ3 hm hbm hk₁ ht₁ hn₁
    exact ⟨_, ht₂, hn₂⟩

theorem split_all_factors (hK2 : ringChar K ≠ 2) (hg : g ∈ borelGroup Tag.D4 K) (hε : ε = 1 ∨ ε = 2)
    (hJρ : ∀ i, i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      (d4Rho ^ ε) i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε q ∈ parabolicRadical Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)),
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {m : ModGL Tag.D4 K} (hm : m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hm2 : m * m = 1)
    (hbm : (semiDirect_levi (K := K) ({0, 1, 3} : Set (Fin Tag.D4.rank))).bar (phiG g a σ ε) m = m) :
    ∀ j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)), ∃ e : SL2 K,
      (ρ j e)⁻¹ * m * ρ j e ∈ Subgroup.normalizer (Uk K j : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨k₀, hk₀, e₀, he₀⟩ := split_three hK2 hm hm2
  have hn₀ : (ρ k₀ e₀)⁻¹ * m * ρ k₀ e₀ ∈ Subgroup.normalizer (Uk K k₀ : Set (ModGL Tag.D4 K)) := by
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    obtain ⟨c', hc'⟩ := he₀ c
    rw [hc']
    exact xUnit_mem_Uk _ _
  intro j hj
  obtain ⟨t, ht, hn⟩ := split_at_all hg hε hJρ hφP hφQ hφ3 hm hbm hk₀ (t₀ := ρ k₀ e₀) ⟨e₀, rfl⟩ hn₀ j hj
  obtain ⟨e, rfl⟩ := mem_Lk.1 ht
  exact ⟨e, hn⟩

theorem common_at_factor (hK2 : ringChar K ≠ 2) {k : Fin Tag.D4.rank} (b b' : Fin Tag.D4.rank → Kˣ)
    (A A' : SL2 K) (R R' : ModGL Tag.D4 K) (hR : ∀ Y : SL2 K, Commute R (ρ k Y))
    (hR' : ∀ Y : SL2 K, Commute R' (ρ k Y))
    (hlift : dconj ((b' k)⁻¹) A * A' = dconj ((b k)⁻¹) A' * A) {e₁ e₂ : SL2 K}
    (h₁ : (ρ k e₁)⁻¹ * (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k e₁ ∈
      Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)))
    (h₂ : (ρ k e₂)⁻¹ * (rootDiagUnit Tag.D4 b' * (ρ k A' * R')) * ρ k e₂ ∈
      Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K))) :
    ∃ e : SL2 K, (ρ k e)⁻¹ * (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k e ∈
        Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) ∧
      (ρ k e)⁻¹ * (rootDiagUnit Tag.D4 b' * (ρ k A' * R')) * ρ k e ∈
        Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
  rw [normalizes_X10_k hK2 b k A e₁ R hR] at h₁
  rw [normalizes_X10_k hK2 b' k A' e₂ R' hR'] at h₂
  obtain ⟨lam, hlam⟩ := eigen_of_X10 (b k) A e₁ h₁
  obtain ⟨lam', hlam'⟩ := eigen_of_X10 (b' k) A' e₂ h₂
  have hg := gmat_comm (b k) (b' k) A A' hlift
  obtain ⟨w, hw0, ⟨μ, hμ⟩, ⟨μ', hμ'⟩⟩ := common_eigen hg (col0_ne_zero e₁) (col0_ne_zero e₂) hlam hlam'
  obtain ⟨e, he0, he1⟩ := exists_SL2_firstCol w hw0
  have hcol : col0 e = w := by
    funext i
    fin_cases i
    · exact he0
    · exact he1
  refine ⟨e, ?_, ?_⟩
  · rw [normalizes_X10_k hK2 b k A e R hR]
    exact X10_of_eigen (b k) A e (l := μ) (by rw [hcol]; exact hμ)
  · rw [normalizes_X10_k hK2 b' k A' e R' hR']
    exact X10_of_eigen (b' k) A' e (l := μ') (by rw [hcol]; exact hμ')

theorem three_form (b : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K) :
    (∃ R : ModGL Tag.D4 K, (∀ Y : SL2 K, Commute R (ρ 0 Y)) ∧
      rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) = rootDiagUnit Tag.D4 b * (ρ 0 A₀ * R)) ∧
    (∃ R : ModGL Tag.D4 K, (∀ Y : SL2 K, Commute R (ρ 1 Y)) ∧
      rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) = rootDiagUnit Tag.D4 b * (ρ 1 A₁ * R)) ∧
    (∃ R : ModGL Tag.D4 K, (∀ Y : SL2 K, Commute R (ρ 3 Y)) ∧
      rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) = rootDiagUnit Tag.D4 b * (ρ 3 A₃ * R)) := by
  refine ⟨⟨ρ 1 A₁ * ρ 3 A₃, fun Y => (comm01 Y A₁).symm.mul_left (comm03 Y A₃).symm, rfl⟩,
    ⟨ρ 0 A₀ * ρ 3 A₃, fun Y => (comm01 A₀ Y).mul_left (comm13 Y A₃).symm, ?_⟩,
    ⟨ρ 0 A₀ * ρ 1 A₁, fun Y => (comm03 A₀ Y).mul_left (comm13 A₁ Y), ?_⟩⟩
  · congr 1
    calc ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃) = (ρ 0 A₀ * ρ 1 A₁) * ρ 3 A₃ := by group
      _ = (ρ 1 A₁ * ρ 0 A₀) * ρ 3 A₃ := by rw [(comm01 A₀ A₁).eq]
      _ = _ := by group
  · congr 1
    calc ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃) = ρ 0 A₀ * (ρ 3 A₃ * ρ 1 A₁) := by rw [(comm13 A₁ A₃).eq]
      _ = (ρ 0 A₀ * ρ 3 A₃) * ρ 1 A₁ := by group
      _ = (ρ 3 A₃ * ρ 0 A₀) * ρ 1 A₁ := by rw [(comm03 A₀ A₃).eq]
      _ = _ := by group

end Split

end CFSG.LocalAnalysis.GLTheoremA
