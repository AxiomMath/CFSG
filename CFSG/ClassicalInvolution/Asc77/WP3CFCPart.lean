module

public import CFSG.ClassicalInvolution.Asc77.WP3CFCMoved
public import CFSG.ClassicalInvolution.Asc77.WP3SCVPart
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.AscIH8Red

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CFC

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77

section Partner

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}


theorem partner_member (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4) {R_K : Subgroup (compModel D j).K}
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K))
    {S : Subgroup (compModel D j).K}
    (hS : S ∈ fundamentalSubgroups (D.tag j) (compModel D j).D) (hc : Commutes R_K S) :
    ∃ N ∈ Ω, z ∈ trivialOnQuot N ∧ t ∈ trivialOnQuot N ∧
      modOdd (z * t) (exactCore (z * t) N) =
        S.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) := by
  have hΩ := hs.hyp
  have hfd := hs.frame
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hzC := zt_z_mem hs
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  obtain ⟨N₀, hN₀, hmod₀⟩ := SCV.vertex_exists_member_of_fund V j hG2 hD4 hS
  have hzK : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ R_K.map (V.psi j) := by
    have h1 : R_K.map (V.psi j) = modOdd (z * t) (exactCore (z * t) K) := hmodK
    rw [h1]
    exact oddQuotMk_mem_modOdd (V.involution_mem_exactCore (zt_memK hs) hKcl) hzC
  have hcomm₀ : ∀ y ∈ modOdd (z * t) (exactCore (z * t) N₀),
      oddQuotMk (z * t) ⟨z, hzC⟩ * y = y * oddQuotMk (z * t) ⟨z, hzC⟩ := by
    intro y hy
    rw [hmod₀] at hy
    obtain ⟨s, hs', rfl⟩ := hy
    obtain ⟨r, hr, hrz⟩ := hzK
    rw [← hrz, ← map_mul, ← map_mul]
    exact congrArg (V.psi j) (hc r hr s hs')
  have hz2 : z * z = 1 := hfd.hz.sq
  have hBel : IsElemAbelian 2 (Subgroup.zpowers z) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2', one_zpow]
  have hBC : Subgroup.zpowers z ≤ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hzC
  obtain ⟨N₁, hN₁, hmod₁, hBN₁⟩ := SCV.vertex_exists_member_normalized V hs.noTwins hBel hBC hN₀ (by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : (⟨z ^ k, hBC hx⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) =
        (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) ^ k :=
      Subtype.ext (by simp)
    rw [e, map_zpow]
    exact ((Commute.zpow_left (hcomm₀ y hy) k).eq))
  obtain ⟨w₁, hw₁⟩ := hΩ.classical N₁ hN₁.1
  have hzN₁ : z ∈ Subgroup.normalizer (N₁ : Set G) := hBN₁ (Subgroup.mem_zpowers z)
  have hz_tq : z ∈ trivialOnQuot N₁ := by
    refine mem_trivialOnQuot_of_centralizes_modOdd hw₁ (zt_hc2 hs) hN₁.2 hzC hzN₁ ?_
    intro y hy
    rw [hmod₁] at hy
    exact hcomm₀ y hy
  have ht_tq : t ∈ trivialOnQuot N₁ := by
    rw [zt_t_eq hs]
    exact Subgroup.mul_mem _ hz_tq hN₁.2
  refine ⟨N₁, hN₁.1, hz_tq, ht_tq, ?_⟩
  have h2 : modOdd (z * t) (exactCore (z * t) N₀) =
      S.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) := hmod₀
  exact hmod₁.trans h2

theorem partner_bound (hs : ChainFrameCore p f Ω K J K' z t z')
    (hThird : ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t))
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4)
    {R_K R_J : Subgroup (compModel D j).K}
    (hRK : R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hRJ : R_J ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K))
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J)) :
    ∃ a b : Subgroup (compModel D j).K,
      ∀ S ∈ SCV.Partners (fundamentalSubgroups (D.tag j) (compModel D j).D) R_K, S = a ∨ S = b := by
  classical
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  set ψ := secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j with hψ
  have hker : ψ.ker ≤ Subgroup.center (compModel D j).K := V.psi_ker j
  have hperf : ∀ S ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, S ≤ ⁅S, S⁆ :=
    fun S hS => (V.fund_perfect j hD4 hS).ge
  have key : ∀ S ∈ SCV.Partners (fundamentalSubgroups (D.tag j) (compModel D j).D) R_K,
      S ≠ R_J → ∃ N ∈ Ω, IsUniqueInvolution N (z * t) ∧
        modOdd (z * t) (exactCore (z * t) N) = S.map ψ := by
    intro S hS hSJ
    obtain ⟨N, hNΩ, hzN, htN, himg⟩ := partner_member hs D j hG2 hD4 hmodK hS.1 hS.2.2
    refine ⟨N, hNΩ, hThird N hNΩ ?_ ?_ hzN htN, himg⟩
    · intro hNK
      rw [hNK] at himg
      exact hS.2.1 (ih8_eq_of_map_eq ψ hker (hperf S hS.1) (hperf R_K hRK)
        (himg.symm.trans hmodK.symm))
    · intro hNJ
      rw [hNJ] at himg
      exact hSJ (ih8_eq_of_map_eq ψ hker (hperf S hS.1) (hperf R_J hRJ)
        (himg.symm.trans hmodJ.symm))
  by_cases h0 : ∃ S₀ ∈ SCV.Partners (fundamentalSubgroups (D.tag j) (compModel D j).D) R_K,
      S₀ ≠ R_J
  · obtain ⟨S₀, hS₀, hS₀J⟩ := h0
    refine ⟨R_J, S₀, fun S hS => ?_⟩
    by_cases hSJ : S = R_J
    · exact Or.inl hSJ
    · right
      obtain ⟨N, hNΩ, hNc, hNimg⟩ := key S hS hSJ
      obtain ⟨N₀, hN₀Ω, hN₀c, hN₀img⟩ := key S₀ hS₀ hS₀J
      have hNN : N₀ = N := hs.noTwins N hNΩ N₀ ⟨hN₀Ω, z * t, hNc, hN₀c⟩
      subst hNN
      exact ih8_eq_of_map_eq ψ hker (hperf S hS.1) (hperf S₀ hS₀.1) (hNimg.symm.trans hN₀img)
  · push Not at h0
    exact ⟨R_J, R_J, fun S hS => Or.inl (h0 S hS)⟩

end Partner

end CFSG.ClassicalInvolution.Asc77.CFC
