module

public import CFSG.ClassicalInvolution.Asc77.AscS22H
public import CFSG.ClassicalInvolution.Asc77.AscT7L2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected

section Emb

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conj_mem_layer (hΩ : HypOmegaMod p f Ω) {u g y : G}
    (hg : g ∈ Subgroup.centralizer ({u} : Set G)) (hy : y ∈ exactLayer Ω u) :
    g * y * g⁻¹ ∈ exactLayer Ω u := by
  have := conj_mem_conjSub (n := g) hy
  rwa [conjSub_exactLayer hΩ.conjInvariant hg] at this

theorem exists_layer_emb (hΩ : HypOmegaMod p f Ω) (u : G) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H)
      (ι : (↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)) →* H)
      (π : ↥(Subgroup.centralizer ({u} : Set G)) →* H),
      Function.Injective ι ∧
      (∀ (g : ↥(Subgroup.centralizer ({u} : Set G))) (y : ↥(exactLayer Ω u)),
        π g * ι (y : ↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)) *
          (π g)⁻¹ = ι ((⟨(g : G) * y * (g : G)⁻¹, conj_mem_layer hΩ g.2 y.2⟩ :
            ↥(exactLayer Ω u)) :
              ↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u))) ∧
      (∀ y : ↥(exactLayer Ω u), π ⟨y, exactLayer_le_centralizer Ω u y.2⟩ =
        ι (y : ↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u))) := by
  classical
  set Y : Subgroup G := exactLayer Ω u with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hYC : Y ≤ C := exactLayer_le_centralizer Ω u
  have hOnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun g hg =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ.conjInvariant hg))
  let N₁ : Subgroup ↥C := (oddCoreOf Y).subgroupOf C
  have hN₁ : N₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hOnorm g g.2) n).mp hn
  have hle : N₀ ≤ N₁.comap (Subgroup.inclusion hYC) := by
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨n, hn, rfl⟩
  let ι : (↥Y ⧸ N₀) →* (↥C ⧸ N₁) := QuotientGroup.map N₀ N₁ (Subgroup.inclusion hYC) hle
  have hιmk : ∀ y : ↥Y, ι (QuotientGroup.mk' N₀ y) =
      QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) := fun y => rfl
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hy1 : QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
      obtain ⟨hyY, hyo⟩ := mem_oddCoreOf_iff.mp hy1
      exact (QuotientGroup.eq_one_iff y).mpr hyo
  have hιmk' : ∀ y : ↥Y, ι (y : ↥Y ⧸ N₀) = ((Subgroup.inclusion hYC y : ↥C) : ↥C ⧸ N₁) :=
    fun y => rfl
  refine ⟨↥C ⧸ N₁, inferInstance, inferInstance, ι, QuotientGroup.mk' N₁, hι, ?_, ?_⟩
  · intro g y
    show (g : ↥C ⧸ N₁) * ι (y : ↥Y ⧸ N₀) * (g : ↥C ⧸ N₁)⁻¹ = _
    rw [hιmk', hιmk', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  · intro y
    rfl

end Emb

section Act

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem layer_act_exact (hΩ : HypOmegaMod p f Ω) (hcpg : IsPGroup 2 (Subgroup.zpowers u))
    {H : Type} [Group H]
    {ι : (↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)) →* H}
    {π : ↥(Subgroup.centralizer ({u} : Set G)) →* H}
    (hconj : ∀ (g : ↥(Subgroup.centralizer ({u} : Set G))) (y : ↥(exactLayer Ω u)),
      π g * ι (y : ↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)) *
        (π g)⁻¹ = ι ((⟨(g : G) * y * (g : G)⁻¹, conj_mem_layer hΩ g.2 y.2⟩ :
          ↥(exactLayer Ω u)) : ↥(exactLayer Ω u) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω u)))
    {J : Subgroup G} (hJ : J ∈ tqMembers Ω u)
    (g : ↥(Subgroup.centralizer ({u} : Set G))) (hgJ : (g : G) ∈ trivialOnQuot J) :
    ∀ x ∈ T7H.exactImg Ω u J, ∃ n ∈ oddCoreOf (T7H.exactImg Ω u J),
      π g * ι x * (π g)⁻¹ = ι (n * x) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hk : (y : G) ∈ exactCore u J := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨n, hn, hnk⟩ := S22.exists_odd_mul hΩ hcpg hJ g.2 hgJ hk y.2
    (conj_mem_layer hΩ g.2 y.2)
  refine ⟨n, hn, ?_⟩
  have e := hconj g y
  exact e.trans (congrArg ι hnk)

end Act

end S16

end CFSG.ClassicalInvolution.Asc77
