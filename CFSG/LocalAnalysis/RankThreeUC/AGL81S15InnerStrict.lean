module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerConcl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerSeries

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped MatrixGroups

section Ctx

variable {G : Type*} [Group G] {L B : Subgroup G}

theorem innerCtx_of_subgroups (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L)
    (hquasi : CFSG.Open.IsQuasisimple ↥L)
    (hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) :
    InnerCtx (L.subgroupOf (L ⊔ B)) (B.subgroupOf (L ⊔ B)) where
  normalizes := fun b hb l hl => Subgroup.mem_subgroupOf.mpr (by
    have := hBN (b : G) (Subgroup.mem_subgroupOf.mp hb) (l : G) (Subgroup.mem_subgroupOf.mp hl)
    simpa using this)
  quasi := CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left) hquasi
  hZ := fun z hz hzc => Subtype.ext (by
    have h1 := hZ (z : G) (Subgroup.mem_subgroupOf.mp hz) fun k hk =>
      congrArg Subtype.val (hzc ⟨k, Subgroup.mem_sup_left hk⟩ (Subgroup.mem_subgroupOf.mpr hk))
    simpa using h1)
  sq := fun b hb => Subtype.ext (by
    simpa using hB2 (b : G) (Subgroup.mem_subgroupOf.mp hb))
  comm := fun b hb c hc => Subtype.ext (by
    simpa using hBc (b : G) (Subgroup.mem_subgroupOf.mp hb) (c : G)
      (Subgroup.mem_subgroupOf.mp hc))
  top := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _

end Ctx

theorem strictMin_inner {G : Type} [Group G] [Finite G] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V) (L B : Subgroup G)
    {U : Submodule (ZMod 2) V} {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* SL(3, F)) (hquasi : CFSG.Open.IsQuasisimple ↥L)
    (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U)
    (hLnt : ¬ L ≤ cenOn ρ L U) (hbest : IsBestOffenderOn ρ B U) (hquad : IsQuadraticOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u)) :
    ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hZ' : ∀ z ∈ Subgroup.center ↥L, z ^ 3 = 1 := center_pow_three e
  have hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1 := by
    intro z hz hzc
    have hmem : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g g.2)
    simpa using congrArg Subtype.val (hZ' _ hmem)
  have hctx := innerCtx_of_subgroups hBN hquasi hZ hB2 hBc
  obtain ⟨Z, iA, iM, iF, κ, hd⟩ := exists_chief_factor ρ L B hctx hinv hLnt hbest hquad hmove
  have e' : ↥(L.subgroupOf (L ⊔ B)) ≃* SL(3, F) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).trans e
  have hcore := core_inner hctx hn hFc e' hd
  intro b hb
  obtain ⟨l, hl, hag⟩ := hcore ⟨b, Subgroup.mem_sup_right hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
  refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, fun k hk => ?_⟩
  have h1 := hag ⟨k, Subgroup.mem_sup_left hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
  simpa using congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankThreeUC.S15
