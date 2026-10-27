module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2Core
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15InnerStrict

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem strictMin_inner_sp4 {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    (L B : Subgroup G) {U : Submodule (ZMod 2) V} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (e : ↥L ≃* StatedSp 2 F)
    (hquasi : CFSG.Open.IsQuasisimple ↥L)
    (hBN : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) U)
    (hLnt : ¬ L ≤ cenOn ρ L U) (hbest : IsBestOffenderOn ρ B U) (hquad : IsQuadraticOn ρ B U)
    (hmove : ∀ b ∈ B, b ∉ cenOn ρ B U → ∃ k ∈ L, ∃ u ∈ U, ρ b (ρ k u) ≠ ρ k (ρ b u)) :
    ∀ b ∈ B, ∃ l ∈ L, ConjAgree L b l := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hctx := innerCtx_of_subgroups hBN hquasi (pow_three_eq_one_of_central_sp4 e) hB2 hBc
  obtain ⟨Z, iA, iM, iF, κ, hd⟩ := exists_chief_factor ρ L B hctx hinv hLnt hbest hquad hmove
  have e' : ↥(L.subgroupOf (L ⊔ B)) ≃* StatedSp 2 F :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).trans e
  have hcore := core_inner_sp4 hctx hn hFc e' hd
  intro b hb
  obtain ⟨l, hl, hag⟩ := hcore ⟨b, Subgroup.mem_sup_right hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
  refine ⟨(l : G), Subgroup.mem_subgroupOf.mp hl, fun k hk => ?_⟩
  have h1 := hag ⟨k, Subgroup.mem_sup_left hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
  simpa using congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankThreeUC.S15

end
