module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFace
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceA2A1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceA1A2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction.TwistedE6Pilot

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


theorem concl_of_famFive_twE6_of_faces
    (hA2A1 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {E : Subgroup (Γ₂ F)},
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    (hA1A2 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {E : Subgroup (Γ₂ F)},
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 3 S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .twE6)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 3 lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    T173Concl 3 S B K N :=
  concl_of_famFive_twE6_of_subset (subset_twE6MaxA5_of_stdD_of_faces hA2A1 hA1A2)
    hcfg hlab htag hmark

theorem i173OOn_famFive_of_faces
    (hA2A1 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {E : Subgroup (Γ₂ F)},
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA2A1 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    (hA1A2 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {E : Subgroup (Γ₂ F)},
        E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA1A2 ⊔
          twistedE6DiagGL F σ →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) :
    I173OOn famFive := by
  intro p Ω _ _ S B N D K x lab hcfg hlab hfam hmark
  obtain ⟨rfl, ⟨htag, h3⟩ | htag⟩ := hfam
  · exact (false_of_famFive_E6 hcfg hlab htag h3 hmark).elim
  · exact concl_of_famFive_twE6_of_faces hA2A1 hA1A2 hcfg hlab htag hmark

theorem i173OOn_famFive : I173OOn famFive :=
  i173OOn_famFive_of_faces card_le_pow_three_of_le_levi_sup_diag_A2A1
    card_le_pow_three_of_le_levi_sup_diag_A1A2

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
