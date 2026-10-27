module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoModel

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false

section RankOne


variable {τ : Tag} {L : Type} [Field L] [CharP L 2] (F : ModGL τ L →* ModGL τ L)

theorem eq_bot_of_le_rootSpan_tw {ω : Lˣ} (hω : orderOf ω = 3) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {μ : Lˣ}
    (hμ : ∀ A : SL2 L, F (rootSL2 τ L α A) = rootSL2 τ L α
      (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)))
    {G : Subgroup (ModGL τ L)} (hGW : G ≤ fixModel F)
    (ht₀G : rootSL2 τ L α (HSL ω) ∈ G)
    (N : Subgroup G) (hNL : ∀ m ∈ N, (m : ModGL τ L) ∈ rootSpan τ L {α, -α})
    (hnorm : ∀ g : G, (g : ModGL τ L) ∈ rootSpan τ L {α, -α} → ∀ m ∈ N, g * m * g⁻¹ ∈ N)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  have hinj := rootSL2_injective_of_field (τ := τ) (K := L) α
  have hfix : ∀ A : SL2 L, rootSL2 τ L α A ∈ fixModel F →
      conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) = A :=
    fun A hA => hinj ((hμ A).symm.trans hA.2)
  have ht₀L : rootSL2 τ L α (HSL ω) ∈ rootSpan τ L {α, -α} := by
    rw [hspan]
    exact ⟨_, rfl⟩
  have hord : ∀ m ∈ N, (m : ModGL τ L) ^ 3 = 1 → m = 1 := by
    intro m hm h3
    have h1 : orderOf (⟨m, hm⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h2 : orderOf (⟨m, hm⟩ : N) ∣ 3 := by
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h3
    have h3' : orderOf (⟨m, hm⟩ : N) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right h1 hcop).symm h2
    rw [orderOf_eq_one_iff] at h3'
    exact congrArg Subtype.val h3'
  refine eq_bot_iff.2 fun m hm => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨A, hA⟩ : (m : ModGL τ L) ∈ (rootSL2 τ L α).range := hspan ▸ hNL m hm
  have hAfix := hfix A (by rw [hA]; exact hGW m.2)
  rcases twFix_cases hAfix with h3 | ⟨h0, h1⟩
  · exact hord m hm (by rw [← hA, ← map_pow, h3, map_one])
  · exfalso
    set g₀ : G := ⟨rootSL2 τ L α (HSL ω), ht₀G⟩ with hg₀
    have hkN : g₀ * m * g₀⁻¹ * m⁻¹ ∈ N := N.mul_mem (hnorm g₀ ht₀L m hm) (N.inv_mem hm)
    have hk : ((g₀ * m * g₀⁻¹ * m⁻¹ : G) : ModGL τ L) = rootSL2 τ L α (HSL (ω ^ 2)) := by
      rw [← HSL_conj_antidiag ω h0 h1, map_mul, map_mul, map_mul, map_inv, map_inv, hA]
      rfl
    have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
    have hk3 : ((g₀ * m * g₀⁻¹ * m⁻¹ : G) : ModGL τ L) ^ 3 = 1 := by
      rw [hk, ← map_pow, HSL_pow_three hω23, map_one]
    have hk1 := hord _ hkN hk3
    have h4 : rootSL2 τ L α (HSL (ω ^ 2)) = rootSL2 τ L α 1 := by
      rw [← hk, hk1, map_one]
      rfl
    have h5 := congrArg (fun B : SL2 L => (B : Matrix (Fin 2) (Fin 2) L) 0 0) (hinj h4)
    have h6 : ((ω ^ 2 : Lˣ) : L) = 1 := by simpa [HSL] using h5
    have h7 : ω ^ 2 = 1 := Units.ext (by rw [h6, Units.val_one])
    have h8 := orderOf_dvd_of_pow_eq_one h7
    rw [hω] at h8
    norm_num at h8

theorem pow_three_mem_rootSpan_tw
    (hFT : ∀ a : Fin τ.rank → Lˣ, F (rootDiagUnit τ a) = (rootDiagUnit τ a)⁻¹ ^ 2)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {μ : Lˣ}
    (hμ : ∀ A : SL2 L, F (rootSL2 τ L α A) = rootSL2 τ L α
      (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)))
    {g : ModGL τ L} (hg : g ∈ fixModel F)
    (hgTL : g ∈ torusGroup τ L ⊔ rootSpan τ L {α, -α}) : g ^ 3 ∈ rootSpan τ L {α, -α} := by
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  have hTN : torusGroup τ L ≤ Subgroup.normalizer (rootSpan τ L {α, -α} : Set (ModGL τ L)) :=
    CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan fun β hβ => by
      rcases hβ with rfl | rfl
      · exact hα
      · exact IsRoot.neg hα
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hgTL
  obtain ⟨t, ht, l, hl, rfl⟩ := hgTL
  obtain ⟨b, rfl⟩ := torusGroup_le_range_rootDiagUnitHom ht
  obtain ⟨A, rfl⟩ : l ∈ (rootSL2 τ L α).range := hspan ▸ hl
  have hF : F (rootDiagUnit τ b * rootSL2 τ L α A) = rootDiagUnit τ b * rootSL2 τ L α A := hg.2
  rw [map_mul] at hF
  change F (rootDiagUnit τ b) * F (rootSL2 τ L α A) = _ at hF
  rw [hFT b, hμ A] at hF
  set B := conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
    (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) with hB
  have hb3 : rootDiagUnit τ b ^ 3 ∈ rootSpan τ L {α, -α} := by
    have h1 : rootDiagUnit τ b ^ 3 = rootSL2 τ L α B * (rootSL2 τ L α A)⁻¹ := by
      calc rootDiagUnit τ b ^ 3 = rootDiagUnit τ b ^ 2 *
            (rootDiagUnit τ b * rootSL2 τ L α A) * (rootSL2 τ L α A)⁻¹ := by group
        _ = rootDiagUnit τ b ^ 2 * ((rootDiagUnit τ b)⁻¹ ^ 2 * rootSL2 τ L α B) *
            (rootSL2 τ L α A)⁻¹ := by rw [← hF]
        _ = rootSL2 τ L α B * (rootSL2 τ L α A)⁻¹ := by group
    rw [h1, hspan]
    exact mul_mem ⟨B, rfl⟩ (inv_mem ⟨A, rfl⟩)
  have hlL : rootSL2 τ L α A ∈ rootSpan τ L {α, -α} := by
    rw [hspan]
    exact ⟨A, rfl⟩
  have hc : ∀ k : ℕ, rootDiagUnit τ b ^ k * rootSL2 τ L α A * (rootDiagUnit τ b ^ k)⁻¹ ∈
      rootSpan τ L {α, -α} := fun k =>
    (Subgroup.mem_normalizer_iff.1 (hTN (pow_mem ht k)) _).1 hlL
  have e2 : (rootDiagUnit τ b * rootSL2 τ L α A) ^ 3 =
      (rootDiagUnit τ b ^ 1 * rootSL2 τ L α A * (rootDiagUnit τ b ^ 1)⁻¹) *
        (rootDiagUnit τ b ^ 2 * rootSL2 τ L α A * (rootDiagUnit τ b ^ 2)⁻¹) *
        (rootDiagUnit τ b ^ 3 * rootSL2 τ L α A * (rootDiagUnit τ b ^ 3)⁻¹) *
      rootDiagUnit τ b ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]
    group
  change (rootDiagUnit τ b * rootSL2 τ L α A) ^ 3 ∈ _
  rw [e2]
  exact mul_mem (mul_mem (mul_mem (hc 1) (hc 2)) (hc 3)) hb3

end RankOne

section Core


variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem twE6Two_commutator_le_model :
    ⁅twE6TwoModel L, twE6TwoModel L⁆ ≤ twE6TwoModel L :=
  Subgroup.commutator_le.2 fun _ hg _ hh =>
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

@[expose] noncomputable def dTwE6Two
    [Finite (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))] {ω : Lˣ}
    (hω : ω ^ 3 = 1) (y : Fin 5 → ZMod 3) :
    ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)) :=
  dS hω (twE6Two_dV_e6InnerVec_mem_commutator (L := L) hω) y

theorem coe_dTwE6Two [Finite (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))]
    {ω : Lˣ} (hω : ω ^ 3 = 1) (y : Fin 5 → ZMod 3) :
    (dTwE6Two hω y : ModGL Tag.E6 L) = dV ω (subLin e6InnerVec y) := rfl

theorem gLAPPrimeCoreOf_centralizer_dS_twE6Two
    [Finite (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))] {ω : Lˣ}
    (hω : orderOf ω = 3)
    {y : Fin 5 → ZMod 3} (hy : y ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer {dTwE6Two (pow_three_of_orderOf hω) y}) = ⊥ := by
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨⟨hhyp, hstd0⟩, -⟩ := hcert
  have hGM : ⁅twE6TwoModel L, twE6TwoModel L⁆ ≤ twE6TwoModel L := twE6Two_commutator_le_model
  have hGC : ⁅twE6TwoModel L, twE6TwoModel L⁆ ≤ adjointGroup Tag.E6 L := fun g hg => (hGM hg).1
  have hX3 : ∀ g ∈ ⁅twE6TwoModel L, twE6TwoModel L⁆, g ∈ torusGroup Tag.E6 L → g ^ 3 = 1 := by
    intro g hg hgT
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hgT
    have hF : twE6TwoF L (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a := (hGM hg).2
    rw [twE6TwoF_rootDiagUnit, inv_pow] at hF
    change rootDiagUnit Tag.E6 a ^ 3 = 1
    rw [pow_succ]
    exact inv_eq_iff_mul_eq_one.1 hF
  have hlenL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec),
      b.length = Tag.E6.rank := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact length_liftL _ _
  have hltL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec), ∀ x ∈ b,
      x < 3 := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact lt_of_mem_liftL _ _
  have hleaf : ∀ fl ∈ normVecs 3 5, GLAPPrimeCoreOf 3 (famCentS ω ⁅twE6TwoModel L, twE6TwoModel L⁆
      ((kerBasis 3 fl).map (liftL (τ := .E6) e6InnerVec))) = ⊥ := by
    intro fl hfl
    refine gLAPPrimeCoreOf_leafS hGC hX3 ?_
    rcases famData_of_famOKW hω (hlenL _) (hltL _) (hhyp fl hfl) with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · obtain ⟨μ, hμ⟩ := exists_twE6TwoF_rootSL2 (L := L) hα
      refine Or.inr ⟨α, hα, hker, hW, fun g hg hgTL => ?_, fun N hNL hnorm hcop => ?_⟩
      · exact pow_three_mem_rootSpan_tw (twE6TwoF L) twE6TwoF_rootDiagUnit hα hμ (hGM hg) hgTL
      · exact eq_bot_of_le_rootSpan_tw (twE6TwoF L) hω hα hμ hGM
          (twE6Two_rootSL2_HSL_mem_commutator hα hω3) N hNL hnorm hcop
  have hstdS : GLAPPrimeCoreOf 3 (famCentS ω ⁅twE6TwoModel L, twE6TwoModel L⁆
      ((Native.stdBasis 5).map (liftL (τ := .E6) e6InnerVec))) = ⊥ :=
    gLAPPrimeCoreOf_leafS hGC hX3 (Or.inl (famData0_of_famOK0W hω (hlenL _) (hltL _) hstd0))
  exact gLAPPrimeCoreOf_centralizer_subS hω
    (twE6Two_dV_e6InnerVec_mem_commutator (L := L) hω3) subLin_e6InnerVec_injective hleaf hstdS hy

end Core

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
