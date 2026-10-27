module

public import CFSG.GH74.GLS.Stage4.HexQuotient
public import CFSG.GH74.GLS.Stage4.Statements
public import CFSG.LieType.Steinberg.TwistedD4.Quasisimple
public import CFSG.Timmesfeld.RankTwo.ModelD43Weyl
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.TitsSimplicity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public noncomputable section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Timmesfeld.RankTwo

namespace CFSG.GH74.GLS.Stage4.Hex

section Fixed

theorem card_fixedField_of_cube {K : Type} [Field K] [Finite K] (σ : K →+* K) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) : Nat.card (fixedField σ) = q := by
  classical
  have := Fintype.ofFinite K
  have hσ3 : ∀ c, σ (σ (σ c)) = c := sigma_three_of_card hK hσq
  let p := ringChar K
  have hpp : p.Prime := CharP.char_is_prime K p
  have : Fact p.Prime := ⟨hpp⟩
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let σE : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  let σA : K ≃ₐ[ZMod p] K := AlgEquiv.ofRingEquiv (f := σE) (fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod (σ.comp (algebraMap (ZMod p) K))
      (algebraMap (ZMod p) K)) x)
  have hσA : ∀ c, σA c = σ c := fun c => rfl
  have hne : σA ≠ 1 := by
    intro h
    have hfix : ∀ c : K, c ^ q = c := fun c => by rw [← hσq, ← hσA, h]; rfl
    have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial K).natDegree = q := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp; omega)]
      simp
    have hq0 : (Polynomial.X ^ q - Polynomial.X : Polynomial K) ≠ 0 := by
      intro h0
      rw [h0] at hdeg
      simp at hdeg
      omega
    have hcard : Fintype.card K ≤ q := by
      have hsub : (Finset.univ : Finset K) ⊆
          (Polynomial.X ^ q - Polynomial.X : Polynomial K).roots.toFinset := by
        intro c _
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hq0]
        simp [Polynomial.IsRoot, hfix c]
      calc Fintype.card K = (Finset.univ : Finset K).card := Finset.card_univ.symm
        _ ≤ _ := Finset.card_le_card hsub
        _ ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial K).roots.card :=
          Multiset.toFinset_card_le _
        _ ≤ (Polynomial.X ^ q - Polynomial.X : Polynomial K).natDegree :=
          Polynomial.card_roots' _
        _ = q := hdeg
    have h1 : q ^ 3 ≤ q := by rw [← hK, Nat.card_eq_fintype_card]; exact hcard
    have h2 : q * q ≥ 4 := by nlinarith
    nlinarith
  have h3 : σA ^ 3 = 1 := by
    ext c
    simp [pow_succ, hσA, hσ3]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σA = 3 := orderOf_eq_prime h3 hne
  let Hs : Subgroup (K ≃ₐ[ZMod p] K) := Subgroup.zpowers σA
  have hHcard : Nat.card Hs = 3 := by
    dsimp [Hs]
    rw [Nat.card_zpowers, hord]
  let Fx : IntermediateField (ZMod p) K := IntermediateField.fixedField Hs
  have hfinrank : Module.finrank Fx K = 3 := by
    change Module.finrank (IntermediateField.fixedField Hs) K = 3
    rw [IntermediateField.finrank_fixedField_eq_card, hHcard]
  have hcardK : Fintype.card K = Fintype.card Fx ^ 3 := by
    calc Fintype.card K = Fintype.card Fx ^ Module.finrank Fx K := Module.card_eq_pow_finrank
      _ = Fintype.card Fx ^ 3 := by rw [hfinrank]
  have hFx : Nat.card Fx = q := by
    have h4 : Nat.card Fx ^ 3 = q ^ 3 := by
      rw [Nat.card_eq_fintype_card (α := Fx), ← hcardK, ← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_left_injective (by norm_num) h4
  have hmem : ∀ c : K, c ∈ fixedField σ ↔ c ∈ Fx := by
    intro c
    have h0 : c ∈ fixedField σ ↔ σ c = c := Iff.rfl
    rw [h0, show c ∈ Fx ↔ ∀ g ∈ Hs, g c = c from IntermediateField.mem_fixedField_iff Hs c]
    constructor
    · intro hc g hg
      have hsub : Hs ≤ MulAction.stabilizer (K ≃ₐ[ZMod p] K) c := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hc
      exact (MulAction.mem_stabilizer_iff.1 (hsub hg))
    · intro h
      exact h σA (Subgroup.mem_zpowers σA)
  rw [← hFx]
  exact Nat.card_congr (Equiv.subtypeEquivRight hmem)

end Fixed

section Data

variable {K : Type} [Field K] (σ : K →+* K)

theorem twistedData
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    G2Data (twistedRootGroup σ) (nHat σ) (hHat σ) where
  ct := twistedDatum_isCTGroupDatum σ hσ
  ext := twistedDatum_steinbergExtras σ hσ
  bruhat := twistedDatum_bruhatExtras σ
  comm := twistedDatum_rootGroupCommutators σ

abbrev twistedX
    : (Fin 2 → ℤ) → Subgroup (twistedGroup σ) := twistedRootGroup σ

theorem d4RGD2
    (hσ : ∀ c, σ (σ (σ c)) = c) :
    RGD2 6 (⨆ i, hHat σ i) (nHat σ (1 : Fin 2)) (nHat σ (0 : Fin 2))
      (posUnipotent (g2Shape (twistedX σ))) (hexGroup (twistedX σ)) :=
  hexRGD2 (twistedData σ hσ)

variable {σ}

theorem card_twistedRootGroup_short
    (hσ : ∀ c, σ (σ (σ c)) = c) {γ : Fin 2 → ℤ}
    (hγ : IsRoot .G2 γ) (hs : ¬ d43Long γ) :
    Nat.card (twistedRootGroup σ γ) = Nat.card K := by
  show Nat.card ((twistedRootSubgroupD4 σ γ).subgroupOf (twistedGroup σ)) = _
  rw [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (twistedRootSubgroupD4_le_twistedGroup σ hγ)).toEquiv]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c : K => (⟨d43XSh σ γ c, d43XSh_mem hσ hγ hs c⟩ :
    twistedRootSubgroupD4 σ γ)) ⟨fun c d h => d43XSh_injective hγ hs (congrArg Subtype.val h), ?_⟩)
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := (mem_iff_d43XSh hσ hγ hs g).1 hg
  exact ⟨c, rfl⟩

theorem card_twistedRootGroup_long
    (hσ : ∀ c, σ (σ (σ c)) = c) {γ : Fin 2 → ℤ}
    (hγ : IsRoot .G2 γ) (hl : d43Long γ) :
    Nat.card (twistedRootGroup σ γ) = Nat.card (fixedField σ) := by
  show Nat.card ((twistedRootSubgroupD4 σ γ).subgroupOf (twistedGroup σ)) = _
  rw [Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (twistedRootSubgroupD4_le_twistedGroup σ hγ)).toEquiv]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun c : fixedField σ =>
    (⟨d43XLg σ γ c, d43XLg_mem hσ hγ hl c⟩ : twistedRootSubgroupD4 σ γ))
    ⟨fun c d h => d43XLg_injective hγ (congrArg Subtype.val h), ?_⟩)
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := (mem_iff_d43XLg hσ hγ hl g).1 hg
  exact ⟨c, rfl⟩

theorem d43Long_hexPos {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) :
    d43Long (hexPos i) ↔ i % 2 = 0 := by
  have e : d43Long (hexPos i) ↔ (3 : ℤ) ∣ hexPos i (1 : Fin 2) := Iff.rfl
  rw [e]
  interval_cases i <;> simp [hexPos]

end Data

section Model

variable {K : Type} [Field K] [Finite K] (σ : K →+* K) {q : ℕ} (hq : 2 ≤ q)
  (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)

include hq hK hσq in
theorem isSimpleGroup_d4Model :
    IsSimpleGroup (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) :=
  (twistedGroup_isQuasisimple_of_card hq hK hσq).2.1

@[expose] def d4ModelSystem :
    RankTwoSystem (twistedGroup σ ⧸ Subgroup.center (twistedGroup σ)) 6 :=
  haveI := isSimpleGroup_d4Model σ hq hK hσq
  hexQuotSystem (twistedData σ (sigma_three_of_card hK hσq))

theorem d4ModelSystem_root
    (i : ℤ) :
    (d4ModelSystem σ hq hK hσq).root i = (hexGroup (twistedX σ) i).map
      (hexProj ↥(twistedGroup σ)) :=
  rfl

theorem d4ModelSystem_U :
    (d4ModelSystem σ hq hK hσq).U =
      (posUnipotent (g2Shape (twistedX σ))).map (hexProj ↥(twistedGroup σ)) :=
  rfl

theorem card_d4ModelSystem_root
    {i : ℤ} (h1 : 1 ≤ i) (h6 : i ≤ 6) :
    Nat.card ((d4ModelSystem σ hq hK hσq).root i) = if i % 2 = 1 then q ^ 3 else q := by
  rw [d4ModelSystem_root, card_hexQuotGroup (twistedData σ (sigma_three_of_card hK hσq)) h1 h6]
  have hγ : IsRoot .G2 (hexPos i) := isRoot_hexPos (by omega) (by omega)
  by_cases hi : i % 2 = 1
  · rw [ite_eq_left hi]
    have hs : ¬ d43Long (hexPos i) := fun h => by have := (d43Long_hexPos h1 h6).1 h; omega
    exact (card_twistedRootGroup_short (sigma_three_of_card hK hσq) hγ hs).trans hK
  · rw [ite_eq_right hi]
    have hl : d43Long (hexPos i) := (d43Long_hexPos h1 h6).2 (by omega)
    exact (card_twistedRootGroup_long (sigma_three_of_card hK hσq) hγ hl).trans
      (card_fixedField_of_cube σ hq hK hσq)

theorem d4Model_rootOrders :
    RootOrdersD4 (d4ModelSystem σ hq hK hσq).root q :=
  Or.inl fun _ h1 h6 => card_d4ModelSystem_root σ hq hK hσq h1 h6

end Model

end CFSG.GH74.GLS.Stage4.Hex
