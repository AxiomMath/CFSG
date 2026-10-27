module

public import CFSG.LargeExtraspecial.S4TwoInput
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
public import Certificates.Certificate113
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.S4One
public import CFSG.LargeExtraspecial.S4Three
public import CFSG.LargeExtraspecial.S4TwoA
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.LargeExtraspecial.Bender

open CFSG.Assembly.LowTwoRank

theorem card_sylow_congr {G G' : Type*} [Group G] [Group G'] [Finite G] (e : G ≃* G')
    (p : ℕ) [Fact p.Prime] : Nat.card (Sylow p G) = Nat.card (Sylow p G') := by
  have : Finite G' := Finite.of_equiv G e.toEquiv
  refine Nat.card_congr
    { toFun := fun P => P.mapSurjective (f := e.toMonoidHom) e.surjective
      invFun := fun P => P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
      left_inv := fun P => ?_
      right_inv := fun P => ?_ }
  · apply Sylow.ext
    change ((P : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom = P
    rw [Subgroup.map_map]
    ext x
    simp
  · apply Sylow.ext
    change ((P : Subgroup G').map e.symm.toMonoidHom).map e.toMonoidHom = P
    rw [Subgroup.map_map]
    ext x
    simp

theorem card_le_card_sylow {G X : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (ρ : G →* Equiv.Perm X) (hX : ¬ p ∣ Nat.card X) (x₀ : X) (P : Subgroup G)
    (hP : IsPGroup p P) (hfix : ∀ y : X, (∀ g ∈ P, ρ g y = y) → y = x₀)
    (htrans : ∀ x : X, ∃ g : G, ρ g x₀ = x) :
    Nat.card X ≤ Nat.card (Sylow p G) := by
  choose g hg using htrans
  choose S hS using fun x : X => (hP.map (MulAut.conj (g x)).toMonoidHom).exists_le_sylow
  refine Nat.card_le_card_of_injective S fun x y hxy => ?_
  obtain ⟨z, hz⟩ : ∃ z : X, ∀ s ∈ (S x : Subgroup G), ρ s z = z := by
    let : MulAction (S x : Subgroup G) X :=
      MulAction.compHom X (ρ.comp (S x : Subgroup G).subtype)
    obtain ⟨z, hz⟩ := (S x).isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card X hX
    exact ⟨z, fun s hs => hz ⟨s, hs⟩⟩
  have key : ∀ w : X, (∀ s ∈ (S w : Subgroup G), ρ s z = z) → z = w := by
    intro w hw
    have h0 : ρ (g w)⁻¹ z = x₀ := by
      refine hfix _ fun h hh => ?_
      have h1 := hw _ (hS w ⟨h, hh, rfl⟩)
      calc ρ h (ρ (g w)⁻¹ z) = ρ (g w)⁻¹ (ρ (g w * h * (g w)⁻¹) z) := by
            rw [← Equiv.Perm.mul_apply, ← map_mul, ← Equiv.Perm.mul_apply, ← map_mul]
            group
        _ = ρ (g w)⁻¹ z := by
            rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
            rw [h1]
    rw [← hg w, ← h0, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]
  exact (key x hz).symm.trans (key y (hxy ▸ hz))

theorem card_sylow_of_psl2 (G : Type) [Group G] [Finite G] (p f : ℕ)
    (hG : StatedClassicalModel G .PSL 2 p f) : Nat.card (Sylow p G) = p ^ f + 1 := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  have : Fact p.Prime := ⟨hp⟩
  rw [card_sylow_congr (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm),
    ← Nat.card_congr (CFSG.GorensteinWalter.psl2ProjectiveLineEquivSylow K hK),
    Projectivization.card_of_finrank_two _ _ (by simp), hK]

theorem card_sylow_of_suzuki (G : Type) [Group G] [Finite G] (s : ℕ)
    (hG : CFSG.Blueprint.LieModel G .twistedB2 0 2 s) :
    Nat.card (Sylow 2 G) = 2 ^ (2 * s) + 1 := by
  have hS : CFSG.Blueprint.SuzukiModel G 2 s := by
    rcases hG with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
  let Q : Sylow 2 G := default
  obtain ⟨T, β, h, -⟩ :=
    CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiPointAction_cosets_of_suzukiModel hS Q
  calc Nat.card (Sylow 2 G)
      = Nat.card (G ⧸ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :=
        Q.card_eq_card_quotient_normalizer
    _ = (2 ^ s) ^ 2 + 1 := h.card_eq
    _ = 2 ^ (2 * s) + 1 := by rw [← pow_mul, mul_comm]

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups in
theorem le_card_sylow_of_psu3 (G : Type) [Group G] [Finite G] (s : ℕ)
    (hG : StatedClassicalModel G .PSU 3 2 s) : 2 ^ (3 * s) + 1 ≤ Nat.card (Sylow 2 G) := by
  obtain ⟨⟨-, hs1, -, hs⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  have hs2 : 2 ≤ s := by
    by_contra h
    exact hs (by rw [show s = 1 by omega, pow_one])
  have hK' : Nat.card K = 2 ^ (2 * s) := by rw [hK, ← pow_mul, mul_comm]
  let J := binaryQuadraticHermitian s (by omega)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 s) 2 2) = (2 ^ s) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 s (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 s) 2 2 // J.conj x = x} =
      2 ^ s :=
    quadraticBinaryFrobenius_fixed_card s (by omega)
  obtain ⟨eJ⟩ := projectiveSpecialUnitary_equiv_PSU3Model J s hs2 rfl hEcard hfixed
  let e₁ : G ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    ((e.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative s hs2 hK')).trans
      (MulEquiv.subgroupCongr (show CFSG.Open.PSU3 2 s = PSU3Model s from rfl))).trans
      eJ.symm
  rw [card_sylow_congr e₁]
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv G e₁.toEquiv
  rcases CFSG.BenderSuzuki.External.huppert_II_10_12 J (2 ^ s) hEcard hfixed rfl with
    ⟨hΩ, rho, pinf, -, -, -, ⟨R, -, -, -, -, -, -, -, hRcard, -, -, -, hreg, -⟩, htwo, -⟩
  have hR : IsPGroup 2 R := IsPGroup.of_card (n := s * 3) (by rw [hRcard, ← pow_mul])
  have : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial, hRcard]
    exact Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  obtain ⟨r, hr⟩ := exists_ne (1 : R)
  have hΩ' := hΩ.trans (show (2 ^ s) ^ 3 + 1 = 2 ^ (3 * s) + 1 by rw [← pow_mul, mul_comm])
  rw [← hΩ']
  refine card_le_card_sylow rho ?_ pinf R hR ?_ ?_
  · rw [hΩ']
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one.not_two_dvd_nat
  · intro y hy
    by_contra hne
    obtain ⟨r₀, -, huniq⟩ := hreg y y hne hne
    exact hr ((huniq r (hy r r.2)).trans (huniq 1 (by simp)).symm)
  · intro x
    by_cases hx : x = pinf
    · exact ⟨1, by simp [hx]⟩
    · obtain ⟨g, hg, -⟩ := htwo pinf x x pinf (Ne.symm hx) hx
      exact ⟨g, hg⟩

theorem benderConjCountInput : S4.BenderConjCountInput := fun G _ _ =>
  ⟨fun f hf => (card_sylow_of_psl2 G 2 f hf).ge,
    fun s _ _ hs => (card_sylow_of_suzuki G s hs).ge,
    fun s _ hs => le_card_sylow_of_psu3 G s hs⟩

end CFSG.LargeExtraspecial.Bender
