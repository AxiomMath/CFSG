module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Lemmas
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

@[expose] def KDInndiagP5 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L → ¬ IsLinearOrUnitaryAt p L →
    ∀ γ α : MulAut L, (∃ k : ℕ, α ^ p ^ k = 1) →
      (∃ k : ℕ, (γ * α * γ⁻¹ * α⁻¹) ^ p ^ k = 1) →
      γ * α * γ⁻¹ * α⁻¹ ∈ (MulAut.conj : L →* MulAut L).range

@[expose] def KD29Inner : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    ¬ IsLinearOrUnitaryAt p L → centralizer (L : Set X) = ⊥ →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    (∃ x ∈ L, orderOf x = p ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
    ∀ d ∈ L, d ≠ 1 → d ^ p = 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥

@[expose] def I294OutDiagExcluded : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    centralizer (L : Set X) = ⊥ → ∀ (D : Subgroup X), IsElemAbelian p D → Nat.card D = p ^ 2 →
    CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X)) →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ z g : X, z ∈ D → z ≠ 1 →
      IsPlaneDiagonal p D z g →
      (∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
      ¬ IsLinearOrUnitaryAt p L

theorem gl83I294Two_of (hΔ : KDInndiagP5) (h29 : KD29Inner) (hOD : I294OutDiagExcluded) :
    GL83I294Two := by
  intro p hp h5 X _ _ L _ hs hn hc hcen D hD hcard hsyl hrank z g hz hz1 hg hlow
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative D := hD.1
  have hp2 : p ≠ 2 := by omega
  have hout : ¬ IsLinearOrUnitaryAt p L :=
    hOD p hp h5 X L hs hn hc hcen D hD hcard hsyl hrank z g hz hz1 hg hlow
  have hDL : D ≤ L := by
    intro d hd
    obtain ⟨d', hd', hdd⟩ := exists_commutator_of_isPlaneDiagonal h5 hD hcard hz hz1 hg d hd
    have hdp : d ^ p = 1 := hD.2 d hd
    have hd'p : d' ^ p = 1 := hD.2 d' hd'
    have hdc : d' * d = d * d' := setLike_mul_comm hd' hd
    have hgd : g * d' * g⁻¹ = d' * d := by
      rw [hdd]
      group
    have hgdd : g * d' * g⁻¹ * d'⁻¹ = d := by
      rw [hgd, hdc]
      group
    have hγα : MulAut.conjNormal (H := L) g * MulAut.conjNormal (H := L) d' *
        (MulAut.conjNormal (H := L) g)⁻¹ * (MulAut.conjNormal (H := L) d')⁻¹ =
          MulAut.conjNormal (H := L) d := by
      rw [← hgdd]
      simp only [map_mul, map_inv]
    have hαp : (MulAut.conjNormal (H := L) d') ^ p ^ 1 = 1 := by
      rw [pow_one, ← map_pow, hd'p, map_one]
    have hγαp : (MulAut.conjNormal (H := L) g * MulAut.conjNormal (H := L) d' *
        (MulAut.conjNormal (H := L) g)⁻¹ * (MulAut.conjNormal (H := L) d')⁻¹) ^ p ^ 1 = 1 := by
      rw [hγα, pow_one, ← map_pow, hdp, map_one]
    have hmem := hΔ p hp h5 L hs hn hc hout (MulAut.conjNormal (H := L) g)
      (MulAut.conjNormal (H := L) d') ⟨1, hαp⟩ ⟨1, hγαp⟩
    rw [hγα, MonoidHom.mem_range] at hmem
    obtain ⟨t, ht⟩ := hmem
    have key : ∀ h ∈ L, (t : X) * h * (t : X)⁻¹ = d * h * d⁻¹ := by
      intro h hh
      have h1 := congrArg Subtype.val (DFunLike.congr_fun ht ⟨h, hh⟩)
      simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h1
    have hcen' : (t : X)⁻¹ * d ∈ centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      calc h * ((t : X)⁻¹ * d) = (t : X)⁻¹ * ((t : X) * h * (t : X)⁻¹) * d := by group
        _ = (t : X)⁻¹ * (d * h * d⁻¹) * d := by rw [key h hh]
        _ = (t : X)⁻¹ * d * h := by group
    rw [hcen, Subgroup.mem_bot] at hcen'
    have hdt : d = (t : X) := (inv_mul_eq_one.1 hcen').symm
    rw [hdt]
    exact t.2
  have hC : ∀ d ∈ D, d ≠ 1 → GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥ := by
    intro d hd hd1
    obtain ⟨x, hxD, hx1, hxr⟩ := hlow
    exact h29 p hp h5 X L hs hn hc hout hcen hrank
      ⟨x, hDL hxD, orderOf_eq_prime (hD.2 x hxD) hx1, hxr⟩ d (hDL hd) hd1 (hD.2 d hd)
  exact Or.inl (signalizer_eq_bot_of_constrained hp hp2 hD hcard hsyl hC)

end CFSG.LocalAnalysis.RankFourTheoremC
