module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Core
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator
open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

theorem false_of_alt7_six_of_nat (pd : PermData) (hX : GNSetting X T) {C₁ C₂ : Subgroup X}
    (hP : IsC118Pair T C₁ C₂) (hY : GNYComponent T C₁ C₂ L)
    (hTN : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hnat : ∀ θ : ↥(nL T L) →* Perm (Fin 7),
      (∀ (g : ↥(nL T L)) (l l' : ↥L), (l' : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) (g : X) * l *
        (QuotientGroup.mk' (gnC T) (g : X))⁻¹ →
          (eL l' : Perm (Fin 7)) = θ g * eL l * (θ g)⁻¹) →
      (∀ (g : ↥(nL T L)) (l : ↥L), (l : X ⧸ gnC T) = QuotientGroup.mk' (gnC T) (g : X) →
        θ g = eL l) →
      nV T L ⊓ Subgroup.centralizer (lT T L : Set X) = ⊥ ∧
        ∃ φ : ↥(nV T L) →* Multiplicative (altHeart 7), Function.Bijective φ ∧
          ∀ (g : ↥(nL T L)) (u v : ↥(nV T L)), (v : X) = (g : X) * u * (g : X)⁻¹ →
            Multiplicative.toAdd (φ v) = altAct (θ g) (Multiplicative.toAdd (φ u))) :
    False := by
  have hTL : T ≤ nL T L := fun t ht => hTN ⟨t, ht, rfl⟩
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := CFSG.AGLEmbeddingD2.GN.commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  obtain ⟨θs, hθs, hθsL, hθs1⟩ := exists_thetaS T L eL
  obtain ⟨hC, φ, hφ, hφe⟩ := hnat (θs.comp (πN T L))
    (fun g l l' h => hθs (πN T L g) l l' h) (fun g l h => hθsL (πN T L g) l h)
  let c₀ : SixCtx T L := ⟨eL, θs, hθs, hθsL, hθs1, φ, hφ, hφe⟩
  obtain ⟨σ, hσ⟩ := c₀.exists_conj_img_T hX hTL hY.1 hJ pd.card_D
  exact (c₀.conj σ).false_of_sixCtx pd hX hP hY hTN hσ hC

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
