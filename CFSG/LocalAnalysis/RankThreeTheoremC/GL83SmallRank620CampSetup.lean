module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620CampParab
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

private theorem Data620.setup_X_le_H (h : Data620 M B H S K z b f) : K ⊔ pCoreOf 2 H ≤ H :=
  sup_le h.K_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H)

private theorem Data620.setup_H_le_normalizer_X (h : Data620 M B H S K z b f) :
    H ≤ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup K (pCoreOf 2 H)
    ⟨h.K_normal hg, h.eq_normalizer.le hg⟩

private theorem Data620.setup_pCoreOf_X (h : Data620 M B H S K z b f) :
    pCoreOf 2 (K ⊔ pCoreOf 2 H) = pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h.setup_X_le_H)
      (h.setup_H_le_normalizer_X.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (h.setup_X_le_H.trans h.eq_normalizer.le) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem Data620.campbell_conclusion (hCamp : KFactCampbell) (h : Data620 M B H S K z b f)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index)
    (hC : (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
      normalizer (S : Set G)) :
    ∃ A₀ B₀ : Subgroup G, A₀ ≤ B₀ ∧ B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 H) ∧
      K ⊔ pCoreOf 2 H ≤ normalizer (A₀ : Set G) ∧ K ⊔ pCoreOf 2 H ≤ normalizer (B₀ : Set G) ∧
      K ≤ centralizer (A₀ : Set G) ∧
      (∀ w ∈ omegaCenter (K ⊓ pCoreOf 2 H), ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀) ∧
      A₀.relIndex B₀ = 8 ∧
      ∀ g ∈ K ⊔ pCoreOf 2 H, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 H := by
  have h0 := h.setup_pCoreOf_X
  have h1 : (K ⊔ pCoreOf 2 H) ⊓ centralizer (pCoreOf 2 (K ⊔ pCoreOf 2 H) : Set G) ≤
      pCoreOf 2 (K ⊔ pCoreOf 2 H) := by
    rw [h0]
    exact (inf_le_inf_right _ h.setup_X_le_H).trans (h.charTwo H h.twoLocal)
  have h2 : K ⊔ pCoreOf 2 H = K ⊔ pCoreOf 2 (K ⊔ pCoreOf 2 H) := by rw [h0]
  have h3 : ∃ f' : ↥K →* GL32, Function.Surjective f' ∧
      ∀ k : ↥K, f' k = 1 ↔ (k : G) ∈ pCoreOf 2 (K ⊔ pCoreOf 2 H) :=
    ⟨f, h.f_surj, fun k => by rw [h0]; exact h.f_ker k⟩
  have h5 : R ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
    le_inf hRX (h.le_normalizer_of_sylow hSR hRX hR2 hRi)
  have h7 : ∀ Q₀ : Subgroup G,
      Q₀ ≤ pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)))).Characteristic →
      ¬ K ⊔ pCoreOf 2 H ≤ normalizer (Q₀ : Set G) := by
    intro Q₀ hQS hQ hchar hX
    rw [h.pCoreOf_normalizer_eq] at hQS hchar
    exact h.K_not_le ((le_sup_left.trans hX).trans (h.char_le Q₀ hQS hQ hchar))
  have key := hCamp G (K ⊔ pCoreOf 2 H) K R ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) h1
    le_sup_left (h.setup_X_le_H.trans h.K_normal) h.K_perfect h2 h3 hRX hR2 hRi h5 inf_le_left
    h.index_normalizer_eq_seven (le_inf inf_le_left hC) h7
  rwa [h0] at key

end CFSG.LocalAnalysis.RankThreeTheoremC
