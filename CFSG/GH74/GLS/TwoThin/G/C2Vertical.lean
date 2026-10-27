module

public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.GLS.TwoThin.G.OrdersB2
public import CFSG.GH74.GLS.TwoThin.G.T2
public import CFSG.GH74.GLS.TwoThin.G.SmallM11
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import Certificates.Certificate12001

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.E2
open CFSG.Open (ordA ordSuzuki)

@[expose] def TwoThinU33Centralizers : Prop :=
  ∀ (K : Type) [Group K] [Finite K], ShapeU33 K → center K = ⊥ → ∀ z : K, orderOf z = 2 →
    Group.IsSolvable ↥(centralizer ({z} : Set K))

@[expose] def TwoThinC2VerticalG_2M12 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Shape2M12 L → ∀ (σ : L ≃* L) (I : Subgroup L) (K₀ : Type)
    [Group K₀], (∀ l, σ (σ l) = l) → IsPCompIn 2 (fixedSubgroup σ) I → InB2 K₀ →
    (∃ φ : ↥I →* K₀, Function.Surjective φ ∧ Odd (Nat.card φ.ker)) → False

theorem card_dvd_of_section {L K₀ : Type*} [Group L] [Finite L] [Group K₀] {I : Subgroup L}
    (φ : ↥I →* K₀) (hφ : Function.Surjective φ) : Nat.card K₀ ∣ Nat.card L := by
  have h1 : Nat.card ↥I = Nat.card (↥I ⧸ φ.ker) * Nat.card φ.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h2 : Nat.card (↥I ⧸ φ.ker) = Nat.card K₀ :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
  rw [h2] at h1
  exact (Dvd.intro _ h1.symm).trans (Subgroup.card_subgroup_dvd_card I)

theorem ordA_one_eight : ordA 1 8 = 504 :=
  Certificates.certificate12001.1

theorem ordA_two_three : ordA 2 3 = 5616 :=
  Certificates.certificate12001.2.1

theorem ordSuzuki_eight : ordSuzuki 8 = 29120 :=
  Certificates.certificate12001.2.2.1

theorem three_lt_of_lieModel_psl_two {K : Type} [Group K] {p f : ℕ} (hp2 : p ≠ 2)
    (h : LieModel K .PSL 2 p f) : Odd (p ^ f) ∧ 3 < p ^ f := by
  obtain ⟨hp, hf, -, h22, h23⟩ := (stated_of_lieModel_PSL h).1
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h2 : 2 ≤ p ^ f := hp.one_lt.trans_le (Nat.le_self_pow (by omega) p)
  have h2' : p ^ f ≠ 2 := fun h' => h22 (by rw [h'])
  have h3' : p ^ f ≠ 3 := fun h' => h23 (by rw [h'])
  obtain ⟨k, hk⟩ := hodd
  exact ⟨⟨k, hk⟩, by omega⟩

theorem twoThinC2VerticalGC
    (hG : GenericKnownFacts)
    (hF : E2ComponentFacts)
    (hU33 : TwoThinU33Centralizers) (h2M : TwoThinC2VerticalG_2M12) :
    TwoThinC2VerticalGC := by
  intro L _ _ σ I K₀ _ hP hq hC hσ hI hK₀ hφ
  obtain ⟨φ, hφs, hφo⟩ := hφ
  have : Finite K₀ := Finite.of_surjective φ hφs
  rcases c2Shape_of_inC2 hG hF hC hP with ⟨hz, hsimple⟩ | hM12 | hSz2
  · rcases hsimple with ⟨p, f, hp, hp2, -, hL⟩ | hL28 | hL33 | hShU33 | hSz | hShM11
    · obtain ⟨hodd, h3⟩ := three_lt_of_lieModel_psl_two hp2 hL
      have hmodel : HasL2Model L (fun q => Odd q ∧ 3 < q) := ⟨p, f, hp, ?_, ⟨hodd, h3⟩, hL⟩
      · exact false_of_solvable_centralizers hK₀ φ hφs hφo
          (fun z hz => solvable_centralizer_of_hasL2Model hmodel z hz)
      · exact (stated_of_lieModel_PSL hL).1.2.1
    · have hcard : Nat.card L = 504 := by
        rw [card_of_lieModel_PSL (by norm_num) hL28]
        exact ordA_one_eight
      exact not_inB2_dvd_504 hK₀ (hcard ▸ card_dvd_of_section φ hφs)
    · have hcard : Nat.card L = 5616 := by
        rw [card_of_lieModel_PSL (by norm_num) hL33]
        exact ordA_two_three
      exact not_inB2_dvd_5616 hK₀ (hcard ▸ card_dvd_of_section φ hφs)
    · exact false_of_solvable_centralizers hK₀ φ hφs hφo
        (fun z hz2 => hU33 L hShU33 hz z hz2)
    · have hcard : Nat.card L = 29120 := by
        rw [card_of_lieModel_twistedB2 hSz]
        exact ordSuzuki_eight
      have h3 := (inB2_three_dvd_card hK₀).trans (hcard ▸ card_dvd_of_section φ hφs)
      revert h3
      exact Certificates.certificate12001.2.2.2.1
    · exact false_of_solvable_centralizers hK₀ φ hφs hφo
        (fun z hz2 => solvable_centralizer_of_M11 hShM11 hz z hz2)
  · exact h2M L hM12 σ I K₀ hσ hI hK₀ ⟨φ, hφs, hφo⟩
  · obtain ⟨-, hc2, hSz⟩ := hSz2
    have hcard : Nat.card L = 58240 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hc2,
        card_of_lieModel_twistedB2 hSz, ordSuzuki_eight]
    have h3 := (inB2_three_dvd_card hK₀).trans (hcard ▸ card_dvd_of_section φ hφs)
    revert h3
    exact Certificates.certificate12001.2.2.2.2

end CFSG.GH74.GLS.TwoThin
