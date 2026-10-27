module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Conf
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X81Conf
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11R

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace X11

theorem card_of_lieModel_psl_two_nine {X : Type} [Group X]
    (h : Blueprint.LieModel X .PSL 2 3 2) : Nat.card X = 360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine (h.statedClassicalModel (by decide))

theorem card_le_eight_of_le {X : Type} [Group X] [Finite X] {J D : Subgroup X} (hDJ : D ≤ J)
    (hD : IsPGroup 2 D) (hJ : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = 360) : Nat.card D ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have h1 : Nat.card D ∣ Nat.card J := Subgroup.card_dvd_of_le hDJ
  have h2 := (pPrimeCore 2 ↥J).card_eq_card_quotient_mul_card_subgroup
  rw [hJ] at h2
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥J)) :=
    Nat.Coprime.pow_left k pPrimeCore_coprime_card
  rw [h2, hk] at h1
  have h3 : 2 ^ k ∣ 360 := hcop.dvd_of_dvd_mul_right h1
  have h4 : 2 ^ k ∣ 8 := by
    have h5 : Nat.Coprime (2 ^ k) 45 := Nat.Coprime.pow_left k (by norm_num)
    exact h5.dvd_of_dvd_mul_right (by simpa using h3)
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h4

theorem center_eq_bot_of_isComponent {X : Type} [Group X] {M : Subgroup X}
    (hs : IsSimpleGroup ↥M) (hc : IsComponent M) : center ↥M = ⊥ := by
  obtain ⟨⟨-, -, x, y, hxy⟩, -⟩ := hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥M) with h | h
  · exact h
  · exfalso
    apply hxy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (x * y)⁻¹ * (y * x) ∈ center ↥M := h ▸ mem_top _
    exact this

end X11

namespace Hyp59.L81Hyp.Data

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}

theorem x11Conf {d : Data H₁} {v : H} (hst : d.Stage7 v)
    (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2)
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1) :
    X11.Conf H (generalizedFitting H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hFn, hsimple, hC, -, -, hJF, hKV, hVF, -, hab, hbJ, hKb, hKc, hPX, hPS⟩ :=
    d.fstarFacts
  refine ⟨hFn, hC, hsimple, h.a, d.b, h.J, h.K, h.orderOf_a, d.b_ord, hab, hJF, h.J_le,
    h.isPComponent_J, hJ, hbJ, fun R hR hR2 => ?_, hKV.trans hVF, hKb, hKc, hK⟩
  obtain ⟨T, hT⟩ := hPS
  obtain ⟨T', hT'⟩ := (hR2.comap_subtype (K := centralizer ({h.a} : Set H) ⊓
    coreActionKernel h.J)).exists_le_sylow
  have hcardT : Nat.card T' = Nat.card T := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hTP : Nat.card T = Nat.card h.P := by
    rw [hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hPX).toEquiv
  have hRle : Nat.card R ≤ Nat.card T' := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv]
    exact Subgroup.card_le_of_le hT'
  have hD : Nat.card h.D ≤ 8 :=
    X11.card_le_eight_of_le inf_le_right
      ((Six.isPGroup_S h.toHyp52).to_le inf_le_left) (X11.card_of_lieModel_psl_two_nine hJ)
  rw [hcardT, hTP, hst.card_P] at hRle
  exact hRle.trans hD

theorem gsRestricted_fstar (d : Data H₁)
    (hcomp : ∀ M : Subgroup H, IsComponent M → GSRestricted (↥M ⧸ center ↥M)) :
    GSRestricted ↥(generalizedFitting H) := by
  obtain ⟨-, hsimple, -, hcF, -⟩ := d.fstarFacts
  have hZ := X11.center_eq_bot_of_isComponent hsimple hcF
  exact OddQuot.gsRestricted_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) (hcomp _ hcF)

end Hyp59.L81Hyp.Data

theorem cf81Exit11Recognition_of_recognition (hR : X11.Recognition) : CF81Exit11Recognition := by
  intro H _ _ h H₁ d v hst hcomp hJ hK
  have hJ' : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 (2 * 1) := hJ
  rcases hR H (generalizedFitting H) (d.x11Conf hst hJ hK) (d.gsRestricted_fstar hcomp) with
    hL | hU | hA
  · exact Or.inr ⟨3, 1, Nat.prime_three, by norm_num, le_rfl, Or.inl hJ', Or.inl hL⟩
  · exact Or.inr ⟨3, 1, Nat.prime_three, by norm_num, le_rfl, Or.inl hJ', Or.inr hU⟩
  · exact Or.inl hA

end CFSG.ComponentClassification.GSThmB
