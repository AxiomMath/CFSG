module

public import CFSG.GH74.GLS.TwoThin.G.Shape
public import CFSG.GH74.GLS.TwoThin.G.OrdersB2
public import CFSG.GH74.GLS.TwoThin.G.Reduction

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint CFSG.Open CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.E2

theorem ker_le_center_of_surjective {L K₀ : Type*} [Group L] [Group K₀] (hq : IsQuasisimple L)
    (ψ : L →* K₀) (hψ : Function.Surjective ψ) [Nontrivial K₀] : ψ.ker ≤ center L := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (MonoidHom.normal_ker ψ) with htop | hle
  · exfalso
    obtain ⟨k, hk⟩ := exists_ne (1 : K₀)
    obtain ⟨l, rfl⟩ := hψ k
    apply hk
    exact (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top l))
  · exact hle

theorem center_eq_bot_of_simple {S : Type*} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a

theorem equiv_or_center_bot_of_surjective {L K₀ : Type} [Group L] [Finite L] [Group K₀]
    (hq : IsQuasisimple L) (hc2 : Nat.card (center L) = 2) (ψ : L →* K₀)
    (hψ : Function.Surjective ψ) [Nontrivial K₀] : Nonempty (L ≃* K₀) ∨ center K₀ = ⊥ := by
  have hker := ker_le_center_of_surjective hq ψ hψ
  by_cases hk : ψ.ker = ⊥
  · exact Or.inl ⟨MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hk, hψ⟩⟩
  · right
    have hcard : Nat.card ↥(center L) ≤ Nat.card ↥ψ.ker := by
      have := (Subgroup.one_lt_card_iff_ne_bot ψ.ker).2 hk
      omega
    have hkc : ψ.ker = center L := (Subgroup.eq_of_le_of_card_ge hker hcard)
    let e : (L ⧸ center L) ≃* K₀ :=
      (QuotientGroup.quotientMulEquivOfEq hkc.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    have hS : center (L ⧸ center L) = ⊥ := center_eq_bot_of_simple hq.2.1 hq.2.2
    rw [← Subgroup.map_center_eq e, hS, Subgroup.map_bot]

theorem twoThinC2CoverG
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) : TwoThinC2CoverP Gen4 := by
  intro L L₁ K₀ _ _ _ _ δ φ hP hq hC hδs _ hφs _ hK₀
  have hψs : Function.Surjective (φ.comp δ) := hφs.comp hδs
  have hnt : Nontrivial K₀ := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK₀.2
    exact ⟨⟨x, 1, fun h => hx1 (Subtype.ext h)⟩⟩
  have hker := ker_le_center_of_surjective hq (φ.comp δ) hψs
  rcases c2ShapeG_of_inC2 hG hF hC hP with hz | h2M | h2S
  ·
    have hinj : Function.Injective (φ.comp δ) :=
      (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr (hker.trans hz.le))
    let e : L ≃* K₀ := MulEquiv.ofBijective (φ.comp δ) ⟨hinj, hψs⟩
    exact hK₀.2 (by rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot])
  · obtain ⟨-, hc2, hM12⟩ := h2M
    rcases equiv_or_center_bot_of_surjective hq hc2 (φ.comp δ) hψs with he | hbot
    · obtain ⟨e⟩ := he
      exact not_inB2_of_card_two_M12 hc2 hM12 (inB2_of_mulEquiv e.symm hK₀)
    · exact hK₀.2 hbot
  · obtain ⟨-, hc2, hSz⟩ := h2S
    rcases equiv_or_center_bot_of_surjective hq hc2 (φ.comp δ) hψs with he | hbot
    · obtain ⟨e⟩ := he
      exact not_inB2_of_card_two_Sz8 hc2 hSz (inB2_of_mulEquiv e.symm hK₀)
    · exact hK₀.2 hbot

theorem twoThinC2CoverGC
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) : TwoThinC2CoverP Gen4Comp :=
  (twoThinC2CoverG hG hF).mono (fun _ _ hP => hP.gen4)

end CFSG.GH74.GLS.TwoThin
