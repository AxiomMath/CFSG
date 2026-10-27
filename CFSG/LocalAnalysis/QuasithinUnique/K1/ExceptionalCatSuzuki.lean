module

public import CFSG.LieType.BorelTits.Suzuki

public section

namespace CFSG.QuasithinUnique.K1

theorem fusionIsBenderGroup_of_suzukiModel {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel X p f) : CFSG.Open.fusionIsBenderGroup X := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  let e' : X ≃* CFSG.Open.Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  exact Or.inr (Or.inr ⟨a, ha, ⟨e'⟩⟩)

end CFSG.QuasithinUnique.K1
