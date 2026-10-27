module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKSL2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cKTrans

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Mix11cN Mix11cK CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.IVK

theorem mix11c_kclass_of_sl2 (h : Mix11cSL2Class) : Mix11cKClass := by
  intro p n hp hp2 hn K _ _ hK
  have : Fact p.Prime := ⟨hp⟩
  rcases hK with hK | hK
  · obtain ⟨F, hFfield, hFfin, hF, ⟨e⟩⟩ := hK
    have hF' : Nat.card F = p ^ n := hF
    have : CharP F p := charP_of_card hF'
    let π : SLm F →* K :=
      (e.symm : ↥(StatedSL 2 F) ≃* K).toMonoidHom.comp
        (specialLinearGroupEquivStatedSL 2 F).toMonoidHom
    have hπinj : Function.Injective π :=
      e.symm.injective.comp (specialLinearGroupEquivStatedSL 2 F).injective
    have hπ : Function.Surjective π :=
      e.symm.surjective.comp (specialLinearGroupEquivStatedSL 2 F).surjective
    have hneg1 : π (T2.negOne F) ≠ 1 := fun h1 =>
      negOne_ne_one hp hp2 (hπinj (by rw [h1, map_one]))
    obtain ⟨hA, hB, hC⟩ := kclass_surj h hp hp2 hn hF' π hπ
    refine ⟨⟨⟨π (T2.negOne F), 1, hneg1⟩⟩, hA, ?_,
      fun W W' _ _ _ _ _ _ σ σ' _ hs _ hs' hlo hhi hd => hC W W' σ σ' hs hs' hlo hhi hd⟩
    intro W _ _ _ σ hinj hs hlo hhi
    rcases hB W σ hs hlo hhi with ⟨_, hd⟩ | ⟨hneg, _, _⟩
    · exact Or.inl ⟨⟨F, hFfield, hFfin, hF, ⟨e⟩⟩, hd⟩
    · exfalso
      apply hneg1
      apply hinj
      rw [map_one]
      exact LinearMap.ext hneg
  · obtain ⟨F₀, hFfield, hFfin, hF, ⟨e⟩⟩ := hK
    have hF' : Nat.card F₀ = p ^ n := hF
    have : CharP F₀ p := charP_of_card hF'
    let π : SLm F₀ →* K := (e.symm : L2 F₀ ≃* K).toMonoidHom.comp (slToL2 F₀)
    have hπ : Function.Surjective π :=
      e.symm.surjective.comp (slToL2_surjective F₀)
    have hneg1 : π (T2.negOne F₀) = 1 := by
      show e.symm (slToL2 F₀ (T2.negOne F₀)) = 1
      rw [slToL2_negOne, map_one]
    obtain ⟨hA, hB, hC⟩ := kclass_surj h hp hp2 hn hF' π hπ
    refine ⟨?_, hA, ?_,
      fun W W' _ _ _ _ _ _ σ σ' _ hs _ hs' hlo hhi hd => hC W W' σ σ' hs hs' hlo hhi hd⟩
    · refine ⟨⟨π (CFSG.GH74.GLS.Stage4.Hex.sl2U (1 : F₀)), 1, fun h1 => ?_⟩⟩
      apply slToL2_unipotent_ne_one F₀
      exact e.symm.injective (by rw [map_one]; exact h1)
    · intro W _ _ _ σ hinj hs hlo hhi
      rcases hB W σ hs hlo hhi with ⟨hneg, hd⟩ | ⟨_, hd, hcard⟩
      · exfalso
        have h0 : ∀ w : W, w = 0 := by
          intro w
          have h1 : w = -w := by simpa [hneg1] using hneg w
          have h2 : (2 : ZMod p) • w = 0 := by
            rw [two_smul]
            nth_rewrite 1 [h1]
            exact neg_add_cancel w
          exact (smul_eq_zero.1 h2).resolve_left (two_ne_zero_of_charP hp hp2)
        have hsub : Subsingleton W := ⟨fun a b => by rw [h0 a, h0 b]⟩
        have : Module.finrank (ZMod p) W = 0 := Module.finrank_zero_of_subsingleton
        omega
      · refine Or.inr ⟨⟨F₀, hFfield, hFfin, hF, ⟨e⟩⟩, hd, ?_⟩
        classical
        have hfin : Finite (Module.End (MonoidAlgebra (ZMod p) K) σ.asModule) :=
          Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero n hp.ne_zero)
        have : IsSimpleModule (MonoidAlgebra (ZMod p) K) σ.asModule := hs
        exact ⟨Module.End (MonoidAlgebra (ZMod p) K) σ.asModule, littleWedderburn _, hfin, hcard,
          ⟨RingEquiv.refl _⟩⟩

end CFSG.GH74.GLS.Stage4.Rest
