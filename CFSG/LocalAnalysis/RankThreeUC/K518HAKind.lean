module

public import CFSG.LocalAnalysis.RankThreeUC.K518HANodeSU

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

@[expose] def RkKind (Λ : Type) [Group Λ] : Prop :=
  (∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
      Nonempty (Λ ≃* Matrix.SpecialLinearGroup (Fin 2) k)) ∨
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (f : ℕ), 1 ≤ f ∧
      Nat.card F = (2 ^ f) ^ 2 ∧ Nonempty (Λ ≃* SU (unitaryInvolution F 2 f) 3))

theorem natCard_range_conj_eq {Λ Λ' : Type} [Group Λ] [Finite Λ] [Group Λ'] [Finite Λ']
    (e : Λ ≃* Λ') :
    Nat.card (MulAut.conj : Λ →* MulAut Λ).range = Nat.card (MulAut.conj : Λ' →* MulAut Λ').range := by
  have hmap : (MulAut.conj : Λ →* MulAut Λ).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : Λ' →* MulAut Λ').range := by
    ext x
    constructor
    · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
      exact ⟨e g, (congr_conj e g).symm⟩
    · rintro ⟨g', rfl⟩
      refine ⟨MulAut.conj (e.symm g'), ⟨e.symm g', rfl⟩, ?_⟩
      change MulAut.congr e (MulAut.conj (e.symm g')) = _
      rw [congr_conj, MulEquiv.apply_symm_apply]
  have hcard := Subgroup.card_map_of_injective (K := (MulAut.conj : Λ →* MulAut Λ).range)
    (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective
  rw [hmap] at hcard
  exact hcard.symm

theorem NodeGood.of_mulEquiv {Λ Λ' : Type} [Group Λ] [Finite Λ] [Group Λ'] [Finite Λ']
    (e : Λ ≃* Λ') {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : NodeGood Λ' p) : NodeGood Λ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases h with ⟨hN, hRK, hI⟩ | hr
  · left
    refine ⟨fun N hNn hN2 => ?_, RKGood.of_mulEquiv e hp hp2 hRK, ?_⟩
    · have h1 : (N.map e.toMonoidHom).Normal := hNn.map _ e.surjective
      have h2 : IsPGroup 2 (N.map e.toMonoidHom) := hN2.map _
      have h3 := hN _ h1 h2
      refine eq_bot_iff.2 fun x hx => ?_
      have hx' : e x ∈ Subgroup.map e.toMonoidHom N := ⟨x, hx, rfl⟩
      rw [h3, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact e.injective (by rw [hx', map_one])
    · rwa [natCard_range_conj_eq e]
  · right
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]

theorem nodeGood_of_rkKind (h1 : K518RkSL2) (h2 : K518RkSU3) {Λ : Type} [Group Λ] [Finite Λ]
    (hk : RkKind Λ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpΛ : p ∣ Nat.card Λ) :
    NodeGood Λ p := by
  rcases hk with ⟨k, _, _, _, ⟨e⟩⟩ | ⟨F, _, _, _, f, hf, hF, ⟨e⟩⟩
  · haveI := Finite.of_equiv Λ e.toEquiv
    refine NodeGood.of_mulEquiv e hp hp2 (nodeGood_sl2 h1 hp hp2 ?_)
    rwa [← Nat.card_congr e.toEquiv]
  · haveI := Finite.of_equiv Λ e.toEquiv
    refine NodeGood.of_mulEquiv e hp hp2 (nodeGood_su3 h2 hf hF hp hp2 ?_)
    rwa [← Nat.card_congr e.toEquiv]

theorem center_eq_bot_of_sl2_equiv {Λ : Type} [Group Λ] {k : Type} [Field k] [CharP k 2]
    (e : Λ ≃* Matrix.SpecialLinearGroup (Fin 2) k) : Subgroup.center Λ = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  rw [Subgroup.mem_bot]
  have hc : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hz (e.symm g)
    apply e.symm.injective
    simpa using this
  rw [CFSG.AGLEmbedding.ParabPrime.sl2_center_eq_bot, Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
