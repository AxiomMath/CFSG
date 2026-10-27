module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti

@[expose] def OuterFixesE9 (M : Type) [Group M] : Prop :=
  ∀ α : MulAut M, α ^ 3 = 1 → α ∉ (MulAut.conj : M →* MulAut M).range →
    ∃ E : Subgroup M, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, α e = e

theorem OuterFixesE9.of_mulEquiv {K M : Type} [Group K] [Group M] (e : K ≃* M)
    (h : OuterFixesE9 M) : OuterFixesE9 K := by
  intro α hα3 hαo
  have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβo : MulAut.congr e α ∉ (MulAut.conj : M →* MulAut M).range := by
    rintro ⟨g, hg⟩
    exact hαo ⟨e.symm g, (CFSG.RankThree.PartOne.CTP.eq_conj_of_congr_eq_conj e hg.symm).symm⟩
  obtain ⟨E, hE, hE9, hfix⟩ := h _ hβ3 hβo
  refine ⟨E.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE9]
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : e (α (e.symm y)) = y := hfix y hy
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2

theorem outerFixesE9_of_descent {M : Type} [Group M]
    (h : ∀ α : MulAut M, α ^ 3 = 1 → α ∉ (MulAut.conj : M →* MulAut M).range →
      ∃ δ f : MulAut M, α = δ * f * δ⁻¹ ∧
        ∃ E : Subgroup M, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ ∀ e ∈ E, f e = e) :
    OuterFixesE9 M := by
  intro α hα3 hαo
  obtain ⟨δ, f, rfl, E, hE, hE9, hfix⟩ := h α hα3 hαo
  refine ⟨E.map δ.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hE _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective δ.injective, hE9]
  · rintro _ ⟨y, hy, rfl⟩
    change (δ * f * δ⁻¹) (δ y) = δ y
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      hfix y hy]

theorem isElemAbelian_zpowers_of_cube_eq_one {M : Type} [Group M] {u : M} (hu3 : u ^ 3 = 1) :
    IsElemAbelian 3 (zpowers u) := by
  rw [Subgroup.zpowers_eq_closure]
  refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
  · rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  · rw [Set.mem_singleton_iff] at ha
    rw [ha, hu3]

theorem isElemAbelian_card_sup_zpowers_of_pair {M : Type} [Group M] [Finite M] {u v : M}
    (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u)
    (hvu : v ∉ zpowers u) :
    IsElemAbelian 3 (zpowers u ⊔ zpowers v) ∧ Nat.card ↥(zpowers u ⊔ zpowers v) = 9 := by
  have hcomm : ∀ a ∈ zpowers u, ∀ b ∈ zpowers v, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact ((Commute.zpow_left huv i).zpow_right j).eq
  refine ⟨(isElemAbelian_zpowers_of_cube_eq_one hu3).sup_of_commute
    (isElemAbelian_zpowers_of_cube_eq_one hv3) hcomm, ?_⟩
  have hc : ∀ e ∈ zpowers u, e * v = v * e := fun e he => hcomm e he v (Subgroup.mem_zpowers v)
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers u) hv3 hvu hc,
    Nat.card_zpowers, orderOf_eq_prime hu3 hu1]

theorem exists_E9_le_of_pair {M : Type} [Group M] [Finite M] {H : Subgroup M} {u v : M}
    (huH : u ∈ H) (hvH : v ∈ H) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1)
    (huv : u * v = v * u) (hvu : v ∉ zpowers u) :
    ∃ E : Subgroup M, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨hE, hE9⟩ := isElemAbelian_card_sup_zpowers_of_pair hu1 hu3 hv3 huv hvu
  exact ⟨_, sup_le ((Subgroup.zpowers_le).2 huH) ((Subgroup.zpowers_le).2 hvH), hE, hE9⟩

theorem isElemAbelian_card_map_of_E9 {M N : Type} [Group M] [Group N] (φ : M →* N)
    (hφ : Function.Injective φ) {E : Subgroup M} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    IsElemAbelian 3 (E.map φ) ∧ Nat.card (E.map φ) = 9 :=
  ⟨CFSG.SectionRank.isElemAbelian_map hE _, by rw [Subgroup.card_map_of_injective hφ, hE9]⟩

@[expose] def OuterFixedAt (d : ValidLieTypeIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (CFSGIndex.lie d).Group) → OuterFixesE9 K

theorem outerFixedAt_of_model {d : ValidLieTypeIndex}
    (h : ∀ (K : Type) [Group K] [Finite K], (K ≃* (CFSGIndex.lie d).Group) →
      ∃ (M : Type) (_ : Group M), OuterFixesE9 M ∧ Nonempty (K ≃* M)) : OuterFixedAt d := by
  intro K _ _ ⟨e⟩
  obtain ⟨M, _, hM, ⟨f⟩⟩ := h K e
  exact hM.of_mulEquiv f

theorem outerFixedE9_of_forall
    (h : ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 →
      (IsRankTwoIndex d.1 ∨ IsRankThreeIndex d.1) → OuterFixedAt d) : OuterFixedE9 := by
  intro d hch hd K _ _ he
  exact h d hch hd K he

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
