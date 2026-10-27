module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinF1
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Rank

variable {G : Type} [Group G] [Finite G] {T M H S : Subgroup G} {z : G}

theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : IsElemAbelian p A) (hB : IsElemAbelian p B) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {v : G} (hv : orderOf v = p) :
    IsElemAbelian p (Subgroup.zpowers v) :=
  CFSG.Open.isElemAbelian_zpowers (hv ▸ pow_orderOf_eq_one v)

theorem conjugate_eq_of_elemAbelian_sq (hs : UnconstrainedSetting G T M) (ht : Tuple25 T M H S z)
    (hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L) {K : Subgroup G}
    (hK : IsComponentIn K H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hEK : E ≤ K)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    ∀ g ∈ H, CFSG.conjugate K g = K := by
  intro g hg
  by_contra hne
  have hK' : IsComponentIn (CFSG.conjugate K g) H := Unc25G2.isComponentIn_conjugate hK hg
  have hcomm : ⁅K, CFSG.conjugate K g⁆ = ⊥ :=
    (BenderBranch.eq_or_commute_of_isComponentIn hK hK').resolve_left fun h => hne h.symm
  have hc : ∀ a ∈ K, ∀ b ∈ CFSG.conjugate K g, a * b = b * a := fun a ha b hb =>
    BenderBranch.commute_of_commutator_eq_bot hcomm ha hb
  have hE' : IsElemAbelian p (CFSG.conjugate E g) :=
    CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj g⁻¹).toMonoidHom
  have hEcard' : Nat.card (CFSG.conjugate E g) = p ^ 2 := by
    rw [BenderBranch.card_conjugate]
    exact hcard
  have hEK' : CFSG.conjugate E g ≤ CFSG.conjugate K g := BenderBranch.conjugate_mono hEK g
  have hdvd : p ∣ Nat.card (CFSG.conjugate E g) := by
    rw [hEcard']
    exact dvd_pow_self p two_ne_zero
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have he'o : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  have he'K' : (x : G) ∈ CFSG.conjugate K g := hEK' x.2
  have hFK' : Subgroup.zpowers (x : G) ≤ CFSG.conjugate K g := Subgroup.zpowers_le.mpr he'K'
  have hcen : Unc25G2.CentreTwo K := ht.centreTwo hs hK (hinn K hK)
  have hdisj : E ⊓ Subgroup.zpowers (x : G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyK : y ∈ K := hEK hy.1
    have hyK' : y ∈ CFSG.conjugate K g := hFK' hy.2
    obtain ⟨k, hk⟩ := hcen y hyK fun w hw => hc w hw y hyK'
    have hyp : y ^ p = 1 := hE.2 y hy.1
    exact Unc25G2.eq_one_of_pow_eq_one_of_two_pow hp hp2 hyp hk
  have hcommEF : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers (x : G), a * b = b * a := fun a ha b hb =>
    hc a (hEK ha) b (hFK' hb)
  have hE'' : IsElemAbelian p (E ⊔ Subgroup.zpowers (x : G)) :=
    isElemAbelian_sup_of_commute hcommEF hE (isElemAbelian_zpowers he'o)
  have hcard'' : Nat.card (E ⊔ Subgroup.zpowers (x : G) : Subgroup G) = p ^ 3 := by
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E (Subgroup.zpowers (x : G))
      hcommEF
    rw [hdisj, Subgroup.card_bot, mul_one, hcard, Nat.card_zpowers, he'o] at h1
    rw [h1]
    ring
  have hle : E ⊔ Subgroup.zpowers (x : G) ≤ H :=
    sup_le (hEK.trans hK.1) (hFK'.trans hK'.1)
  exact Unc25G2.false_of_isElemAbelian_card_cube hs.setting.qtke.2.2 ht.gamma0.isGamma.1 hle hp hp2
    hE'' hcard''

end Rank

section Facts

@[expose] def OddRankTwoFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G),
    ((IsRankTwoEvenType K ∧ ¬ IsL2pType ↥K) ∨
      StatedClassicalModel ↥K .PSL 3 3 1 ∨
      Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2

theorem noCommutingConjugate_of_rank (h252 : Lemma252) (hr : OddRankTwoFacts) :
    NoCommutingConjugate := by
  intro G _ _ T M H S z hs ht K hK hBe hcl hcase g hg
  have hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L := fun L hL =>
    (h252 G T M H S z hs ht L hL).2.1
  have hex : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
    apply hr G K
    rcases hcase with hL2p | hc3
    · obtain ⟨-, -, -, -, hlist⟩ := hcl
      rcases hlist with h1 | h2 | h3 | h4
      · exact absurd h1.1 hBe
      · exact Or.inl ⟨h2.1, hL2p⟩
      · exact Or.inr h3.1
      · exact absurd (Or.inl h4.1) hL2p
    · exact Or.inr hc3.1
  obtain ⟨p, hp, hp2, E, hEK, hE, hcard⟩ := hex
  exact conjugate_eq_of_elemAbelian_sq hs ht hinn hK hp hp2 hEK hE hcard g hg

end Facts

end CFSG.QuasithinUnique.Fin253
