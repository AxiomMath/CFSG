module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabGraph
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTorus

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups

section Basic

variable {K G : Type} [Group K] [Group G]

theorem muTab_mem_normalizer_map (ψ : K →* G) {R : Subgroup K} {x : K}
    (hx : x ∈ Subgroup.normalizer (R : Set K)) :
    ψ x ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨x * r * x⁻¹, (hx r).mp hr, by simp⟩
  · rintro ⟨r, hr, hrh⟩
    refine ⟨x⁻¹ * r * x, ?_, ?_⟩
    · exact (hx (x⁻¹ * r * x)).mpr (by simpa [mul_assoc] using hr)
    · simp only [map_mul, map_inv]
      rw [hrh]
      group

theorem muTab_invol_comm {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂)) {R S : Subgroup K}
    (eR : R ≃* SL(2, F₁)) (eS : S ≃* SL(2, F₂)) {s : K} (hsS : s ∈ S)
    (hsN : s ∈ Subgroup.normalizer (R : Set K)) {a : ℕ} (hord : orderOf s = 2 ^ a) (ha : 1 ≤ a) :
    sl2Inv eS * sl2Inv eR = sl2Inv eR * sl2Inv eS := by
  have hdvd : 2 ^ (a - 1) ∣ orderOf s := by
    rw [hord]
    exact pow_dvd_pow 2 (Nat.sub_le a 1)
  have hw2 : orderOf (s ^ 2 ^ (a - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hdvd, hord,
      Nat.pow_div (Nat.sub_le a 1) (by norm_num)]
    have h3 : a - (a - 1) = 1 := by omega
    rw [h3, pow_one]
  have hwz : s ^ 2 ^ (a - 1) = sl2Inv eS :=
    eq_sl2Inv_of_orderOf_eq_two hodd₂ eS (S.pow_mem hsS _) hw2
  have hzN : sl2Inv eS ∈ Subgroup.normalizer (R : Set K) := hwz ▸ Subgroup.pow_mem _ hsN _
  have hconj : sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp (sl2Inv_mem eR)
  have hord2 : orderOf (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (sl2Inv eS)) (sl2Inv eR)
    rw [MulAut.conj_apply] at this
    rw [this]
    exact orderOf_sl2Inv hodd₁ eR
  have hcomm := eq_sl2Inv_of_orderOf_eq_two hodd₁ eR hconj hord2
  calc sl2Inv eS * sl2Inv eR = (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) * sl2Inv eS := by group
    _ = sl2Inv eR * sl2Inv eS := by rw [hcomm]

end Basic

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

omit [Finite G] in
theorem muTab_orderOf_map (hnpsl : ¬ (t = .PSL ∧ k = 2))
    {S : Subgroup (modelUniv t k p e Fact.out).K} (hS : S ∈ M.cls) {x : _} (hx : x ∈ S) :
    orderOf (M.ψ x) = orderOf x := by
  have hinj := M.injOn_fund hnpsl (M.cls_sub hS)
  rw [orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro h
    exact hinj (x ^ n) (S.pow_mem hx n) (by rw [map_pow]; exact h)
  · intro h
    rw [← map_pow, h, map_one]

theorem muTab_star_elt (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hD4 : t ≠ .trialityD4) (hnpsl : ¬ (t = .PSL ∧ k = 2))
    {R S : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) :
    ∃ s ∈ S, s ∈ Subgroup.normalizer (R : Set (modelUniv t k p e Fact.out).K) ∧ ∃ a : ℕ,
      orderOf s = 2 ^ a ∧ 2 * 2 ^ a = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 := by
  obtain ⟨-, -, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R', hR', hUR', hcyc, hidx⟩ := hU
  obtain ⟨J', hJ', hRJ'⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hcard : Nat.card R' = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 :=
    hΩ.natCard_isSylow2In hJ' hRJ'
  have h1 := Subgroup.relIndex_mul_card U R'
  rw [inf_eq_left.mpr hUR', hidx] at h1
  have hv : (Nat.card SL(2, GaloisField p f)).factorization 2 ≠ 0 := by
    intro h0
    rw [h0, pow_zero, ← h1] at hcard
    have hU0 : 0 < Nat.card U := Nat.card_pos
    omega
  obtain ⟨a, ha⟩ : ∃ a, (Nat.card SL(2, GaloisField p f)).factorization 2 = a + 1 :=
    ⟨(Nat.card SL(2, GaloisField p f)).factorization 2 - 1, by omega⟩
  have hUc : Nat.card U = 2 ^ a := by
    rw [ha, pow_succ] at hcard
    omega
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  have hordu : orderOf (u : G) = 2 ^ a := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu, hUc]
  obtain ⟨s, hsS, hsu⟩ := hUJ u.2
  refine ⟨s, hsS, ?_, a, ?_, ?_⟩
  · refine ih8_mem_normalizer_of_map M.ker_le_center (M.cls_perfect hp2 hD4 hq hR) ?_
    rw [hsu]
    exact hUN u.2
  · rw [← M.muTab_orderOf_map hnpsl hS hsS, hsu, hordu]
  · rw [← hcard, ← h1, hUc]

theorem muTab_star_trichotomy {lin uni : Prop}
    (hdich : ModelFacts.StandardPairDichotomyTypes p t k e lin uni) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hnpsl : ¬ (t = .PSL ∧ k = 2)) {R S : Subgroup (modelUniv t k p e Fact.out).K}
    (hR : R ∈ M.cls) (hS : S ∈ M.cls) (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) :
    Commutes R S ∨ (lin ∧ p ^ f % 4 = 1) ∨ (uni ∧ p ^ f % 4 = 3) := by
  have he := M.exp_eq_f hD4
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hq' : 5 ≤ p ^ e := he ▸ hq
  have hodd := M.natCard_galoisField_odd hp2
  have hcardF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hpodd : Odd (p ^ e) := by
    rw [← hcardF]
    exact hodd
  have hmod : p ^ e % 4 = 1 ∨ p ^ e % 4 = 3 := by
    obtain ⟨m, hm⟩ := hpodd
    omega
  obtain ⟨s, hsS, hsN, a, hord, hcard⟩ := M.muTab_star_elt hΩ hp2 hq hD4 hnpsl hR hS hJ
  subst he
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eS⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hS
  have h8 := MuTab.eight_dvd_two_pow_sl2 (F := GaloisField p e) hodd
  rw [← hcard] at h8
  have h4 : 4 ∣ 2 ^ a := by omega
  have ha : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    norm_num at h4
  have hzcomm := muTab_invol_comm hodd hodd eR eS hsS hsN hord ha
  have hRl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hR)
  have hSl := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ (M.cls_sub hS)
  have hx : M.ψ s ∈ S.map M.ψ := Subgroup.mem_map_of_mem _ hsS
  have hxN := muTab_mem_normalizer_map M.ψ hsN
  have hxo : orderOf (M.ψ s) = 2 ^ a := (M.muTab_orderOf_map hnpsl hS hsS).trans hord
  rcases hdich.map_of_commute hp2 hq' M.ψ M.ker_le_center hRl hSl (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hzcomm.symm with h | h | ⟨hl, W, hW⟩ |
    ⟨hu, W, hW⟩
  · exact absurd h.symm hJ.2.1
  · exact Or.inl (ih8_commutes_of_commutes_map M.ψ M.ker_le_center
      (M.cls_perfect hp2 hD4 hq' hR) h)
  · refine Or.inr (Or.inl ⟨hl, ?_⟩)
    by_contra hne
    have h3 : Nat.card (GaloisField p e) % 4 = 3 := by omega
    have hpow := LinearBlockStandardPair.muTab_pow_card_sub_one
      (M.four_le_natCard_galoisField hD4 hq') hW hx hxN
    have hdvd : 2 ^ a ∣ Nat.card (GaloisField p e) - 1 := hxo ▸ orderOf_dvd_of_pow_eq_one hpow
    exact MuTab.false_of_linear hodd h3 hcard hdvd
  · refine Or.inr (Or.inr ⟨hu, ?_⟩)
    by_contra hne
    have h1 : Nat.card (GaloisField p e) % 4 = 1 := by omega
    have hpow := UnitaryBlockStandardPair.muTab_pow_card_add_one
      (CFSG.LieType.Universal.card_galoisField_two_mul p e hf1) hq' hW hx hxN
    have hdvd : 2 ^ a ∣ Nat.card (GaloisField p e) + 1 := by
      rw [hcardF]
      exact hxo ▸ orderOf_dvd_of_pow_eq_one hpow
    exact MuTab.false_of_unitary hodd h1 hcard hdvd

end Ih8Model

section Types

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {k e : ℕ}

theorem Ih8Model.muTab_star_psl (M : Ih8Model p f Ω .PSL k e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hk : k ≠ 2) (hq3 : p ^ f % 4 = 3)
    {R S : Subgroup (modelUniv .PSL k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) : Commutes R S := by
  rcases M.muTab_star_trichotomy (ModelFacts.standardPairDichotomyTypes_psl M.admissible) hΩ hp2
    hq (by decide) (by decide) (by simpa using hk) hR hS hJ with h | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega
  · exact h.elim

theorem Ih8Model.muTab_star_psu (M : Ih8Model p f Ω .PSU k e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq1 : p ^ f % 4 = 1)
    {R S : Subgroup (modelUniv .PSU k p e Fact.out).K} (hR : R ∈ M.cls) (hS : S ∈ M.cls)
    (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) : Commutes R S := by
  rcases M.muTab_star_trichotomy (ModelFacts.standardPairDichotomyTypes_psu M.admissible) hΩ hp2
    hq (by decide) (by decide) (by simp) hR hS hJ with h | ⟨h, -⟩ | ⟨-, h⟩
  · exact h
  · exact h.elim
  · omega

theorem Ih8Model.muTab_star_psp (M : Ih8Model p f Ω .PSp k e) (hΩ : HypOmegaMod p f Ω)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {R S : Subgroup (modelUniv .PSp k p e Fact.out).K}
    (hR : R ∈ M.cls) (hS : S ∈ M.cls) (hJ : S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ)) :
    Commutes R S := by
  rcases M.muTab_star_trichotomy (ModelFacts.standardPairDichotomyTypes_psp M.admissible) hΩ hp2
    hq (by decide) (by decide) (by simp) hR hS hJ with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact h.elim
  · exact h.elim

end Types

namespace Ih8Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem muTab_starSubset (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hcomm : ∀ R ∈ M.cls, ∀ S ∈ M.cls, S.map M.ψ ∈ omegaStarNbr Ω (R.map M.ψ) →
      Commutes R S) : ∀ K ∈ Ω, omegaStarNbr Ω K ⊆ omegaNbr Ω K := by
  intro K hK J hJ
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨S, hS, rfl⟩ := (M.mem_iff J).mp hJ.1
  refine (M.muTab_omegaNbr_iff hΩ hp2 hq hG2 hD4 hR hS).mpr ⟨fun h => hJ.2.1 (by rw [h]),
    hcomm R hR S hS hJ⟩

end Ih8Model

end CFSG.ClassicalInvolution.Asc77
