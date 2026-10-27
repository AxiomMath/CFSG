module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem isElemAbelian_of_equiv_le {p : ℕ} {G H : Type*} [Group G] [Group H] {U : Subgroup H}
    (hU : IsElemAbelian p U) {D : Subgroup H} (hDU : D ≤ U) {D₀ : Subgroup G} (f : D₀ ≃* D) :
    IsElemAbelian p D₀ := by
  refine ⟨⟨⟨fun y z => ?_⟩⟩, fun y hy => ?_⟩
  · apply f.injective
    rw [map_mul, map_mul]
    have := hU.1.is_comm.comm ⟨(f y : H), hDU (f y).2⟩ ⟨(f z : H), hDU (f z).2⟩
    have h := congrArg Subtype.val this
    exact Subtype.ext h
  · have h1 := hU.2 (f ⟨y, hy⟩ : H) (hDU (f ⟨y, hy⟩).2)
    have h2 : f ((⟨y, hy⟩ : D₀) ^ p) = f 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using h1)
    have h3 := f.injective h2
    simpa using congrArg Subtype.val h3

theorem not_jStarElimData_three_three_of_rank {L : Type} [Group L] [Finite L]
    (hZ : Subgroup.center L = ⊥) (h4 : 3 ^ 4 ∣ Nat.card L)
    (hrk : ∀ E : Subgroup L, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) :
    ¬ JStarElimData L 3 3 := by
  intro hdata
  have hdata' : JStarElimDataOf L 3 (3 ^ 3 * 3) (PSL2GF 3 3) := hdata
  obtain ⟨U, D, D₀, hDU, ⟨f⟩, hcard⟩ := hdata'.exists_inner_copy hZ h4
  obtain ⟨hUe, hUcard⟩ := psl2GF_sylow 3 3 (by norm_num) U
  have hD : Nat.card D ≤ Nat.card U := Subgroup.card_le_of_le hDU
  rw [hUcard] at hcard hD
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hD27 : Nat.card D = 3 ^ 3 := by
    norm_num at hcard hD ⊢
    omega
  have hE : IsElemAbelian 3 D₀ := isElemAbelian_of_equiv_le hUe hDU f
  have := hrk D₀ hE
  rw [Nat.card_congr f.toEquiv, hD27] at this
  norm_num at this

theorem not_jStarElimData_three_six_of_rank {L : Type} [Group L] [Finite L]
    (hZ : Subgroup.center L = ⊥) (h6 : 3 ^ 6 ∣ Nat.card L)
    (hrk : ∀ E : Subgroup L, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 4) :
    ¬ JStarElimData L 3 6 := by
  intro hdata
  have hdata' : JStarElimDataOf L 3 (3 ^ 6 * 6) (PSL2GF 3 6) := hdata
  obtain ⟨U, D, D₀, hDU, ⟨f⟩, hcard⟩ := hdata'.exists_inner_copy hZ h6
  obtain ⟨hUe, hUcard⟩ := psl2GF_sylow 3 6 (by norm_num) U
  have hD : Nat.card D ≤ Nat.card U := Subgroup.card_le_of_le hDU
  rw [hUcard] at hcard hD
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hE : IsElemAbelian 3 D₀ := isElemAbelian_of_equiv_le hUe hDU f
  have := hrk D₀ hE
  rw [Nat.card_congr f.toEquiv] at this
  norm_num at hcard hD this
  omega


theorem not_jStarElimDataOf_unitary_of_order_nine {L : Type} [Group L] [Finite L]
    (hKU2 : KFactUnitarySylowStructure) {d₀ : TauCeti.ValidLieTypeIndex}
    (hd₀ : IsUnitaryIndex 3 d₀) (hn : d₀.1.fieldExponent = 2)
    (hZ : Subgroup.center L = ⊥) (h6 : 3 ^ 6 ∣ Nat.card L) (h7 : ¬ 3 ^ 7 ∣ Nat.card L)
    (hg : ∃ g : L, orderOf g = 9) :
    ¬ JStarElimDataOf L 3 (3 ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀) := by
  intro hdata
  have hTfin : Finite (CatGroup d₀) := by
    obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := hdata
    exact Finite.of_surjective φ hφ
  have hT6 : 3 ^ 6 ∣ Nat.card (CatGroup d₀) := by
    have := pow_dvd_card_catGroup_unitary hd₀
    rwa [hn] at this
  rw [hn] at hdata
  obtain ⟨U, D, D₀, hDU, ⟨f⟩, hcard⟩ := hdata.exists_inner_copy hZ h6
  have hU6 : 3 ^ 6 ∣ Nat.card U := U.pow_dvd_card_of_pow_dvd_card hT6
  have hDp : IsPGroup 3 D := U.isPGroup'.to_le hDU
  have hD0p : IsPGroup 3 D₀ := hDp.of_equiv f.symm
  obtain ⟨k, hk⟩ := hD0p.exists_card_eq
  have hD6 : 3 ^ 6 ∣ Nat.card D := by
    obtain ⟨u, hu⟩ := hU6
    rw [hu] at hcard
    have h1 : 3 ^ 6 * (3 ^ 6 * u) ∣ 3 ^ 6 * (2 * Nat.card D) := by
      have : 3 ^ 6 * u * 3 ^ 6 * 1 = 3 ^ 6 * (3 ^ 6 * u) := by ring
      calc 3 ^ 6 * (3 ^ 6 * u) = 3 ^ 6 * u * 3 ^ 6 := by ring
        _ ∣ 3 ^ (3 * 2) * 2 * Nat.card D := hcard
        _ = 3 ^ 6 * (2 * Nat.card D) := by norm_num; ring
    have h2 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    have h3 : 3 ^ 6 ∣ 2 * Nat.card D := (Dvd.intro _ rfl).trans h2
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
  have hk6 : k = 6 := by
    have hk' : 3 ^ k ∣ Nat.card L := by
      rw [← hk]; exact Subgroup.card_subgroup_dvd_card D₀
    have hk1 : 6 ≤ k := by
      rw [Nat.card_congr f.toEquiv] at hk
      rw [hk] at hD6
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hD6
    by_contra hne
    exact h7 ((pow_dvd_pow 3 (by omega : 7 ≤ k)).trans hk')
  subst hk6
  have hexp : ∀ x ∈ D₀, x ^ 3 = 1 := by
    intro x hx
    have hx3 := (hKU2 (CatGroup d₀) 3 d₀ (by norm_num) hd₀ ⟨MulEquiv.refl _⟩ U).2.2.1
      (f ⟨x, hx⟩ : CatGroup d₀) (hDU (f ⟨x, hx⟩).2)
    have h2 : f ((⟨x, hx⟩ : D₀) ^ 3) = f 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hx3)
    simpa using congrArg Subtype.val (f.injective h2)
  obtain ⟨Q, hQ⟩ := hD0p.exists_le_sylow
  have hLne : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card L).factorization 3 = 6 := by
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hLne).mp h6
    have h2 : ¬ 7 ≤ (Nat.card L).factorization 3 := fun h =>
      h7 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hLne).mpr h)
    omega
  have hQcard : Nat.card Q = 3 ^ 6 := by rw [Q.card_eq_multiplicity, hv]
  have hD0card : Nat.card D₀ = 3 ^ 6 := hk
  have hQD : (D₀ : Subgroup L) = Q :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hQcard, hD0card])
  obtain ⟨g, hg9⟩ := hg
  have hgp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg9]; norm_num)
  obtain ⟨Q2, hQ2⟩ := hgp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq L Q Q2
  have hgmem : g ∈ ((h • Q : Sylow 3 L) : Subgroup L) := by
    rw [hh]; exact hQ2 (Subgroup.mem_zpowers g)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hgmem
  obtain ⟨y, hy, hyg⟩ := hgmem
  rw [MulAut.smul_def, MulAut.conj_apply] at hyg
  have hy3 : y ^ 3 = 1 := hexp y (hQD ▸ hy)
  have hg3 : g ^ 3 = 1 := by
    rw [← hyg, conj_pow, hy3]
    group
  have := orderOf_dvd_of_pow_eq_one hg3
  rw [hg9] at this
  omega


theorem jStarResidualD4TwoThree_of_rank (h : D4TwoRankTwo)
    

    : JStarResidualD4TwoThree := by
  intro L _ _ hs d q hq hq1 hdq ⟨e⟩
  have hcard : Nat.card L = ordTrialityD4 (2 ^ 1) := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_trialityD4_even hq hdq, hq1]
  have h4 : 3 ^ 4 ∣ Nat.card L := by rw [hcard]; decide
  have hnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_three ((pow_dvd_pow 3 (by norm_num : 2 ≤ 4)).trans h4)
  exact not_jStarElimData_three_three_of_rank (center_bot_of_simple_nonab hnc) h4
    (h L d q hq hq1 hdq ⟨e⟩)

theorem jStarResidualE6TwoSix_of_rank (h : E6TwoRankFour)
    

    : JStarResidualE6TwoSix := by
  intro L _ _ hs d q hq hq1 hdq ⟨e⟩
  have hcard : Nat.card L = ordE6 (2 ^ 1) := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_E6_even hq hdq, hq1]
  have h6 : 3 ^ 6 ∣ Nat.card L := by rw [hcard]; decide
  have hnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_three ((pow_dvd_pow 3 (by norm_num : 2 ≤ 6)).trans h6)
  exact not_jStarElimData_three_six_of_rank (center_bot_of_simple_nonab hnc) h6
    (h L d q hq hq1 hdq ⟨e⟩)

theorem jStarResidualE6TwoTwo_of_order_nine (hKU2 : KFactUnitarySylowStructure)
    (h : E6TwoHasOrderNine)
    

    : JStarResidualE6TwoTwo := by
  intro d₀ hd₀ hn L _ _ hs d q hq hq1 hdq ⟨e⟩
  have hcard : Nat.card L = ordE6 (2 ^ 1) := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_E6_even hq hdq, hq1]
  have h6 : 3 ^ 6 ∣ Nat.card L := by rw [hcard]; decide
  have h7 : ¬ 3 ^ 7 ∣ Nat.card L := by rw [hcard]; decide
  have hnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_three ((pow_dvd_pow 3 (by norm_num : 2 ≤ 6)).trans h6)
  exact not_jStarElimDataOf_unitary_of_order_nine hKU2 hd₀ hn (center_bot_of_simple_nonab hnc) h6 h7
    (h L d q hq hq1 hdq ⟨e⟩)

end CFSG.AGLEmbedding
