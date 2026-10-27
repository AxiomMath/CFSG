module

public import CFSG.RankThree.PartOne.SolD3.SzU3Indec
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Open CFSG.ComponentClassification.Asc76X
  CFSG.RankThree.PartOne.SolD3

theorem mem_commutator_of_psu3 {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (e : ↥N ⧸ CFSG.Assembly.oddCore ↥N ≃* PSU3 2 2) {T : Subgroup G} (hT : IsSylowOf 2 T N)
    {a : G} (haT : a ∈ T) (ha2 : a * a = 1) : a ∈ ⁅T, T⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup ↥N := CFSG.Assembly.oddCore ↥N with hO
  have hOodd : Odd (Nat.card O) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  set π : ↥N →* ↥N ⧸ O := QuotientGroup.mk' O with hπ
  set T' : Subgroup ↥N := T.subgroupOf N with hT'
  have hTN : T ≤ N := hT.le
  have hT'p : IsPGroup 2 T' := hT.isPGroup.comap_subtype
  have hinj : Function.Injective (π.domRestrict T') := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [MonoidHom.domRestrict_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    obtain ⟨k, hk⟩ := hT'p x
    have h1 : orderOf (x : ↥N) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf (x : ↥N) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hx
    have h3 : orderOf (x : ↥N) = 1 := by
      have h4 := Nat.dvd_gcd h1 h2
      have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hOodd)
      rwa [hcop.gcd_eq_one, Nat.dvd_one] at h4
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  set Q : Subgroup (↥N ⧸ O) := T'.map π with hQ
  have hQrange : (π.domRestrict T').range = Q := MonoidHom.domRestrict_range T' π
  have hQcard : Nat.card Q = Nat.card T' := by
    rw [← hQrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hNcard : Nat.card ↥N = Nat.card (↥N ⧸ O) * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hfac : (Nat.card ↥N).factorization 2 = (Nat.card (↥N ⧸ O)).factorization 2 := by
    have hQpos : Nat.card (↥N ⧸ O) ≠ 0 := Nat.card_pos.ne'
    have hOpos : Nat.card O ≠ 0 := Nat.card_pos.ne'
    have h1 : (Nat.card O).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hOodd.not_two_dvd_nat
    rw [hNcard, Nat.factorization_mul hQpos hOpos]
    simp [h1]
  have hQsyl : Nat.card Q = 2 ^ (Nat.card (↥N ⧸ O)).factorization 2 := by
    rw [hQcard, hT'card, hT.card_eq, hfac]
  let Qs : Sylow 2 (↥N ⧸ O) := Sylow.ofCard Q hQsyl
  have hQs : (Qs : Subgroup (↥N ⧸ O)) = Q := Sylow.coe_ofCard _ _
  have hB := fusionBenderBorel_of_mulEquiv_psu3 (le_refl 2) e
  have : Finite (PSU3 2 2) := Finite.of_equiv _ e.toEquiv
  have hsp : SylowSpecial (↥N ⧸ O) := (sylowSpecial_PSU3 2 le_rfl).map_mulEquiv e.symm
  have haN : a ∈ N := hTN haT
  set a' : ↥N := ⟨a, haN⟩ with ha'
  have ha'T' : a' ∈ T' := haT
  have hāQ : π a' ∈ Q := Subgroup.mem_map_of_mem π ha'T'
  have hāQs : π a' ∈ (Qs : Subgroup (↥N ⧸ O)) := hQs ▸ hāQ
  have hā2 : π a' ^ 2 = 1 := by
    have h1 : a' * a' = 1 := Subtype.ext ha2
    rw [pow_two, ← map_mul, h1, map_one]
  have hcent := mem_centralizer_of_fusionBenderBorel hB (by norm_num) Qs hāQs hā2
  have hcenter : (⟨π a', hāQs⟩ : ↥(Qs : Subgroup (↥N ⧸ O))) ∈
      Subgroup.center ↥(Qs : Subgroup (↥N ⧸ O)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using (mem_centralizer_iff.mp hcent) g.1 g.2)
  have hcomm := hsp Qs hcenter
  have hcomm' : π a' ∈ ⁅(Qs : Subgroup (↥N ⧸ O)), (Qs : Subgroup (↥N ⧸ O))⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, hcomm, rfl⟩
  rw [hQs, hQ, ← Subgroup.map_commutator] at hcomm'
  obtain ⟨c, hc, hcπ⟩ := hcomm'
  have hcT' : c ∈ T' := Subgroup.commutator_le_self T' hc
  have hcea : c = a' := by
    have := hinj (a₁ := ⟨c, hcT'⟩) (a₂ := ⟨a', ha'T'⟩) (by simpa using hcπ)
    exact congrArg Subtype.val this
  rw [hcea] at hc
  have hT'map : T'.map N.subtype = T := by
    rw [hT', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTN]
  have hmem : a ∈ (⁅T', T'⁆).map N.subtype := ⟨a', hc, rfl⟩
  rw [Subgroup.map_commutator, hT'map] at hmem
  exact hmem

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
