module

public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.GH74.GLS.C3.Layer1.Back91Setup
public import CFSG.GH74.GLS.C3.Layer1.BackBasic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_two_of_ne_bot {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE : IsPGroup 2 E) (hne : E ≠ ⊥) : ∃ y ∈ E, orderOf y = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hE
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    exact Subgroup.eq_bot_of_card_eq E (by simpa using hn)
  have h2 : 2 ∣ Nat.card E := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem one_le_pRank_of_ne_bot {E : Subgroup G} (hE : IsPGroup 2 E) (hne : E ≠ ⊥) :
    1 ≤ pRank 2 ↥E := by
  obtain ⟨y, hyE, hy⟩ := exists_orderOf_two_of_ne_bot hE hne
  exact (U1a.one_le_pRank_zpowers hy).trans (pRank_mono' (zpowers_le.mpr hyE))

theorem exists_involution_central {Q R : Subgroup G} (hQ : IsPGroup 2 Q) (hR : IsPGroup 2 R)
    (hQne : Q ≠ ⊥) (hRQ : R ≤ normalizer (Q : Set G)) :
    ∃ u ∈ Q, orderOf u = 2 ∧ (∀ r ∈ R, u * r = r * u) ∧ (∀ q ∈ Q, u * q = q * u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := Q ⊔ R with hP
  have hPp : IsPGroup 2 P := hQ.to_sup_of_normal_left' hR hRQ
  have hQP : Q ≤ P := le_sup_left
  have hRP : R ≤ P := le_sup_right
  have hnorm : (Q.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQP]
    intro h k hh hk
    have hk' : k ∈ normalizer (Q : Set G) := sup_le le_normalizer hRQ hk
    exact (mem_normalizer_iff.mp hk' h).mp hh
  have hPpP : IsPGroup 2 ↥P := hPp
  have : Group.IsNilpotent ↥P := hPpP.isNilpotent
  have hne : Q.subgroupOf P ≠ ⊥ := by
    intro h
    apply hQne
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hQP] at h
    exact h
  have hW : Q.subgroupOf P ⊓ center ↥P ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hWp : IsPGroup 2 ↥(Q.subgroupOf P ⊓ center ↥P) := hPpP.to_subgroup _
  obtain ⟨w, hw, hw2⟩ := exists_orderOf_two_of_ne_bot hWp hW
  have hwQ : (w : G) ∈ Q := hw.1
  have hwc : ∀ y : ↥P, y * w = w * y := fun y => (Subgroup.mem_center_iff.mp hw.2 y)
  refine ⟨(w : G), hwQ, by rw [Subgroup.orderOf_coe]; exact hw2, fun r hr => ?_, fun q hq => ?_⟩
  · have := hwc ⟨r, hRP hr⟩
    exact (congrArg Subtype.val this).symm
  · have := hwc ⟨q, hQP hq⟩
    exact (congrArg Subtype.val this).symm

theorem isPCompIn_of_le {H H' K : Subgroup G} (h : IsPCompIn 2 H K) (hKH' : K ≤ H') (hH'H : H' ≤ H) :
    IsPCompIn 2 H' K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hKH', ?_⟩
  have h2 : K.subgroupOf H ≤ H'.subgroupOf H := fun x hx => hKH' hx
  have h3 := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 h.2 h2
  exact (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hH'H 2
    Nat.prime_two).mp h3

omit [Finite G] in
theorem perfect_of_isPCompIn {H K : Subgroup G} (h : IsPCompIn 2 H K) : ⁅K, K⁆ = K := by
  have hp : Group.IsPerfect (K.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect h.2
  have hp' : Group.IsPerfect K := by
    have e := Subgroup.subgroupOfEquivOfLe h.1
    have := hp
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.mp hp'

theorem le_of_perfect_of_le_sup_odd {A N O : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hO : Odd (Nat.card O)) (hON : O ≤ normalizer (N : Set G)) (hAle : A ≤ N ⊔ O) : A ≤ N := by
  set J : Subgroup G := N ⊔ O with hJ
  have hNJ : N ≤ J := le_sup_left
  have hOJ : O ≤ J := le_sup_right
  have hJnorm : J ≤ normalizer (N : Set G) := sup_le le_normalizer hON
  have hNn : (N.subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNJ]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp (hJnorm hk) h).mp hh
  let φ : ↥J →* ↥J ⧸ N.subgroupOf J := QuotientGroup.mk' _
  let ψ : ↥A →* ↥J ⧸ N.subgroupOf J := φ.comp (Subgroup.inclusion hAle)
  have hrange_le : ψ.range ≤ (O.subgroupOf J).map φ := by
    rintro _ ⟨a, rfl⟩
    have hx : (a : G) ∈ ((N ⊔ O : Subgroup G) : Set G) := hAle a.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hON] at hx
    obtain ⟨n, hn, o, ho, hno⟩ := hx
    refine ⟨⟨o, hOJ ho⟩, Subgroup.mem_subgroupOf.mpr ho, ?_⟩
    show φ ⟨o, hOJ ho⟩ = φ (Subgroup.inclusion hAle a)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (o : G)⁻¹ * (a : G) ∈ N
    rw [← hno]
    have : o⁻¹ * (n * o) = o⁻¹ * n * o⁻¹⁻¹ := by group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem (hON ho)) n).mp hn
  have hOdd : Odd (Nat.card ↥((O.subgroupOf J).map φ)) := by
    have h1 : Nat.card ↥((O.subgroupOf J).map φ) ∣ Nat.card ↥(O.subgroupOf J) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(O.subgroupOf J) = Nat.card ↥O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hO h1
  have hsolv : Group.IsSolvable ↥((O.subgroupOf J).map φ) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOdd
  have hsolv' : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hrange_le)
  have hperfA : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hA
  have hperfR : Group.IsPerfect ↥ψ.range := by
    have := hperfA
    exact Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) (MonoidHom.rangeRestrict_surjective ψ)
  have hbot : ψ.range = ⊥ := by
    by_contra hne
    have : Nontrivial ↥ψ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (G := ↥ψ.range) hsolv'
  intro a ha
  have h1 : ψ ⟨a, ha⟩ = 1 := by
    have : ψ ⟨a, ha⟩ ∈ ψ.range := ⟨⟨a, ha⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have h2 : (Subgroup.inclusion hAle ⟨a, ha⟩ : ↥J) ∈ N.subgroupOf J := (QuotientGroup.eq_one_iff _).mp h1
  exact h2

theorem inf_pPrimeCoreOf_le' {L M : Subgroup G} (hLM : L ≤ M) :
    L ⊓ pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 L := by
  refine Back.Setup91.le_pPrimeCoreOf_of_normalized inf_le_left (fun c hc w hw => ?_) ?_
  · exact ⟨L.mul_mem (L.mul_mem hc hw.1) (L.inv_mem hc),
      TwoThin.pPrimeCoreOf_normalized M (hLM hc) hw.2⟩
  · exact Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd M) (Subgroup.card_dvd_of_le inf_le_right)

theorem isSylowOf_of_cover {K L O S : Subgroup G} (hKL : K ≤ L) (hOL : O ≤ L)
    (hO : Odd (Nat.card O)) (hOn : ∀ l ∈ L, ∀ o ∈ O, l * o * l⁻¹ ∈ O) (hcov : L ≤ K ⊔ O)
    (hS : IsSylowOf 2 S K) : IsSylowOf 2 S L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hS ⊢
  obtain ⟨hSK, hS2, hSdvd⟩ := hS
  refine ⟨hSK.trans hKL, hS2, ?_⟩
  have hOnorm : (O.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOL]
    exact fun h k hh hk => hOn k hk h hh
  have hsup : O.subgroupOf L ⊔ K.subgroupOf L = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ O ⊔ K := by rw [sup_comm]; exact hcov hx
    have hmap : (O.subgroupOf L ⊔ K.subgroupOf L).map L.subtype = O ⊔ K := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hOL,
        Subgroup.map_subgroupOf_eq_of_le hKL]
    rw [← hmap] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy
  have hrel := relIndex_sup_eq_relIndex_of_normal (O.subgroupOf L)
    (K.subgroupOf L)
  rw [hsup, Subgroup.relIndex_top_right] at hrel
  have hidx : K.relIndex L ∣ Nat.card O := by
    have h1 : (K.subgroupOf L).index = K.relIndex L := rfl
    rw [h1] at hrel
    rw [hrel]
    have h2 : (K.subgroupOf L).relIndex (O.subgroupOf L) ∣ Nat.card ↥(O.subgroupOf L) :=
      Subgroup.index_dvd_card _
    have h3 : Nat.card ↥(O.subgroupOf L) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOL).toEquiv
    rwa [h3] at h2
  have hmul := Subgroup.relIndex_mul_relIndex S K L hSK hKL
  rw [← hmul]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hSdvd h
  · exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hO hidx)) (even_iff_two_dvd.mpr h)

omit [Finite G] in
theorem normalizer_eq_of_coatom (hG : IsSimpleGroup G) {M L : Subgroup G} (hM : IsCoatom M) (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hL0 : L ≠ ⊥) : normalizer (L : Set G) = M := by
  have hMN : M ≤ normalizer (L : Set G) := fun m hm => U1a.mem_normalizer_of_norm hLn hm
  by_contra hne
  have hlt : M < normalizer (L : Set G) := lt_of_le_of_ne hMN (Ne.symm hne)
  have htop : normalizer (L : Set G) = ⊤ := hM.2 _ hlt
  have hnormal : L.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact hL0 h
  · exact hM.1 (eq_top_iff.mpr (h ▸ hLM))

omit [Finite G] in
theorem normalizer_eq_self_of_coatom (hG : IsSimpleGroup G) {M : Subgroup G} (hM : IsCoatom M)
    (hM0 : M ≠ ⊥) : normalizer (M : Set G) = M := by
  by_contra hne
  have hlt : M < normalizer (M : Set G) := lt_of_le_of_ne le_normalizer (Ne.symm hne)
  have htop : normalizer (M : Set G) = ⊤ := hM.2 _ hlt
  have hnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with h | h
  · exact hM0 h
  · exact hM.1 h

end CFSG.GH74.GLS.C3.Layer1.Bk
