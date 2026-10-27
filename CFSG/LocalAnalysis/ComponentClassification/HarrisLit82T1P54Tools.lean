module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54

open CFSG Subgroup Assembly.LowTwoRank
open scoped commutatorElement

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {w x : G} (hw : orderOf w = 2)
    (hx : x ∈ zpowers w) : x = 1 ∨ x = w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hw]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

theorem pPrimeCore_eq_bot_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 2 (center Q)) (h2 : 2 ∣ Nat.card Q) :
    pPrimeCore 2 Q = ⊥ := by
  have hodd : Odd (Nat.card (pPrimeCore 2 Q)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rcases LocalCores.quasisimple_normal_subgroups hQ
      (inferInstance : (pPrimeCore 2 Q).Normal) with h | h
  · exfalso
    rw [h, card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    obtain ⟨k, hk⟩ := hZ ⟨x, h hx⟩
    have h1 : orderOf x ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk
      simpa using this
    have h2' : orderOf x ∣ Nat.card (pPrimeCore 2 Q) := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : pPrimeCore 2 Q)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 Q)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2')

theorem fusionZStar_eq_center_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (h2 : 2 ∣ Nat.card Q) : Open.fusionZStar Q = center Q := by
  have hodd : Odd (Nat.card (pPrimeCore 2 Q)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOc : pPrimeCore 2 Q ≤ center Q := by
    rcases LocalCores.quasisimple_normal_subgroups hQ
        (inferInstance : (pPrimeCore 2 Q).Normal) with h | h
    · exfalso
      rw [h, card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    · exact h
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  have hZ : center (Q ⧸ center Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with hc | hc
    · exact hc
    · exact absurd (mem_center_iff.mp (hc ▸ mem_top b) a) hab
  apply le_antisymm
  · intro x hx
    rw [GSThmB.OddQuot.mem_fusionZStar_iff] at hx
    have hxZ : QuotientGroup.mk' (center Q) x ∈ center (Q ⧸ center Q) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (center Q) g
      have hc : ⁅x, m⁆ ∈ center Q := hOc (hx m)
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
    rw [hZ, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxZ
    exact hxZ
  · intro x hx
    exact GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => by
      rw [(commutatorElement_eq_one_iff_mul_comm).mpr (mem_center_iff.mp hx m).symm]
      exact one_mem _

theorem not_mem_fusionZStar {Y : Type} [Group Y] [Finite Y] (hq : IsQuasisimple Y) {t : Y}
    (ht : orderOf t = 2) {u : Y} (hu : u ∉ center Y) : u ∉ Open.fusionZStar Y := by
  rwa [fusionZStar_eq_center_of_isQuasisimple hq (ht ▸ orderOf_dvd_natCard t)]

theorem exists_mulEquiv_of_card_ker_two {U S Y : Type} [Group U] [Group S] [Group Y] [Finite U]
    [Finite Y] {β : U →* S} (hβ : Function.Surjective β) (hβ2 : Nat.card β.ker = 2)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* U), Function.Surjective π →
      π.ker ≤ center E → IsPGroup 2 π.ker → ∃ σ : U →* E, ∀ x, π (σ x) = x)
    (hq : IsQuasisimple Y) (hZ2 : IsPGroup 2 (center Y)) (hZ : center Y ≠ ⊥)
    (e : Y ⧸ center Y ≃* S) : ∃ α : U ≃* Y, β.ker.map α.toMonoidHom = center Y := by
  have : Group.IsPerfect Y := hq.1
  set η : Y →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Y)) with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect hsplit hβ hηs
    (hηker ▸ le_rfl) (hηker ▸ hZ2)
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h1
    apply hZ
    rw [← hηker, hker, ← h1, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have h1 : Nat.card α.ker = 1 := by
    rw [hβ2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hαβ (by rw [h, hβ2])) hne
  have hinj : Function.Injective α :=
    (MonoidHom.ker_eq_bot_iff α).1 (Subgroup.eq_bot_of_card_eq _ h1)
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hαs⟩, hker.symm.trans hηker⟩

theorem isTwoComponentIn_of_normal {G : Type*} [Group G] {J A : Subgroup G} (hJA : J ≤ A)
    (hn : (J.subgroupOf A).Normal) (hq : IsQuasisimple J) (hO : pPrimeCore 2 J = ⊥) :
    IsTwoComponentIn J A :=
  ⟨hJA, Subgroup.Normal.isSubnormal hn, hq.1, LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩

theorem isSLTwoOver_quot {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hJ : IsSLTwoOver (p ^ f) J) : IsSLTwoOver (p ^ f) (J ⧸ pPrimeCore 2 J) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h => by rw [h, pow_zero] at h5; omega
  obtain ⟨-, -, -, hO⟩ := Lemma47.sl2_facts hp hp2 hf h5 hJ
  exact isSLTwoOver_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hJ

theorem lieModel_psl_of_isSLTwoOver {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hJ : IsSLTwoOver (p ^ f) J) :
    Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 2 p f := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h => by rw [h, pow_zero] at h5; omega
  obtain ⟨-, -, hlie, hO⟩ := Lemma47.sl2_facts hp hp2 hf h5 hJ
  exact GSThmB.OddQuot.lieModel_of_equiv
    (QuotientGroup.quotientMulEquivOfEq (Frame.fusionZStar_eq_center hO)).symm hlie

theorem isQuasisimple_of_isSLTwoOver {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hJ : IsSLTwoOver (p ^ f) J) :
    IsQuasisimple J ∧ pPrimeCore 2 J = ⊥ := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h => by rw [h, pow_zero] at h5; omega
  obtain ⟨hq, -, -, hO⟩ := Lemma47.sl2_facts hp hp2 hf h5 hJ
  exact ⟨hq, hO⟩

end CFSG.ComponentClassification.HarrisLit.T1.P54
