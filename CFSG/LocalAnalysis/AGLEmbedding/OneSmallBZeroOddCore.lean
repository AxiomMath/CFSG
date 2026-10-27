module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem commute_of_plane {p : ℕ} (hp : p.Prime) {A V : Subgroup G} (hA : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (hVp : ¬ p ∣ Nat.card V) {c : G}
    (hc : ∀ b ∈ A, b ≠ 1 → ∀ u ∈ V ⊓ Subgroup.centralizer ({b} : Set G), Commute u c) :
    ∀ u ∈ V, Commute u c := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative A := hA.1
  have : IsElementaryAbelian p A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hA.2 x x.2) }
  have : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hAcard]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  intro u hu
  have hgen := RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) hAV hVp hu
  have hle : (⨆ (B : Subgroup A) (_ : B.index = p),
      V ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G)) ≤
        Subgroup.centralizer ({c} : Set G) := by
    refine iSup₂_le fun B hB => ?_
    have hBcard : Nat.card B = p := by
      have h := B.card_mul_index
      rw [hB, hAcard] at h
      have : Nat.card B * p = p * p := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos this
    obtain ⟨b, hb⟩ : ∃ b : B, b ≠ 1 := by
      by_contra h
      push Not at h
      have : Nat.card B = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by rw [h x, h y]⟩,
        inferInstance⟩
      rw [hBcard] at this
      exact hp.one_lt.ne' this
    have hb1 : ((b : A) : G) ≠ 1 := fun h1 => hb (Subtype.ext (Subtype.ext h1))
    intro w hw
    have hwV := hw.1
    have hwb : w ∈ Subgroup.centralizer ({((b : A) : G)} : Set G) :=
      Subgroup.centralizer_le (by
        rintro _ rfl
        exact ⟨b, b.2, rfl⟩) hw.2
    have h := hc _ (b : A).2 hb1 w ⟨hwV, hwb⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact h.symm.eq
  have := Subgroup.mem_centralizer_iff.mp (hle hgen) c rfl
  exact this.symm

theorem eq_one_of_plane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hchar : IsCharTwoType G)
    {M A : Subgroup G} (hM : IsTwoLocal M) (hAM : A ≤ M) (hA : IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) {a : G} (ha : a ∈ A)
    (hC : ∀ b ∈ A, b ∉ Subgroup.zpowers a →
      pCoreOf 2 M ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer ({a} : Set G)) :
    a = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hVp : ¬ p ∣ Nat.card (pCoreOf 2 M) := by
    intro hdvd
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hAV : A ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
    hAM.trans (localGroup_le_normalizer_pCoreOf 2 M)
  have hcomm := commute_of_plane hp hA hAcard hAV hVp (c := a) (fun b hb hb1 u hu => by
    by_cases hba : b ∈ Subgroup.zpowers a
    ·
      have ha1 : a ≠ 1 := fun h => hb1 (by
        rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hba
        exact hba)
      have hab := mem_zpowers_of_mem_zpowers_of_prime hp (orderOf_eq_prime (hA.2 a ha) ha1) hba hb1
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hab
      have hub : u * b = b * u := Subgroup.mem_centralizer_singleton_iff.mp hu.2
      exact Commute.zpow_right (show Commute u b from hub) j
    · have := hC b hb hba hu
      exact (Subgroup.mem_centralizer_iff.mp this a rfl).symm)
  have haC : a ∈ M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
    ⟨hAM ha, Subgroup.mem_centralizer_iff.mpr fun u hu => (hcomm u hu).eq⟩
  have haQ := hchar M hM haC
  obtain ⟨k, hk⟩ := h2 ⟨a, haQ⟩
  have hak : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hap : a ^ p = 1 := hA.2 a ha
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 : orderOf a ∣ Nat.gcd (2 ^ k) p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hak) (orderOf_dvd_of_pow_eq_one hap)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h1
  exact orderOf_eq_one_iff.mp h1

end CFSG.AGLEmbedding
