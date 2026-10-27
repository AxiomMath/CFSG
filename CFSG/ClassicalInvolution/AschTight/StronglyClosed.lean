module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Goldschmidt
public import CFSG.GH74.Bender.Suzuki
public import CFSG.StronglyEmbedded.UniqueCosetEnd
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedA2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem isBenderGroup_of_fusionIsBenderGroup' {X : Type} [Group X]
    (h : CFSG.Open.fusionIsBenderGroup X) : CFSG.BenderSuzuki.IsBenderGroup X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact .isPSL2 f hf e
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
        CFSG.Models.benderPSU3Model_eq_psu3 f
    exact .isPSU3 f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  · exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr
      (CFSG.GH74.Bender.szModel_eq_sz a).symm))

theorem isSolvable_centralizer_of_isBenderGroup {X : Type} [Group X] [Finite X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) {z : X} (hz : orderOf z = 2) :
    Group.IsSolvable (Subgroup.centralizer ({z} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, i, e, hT⟩ := CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp h
  obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_orderOf_two hz)
  obtain ⟨t, hc⟩ := hT.exists_benderCore Q
  have hzQ' : z ∈ (Q : Subgroup X) := hzQ (Subgroup.mem_zpowers z)
  have hzr := hc.involution_iff.mp ⟨CFSG.GH74.Uniqueness.Bender.le_borel _ hzQ', hz⟩
  have hle : Subgroup.centralizer ({z} : Set X) ≤
      Subgroup.normalizer ((Q : Subgroup X) : Set X) := by
    rw [hc.centralizer_eq hzr.1 hzr.2]
    exact sup_le (CFSG.GH74.Uniqueness.Bender.le_borel _)
      ((CFSG.GH74.Uniqueness.Bender.fixCartan_le_cartan _ _).trans
        (CFSG.GH74.Uniqueness.Bender.cartan_le_borel _ _))
  have := CFSG.StronglyEmbedded.UniqueCoset.isSolvable_normalizer_sylow Q
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

variable {G : Type} [Group G]

theorem card_le_of_isPGroup_of_card_eq [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) {a j : ℕ}
    (hj : Odd j) (hG : Nat.card G = 2 ^ a * j) : Nat.card P ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := hP.exists_card_eq
  have h1 : 2 ^ c ∣ 2 ^ a * j := hc ▸ hG ▸ Subgroup.card_subgroup_dvd_card P
  have h2 : Nat.Coprime (2 ^ c) j := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hj)
  rw [hc]
  exact Nat.le_of_dvd (by positivity) (h2.dvd_of_dvd_mul_right h1)

theorem twoRank_le_one_of_sylow_unique_involution [Finite G] (T : Sylow 2 G)
    (hT : ∀ x ∈ (T : Subgroup G), ∀ y ∈ (T : Subgroup G), orderOf x = 2 → orderOf y = 2 →
      x = y) : CFSG.Open.twoRank G ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold CFSG.Open.twoRank CFSG.Open.pRank
  refine csSup_le ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by
    rw [Subgroup.mem_bot] at hx; rw [hx, one_pow]⟩, by simp⟩ ?_
  rintro k ⟨E, -, ⟨-, hE2⟩, hcard⟩
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := k) hcard
  obtain ⟨T', hET'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T T'
  have hT' : (T' : Subgroup G) = (T : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  have hU : ∀ x ∈ (T' : Subgroup G), ∀ y ∈ (T' : Subgroup G), orderOf x = 2 →
      orderOf y = 2 → x = y := by
    intro x hx y hy hx2 hy2
    rw [hT'] at hx hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hx2' : orderOf x' = 2 := by rw [← (MulAut.conj g).orderOf_eq x']; exact hx2
    have hy2' : orderOf y' = 2 := by rw [← (MulAut.conj g).orderOf_eq y']; exact hy2
    rw [hT x' hx' y' hy' hx2' hy2']
  have hEle : Nat.card E ≤ 2 := by
    by_cases hbot : E = ⊥
    · rw [hbot, Subgroup.card_bot]
      norm_num
    obtain ⟨⟨w, hwE⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hw2 : orderOf w = 2 := orderOf_eq_prime (hE2 w hwE) hw1'
    have hle : E ≤ Subgroup.zpowers w := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      · rw [hU y (hET' hy) w (hET' hwE) (orderOf_eq_prime (hE2 y hy) hy1) hw2]
        exact Subgroup.mem_zpowers w
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers w) := Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, hw2]
  rw [hcard] at hEle
  by_contra hk
  have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem eq_bot_of_stronglyClosed_of_abelian [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) {L : Subgroup G}
    (hLz : L ≤ Subgroup.centralizer ({z} : Set G)) (hL : ¬ Group.IsSolvable L)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR8 : 8 ≤ Nat.card R)
    (hRu : ∀ x ∈ R, ∀ y ∈ R, orderOf x = 2 → orderOf y = 2 → x = y)
    (h3 : 3 ≤ CFSG.Open.twoRank G) (T : Sylow 2 G) {A : Subgroup G}
    (hAT : A ≤ (T : Subgroup G)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hA1
  have hS := CFSG.ClassicalInvolution.Hat2A7.goldschmidtSimpleType_of_milestone
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian hnab T hA1 hAT hAab hcl
  have hbender : CFSG.Open.fusionIsBenderGroup G → False := by
    intro hB
    have := isSolvable_centralizer_of_isBenderGroup (isBenderGroup_of_fusionIsBenderGroup' hB) hz
    exact hL (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLz)
      (Subgroup.inclusion_injective hLz))
  have hsmall : ∀ a j : ℕ, a ≤ 3 → Odd j → Nat.card G = 2 ^ a * j → False := by
    intro a j ha hj hG
    obtain ⟨T', hRT'⟩ := hR2.exists_le_sylow
    have hT'le : Nat.card (T' : Subgroup G) ≤ 8 :=
      (card_le_of_isPGroup_of_card_eq T'.isPGroup' hj hG).trans
        (le_of_le_of_eq (Nat.pow_le_pow_right (by norm_num) ha) (by norm_num))
    have hRT : R = (T' : Subgroup G) := Subgroup.eq_of_le_of_card_ge hRT' (hT'le.trans hR8)
    have h1 := twoRank_le_one_of_sylow_unique_involution T' (hRT ▸ hRu)
    omega
  rcases hS with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
    ⟨p, f, hp, hodd, hf0, -, hmod, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e⟩⟩
  · exact hbender (Or.inl ⟨f, by omega, ⟨e⟩⟩)
  · exact hbender (Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩))
  · exact hbender (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  · have hf0' : f ≠ 0 := by omega
    have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0'
    have hodd' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hp.out, hodd, hf0, hK⟩
    have hc := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p f) hodd'
    rw [hK] at hc
    obtain ⟨j, hj, hj4⟩ := CFSG.ClassicalInvolution.Hat2A7.psl2_card_eq_four_mul_odd hmod
    exact hsmall 2 j (by norm_num) hj (by
      rw [Nat.card_congr e.toEquiv]
      exact hc.trans (hj4.trans (by norm_num)))
  · obtain ⟨j, hj, hj8⟩ := CFSG.ClassicalInvolution.Hat2A7.ordRee_eq_eight_mul_odd m
    exact hsmall 3 j le_rfl hj (by rw [hcard, hj8]; norm_num)
  · exact hsmall 3 21945 le_rfl ⟨10972, by norm_num⟩
      (by rw [← CFSG.ClassicalInvolution.Hat2A7.card_goldschmidtJ1_eq, Nat.card_congr e.toEquiv])

variable {p f : ℕ} [Fact p.Prime]

end CFSG.ClassicalInvolution.Disconnected.AschTight
