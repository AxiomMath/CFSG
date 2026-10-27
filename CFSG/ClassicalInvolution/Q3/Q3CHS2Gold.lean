module

public import CFSG.ClassicalInvolution.AschTight.StronglyClosed
public import CFSG.ClassicalInvolution.AschTight.S19RCore

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.GH74.Uniqueness.Bender (borel le_borel fixCartan_le_cartan cartan_le_borel)

theorem commute_of_isBenderGroup {X : Type} [Group X] [Finite X]
    (h : CFSG.BenderSuzuki.IsBenderGroup X) {z a b : X} (hz : orderOf z = 2)
    (ha : a ∈ Subgroup.centralizer ({z} : Set X)) (hb : b ∈ Subgroup.centralizer ({z} : Set X))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, i, e, hT⟩ := CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp h
  obtain ⟨Q, hzQ⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_orderOf_two hz)
  obtain ⟨t, hc⟩ := hT.exists_benderCore Q
  have hzQ' : z ∈ (Q : Subgroup X) := hzQ (Subgroup.mem_zpowers z)
  have hzr := hc.involution_iff.mp ⟨le_borel _ hzQ', hz⟩
  have hle : Subgroup.centralizer ({z} : Set X) ≤ borel (Q : Subgroup X) := by
    rw [hc.centralizer_eq hzr.1 hzr.2]
    exact sup_le (le_borel _) ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _))
  have har := (hc.involution_iff.mp ⟨hle ha, ha2⟩).1
  have hbr := (hc.involution_iff.mp ⟨hle hb, hb2⟩).1
  have ha' : a ∈ (Q : Subgroup X) := (Subgroup.mem_inf.mp har).1
  have hb' : b ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X) := (Subgroup.mem_inf.mp hbr).2
  exact Subgroup.mem_centralizer_iff.mp hb' a ha'

variable {G : Type} [Group G]

theorem eq_bot_of_stronglyClosed_of_abelian3 [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z a b : G} (hz : orderOf z = 2)
    (ha : a ∈ Subgroup.centralizer ({z} : Set G)) (hb : b ∈ Subgroup.centralizer ({z} : Set G))
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b ≠ b * a)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR8 : 8 ≤ Nat.card R)
    (hRu : ∀ x ∈ R, ∀ y ∈ R, orderOf x = 2 → orderOf y = 2 → x = y)
    (h3 : 3 ≤ twoRank G) (T : Sylow 2 G) {A : Subgroup G}
    (hAT : A ≤ (T : Subgroup G)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) → g⁻¹ * a * g ∈ A) : A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hA1
  have hS := Hat2A7.goldschmidtSimpleType_of_milestone
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian hnab T hA1 hAT hAab hcl
  have hbender : fusionIsBenderGroup G → False := fun hB =>
    hab (commute_of_isBenderGroup (isBenderGroup_of_fusionIsBenderGroup' hB) hz ha hb ha2 hb2)
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
    obtain ⟨j, hj, hj4⟩ := Hat2A7.psl2_card_eq_four_mul_odd hmod
    exact hsmall 2 j (by norm_num) hj (by
      rw [Nat.card_congr e.toEquiv]
      exact hc.trans (hj4.trans (by norm_num)))
  · obtain ⟨j, hj, hj8⟩ := Hat2A7.ordRee_eq_eight_mul_odd m
    exact hsmall 3 j le_rfl hj (by rw [hcard, hj8]; norm_num)
  · exact hsmall 3 21945 le_rfl ⟨10972, by norm_num⟩
      (by rw [← Hat2A7.card_goldschmidtJ1_eq, Nat.card_congr e.toEquiv])

end CFSG.ClassicalInvolution.Q3.Q3CH
