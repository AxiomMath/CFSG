module

public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.Bender
public import CFSG.GH74.Uniqueness.SU.SU14Walter

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup

theorem ree_not_dvd_sixteen (m : ℕ) : ¬ 16 ∣ CFSG.Open.ordRee (3 ^ (2 * m + 1)) := by
  unfold CFSG.Open.ordRee
  have hmod : ∀ m : ℕ, 3 ^ (2 * m + 1) % 16 = 3 ∨ 3 ^ (2 * m + 1) % 16 = 11 := by
    intro m
    induction m with
    | zero => left; norm_num
    | succ k ih =>
      have : 3 ^ (2 * (k + 1) + 1) = 3 ^ (2 * k + 1) * 9 := by ring
      rw [this, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  have hpos : 1 ≤ 3 ^ (2 * m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hm := hmod m
  generalize 3 ^ (2 * m + 1) = q at hpos hm ⊢
  intro h
  have h1 : (q ^ 3 * (q ^ 3 + 1) * (q - 1)) % 16 = 0 := Nat.mod_eq_zero_of_dvd h
  rcases hm with h3 | h3
  · have hq1 : (q - 1) % 16 = 2 := by omega
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, h3, hq1] at h1
  · have hq1 : (q - 1) % 16 = 10 := by omega
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, h3, hq1] at h1

theorem even_case_f_sixteen (f idx : ℕ) (hf : 2 ≤ f) (hidx : idx % 2 = 1)
    (h : 2 ^ f * ((2 ^ f) ^ 2 - 1) = 16 * idx) : f = 4 := by
  by_cases hf5 : 5 ≤ f
  · exfalso
    have h32 : 2 ^ 5 ∣ 2 ^ f := Nat.pow_dvd_pow 2 hf5
    have : 32 ∣ 16 * idx := by
      rw [← h]
      exact Dvd.dvd.mul_right (by simpa using h32) _
    omega
  · have hf4 : f ≤ 4 := by omega
    interval_cases f
    · norm_num at h
      omega
    · norm_num at h
      omega
    · rfl

theorem nonempty_psl2_sixteen_of_abelian_sylow
    {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (hSab : IsMulCommutative (S : Subgroup G)) (hS16 : Nat.card (S : Subgroup G) = 16) :
    Nonempty (G ≃* CFSG.Theory.Comparator.PSL2Model 4) := by
  have hidx : (S : Subgroup G).index % 2 = 1 := by
    have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    omega
  have hcard : Nat.card G = 16 * (S : Subgroup G).index := by
    rw [← Subgroup.card_mul_index (S : Subgroup G), hS16]
  rcases CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hn S hSab with
    ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf0, h5le, hmod, ⟨e⟩⟩ | ⟨m, hm, hree⟩ | hJ
  ·
    have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (K := GaloisField 2 f) (CharTwo.neg_eq 1)
    have hpsl := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center (K := GaloisField 2 f)
    rw [hK, hcenter, mul_one] at hpsl
    have hG : Nat.card G = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact hpsl
    have hf4 := even_case_f_sixteen f _ hf hidx (hG.symm.trans hcard)
    subst hf4
    exact ⟨e⟩
  ·
    exfalso
    have hcardK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p f)) :=
      ⟨p, f, hp.out, hpodd, hf0, hcardK⟩
    have hG : Nat.card G = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _ hodd, hcardK]
    have h8 : 8 ∣ Nat.card G := ⟨2 * (S : Subgroup G).index, by rw [hcard]; ring⟩
    rw [hG] at h8
    exact SU14.odd_psl_not_dvd_eight (p ^ f) hmod h8
  ·
    exfalso
    have h16 : 16 ∣ Nat.card G := ⟨(S : Subgroup G).index, hcard⟩
    rw [hree] at h16
    exact ree_not_dvd_sixteen m h16
  ·
    exfalso
    obtain ⟨e⟩ := hJ
    have hG : Nat.card G = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.J1Props.card_walterJ1
    have h16 : 16 ∣ Nat.card G := ⟨(S : Subgroup G).index, hcard⟩
    rw [hG] at h16
    omega

theorem false_of_central_quotient_sylow_sixteen
    {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) (hZ2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (P : Sylow 2 (K ⧸ center K)) (hP : IsMulCommutative (P : Subgroup (K ⧸ center K)))
    (hcard : Nat.card (P : Subgroup (K ⧸ center K)) = 16) : False := by
  obtain ⟨hperf, hsimp, hnab⟩ := hq
  obtain ⟨e⟩ := nonempty_psl2_sixteen_of_abelian_sylow hsimp hnab P hP hcard
  have hL : CFSG.Blueprint.LieModel (K ⧸ center K) .PSL 2 2 4 :=
    CFSG.GH74.lieModel_PSL_two_two_of_mulEquiv_psl2Model (by norm_num) e
  exact hZ (CFSG.GH74.KGroups.noTwoCover_even (K ⧸ center K) (Or.inr (Or.inl hL)) K
    ⟨hperf, hsimp, hnab⟩ hZ2 ⟨MulEquiv.refl _⟩)

end CFSG.GH74.Uniqueness.SU.K.R4
