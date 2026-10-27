module

public import CFSG.Walter.Statement
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Walter.J1Props.Elt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.OddStandard.ThmC.O2.Gor

open CFSG Subgroup
open scoped MatrixGroups

theorem gw_exists_bad_psl2 (U : Sylow 2 PSL(2, GaloisField 2 4)) :
    ∃ d ∈ normalizer ((U : Subgroup PSL(2, GaloisField 2 4)) : Set PSL(2, GaloisField 2 4)),
      ∃ u ∈ (U : Subgroup PSL(2, GaloisField 2 4)), d ^ 3 * u * (d ^ 3)⁻¹ ≠ u := by
  obtain ⟨D, hDcyc, hDcard, -, hsup, hreg⟩ :=
    CFSG.Walter.psl2_even_normalizer_sylow_two (f := 4) (by norm_num) U
  obtain ⟨-, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two (f := 4) (by norm_num) U
  obtain ⟨g, hg⟩ := hDcyc.exists_generator
  have hord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hDcard]
    norm_num
  have hg3 : g ^ 3 ≠ 1 := by
    intro h
    have h15 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h15
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ : ∃ a : (U : Subgroup PSL(2, GaloisField 2 4)), a ≠ 1 := by
    rw [← Subgroup.ne_bot_iff_exists_ne_one]
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    norm_num at hUcard
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  refine ⟨(g : PSL(2, GaloisField 2 4)), ?_, u, hu, ?_⟩
  · rw [← hsup]
    exact Subgroup.mem_sup_right g.2
  · intro h
    have h1 : ((g ^ 3 : D) : PSL(2, GaloisField 2 4)) * u *
        ((g ^ 3 : D) : PSL(2, GaloisField 2 4))⁻¹ = u := by
      simpa [Subgroup.coe_pow] using h
    have h2 : ((1 : D) : PSL(2, GaloisField 2 4)) * u * ((1 : D) : PSL(2, GaloisField 2 4))⁻¹ =
        u := by simp
    exact hg3 ((hreg u hu hu1' u hu hu1').unique h1 h2)

theorem exists_bad_of_mulEquiv {G : Type} [Group G] [Finite G]
    (e : G ≃* PSL(2, GaloisField 2 4)) (P : Sylow 2 G) :
    ∃ g ∈ normalizer ((P : Subgroup G) : Set G), ∃ u ∈ (P : Subgroup G),
      g ^ 3 * u * (g ^ 3)⁻¹ ≠ u := by
  let U : Sylow 2 PSL(2, GaloisField 2 4) := P.mapSurjective (f := (e : G →* _)) e.surjective
  have hU : ∀ y, y ∈ (U : Subgroup PSL(2, GaloisField 2 4)) ↔ e.symm y ∈ (P : Subgroup G) := by
    intro y
    change y ∈ (P : Subgroup G).map (e : G →* _) ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨e.symm y, h, by simp⟩
  obtain ⟨d, hd, u, hu, hne⟩ := gw_exists_bad_psl2 U
  refine ⟨e.symm d, ?_, e.symm u, (hU u).1 hu, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.1 hd) (e x)
    rw [hU, hU] at h1
    simpa using h1
  · intro h
    apply hne
    simpa using congrArg e h

theorem gw_ree_not_dvd_sixteen (m : ℕ) : ¬ 16 ∣ CFSG.Open.ordRee (3 ^ (2 * m + 1)) := by
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

theorem gw_even_case_f_sixteen (f idx : ℕ) (hf : 2 ≤ f) (hidx : idx % 2 = 1)
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

theorem gw_odd_psl_not_dvd_eight (q : ℕ) (h : q % 8 = 3 ∨ q % 8 = 5) :
    ¬ 8 ∣ q * (q ^ 2 - 1) / 2 := by
  intro hd
  have hq1 : 1 ≤ q := by omega
  have h16 : q ^ 2 % 16 = 9 := by
    have : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
    rcases this with h | h | h | h <;> simp [pow_two, Nat.mul_mod, h]
  obtain ⟨k, hk⟩ : ∃ k, q ^ 2 - 1 = 16 * k + 8 := ⟨q ^ 2 / 16 - 0, by omega⟩
  have hq2 : Odd q := by rw [Nat.odd_iff]; omega
  have hmul : q * (q ^ 2 - 1) / 2 = 4 * (q * (2 * k + 1)) := by
    rw [hk]
    have : q * (16 * k + 8) = 2 * (4 * (q * (2 * k + 1))) := by ring
    rw [this]; simp
  rw [hmul] at hd
  have h2 : 2 ∣ q * (2 * k + 1) := by
    have : 4 * 2 ∣ 4 * (q * (2 * k + 1)) := by simpa using hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hodd : Odd (q * (2 * k + 1)) := hq2.mul (by simp)
  have := (Nat.odd_iff.mp hodd)
  omega

theorem nonempty_psl2_sixteen
    (hW : CFSG.Walter.WalterOrderForm)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hn : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) (hSab : IsMulCommutative (S : Subgroup G))
    (hS16 : Nat.card (S : Subgroup G) = 16) : Nonempty (G ≃* PSL(2, GaloisField 2 4)) := by
  have hidx : (S : Subgroup G).index % 2 = 1 := by
    have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    omega
  have hcard : Nat.card G = 16 * (S : Subgroup G).index := by
    rw [← Subgroup.card_mul_index (S : Subgroup G), hS16]
  rcases hW G hn S hSab with
    ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf0, h5le, hmod, ⟨e⟩⟩ | ⟨m, hm, hree⟩ | hJ
  ·
    have hG : Nat.card G = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.psl2_even_card (by omega)
    have hf4 := gw_even_case_f_sixteen f _ hf hidx (hG.symm.trans hcard)
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
    exact gw_odd_psl_not_dvd_eight (p ^ f) hmod h8
  ·
    exfalso
    have h16 : 16 ∣ Nat.card G := ⟨(S : Subgroup G).index, hcard⟩
    rw [hree] at h16
    exact gw_ree_not_dvd_sixteen m h16
  ·
    exfalso
    obtain ⟨e⟩ := hJ
    have hG : Nat.card G = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.J1Props.card_walterJ1
    have h16 : 16 ∣ Nat.card G := ⟨(S : Subgroup G).index, hcard⟩
    rw [hG] at h16
    omega

end CFSG.OddStandard.ThmC.O2.Gor
