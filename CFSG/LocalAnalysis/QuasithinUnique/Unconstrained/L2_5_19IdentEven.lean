module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open BenderSuzuki.MatrixGroups

section KTypeElements

theorem exists_two_elt_of_nonab {H : Type} [Group H] [Finite H]
    (h : ∀ P : Subgroup H, IsSylowTwoOf P ⊤ → ∃ y ∈ P, y ^ 2 ≠ 1) :
    ∃ y : H, ∃ m : ℕ, y ^ (2 ^ m) = 1 ∧ y ^ 2 ≠ 1 := by
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (⊤ : Subgroup H)
  obtain ⟨y, hy, hy2⟩ := h S hS
  obtain ⟨m, hm⟩ := hS.2.1 ⟨y, hy⟩
  refine ⟨y, m, ?_, hy2⟩
  have := congrArg Subtype.val hm
  simpa using this

theorem exists_two_elt_alt6 : ∃ y : alternatingGroup (Fin 6), y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  have hσ : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5 ∈
      alternatingGroup (Fin 6) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)
  refine ⟨⟨_, hσ⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    decide
  · intro h
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    revert this
    decide

variable {G : Type} [Group G] [Finite G]

theorem isKType_exists_two_elt
    {K : Subgroup G} (hK : IsKType K) :
    ∃ y : ↥K, ∃ m : ℕ, y ^ (2 ^ m) = 1 ∧ y ^ 2 ≠ 1 := by
  rcases hK with ⟨p, hp, h7, hm⟩ | hK | hK
  · exact exists_two_elt_of_nonab (l2pFacts ↥K (Or.inl ⟨p, hp, h7, hm⟩)).nonab
  · exact exists_two_elt_of_nonab (l2pFacts ↥K (Or.inr hK)).nonab
  · obtain ⟨e⟩ := hK
    obtain ⟨y, hy4, hy2⟩ := exists_two_elt_alt6
    refine ⟨e.symm y, 2, ?_, fun h => hy2 ?_⟩
    · rw [← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, hy4, map_one]
    · exact e.symm.injective (by rw [map_pow, h, map_one])

end KTypeElements

section L2Even

theorem two_power_sq_eq_one_psl2 {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hcard : Nat.card F = 2 ^ f) (z : PSL2MatrixGroup F) {m : ℕ} (hz : z ^ (2 ^ m) = 1) :
    z ^ 2 = 1 := by
  have hord : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hz
  have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hpos : 0 < 2 ^ f := by positivity
  have hodd : ∀ N : ℕ, Odd N → orderOf z ∣ N → z ^ 2 = 1 := by
    intro N hN hzN
    have hcop : Nat.Coprime (2 ^ m) N := (Nat.coprime_two_left.mpr hN).pow_left m
    have h1 : orderOf z ∣ Nat.gcd (2 ^ m) N := Nat.dvd_gcd hord hzN
    rw [hcop] at h1
    have : orderOf z = 1 := Nat.dvd_one.mp h1
    rw [orderOf_eq_one_iff.mp this]
    exact one_pow 2
  have hgcd : Nat.gcd (2 ^ f - 1) 2 = 1 := by
    have : ¬ 2 ∣ 2 ^ f - 1 := by omega
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this)
  rcases CFSG.Glauberman.Dickson.psl2_orderOf_dvd (p := 2) hcard z with h | h | h
  · exact orderOf_dvd_iff_pow_eq_one.mp h
  · rw [hcard, hgcd, Nat.div_one] at h
    exact hodd _ (Nat.odd_iff.mpr (by omega)) h
  · rw [hcard, hgcd, Nat.div_one] at h
    exact hodd _ (Nat.odd_iff.mpr (by omega)) h

variable {G : Type} [Group G] [Finite G]

theorem tabIdentFor_l2Even
    : TabIdentFor @Ident.FamL2Even := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨-, f, hf, -, F, _, _, hcard, ⟨e⟩⟩ := hX
  let e' : ↥X ≃* PSL2MatrixGroup F :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  obtain ⟨y, m, hym, hy2⟩ := isKType_exists_two_elt hs.ktype
  let y' : ↥X := ⟨(y : G), hs.K_le y.2⟩
  have hy'm : y' ^ (2 ^ m) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hym
    simpa [y'] using this
  have hz : (e' y') ^ (2 ^ m) = 1 := by rw [← map_pow, hy'm, map_one]
  have h2 := two_power_sq_eq_one_psl2 (by omega) hcard (e' y') hz
  have hy'2 : y' ^ 2 = 1 := e'.injective (by rw [map_pow, h2, map_one])
  apply hy2
  apply Subtype.ext
  have := congrArg Subtype.val hy'2
  simpa [y'] using this

end L2Even

section Suzuki

theorem isKType_three_dvd {G : Type} [Group G] {K : Subgroup G} (hK : IsKType K) :
    3 ∣ Nat.card ↥K := by
  rcases isKType_card hK with h | h | ⟨p, -, -, hpk⟩
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · have h3 : 3 ∣ p * (p * p - 1) := by
      by_cases hp0 : p % 3 = 0
      · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hp0) _
      · have hpp : p * p % 3 = 1 := by
          have : p % 3 = 1 ∨ p % 3 = 2 := by omega
          rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
        exact Dvd.dvd.mul_left (by omega) _
    rw [hpk] at h3
    omega

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : Nat.Prime 3 := by norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  intro h
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := h3.dvd_of_dvd_pow h
      omega
    · omega
  · have h4 : q ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hq]
    omega

variable {G : Type} [Group G] [Finite G]

theorem tabIdentFor_suzuki :
    TabIdentFor @Ident.FamSuzuki := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨-, f, -, -, hm⟩ := hX
  obtain ⟨-, a, -, F, _, _, hfa, hcard, ⟨e⟩⟩ := hm
  subst hfa
  have hXcard : Nat.card ↥X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.Ree.suzuki_order hcard
  have hdvd : Nat.card ↥K ∣ Nat.card ↥X :=
    (hs.card_dvd hs.ktype).trans (Subgroup.card_quotient_dvd_card _)
  have h3 : 3 ∣ Nat.card ↥X := (isKType_three_dvd hs.ktype).trans hdvd
  rw [hXcard] at h3
  exact not_three_dvd_suzuki_order a h3

end Suzuki

end CFSG.QuasithinUnique.Id2519
