module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Syl
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddNormalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.U3TwoAdic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ABGLocalTools
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

section Regular

variable (hF : Nat.card F = (p ^ f) ^ 2)

theorem centralizer_tSU_of_regular {μ : Fˣ} (h01 : (μ : F) ≠ ((μ ^ (p ^ f - 1) : Fˣ) : F))
    (h02 : (μ : F) ≠ (((μ ^ (p ^ f)) ⁻¹ : Fˣ) : F))
    (h12 : ((μ ^ (p ^ f - 1) : Fˣ) : F) ≠ (((μ ^ (p ^ f)) ⁻¹ : Fˣ) : F)) :
    Subgroup.centralizer ({tSU hF μ} : Set (SU (unitaryInvolution F p f) 3)) =
      (tSU hF).range := by
  ext x
  constructor
  · intro hx
    have hc := hx (tSU hF μ) rfl
    have hm : (((tSU hF μ : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (((x : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (((x : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * (((tSU hF μ : SU (unitaryInvolution F p f) 3) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
      congrArg (fun g : SU (unitaryInvolution F p f) 3 => ((g : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)) hc
    have hd : (((tSU hF μ : SU (unitaryInvolution F p f) 3) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![(μ : F), ((μ ^ (p ^ f - 1) : Fˣ) : F),
          (((μ ^ (p ^ f)) ⁻¹ : Fˣ) : F)] := rfl
    rw [hd] at hm
    have := eq_diagonal_of_commute h01 h02 h12 hm.symm
    exact exists_tSU_of_diagonal hF this
  · rintro ⟨ν, rfl⟩ g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [← map_mul, ← map_mul, mul_comm]

end Regular

section Orders

variable (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1)

include hω hq3 in
theorem pow_two_mul_card_add_one_eq_one {u : SU (unitaryInvolution F p f) 3}
    (hu : u ∈ normA0 hF ω) (hnT : u ∉ (tSU hF).range) : u ^ (2 * (p ^ f + 1)) = 1 := by
  obtain ⟨t, ⟨μ, rfl⟩, rfl⟩ := ((mem_normalizer_a0_iff hF hω hq3 u).1 hu).resolve_left hnT
  have hμ : μ ^ ((p ^ f) ^ 2) = μ := Units.ext (by
    rw [Units.val_pow_eq_pow_val]; exact pow_card_sq_eq hF _)
  have hsq : (tSU hF μ * sSU) ^ 2 = tSU hF (μ * (μ ^ (p ^ f))⁻¹) := by
    calc (tSU hF μ * sSU) ^ 2 = tSU hF μ * (sSU * tSU hF μ) * sSU := by
          rw [pow_two]; simp only [mul_assoc]
      _ = tSU hF μ * (tSU hF (μ ^ (p ^ f))⁻¹ * sSU) * sSU := by rw [sSU_mul_tSU]
      _ = tSU hF μ * tSU hF (μ ^ (p ^ f))⁻¹ * (sSU * sSU) := by group
      _ = tSU hF (μ * (μ ^ (p ^ f))⁻¹) := by rw [sSU_mul_self, mul_one, map_mul]
  have key : (μ * (μ ^ (p ^ f))⁻¹) ^ (p ^ f + 1) = 1 := by
    rw [mul_pow, inv_pow, ← pow_mul]
    have : μ ^ (p ^ f * (p ^ f + 1)) = μ ^ (p ^ f + 1) := by
      rw [mul_add, mul_one, pow_add, ← sq, hμ, pow_succ]
      exact mul_comm _ _
    rw [this, mul_inv_cancel]
  rw [pow_mul, hsq, ← map_pow, key, map_one]

include hω hq3 in
theorem pow_four_eq_one_of_mem {S₀ : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hq4 : (p ^ f) % 4 = 1) (hS₀N : S₀ ≤ normA0 hF ω) (hS₀ : IsPGroup 2 S₀)
    {u : SU (unitaryInvolution F p f) 3} (hu : u ∈ S₀) (hnT : u ∉ (tSU hF).range) :
    u ^ 4 = 1 := by
  have h1 := pow_two_mul_card_add_one_eq_one hF hω hq3 (hS₀N hu) hnT
  obtain ⟨j, hj⟩ := hS₀ ⟨u, hu⟩
  have hj' : u ^ (2 ^ j) = 1 := congrArg Subtype.val hj
  have hd1 : orderOf u ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hd2 : orderOf u ∣ 2 * (p ^ f + 1) := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
  have hvq : padicValNat 2 (p ^ f + 1) = 1 := u3two_padic_add_one_of_mod4_one _ hq4
  have hi : i ≤ 2 := by
    have h2i : 2 ^ i ∣ 2 * (p ^ f + 1) := hio ▸ hd2
    have hne : 2 * (p ^ f + 1) ≠ 0 := by omega
    have := (padicValNat_dvd_iff_le hne).1 h2i
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self, hvq] at this
    omega
  have : orderOf u ∣ 4 := by
    rw [hio]
    exact (pow_dvd_pow 2 hi).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 this

end Orders

section Torus

variable (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem tSU_regular_of_orderOf (hq4 : (p ^ f) % 4 = 1) {μ : Fˣ} {i : ℕ} (hμ : orderOf μ = 2 ^ i)
    (hi : 3 ≤ i) :
    (μ : F) ≠ ((μ ^ (p ^ f - 1) : Fˣ) : F) ∧ (μ : F) ≠ (((μ ^ (p ^ f)) ⁻¹ : Fˣ) : F) ∧
      ((μ ^ (p ^ f - 1) : Fˣ) : F) ≠ (((μ ^ (p ^ f)) ⁻¹ : Fˣ) : F) := by
  have hq2 : 2 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    by_contra h
    have h2 : p ^ f ≤ 1 := by omega
    have h3 : (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  have hbad : ∀ N : ℕ, N ≠ 0 → padicValNat 2 N ≤ 1 → μ ^ N = 1 → False := by
    intro N hN hv hμN
    have h1 : 2 ^ i ∣ N := hμ ▸ orderOf_dvd_of_pow_eq_one hμN
    have := (padicValNat_dvd_iff_le hN).1 h1
    omega
  have hodd : ∀ N : ℕ, Odd N → padicValNat 2 N ≤ 1 := fun N h => by
    rw [u3two_padic_of_odd h]; omega
  have hq1 : (p ^ f) % 2 = 1 := by omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h' : μ = μ ^ (p ^ f - 1) := Units.ext h
    refine hbad (p ^ f - 2) (by omega) (hodd _ (Nat.odd_iff.2 (by omega))) ?_
    have h2 : μ ^ (p ^ f - 1) = μ ^ (p ^ f - 2) * μ := by
      rw [← pow_succ]; congr 1; omega
    rw [h2] at h'
    exact mul_eq_right.mp h'.symm
  · have h' : μ = (μ ^ (p ^ f))⁻¹ := Units.ext h
    refine hbad (p ^ f + 1) (by omega) ?_ ?_
    · rw [u3two_padic_add_one_of_mod4_one _ hq4]
    · have h2 : μ * μ ^ (p ^ f) = 1 := by
        calc μ * μ ^ (p ^ f) = μ * (μ ^ (p ^ f))⁻¹⁻¹ := by rw [inv_inv]
          _ = 1 := by rw [← h']; exact mul_inv_cancel _
      rw [pow_succ', ← h2]
  · have h' : μ ^ (p ^ f - 1) = (μ ^ (p ^ f))⁻¹ := Units.ext h
    refine hbad (2 * p ^ f - 1) (by omega) (hodd _ (Nat.odd_iff.2 (by omega))) ?_
    have h2 : μ ^ (p ^ f - 1) * μ ^ (p ^ f) = 1 := by
      rw [h']; exact inv_mul_cancel _
    rw [← h2, ← pow_add]; congr 1; omega

end Torus

section Normalizer

variable (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1)

omit [CharP F p] [Fact p.Prime] in
include hω in
theorem mem_zpowers_of_pow_three_eq_one {μ : Fˣ} (hμ : μ ^ 3 = 1) : μ ∈ Subgroup.zpowers ω := by
  classical
  have := Fintype.ofFinite Fˣ
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h1 : μ = 1
  · rw [h1]; exact Subgroup.one_mem _
  have hμo : orderOf μ = 3 := orderOf_eq_prime hμ h1
  have hdvd : 3 ∣ Fintype.card Fˣ := by
    rw [← Nat.card_eq_fintype_card, ← hω]; exact orderOf_dvd_natCard ω
  have hcard : (Finset.univ.filter fun a : Fˣ => orderOf a = 3).card = Nat.totient 3 :=
    IsCyclic.card_orderOf_eq_totient hdvd
  have hω1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; omega
  have hω2o : orderOf (ω ^ 2) = 3 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hω]; norm_num)]; exact hω
  have hω2 : ω ^ 2 ≠ ω := by
    intro h
    have : ω = 1 := by
      have : ω * ω = ω * 1 := by rw [mul_one, ← pow_two]; exact h
      exact mul_left_cancel this
    exact hω1 this
  by_contra hμω
  have hμω2 : μ ≠ ω ^ 2 := fun h => hμω (by
    rw [h]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ω) 2)
  have hμω' : μ ≠ ω := fun h => hμω (h ▸ Subgroup.mem_zpowers ω)
  have hsub : ({ω, ω ^ 2, μ} : Finset Fˣ) ⊆ Finset.univ.filter fun a : Fˣ => orderOf a = 3 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact hω
    · exact hω2o
    · exact hμo
  have h3le := Finset.card_le_card hsub
  rw [hcard, Finset.card_insert_of_notMem (by simp [hω2.symm, hμω'.symm]),
    Finset.card_insert_of_notMem (by simp [hμω2.symm]), Finset.card_singleton] at h3le
  norm_num [Nat.totient_prime Nat.prime_three] at h3le

include hω hq3 in
theorem mem_normA0_of_forall_conj_mem_range {n : SU (unitaryInvolution F p f) 3}
    (h : ∀ g ∈ (tSU hF).range, n * g * n⁻¹ ∈ (tSU hF).range) : n ∈ normA0 hF ω := by
  have ha₀ : tSU hF ω ∈ (tSU hF).range := ⟨ω, rfl⟩
  obtain ⟨μ', hμ'⟩ := h _ ha₀
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hcube : (tSU hF μ') ^ 3 = 1 := by
    rw [hμ', conj_pow, ← map_pow, hω3, map_one]
    group
  have hμ3 : μ' ^ 3 = 1 := tSU_injective hF (by rw [map_pow, hcube, map_one])
  have hmem' : tSU hF μ' ∈ Subgroup.zpowers (tSU hF ω) := by
    rw [← MonoidHom.map_zpowers]
    exact ⟨μ', mem_zpowers_of_pow_three_eq_one hω hμ3, rfl⟩
  have hmem : n * tSU hF ω * n⁻¹ ∈ Subgroup.zpowers (tSU hF ω) := hμ' ▸ hmem'
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hmem k

end Normalizer

section Key

theorem normalizer_le_normA0 (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ} (hω : orderOf ω = 3)
    (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 1)
    {S₀ : Subgroup (SU (unitaryInvolution F p f) 3)} (hS₀N : S₀ ≤ normA0 hF ω)
    (hS₀ : IsPGroup 2 S₀) {x : SU (unitaryInvolution F p f) 3} (hxS : x ∈ S₀)
    (hxT : x ∈ (tSU hF).range) {i : ℕ} (hxo : orderOf x = 2 ^ i) (hi : 3 ≤ i) :
    Subgroup.normalizer (S₀ : Set (SU (unitaryInvolution F p f) 3)) ≤ normA0 hF ω := by
  intro n hn
  have hy : n * x * n⁻¹ ∈ S₀ := (Subgroup.mem_normalizer_iff.1 hn x).1 hxS
  have hyo : orderOf (n * x * n⁻¹) = 2 ^ i := by
    rw [← hxo]
    simpa [MulAut.conj_apply] using (MulAut.conj n).orderOf_eq x
  have hyT : n * x * n⁻¹ ∈ (tSU hF).range := by
    by_contra hnT
    have h4 := pow_four_eq_one_of_mem hF hω hq3 hq4 hS₀N hS₀ hy hnT
    have h5 := orderOf_le_of_pow_eq_one (by norm_num) h4
    rw [hyo] at h5
    have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    omega
  obtain ⟨μ, rfl⟩ := hxT
  obtain ⟨μ', hμ'⟩ := hyT
  have hμo : orderOf μ = 2 ^ i := by
    rw [← orderOf_injective (tSU hF) (tSU_injective hF) μ]; exact hxo
  have hμ'o : orderOf μ' = 2 ^ i := by
    rw [← orderOf_injective (tSU hF) (tSU_injective hF) μ', hμ', hyo]
  obtain ⟨a1, a2, a3⟩ := tSU_regular_of_orderOf hF hq4 hμo hi
  obtain ⟨b1, b2, b3⟩ := tSU_regular_of_orderOf hF hq4 hμ'o hi
  have hcx := centralizer_tSU_of_regular hF a1 a2 a3
  have hcy := centralizer_tSU_of_regular hF b1 b2 b3
  refine mem_normA0_of_forall_conj_mem_range hF hω hq3 fun g hg => ?_
  have hg' : g ∈ Subgroup.centralizer ({tSU hF μ} : Set (SU (unitaryInvolution F p f) 3)) :=
    hcx ▸ hg
  rw [← hcy, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hgc := Subgroup.mem_centralizer_iff.1 hg' (tSU hF μ) rfl
  rw [hμ']
  calc n * tSU hF μ * n⁻¹ * (n * g * n⁻¹) = n * (tSU hF μ * g) * n⁻¹ := by group
    _ = n * (g * tSU hF μ) * n⁻¹ := by rw [hgc]
    _ = n * g * n⁻¹ * (n * tSU hF μ * n⁻¹) := by group

theorem three_le_padic_sq_sub_one {q : ℕ} (hq4 : q % 4 = 1) (hq2 : 2 ≤ q) :
    3 ≤ padicValNat 2 (q ^ 2 - 1) := by
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  rw [u3two_padic_sq_sub_one q hodd (by omega), u3two_padic_add_one_of_mod4_one _ hq4]
  have h4 : 2 ^ 2 ∣ q - 1 := by omega
  have := (padicValNat_dvd_iff_le (by omega)).1 h4
  omega

end Key

section Existence

theorem two_le_prime_pow_of_card' (hF : Nat.card F = (p ^ f) ^ 2) : 2 ≤ p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have h2 : p ^ f ≤ 1 := by omega
  have h3 : (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
  omega

theorem exists_unit_orderOf_padic (hF : Nat.card F = (p ^ f) ^ 2) :
    ∃ μ : Fˣ, orderOf μ = 2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hq2 := two_le_prime_pow_of_card' hF
  have hgo : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  have hpos : 0 < (p ^ f) ^ 2 - 1 := by
    have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  obtain ⟨k, hk⟩ : 2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) ∣ (p ^ f) ^ 2 - 1 := pow_padicValNat_dvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  refine ⟨g ^ k, ?_⟩
  rw [orderOf_pow_of_dvd hk0 (by rw [hgo]; exact Dvd.intro_left _ hk.symm), hgo]
  conv_lhs => rw [hk]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)

theorem exists_isSylowOf_normalizer_le (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ}
    (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 1) :
    ∃ S₀ : Subgroup (SU (unitaryInvolution F p f) 3), IsSylowOf 2 S₀ ⊤ ∧ S₀ ≤ normA0 hF ω ∧
      Subgroup.normalizer (S₀ : Set (SU (unitaryInvolution F p f) 3)) ≤ normA0 hF ω := by
  have hq2 := two_le_prime_pow_of_card' hF
  have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  obtain ⟨μ₀, hμ₀⟩ := exists_unit_orderOf_padic hF
  have hm3 : 3 ≤ padicValNat 2 ((p ^ f) ^ 2 - 1) := three_le_padic_sq_sub_one hq4 hq2
  have hxo : orderOf (tSU hF μ₀) = 2 ^ padicValNat 2 ((p ^ f) ^ 2 - 1) := by
    rw [orderOf_injective (tSU hF) (tSU_injective hF) μ₀]; exact hμ₀
  have hxN : tSU hF μ₀ ∈ normA0 hF ω := range_tSU_le_normA0 hF hω hq3 ⟨μ₀, rfl⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers (tSU hF μ₀)) :=
    IsPGroup.of_card (n := padicValNat 2 ((p ^ f) ^ 2 - 1)) (by rw [Nat.card_zpowers, hxo])
  obtain ⟨S₀, hxS₀, hS₀⟩ := exists_isSylowOf_two_ge hxp (Subgroup.zpowers_le.2 hxN)
  have hS₀N : S₀ ≤ normA0 hF ω := hS₀.le
  refine ⟨S₀, ?_, hS₀N, ?_⟩
  · have hcard := hS₀.card_eq
    rw [card_normA0 hF hω hq3] at hcard
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, card_SU3 hF, hcard]
    congr 1
    have hsub : (p ^ f) ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    have hq1 : 1 < p ^ f := by omega
    have hv2 : padicValNat 2 (p ^ f + 1) = 1 := u3two_padic_add_one_of_mod4_one _ hq4
    have hm' : padicValNat 2 ((p ^ f) ^ 2 - 1) =
        padicValNat 2 (p ^ f - 1) + padicValNat 2 (p ^ f + 1) :=
      u3two_padic_sq_sub_one _ hodd hq1
    rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two,
      padicValNat.mul (by norm_num) hsub, padicValNat_self, u3two_padic_order _ hodd hq1]
    omega
  · exact normalizer_le_normA0 hF hω hq3 hq4 hS₀N hS₀.isPGroup
      (hxS₀ (Subgroup.mem_zpowers _)) ⟨μ₀, rfl⟩ hxo hm3

end Existence

section Final

theorem mem_normalizer_of_conj {Ω : Type*} [Group Ω] {S₀ S : Subgroup Ω} {k n : Ω}
    (hk : ∀ y, y ∈ S ↔ k⁻¹ * y * k ∈ S₀) (hn : n ∈ Subgroup.normalizer (S : Set Ω)) :
    k⁻¹ * n * k ∈ Subgroup.normalizer (S₀ : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  have e1 : h ∈ S₀ ↔ k * h * k⁻¹ ∈ S := by
    rw [hk]
    have : k⁻¹ * (k * h * k⁻¹) * k = h := by group
    rw [this]
  have e2 : n * (k * h * k⁻¹) * n⁻¹ ∈ S ↔ k⁻¹ * n * k * h * (k⁻¹ * n * k)⁻¹ ∈ S₀ := by
    rw [hk]
    have : k⁻¹ * (n * (k * h * k⁻¹) * n⁻¹) * k = k⁻¹ * n * k * h * (k⁻¹ * n * k)⁻¹ := by group
    rw [this]
  rw [e1, hn (k * h * k⁻¹), e2]

theorem normalizer_le_of_isSylowOf_mod4 (hF : Nat.card F = (p ^ f) ^ 2) {ω : Fˣ}
    (hω : orderOf ω = 3) (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 1)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    {S : Subgroup (SU (unitaryInvolution F p f) 3)} (hS : IsSylowOf 2 S ⊤) (hSW : S ≤ W) :
    Subgroup.normalizer (S : Set (SU (unitaryInvolution F p f) 3)) ≤ W := by
  obtain ⟨S₀, hS₀top, hS₀N, hS₀norm⟩ := exists_isSylowOf_normalizer_le hF hω hq3 hq4
  have hS₀W : IsSylowOf 2 S₀ W := hS₀top.of_le (hS₀N.trans hNW) le_top
  have hSW' : IsSylowOf 2 S W := hS.of_le hSW le_top
  obtain ⟨k, hkW, hk⟩ := exists_conj_of_isSylowOf_two hS₀W hSW'
  intro n hn
  have hn' := mem_normalizer_of_conj hk hn
  have hnW : k⁻¹ * n * k ∈ W := hNW (hS₀norm hn')
  have : n = k * (k⁻¹ * n * k) * k⁻¹ := by group
  rw [this]
  exact W.mul_mem (W.mul_mem hkW hnW) (W.inv_mem hkW)

end Final

section Core

theorem f1Core_SU3_of_mod4_one (hF : Nat.card F = (p ^ f) ^ 2) (hq3 : (p ^ f) % 3 = 1)
    (hq4 : (p ^ f) % 4 = 1) : F1Core (SU (unitaryInvolution F p f) 3) := by
  have hq2 := two_le_prime_pow_of_card' hF
  have hF3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    have h3 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hF3
  refine f1Core_of_A0 (A₀ := Subgroup.zpowers (tSU hF ω)) ?_ ?_
  · rw [Nat.card_zpowers, orderOf_injective (tSU hF) (tSU_injective hF) ω, hω]
  · intro W Y hNW _ _ _ _ S hS hSW
    exact normalizer_le_of_isSylowOf_mod4 hF hω hq3 hq4 hNW hS hSW

end Core

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
