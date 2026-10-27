module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporB31
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBCentral
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBLocal
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporFrob
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporKill
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporLyLocal
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMemoir
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOp
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporSieveB

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Assembly

private theorem not_pow_dvd_of_mem_primes_B {L : Type} [Group L] [Finite L] {d : ℕ}
    (hd2 : d ≠ 2) (hd5 : d ≠ 5) (hd31 : d ≠ 31)
    (hL : Nat.card L = 4154781481226426191177580544000000)
    (hdiv : d ^ (Nat.card L).factorization d ∣ 2 ^ 48 * 3 ^ 5 * 5 ^ 9 * 31)
    (hmem : d ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 47]) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hd2 rfl
  · exact not_pow_dvd_of_factorization (q := 3) (e := 13) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact hd5 rfl
  · exact not_pow_dvd_of_factorization (q := 7) (e := 2) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 11) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 13) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 17) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 19) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 23) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact hd31 rfl
  · exact not_pow_dvd_of_factorization (q := 47) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv

section CardB

private theorem card_of_mulEquiv_B {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) :
    Nat.card L = 4154781481226426191177580544000000 := by
  rw [Nat.card_congr e.toEquiv]
  change Nat.card CFSG.Blueprint.NativeSporadic.B =
    4154781481226426191177580544000000
  rw [CFSG.Monster.Existence.card_nativeB, CFSG.Open.monsterBabyOrder]
  norm_num

private theorem factorization_five_of_mulEquiv_B {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) : (Nat.card L).factorization 5 = 6 := by
  rw [Nat.card_congr e.toEquiv]
  change (Nat.card CFSG.Blueprint.NativeSporadic.B).factorization 5 = 6
  exact CFSG.RankThree.Native.factorization_card_B_five

private theorem not_pow_dvd_card_mul_card_centralizer_B {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hR2 : ∀ (L : Type) [Group L] [Finite L], CFSG.SectionRank.IsKGroupCat L →
      L ≃* Carrier .B → ∀ z : L, orderOf z = 5 →
        5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6)
    (hd31 : d ≠ 31) :
    ∀ z : L, orderOf z = 5 →
      5 ^ (Nat.card L).factorization 5 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ^ (Nat.card L).factorization d ∣ (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  have hL := card_of_mulEquiv_B e
  have h5L := factorization_five_of_mulEquiv_B e
  obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
  have hdvd : d ∣ 4154781481226426191177580544000000 := by
    rw [← hL]
    exact hdY.trans (Subgroup.card_subgroup_dvd_card Y)
  intro z hz h56 hd
  have h56' : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    rw [← h5L]
    exact h56
  have hC : Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6 :=
    hR2 L h.kgroup e z hz h56'
  have hN0 : (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) *
      Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 48 * 3 ^ 5 * 5 ^ 9 * 31 := by
    have hP : (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) = 2 ^ 7 * 3 * 5 ^ 3 * 31 := by
      norm_num
    rw [hP]
    exact (Nat.mul_dvd_mul (dvd_refl _) hC).trans (by norm_num)
  have hdiv : d ^ (Nat.card L).factorization d ∣ 2 ^ 48 * 3 ^ 5 * 5 ^ 9 * 31 :=
    hd.trans hN0
  have hprod : ([(2, 41), (3, 13), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1),
      (23, 1), (31, 1), (47, 1)].map fun x => x.1 ^ x.2).prod =
      4154781481226426191177580544000000 := by
    norm_num
  have hmem := mem_of_prime_dvd h.d_prime (qs := [(2, 41), (3, 13), (5, 6), (7, 2), (11, 1),
      (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (47, 1)]) (by norm_num) (by
        rw [hprod]
        exact hdvd)
  exact not_pow_dvd_of_mem_primes_B h.d_ne_two h.d_ne hd31 hL hdiv hmem

private theorem not_dvd_card_mul_card_centralizer_B_of_d_eq_31 {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hR2 : ∀ (L : Type) [Group L] [Finite L], CFSG.SectionRank.IsKGroupCat L →
      L ≃* Carrier .B → ∀ z : L, orderOf z = 5 →
        5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6)
    (hd : d = 31) :
    ∀ z : L, orderOf z = 5 →
      5 ^ (Nat.card L).factorization 5 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ∣ (5 ^ 2 - 1) * (5 ^ 2 - 5) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  subst hd
  have h5L := factorization_five_of_mulEquiv_B e
  intro z hz h56 h31dvd
  have h56' : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    rw [← h5L]
    exact h56
  have hC : Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6 :=
    hR2 L h.kgroup e z hz h56'
  have hP : (5 ^ 2 - 1) * (5 ^ 2 - 5) = 2 ^ 5 * 3 * 5 := by norm_num
  have hdiv : (5 ^ 2 - 1) * (5 ^ 2 - 5) * Nat.card (Subgroup.centralizer ({z} : Set L)) ∣
      2 ^ 46 * 3 ^ 5 * 5 ^ 7 := by
    rw [hP]
    exact (Nat.mul_dvd_mul (dvd_refl _) hC).trans (by norm_num)
  exact absurd (h31dvd.trans hdiv) (by norm_num)

private theorem op_eq_bot_of_data_B {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hR2 : ∀ (L : Type) [Group L] [Finite L], CFSG.SectionRank.IsKGroupCat L →
      L ≃* Carrier .B → ∀ z : L, orderOf z = 5 →
        5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6)
    (h31 : ∀ (L : Type) [Group L], L ≃* Carrier .B →
      ∃ (a b : L) (k : ℕ), orderOf a = 31 ∧ b * a * b⁻¹ = a ^ k ∧
        ∀ j < 3, ¬ k ≡ 5 ^ j [MOD 31]) :
    ∀ R : Subgroup L, IsPGroup 5 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥ := by
  by_cases hd31 : d = 31
  · subst hd31
    exact op_eq_bot_of_data_of_conj_pow h
      (not_dvd_card_mul_card_centralizer_B_of_d_eq_31 e h hR2 rfl) (h31 L e)
  · exact op_eq_bot_of_data h
      (not_pow_dvd_card_mul_card_centralizer_B e h hR2 hd31)

end CardB

section ExponentB

private theorem five_pow_dvd_card_simple_of_data {L : Type} [Group L] [Finite L]
    {d : ℕ} {Y J : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hJY : J ≤ Y) (hJn : (J.subgroupOf Y).Normal)
    (hJC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥)
    (hinn : ∀ α : MulAut ↥J, α ^ 5 = 1 → α ∈ inner ↥J)
    (e : L ≃* Carrier .B) :
    5 ^ 5 ∣ Nat.card ↥J := by
  obtain ⟨F, hFcard, hFexp⟩ := exists_exponent_five_B e
  obtain ⟨Q, hQY⟩ := exists_sylow_le_of_data h
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (Y := ⊤)
    (H := Q) le_top le_top hFexp (by rw [Subgroup.card_top, Sylow.card_eq_multiplicity,
      Nat.Prime.factorization_pow (Fact.out : Nat.Prime 5), Finsupp.single_eq_same])
  have hF'exp : ∀ x ∈ F.map (MulAut.conj g).toMonoidHom, x ^ 5 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hFexp y hy, map_one]
  have hF'J : F.map (MulAut.conj g).toMonoidHom ≤ J := by
    rw [← Subgroup.closure_eq (F.map (MulAut.conj g).toMonoidHom)]
    exact closure_le_of_pow_eq_one hJY hJn hJC hinn
      (S := (F.map (MulAut.conj g).toMonoidHom : Set L)) (hg.trans hQY) hF'exp
  rw [← hFcard, ← Subgroup.card_map_of_injective (K := F)
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact Subgroup.card_dvd_of_le hF'J

end ExponentB

private theorem false_B_of_classical_lieModel {L : Type} [Group L] [Finite L]
    {d : ℕ} {Y J : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hm : LieModel ↥J .PSL 4 5 1 ∨ LieModel ↥J .PSU 4 5 1 ∨
      LieModel ↥J .PSL 3 5 2) : False := by
  rcases hm with hm | hm | hm
  · have hsc := hm.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
    obtain ⟨-, -, hcases⟩ :=
      CFSG.SectionRank.classical_model_rank (p := 5) (by norm_num) hsc
    rcases hcases with ⟨-, hr | hr | hr⟩ | ⟨hr, -⟩ | ⟨hr, -⟩ | hr
    · exact absurd hr.1 (by norm_num)
    · exact absurd hr.1 (by norm_num)
    · exact false_of_four_le_pRank_of_data h J hr
    · cases hr
    · cases hr
    · exact false_of_four_le_pRank_of_data h J hr
  · have hsc := hm.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
    obtain ⟨-, -, hcases⟩ :=
      CFSG.SectionRank.classical_model_rank (p := 5) (by norm_num) hsc
    rcases hcases with ⟨hr, -⟩ | ⟨-, hr | hr⟩ | ⟨hr, -⟩ | hr
    · cases hr
    · exact absurd hr.1 (by norm_num)
    · exact false_of_four_le_pRank_of_data h J hr
    · cases hr
    · exact false_of_four_le_pRank_of_data h J hr
  · have hsc := hm.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0)
    obtain ⟨-, -, hcases⟩ :=
      CFSG.SectionRank.classical_model_rank (p := 5) (by norm_num) hsc
    rcases hcases with ⟨-, hr | hr | hr⟩ | ⟨hr, -⟩ | ⟨hr, -⟩ | hr
    · exact absurd hr.1 (by norm_num)
    · exact false_of_four_le_pRank_of_data h J (by simpa using hr.2)
    · exact false_of_four_le_pRank_of_data h J hr
    · cases hr
    · cases hr
    · exact false_of_four_le_pRank_of_data h J hr

section G2B

private theorem false_B_of_G2_case {L : Type} [Group L] [Finite L]
    {d : ℕ} {Y J : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hJY : J ≤ Y) (hJn : (J.subgroupOf Y).Normal)
    (hJC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥)
    (hJcard : Nat.card ↥J = 5859000000)
    (hmodel : LieModel ↥J .G2 0 5 1)
    (hL : Nat.card L = 4154781481226426191177580544000000) : False := by
  have hYJ : Y ≤ J :=
    le_of_forall_mem_inner hJY hJn hJC fun α =>
      mem_inner_of_chevalleyExceptionalModel_G2 (by norm_num) (by norm_num)
        (LieModel.chevalleyExceptionalModel hmodel (by decide)) α
  have hYeq : Y = J := le_antisymm hYJ hJY
  have hYcard : Nat.card Y = 5859000000 := by rw [hYeq, hJcard]
  obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
  have hidx : Y.index = 709128090327091003785216 := by
    rw [Subgroup.index_eq_card_div, hL, hYcard]
  have hidxmod := index_modEq_one_of_data h
  rw [hidx] at hidxmod
  have hmem := mem_of_prime_dvd h.d_prime
    (qs := [(2, 6), (3, 3), (5, 6), (7, 1), (31, 1)]) (by norm_num)
    (by
      have hprod : ([(2, 6), (3, 3), (5, 6), (7, 1), (31, 1)].map
          fun x => x.1 ^ x.2).prod = 5859000000 := by norm_num
      rw [hprod, ← hYcard]
      exact hdY)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact h.d_ne_two rfl
  · norm_num at hidxmod
  · exact h.d_ne rfl
  · norm_num at hidxmod
  · norm_num at hidxmod

end G2B

private theorem false_B_of_HN_case_one {L : Type} [Group L] [Finite L]
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hYcard : Nat.card Y = 273030912000000) (hdY : d ∣ Nat.card Y)
    (hidxmod : Y.index ≡ 1 [MOD d])
    (hL : Nat.card L = 4154781481226426191177580544000000) : False := by
  have hidx : Y.index = 15217256723027853312 := by
    rw [Subgroup.index_eq_card_div, hL, hYcard]
  rw [hidx] at hidxmod
  have hmem := mem_of_prime_dvd h.d_prime
    (qs := [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]) (by norm_num)
    (by
      have hprod : ([(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)].map
          fun x => x.1 ^ x.2).prod = 273030912000000 := by norm_num
      rw [hprod, ← hYcard]
      exact hdY)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.d_ne_two rfl
  · norm_num at hidxmod
  · exact h.d_ne rfl
  · norm_num at hidxmod
  · norm_num at hidxmod
  · norm_num at hidxmod

private theorem false_B_of_HN_case_two {L : Type} [Group L] [Finite L]
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hYcard : Nat.card Y = 546061824000000) (hdY : d ∣ Nat.card Y)
    (hidxmod : Y.index ≡ 1 [MOD d])
    (hL : Nat.card L = 4154781481226426191177580544000000) : False := by
  have hidx : Y.index = 7608628361513926656 := by
    rw [Subgroup.index_eq_card_div, hL, hYcard]
  rw [hidx] at hidxmod
  have hmem := mem_of_prime_dvd h.d_prime
    (qs := [(2, 15), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]) (by norm_num)
    (by
      have hprod : ([(2, 15), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)].map
          fun x => x.1 ^ x.2).prod = 546061824000000 := by norm_num
      rw [hprod, ← hYcard]
      exact hdY)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.d_ne_two rfl
  · norm_num at hidxmod
  · exact h.d_ne rfl
  · norm_num at hidxmod
  · norm_num at hidxmod
  · norm_num at hidxmod

section HNB

private theorem false_B_of_HN_case {L : Type} [Group L] [Finite L]
    {d : ℕ} {Y J : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hJY : J ≤ Y) (hJn : (J.subgroupOf Y).Normal)
    (hJC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥)
    (eJ : ↥J ≃* Carrier .HN)
    (hL : Nat.card L = 4154781481226426191177580544000000) : False := by
  have hHNcard : Nat.card ↥J = 273030912000000 :=
    (Nat.card_congr eJ.toEquiv).trans CFSG.Sporadic.HN.card_HN
  have haut : Nat.card (MulAut ↥J) = 546061824000000 :=
    (Nat.card_congr (MulAut.congr eJ).toEquiv).trans
      CFSG.Sporadic.HNSchreier.card_aut_HN
  have hYdvd : Nat.card Y ∣ 546061824000000 := by
    rw [← haut]
    exact card_dvd_card_mulAut_of_centralizer_inf_eq_bot hJY hJn hJC
  have hHNdvd : 273030912000000 ∣ Nat.card Y := by
    rw [← hHNcard]
    exact Subgroup.card_dvd_of_le hJY
  obtain ⟨k, hk⟩ := hHNdvd
  have hk2 : k ∣ 2 := by
    have h := hYdvd
    rw [hk] at h
    rw [show 546061824000000 = 273030912000000 * 2 by norm_num] at h
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 273030912000000)).mp h
  obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
  have hidxmod := index_modEq_one_of_data h
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with hk1 | hk2
  · have hYcard : Nat.card Y = 273030912000000 := by rw [hk, hk1, mul_one]
    exact false_B_of_HN_case_one h hYcard hdY hidxmod hL
  · have hYcard : Nat.card Y = 546061824000000 := by
      rw [hk, hk2]
    exact false_B_of_HN_case_two h hYcard hdY hidxmod hL

end HNB

section KillB

private theorem false_B_of_data_of_op_eq_bot {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hOp : ∀ R : Subgroup L, IsPGroup 5 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥) :
    False := by
  have hL := card_of_mulEquiv_B e
  have hO : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 5 L :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt.of_mulEquiv e
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_B_five
  have hO5 : CFSG.Open.GLAPPrimeCoreOf 5 Y = ⊥ := gLAPPrimeCoreOf_eq_bot_of_data h hO
  obtain ⟨J, hJY, hJn, hJs, hJna, hJC⟩ :=
    exists_simple_normal_of_data h le_rfl hO5 hOp (card_center_sylow_B e)
  have hcat : Catalog ↥J :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroup J (MonoidHom.id ↥J)
      Function.surjective_id
  have hord : Nat.card ↥J ∣ 4154781481226426191177580544000000 := by
    rw [← hL]
    exact Subgroup.card_subgroup_dvd_card J
  rcases b_sieve hcat hJna hord with h5' | ⟨hinn, h55⟩
  · exact false_of_not_dvd_of_gLAPPrimeCoreOf_eq_bot Nat.prime_five hO5 hJY hJn h5' hJna
  · have hdvd : 5 ^ 5 ∣ Nat.card ↥J :=
      five_pow_dvd_card_simple_of_data h hJY hJn hJC hinn e
    rcases h55 hdvd with hcard | hHN | hmPSL4 | hmPSU4 | hmPSL3 | ⟨hcard, hmodel⟩
    · have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J (hcard.trans hL.symm)
      rw [hJtop] at hJY
      exact h.ne_top (top_le_iff.mp hJY)
    · obtain ⟨eJ⟩ := hHN
      exact false_B_of_HN_case h hJY hJn hJC eJ hL
    · exact false_B_of_classical_lieModel h (Or.inl hmPSL4)
    · exact false_B_of_classical_lieModel h (Or.inr (Or.inl hmPSU4))
    · exact false_B_of_classical_lieModel h (Or.inr (Or.inr hmPSL3))
    · exact false_B_of_G2_case h hJY hJn hJC hcard hmodel hL

private theorem false_B_of_data {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .B) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hR2 : ∀ (L : Type) [Group L] [Finite L], CFSG.SectionRank.IsKGroupCat L →
      L ≃* Carrier .B → ∀ z : L, orderOf z = 5 →
        5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6)
    (h31 : ∀ (L : Type) [Group L], L ≃* Carrier .B →
      ∃ (a b : L) (k : ℕ), orderOf a = 31 ∧ b * a * b⁻¹ = a ^ k ∧
        ∀ j < 3, ¬ k ≡ 5 ^ j [MOD 31]) : False :=
  false_B_of_data_of_op_eq_bot e h (op_eq_bot_of_data_B e h hR2 h31)

theorem sporBigNone_B_of
    (hR2 : ∀ (L : Type) [Group L] [Finite L], CFSG.SectionRank.IsKGroupCat L →
      L ≃* NativeSporadic.Carrier .B → ∀ z : L, orderOf z = 5 →
        5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
          Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 41 * 3 ^ 4 * 5 ^ 6)
    (h31 : ∀ (L : Type) [Group L], L ≃* NativeSporadic.Carrier .B →
      ∃ (a b : L) (k : ℕ), orderOf a = 31 ∧ b * a * b⁻¹ = a ^ k ∧
        ∀ j < 3, ¬ k ≡ 5 ^ j [MOD 31]) :
    SporBigNone .B 5 := by
  intro L _ _ ⟨e⟩ d Y h
  exact false_B_of_data e h hR2 h31

section Final

theorem sporBigNone_B : SporBigNone .B 5 :=
  sporBigNone_B_of (fun _ _ _ hK e _ hz h56 => card_centralizer_dvd_B_of_five_central hK e hz h56)
    fun _ _ e => exists_conj_pow_thirtyOne_B e

end Final

end KillB

end Assembly

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
