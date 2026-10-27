module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNFiveOrders
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHNLocal
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporInner
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMemoir
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOp
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporSieve

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Blueprint.NativeSporadic

section CentralizerBound

theorem not_pow_dvd_card_mul_card_centralizer_HN {L : Type} [Group L] [Finite L]
    (e : L ≃* Carrier .HN) {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y) :
    ∀ z : L, orderOf z = 5 →
      5 ^ (Nat.card L).factorization 5 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ^ (Nat.card L).factorization d ∣ (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  have e0 : L ≃* CFSG.Blueprint.NativeSporadic.HN := e
  have hL : Nat.card L = 273030912000000 :=
    (Nat.card_congr e0.toEquiv).trans CFSG.Sporadic.HN.card_HN
  have h5L : (Nat.card L).factorization 5 = 6 := by
    rw [Nat.card_congr e0.toEquiv]
    exact CFSG.RankThree.PartOne.KS.factorization_card_HN_five
  obtain ⟨-, -, -, -, hdY, -, -, -, -, -⟩ := coreOfData h
  have hdvd : d ∣ 273030912000000 := by
    rw [← hL]
    exact hdY.trans (Subgroup.card_subgroup_dvd_card Y)
  intro z hz h56 hd
  have h56' : 5 ^ 6 ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    rw [← h5L]
    exact h56
  have hC : Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 14 * 3 * 5 ^ 6 :=
    card_centralizer_dvd_HN_of_five_central e hz h56'
  have hN0 : (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) *
      Nat.card (Subgroup.centralizer ({z} : Set L)) ∣ 2 ^ 21 * 3 ^ 2 * 5 ^ 9 * 31 := by
    have hP : (5 ^ 3 - 1) * (5 ^ 3 - 5) * (5 ^ 3 - 5 ^ 2) = 2 ^ 7 * 3 * 5 ^ 3 * 31 := by
      norm_num
    rw [hP]
    exact (Nat.mul_dvd_mul (dvd_refl _) hC).trans (by norm_num)
  have hdiv : d ^ (Nat.card L).factorization d ∣ 2 ^ 21 * 3 ^ 2 * 5 ^ 9 * 31 := hd.trans hN0
  have hmem := mem_of_prime_dvd h.d_prime
    (qs := [(2, 14), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]) (by norm_num)
    (by norm_num; exact hdvd)
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.d_ne_two rfl
  · exact not_pow_dvd_of_factorization (q := 3) (e := 6) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact h.d_ne rfl
  · exact not_pow_dvd_of_factorization (q := 7) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 11) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv
  · exact not_pow_dvd_of_factorization (q := 19) (e := 1) (by norm_num) (Nat.card_pos.ne')
      (by rw [hL]; norm_num) (by norm_num) hdiv

end CentralizerBound

section Kill

theorem false_HN_of_data_of_op_eq_bot {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .HN)
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y)
    (hOp : ∀ R : Subgroup L, IsPGroup 5 R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥) :
    False := by
  have hfact : Fact (Nat.Prime 5) := ⟨h.prime⟩
  have e0 : L ≃* CFSG.Blueprint.NativeSporadic.HN := e
  have hHN : IsSimpleGroup (Carrier .HN) := CFSG.Sporadic.HN.isSimpleGroup_HN
  have hsimpL : IsSimpleGroup L := MulEquiv.isSimpleGroup e
  have hO : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OPrimeCoreTrivialAt 5 L :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOPrimeHolds_HN_five_of_orders
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.hnFiveOrders_holds L ⟨e0⟩
  have hO5 := gLAPPrimeCoreOf_eq_bot_of_data h hO
  obtain ⟨J, hJY, hJn, hJs, hJna, hJC⟩ :=
    exists_simple_normal_of_data h le_rfl hO5 hOp (card_center_sylow_HN e)
  have hsimpJ : IsSimpleGroup ↥J := hJs
  have hcat : CFSG.Blueprint.Catalog ↥J :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective h.kgroup J (MonoidHom.id ↥J)
      Function.surjective_id
  have hL : Nat.card L = 273030912000000 :=
    (Nat.card_congr e0.toEquiv).trans CFSG.Sporadic.HN.card_HN
  have hord : Nat.card ↥J ∣ 273030912000000 := by
    rw [← hL]
    exact Subgroup.card_subgroup_dvd_card J
  obtain ⟨hinn, h55⟩ := hn_sieve hcat hJna hord
  obtain ⟨F, hFcard, hFexp⟩ := exists_exponent_five_HN e
  obtain ⟨Q, hQY⟩ := exists_sylow_le_of_data h
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (Y := ⊤)
    (H := Q) le_top le_top hFexp (by rw [Subgroup.card_top, Sylow.card_eq_multiplicity,
      Nat.Prime.factorization_pow hfact.out, Finsupp.single_eq_same])
  have hF'exp : ∀ x ∈ F.map (MulAut.conj g).toMonoidHom, x ^ 5 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hFexp y hy, map_one]
  have hF'J : F.map (MulAut.conj g).toMonoidHom ≤ J := by
    rw [← Subgroup.closure_eq (F.map (MulAut.conj g).toMonoidHom)]
    exact closure_le_of_pow_eq_one hJY hJn hJC hinn
      (S := (F.map (MulAut.conj g).toMonoidHom : Set L)) (hg.trans hQY) hF'exp
  have hdvd : 5 ^ 5 ∣ Nat.card ↥J := by
    rw [← hFcard, ← Subgroup.card_map_of_injective (K := F)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
    exact Subgroup.card_dvd_of_le hF'J
  have hcard : Nat.card ↥J = Nat.card L := (h55 hdvd).trans hL.symm
  have hJtop : J = ⊤ := Subgroup.eq_top_of_card_eq J hcard
  rw [hJtop] at hJY
  exact h.ne_top (top_le_iff.mp hJY)

theorem sporBigNone_HN : SporBigNone .HN 5 :=
  fun _ _ _ ⟨e⟩ _ _ h => false_HN_of_data_of_op_eq_bot e h
    (op_eq_bot_of_data h (not_pow_dvd_card_mul_card_centralizer_HN e h))

end Kill

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
