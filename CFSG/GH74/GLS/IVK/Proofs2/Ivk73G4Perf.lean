module

public import CFSG.GH74.GLS.C3.Layer1.Th2Conn
public import CFSG.GH74.Generic.S45.LAltL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open scoped commutatorElement

theorem no_component_of_perfect {C : Type} [Group C] [Finite C] (hC : Group.IsPerfect C)
    {K : Subgroup C} (hK : IsComponent K) (hZ : center ↥K = ⊥)
    (hcard : Nat.card C < Nat.card ↥K * Nat.card ↥K)
    {j : ℕ} (hj : 1 ≤ j) (hdiv : Nat.card C = Nat.card ↥K * 2 ^ j) : False := by
  have hKn : K.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro c
    set K' := K.map (MulAut.conj c).toMonoidHom with hK'def
    have hK' : IsComponent K' := LocalCores.isComponent_map_mulEquiv _ hK
    rcases LocalCores.distinct_components_commute hK hK' with h | h
    · exact h.symm
    · exfalso
      have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
        commutatorElement_eq_one_iff_mul_comm.1 (by
          have : ⁅a, b⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator ha hb
          rwa [h, Subgroup.mem_bot] at this)
      have hcd : Th2.CommDisj K K' := by
        refine ⟨hcomm, ?_⟩
        rw [eq_bot_iff]
        intro x hx
        have hxZ : (⟨x, hx.1⟩ : ↥K) ∈ center ↥K := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (hcomm g g.2 x hx.2)
        rw [hZ, Subgroup.mem_bot] at hxZ
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val hxZ
      have hKK' : Nat.card ↥K' = Nat.card ↥K :=
        Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
      have h1 := hcd.card_sup (U := K) (E := K') le_rfl le_rfl
      have h2 : Nat.card ↥(K ⊔ K') ≤ Nat.card C := Subgroup.card_le_card_group _
      rw [h1, hKK'] at h2
      omega
  have hperf : Group.IsPerfect (C ⧸ K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective K)
  have hq : Nat.card (C ⧸ K) = 2 ^ j := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    rw [hdiv] at h
    exact (Nat.eq_of_mul_eq_mul_left hKpos (by rw [mul_comm] at h; linarith)).symm
  have hp : IsPGroup 2 (C ⧸ K) := IsPGroup.of_card (n := j) hq
  have hnil : Group.IsNilpotent (C ⧸ K) := hp.isNilpotent
  have hnt : Nontrivial (C ⧸ K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hq]
    exact Nat.one_lt_two_pow (by omega)
  have hsolv : Group.IsSolvable (C ⧸ K) := inferInstance
  exact Group.IsPerfect.not_isSolvable (C ⧸ K) hsolv

theorem u2_card_data {B : Type} [Group B] [Finite B] (hq : IsQuasisimple B)
    (hU : HasL2Model (B ⧸ pPrimeCore 2 B) Odd ∨
      Nonempty ((B ⧸ pPrimeCore 2 B) ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (center B))) :
    ∃ n : ℕ, (n = 2520 ∨ ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ 2 * n = q * (q ^ 2 - 1)) ∧
      Nat.card B = n * Nat.card (center B) := by
  have hnt : Nontrivial (B ⧸ pPrimeCore 2 B) := by
    rcases hU with hL | he
    · obtain ⟨hs, -⟩ := Generic.S45.LAlt.hasL2Model_data hL
      infer_instance
    · obtain ⟨e⟩ := he
      have hA : Nontrivial (alternatingGroup (Fin 7)) := by
        rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
        decide
      exact e.symm.injective.nontrivial
  have hNZ : pPrimeCore 2 B = center B := by
    apply le_antisymm
    · rcases LocalCores.quasisimple_normal_subgroups hq (inferInstance : (pPrimeCore 2 B).Normal) with h | h
      · exfalso
        have : Subsingleton (B ⧸ pPrimeCore 2 B) := by
          rw [h]
          exact (QuotientGroup.subsingleton_quotient_top)
        exact not_subsingleton _ this
      · exact h
    · exact le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hodd⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 B)
  have hcardN : Nat.card ↥(pPrimeCore 2 B) = Nat.card ↥(center B) := by rw [hNZ]
  rw [hcardN] at hcard
  refine ⟨Nat.card (B ⧸ pPrimeCore 2 B), ?_, hcard⟩
  rcases hU with hL | he
  · obtain ⟨-, -, -, q, hq5, hqo, hc, -⟩ := Generic.S45.LAlt.hasL2Model_data hL
    exact Or.inr ⟨q, hq5, hqo, by omega⟩
  · obtain ⟨e⟩ := he
    left
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide

theorem u2_arith {n z N : ℕ} (hN : N = 1920 ∨ N = 2688)
    (hn : n = 2520 ∨ ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ 2 * n = q * (q ^ 2 - 1)) (hz : Odd z)
    (hd : n * z ∣ N) : (N = 1920 ∧ n = 60 ∧ z = 1) ∨ (N = 2688 ∧ n = 168 ∧ z = 1) := by
  have hz0 : 0 < z := hz.pos
  have hnN : n ∣ N := Dvd.dvd.trans (Dvd.intro z rfl) hd
  have hNle : N ≤ 2688 := by rcases hN with rfl | rfl <;> norm_num
  have hN0 : 0 < N := by rcases hN with rfl | rfl <;> norm_num
  have hnle : n ≤ N := Nat.le_of_dvd hN0 hnN
  have hzodd : ∀ i : ℕ, z ∣ 2 ^ i → z = 1 := by
    intro i hzi
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hzi
    rcases j with _ | j
    · rfl
    · exact absurd hz (by rw [Nat.not_odd_iff_even]; exact Nat.even_pow.2 ⟨even_two, by omega⟩)
  rcases hn with rfl | ⟨q, hq5, hqo, hqn⟩
  · exfalso
    omega
  · have hq18 : q ≤ 18 := by
      by_contra hc
      push Not at hc
      have h1 : 19 * (19 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
      norm_num at h1
      omega
    obtain ⟨k, rfl⟩ := hqo
    have hk : k ≤ 8 := by omega
    have hk2 : 2 ≤ k := by omega
    interval_cases k <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hqn
    ·
      have hn60 : n = 60 := by omega
      subst hn60
      rcases hN with rfl | rfl
      · have hz32 : z ∣ 2 ^ 5 := by
          have h1 : 60 * z ∣ 60 * 32 := by simpa using hd
          simpa using Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
        exact Or.inl ⟨rfl, rfl, hzodd 5 hz32⟩
      · exfalso
        obtain ⟨c, hc⟩ := hd
        omega
    ·
      have hn168 : n = 168 := by omega
      subst hn168
      rcases hN with rfl | rfl
      · exfalso
        have h1 : (168 : ℕ) ∣ 1920 := hnN
        omega
      · have hz16 : z ∣ 2 ^ 4 := by
          have h1 : 168 * z ∣ 168 * 16 := by simpa using hd
          simpa using Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
        exact Or.inr ⟨rfl, rfl, hzodd 4 hz16⟩
    · exfalso; have h : n = 360 := by omega
      subst h; rcases hN with rfl | rfl <;> omega
    · exfalso; have h : n = 660 := by omega
      subst h; rcases hN with rfl | rfl <;> omega
    · exfalso; have h : n = 1092 := by omega
      subst h; rcases hN with rfl | rfl <;> omega
    · exfalso; have h : n = 1680 := by omega
      subst h; rcases hN with rfl | rfl <;> omega
    · exfalso; have h : n = 2448 := by omega
      subst h; rcases hN with rfl | rfl <;> omega

theorem false_of_perfect_u2_component {C : Type} [Group C] [Finite C] (hC : Group.IsPerfect C)
    (hN : Nat.card C = 1920 ∨ Nat.card C = 2688) {B : Subgroup C} (hB : IsComponent B)
    (hU : HasL2Model (↥B ⧸ pPrimeCore 2 ↥B) Odd ∨
      Nonempty ((↥B ⧸ pPrimeCore 2 ↥B) ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (center ↥B))) : False := by
  obtain ⟨n, hn, hcardB⟩ := u2_card_data hB.1 hU hodd
  have hdvd : Nat.card ↥B ∣ Nat.card C := Subgroup.card_subgroup_dvd_card B
  rw [hcardB] at hdvd
  rcases u2_arith hN hn hodd hdvd with ⟨hN1, hn60, hz1⟩ | ⟨hN2, hn168, hz1⟩
  · have hZ : center ↥B = ⊥ := Subgroup.card_eq_one.1 hz1
    refine no_component_of_perfect hC hB hZ ?_ (j := 5) (by norm_num) ?_
    · rw [hN1, hcardB, hn60, hz1]; norm_num
    · rw [hN1, hcardB, hn60, hz1]; norm_num
  · have hZ : center ↥B = ⊥ := Subgroup.card_eq_one.1 hz1
    refine no_component_of_perfect hC hB hZ ?_ (j := 4) (by norm_num) ?_
    · rw [hN2, hcardB, hn168, hz1]; norm_num
    · rw [hN2, hcardB, hn168, hz1]; norm_num

end CFSG.GH74.GLS.IVK
