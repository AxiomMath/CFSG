module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalSymm
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalDatum

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem rightConjugate_inf_normalizer (A : Subgroup G) (g : G) :
    rightConjugate (rightConjugate A g ⊓ Subgroup.normalizer (A : Set G)) g⁻¹ =
      A ⊓ Subgroup.normalizer (rightConjugate A g⁻¹ : Set G) := by
  rw [AschbacherTheorem3.rightConjugate_inf, rightConjugate_rightConjugate_inv,
    AschbacherTheorem3.rightConjugate_normalizer]

omit [Finite G] in
theorem rightConjugate_inf_normalizer' (A : Subgroup G) (g : G) :
    rightConjugate (A ⊓ Subgroup.normalizer (rightConjugate A g : Set G)) g⁻¹ =
      rightConjugate A g⁻¹ ⊓ Subgroup.normalizer (A : Set G) := by
  rw [AschbacherTheorem3.rightConjugate_inf, ← AschbacherTheorem3.rightConjugate_normalizer,
    rightConjugate_rightConjugate_inv]

theorem card_sylow_rightConjugate {P Q K : Subgroup G} (hP : IsSylowOf 2 P K) (g : G)
    (hQ : IsSylowOf 2 Q (rightConjugate K g)) : Nat.card Q = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hQ.card_eq, hP.card_eq, rightConjugate_card]

theorem sylow_not_le_normalizer (hC : Counterexample G D r Abar) (hr : r = 2) (i : Fin r)
    {X P : Subgroup G} (hXH : X ≤ Subgroup.normalizer (D : Set G))
    (hXN : ¬ X ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hP : IsSylowOf 2 P X) :
    ¬ P ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hPN
  set N := Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)
  have hcard := card_eq_two_mul hC hr i hXH hXN
  have hP' : IsSylowOf 2 P (X ⊓ N) := hP.of_le (le_inf hP.le hPN) inf_le_left
  have h1 := hP.card_eq
  have h2 := hP'.card_eq
  have hpos : Nat.card (X ⊓ N : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card X).factorization 2 =
      (Nat.card (X ⊓ N : Subgroup G)).factorization 2 + 1 := by
    rw [hcard, Nat.factorization_mul two_ne_zero hpos, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, add_comm]
  rw [h2, hfac, pow_succ] at h1
  have h3 : 0 < 2 ^ (Nat.card (X ⊓ N : Subgroup G)).factorization 2 := by positivity
  omega

theorem exists_swap_core (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (a : Fin r) {T W : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G)))
    (hW : IsSylowOf 2 W (aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G)))
    (hTW : Nat.card T ≤ Nat.card W) :
    ∃ y ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
        Subgroup.normalizer (D : Set G),
      y ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) ∧
      ∃ W' : Subgroup G, IsSylowOf 2 W' (aschbacherThm5Preimage D (Abar a) ⊓
          Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G)) ∧
        ∃ s ∈ W', s ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) y ∧ s ≠ 1 ∧
          s ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set H := Subgroup.normalizer (D : Set G) with hHdef
  have hΔ' := inv_mem_deltaConjugates hloc hC hΔ
  obtain ⟨d, hdg, -⟩ := exists_sylow_datum hC hΔ' a
  have hdT : IsSylowOf 2 d.T (rightConjugate (A ⊓ Subgroup.normalizer
      (rightConjugate A g : Set G)) g⁻¹) := by
    rw [rightConjugate_inf_normalizer', ← hdg]
    exact d.sylowT
  have hsize : 2 ^ (Nat.card (A ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) :
      Subgroup G)).factorization 2 ≤ Nat.card d.T := by
    rw [hdg]
    have h1 : IsSylowOf 2 (rightConjugate T g⁻¹)
        (A ⊓ Subgroup.normalizer (rightConjugate A g⁻¹ : Set G)) := by
      rw [← rightConjugate_inf_normalizer]
      exact AschbacherTheorem3.isSylowOf_rightConjugate hT g⁻¹
    rw [← h1.card_eq, rightConjugate_card, card_sylow_rightConjugate hW g⁻¹ hdT]
    exact hTW
  obtain ⟨x, hxA, hxN, heven, -⟩ := hloc.lemma_6_8 hC d hsize
  rw [hdg] at hxN
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have htT : (t : G) ∈ d.T := (Subgroup.mem_inf.mp t.2).1
  have htTx : (t : G) ∈ rightConjugate d.T x := (Subgroup.mem_inf.mp t.2).2
  have htA : (t : G) ∈ rightConjugate A g⁻¹ := by
    have := d.sylowT.le htT
    rw [hdg] at this
    exact this.1
  have htAx : (t : G) ∈ rightConjugate (rightConjugate A g⁻¹) x := by
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate
      (d.sylowT.le.trans inf_le_left) x htTx
    rwa [hdg] at h1
  have ht2 : (t : G) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at ht
    rw [← ht]
    exact pow_orderOf_eq_one _
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hsA : g⁻¹ * t * g ∈ A := by
    rw [mem_rightConjugate_iff] at htA
    simpa using htA
  have hsAy : g⁻¹ * t * g ∈ rightConjugate A (g⁻¹ * x * g) := by
    rw [rightConjugate_mul, mem_rightConjugate_iff] at htAx
    rw [mem_rightConjugate_iff]
    have heq : g⁻¹ * x * g * (g⁻¹ * ↑t * g) * (g⁻¹ * x * g)⁻¹ =
        g⁻¹ * x * ↑t * (g⁻¹ * x)⁻¹ := by group
    rw [heq]
    exact htAx
  have hs1 : g⁻¹ * (t : G) * g ≠ 1 := by
    intro h1
    apply ht1
    calc (t : G) = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hs2 : (g⁻¹ * (t : G) * g) ^ 2 = 1 := by
    rw [show g⁻¹ * (t : G) * g = g⁻¹ * t * g⁻¹⁻¹ by simp, conj_pow, ht2]
    group
  have hW' : IsSylowOf 2 (rightConjugate d.T g) (A ⊓ Subgroup.normalizer
      (rightConjugate A g : Set G)) := by
    have h1 := AschbacherTheorem3.isSylowOf_rightConjugate hdT g
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h1
  refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_, rightConjugate d.T g, hW',
    g⁻¹ * t * g, AschbacherTheorem3.conj_mem_rightConjugate htT g, hsAy, hs1, hs2⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hxA
  · by_contra hyH
    exact hs1 (eq_one_of_mem_inf_conj hC hyH ⟨1, by rw [pow_one, hs2]⟩ hsA hsAy)
  · intro hyN
    apply hxN
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
    simpa [mul_assoc] using hyN

theorem exists_not_normalizer_of_card_le (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (a : Fin r) {T W : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G)))
    (hW : IsSylowOf 2 W (aschbacherThm5Preimage D (Abar a) ⊓
      Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) g : Set G)))
    (hTW : Nat.card T ≤ Nat.card W) :
    ∃ y ∈ rightConjugate (aschbacherThm5Preimage D (Abar a)) g ⊓
        Subgroup.normalizer (D : Set G),
      y ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) := by
  obtain ⟨y, hy, hyN, -⟩ := exists_swap_core hloc hC hΔ a hT hW hTW
  exact ⟨y, hy, hyN⟩

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
