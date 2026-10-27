module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Comp
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (lieSemisimpleCentLinearUnitary)
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (exists_eq_scalar_of_conjAut_eq_one
  exists_primeFormP_mulEquiv_of_isUnitaryIdx)

theorem componentsNoD4_conjAut {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k]
    [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (A : GL (Fin n) k) (hβ3 : LinearFlag.conjAut n k A ^ 3 = 1) :
    ComponentsNoD4 (LinearFlag.conjAut n k A) := by
  intro K hK
  haveI : CharP k 2 :=
    finite_field_prime_power_characteristic Nat.prime_two hf hk
  have hpk : ((3 : ℕ) : k) ≠ 0 := fun h0 => by
    have h23 := (CharP.cast_eq_zero_iff k 2 3).1 h0
    omega
  have hA3 : LinearFlag.conjAut n k (A ^ 3) = 1 := by rw [map_pow, hβ3]
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_conjAut_eq_one hn hA3
  obtain ⟨E, _, _, m, j, hm, hj, -, hcardE, hbig, g, hg, hker⟩ :=
    linear_inner_component_type_card hpk hc K hK
  have hbig' : m = 2 → 4 ≤ Fintype.card E := fun h2 => by
    rw [Fintype.card_eq_nat_card]
    exact hbig h2
  obtain ⟨φ⟩ :=
    nonempty_centralQuotient_mulEquiv (slFactorFacts_holds E m hm hbig').perfect g hg hker
  rw [← Nat.card_congr φ.toEquiv]
  exact card_centerQuot_sl_ne hm (Nat.mul_pos hf hj)
    (by rw [hcardE, hk, pow_mul]) hbig (MulEquiv.refl _)

theorem componentsNoD4_projectiveSL {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k]
    [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    {β : MulAut (LinearFlag.projectiveSL n k)}
    (hβ : β ∈ innAutDerived (LinearFlag.projectiveSL n k)) (hβ3 : β ^ 3 = 1) :
    ComponentsNoD4 β := by
  obtain ⟨A, rfl⟩ := LinearFlag.mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup hn hβ)
  exact componentsNoD4_conjAut hn hf hk A hβ3

theorem componentsNoD4_primeFormP_diag {q : TauCeti.PrimePower} {r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) (hr : 3 ≤ r + 1)
    (hp : q.p = 2)
    {β : MulAut (primeFormP h (idGram K (r + 1)))}
    (hβ : β ∈ primeFormD h (idGram K (r + 1))) (hβ3 : β ^ 3 = 1) :
    ComponentsNoD4 β := by
  intro T hT
  classical
  obtain ⟨A, c, -, hA, rfl⟩ :=
    CFSG.ComponentClassification.OuterAutomorphisms.exists_primeFormConjHom_pow_scalar_of_mem_primeFormD
      h isPrimeFormGram_idGram hr hβ hβ3
  obtain ⟨d, hd, hcase⟩ := exists_field_factor_of_component_primeFormConjHom (h := h)
    Nat.prime_three (by omega) A hA T hT
  have he : 1 ≤ q.exponent * d := Nat.mul_pos q.exponent_pos hd
  rcases hcase with ⟨F, _, _, -, hcardF, h4, g, hg, hk⟩ |
      ⟨E, _, _, m, -, hcardE, hm, hne, g, hg, hk⟩ | ⟨E, _, _, m, -, hcardE, hm, h4, g, hg, hk⟩
  · obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv
      (slFactorFacts_holds F 2 le_rfl fun _ => h4).perfect g hg hk
    rw [← Nat.card_congr φ.toEquiv]
    exact card_centerQuot_sl_ne le_rfl he (by rw [Nat.card_eq_fintype_card, hcardF, hp])
      (fun _ => by rw [Nat.card_eq_fintype_card]; exact h4) (MulEquiv.refl _)
  · obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv
      (suFactorFacts_holds E m _ hcardE hm hne).perfect g hg hk
    rw [← Nat.card_congr φ.toEquiv]
    exact card_centerQuot_su_ne hm he (by rw [hp]) hne
      (by rw [Nat.card_eq_fintype_card, hcardE]) (MulEquiv.refl _)
  · obtain ⟨φ⟩ := nonempty_centralQuotient_mulEquiv
      (slFactorFacts_holds E m hm fun _ => h4).perfect g hg hk
    rw [← Nat.card_congr φ.toEquiv]
    exact card_centerQuot_sl_ne (k := 2 * (q.exponent * d)) hm (by omega)
      (by rw [Nat.card_eq_fintype_card, hcardE, hp])
      (fun _ => by rw [Nat.card_eq_fintype_card]; exact h4) (MulEquiv.refl _)

theorem componentsNoD4_primeFormP {q : TauCeti.PrimePower} {r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData q.p q.exponent K) (hr : 3 ≤ r + 1)
    (hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2)) (hp : q.p = 2)
    {β : MulAut (primeFormP h (idGram K (r + 1)))}
    (hβ : β ∈ innAutDerived (primeFormP h (idGram K (r + 1)))) (hβ3 : β ^ 3 = 1) :
    ComponentsNoD4 β := by
  exact componentsNoD4_primeFormP_diag h hr hp
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_primeFormD_of_mem_innAutDerived
      h isPrimeFormGram_idGram hr hq hβ) hβ3

theorem triD4NoA_holds : TriD4NoA := by
  rintro S _ _ hS hnc ⟨d, hv⟩ ⟨n, q, rfl⟩ hc hf ⟨e⟩ α _ hα hα3 hα1 - - - J hJ hT -
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hk : Nat.card (GaloisField q.p q.exponent) = 2 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
    exact hf
  have hn : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  let e' : S ≃* LinearFlag.projectiveSL (n + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) _))
  exact (false_of_componentsNoD4 (lieSemisimpleCentLinearUnitary S hS hnc ⟨_, hv⟩ rfl ⟨e⟩ 3
    Nat.prime_three (by norm_num) (fun h3 => absurd (h3.trans hc) (by norm_num)) α hα3 hα1)
    (ComponentsNoD4.of_congr e' (componentsNoD4_projectiveSL (by omega) le_rfl
      (hk.trans (pow_one 2).symm)
      ((mem_innAutDerived_congr e').2 hα) (by rw [← map_pow, hα3, map_one]))) hJ hT).elim

theorem triD4NoTwistedA_holds : TriD4NoTwistedA := by
  rintro S _ _ hS hnc d ⟨_, _, hd⟩ hc - ⟨e⟩ α _ hα hα3 hα1 - - - J hJ hT -
  obtain ⟨r, q, K, _, hU, hr, hdA, hne, ⟨eP⟩⟩ :=
    exists_primeFormP_mulEquiv_of_isUnitaryIdx (d := d) (by rw [hd]; exact trivial)
  have hp : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_twistedA r q, ← hdA]
    exact hc
  have hq : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 =>
    hne ⟨h3.1, (TauCeti.PrimePower.card_def q).trans h3.2⟩
  let e' : S ≃* primeFormP hU (idGram K (r + 1)) := e.trans eP.symm
  exact (false_of_componentsNoD4 (lieSemisimpleCentLinearUnitary S hS hnc d
    ((congrArg CFSG.Yardstones.Md42047359a2a.lieFamily hdA).trans rfl) ⟨e⟩ 3 Nat.prime_three
    (by norm_num) (fun h3 => absurd (h3.trans hc) (by norm_num)) α hα3 hα1)
    (ComponentsNoD4.of_congr e' (componentsNoD4_primeFormP hU (by omega) hq hp
      ((mem_innAutDerived_congr e').2 hα) (by rw [← map_pow, hα3, map_one]))) hJ hT).elim

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
