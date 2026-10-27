module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256p
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256o2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxExcTwisted
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256p

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256m (IsGF4Type IsGF4Comp GF4CompsOn)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

section Unitary

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {K : Type} [Field K]

theorem two_pow_two_mul_eq_four_pow (d : ℕ) : 2 ^ (2 * d) = 4 ^ d := by
  rw [pow_mul]
  norm_num

theorem coprime_card_normOneScalars_four {n : ℕ} (h : UnitaryFieldData 2 2 K) :
    Nat.Coprime (Nat.card (normOneScalars h (gramSU h (idGram K n)) n)) 2 := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h2 => ?_)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, hc, -, hzc⟩ := z.2
  have hc5 : c ^ 5 = 1 := by
    apply Units.ext
    have h1 : (c : K) * (c : K) ^ (2 ^ 2) = 1 := hc
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    calc (c : K) ^ 5 = (c : K) * (c : K) ^ (2 ^ 2) := by ring
      _ = 1 := h1
  have hz5 : z ^ 5 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show ((z : gramSU h (idGram K n)) : GL (Fin n) K) ^ 5 = 1
    rw [hzc, ← map_pow, hc5, map_one]
  have hz2 : z ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hz] at h1
  have hz1 : z = 1 := by
    calc z = z ^ 5 * (z ^ 2)⁻¹ * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz5, hz2]; group
  rw [hz1, orderOf_one] at hz
  norm_num at hz

theorem twoElement_mem_glaLayer_primeFormConjHom {n : ℕ} (h : UnitaryFieldData 2 2 K)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {s : primeFormP h (idGram K n)} (hs : s ∈ fixSubgroup (primeFormConjHom h (idGram K n) A))
    (hs2 : ∃ m : ℕ, s ^ 2 ^ m = 1) :
    s ∈ GLALayer (fixSubgroup (primeFormConjHom h (idGram K n) A)) := by
  classical
  haveI := h.finite
  haveI : CharP K 2 := h.charP
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hq : 2 ≤ 2 ^ 2 := by norm_num
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) with hx
  have H : UnitaryPrimaryData h.bar (idForm h n) x :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.primaryData_toLin' h A.2 Nat.prime_three
      (by norm_num) hA
  set α : MulAut ↥(gramSU h (idGram K n)) := primeFormConjSU h (idGram K n) A with hα
  let π : ↥(gramSU h (idGram K n)) →* primeFormP h (idGram K n) :=
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = normOneScalars h (gramSU h (idGram K n)) n := QuotientGroup.ker_mk' _
  haveI : Finite (LinearMap.GeneralLinearGroup K (Fin n → K)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.finite_gl_of_unitaryFieldData h
  haveI : Finite ↥(gramSU h (idGram K n)) := inferInstance
  haveI : Finite π.ker := inferInstance
  have hcop : Nat.Coprime (Nat.card π.ker) 2 := by
    rw [hker]
    exact coprime_card_normOneScalars_four h
  obtain ⟨m, hm⟩ := hs2
  obtain ⟨g, rfl, hgm⟩ := Inputs256e.exists_pow_lift π hπ hcop hm
  have hαπ : ∀ g' : ↥(gramSU h (idGram K n)), π (α g') = primeFormConjHom h (idGram K n) A (π g') :=
    fun g' => (primeFormConjHom_mk h (idGram K n) A g').symm
  have hs' : primeFormConjHom h (idGram K n) A (π g) = π g := mem_fixSubgroup.1 hs
  have hzk : g⁻¹ * α g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαπ, hs', inv_mul_cancel]
  have hcomm : Commute g (α g) := by
    have hz : Commute g (g⁻¹ * α g) := by
      rw [hker] at hzk
      exact Subgroup.mem_center_iff.1 (normOneScalars_le_center h _ n hzk) g
    have e : α g = g * (g⁻¹ * α g) := by group
    rw [e]
    exact (Commute.refl g).mul_right hz
  have hzq : (g⁻¹ * α g) ^ 2 ^ m = 1 := by
    rw [(hcomm.inv_left).mul_pow, inv_pow, hgm, ← map_pow, hgm, map_one, inv_one, one_mul]
  have hαg : α g = g := by
    have h1 := Inputs256e.eq_one_of_mem_of_coprime hcop hzk hzq
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  have hgfix : g ∈ fixSubgroup α := hαg
  set y := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n g with hy
  have hyU : y ∈ unitaryCentralizer (idForm h n) x :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU_mem_unitaryCentralizer A hx hgfix
  have hym : (⟨y, hyU.2⟩ : gl_centralizer x) ^ 2 ^ m = 1 := by
    apply Subtype.ext
    show y ^ 2 ^ m = 1
    rw [hy, ← map_pow, hgm, map_one]
  have hdet : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
      blockDetHom x (b : K[X]) ⟨y, hyU.2⟩ = 1 := by
    intro b
    haveI : Fact (Irreducible (b : K[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
    haveI : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
    have hchar : ringChar (AdjoinRoot (b : K[X])) = 2 := by
      rw [← Algebra.ringChar_eq K (AdjoinRoot (b : K[X])), hK2]
    refine Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units Nat.prime_two hchar)
      (n := m) ?_
    rw [← map_pow, hym, map_one]
  have hbad : ∀ b : primaryFactors (x : Module.End K (Fin n → K)), ¬ IsGoodBlock h x b →
      blockRestrict x (b : K[X]) ⟨y, hyU.2⟩ = 1 := by
    intro b hb
    haveI : Fact (Irreducible (b : K[X])) := ⟨irreducible_of_mem_primaryFactors b.2⟩
    haveI : Finite (AdjoinRoot (b : K[X])) := Module.finite_of_finite K
    have hchar : ringChar (AdjoinRoot (b : K[X])) = 2 := by
      rw [← Algebra.ringChar_eq K (AdjoinRoot (b : K[X])), hK2]
    have hle : primaryMultiplicity (x : Module.End K (Fin n → K)) (b : K[X]) ≤ 1 := by
      by_contra hlt
      apply hb
      refine ⟨by omega, fun _ hmem => ?_⟩
      have hdeg : 1 ≤ (b : K[X]).natDegree :=
        Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors b.2)
      have h4 : 4 ≤ 2 ^ (2 * (b : K[X]).natDegree) := by
        rw [two_pow_two_mul_eq_four_pow]
        exact Nat.le_self_pow (by omega) 4
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      omega
    have hcopgl := Inputs256e.coprime_card_gl_of_finrank_le_one
      (W := primaryComponent (x : Module.End K (Fin n → K)) (b : K[X])) Nat.prime_two hchar hle
    haveI : Finite (blockGL (x : Module.End K (Fin n → K)) (b : K[X])) :=
      Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (fun h0 => by
        rw [blockGL] at h0
        rw [h0] at hcopgl
        exact Nat.prime_two.one_lt.ne' (Nat.coprime_zero_left _ |>.1 hcopgl))).ne'
    refine Inputs256e.eq_one_of_coprime_card hcopgl (n := m) ?_
    rw [← map_pow, hym, map_one]
  have hmem := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.mem_iSup_specialBlock_of_blocks H hyU
    hdet hbad
  have hSBle : ∀ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
      specialBlock (idForm h n) x (a.1 : K[X]) ≤
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n).range := fun a g' hg' =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.mem_range_toLinSU
      (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2 hg')
  let F : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a} →
      Subgroup ↥(gramSU h (idGram K n)) :=
    fun a => (specialBlock (idForm h n) x (a.1 : K[X])).comap
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n)
  have hFmap : ∀ a, (F a).map (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n) =
      specialBlock (idForm h n) x (a.1 : K[X]) :=
    fun a => Subgroup.map_comap_eq_self (hSBle a)
  have hgF : g ∈ ⨆ a, F a := by
    have hmapsup : (⨆ a, F a).map (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n) =
        ⨆ a : {a : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a},
          specialBlock (idForm h n) x (a.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hFmap
    have hk : y ∈ (⨆ a, F a).map (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n) := by
      rw [hmapsup]
      exact hmem
    obtain ⟨g', hg', hg'y⟩ := hk
    have : g' = g := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU_injective hg'y
    rw [← this]
    exact hg'
  have hFperf : ∀ a, ⁅F a, F a⁆ = F a := by
    intro a
    have e : ↥(F a) ≃* ↥(specialBlock (idForm h n) x (a.1 : K[X])) :=
      (Subgroup.equivMapOfInjective (F a) (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU h n)
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.toLinSU_injective).trans
        (MulEquiv.subgroupCongr (hFmap a))
    have hQ := (specialBlockFacts_of_good H hq a.1 a.2).quasisimple a.2.1
    haveI : Group.IsPerfect ↥(specialBlock (idForm h n) x (a.1 : K[X])) := hQ.1
    exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hFfix : ∀ a, F a ≤ fixSubgroup α := fun a g' hg' =>
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.mem_fixSubgroup_primeFormConjSU_iff A hx g').mpr
      (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg')).2
  have hDperf : ⁅(⨆ a, F a).map π, (⨆ a, F a).map π⁆ = (⨆ a, F a).map π := by
    rw [← Subgroup.map_commutator, commutator_iSup_eq_self_of_perfect F hFperf]
  have hDle : (⨆ a, F a).map π ≤ fixSubgroup (primeFormConjHom h (idGram K n) A) := by
    rintro _ ⟨g', hg', rfl⟩
    have hg'fix : α g' = g' := iSup_le hFfix hg'
    show primeFormConjHom h (idGram K n) A (π g') = π g'
    rw [← hαπ, hg'fix]
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_primeFormConjHom h Nat.prime_three
    (by norm_num) A hA _ hDle hDperf (Subgroup.mem_map_of_mem π hgF)

end Unitary

section UnitaryMain

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {K : Type} [Field K]

theorem isGF4Comp_of_isComponentOf_primeFormConjHom {n : ℕ} (h : UnitaryFieldData 2 2 K)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {T : Subgroup (primeFormP h (idGram K n))}
    (hT : IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K n) A))) :
    IsGF4Comp (primeFormConjHom h (idGram K n) A) T := by
  obtain ⟨dd, hdd, hcase⟩ :=
    exists_field_factor_of_component_primeFormConjHom (h := h) Nat.prime_three (by norm_num) A hA T hT
  rcases hcase with
      ⟨F, hF, hFt, hcharF, hcardF, h4, g, hg, hk⟩ |
      ⟨E, hE, hEt, m, hcharE, hcardE, hm, hne, g, hg, hk⟩ |
      ⟨E, hE, hEt, m, hcharE, hcardE, hm2, h4, g, hg, hk⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
      (slFactorFacts_holds F 2 le_rfl (fun _ => h4)).perfect
    have hcat := (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.catalogueOver_sl F 2 le_rfl
      (fun _ => h4)).of_surjective hperf g hg hk
    rw [hcharF, hcardF, two_pow_two_mul_eq_four_pow] at hcat
    exact isGF4Comp_of_catalogueOver hT hdd hcat
  · letI : Field E := hE
    letI : Fintype E := hEt
    have hperf : commutator ↥(StatedSU m (2 ^ (2 * dd)) E) = ⊤ :=
      (suFactorFacts_holds E m (2 ^ (2 * dd)) hcardE hm hne).perfect
    have hcat := (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.catalogueOver_su E m (2 ^ (2 * dd)) hcardE hm
      hne).of_surjective hperf g hg hk
    rw [hcharE, two_pow_two_mul_eq_four_pow] at hcat
    exact isGF4Comp_of_catalogueOver hT hdd hcat
  · letI : Field E := hE
    letI : Fintype E := hEt
    have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤ :=
      (slFactorFacts_holds E m hm2 (fun _ => h4)).perfect
    have hcat := (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.catalogueOver_sl E m hm2
      (fun _ => h4)).of_surjective hperf g hg hk
    rw [hcharE, hcardE, two_pow_two_mul_eq_four_pow] at hcat
    exact isGF4Comp_of_catalogueOver hT (by omega) hcat

theorem gf4Gen_primeFormP {n : ℕ} (hn : 3 ≤ n) (h : UnitaryFieldData 2 2 K)
    (β : MulAut (primeFormP h (idGram K n))) (hβ : orderOf β = 3) :
    ∀ s : primeFormP h (idGram K n), β s = s → (∃ m : ℕ, s ^ 2 ^ m = 1) →
      s ∈ ⨆ (J : Subgroup (primeFormP h (idGram K n))) (_ : IsGF4Comp β J), J := by
  have hq' : ¬(n = 3 ∧ 2 ^ 2 = 2) := by norm_num
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  have hβ3 : β ^ 3 = 1 := hβ ▸ pow_orderOf_eq_one β
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq'
  have hσ : primeFormFieldFactor h hC hn hq' β = 1 := by
    by_contra hσ
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hσp : orderOf (primeFormFieldFactor h hC hn hq' β) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hβ3, map_one]) hσ
    obtain ⟨h32, -⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn hq'
      Nat.prime_three (by norm_num) β hβ _ rfl hσp
    norm_num at h32
  have hβD : β ∈ (primeFormFieldFactor h hC hn hq').ker := hσ
  rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
  obtain ⟨A, hA⟩ := hβD
  have h1 : primeFormPsi h hC ⟨A ^ 3, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_pow, hA, hβ3, map_one, one_mul]
  obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
  have hA3 : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rwa [SubgroupClass.coe_pow] at hc
  subst hA
  intro s hs hs2
  exact glaLayer_le_iSup_isGF4Comp (fun J hJ => isGF4Comp_of_isComponentOf_primeFormConjHom h A hA3 hJ)
    (twoElement_mem_glaLayer_primeFormConjHom h A hA3 hs hs2)

theorem gf4CompsOn_unitary :
    GF4CompsOn fun d => ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA r q ∧ q.card = 4 := by
  rintro S _ _ ⟨d, hv⟩ ⟨r, q, hdq, hq4⟩ ⟨eS⟩ β hβ
  simp only at hdq
  subst hdq
  have hr2 : 2 ≤ r :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eS
  obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  rw [hp2, he2] at hmodel
  obtain ⟨K, _, hU, -, ⟨eP⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel hmodel
  have hβ' : orderOf (MulAut.congr eP β) = 3 := by rw [MulEquiv.orderOf_eq, hβ]
  exact Inputs256m.gf4Gen_of_congr eP β (gf4Gen_primeFormP (n := r + 1) (by omega) hU _ hβ')

end UnitaryMain

section GF4Arith

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem pow_three_ne_four (x : ℕ) : x ^ 3 ≠ 4 := by
  intro h
  have hx : x ≤ 4 := by
    by_contra hx
    have : 5 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases x <;> norm_num at h

theorem not_subRelC_three_of_fieldSize_four {d : TauCeti.LieTypeIndex} (hd4 : fieldSize d = 4)
    (i : TauCeti.CFSGIndex) : ¬ subRelC 3 d i := by
  intro hi
  cases i with
  | lie e =>
    rcases hi with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact pow_three_ne_four _ (h.trans hd4)
    · exact pow_three_ne_four _ (h.trans hd4)
    all_goals (rw [hd4] at h; norm_num at h)
  | alternating n hn =>
    rcases hi with ⟨-, -, h | h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, -, h⟩
    all_goals (rw [hd4] at h; norm_num at h)
  | cyclic p hp => exact hi
  | sporadic s => exact hi

theorem exists_conj_eq_of_conj_eq_mulAutCongr {S G : Type*} [Group S] [Group G] (e : S ≃* G) {β : MulAut S}
    {g : G} (hg : MulAut.conj g = MulAut.congr e β) : ∃ a : S, MulAut.conj a = β := by
  refine ⟨e.symm g, (MulAut.congr e).injective ?_⟩
  rw [← hg]
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

end GF4Arith

section Statements

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def ExcCompFieldIdx : Prop :=
  LieCompIdx isTrialityIdx ∧ LieCompIdx isExcUntwistedIdx ∧ LieCompIdx isExcTwistedIdx

@[expose] def IsOrthIdxGF4 (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), (d.1 = .D r q ∨ d.1 = .twistedD r q) ∧ q.card = 4

@[expose] def IsGF4RestIdx (d : TauCeti.ValidLieTypeIndex) : Prop :=
  d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4 ∧
    (¬ ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .A r q) ∧
    (¬ ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA r q) ∧
    ¬ ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .B r q

@[expose] def TwoEltLayerOn (P : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), P d →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, orderOf β = 3 → ∀ s : S, β s = s → (∃ n : ℕ, s ^ (2 ^ n) = 1) →
      s ∈ GLALayer (fixSubgroup β)

@[expose] def GF4CompsRest2 : Prop :=
  TwoEltLayerOn IsGF4RestIdx ∧ ExcCompFieldIdx

end Statements

section FieldOfDefinition

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem lieCompIdx_all_of_excCompFieldIdx (h : ExcCompFieldIdx) : LieCompIdx fun _ => True := by
  rintro ⟨d, hv⟩ p hp hp2 hpc -
  cases d with
  | A n q => exact lieCompIdx_linear ⟨_, hv⟩ p hp hp2 hpc trivial
  | twistedA n q => exact lieCompIdx_unitary ⟨_, hv⟩ p hp hp2 hpc trivial
  | B n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | C n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | D n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | twistedD n q => exact lieCompIdx_classicalBCD ⟨_, hv⟩ p hp hp2 hpc trivial
  | E6 q => exact h.2.1 ⟨_, hv⟩ p hp hp2 hpc trivial
  | E7 q => exact h.2.1 ⟨_, hv⟩ p hp hp2 hpc trivial
  | E8 q => exact h.2.1 ⟨_, hv⟩ p hp hp2 hpc trivial
  | F4 q => exact h.2.1 ⟨_, hv⟩ p hp hp2 hpc trivial
  | G2 q => exact h.2.1 ⟨_, hv⟩ p hp hp2 hpc trivial
  | twistedE6 q => exact h.2.2 ⟨_, hv⟩ p hp hp2 hpc trivial
  | trialityD4 q => exact h.1 ⟨_, hv⟩ p hp hp2 hpc trivial
  | suzuki k => exact h.2.2 ⟨_, hv⟩ p hp hp2 hpc trivial
  | reeG2 k => exact h.2.2 ⟨_, hv⟩ p hp hp2 hpc trivial
  | reeF4 k => exact h.2.2 ⟨_, hv⟩ p hp hp2 hpc trivial
  | tits => exact h.2.2 ⟨_, hv⟩ p hp hp2 hpc trivial

theorem compIdxAt_of_excCompFieldIdx (h : ExcCompFieldIdx) {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓd : ℓ ≠ d.1.characteristic) : CompIdxAt ℓ d.1 S :=
  compIdxAt_of_mulEquiv eS.symm (lieCompIdx_all_of_excCompFieldIdx h d ℓ hℓ hℓ2 hℓd trivial)

end FieldOfDefinition

section GF4Comps

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_innAutDerived_of_orderOf_three_gf4 {S : Type} [Group S] [Finite S] {d : TauCeti.ValidLieTypeIndex}
    (hd2 : d.1.characteristic = 2) (hd4 : Inputs256c.defField d.1 = 4)
    (hnot : ¬ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (β : MulAut S) (hβ : orderOf β = 3) : β ∈ innAutDerived S := by
  rw [← mem_innAutDerived_congr eS]
  by_contra h
  have hβ3 : MulAut.congr eS β ^ 3 = 1 := by
    rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  have h3S : 3 ∣ Nat.card S :=
    Inputs256p.three_dvd_card_of_isGF4Type ⟨d, hd2, ⟨1, le_rfl, by rw [hd4]; norm_num⟩, ⟨eS⟩⟩
  have h3 : 3 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
    rwa [← Nat.card_congr eS.toEquiv]
  have hfs : fieldSize d.1 = 4 := (defField_eq_kd264FieldSize d.1).symm.trans hd4
  have hexcl : ¬ (3 = 3 ∧
      ((∃ q : TauCeti.PrimePower, (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
        (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q))) := by
    rintro ⟨-, ⟨q, hq | hq, hq8⟩ | h3D4⟩
    · rw [hq] at hfs
      exact absurd (hq8.symm.trans hfs) (by norm_num)
    · rw [hq] at hfs
      exact absurd (hq8.symm.trans hfs) (by norm_num)
    · exact hnot h3D4
  obtain ⟨J, -, -, i, -, hi⟩ := kd264OuterIdx_of_families lieOuterIdx_linear lieOuterIdx_unitary
      lieOuterIdx_classicalBCD lieOuterIdx_triality lieOuterIdx_excUntwisted lieOuterIdx_excTwisted d 3 Nat.prime_three (by norm_num)
    (by rw [hd2]; norm_num) h3 hexcl (by norm_num) (MulAut.congr eS β) hβ3 h
  exact not_subRelC_three_of_fieldSize_four hfs i hi

theorem isGF4Comp_of_compRelC {S : Type} [Group S] {β : MulAut S} {K : Subgroup S}
    (hK : IsComponentOf K (fixSubgroup β)) {d : TauCeti.LieTypeIndex} (hd2 : d.characteristic = 2)
    (hd4 : fieldSize d = 4) {i : TauCeti.CFSGIndex} (φ : ↥K ⧸ Subgroup.center ↥K ≃* i.Group)
    (hi : compRelC d i) : IsGF4Comp β K := by
  have ht : MovingAround.IsAltType 5 (↥K ⧸ Subgroup.center ↥K) ∨
      IsGF4Type (↥K ⧸ Subgroup.center ↥K) := by
    cases i with
    | lie e =>
      rcases hi with ⟨hch, ⟨j, hj, hfs⟩, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩
      · refine Or.inr ⟨e, hch.trans hd2, ⟨j, hj, ?_⟩, ⟨φ⟩⟩
        rw [defField_eq_kd264FieldSize, hfs, hd4]
      · omega
      · omega
    | alternating n hn =>
      rcases hi with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl ⟨φ⟩
      · omega
      · omega
    | cyclic p hp => exact hi.elim
    | sporadic s => exact hi.elim
  refine ⟨hK.2.1, hK.2.2, ?_, ht⟩
  rcases ht with ⟨⟨ψ⟩⟩ | hg
  · rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · exact Inputs256p.three_dvd_card_of_isGF4Type hg

theorem isGF4Comp_of_compIdxAt {S : Type} [Group S] {d : TauCeti.LieTypeIndex} (hd2 : d.characteristic = 2)
    (hd4 : Inputs256c.defField d = 4) (hc : CompIdxAt 3 d S) {β : MulAut S} (hβ : orderOf β = 3)
    (hβmem : β ∈ innAutDerived S) {K : Subgroup S} (hK : IsComponentOf K (fixSubgroup β)) :
    IsGF4Comp β K := by
  have hβ3 : β ^ 3 = 1 := by
    rw [← hβ]
    exact pow_orderOf_eq_one β
  have hβ1 : β ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hβ
    norm_num at hβ
  obtain ⟨i, ⟨φ⟩, hi⟩ := hc β hβmem hβ3 hβ1 K hK
  exact isGF4Comp_of_compRelC hK hd2 ((defField_eq_kd264FieldSize d).symm.trans hd4) φ hi

theorem catalogueOver_component_triality_outer {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq3 : q.p ≠ 3)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) {β : MulAut S} (hβ3 : β ^ 3 = 1)
    (hinn : β ∉ (MulAut.conj : S →* MulAut S).range) {K : Subgroup S}
    (hK : IsComponentOf K (fixSubgroup β)) : CatalogueOver q.p (q.p ^ q.exponent) ↥K := by
  classical
  obtain ⟨F, _, _, σ, hF, hσ, -, ⟨eF⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e' := eS.trans eF
  have hφ3 : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hφ : MulAut.congr e' β ∉ (MulAut.conj :
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 F σ.toRingHom) →*
        MulAut ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 F
          σ.toRingHom)).range := by
    rintro ⟨y, hy⟩
    exact hinn (exists_conj_eq_of_conj_eq_mulAutCongr e' hy)
  have hC := compsWith_catalogueOver_triality_outer (trialityOddA2CompsCatalogue_holds q.p q.exponent)
    hq3 q.exponent_pos hF σ hσ _ hφ3 hφ
  have hC' : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsWith
      (CatalogueOver q.p (q.p ^ q.exponent)) ↥(fixSubgroup β) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsWith.of_mulEquiv
      (isComponentProperty_catalogueOver _ _)
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e' β) hC
  have hK' : IsComponentOf (K.subgroupOf (fixSubgroup β)) ⊤ :=
    (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hK.1).1 hK
  exact (hC' _ hK').of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1)

theorem isGF4Comp_of_isComponentOf_triality_outer {S : Type} [Group S] [Finite S]
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : d.1 = .trialityD4 q)
    (hd4 : Inputs256c.defField d.1 = 4) (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group) {β : MulAut S}
    (hβ : orderOf β = 3) (hinn : β ∉ (MulAut.conj : S →* MulAut S).range) {K : Subgroup S}
    (hK : IsComponentOf K (fixSubgroup β)) : IsGF4Comp β K := by
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  have hq4 : q.card = 4 := hd4
  obtain ⟨hp2, he2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (r := 2) (s := 2)
    Nat.prime_two (by norm_num) (hq4.trans (by norm_num))
  have hβ3 : β ^ 3 = 1 := by
    rw [← hβ]
    exact pow_orderOf_eq_one β
  have hcat := catalogueOver_component_triality_outer q hv (by rw [hp2]; norm_num) eS hβ3 hinn hK
  have h4 : q.p ^ q.exponent = 4 ^ 1 := by
    rw [hp2, he2]
    norm_num
  rw [h4, hp2] at hcat
  exact isGF4Comp_of_catalogueOver hK le_rfl hcat

theorem isGF4Comp_of_isComponentOf_gf4 (hc : ExcCompFieldIdx) {S : Type} [Group S] [Finite S]
    {d : TauCeti.ValidLieTypeIndex} (hd2 : d.1.characteristic = 2) (hd4 : Inputs256c.defField d.1 = 4)
    (eS : S ≃* (TauCeti.CFSGIndex.lie d).Group) {β : MulAut S} (hβ : orderOf β = 3) {K : Subgroup S}
    (hK : IsComponentOf K (fixSubgroup β)) : IsGF4Comp β K := by
  by_cases hmem : β ∈ innAutDerived S
  · exact isGF4Comp_of_compIdxAt hd2 hd4
      (compIdxAt_of_excCompFieldIdx hc eS Nat.prime_three (by norm_num) (by rw [hd2]; norm_num)) hβ hmem hK
  · by_cases h3D4 : ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q
    · obtain ⟨q, hq⟩ := h3D4
      exact isGF4Comp_of_isComponentOf_triality_outer hq hd4 eS hβ
        (fun h => hmem (inner_le_innAutDerived S h)) hK
    · exact absurd (mem_innAutDerived_of_orderOf_three_gf4 hd2 hd4 h3D4 eS β hβ) hmem

end GF4Comps

section Residual

theorem gf4CompsOn_of_twoEltLayer {P : TauCeti.ValidLieTypeIndex → Prop} (h2 : TwoEltLayerOn P)
    (hc : ExcCompFieldIdx) (hP : ∀ d, P d → d.1.characteristic = 2 ∧ Inputs256c.defField d.1 = 4) :
    GF4CompsOn P := by
  intro S _ _ d hd ⟨eS⟩ β hβ s hs hs2
  obtain ⟨hd2, hd4⟩ := hP d hd
  exact glaLayer_le_iSup_isGF4Comp (fun K hK => isGF4Comp_of_isComponentOf_gf4 hc hd2 hd4 eS hβ hK)
    (h2 S d hd ⟨eS⟩ β hβ s hs hs2)

theorem gf4CompsRest_of_rest2 (h : GF4CompsRest2) : Inputs256o.GF4CompsRest := by
  refine (GF4CompsOn.or (GF4CompsOn.or gf4CompsOn_symplectic gf4CompsOn_unitary)
    (gf4CompsOn_of_twoEltLayer h.1 h.2 fun d hd => ⟨hd.1, hd.2.1⟩)).mono fun d hd => ?_
  obtain ⟨hd2, hd4, -, hnA⟩ := hd
  by_cases hB : ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .B r q
  · obtain ⟨r, q, hrq⟩ := hB
    rw [hrq] at hd4
    exact Or.inl (Or.inl ⟨r, q, hrq, hd4⟩)
  by_cases hU : ∃ (r : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA r q
  · obtain ⟨r, q, hrq⟩ := hU
    rw [hrq] at hd4
    exact Or.inl (Or.inr ⟨r, q, hrq, hd4⟩)
  exact Or.inr ⟨hd2, hd4, hnA, hU, hB⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256p

end
