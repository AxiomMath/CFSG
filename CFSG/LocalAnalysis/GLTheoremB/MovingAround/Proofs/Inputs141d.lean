module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

section TwoElements

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_pow {g : G} {m : ℕ} (h : g ^ (2 ^ m) = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨m, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem exists_pow_eq_one_of_isPGroup {g : G} (h : IsPGroup 2 ↥(Subgroup.zpowers g)) :
    ∃ m : ℕ, g ^ (2 ^ m) = 1 := by
  obtain ⟨m, hm⟩ := h ⟨g, Subgroup.mem_zpowers g⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

variable [Finite G]

theorem exists_two_parts {a c : G} (hac : Commute a c) (hg : IsPGroup 2 ↥(Subgroup.zpowers (a * c))) :
    ∃ k : ℕ, (a * c) ^ k = a * c ∧ IsPGroup 2 ↥(Subgroup.zpowers (a ^ k)) ∧
      IsPGroup 2 ↥(Subgroup.zpowers (c ^ k)) := by
  have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  set N := Nat.card G with hN
  set e := N.factorization 2 with he
  set u := N / 2 ^ e with hu
  have hNu : 2 ^ e * u = N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have hcop : Nat.Coprime (2 ^ e) u := Nat.Coprime.pow_left e (Nat.coprime_ordCompl Nat.prime_two hN0)
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have huk : u ∣ k := (Nat.modEq_zero_iff_dvd).1 hk0
  have hpow : ∀ y : G, y ^ (k * 2 ^ e) = 1 := by
    intro y
    apply orderOf_dvd_iff_pow_eq_one.1
    refine (orderOf_dvd_natCard y).trans ?_
    rw [← hN, ← hNu, mul_comm k]
    exact Nat.mul_dvd_mul_left _ huk
  refine ⟨k, ?_, isPGroup_zpowers_of_pow (m := e) (by rw [← pow_mul]; exact hpow a),
    isPGroup_zpowers_of_pow (m := e) (by rw [← pow_mul]; exact hpow c)⟩
  obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hg
  have h1 : orderOf (a * c) ∣ 2 ^ e := by
    have hd : orderOf (a * c) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have hdN : orderOf (a * c) ∣ N := orderOf_dvd_natCard _
    rw [ht] at hdN ⊢
    exact pow_dvd_pow 2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 hdN)
  have h2 : k ≡ 1 [MOD orderOf (a * c)] := Nat.ModEq.of_dvd h1 hk1
  have h3 := (pow_eq_pow_iff_modEq (x := a * c) (n := k) (m := 1)).2 h2
  rwa [pow_one] at h3

theorem mem_iSup_of_two {ι : Type*} [Finite ι] (A B : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (h2 : ∀ i, ∀ g ∈ A i, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ B i)
    {g : G} (hg : g ∈ ⨆ i, A i) (hg2 : IsPGroup 2 ↥(Subgroup.zpowers g)) : g ∈ ⨆ i, B i := by
  classical
  cases nonempty_fintype ι
  suffices key : ∀ s : Finset ι, ∀ g ∈ ⨆ i ∈ s, A i, IsPGroup 2 ↥(Subgroup.zpowers g) →
      g ∈ ⨆ i ∈ s, B i by
    have h := key Finset.univ g (by simpa using hg) hg2
    simpa using h
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g hg _
    have hg1 : g = 1 := by simpa using hg
    rw [hg1]
    exact Subgroup.one_mem _
  | insert j s hj ih =>
    intro g hg hg2
    rw [Finset.iSup_insert] at hg ⊢
    have hcomm : ∀ a ∈ A j, ∀ c ∈ ⨆ i ∈ s, A i, a * c = c * a := by
      intro a ha c hc'
      have hle : (⨆ i ∈ s, A i) ≤ Subgroup.centralizer (A j : Set G) :=
        iSup₂_le fun i hi y hy => Subgroup.mem_centralizer_iff.2 fun z hz =>
          (hc j i (fun h => hj (h ▸ hi)) z hz y hy).eq
      exact Subgroup.mem_centralizer_iff.1 (hle hc') a ha
    obtain ⟨a, ha, c, hc', rfl⟩ := Input183.mem_sup_of_commute hcomm hg
    have hac : Commute a c := hcomm a ha c hc'
    obtain ⟨k, hk, hak, hck⟩ := exists_two_parts hac hg2
    rw [← hk, hac.mul_pow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (h2 j _ (pow_mem ha k) hak))
      (Subgroup.mem_sup_right (ih _ (pow_mem hc' k) hck))

end TwoElements

section Family

theorem isComponentOf_of_perfectInLayer {S : Type} [Group S] [Finite S] {β : MulAut S} (hlay : PerfectInLayer β)
    {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) J) : IsComponentOf J (fixSubgroup β) :=
  (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ
    (hlay J hJ.1 (glaPComponent_perfect hJ))).1

theorem structAt_of_family {X Q : Type} [Group X] [Group Q] [Finite X] [Finite Q] (π : X →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X) (hodd : Nat.Coprime 2 (Nat.card π.ker))
    (α : MulAut X) (β : MulAut Q) (hαβ : ∀ x, π (α x) = β (π x)) {ι : Type*} (B : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ B i, ∀ b ∈ B j, Commute a b)
    (h2 : ∀ g ∈ fixSubgroup α, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ ⨆ i, B i)
    {J : Subgroup Q} (hJ : IsComponentOf J (fixSubgroup β)) (i₀ : ι) (hJi : J = (B i₀).map π) :
    StructAt β J := by
  refine ⟨Set.range fun i => (B i).map π, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hij : i ≠ j := fun h => hne (by rw [h])
    rw [← map_mul, ← map_mul, (hc i j hij x hx y hy).eq]
  · intro k hk hk2
    obtain ⟨g, hg, hg2, rfl⟩ := exists_two_lift π hπ hker hodd α β hαβ hk hk2
    have hle : (⨆ i, B i) ≤ (sSup (Set.range fun i => (B i).map π)).comap π :=
      iSup_le fun i => Subgroup.map_le_iff_le_comap.1 (le_sSup ⟨i, rfl⟩)
    exact hle (h2 g hg hg2)
  · exact le_iSup₂_of_le J ⟨i₀, hJi.symm⟩ (le_iSup_of_le hJ le_rfl)

end Family

section Unitary

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (toLinSU toLinSU_injective mem_range_toLinSU
  toLinSU_mem_unitaryCentralizer exists_good_primaryFactor_of_component primaryData_toLin'
  nonempty_statedSU_mulEquiv_fixSubgroup isSolvable_gramSU_three_two)

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem coprime_two_card_normOneScalars (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 1 ≤ n)
    (C : Matrix (Fin n) (Fin n) K) : Nat.Coprime 2 (Nat.card (normOneScalars h (gramSU h C) n)) := by
  haveI : CharP K 2 := hℓ ▸ h.charP
  haveI := h.finite
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  obtain ⟨c, -, -, hzc⟩ := z.2
  have hzc2 : (Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ 2) : GL (Fin n) K) = 1 := by
    have h1 := congrArg (fun w : ↥(normOneScalars h (gramSU h C) n) =>
      ((w : ↥(gramSU h C)) : GL (Fin n) K)) hz2
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [hzc, ← map_pow] at h1
    exact h1
  have hc2 : (c : K) ^ (2 ^ 1) = 1 := by
    have h1 := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) hzc2
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Units.val_pow_eq_pow_val] at h1
    simpa using h1
  have hc1 : c = 1 := Units.val_eq_one.1 (eq_one_of_pow_two_pow_eq_one hc2)
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hzc, hc1, map_one]
    rfl
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem structAt_primeFormFieldHom (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) (σ : K ≃+* K) (hσ : orderOf σ = 3)
    {J : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hJ : GLAPComponent 3 (fixSubgroup (primeFormFieldHom h hC σ)) J) :
    StructAt (primeFormFieldHom h hC σ) J := by
  haveI := h.finite
  set X := gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hX
  let π : ↥X →* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    QuotientGroup.mk' (normOneScalars h X n)
  have hker : π.ker ≤ Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hodd : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact coprime_two_card_normOneScalars h hℓ (by omega) _
  have hαβ : ∀ x, π (primeFormFieldSU h hC σ x) = primeFormFieldHom h hC σ (π x) := fun x =>
    (primeFormFieldAut_mk h hC σ x).symm
  refine structAt_of_cover π (QuotientGroup.mk'_surjective _) hker hodd _ _ hαβ hJ fun J₀ hJ₀ _ => ?_
  have h₀ : UnitaryFieldData ℓ (f / 3) (CFSG.LieType.Chevalley.fixSubfield σ) :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ
  have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσ
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_fixSubgroup (n := n) h h₀ hbar hC
  by_cases hq₀ : n = 3 ∧ ℓ ^ (f / 3) = 2
  · exfalso
    obtain ⟨hn3, hq2⟩ := hq₀
    subst hn3
    haveI := isSolvable_gramSU_three_two h₀ hq2
    haveI : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (ℓ ^ (f / 3)) (CFSG.LieType.Chevalley.fixSubfield σ)) :=
      Group.isSolvable_of_surjective
        (f := (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h₀ 3)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hsolv : Group.IsSolvable ↥(fixSubgroup (primeFormFieldSU h hC σ)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact false_of_glaPComponent_of_isSolvable hsolv hJ₀
  · haveI : Fact ℓ.Prime := ⟨h.prime⟩
    have hcard : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = (ℓ ^ (f / 3)) ^ 2 := by
      rw [h₀.card, ← pow_mul, mul_comm]
    have hq : CFSG.IsQuasisimple ↥(fixSubgroup (primeFormFieldSU h hC σ)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard hn
          (fun heq => hq₀ ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)).1
    exact structAt_of_isQuasisimple_fixSubgroup ⟨hq.1.1, hq.2.1⟩ hJ₀.1

theorem det_eq_one_of_pow_two {V : Type*} [AddCommGroup V] [Module K V] [CharP K 2]
    {y : LinearMap.GeneralLinearGroup K V} {m : ℕ} (hm : y ^ (2 ^ m) = 1) :
    LinearMap.det (y : Module.End K V) = 1 := by
  refine eq_one_of_pow_two_pow_eq_one (m := m) ?_
  rw [← map_pow, ← Units.val_pow_eq_pow_val, hm, Units.val_one, map_one]

theorem structAt_primeFormConjHom (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 1 ≤ n)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    {J : Subgroup (primeFormP h (idGram K n))}
    (hJ : GLAPComponent 3 (fixSubgroup (primeFormConjHom h (idGram K n) A)) J) :
    StructAt (primeFormConjHom h (idGram K n) A) J := by
  classical
  haveI := h.finite
  haveI : CharP K 2 := hℓ ▸ h.charP
  have h3ℓ : 3 ≠ ℓ := by omega
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  set X := gramSU h (idGram K n) with hX
  let π : ↥X →* primeFormP h (idGram K n) := QuotientGroup.mk' (normOneScalars h X n)
  have hker : π.ker ≤ Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hodd : Nat.Coprime 2 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact coprime_two_card_normOneScalars h hℓ hn _
  have hαβ : ∀ g, π (primeFormConjSU h (idGram K n) A g) = primeFormConjHom h (idGram K n) A (π g) :=
    fun g => (primeFormConjHom_mk h (idGram K n) A g).symm
  have hJc := isComponentOf_of_perfectInLayer
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_primeFormConjHom h Nat.prime_three
      h3ℓ A hA) hJ
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) with hx
  have H : UnitaryPrimaryData h.bar (idForm h n) x := primaryData_toLin' h A.2 Nat.prime_three h3ℓ hA
  obtain ⟨a, ha⟩ := exists_good_primaryFactor_of_component hq A rfl H J hJc
  obtain ⟨hcomm, -, hgen⟩ := (CFSG.RankThree.PartOne.r3e_unitary_semisimple_primary_algebra_and_full_centralizer h
    (idForm h n) H.symm H.sep x H.isom H.squarefree).directProduct
  haveI : Finite (CFSG.RankThree.PartOne.adjointOrbits h x) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  let B' : CFSG.RankThree.PartOne.adjointOrbits h x → Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)) :=
    fun O => supportedUnitary (idForm h n) x (O : Set K[X]) ⊓ sesqSpecialUnitaryGroup (idForm h n) ⊓
      (if ((a.1 : K[X]) ∈ (O : Set K[X])) then specialBlock (idForm h n) x (a.1 : K[X]) else ⊤)
  let B : CFSG.RankThree.PartOne.adjointOrbits h x → Subgroup ↥X := fun O => (B' O).comap (toLinSU h n)
  have hB'le : ∀ O, B' O ≤ (toLinSU h n).range := fun O g hg => mem_range_toLinSU hg.1.2
  let O₀ : CFSG.RankThree.PartOne.adjointOrbits h x :=
    ⟨{(a.1 : K[X]), dualPoly h.bar (a.1 : K[X])}, (a.1 : K[X]), Finset.mem_coe.2 a.1.2, rfl⟩
  have horbit : ∀ O : CFSG.RankThree.PartOne.adjointOrbits h x, (a.1 : K[X]) ∈ (O : Set K[X]) →
      (O : Set K[X]) = {(a.1 : K[X]), dualPoly h.bar (a.1 : K[X])} := by
    rintro ⟨O, b, hb, rfl⟩ haO
    exact (CFSG.RankThree.PartOne.adjointOrbits_eq_of_mem H (Finset.mem_coe.1 hb) haO).symm
  refine structAt_of_family π (QuotientGroup.mk'_surjective _) hker hodd _ _ hαβ B ?_ ?_ hJc O₀ ?_
  ·
    intro O O' hne g hg g' hg'
    have h1 : Commute (toLinSU h n g) (toLinSU h n g') :=
      hcomm O O.2 O' O'.2 (fun e => hne (Subtype.ext e)) _ hg.1.1 _ hg'.1.1
    exact toLinSU_injective (by rw [map_mul, map_mul]; exact h1.eq)
  ·
    intro g hg hg2
    have hgU : toLinSU h n g ∈ unitaryCentralizer (idForm h n) x := toLinSU_mem_unitaryCentralizer A rfl hg
    rw [← hgen] at hgU
    have hg2' : IsPGroup 2 ↥(Subgroup.zpowers (toLinSU h n g)) := by
      have h1 := hg2.map (toLinSU h n)
      rwa [MonoidHom.map_zpowers] at h1
    have hmem : toLinSU h n g ∈ ⨆ O, B' O := by
      refine mem_iSup_of_two (fun O : CFSG.RankThree.PartOne.adjointOrbits h x =>
        supportedUnitary (idForm h n) x (O : Set K[X])) B'
        (fun O O' hne => hcomm O O.2 O' O'.2 (fun e => hne (Subtype.ext e))) ?_ hgU hg2'
      intro O y hy hy2
      obtain ⟨m, hm⟩ := exists_pow_eq_one_of_isPGroup hy2
      have hyU : y ∈ unitaryCentralizer (idForm h n) x := supportedUnitary_le_unitaryCentralizer _ hy
      have hySU : y ∈ sesqSpecialUnitaryGroup (idForm h n) :=
        mem_sesqSpecialUnitaryGroup.2 ⟨(mem_unitaryCentralizer.mp hyU).1, det_eq_one_of_pow_two hm⟩
      refine ⟨⟨hy, hySU⟩, ?_⟩
      split_ifs with haO
      · have hyc : y ∈ gl_centralizer x := supportedUnitary_le_gl_centralizer _ hy
        refine mem_specialBlock.2 ⟨?_, hyc, ?_⟩
        · change y ∈ supportedUnitary (idForm h n) x {(a.1 : K[X]), dualPoly h.bar (a.1 : K[X])}
          rw [← horbit O haO]
          exact hy
        · haveI : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
          haveI : CharP (AdjoinRoot (a.1 : K[X])) 2 :=
            charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (a.1 : K[X]))).injective 2
          apply Units.ext
          refine eq_one_of_pow_two_pow_eq_one (m := m) ?_
          have e1 : (⟨y, hyc⟩ : gl_centralizer x) ^ (2 ^ m) = 1 := Subtype.ext (by simpa using hm)
          rw [← Units.val_pow_eq_pow_val, ← map_pow, e1, map_one, Units.val_one]
      · exact Subgroup.mem_top _
    have hmap : (⨆ O, B' O) = (⨆ O, B O).map (toLinSU h n) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun O => (Subgroup.map_comap_eq_self (hB'le O)).symm
    rw [hmap] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rwa [← toLinSU_injective hgg']
  ·
    have hin : (a.1 : K[X]) ∈ (O₀ : Set K[X]) := Or.inl rfl
    have hB0 : B' O₀ = specialBlock (idForm h n) x (a.1 : K[X]) := by
      simp only [B', if_pos hin]
      exact le_antisymm inf_le_right (le_inf (le_inf specialBlock_le_orbitFactor
        (specialBlock_le_sesqSpecialUnitaryGroup_of_good H hq a.1 a.2)) le_rfl)
    rw [ha]
    show _ = ((B' O₀).comap (toLinSU h n)).map π
    rw [hB0]

end Unitary

section UnitaryCatalogue

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem input14_1StructFor_unitary :
    Input14_1StructFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.twistedA r q := by
  intro S _ _ _ _ d hd hchar he β hβ3 _ J hJ _
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, rfl⟩ := hd
  have hq2 : q.p = 2 := by
    have h1 : (TauCeti.LieTypeIndex.twistedA r q).characteristic = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA r q
    rw [← h1]
    exact hchar
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := he
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) K) := isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  refine structAt_of_congr e' ?_
  have hJ' := glaPComponent_congr e' hJ
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β) = 1
  ·
    have hβD : MulAut.congr e' β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ 3, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    have hA3 : (A : GL (Fin (r + 1)) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    rw [← hA] at hJ' ⊢
    exact structAt_primeFormConjHom h hq2 (by omega) A hA3 hJ'
  ·
    have hne : MulAut.congr e' β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (MulAut.congr e' β) = 3 := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' Nat.prime_three
        (by norm_num) (MulAut.congr e' β) hord _ rfl hσp
    set φ : MulAut (primeFormP h (idGram K (r + 1))) := primeFormConjHom h (idGram K (r + 1)) M with hφ
    have hc : MulAut.congr (φ⁻¹ : MulAut (primeFormP h (idGram K (r + 1)))) (MulAut.congr e' β) =
        primeFormFieldHom h hC (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) := by
      have e1 : MulAut.congr (φ⁻¹ : MulAut (primeFormP h (idGram K (r + 1)))) (MulAut.congr e' β) =
          φ⁻¹ * MulAut.congr e' β * φ⁻¹⁻¹ := by
        ext y
        rfl
      rw [e1, inv_inv]
      exact hM
    refine structAt_of_congr (φ⁻¹ : MulAut (primeFormP h (idGram K (r + 1)))) ?_
    have hJ'' := glaPComponent_congr (φ⁻¹ : MulAut (primeFormP h (idGram K (r + 1)))) hJ'
    rw [hc] at hJ'' ⊢
    exact structAt_primeFormFieldHom h hq2 hn3 hC _ hσp hJ''

theorem input14_1CoreFor_unitary :
    Input14_1CoreFor fun d => ∃ r q, d = TauCeti.LieTypeIndex.twistedA r q :=
  input14_1CoreFor_of_struct input14_1StructFor_unitary

end UnitaryCatalogue

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d

end
