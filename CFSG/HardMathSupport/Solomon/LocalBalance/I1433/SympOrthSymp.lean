module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthGeneric
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped commutatorElement

theorem sympl_inner_of_mem_commutator {ℓ f r : ℕ} {K : Type} [Field K] (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSp r K)) {β : MulAut S} (hβ : β ∈ commutator (MulAut S))
    (hβ3 : β ^ 3 = 1) : ∃ t : S, MulAut.conj t = β := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  obtain ⟨-, -, -, -, -, hDnorm, hcomm, -, hrel, -⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hr hK
  have hD : MulAut.congr e β ∈ spLinearAutGroup r K := by
    have hle : commutator (MulAut S) ≤
        (spLinearAutGroup r K).comap (MulAut.congr e).toMonoidHom := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap]
      show (MulAut.congr e) ⁅a, b⁆ ∈ _
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hcomm _ _
    exact hle hβ
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K))).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hrel' : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
    hrel.trans (Nat.gcd_dvd_left 2 _)
  obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel'
    Nat.prime_three (by norm_num) hD hβ'
  refine ⟨e.symm t, ?_⟩
  apply (MulAut.congr e).injective
  rw [congr_conj_apply_so, MulEquiv.apply_symm_apply, ht]

@[expose] noncomputable def sympPi {r : ℕ} {K : Type} [Field K] {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSp r K)) : StatedSp r K →* S :=
  (e.symm : StatedProj (StatedSp r K) →* S).comp (SymplecticFlag.proj r K)

theorem sympPi_surjective {r : ℕ} {K : Type} [Field K] {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSp r K)) : Function.Surjective (sympPi e) :=
  e.symm.surjective.comp proj_surjective

theorem sympPi_ker {r : ℕ} {K : Type} [Field K] {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSp r K)) : (sympPi e).ker = (SymplecticFlag.proj r K).ker := by
  ext g
  simp only [MonoidHom.mem_ker, sympPi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact ⟨fun h => (MulEquiv.map_eq_one_iff e.symm).mp h, fun h => by rw [h, map_one]⟩

theorem sympPi_ker_le_center {r : ℕ} {K : Type} [Field K] {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSp r K)) : (sympPi e).ker ≤ Subgroup.center (StatedSp r K) := by
  rw [sympPi_ker, ker_proj]; exact spScalars_le_center

theorem sympPi_ker_sq {r : ℕ} {K : Type} [Field K] [Finite K] {S : Type} [Group S] (hr : 1 ≤ r)
    (e : S ≃* StatedProj (StatedSp r K)) : ∀ z ∈ (sympPi e).ker, z ^ 2 = 1 := by
  intro z hz
  rw [sympPi_ker] at hz
  exact CFSG.RankThree.PartOne.sq_eq_one_of_proj_eq_one hr hz

theorem sympl_perfectInLayer {ℓ f r : ℕ} {K : Type} [Field K] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3) {S : Type} [Group S]
    (e : S ≃* StatedProj (StatedSp r K)) (y : S) (hy : y ^ 3 = 1) :
    PerfectInLayer (MulAut.conj y) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  refine LieSemisimple.perfectInLayer_of_congr e _ ?_
  rw [congr_conj_apply_so]
  have hey : (e y) ^ 3 = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨x, hx, hx3⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega)
    Nat.prime_three (by norm_num) hey
  rw [← hx]
  exact LieSemisimple.perfectInLayer_conj_sp hℓ hf hK (by omega) Nat.prime_three (by norm_num)
    (Ne.symm hℓ3) x hx3

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCOrthogonal Polynomial

theorem mem_of_map_mem_of_cube {G S : Type*} [Group G] [Group S] (π : G →* S)
    (hker : π.ker ≤ Subgroup.center G) (hker2 : ∀ z ∈ π.ker, z ^ 2 = 1) {P : Subgroup G} {X : G}
    (hX3 : X ^ 3 = 1) (h : π X ∈ P.map π) : X ∈ P := by
  obtain ⟨g, hg, hgX⟩ := h
  have hz : X⁻¹ * g ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgX, inv_mul_cancel]
  obtain ⟨z, hzdef⟩ : ∃ z : G, z = X⁻¹ * g := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have hzc : Commute X z := Subgroup.mem_center_iff.mp (hker hz) X
  have hg' : g = X * z := by rw [hzdef]; group
  have hz2 := hker2 z hz
  have h4 : g ^ 4 = X := by
    rw [hg', hzc.mul_pow]
    calc X ^ 4 * z ^ 4 = (X ^ 3 * X) * (z ^ 2) ^ 2 := by group
      _ = X := by rw [hX3, hz2]; group
  rw [← h4]
  exact P.pow_mem hg 4

@[expose] noncomputable def sympCentralizerGL {r : ℕ} {K : Type} [Field K] (X : StatedSp r K) :
    Subgroup.centralizer ({X} : Set (StatedSp r K)) →* gl_centralizer (spLin r K X) :=
  ((spLin r K).comp (Subgroup.centralizer ({X} : Set (StatedSp r K))).subtype).codRestrict
    (gl_centralizer (spLin r K X)) (fun g => by
      rw [mem_gl_centralizer]
      have h : X * g.1 = g.1 * X := (Subgroup.mem_centralizer_singleton_iff.mp g.2).symm
      have h2 : spLin r K g.1 * spLin r K X = spLin r K X * spLin r K g.1 := by
        rw [← map_mul, ← map_mul, ← h]
      exact (Commute.units_val (show Commute (spLin r K g.1) (spLin r K X) from h2)))

@[expose] noncomputable def sympBlockRestrict {r : ℕ} {K : Type} [Field K] (X : StatedSp r K)
    (c : K[X]) : Subgroup.centralizer ({X} : Set (StatedSp r K)) →*
      blockGL (spEnd X) c :=
  (blockRestrict (spLin r K X) c).comp (sympCentralizerGL X)

theorem blockApply_sympBlockRestrict {r : ℕ} {K : Type} [Field K] (X : StatedSp r K) (c : K[X])
    (g : Subgroup.centralizer ({X} : Set (StatedSp r K))) (v : Fin r ⊕ Fin r → K)
    (hv : v ∈ primaryComponent (spEnd X) c) :
    blockApply (sympBlockRestrict X c g) v hv = spEnd g.1 v := rfl

theorem sympBlockRestrict_self {r : ℕ} {K : Type} [Field K] (X : StatedSp r K) (c : K[X])
    (u : primaryComponent (spEnd X) c) :
    ((sympBlockRestrict X c (selfCentralizer X) : blockGL (spEnd X) c) :
      Module.End (AdjoinRoot c) (primaryComponent (spEnd X) c)) u = AdjoinRoot.root c • u := by
  apply Subtype.ext
  rw [coe_root_smul_primaryComponent]
  exact blockApply_sympBlockRestrict X c (selfCentralizer X) u.1 u.2


theorem exists_noncomm_of_isQuasisimple {P : Type*} [Group P] (h : CFSG.IsQuasisimple P) :
    ∃ a b : P, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h' => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])⟩

theorem spSupported_le_centralizer {r : ℕ} {K : Type} [Field K] (X : StatedSp r K) (O : Set K[X]) :
    spSupported X O ≤ Subgroup.centralizer ({X} : Set (StatedSp r K)) := fun g hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_spSupported.mp hg).1

theorem eq_one_of_mem_spSupported_fixed {r ℓ f : ℕ} {K : Type} [Field K] {x : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks ℓ f 3 x a)
    (hx : x ∈ spSupported x {(Polynomial.X - 1 : K[X])}) : x = 1 := by
  classical
  have hx' := mem_spSupported.mp hx
  have hall : ∀ k : primaryFactors (spEnd x), ∀ v ∈ primaryComponent (spEnd x) (k : K[X]),
      spEnd x v = v := by
    intro k v hv
    by_cases hk : (k : K[X]) = Polynomial.X - 1
    · have hv' : v ∈ primaryComponent (spEnd x) (Polynomial.X - 1) := by rw [← hk]; exact hv
      rw [blocks.fixed_eq] at hv'
      have := LinearMap.mem_ker.mp hv'
      simpa [sub_eq_zero] using this
    · exact hx'.2 k k.2 (by simpa using hk) v hv
  have htop : ∀ v : Fin r ⊕ Fin r → K, spEnd x v = v := by
    intro v
    have hmem : v ∈ ⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : K[X]) := by
      rw [blocks.isInternal.submodule_iSup_eq_top]; trivial
    have hle : (⨆ k : primaryFactors (spEnd x), primaryComponent (spEnd x) (k : K[X])) ≤
        LinearMap.ker (spEnd x - 1) := by
      refine iSup_le fun k w hw => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hall k w hw, Module.End.one_apply, sub_self]
    have := LinearMap.mem_ker.mp (hle hmem)
    simpa [sub_eq_zero] using this
  apply spLin_injective (r := r) (K := K)
  apply Units.ext
  rw [map_one]
  exact LinearMap.ext fun v => htop v

theorem sympl_hasLowRankBlock {ℓ f r : ℕ} {K : Type} [Field K] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3)
    (hne : ¬(r = 2 ∧ ℓ ^ f = 2)) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSp r K)) (X : StatedSp r K) (hX3 : X ^ 3 = 1)
    (hX1 : sympPi e X ≠ 1) (J : Subgroup S)
    (hJ : IsComponentOf J (Subgroup.centralizer ({sympPi e X} : Set S))) (hXJ : sympPi e X ∈ J) :
    HasLowRankBlock (sympPi e) X J := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hr1 : 1 ≤ r := by omega
  have hX1' : SymplecticFlag.proj r K X ≠ 1 := fun h => hX1 (by simp [sympPi, h])
  have hX1'' : X ≠ 1 := fun h => hX1' (by rw [h, map_one])
  have hXord : orderOf X = 3 := orderOf_eq_prime hX3 hX1''
  have hx₀ord : orderOf (SymplecticFlag.proj r K X) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hX3, map_one]) hX1'
  have blocks := ((symplectic_cross_prime_primary_centralizer_blocks hℓ hf hK Nat.prime_three
    (by norm_num) (Ne.symm hℓ3) hr1 (SymplecticFlag.proj r K X) hx₀ord).2 X rfl hXord)
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    have := Fintype.ofFinite K
    have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h)
  have hsq := (altPrimaryData_spLin hpK hX3).squarefree
  haveI : Finite (reciprocalOrbits (spEnd X)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hq : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  set A : reciprocalOrbits (spEnd X) → Subgroup (StatedSp r K) :=
    fun O => spSupported X (O : Set K[X]) with hA
  have hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b := fun i j hij a ha b hb =>
    hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i) := fun O =>
    LieSemisimple.quasisimple_or_solvable_spSupported (by norm_num) hq hsq blocks O
  have hfix := fixSubgroup_conj_eq_centralizer_so (sympPi e X)
  have hJ' : IsComponentOf J (fixSubgroup (MulAut.conj (sympPi e X))) := by rw [hfix]; exact hJ
  obtain ⟨i, hiq, hJi⟩ := LieComp.components_conj_of_orbit_family (sympPi e)
    (sympPi_surjective e) (sympPi_ker_le_center e) X A hc hjoin htame J hJ'
  have hXP : X ∈ ⁅A i, A i⁆ := by
    refine mem_of_map_mem_of_cube (sympPi e) (sympPi_ker_le_center e) (sympPi_ker_sq hr1 e) hX3 ?_
    rw [← hJi]; exact hXJ
  obtain ⟨c, hc_mem, hOc⟩ := i.2
  have hcP : c ∈ primaryFactors (spEnd X) := Finset.mem_coe.mp hc_mem
  have hOc' : ({c, reciprocalPolynomial c} : Set K[X]) = ↑i := hOc
  have hAi : A i = spSupported X {c, reciprocalPolynomial c} := by
    simp only [hA]; rw [hOc']
  rw [hAi] at hiq hJi hXP
  have hFC := spSupported_le_centralizer X ({c, reciprocalPolynomial c} : Set K[X])
  have hperf : ⁅⁅spSupported X {c, reciprocalPolynomial c},
        spSupported X {c, reciprocalPolynomial c}⁆,
      ⁅spSupported X {c, reciprocalPolynomial c},
        spSupported X {c, reciprocalPolynomial c}⁆⁆ =
      ⁅spSupported X {c, reciprocalPolynomial c},
        spSupported X {c, reciprocalPolynomial c}⁆ :=
    Subgroup.isPerfect_iff.mp hiq.1
  have hnonab : ∃ g₁ ∈ ⁅spSupported X {c, reciprocalPolynomial c},
      spSupported X {c, reciprocalPolynomial c}⁆, ∃ g₂ ∈ ⁅spSupported X {c, reciprocalPolynomial c},
      spSupported X {c, reciprocalPolynomial c}⁆, g₁ * g₂ ≠ g₂ * g₁ := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hiq
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  by_cases hc1 : c = Polynomial.X - 1
  ·
    exfalso
    have hrec : reciprocalPolynomial c = c := by
      rw [hc1]; exact reciprocalPolynomial_X_sub_one
    have hXF : X ∈ spSupported X {(Polynomial.X - 1 : K[X])} := by
      have h1 : X ∈ spSupported X {c, reciprocalPolynomial c} :=
        Subgroup.commutator_le_self _ hXP
      rw [hrec, Set.pair_eq_singleton, hc1] at h1
      exact h1
    exact hX1'' (eq_one_of_mem_spSupported_fixed blocks hXF)
  · haveI : Fact (Irreducible c) := ⟨irreducible_of_mem_primaryFactors hcP⟩
    have hord : orderOf (AdjoinRoot.root c) = 3 := blocks.nontrivial c hcP hc1
    have hω3 : (AdjoinRoot.root c) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (AdjoinRoot.root c)
      rwa [hord] at this
    have hω1 : AdjoinRoot.root c ≠ 1 := by
      intro h; rw [h, orderOf_one] at hord; omega
    have hω0 : AdjoinRoot.root c ≠ 0 := by
      intro h; rw [h] at hω3; simp at hω3
    by_cases hself : reciprocalPolynomial c = c
    ·
      obtain ⟨d, -, -, σ, -, -, -, hσroot, -, hE, hbar, Hf, hHf, hHfl, -, ⟨eb, heb⟩, φ, hφ⟩ :=
        (blocks.selfDual ⟨c, hcP⟩ hc1 hself).exists_half
      have hFeq : spSupported X {c, reciprocalPolynomial c} = spSupported X {c} := by
        rw [hself, Set.pair_eq_singleton]
      rw [hFeq] at hiq hJi hXP hperf hnonab
      have hFC' := spSupported_le_centralizer X ({c} : Set K[X])
      have hρφ : ∀ g (hg : g ∈ spSupported X {c}),
          sympBlockRestrict X c ⟨g, hFC' hg⟩ = ((φ ⟨g, hg⟩ : sesqUnitaryGroup Hf) :
            blockGL (spEnd X) c) := by
        intro g hg
        exact blockGL_ext fun v hv => by
          rw [blockApply_sympBlockRestrict]; exact (hφ ⟨g, hg⟩ v hv).symm
      have hωn : hE.bar (AdjoinRoot.root c) * AdjoinRoot.root c = 1 := by
        rw [hbar, hσroot, inv_mul_cancel₀ hω0]
      refine hasLowRankBlock_of_factor (sympPi e) X J (AdjoinRoot c)
        (primaryComponent (spEnd X) c) (sympBlockRestrict X c) (AdjoinRoot.root c) hω1 hω3
        (sympBlockRestrict_self X c) (spSupported X {c}) hFC' hJi hperf hnonab
        (sesqUnitaryGroup Hf) (fun g hg => ?_) (fun u hu => ?_) (fun g₁ h₁ g₂ h₂ h => ?_)
        (fun N hNle hN hna => ?_)
      · rw [hρφ g hg]; exact (φ ⟨g, hg⟩).2
      · refine ⟨(φ.symm ⟨u, hu⟩).1, (φ.symm ⟨u, hu⟩).2, ?_⟩
        rw [hρφ _ (φ.symm ⟨u, hu⟩).2]; simp
      · rw [hρφ g₁ h₁, hρφ g₂ h₂] at h
        exact congrArg Subtype.val (φ.injective (Subtype.ext h))
      · exact exists_lowRank_of_normal_nonabelian_unitary eb heb hω1 hωn hN hna
    · have hne : c ≠ reciprocalPolynomial c := fun h => hself h.symm
      obtain ⟨φ, hφ, -⟩ := (blocks.paired ⟨c, hcP⟩ hne).factor
      have hρφ : ∀ g (hg : g ∈ spSupported X {c, reciprocalPolynomial c}),
          sympBlockRestrict X c ⟨g, hFC hg⟩ = φ ⟨g, hg⟩ := by
        intro g hg
        exact blockGL_ext fun v hv => by
          rw [blockApply_sympBlockRestrict]; exact (hφ ⟨g, hg⟩ v hv).symm
      refine hasLowRankBlock_of_factor (sympPi e) X J (AdjoinRoot c)
        (primaryComponent (spEnd X) c) (sympBlockRestrict X c) (AdjoinRoot.root c) hω1 hω3
        (sympBlockRestrict_self X c) (spSupported X {c, reciprocalPolynomial c}) hFC hJi hperf
        hnonab ⊤ (fun _ _ => Subgroup.mem_top _) (fun u _ => ?_) (fun g₁ h₁ g₂ h₂ h => ?_)
        (fun N hNle hN hna => ?_)
      · refine ⟨(φ.symm u).1, (φ.symm u).2, ?_⟩
        rw [hρφ _ (φ.symm u).2]; simp
      · rw [hρφ g₁ h₁, hρφ g₂ h₂] at h
        exact congrArg Subtype.val (φ.injective h)
      · exact exists_lowRank_of_normal_nonabelian_gl
          (Module.finBasis (AdjoinRoot c) (primaryComponent (spEnd X) c)) hω1 hω0
          (fun f n hn => hN f (Subgroup.mem_top _) n hn) hna

theorem sympl_contra {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {r ℓ f : ℕ} (hG : StatedClassicalModel S .PSp r ℓ f)
    (hℓ3 : ℓ ≠ 3) {Q : Subgroup (MulAut S)} {x : S} {J : Subgroup S} {q : ℕ}
    (c : I1433SCfg Q x J q) : False := by
  obtain ⟨⟨hℓ, hf, hr, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  have hne' : ¬(r = 2 ∧ ℓ ^ f = 2) := fun h => hne (Prod.ext h.1 h.2)
  haveI := hs
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hS : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hna
  have hinn : ∀ β ∈ Q, ∃ t : S, MulAut.conj t = β := fun β hβ =>
    sympl_inner_of_mem_commutator hℓ hf hr hK e (c.derived hβ) (c.exponent β hβ)
  refine c.false_of_lowRank (sympPi e) (sympPi_surjective e) (sympPi_ker_le_center e)
    (sympPi_ker_sq (by omega) e) hS (fun y hy => sympl_perfectInLayer hℓ hf hr hK hℓ3 e y hy)
    (fun X hX3 hX1 J hJ hXJ => ?_) hinn
  exact sympl_hasLowRankBlock hℓ hf hr hK hℓ3 hne' e X hX3 hX1 J hJ hXJ

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
