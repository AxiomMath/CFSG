module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256p
public import CFSG.RankThree.PartOne.S11d.OrthLayer
import CFSG.RankThree.PartOne.S11d.OrthSplitFixed
import CFSG.RankThree.PartOne.S11d.OrthCaseN
import CFSG.HardMathSupport.Dickson.Bal207.OrthEightFixed
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions

section FixedSpace

variable {K : Type} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {R : QuadraticForm K W}

theorem twoElt_eq_one_of_dickson_of_finrank_le_two [CharP K 2] (hR : R.polarBilin.Nondegenerate)
    (hW : finrank K W ≤ 2) {t : TauCeti.QuadraticMap.orthogonalGroup R} (hδ : dicksonHom R hR t = 1) :
    ∀ n : ℕ, t ^ 2 ^ n = 1 → t = 1 := by
  have key : ∀ u : TauCeti.QuadraticMap.orthogonalGroup R, u ^ 2 = 1 → dicksonHom R hR u = 1 →
      u = 1 := by
    intro u hu hδu
    rcases (show finrank K W ≤ 1 ∨ finrank K W = 2 by omega) with h1 | h2
    · exact Subtype.ext (eq_one_of_dicksonHom_eq_one_of_finrank_le_one hR h1 hδu)
    · exact CFSG.HardMathSupport.Dickson.Bal207.OrthEight.eq_one_of_sq_eq_one_of_dicksonHom hR h2 hu hδu
  intro n
  induction n with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    refine ih (key _ ?_ ?_)
    · rw [← pow_mul, ← pow_succ]
      exact h
    · rw [map_pow, hδ, one_pow]

end FixedSpace

section FixedDerived

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem dicksonDerived_fixedSpace_of_four_le_card [CharP K 2] (hK : 4 ≤ Nat.card K)
    (hx : OddOrderIsometry Q p x) (h3 : 3 ≤ finrank K (fixedSpace x)) :
    DicksonDerived (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate := by
  have hWnd := hx.polarBilin_fixed_nondegenerate
  obtain ⟨m, hm⟩ := hx.even_finrank_fixed
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
    · by_cases hsplit : ∃ U : Submodule K (fixedSpace x), finrank K U = 2 ∧
          ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
      · obtain ⟨M⟩ := exists_splitFourModel hx (by omega) hsplit hK
        exact M.dicksonDerived hWnd
      · refine (nonsplit_quasisimple_dicksonDerived _ hWnd (Or.inl (by omega)) fun U hU => ?_).2
        by_contra hall
        push Not at hall
        exact hsplit ⟨U, by omega, hall⟩
    · by_cases hTW : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
          ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
      · exact dicksonDerived_of_threeSingular _ hWnd hTW
      · refine (nonsplit_quasisimple_dicksonDerived _ hWnd (Or.inr (by omega)) fun U hU => ?_).2
        by_contra hall
        push Not at hall
        exact hTW ⟨U, by omega, hall⟩
  · exact dicksonDerived_of_threeSingular _ hWnd (exists_threeSingular_of_dim _ hWnd hm4 (by omega))

theorem commutator_supportedFixedDerived_eq_of_four_le_card (hK : 4 ≤ Nat.card K)
    (hx : OddOrderIsometry Q p x) (h3 : 3 ≤ finrank K (fixedSpace x)) :
    ⁅supportedFixedDerived Q x, supportedFixedDerived Q x⁆ = supportedFixedDerived Q x := by
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
    rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega
  have hcov := ((orthogonal_regular_space_coverage _ hWnd h3).2 hnexc).1
  set O := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) with hO
  have e : ↥(commutator ↥O) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O))
  haveI := hcov
  haveI : Group.IsPerfect ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hperf : Group.IsPerfect ↥(supportedFixedDerived Q x) :=
    Group.IsPerfect.ofSurjective (f := (supportedFixedDerivedEquiv hx).symm.toMonoidHom)
      (supportedFixedDerivedEquiv hx).symm.surjective
  exact Subgroup.isPerfect_iff.1 hperf

end FixedDerived

section Special

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem ne_reciprocal_of_card_four_three (hK : Nat.card K = 4) (hx : OddOrderIsometry Q 3 x)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    h ≠ reciprocalPolynomial h := by
  intro hself
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨d, -, -, hroot, -⟩ := hx.exists_selfDual_hermitian (by decide) hh hne1 hself
  have h3 := hx.dvd_card_pow_add_one Nat.prime_three hh hne1 hroot
  rw [hK] at h3
  have h4 : (4 : ℕ) ^ d % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem commutator_specialBlock_eq_of_card_four_three (hK : Nat.card K = 4)
    (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : ⁅specialBlock Q x h, specialBlock Q x h⁆ = specialBlock Q x h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap h
  · have hne := ne_reciprocal_of_card_four_three hK hx hh hne1
    have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
      have := hx.p_lt_card_adjoinRoot Nat.prime_three hh hne1
      omega
    let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
        (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
    let e₁ := MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
    have hq : CFSG.IsQuasisimple ↥(specialBlock Q x h) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm)
        (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)
    exact Subgroup.isPerfect_iff.1 hq.1
  · have h1 : primaryMultiplicity x.toLinearMap h = 1 := by
      have := hx.primaryMultiplicity_pos hh
      omega
    rw [hx.specialBlock_eq_bot_of_finrank_eq_one hh h1, Subgroup.commutator_bot_left]

omit [Finite K] [FiniteDimensional K V] in
theorem mem_specialBlock_of_pow_two_pow_eq_one [CharP K 2] {h : K[X]} [Fact (Irreducible h)]
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x h) {n : ℕ} (hgn : g ^ 2 ^ n = 1) :
    g ∈ specialBlock Q x h := by
  refine mem_specialBlock.mpr ⟨hg, ?_⟩
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (⟨g, hg⟩ : ↥(supportedBlock Q x h)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hgn)
  have hc : blockDet Q x h ⟨g, hg⟩ ^ 2 ^ n = 1 := by rw [← map_pow, h1, map_one]
  have h0 : (blockDet Q x h ⟨g, hg⟩ - 1) ^ 2 ^ n = 0 := by
    rw [sub_pow_char_pow, hc, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by positivity)).mp h0)

end Special

section DicksonComponent

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem supportedBlock_le_orthogonalGroup_q (r : K[X]) :
    supportedBlock Q x r ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun _ hg =>
  (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer r hg)).1

theorem dicksonHom_blockComponent_eq_one (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (t : ∀ i : ↥Rep, ↥(supportedBlock Q x i))
    (ht : blockProduct hx hRep t ∈ orthDerived Q) (i₀ : ↥Rep) (hi₀ : (i₀ : K[X]) = X - 1) :
    dicksonHom Q hQ ⟨(t i₀ : V ≃ₗ[K] V), supportedBlock_le_orthogonalGroup_q _ (t i₀).2⟩ = 1 := by
  classical
  have hrange : ∀ u : ∀ i : ↥Rep, ↥(supportedBlock Q x i),
      blockProduct hx hRep u ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun u => by
    have : blockProduct hx hRep u ∈ (blockProduct hx hRep).range := ⟨u, rfl⟩
    rw [range_blockProduct] at this
    exact (Subgroup.mem_inf.mp this).1
  set φ₁ : (∀ i : ↥Rep, ↥(supportedBlock Q x i)) →* Multiplicative (ZMod 2) :=
    (dicksonHom Q hQ).comp ((blockProduct hx hRep).codRestrict _ hrange) with hφ₁
  set φ₂ : (∀ i : ↥Rep, ↥(supportedBlock Q x i)) →* Multiplicative (ZMod 2) :=
    (dicksonHom Q hQ).comp ((Subgroup.inclusion (supportedBlock_le_orthogonalGroup_q (Q := Q)
      (x := x) (i₀ : K[X]))).comp (Pi.evalMonoidHom (fun i : ↥Rep => ↥(supportedBlock Q x i)) i₀))
    with hφ₂
  have hφ : φ₁ = φ₂ := by
    refine MonoidHom.pi_ext fun i z => ?_
    have h1 : φ₁ (Pi.mulSingle i z) =
        dicksonHom Q hQ ⟨(z : V ≃ₗ[K] V), supportedBlock_le_orthogonalGroup_q _ z.2⟩ := by
      rw [hφ₁, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext (blockProduct_mulSingle hx hRep i z)
    rw [h1]
    by_cases hii : i = i₀
    · subst hii
      rw [hφ₂, MonoidHom.comp_apply, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext (by simp)
    · have hne1 : (i : K[X]) ≠ X - 1 := fun h => hii (Subtype.ext (h.trans hi₀.symm))
      have hev := hx.even_finrank_commSpace_of_mem_supportedBlock hp2 (hRep.1 i.2) hne1 z.2
      have h2 : φ₂ (Pi.mulSingle i z) = 1 := by
        rw [hφ₂, MonoidHom.comp_apply, MonoidHom.comp_apply]
        have h3 : (Pi.evalMonoidHom (fun i : ↥Rep => ↥(supportedBlock Q x i)) i₀)
            (Pi.mulSingle i z) = 1 := by
          simp [Pi.mulSingle_eq_of_ne (Ne.symm hii)]
        rw [h3, map_one, map_one]
      rw [h2, dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
      exact ZMod.natCast_eq_zero_iff_even.mpr hev
  have h1 : φ₁ t = 1 := dicksonHom_eq_one_of_mem_orthDerived hQ ht
  have h2 : φ₂ t = dicksonHom Q hQ ⟨(t i₀ : V ≃ₗ[K] V), supportedBlock_le_orthogonalGroup_q _ (t i₀).2⟩ :=
    rfl
  rw [← h2, ← hφ, h1]

end DicksonComponent

section FixedComponent

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem mem_fixedPart_of_twoElement [CharP K 2] (hK : 4 ≤ Nat.card K) (hx : OddOrderIsometry Q p x)
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x (X - 1)) {n : ℕ} (hgn : g ^ 2 ^ n = 1)
    (hδ : dicksonHom (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate
      ⟨restrictFixed Q x ⟨g, hg⟩, restrictFixed_mem_orthogonalGroup _⟩ = 1) :
    g ∈ (if 3 ≤ finrank K (fixedSpace x) then supportedFixedDerived Q x else ⊥) := by
  split_ifs with h3
  · exact mem_supportedFixedDerived.mpr
      ⟨hg, dicksonDerived_fixedSpace_of_four_le_card hK hx h3 _ hδ⟩
  · rw [Subgroup.mem_bot]
    have hgn' : (⟨g, hg⟩ : ↥(supportedBlock Q x (X - 1))) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using hgn)
    have hu := twoElt_eq_one_of_dickson_of_finrank_le_two hx.polarBilin_fixed_nondegenerate
      (by omega) hδ n (Subtype.ext (by
        change (restrictFixed Q x ⟨g, hg⟩) ^ 2 ^ n = 1
        rw [← map_pow, hgn', map_one]))
    have h1 : restrictFixed Q x ⟨g, hg⟩ = 1 := congrArg Subtype.val hu
    have h2 : (⟨g, hg⟩ : ↥(supportedBlock Q x (X - 1))) = 1 :=
      restrictFixed_injective hx (by rw [h1, map_one])
    exact congrArg Subtype.val h2

end FixedComponent

section Main

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_perfect_of_twoElement_projOrthDerived (hK : Nat.card K = 4)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {a : ProjOrthDerived Q} (ha : orderOf a = 3) {s : ProjOrthDerived Q}
    (hs : s ∈ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) {n : ℕ} (hsn : s ^ 2 ^ n = 1) :
    ∃ P : Subgroup (ProjOrthDerived Q), P ≤ Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) ∧
      ⁅P, P⁆ = P ∧ s ∈ P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    haveI := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hK4 : 4 ≤ Nat.card K := hK.ge
  haveI : Nontrivial V := by
    obtain ⟨U₀, hU₀, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by omega : 0 < 3) (hU₀ ▸ Submodule.finrank_le U₀))
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨-, hxp⟩, -, hcent⟩ := hlift 3 Nat.prime_three (by norm_num) a ha
  have hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three (by rw [hK2]; norm_num) hQ x hxp
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hp2 : Odd 3 := by decide
  rw [hcent] at hs
  obtain ⟨y, hyc, rfl⟩ := hs
  have hyn : y ^ 2 ^ n = 1 := piOrth_injective hQ (by rw [map_pow, map_one]; exact hsn)
  have hyM : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) := by
    refine Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup y.2, ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hyc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hyc
  have hyn' : (y : V ≃ₗ[K] V) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hyn
  obtain ⟨t, ht⟩ := exists_blockProduct_eq hx hRep hyM
  have htn : t ^ 2 ^ n = 1 :=
    blockProduct_injective hx hRep (by rw [map_pow, ht, hyn', map_one])
  have htin : ∀ i : ↥Rep, ((t i : V ≃ₗ[K] V)) ^ 2 ^ n = 1 := fun i => by
    have h1 : t i ^ 2 ^ n = 1 := by simpa using congrFun htn i
    simpa using congrArg Subtype.val h1
  set F₀ : Subgroup (V ≃ₗ[K] V) := if 3 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V))
    then supportedFixedDerived Q x else ⊥ with hF₀
  set P : ↥Rep → Subgroup (V ≃ₗ[K] V) := fun r =>
    if (r : K[X]) = X - 1 then F₀ else specialBlock Q x r with hP
  have hF₀B : F₀ ≤ supportedBlock Q x (X - 1) := by
    rw [hF₀]
    split_ifs
    · exact supportedFixedDerived_le_supportedBlock
    · exact bot_le
  have hPB : ∀ r : ↥Rep, P r ≤ supportedBlock Q x r := by
    intro r
    simp only [hP]
    split_ifs with h1
    · rw [h1]
      exact hF₀B
    · exact specialBlock_le_supportedBlock _
  have hPperf : ∀ r : ↥Rep, ⁅P r, P r⁆ = P r := by
    intro r
    simp only [hP]
    split_ifs with h1
    · rw [hF₀]
      split_ifs with h3
      · exact commutator_supportedFixedDerived_eq_of_four_le_card hK4 hx h3
      · exact Subgroup.commutator_bot_left _
    · exact commutator_specialBlock_eq_of_card_four_three hK hx (hRep.1 r.2) h1
  have htP : ∀ r : ↥Rep, ((t r : ↥(supportedBlock Q x r)) : V ≃ₗ[K] V) ∈ P r := by
    intro r
    simp only [hP]
    split_ifs with h1
    · have hg : ((t r : ↥(supportedBlock Q x r)) : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) := by
        rw [← h1]
        exact (t r).2
      have hδ := dicksonHom_blockComponent_eq_one hx hp2 hQ hRep t (by rw [ht]; exact y.2) r h1
      have hX : (X - 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap := by
        rw [← h1]
        exact hRep.1 r.2
      have hδW := hx.dicksonHom_eq_restrict_of_mem_supportedBlock hp2 hQ hX hg
      have hδ' : dicksonHom (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype)
          hx.polarBilin_fixed_nondegenerate
          ⟨restrictFixed Q x ⟨_, hg⟩, restrictFixed_mem_orthogonalGroup _⟩ = 1 :=
        hδW.symm.trans hδ
      exact mem_fixedPart_of_twoElement hK4 hx hg (htin r) hδ'
    · haveI : Fact (Irreducible (r : K[X])) := ⟨irreducible_of_mem_primaryFactors (hRep.1 r.2)⟩
      exact mem_specialBlock_of_pow_two_pow_eq_one (t r).2 (htin r)
  set P₀ : Subgroup (V ≃ₗ[K] V) := ⨆ r, P r with hP₀
  have hyP₀ : (y : V ≃ₗ[K] V) ∈ P₀ := by
    rw [← ht]
    exact blockProduct_mem hx hRep P₀ t fun r => le_iSup P r (htP r)
  have hP₀perf : ⁅P₀, P₀⁆ = P₀ := Inputs256p.commutator_iSup_eq_self_of_perfect P hPperf
  have hP₀M : P₀ ≤ isometryCentralizer Q x :=
    iSup_le fun r => (hPB r).trans (supportedBlock_le_isometryCentralizer _)
  have hP₀O : P₀ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    (Subgroup.mem_inf.mp (hP₀M hg)).1
  have hP₀Ω : P₀ ≤ orthDerived Q := by
    calc P₀ = ⁅P₀, P₀⁆ := hP₀perf.symm
      _ ≤ orthDerived Q := Subgroup.commutator_mono hP₀O hP₀O
  refine ⟨(P₀.subgroupOf (orthDerived Q)).map (piOrth Q), ?_, ?_, ?_⟩
  · rw [hcent]
    refine Subgroup.map_mono fun z hz => ?_
    have hzM := hP₀M (Subgroup.mem_subgroupOf.mp hz)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hzM).2)
  · have hsub : ⁅P₀.subgroupOf (orthDerived Q), P₀.subgroupOf (orthDerived Q)⁆ =
        P₀.subgroupOf (orthDerived Q) := by
      apply Subgroup.map_injective (orthDerived Q).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP₀Ω, hP₀perf]
    rw [← Subgroup.map_commutator, hsub]
  · exact ⟨y, Subgroup.mem_subgroupOf.mpr hyP₀, rfl⟩

end Main

section Models

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.KCOrthogonalAut

theorem exists_projOrthDerived_of_model_gf4 {G : Type} [Group G] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n : ℕ} (hG : StatedClassicalModel G t n 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ) (Q : QuadraticForm K (Fin d → K)),
      Nat.card K = 4 ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl
  · have hG0 := hG
    obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hG
    letI := hKf
    letI := hKfin
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hG0 K hK e
    have hd : 0 < 2 * n := by
      have := hadm.2.2
      omega
    exact ⟨K, hKf, hKfin, 2 * n, coordinateQuadPlus n K, by rw [hK]; norm_num, hnd, hT,
      ⟨(coordinatePlusWitnessEquiv K e).trans (coordBridge _ hd)⟩⟩
  · have hG0 := hG
    obtain ⟨hadm, K, hKf, hKfin, hK, b, c, hirr, ⟨e⟩⟩ := hG
    letI := hKf
    letI := hKfin
    obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hG0 K hK b c hirr e
    have hn1 : 1 ≤ n := by
      have := hadm.2.2
      omega
    have hd : 0 < 2 * n := by omega
    exact ⟨K, hKf, hKfin, 2 * n, coordinateQuadMinus n K hn1 b c, by rw [hK]; norm_num, hnd, hT,
      ⟨(coordinateMinusWitnessEquiv K hn1 b c e).trans (coordBridge _ hd)⟩⟩

theorem twoElement_mem_glaLayer_inner_omega_gf4 {G : Type} [Group G] {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n : ℕ} (hG : StatedClassicalModel G t n 2 2)
    (β : MulAut G) (hβ : orderOf β = 3) (hinn : β ∈ (MulAut.conj : G →* MulAut G).range)
    {s : G} (hs : β s = s) {m : ℕ} (hsm : s ^ 2 ^ m = 1) :
    s ∈ CFSG.Open.GLALayer (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) := by
  obtain ⟨K, hKf, hKfin, d, Q, hK, hQ, hT, ⟨E⟩⟩ := exists_projOrthDerived_of_model_gf4 ht hG
  letI := hKf
  letI := hKfin
  obtain ⟨b, rfl⟩ := hinn
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived Q) = ⊥ := b3Lie_center_eq_bot hnonab
  have hconj : MulAut.conj (E b) = MulAut.congr E (MulAut.conj b) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hEb : orderOf (E b) = 3 := by
    rw [← orderOf_injective _ (CFSG.mulAutConj_injective_of_center_eq_bot hZ) (E b), hconj,
      MulEquiv.orderOf_eq, hβ]
  have hb3 : b ^ 3 = 1 := by
    have h3 : orderOf b = 3 := by rw [← MulEquiv.orderOf_eq E b, hEb]
    rw [← h3]
    exact pow_orderOf_eq_one b
  have hsc : s ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [← Inputs256p.fixSubgroup_conj_eq_centralizer_gf4]
    exact CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.mpr hs
  have hEs : E s ∈ Subgroup.centralizer ({E b} : Set (ProjOrthDerived Q)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hsc ⊢
    rw [← map_mul, ← map_mul, hsc]
  have hEsm : (E s) ^ 2 ^ m = 1 := by rw [← map_pow, hsm, map_one]
  obtain ⟨P, hPc, hPperf, hsP⟩ :=
    exists_perfect_of_twoElement_projOrthDerived hK hQ hT hEb hEs hEsm
  have hle : P.map E.symm.toMonoidHom ≤
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj b) := by
    rw [Inputs256p.fixSubgroup_conj_eq_centralizer_gf4]
    rintro _ ⟨z, hz, rfl⟩
    have hzc := hPc hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hzc ⊢
    apply E.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hzc
  have hperf : ⁅P.map E.symm.toMonoidHom, P.map E.symm.toMonoidHom⁆ = P.map E.symm.toMonoidHom := by
    rw [← Subgroup.map_commutator, hPperf]
  have hPL := LieSemisimple.perfectInLayer_conj_omega
    (ht.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))) hG Nat.prime_three
    (by norm_num) (by norm_num) b hb3 (P.map E.symm.toMonoidHom) hle hperf
  exact hPL ⟨E s, hsP, by simp⟩

end Models

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256q

end
