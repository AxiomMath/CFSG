module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256f
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFieldExport
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4OddMinus
import CFSG.RankThree.PartOne.S11d.FixedFactsE6Tw

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Assembly.LowTwoRank

section QPerf

@[expose] def QPerf (q : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∀ s : S, β s = s → (∃ n : ℕ, s ^ q ^ n = 1) →
    ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ s ∈ P

theorem qGen_of_qPerf {T : Type} [Group T] {q : ℕ} {β : MulAut T}
    (hβ : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieCompsExport q β) (h : QPerf q β) :
    Inputs256e.QGen q β :=
  qGen_of_lieCompsExport hβ h

theorem qPerf_of_congr {S T : Type} [Group S] [Group T] {q : ℕ} (e : S ≃* T) {β : MulAut S}
    (h : QPerf q (MulAut.congr e β)) : QPerf q β := by
  intro s hs ⟨n, hn⟩
  have hs' : MulAut.congr e β (e s) = e s := by
    show e (β (e.symm (e s))) = e s
    rw [e.symm_apply_apply, hs]
  obtain ⟨P, hPC, hP, hsP⟩ := h (e s) hs' ⟨n, by rw [← map_pow, hn, map_one]⟩
  refine ⟨P.map (e.symm : T →* S), ?_, ?_, ⟨e s, hsP, e.symm_apply_apply s⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    have h1 : e (β (e.symm t)) = t := mem_fixSubgroup.1 (hPC ht)
    rw [mem_fixSubgroup]
    exact (e.eq_symm_apply).2 h1
  · rw [← Subgroup.map_commutator, hP]

theorem mem_of_isPGroup_two_quotient {G : Type*} [Group G] {J : Subgroup G} [J.Normal]
    (h2 : IsPGroup 2 (G ⧸ J)) {g : G} (hodd : Odd (orderOf g)) : g ∈ J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 (g : G ⧸ J)
  have hdvd : orderOf (g : G ⧸ J) ∣ orderOf g := orderOf_map_dvd (QuotientGroup.mk' J) g
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ orderOf g := (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact (QuotientGroup.eq_one_iff g).1 hk

theorem mem_of_isPGroup_two_quotient' {G : Type*} [Group G] {N J : Subgroup G} (hJN : J ≤ N)
    [(J.subgroupOf N).Normal] (h2 : IsPGroup 2 (↥N ⧸ J.subgroupOf N)) {g : G} (hg : g ∈ N)
    (hodd : Odd (orderOf g)) : g ∈ J := by
  have hodd' : Odd (orderOf (⟨g, hg⟩ : N)) := by rwa [← Subgroup.orderOf_coe]
  have := mem_of_isPGroup_two_quotient h2 hodd'
  rw [Subgroup.mem_subgroupOf] at this
  exact this

theorem odd_orderOf_of_pow {G : Type*} [Group G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {g : G}
    {n : ℕ} (hn : g ^ q ^ n = 1) : Odd (orderOf g) :=
  Odd.of_dvd_nat ((hq.odd_of_ne_two hq2).pow) (orderOf_dvd_of_pow_eq_one hn)

end QPerf

section OrthOuter

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

private theorem qPerf_fieldAutT (S : SubfieldSetup k Q₀ Q σ p) (hd0 : 0 < d) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : QPerf q (fieldAutT Q σ S.hQσ) := by
  obtain ⟨hsimp, hnonab⟩ := matrix_simple_nonabelian hd0 S.hnd₀ S.hT₀
  have hJq : CFSG.IsQuasisimple ↥(subfieldDerivedImage k S.hext) :=
    CFSG.IsQuasisimple.of_mulEquiv (inclEquiv k S.hext hd0).symm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hsimp
        hnonab)
  haveI hJn := subfieldDerivedImage_normal k S.hext
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  rintro s hs ⟨n, hn⟩
  have hsN : s ∈ subfieldFixedGroup k Q₀ Q := hfix ▸ mem_fixSubgroup.2 hs
  refine ⟨subfieldDerivedImage k S.hext, hfix ▸ subfieldDerivedImage_le k S.hext,
    commutator_self_of_perfect (Group.isPerfect_def.mp hJq.1), ?_⟩
  exact mem_of_isPGroup_two_quotient' (subfieldDerivedImage_le k S.hext) hquot hsN
    (odd_orderOf_of_pow hq hq2 hn)

private theorem qPerf_of_omegaFieldConj {G : Type} [Group G] {β : MulAut G} {ℓ q : ℕ}
    (h : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFieldConj G β ℓ p) (hq : q.Prime)
    (hq2 : q ≠ 2) : QPerf q β := by
  obtain ⟨K, _, _, k, d, Q₀, Q, σ, S, e, hd, -, he⟩ := h.out
  refine qPerf_of_congr e ?_
  rw [he]
  exact qPerf_fieldAutT S (by omega) hq hq2

theorem qGen_omega_outer {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] [Finite G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (hℓ2 : ℓ ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hD4 : t = .POmegaPlus → n = 4 → p ≠ 3) (β : MulAut G)
    (hβ : β ^ p = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) : Inputs256e.QGen ℓ β := by
  have hℓ : ℓ.Prime := by
    rcases ht with rfl | rfl | rfl
    · exact hG.1.1
    · exact hG.1.1
    · exact hG.1.1
  refine qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_omega_outer
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorFacts_holds hp hp2 ht hG hD4 β hβ hout)
    ?_
  have hc : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OmegaFieldConj G β ℓ p := by
    rcases ht with rfl | rfl | rfl
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_odd hp hp2 hG β hβ hout
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_plus hp hp2 hG (hD4 rfl) β
        hβ hout
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFieldConj_minus hp hp2 hG β hβ hout
  exact qPerf_of_omegaFieldConj hc hℓ hℓ2

end OrthOuter

section OrthBlocks

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

theorem eq_one_of_pow_char_pow {E : Type*} [Field E] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP E ℓ] {u : E}
    {n : ℕ} (hu : u ^ ℓ ^ n = 1) : u = 1 := by
  have h : (u - 1) ^ ℓ ^ n = 0 := by rw [sub_pow_char_pow, hu, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero n hℓ.out.ne_zero)).1 h)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem mem_specialBlock_of_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (hK : ringChar K = ℓ) {h : K[X]}
    [Fact (Irreducible h)] {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x h) {n : ℕ}
    (hn : g ^ ℓ ^ n = 1) : g ∈ specialBlock Q x h := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hK ▸ ringChar.charP K
  haveI : CharP (AdjoinRoot h) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective ℓ
  refine mem_specialBlock.mpr ⟨hg, eq_one_of_pow_char_pow (n := n) ?_⟩
  have e1 : (⟨g, hg⟩ : ↥(supportedBlock Q x h)) ^ ℓ ^ n = 1 := Subtype.ext (by simpa using hn)
  rw [← map_pow, e1, map_one]

theorem isQuasisimple_specialBlock_of_four_le (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (h4 : 4 ≤ Nat.card K) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) : CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  classical
  by_cases hself : h = reciprocalPolynomial h
  · have hp2' : Odd p := hp.odd_of_ne_two hp2
    have hirr := irreducible_of_mem_primaryFactors hh
    obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
      hx.exists_selfDual_hermitian hp2' hh hne1 hself
    have hd : finrank K (AdjoinRoot h) = 2 * d := by
      rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
    obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
    have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
      rw [hbar, frobPow_apply]
    let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
      LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
        (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
        (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
    have hBH : ∀ u w, B u w = H u w := fun u w => rfl
    have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
    have hBl : B.SeparatingLeft := by
      intro u hu
      refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
      have h1 := hH u ⟨w, hw⟩ 1
      rw [mul_one, one_smul] at h1
      have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
      rw [h2, map_zero] at h1
      exact h1.symm
    have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
      rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
      congr 1
      ext γ
      rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
      exact Iff.rfl
    have hd0 : 1 ≤ d := by
      have := Module.finrank_pos (R := K) (M := AdjoinRoot h)
      omega
    have hq4 : 4 ≤ ℓ ^ (f * d) := by
      have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq, pow_mul]
      have h2 : Nat.card K ≤ Nat.card K ^ d := Nat.le_self_pow (by omega) _
      omega
    let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
      (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
        (MulEquiv.subgroupCongr hrange)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hU hBsymm hBl
        hm ⟨fun _ => hq4, fun _ => by omega⟩)
  · have h4' : 4 ≤ Nat.card (AdjoinRoot h) :=
      h4.trans (Nat.card_le_card_of_injective _ (algebraMap K (AdjoinRoot h)).injective)
    let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
        (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
    let e₁ : ↥(specialBlock Q x h) ≃*
        SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
      MulEquiv.ofBijective (specialToSL Q x h)
        ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hself⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm)
      (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4')

theorem eq_one_of_pow_of_finrank_le_two {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W} (hR : R.polarBilin.Nondegenerate) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hK : ringChar K = ℓ) (hW : finrank K W ≤ 2)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)} {n : ℕ} (hg : g ^ ℓ ^ n = 1) :
    (g : W ≃ₗ[K] W) = 1 := by
  have hodd : Odd (ℓ ^ n) := (hℓ.odd_of_ne_two hℓ2).pow
  have hev := even_finrank_commSpace_of_dicksonHom_eq_one hR
    (dicksonHom_eq_one_of_pow_eq_one hR hodd hg)
  have hle : finrank K (commSpace (g : W ≃ₗ[K] W)) ≤ finrank K W := Submodule.finrank_le _
  have h0 : finrank K (commSpace (g : W ≃ₗ[K] W)) = 0 := by
    by_contra hne
    have h2 : finrank K (commSpace (g : W ≃ₗ[K] W)) = finrank K W := by
      obtain ⟨m, hm⟩ := hev
      omega
    have htop : commSpace (g : W ≃ₗ[K] W) = ⊤ := Submodule.eq_top_of_finrank_eq h2
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    haveI : CharP K ℓ := hK ▸ ringChar.charP K
    haveI : CharP (Module.End K W) ℓ :=
      charP_of_injective_algebraMap (algebraMap K (Module.End K W)).injective ℓ
    set N : Module.End K W := ((g : W ≃ₗ[K] W) : W →ₗ[K] W) - 1 with hNdef
    have hgn : ((g : W ≃ₗ[K] W) : W →ₗ[K] W) ^ ℓ ^ n = 1 := by
      have h1 : (g : W ≃ₗ[K] W) ^ ℓ ^ n = 1 := by
        have := congrArg Subtype.val hg
        simpa using this
      have h2 := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom h1
      rw [map_pow, map_one] at h2
      exact h2
    have hN : N ^ ℓ ^ n = 0 := by
      rw [hNdef, sub_pow_char_pow_of_commute ℓ n (Commute.one_right _), one_pow, hgn, sub_self]
    have hsurj : Function.Surjective N := LinearMap.range_eq_top.1 htop
    have hsurj' : Function.Surjective (N ^ ℓ ^ n) := by
      rw [Module.End.coe_pow]
      exact hsurj.iterate _
    rw [hN] at hsurj'
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨v, hv⟩ := hsurj' w
    exact hw (by rw [← hv]; rfl)
  have hbot : commSpace (g : W ≃ₗ[K] W) = ⊥ := Submodule.finrank_eq_zero.mp h0
  ext v
  have hv : (g : W ≃ₗ[K] W) v - v ∈ commSpace (g : W ≃ₗ[K] W) := sub_mem_commSpace _ v
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
  rw [hv, LinearEquiv.coe_one, id]

theorem mem_orthDerived_of_odd_orderOf {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate)
    (hodd : Odd (Nat.card K)) (h3 : 3 ≤ finrank K W) (hne : ¬ SmallFixedException R)
    {g : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) (hgo : Odd (orderOf g)) :
    g ∈ orthDerived R := by
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0
  · exact (CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR
      hT).2.2.2.2.2.2.1 g hg hgo
  · have hdim6 : finrank K W ≤ 6 := (finite_odd_quadratic_low_Witt_dimension_bound hodd R hR).2.2 hT
    have hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨ finrank K W = 5)) ∨
        (Odd (Nat.card K) ∧ finrank K W = 6 ∧
          ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) ∨
        (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) := by
      by_cases hd6 : finrank K W = 6
      · exact Or.inr (Or.inl ⟨hodd, hd6, hT⟩)
      · exact Or.inl ⟨hodd, by omega⟩
    obtain ⟨-, h2, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage R hR hcase
    obtain ⟨-, h2grp, -, -⟩ := h2 hne
    have hmem : (⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ∈
        commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
      refine mem_of_isPGroup_two_quotient h2grp ?_
      rwa [← Subgroup.orderOf_coe]
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact ⟨_, hmem, rfl⟩

end OrthBlocks

section OrthInner

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ClassicalGroups.Orthogonal (scalars)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem commutator_subgroupOf_eq' {G : Type*} [Group G] {H Ω : Subgroup G} (hH : H ≤ Ω)
    (hP : ⁅H, H⁆ = H) : ⁅H.subgroupOf Ω, H.subgroupOf Ω⁆ = H.subgroupOf Ω := by
  apply Subgroup.map_injective Ω.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hH, hP]

private theorem mem_of_supportedBlock_of_pow {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hKℓ : ringChar K = ℓ)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) {m : ℕ}
    (F : Fin m → Subgroup (V ≃ₗ[K] V))
    (hFsup : FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) (P₀ : Subgroup (V ≃ₗ[K] V))
    (hFP : ∀ i, F i ≤ P₀)
    (hSP : ∀ r : ↥Rep, (r : K[X]) ≠ X - 1 → CFSG.IsQuasisimple ↥(specialBlock Q x r) →
      specialBlock Q x r ≤ P₀)
    (r : ↥Rep) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x r) {k : ℕ} (hk : g ^ ℓ ^ k = 1) :
    g ∈ P₀ := by
  have hℓ2 : ℓ ≠ 2 := by omega
  obtain ⟨j, hj, hKcard⟩ := Inputs256e.exists_card_eq_pow hℓ hKℓ
  have hK5 : 5 ≤ Nat.card K := by
    rw [hKcard]
    exact h5.trans (Nat.le_self_pow (by omega) ℓ)
  have hoddK : Odd (Nat.card K) := by
    rw [hKcard]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  haveI : Fact (Irreducible (r : K[X])) := ⟨irreducible_of_mem_primaryFactors (hRep.1 r.2)⟩
  by_cases hr1 : (r : K[X]) = X - 1
  · have hg' : g ∈ supportedBlock Q x (X - 1) := hr1 ▸ hg
    have hwO : restrictFixed Q x ⟨g, hg'⟩ ∈
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
      rw [← isometryRestrictFixed_restrictFixed]
      exact isometryRestrictFixed_mem_orthogonalGroup _
    have hwk : restrictFixed Q x ⟨g, hg'⟩ ^ ℓ ^ k = 1 := by
      rw [← map_pow]
      have : (⟨g, hg'⟩ : ↥(supportedBlock Q x (X - 1))) ^ ℓ ^ k = 1 :=
        Subtype.ext (by simpa using hk)
      rw [this, map_one]
    by_cases hlist : FixedLayerListed Q x
    · have hwΩ : restrictFixed Q x ⟨g, hg'⟩ ∈ orthDerived (Q.comp (fixedSpace x).subtype) :=
        mem_orthDerived_of_odd_orderOf _ hx.polarBilin_fixed_nondegenerate hoddK hlist.1 hlist.2
          hwO (odd_orderOf_of_pow hℓ hℓ2 hwk)
      have hgS : g ∈ supportedFixedDerived Q x := mem_supportedFixedDerived.mpr ⟨hg', hwΩ⟩
      rw [← hFsup hlist] at hgS
      exact (iSup_le hFP) hgS
    · have hdim : finrank K (fixedSpace x) ≤ 2 := by
        by_contra h3
        refine hlist ⟨by omega, fun hS => ?_⟩
        rcases hS with ⟨-, h⟩ | ⟨-, h | h⟩ <;> omega
      have hw1 : restrictFixed Q x ⟨g, hg'⟩ = 1 :=
        eq_one_of_pow_of_finrank_le_two hx.polarBilin_fixed_nondegenerate hℓ hℓ2 hKℓ hdim
          (g := ⟨restrictFixed Q x ⟨g, hg'⟩, hwO⟩) (n := k) (Subtype.ext (by simpa using hwk))
      rw [hx.eq_one_of_restrictFixed_eq_one hg' hw1]
      exact one_mem _
  · have hgS := mem_specialBlock_of_pow (Q := Q) (x := x) hℓ hKℓ hg hk
    have hpos := hx.primaryMultiplicity_pos (hRep.1 r.2)
    by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap (r : K[X])
    · exact hSP r hr1 (isQuasisimple_specialBlock_of_four_le hx hp hp2 (by omega) (hRep.1 r.2) hr1 hm)
        hgS
    · rw [hx.specialBlock_eq_bot_of_finrank_eq_one (hRep.1 r.2) (by omega)] at hgS
      rw [Subgroup.mem_bot.1 hgS]
      exact one_mem _

theorem exists_perfect_isometryCentralizer {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2 : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) (hKℓ : ringChar K = ℓ) :
    ∃ P₀ : Subgroup (V ≃ₗ[K] V), P₀ ≤ orthDerived Q ∧ P₀ ≤ isometryCentralizer Q x ∧ ⁅P₀, P₀⁆ = P₀ ∧
      ∀ y ∈ isometryCentralizer Q x, (∃ n : ℕ, y ^ ℓ ^ n = 1) → y ∈ P₀ := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨m, F, hF, hFsup, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixedFactors hx
  let ι₁ := {r : ↥Rep // (r : K[X]) ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q x r)}
  let Fam : Fin m ⊕ ι₁ → Subgroup (V ≃ₗ[K] V) := Sum.elim F (fun r => specialBlock Q x r.1)
  have hFamq : ∀ i, CFSG.IsQuasisimple ↥(Fam i) := by
    rintro (i | r)
    · exact (hF i).1
    · exact r.2.2
  have hFamΩ : ∀ i, Fam i ≤ orthDerived Q := by
    rintro (i | r)
    · exact (hF i).2.1.trans hx.supportedFixedDerived_le_orthDerived
    · exact specialBlock_le_orthDerived_of_perfect r.2.2.1
        ((specialBlock_le_isometryCentralizer _).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hFamM : ∀ i, Fam i ≤ isometryCentralizer Q x := by
    rintro (i | r)
    · exact (hF i).2.1.trans supportedFixedDerived_le_isometryCentralizer
    · exact specialBlock_le_isometryCentralizer _
  refine ⟨⨆ i, Fam i, iSup_le hFamΩ, iSup_le hFamM,
    commutator_iSup_eq Fam fun i => commutator_self_of_perfect (Group.isPerfect_def.mp (hFamq i).1),
    fun y hy ⟨n, hn⟩ => ?_⟩
  rw [← hx.blocks_iSup_eq hRep] at hy
  exact mem_of_mem_iSup_commute hℓ (fun r : ↥Rep => supportedBlock Q x r)
    (fun i j hij a ha b hb => hx.blocks_commute hRep hij a b ha hb) _
    (fun r g hg ⟨k, hk⟩ => mem_of_supportedBlock_of_pow hx hp hp2 hℓ h5 hKℓ hRep F hFsup _
      (fun i => le_iSup Fam (Sum.inl i))
      (fun r hr1 hq => le_iSup Fam (Sum.inr ⟨r, hr1, hq⟩)) r hg hk) hy hn

theorem qPerf_conj_projOrth (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h5 : 5 ≤ ℓ) (hKℓ : ringChar K = ℓ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ℓ)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) : QPerf ℓ (MulAut.conj a) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hℓ2 : ℓ ≠ 2 := by omega
  obtain ⟨-, hcenter, hZ2, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift p hp hp2 a ha
  subst hxa
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [hKℓ]; exact hpl) hQ x hxp
  obtain ⟨P₀, hP₀Ω, hP₀M, hP₀perf, hP₀gen⟩ :=
    exists_perfect_isometryCentralizer hx hp hp2 hℓ h5 hKℓ
  have hker : (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker ≤
      Subgroup.center ↥(orthDerived Q) := by
    rw [QuotientGroup.ker_mk', hcenter]
  have hcop : Nat.Coprime
      (Nat.card (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker) ℓ := by
    rw [QuotientGroup.ker_mk']
    have h1 := Nat.card_pos (α := ↥((scalars K V).subgroupOf (orthDerived Q)))
    rcases (show Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) = 1 ∨
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) = 2 by omega) with h | h
    · rw [h]
      exact Nat.coprime_one_left ℓ
    · rw [h]
      exact (Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm hℓ2)
  rintro s hs ⟨n, hn⟩
  obtain ⟨y, rfl, hy, hyn⟩ := exists_fixed_lift
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) (QuotientGroup.mk'_surjective _)
    hker hcop (MulAut.conj x) (MulAut.conj (QuotientGroup.mk' _ x))
    (fun g => by rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]) hs hn
  have hyx : y * x = x * y := by
    have h1 : x * y * x⁻¹ = y := hy
    calc y * x = (x * y * x⁻¹) * x := by rw [h1]
      _ = x * y := by group
  have hyM : (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup y.2,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyx)⟩
  have hyn' : (y : V ≃ₗ[K] V) ^ ℓ ^ n = 1 := by
    have := congrArg Subtype.val hyn
    simpa using this
  have hyP : (y : V ≃ₗ[K] V) ∈ P₀ := hP₀gen _ hyM ⟨n, hyn'⟩
  refine ⟨(P₀.subgroupOf (orthDerived Q)).map
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))), ?_, ?_, ⟨y, hyP, rfl⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hzM : (z : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) := hP₀M hz
    have hzx : z * x = x * z :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hzM).2)
    have hconj : x * z * x⁻¹ = z := by rw [← hzx, mul_inv_cancel_right]
    have h1 := congrArg (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) hconj
    rw [map_mul, map_mul, map_inv] at h1
    rw [mem_fixSubgroup, MulAut.conj_apply]
    exact h1
  · rw [← Subgroup.map_commutator, commutator_subgroupOf_eq' hP₀Ω hP₀perf]

end OrthInner

section Assembly

open CFSG.RankThree.Classical2 (ProjOrthDerived)

theorem orderOf_conj_of_center_eq_bot {T : Type*} [Group T] (hZ : Subgroup.center T = ⊥) (t : T) :
    orderOf (MulAut.conj t) = orderOf t := by
  refine orderOf_injective MulAut.conj (fun a b hab => ?_) t
  have hc : a⁻¹ * b ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut T => φ g) hab
    simp only [MulAut.conj_apply] at h1
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h1]
      _ = a⁻¹ * b * g := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc

@[expose] def QGenD4Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {ℓ f : ℕ}, StatedClassicalModel G .POmegaPlus 4 ℓ f → 5 ≤ ℓ →
    ∀ β : MulAut G, orderOf β = 3 → (∀ a : G, MulAut.conj a ≠ β) → Inputs256e.QGen ℓ β

theorem qGen_omega {t : StatedLieTag} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) (h5 : 5 ≤ ℓ) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hD4 : QGenD4Three) (β : MulAut G)
    (hβ : orderOf β = p) : Inputs256e.QGen ℓ β := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hKℓ, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_projOrth_model ht hG
  have hℓ : ℓ.Prime := by
    rcases ht with rfl | rfl | rfl
    · exact hG.1.1
    · exact hG.1.1
    · exact hG.1.1
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite G := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived Q) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnonab
  have hβp : β ^ p = 1 := by rw [← hβ]; exact pow_orderOf_eq_one β
  by_cases hin : ∃ a : G, MulAut.conj a = β
  · obtain ⟨a, rfl⟩ := hin
    have hc : MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    have hea : orderOf (e a) = p := by
      rw [← orderOf_conj_of_center_eq_bot hZ, ← hc, orderOf_congr, hβ]
    have hap : a ^ p = 1 := by
      have h1 : (e a) ^ p = 1 := by rw [← hea]; exact pow_orderOf_eq_one _
      exact (map_eq_one_iff e e.injective).1 (by rw [map_pow]; exact h1)
    refine qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsExport_conj_omega
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorFacts_holds hp hp2 ht hG hpℓ a hap)
      ?_
    refine qPerf_of_congr e ?_
    rw [hc]
    exact qPerf_conj_projOrth hQ hT hℓ h5 hKℓ hp hp2 hpℓ (e a) hea
  · have hout : ∀ a : G, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    by_cases h43 : t = .POmegaPlus ∧ n = 4 ∧ p = 3
    · obtain ⟨rfl, rfl, rfl⟩ := h43
      exact hD4 G hG h5 β hβ hout
    · exact qGen_omega_outer ht hG (by omega) hp hp2 (fun h1 h2 h3 => h43 ⟨h1, h2, h3⟩) β hβp hout

theorem qGenOrth_of_d4Three (hD4 : QGenD4Three) : QGenOrth := by
  rintro ⟨d, hv⟩ hd hd5 p hp hp2 hpd β hβ
  rcases hd with ⟨r, Q, hdr, hr3⟩ | ⟨r, Q, hdr⟩ | ⟨r, Q, hdr⟩
  · change d = TauCeti.LieTypeIndex.B r Q at hdr
    subst hdr
    have hQc : (TauCeti.LieTypeIndex.B r Q).characteristic = Q.p :=
      TauCeti.LieTypeIndex.characteristic_B r Q
    change 5 ≤ (TauCeti.LieTypeIndex.B r Q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.B r Q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.B r Q).characteristic β
    rw [hQc] at hd5 hpd ⊢
    exact qGen_omega (Or.inl rfl) (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r Q hv
      (by omega) hr3 (MulEquiv.refl _)) hd5 hp hp2 hpd hD4 β hβ
  · change d = TauCeti.LieTypeIndex.D r Q at hdr
    subst hdr
    have hQc : (TauCeti.LieTypeIndex.D r Q).characteristic = Q.p :=
      TauCeti.LieTypeIndex.characteristic_D r Q
    change 5 ≤ (TauCeti.LieTypeIndex.D r Q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.D r Q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.D r Q).characteristic β
    rw [hQc] at hd5 hpd ⊢
    exact qGen_omega (Or.inr (Or.inl rfl)) (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r Q
      hv (MulEquiv.refl _)) hd5 hp hp2 hpd hD4 β hβ
  · change d = TauCeti.LieTypeIndex.twistedD r Q at hdr
    subst hdr
    have hQc : (TauCeti.LieTypeIndex.twistedD r Q).characteristic = Q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedD r Q
    change 5 ≤ (TauCeti.LieTypeIndex.twistedD r Q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.twistedD r Q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.twistedD r Q).characteristic β
    rw [hQc] at hd5 hpd ⊢
    exact qGen_omega (Or.inr (Or.inr rfl)) (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD
      r Q hv (MulEquiv.refl _)) hd5 hp hp2 hpd hD4 β hβ

theorem qGenSympOrth_of_d4Three (hD4 : QGenD4Three) : Inputs256e.QGenSympOrth :=
  qGenSympOrth_of_orth (qGenOrth_of_d4Three hD4)

end Assembly

section D4Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.RecipeExcLang CFSG.RankThree.Chevalley CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (CompsFine CompsFine.of_mulEquiv)
open CFSG.PGLModel (projImage)
open scoped Pointwise

private def QElemNormal (q : ℕ) (C : Type) [Group C] : Prop :=
  ∃ J : Subgroup C, J.Normal ∧ CFSG.IsQuasisimple ↥J ∧ ∀ c : C, (∃ n : ℕ, c ^ q ^ n = 1) → c ∈ J

private def FixGood (q : ℕ) (C : Type) [Group C] : Prop := CompsFine q C ∧ QElemNormal q C

private theorem qElemNormal_of_mulEquiv {q : ℕ} {C C' : Type} [Group C] [Group C'] (e : C ≃* C')
    (h : QElemNormal q C') : QElemNormal q C := by
  obtain ⟨J, hJn, hJq, hJ⟩ := h
  refine ⟨J.map (e.symm : C' →* C), hJn.map _ e.symm.surjective,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.symm.subgroupMap J) hJq, fun c ⟨n, hn⟩ => ?_⟩
  exact ⟨e c, hJ (e c) ⟨n, by rw [← map_pow, hn, map_one]⟩, e.symm_apply_apply c⟩

private theorem fixGood_of_mulEquiv {q : ℕ} {C C' : Type} [Group C] [Group C'] (e : C ≃* C')
    (h : FixGood q C') : FixGood q C :=
  ⟨h.1.of_mulEquiv e, qElemNormal_of_mulEquiv e h.2⟩

private theorem qElemNormal_of_isQuasisimple {q : ℕ} {C : Type} [Group C] (h : CFSG.IsQuasisimple C) :
    QElemNormal q C :=
  ⟨⊤, inferInstance, CFSG.IsQuasisimple.of_mulEquiv Subgroup.topEquiv h, fun c _ => Subgroup.mem_top c⟩

private theorem qGen_of_fixGood {S : Type} [Group S] {q : ℕ} {β : MulAut S}
    (h : FixGood q ↥(fixSubgroup β)) : Inputs256e.QGen q β := by
  obtain ⟨hc, J, hJn, hJq, hJ⟩ := h
  haveI := hJn
  have hJc : IsComponentOf J (⊤ : Subgroup ↥(fixSubgroup β)) :=
    ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hJq⟩
  obtain ⟨⟨X, _, _, hX, f, hf, hfk⟩, -⟩ := hc J hJc
  obtain ⟨e₀⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hX.perfect f hf hfk
  let eJ : ↥J ≃* ↥(J.map (fixSubgroup β).subtype) :=
    J.equivMapOfInjective (fixSubgroup β).subtype (fixSubgroup β).subtype_injective
  have hJ'C : J.map (fixSubgroup β).subtype ≤ fixSubgroup β := Subgroup.map_subtype_le J
  have hJ'sub : (J.map (fixSubgroup β).subtype).subgroupOf (fixSubgroup β) = J :=
    Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective J
  have hJ'n : ((J.map (fixSubgroup β).subtype).subgroupOf (fixSubgroup β)).Normal := by
    rw [hJ'sub]; exact hJn
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q
      (↥(J.map (fixSubgroup β).subtype) ⧸ Subgroup.center ↥(J.map (fixSubgroup β).subtype)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_congr
      (e₀.trans (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ))) hX.chev
  have hIs : Inputs256e.IsChevSub q β (J.map (fixSubgroup β).subtype) :=
    ⟨IsSubnormal.step hJ'C hJ'n (IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq), hchev⟩
  intro s hs ⟨n, hn⟩
  have hsJ : (⟨s, hs⟩ : ↥(fixSubgroup β)) ∈ J := hJ ⟨s, hs⟩ ⟨n, Subtype.ext (by simpa using hn)⟩
  exact le_iSup₂_of_le (f := fun (J : Subgroup S) (_ : Inputs256e.IsChevSub q β J) => J)
    (J.map (fixSubgroup β).subtype) hIs le_rfl ⟨⟨s, hs⟩, hsJ, rfl⟩

private theorem fixGood_of_conj_eq {q : ℕ} {Y : Type} [Group Y] {α δ : MulAut Y} (ψ : MulAut Y)
    (hψ : ψ * α * ψ⁻¹ = δ) (h : FixGood q ↥(fixSubgroup δ)) : FixGood q ↥(fixSubgroup α) := by
  rw [← hψ] at h
  exact fixGood_of_mulEquiv (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupConjEquiv ψ α) h

private theorem fixGood_of_conj_inv_eq {q : ℕ} {Y : Type} [Group Y] {α δ : MulAut Y} (ψ : MulAut Y)
    (hψ : ψ * α⁻¹ * ψ⁻¹ = δ) (h : FixGood q ↥(fixSubgroup δ)) : FixGood q ↥(fixSubgroup α) := by
  have h1 := fixGood_of_conj_eq ψ hψ h
  exact fixGood_of_mulEquiv (MulEquiv.subgroupCongr
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq α).symm) h1

private theorem mem_of_pow_mem_of_coprime' {G : Type} [Group G] {H : Subgroup G} {y : G} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hy : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast y a, ← zpow_natCast y b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [hy]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

private theorem mul_pow_mem_of_mem_normalizer' {G : Type} [Group G] {N : Subgroup G} {t n : G}
    (ht : t ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N) (m : ℕ) :
    (t ^ m)⁻¹ * (t * n) ^ m ∈ N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (t ^ (m + 1))⁻¹ * (t * n) ^ (m + 1) =
        ((t⁻¹ * ((t ^ m)⁻¹ * (t * n) ^ m) * t) * n) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    refine mul_mem ?_ hn
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem ht) _).1 ih
    simpa using h1

private theorem mem_projImage_slPi_of_pow {π : Bool} {p f : ℕ} {F : Type} [Field F]
    (hF : Sec4.PiField π p f F) {x : ↥(projImage (Sec4.glPi π 3 (p ^ f) F))} {n : ℕ}
    (hx : x ^ p ^ n = 1) : (x : Matrix.ProjGenLinGroup (Fin 3) F) ∈ projImage (Sec4.slPi π 3 (p ^ f) F) := by
  classical
  haveI := hF.finite
  have hp := hF.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F := fun h => by
    subst h; exact hF.unitary
  have hcharF : ringChar F = p := by
    haveI := Fintype.ofFinite F
    have hcard : Fintype.card F = p ^ (cond π f (2 * f)) := by
      rw [← Nat.card_eq_fintype_card, hF.card]
      cases π
      · simp [Sec4.piCard, ← pow_mul, mul_comm]
      · simp [Sec4.piCard]
    haveI : CharP F p := charP_of_card_eq_prime_pow hcard
    exact ringChar.eq F p
  let ρ : ↥(Sec4.glPi π 3 (p ^ f) F) →* ↥(projImage (Sec4.glPi π 3 (p ^ f) F)) :=
    (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _).subgroupMap (Sec4.glPi π 3 (p ^ f) F)
  have hρ : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
  haveI : Finite (GL (Fin 3) F) := inferInstance
  have hcop : Nat.Coprime (Nat.card ρ.ker) p := by
    refine Inputs256e.coprime_card_of_pow_eq_one hp (Inputs256e.coprime_card_units hp hcharF)
      fun z hz => ?_
    have h1 : Matrix.ProjGenLinGroup.mk ((z : ↥(Sec4.glPi π 3 (p ^ f) F)) : GL (Fin 3) F) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hz)
    have h2 := Matrix.ProjGenLinGroup.mk_eq_one.1 h1
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
    obtain ⟨c, hc⟩ := h2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← hc, ← map_pow, pow_card_eq_one', map_one]
    rfl
  obtain ⟨y, hyx, hyn⟩ := Inputs256e.exists_pow_lift ρ hρ hcop hx
  have hdet : Matrix.GeneralLinearGroup.det ((y : ↥(Sec4.glPi π 3 (p ^ f) F)) : GL (Fin 3) F) = 1 := by
    refine Inputs256e.eq_one_of_coprime_card (Inputs256e.coprime_card_units hp hcharF) (n := n) ?_
    rw [← map_pow]
    have : ((y : ↥(Sec4.glPi π 3 (p ^ f) F)) : GL (Fin 3) F) ^ p ^ n = 1 := by
      have := congrArg Subtype.val hyn
      simpa using this
    rw [this, map_one]
  have hyS : ((y : ↥(Sec4.glPi π 3 (p ^ f) F)) : GL (Fin 3) F) ∈ Sec4.slPi π 3 (p ^ f) F := by
    rw [Sec4.mem_slPi_iff hπ]
    refine ⟨y.2, ?_⟩
    have := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  rw [← hyx]
  exact ⟨_, hyS, rfl⟩

section FieldAut


variable {F : Type} [Field F] [Finite F]

private theorem torus_pow_card_sub_one {τ : Tag} {t : ModGL τ F} (ht : t ∈ torusGroup τ F) :
    t ^ (Nat.card F - 1) = 1 := by
  obtain ⟨c, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_torusGroup_iff_cartanChar.1 ht
  have h1 : (cartanChar c) ^ (Nat.card F - 1) = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
    exact pow_card_eq_one'
  have h2 := map_pow (rootDiagUnitHom τ F) (cartanChar c) (Nat.card F - 1)
  rw [h1, map_one] at h2
  exact h2.symm

private theorem qElemNormal_entrywiseAdjointAut (τ : Tag) {ℓ : ℕ} (hℓ : ℓ.Prime) (hFℓ : ringChar F = ℓ)
    (σ : F ≃+* F) (hG2 : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ)) :
    QElemNormal ℓ ↥(fixSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  haveI : Finite (ModGL τ F) := finite_modGL
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨-, hinj, -, hJΓ, hΓeq, hJnormal, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup τ F σ
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup τ
    (fixSubfield σ) hG2
  obtain ⟨hs, hnc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect
    τ (fixSubfield σ) hperf
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ F := fun g hg => (hJΓ hg).1
  have hΓnorm : entrywiseFixedGroup τ σ ≤
      Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ F)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 hJnormal
  have hfix : ∀ x : adjointGroup τ F,
      x ∈ fixSubgroup (entrywiseAdjointAut τ σ) ↔ (x : ModGL τ F) ∈ entrywiseFixedGroup τ σ := fun x => by
    rw [mem_fixSubgroup, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨x.2, (coe_entrywiseAdjointAut τ σ x).symm.trans (congrArg Subtype.val h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ x).trans h)
  set C := fixSubgroup (entrywiseAdjointAut τ σ) with hCdef
  let J₀ : Subgroup ↥(adjointGroup τ F) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ F)
  have hJ₀C : J₀ ≤ C := fun x hx => (hfix x).2 (hJΓ hx)
  let J : Subgroup ↥C := J₀.subgroupOf C
  have hJmem : ∀ c : ↥C, c ∈ J ↔
      (((c : adjointGroup τ F) : ModGL τ F)) ∈ fixedFieldImage τ σ := fun c => Iff.rfl
  refine ⟨J, ⟨fun j hj c => ?_⟩, ?_, fun c ⟨n, hn⟩ => ?_⟩
  · rw [hJmem] at hj ⊢
    have hcΓ := (hfix c.1).1 c.2
    have h1 := (Subgroup.mem_normalizer_iff.1 (hΓnorm hcΓ) _).1 hj
    simpa using h1
  · let e₃ : ↥(adjointGroup τ (fixSubfield σ)) ≃* ↥(fixedFieldImage τ σ) :=
      (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ hinj
    let eJ : ↥J ≃* ↥(adjointGroup τ (fixSubfield σ)) :=
      ((Subgroup.subgroupOfEquivOfLe hJ₀C).trans (Subgroup.subgroupOfEquivOfLe hJC)).trans e₃.symm
    exact CFSG.IsQuasisimple.of_mulEquiv eJ
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc)
  · set y : ModGL τ F := ((c : adjointGroup τ F) : ModGL τ F) with hy
    have hyΓ : y ∈ entrywiseFixedGroup τ σ := (hfix c.1).1 c.2
    have hyn : y ^ ℓ ^ n = 1 := by
      have h1 := congrArg (fun z : ↥C => (((z : adjointGroup τ F) : ModGL τ F))) hn
      simpa using h1
    have hyset : y ∈ (entrywiseFixedTorus τ σ : Set (ModGL τ F)) *
        (fixedFieldImage τ σ : Set (ModGL τ F)) := by
      rw [← hΓeq]
      exact hyΓ
    obtain ⟨t, ht, j, hj, htj⟩ := hyset
    have htT : t ∈ torusGroup τ F := (Subgroup.mem_inf.1 ht).1
    have htΓ : t ∈ entrywiseFixedGroup τ σ := (Subgroup.mem_inf.1 ht).2
    have hN : y ^ (Nat.card F - 1) ∈ fixedFieldImage τ σ := by
      have h1 := mul_pow_mem_of_mem_normalizer' (hΓnorm htΓ) hj (Nat.card F - 1)
      rw [torus_pow_card_sub_one htT, inv_one, one_mul] at h1
      have htj' : t * j = y := htj
      rw [htj'] at h1
      exact h1
    have hcop : Nat.Coprime (Nat.card F - 1) (ℓ ^ n) := by
      rw [← Nat.card_units]
      exact Nat.Coprime.pow_right n (Inputs256e.coprime_card_units hℓ hFℓ)
    rw [hJmem]
    exact mem_of_pow_mem_of_coprime' hcop hN (by rw [hyn]; exact one_mem _)

end FieldAut


private theorem fixGood_projImage_glPi {π : Bool} {p f : ℕ} {F : Type} [Field F]
    (hF : Sec4.PiField π p f F) (hq5 : 5 ≤ p ^ f) : FixGood p ↥(projImage (Sec4.glPi π 3 (p ^ f) F)) := by
  classical
  haveI := hF.finite
  have hq2 : 2 < p ^ f := by omega
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F := fun h => by
    subst h; exact hF.unitary
  have hSP : projImage (Sec4.slPi π 3 (p ^ f) F) ≤ projImage (Sec4.glPi π 3 (p ^ f) F) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  refine ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsFine_projImage_glPi hF (fun _ => hq2),
    (projImage (Sec4.slPi π 3 (p ^ f) F)).subgroupOf (projImage (Sec4.glPi π 3 (p ^ f) F)), ?_, ?_,
    fun c ⟨n, hn⟩ => mem_projImage_slPi_of_pow hF hn⟩
  · rw [Subgroup.normal_subgroupOf_iff hSP]
    rintro _ _ ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩
    refine ⟨x * y * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    simp only [SetLike.mem_coe] at hy hx ⊢
    rw [Sec4.mem_slPi_iff hπ] at hy ⊢
    refine ⟨mul_mem (mul_mem hx hy.1) (inv_mem hx), ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hy.2, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  · have hs := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hF hq2
    have hperf := CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hF hq2
    haveI := hs
    exact CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSP)
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs
        (CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf))

variable {F : Type} [Field F] [Finite F]

private theorem fixGood_entrywiseAdjointAut_D4 {ℓ : ℕ} (hℓ : ℓ.Prime) (hFℓ : ringChar F = ℓ)
    (σ : F ≃+* F) : FixGood ℓ ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)) := by
  classical
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup .D4
    (fixSubfield σ) (fun h => absurd h (by decide))
  obtain ⟨hs, hnc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect
    .D4 (fixSubfield σ) hperf
  obtain ⟨hChev, hA6⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isChevSimple_adjointGroup_D4
    (K := fixSubfield σ)
  have hring : ringChar (fixSubfield σ) = ℓ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_subfield hFℓ (fixSubfield σ)
  rw [hring] at hChev
  exact ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsFine_fixSubgroup_entrywiseAdjointAut .D4 σ
    hs hnc hChev hA6, qElemNormal_entrywiseAdjointAut .D4 hℓ hFℓ σ (fun h => absurd h (by decide))⟩

private theorem fixGood_twistedEntrywiseAut_D4 {ℓ e : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (he : 1 ≤ e)
    (hK : Nat.card F = ℓ ^ (e * 3)) (T : F ≃+* F) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ)
    (hj : j % 3 = 1 ∨ j % 3 = 2) : FixGood ℓ ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
  classical
  refine ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsFine_fixSubgroup_twistedEntrywiseAut_D4 he hK
    T hT j hj, ?_⟩
  have : Fintype F := Fintype.ofFinite F
  have hq3 : ∀ c : F, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← pow_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul, show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
    have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
    intro c
    rw [h1, pow_two]
    change T (T c) = _
    rw [hT, hT, ← pow_mul, sq]
  have hper : twistedEntrywiseAut TwistTag.D4 j T = twistedEntrywiseAut TwistTag.D4 (j % 3) T := by
    have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
    rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
      change j % 3 + j / 3 * 3 = j
      omega] at h
    exact h
  rw [hper]
  rcases hj with h | h
  · rw [h]
    obtain ⟨hs, hnc, ⟨eF⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_twistedOne_equiv
      he hK T 1 (Or.inl rfl) (fun c => by rw [hT, pow_one])
    haveI := hs
    exact qElemNormal_of_mulEquiv eF (qElemNormal_of_isQuasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc))
  · rw [h]
    have hfix := fixedSubgroup_twistedEntrywiseAut_D4_two T
    obtain ⟨hs, hnc, ⟨eF⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_twistedOne_equiv
      he hK T⁻¹ 2 (Or.inr rfl) hinv
    haveI := hs
    exact qElemNormal_of_mulEquiv ((MulEquiv.subgroupCongr hfix).trans eF) (qElemNormal_of_isQuasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc))

private theorem fixGood_d4_graph {ℓ f : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hF : Nat.card F = ℓ ^ f) {α : MulAut ↥(adjointGroup Tag.D4 F)} (hα3 : α ^ 3 = 1)
    (hαT : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) :
    FixGood ℓ ↥(fixSubgroup α) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : CharP F ℓ := by
    haveI := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hFℓ : ringChar F = ℓ := ringChar.eq F ℓ
  have hF5 : 5 ≤ Nat.card F := by
    rw [hF]
    exact h5.trans (Nat.le_self_pow (by omega) ℓ)
  rcases CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3.isG2Type_or_isA2Type
      (by rw [hFℓ]; omega) hα3 hαT with ⟨ψ, hψ | hψ⟩ | ⟨ψ, B, hB3, hB1, hψ | hψ⟩
  · refine fixGood_of_conj_eq ψ hψ ⟨?_, qElemNormal_of_isQuasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_fixSubgroup_d4Graph_one
        (by omega))⟩
    exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsFine_adjointGroup_G2 hFℓ).of_mulEquiv
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2 F (by omega))
  · refine fixGood_of_conj_eq ψ hψ ?_
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_d4Graph_two]
    refine ⟨?_, qElemNormal_of_isQuasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_fixSubgroup_d4Graph_one
        (by omega))⟩
    exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsFine_adjointGroup_G2 hFℓ).of_mulEquiv
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2 F (by omega))
  all_goals
    obtain ⟨π, p, f', F', _, hF', hpf, -, ⟨eP⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds F
        (by rw [hFℓ]; omega) (by rw [hFℓ]; omega) hF5 B hB3 hB1
    have hpℓ : ℓ = p := by
      have h1 : p ∣ p ^ f' := dvd_pow_self p (by have := hF'.one_le; omega)
      rw [hpf, hF] at h1
      exact ((Nat.prime_dvd_prime_iff_eq hF'.prime hℓ).1 (hF'.prime.dvd_of_dvd_pow h1)).symm
    subst hpℓ
    have hgood := fixGood_projImage_glPi hF' (by rw [hpf]; exact hF5)
    rw [hpf] at hgood
    have hfixeq : fixSubgroup (CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.gammaP F B) =
        CFSG.RankThree.PartOne.CTP.fixedSubgroup
          (CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.gammaP F B) :=
      Subgroup.ext fun _ => Iff.rfl
    have hB : FixGood ℓ ↥(fixSubgroup (CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.gammaP F B)) :=
      fixGood_of_mulEquiv ((MulEquiv.subgroupCongr hfixeq).trans eP) hgood
  · exact fixGood_of_conj_eq ψ hψ hB
  · refine fixGood_of_conj_eq ψ hψ ?_
    exact fixGood_of_mulEquiv (MulEquiv.subgroupCongr
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq _)) hB

private theorem d4Graph_zero_eq : d4Graph F 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem qGen_d4_outer {ℓ f : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hF : Nat.card F = ℓ ^ f)
    (α : MulAut ↥(adjointGroup Tag.D4 F)) (hα : α ^ 3 = 1)
    (hout : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ α) : Inputs256e.QGen ℓ α := by
  classical
  refine qGen_of_fixGood ?_
  have hℓ : ℓ.Prime := Fact.out
  haveI : CharP F ℓ := by
    haveI := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hFℓ : ringChar F = ℓ := ringChar.eq F ℓ
  have hchar : ringChar F ≠ 3 := by rw [hFℓ]; omega
  obtain ⟨g, a, σ, ε, hε, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα
  by_cases hσ1 : σ = 1
  · subst hσ1
    rcases (show ε = 0 ∨ ε = 1 ∨ ε = 2 by omega) with rfl | hε1 | hε2
    · exfalso
      have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 F a 1 0 := by
        rw [hαeq, d4Graph_zero_eq, mul_one]
      rw [hα'] at hα
      obtain ⟨h, hh⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.d4_inner_of_diag hchar g a hα
      exact hout h (by rw [hα', hh])
    · exact fixGood_d4_graph h5 hf hF hα ⟨g, a, 1, ε, hε, hσ3, ⟨by omega, rfl⟩, hαeq⟩
    · exact fixGood_d4_graph h5 hf hF hα ⟨g, a, 1, ε, hε, hσ3, ⟨by omega, rfl⟩, hαeq⟩
  · rcases (show ε = 0 ∨ ε = 1 ∨ ε = 2 by omega) with rfl | hε12 | hε12
    · have hα' : α = MulAut.conj g * exactNormalAut Tag.D4 F a σ 0 := by
        rw [hαeq, d4Graph_zero_eq, mul_one]
      rw [hα'] at hα ⊢
      obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_conj_eq_entrywiseAdjointAut
        .D4 Nat.prime_three g a σ hσ1 hσ3 hα
      exact fixGood_of_conj_eq ψ hψ (fixGood_entrywiseAdjointAut_D4 hℓ hFℓ σ)
    all_goals
      obtain ⟨ℓ', e, T, hℓ', hchar', he, hK, hT, hσT⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_frobenius_data_D4 σ hσ1 hσ3
      obtain rfl : ℓ' = ℓ := CharP.eq F hchar' ‹CharP F ℓ›
      have hK4 : 4 ≤ Nat.card F := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ ℓ' ^ 2 := Nat.pow_le_pow_left hℓ'.two_le 2
          _ ≤ ℓ' ^ (e * 3) := Nat.pow_le_pow_right hℓ'.pos (by omega)
      rcases hσT with hσT | hσT
      · subst hσT
        obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm F hK hK4 he rfl σ hT α hα
          g a ε hαeq
        refine fixGood_of_conj_eq ψ hψ (fixGood_twistedEntrywiseAut_D4 he hK σ hT ε ?_)
        omega
      · subst hσT
        obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm F hK hK4 he rfl T T⁻¹ hT
          (mul_inv_cancel T) α hα g a ε hαeq
        refine fixGood_of_conj_inv_eq ψ hψ (fixGood_twistedEntrywiseAut_D4 he hK T hT (-(ε : ℤ)) ?_)
        omega

theorem qGenD4Three_holds : QGenD4Three := by
  intro G _ _ ℓ f hG h5 β hβ hout
  obtain ⟨⟨hℓ, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hG
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let e₂ : G ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  refine Inputs256e.qGen_of_congr e₂ β (qGen_d4_outer h5 hf hF _ ?_ fun h hh => ?_)
  · rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  · apply hout (e₂.symm h)
    apply (MulAut.congr e₂).injective
    rw [← hh]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]

theorem qGenSympOrth_holds : Inputs256e.QGenSympOrth :=
  qGenSympOrth_of_d4Three qGenD4Three_holds

end D4Adjoint

section ExcField

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.RecipeExcLang (inndiagGroup)

@[expose] def QGenExcInndiag : Prop :=
  ∀ (τ : Tag), (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K], 5 ≤ ringChar K →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → p ≠ ringChar K →
    ∀ (α : MulAut ↥(adjointGroup τ K)) (b : Fin τ.rank → Kˣ) (j : ModGL τ K), j ∈ adjointGroup τ K →
      (∀ c : adjointGroup τ K,
        (α c : ModGL τ K) = (rootDiagUnit τ b * j) * c * (rootDiagUnit τ b * j)⁻¹) →
      (rootDiagUnit τ b * j) ^ p = 1 → rootDiagUnit τ b * j ≠ 1 →
        Inputs256e.QGen (ringChar K) α

@[expose] def QGenTwE6 : Prop := Inputs256e.QGenOn fun d => ∃ q, d.1 = .twistedE6 q

@[expose] def QGenTriD4 : Prop := Inputs256e.QGenOn fun d => ∃ q, d.1 = .trialityD4 q

@[expose] def QGenTriD4Rest :
    Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 5 ≤ ℓ → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ (Fr : K ≃+* K), (∀ c, Fr c = c ^ (ℓ ^ f)) → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ →
    ∀ φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom), orderOf φ = p →
      (φ ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom)).range ∨
        (p = 3 ∧ ¬ ∃ β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K Fr.toRingHom),
          φ = β * fieldActor (t := TwistTag.D4) Fr Fr * β⁻¹ ∨
            φ = β * (fieldActor (t := TwistTag.D4) Fr Fr)⁻¹ * β⁻¹)) →
        Inputs256e.QGen ℓ φ

@[expose] def QGenTwE6Inndiag :
    Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 5 ≤ ℓ → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ (ℓ ^ f)) → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ →
    ∀ h : ↥(CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL K σ), h ^ p = 1 → h ≠ 1 →
      Inputs256e.QGen ℓ (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ h)

private theorem mulAut_pow_apply_of_apply_eq {S : Type} [Group S] {β : MulAut S} {x : S} (h : β x = x)
    (n : ℕ) : (β ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

private theorem qPerf_of_fixSubgroup_eq {S : Type} [Group S] {q : ℕ} {β β' : MulAut S}
    (h : fixSubgroup β = fixSubgroup β') (h' : QPerf q β') : QPerf q β := by
  intro s hs hn
  obtain ⟨P, hP, hPP, hsP⟩ := h' s (mem_fixSubgroup.1 (h ▸ mem_fixSubgroup.2 hs)) hn
  exact ⟨P, h ▸ hP, hPP, hsP⟩

private theorem qPerf_of_qElemNormal {S : Type} [Group S] {q : ℕ} {β : MulAut S}
    (h : QElemNormal q ↥(fixSubgroup β)) : QPerf q β := by
  obtain ⟨J, -, hJq, hJ⟩ := h
  intro s hs ⟨n, hn⟩
  have hP : CFSG.IsQuasisimple ↥(J.map (fixSubgroup β).subtype) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (J.equivMapOfInjective (fixSubgroup β).subtype (fixSubgroup β).subtype_injective) hJq
  exact ⟨J.map (fixSubgroup β).subtype, Subgroup.map_subtype_le J,
    commutator_self_of_perfect (Group.isPerfect_def.mp hP.1),
    ⟨⟨s, hs⟩, hJ ⟨s, hs⟩ ⟨n, Subtype.ext (by simpa using hn)⟩, rfl⟩⟩


private theorem qGen_exc_untw (hI : QGenExcInndiag) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (h5 : 5 ≤ q.p) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (β : MulAut (CFSG.LieType.SeitzGeneration.Cat ⟨c q, hv⟩)) (hβ : orderOf β = p) :
    Inputs256e.QGen q.p β := by
  classical
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  have hℓ : ringChar K = q.p := ringChar.eq K q.p
  have hα : MulAut.congr e β ^ p = 1 := by rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
  have hα1 : MulAut.congr e β ≠ 1 := fun h => by
    have h1 : β = 1 := (MulAut.congr e).injective (h.trans (map_one _).symm)
    rw [h1, orderOf_one] at hβ
    exact hp.one_lt.ne' hβ.symm
  refine Inputs256e.qGen_of_congr e β ?_
  have hq5 : 5 ≤ Nat.card K := by
    rw [hK, TauCeti.PrimePower.card_def]
    exact h5.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, ((MulAut.congr e β) c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inr h)
        (fun _ => by omega) hp hp2 _ hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inl h)
        (fun _ => by omega) hp hp2 _ hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inl h) hp hp2 _
        hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inr (Or.inl h))
        hp hp2 _ hα hα1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inr (Or.inr h))
        hp hp2 _ hα hα1
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hαh, hhp, hh1⟩
  · have hk : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ) := fun _ => by
      obtain ⟨q', hq'p, hq'c⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_primePower_card_subfield hℓ (fixSubfield σ)
      rw [hq'c, TauCeti.PrimePower.card_def, hq'p]
      exact (by omega : 3 ≤ q.p).trans (Nat.le_self_pow q'.exponent_pos.ne' q.p)
    have hQ : Inputs256e.QGen q.p (entrywiseAdjointAut τ σ) :=
      qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompExport_entrywiseAdjointAut_untw
        hB hchar hvalid hA6 hℓ σ).toComps
        (qPerf_of_qElemNormal (qElemNormal_entrywiseAdjointAut τ q.prime_p hℓ σ hk))
    have hc : MulAut.congr ψ (MulAut.congr e β) = entrywiseAdjointAut τ σ := by
      rw [← hψ]
      exact MulEquiv.ext fun x => rfl
    refine Inputs256e.qGen_of_congr ψ _ ?_
    rw [hc]
    exact hQ
  · obtain ⟨b, j, hj, rfl⟩ := hh
    have h1 := hI τ hτ K (by rw [hℓ]; exact h5) p hp hp2 (by rw [hℓ]; exact hpq) _ b j hj hαh hhp hh1
    rwa [hℓ] at h1

theorem qGenExc_of_residuals (hI : QGenExcInndiag) (hT : QGenTwE6) (hD : QGenTriD4) :
    Inputs256e.QGenExc := by
  rintro ⟨d, hv⟩ hd hd5 p hp hp2 hpd β hβ
  cases d with
  | E6 q =>
    change 5 ≤ (TauCeti.LieTypeIndex.E6 q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.E6 q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.E6 q).characteristic β
    rw [TauCeti.LieTypeIndex.characteristic_E6] at hd5 hpd ⊢
    exact qGen_exc_untw hI (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) (c := TauCeti.LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.E6 q, hv⟩ (Or.inl rfl))
      q hv hd5 hp hp2 hpd β hβ
  | E7 q =>
    change 5 ≤ (TauCeti.LieTypeIndex.E7 q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.E7 q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.E7 q).characteristic β
    rw [TauCeti.LieTypeIndex.characteristic_E7] at hd5 hpd ⊢
    exact qGen_exc_untw hI (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (c := TauCeti.LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.E7 q, hv⟩ (Or.inl rfl))
      q hv hd5 hp hp2 hpd β hβ
  | E8 q =>
    change 5 ≤ (TauCeti.LieTypeIndex.E8 q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.E8 q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.E8 q).characteristic β
    rw [TauCeti.LieTypeIndex.characteristic_E8] at hd5 hpd ⊢
    exact qGen_exc_untw hI (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (c := TauCeti.LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.E8 q, hv⟩ (Or.inl rfl))
      q hv hd5 hp hp2 hpd β hβ
  | F4 q =>
    change 5 ≤ (TauCeti.LieTypeIndex.F4 q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.F4 q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.F4 q).characteristic β
    rw [TauCeti.LieTypeIndex.characteristic_F4] at hd5 hpd ⊢
    exact qGen_exc_untw hI (τ := .F4) (Or.inr (Or.inl rfl)) (c := TauCeti.LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.F4 q, hv⟩ (Or.inl rfl))
      q hv hd5 hp hp2 hpd β hβ
  | G2 q =>
    change 5 ≤ (TauCeti.LieTypeIndex.G2 q).characteristic at hd5
    change p ≠ (TauCeti.LieTypeIndex.G2 q).characteristic at hpd
    change Inputs256e.QGen (TauCeti.LieTypeIndex.G2 q).characteristic β
    rw [TauCeti.LieTypeIndex.characteristic_G2] at hd5 hpd ⊢
    exact qGen_exc_untw hI (τ := .G2) (Or.inl rfl) (c := TauCeti.LieTypeIndex.G2)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl))
      q hv hd5 hp hp2 hpd β hβ
  | twistedE6 q => exact hT ⟨.twistedE6 q, hv⟩ ⟨q, rfl⟩ hd5 p hp hp2 hpd β hβ
  | trialityD4 q => exact hD ⟨.trialityD4 q, hv⟩ ⟨q, rfl⟩ hd5 p hp hp2 hpd β hβ
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd


private theorem qPerf_triD4_outer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hφ : orderOf φ = p)
    (hφout : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) : QPerf ℓ φ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, Θ, hΘ, -⟩ := CFSG.RankThree.Chevalley.triality_normal_form_data hℓ hf K hK σ hσ
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hℓ hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨φ, Subgroup.mem_top _⟩ hφout
      (by rw [Subgroup.orderOf_mk]; exact hφ)
  have hh₀' : MulAut.conj h₀ * φ * (MulAut.conj h₀)⁻¹ = fieldActor (t := TwistTag.D4) σ (Θ φ) := hh₀
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  obtain ⟨φ', hφ', hφord', -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ' ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hφ' _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega)
      (by rw [hφord', hff']; exact ⟨p, by ring⟩), hφord', hff',
      show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ φ) = Subgroup.zpowers δc :=
    CFSG.RankThree.PartOne.CTP.zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 3 * f) hK3
      hηord hδcord
  have hfix_eq : fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ φ)) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, -, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd
      hp.two_le hm3 K hK' σ hσ' δc hδc
  haveI := hsimpJ
  have e3 : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  haveI hsimE : IsSimpleGroup ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) := e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)), a * b ≠ b * a := by
    simp only [not_forall, ne_eq] at hncJ
    obtain ⟨a, b, hab⟩ := hncJ
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  have hperf : ⁅fixSubgroup (fieldActor (t := TwistTag.D4) σ δc),
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)⁆ = fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) :=
    Subgroup.isPerfect_iff.1 ⟨(CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hncE).1⟩
  refine qPerf_of_congr (MulAut.conj h₀) ?_
  have hc : MulAut.congr (MulAut.conj h₀) φ = fieldActor (t := TwistTag.D4) σ (Θ φ) := by
    rw [← hh₀']
    exact MulEquiv.ext fun x => rfl
  rw [hc]
  intro s hs _
  exact ⟨fixSubgroup (fieldActor (t := TwistTag.D4) σ δc), le_of_eq hfix_eq.symm, hperf,
    hfix_eq ▸ mem_fixSubgroup.2 hs⟩

private theorem fixGood_triD4_G2 {ℓ f : ℕ} [Fact ℓ.Prime] (h5 : 5 ≤ ℓ) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    FixGood ℓ ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
    (by omega) hf (Or.inr h5) hK σ hσ
  haveI : CharP K ℓ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.charP_of_card_pow_three hℓ hf hK
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hk : 3 ≤ Nat.card (fixSubfield σ) := by
    obtain ⟨q', hq'p, hq'c⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_primePower_card_subfield
      (ringChar.eq K ℓ) (fixSubfield σ)
    rw [hq'c, TauCeti.PrimePower.card_def, hq'p]
    exact (by omega : 3 ≤ ℓ).trans (Nat.le_self_pow q'.exponent_pos.ne' ℓ)
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup .G2
    (fixSubfield σ) (fun _ => hk)
  obtain ⟨hs, hnc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect
    .G2 (fixSubfield σ) hperf
  exact ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsFine_fixSubgroup_fieldActor (by omega) hf
    (Or.inr h5) hK σ hσ, qElemNormal_of_mulEquiv e (qElemNormal_of_isQuasisimple
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc))⟩

theorem qGenTriD4_of_rest (h : QGenTriD4Rest) : QGenTriD4 := by
  rintro ⟨d, hv⟩ ⟨q, rfl⟩ hd5 p hp hp2 hpd β hβ
  classical
  change 5 ≤ (TauCeti.LieTypeIndex.trialityD4 q).characteristic at hd5
  change p ≠ (TauCeti.LieTypeIndex.trialityD4 q).characteristic at hpd
  change Inputs256e.QGen (TauCeti.LieTypeIndex.trialityD4 q).characteristic β
  rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at hd5 hpd ⊢
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  refine Inputs256e.qGen_of_congr eK β ?_
  have hα : orderOf (MulAut.congr eK β) = p := by rw [orderOf_congr]; exact hβ
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  by_cases hin : MulAut.congr eK β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∨
      (p = 3 ∧ ¬ ∃ γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        MulAut.congr eK β = γ * fieldActor (t := TwistTag.D4) σ σ * γ⁻¹ ∨
          MulAut.congr eK β = γ * (fieldActor (t := TwistTag.D4) σ σ)⁻¹ * γ⁻¹)
  · exact h q.p q.exponent q.prime_p hd5 q.exponent_pos K hK σ hσ p hp hp2 hpd _ hα hin
  · have hout : MulAut.congr eK β ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun h' => hin (Or.inl h')
    by_cases hp3 : p = 3
    · have hconj : ∃ γ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          MulAut.congr eK β = γ * fieldActor (t := TwistTag.D4) σ σ * γ⁻¹ ∨
            MulAut.congr eK β = γ * (fieldActor (t := TwistTag.D4) σ σ)⁻¹ * γ⁻¹ := by
        by_contra hc
        exact hin (Or.inr ⟨hp3, hc⟩)
      obtain ⟨γ, hγ | hγ⟩ := hconj
      · refine qGen_of_fixGood (fixGood_of_conj_eq γ⁻¹ ?_ (fixGood_triD4_G2 hd5 q.exponent_pos hK σ hσ))
        rw [hγ]
        group
      · refine qGen_of_fixGood (fixGood_of_conj_inv_eq γ⁻¹ ?_ (fixGood_triD4_G2 hd5 q.exponent_pos hK σ hσ))
        rw [hγ]
        group
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := fun h4 => by rw [h4] at hp; exact absurd hp (by decide)
        omega
      have hpow : MulAut.congr eK β ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one _
      exact qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.trialityFieldExportP hp hp5 q.p
        q.exponent q.exponent_pos K hK σ hσ _ hpow hout)
        (qPerf_triD4_outer q.prime_p q.exponent_pos hK σ hσ hp hp5 hα hout)

private theorem qPerf_twE6_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ (2 * f)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1) (hη1 : Θ β ≠ 1) : QPerf ℓ β := by
  classical
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp hp2 β hβ hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, hcardk, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set J := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
    (fixSubfieldRestrict T κ) with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  haveI : Finite (fixSubfield κ) := Subtype.finite
  have hder' : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J.subgroupOf (twistedE6RootGroup K σ) := hder
  have eJC : J.subgroupOf (twistedE6RootGroup K σ) ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  haveI := hsimpleJ
  have hJs : IsSimpleGroup (J.subgroupOf (twistedE6RootGroup K σ)) := eJC.isSimpleGroup
  have hJn : ∃ x y : J.subgroupOf (twistedE6RootGroup K σ), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hJperf : ⁅J.subgroupOf (twistedE6RootGroup K σ), J.subgroupOf (twistedE6RootGroup K σ)⁆ =
      J.subgroupOf (twistedE6RootGroup K σ) :=
    commutator_self_of_perfect (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hJn).1
  have hψpow : ∀ c, (σ * ε) c = c ^ ℓ ^ d := fun c => by
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = ℓ ^ (2 * d * p) := by rw [← Nat.card_eq_fintype_card, hKdp]
    have h1 : c ^ (ℓ ^ (2 * d * p)) = c := by
      have := FiniteField.pow_card c
      rwa [hcard] at this
    rw [RingAut.mul_apply, hε, hσdp, ← pow_mul, show ℓ ^ (d * (p + 1)) * ℓ ^ (d * p) =
      ℓ ^ (2 * d * p) * ℓ ^ d by rw [← pow_add, ← pow_add]; congr 1; ring, pow_mul, h1]
  have hK0 : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ 2 := by rw [hcardk, ← pow_mul, mul_comm]
  have hδ : QPerf ℓ δ := by
    intro x hx ⟨n, hn⟩
    refine ⟨J.subgroupOf (twistedE6RootGroup K σ), hder' ▸ commutator_le_self' _, hJperf, ?_⟩
    have hδx : Units.map (entrywiseHom ε.toRingHom) (x : ModGL TwistTag.E6.tag K) = x := by
      have h := congrArg Subtype.val hx
      rwa [coe_fieldActor] at h
    have hxψ : (x : ModGL TwistTag.E6.tag K) ∈ CFSG.Blueprint.twistedFixedGroup TwistTag.E6 K (σ * ε).toRingHom := by
      obtain ⟨hxA, hxσ⟩ := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
        (graphFixedRootGroup_le _ _ _ x.2)
      refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K (σ * ε).toRingHom).2 ⟨hxA, ?_⟩
      rw [twistHom_apply] at hxσ ⊢
      rw [show (σ * ε).toRingHom = σ.toRingHom.comp ε.toRingHom from RingHom.ext fun _ => rfl,
        ← units_map_entrywiseHom_comp, hδx]
      exact hxσ
    have hxn : (x : ModGL TwistTag.E6.tag K) ^ ℓ ^ n = 1 := by
      have h1 := congrArg Subtype.val hn
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).1 (orderOf_dvd_of_pow_eq_one hxn)
    exact Subgroup.mem_subgroupOf.2 (CFSG.RankThree.PartOne.FieldFix.twistedE6_pElement_mem_subfield hℓ hd1
      (fixSubfield κ) hK0 (fixSubfieldRestrict T κ) hσ₀ (σ * ε) hψpow hℓ hℓ3 hxψ ⟨j, hj⟩)
  have hβr : QPerf ℓ (β ^ r) := by
    refine qPerf_of_congr ψ ?_
    have hc : MulAut.congr ψ (β ^ r) = δ := by
      rw [← hψ]
      exact MulEquiv.ext fun x => rfl
    rw [hc]
    exact hδ
  refine qPerf_of_fixSubgroup_eq ?_ hβr
  ext x
  simp only [mem_fixSubgroup]
  constructor
  · intro hx
    exact mulAut_pow_apply_of_apply_eq hx r
  · intro hx
    have h1 : (β ^ r) ^ s = β := hrs
    rw [← h1]
    exact mulAut_pow_apply_of_apply_eq hx s

theorem qGenTwE6_of_inndiag (h : QGenTwE6Inndiag) : QGenTwE6 := by
  rintro ⟨d, hv⟩ ⟨q, rfl⟩ hd5 p hp hp2 hpd β hβ
  classical
  change 5 ≤ (TauCeti.LieTypeIndex.twistedE6 q).characteristic at hd5
  change p ≠ (TauCeti.LieTypeIndex.twistedE6 q).characteristic at hpd
  change Inputs256e.QGen (TauCeti.LieTypeIndex.twistedE6 q).characteristic β
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hd5 hpd ⊢
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  refine Inputs256e.qGen_of_congr eK β ?_
  have hα : orderOf (MulAut.congr eK β) = p := by rw [orderOf_congr]; exact hβ
  have hβ' : MulAut.congr eK β ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one _
  have hβ1' : MulAut.congr eK β ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hα
    exact hp.one_lt.ne' hα.symm
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr eK β) = 1
  · have hmem : MulAut.congr eK β ∈ (CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj K σ).range := by
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨g, hg⟩ := hmem
    have hp1 : g ^ p = 1 :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
        (by rw [map_pow, hg, hβ', map_one])
    have hg1 : g ≠ 1 := fun h' => hβ1' (by rw [← hg, h', map_one])
    rw [← hg]
    exact h q.p q.exponent q.prime_p hd5 q.exponent_pos K hK σ hσ p hp hp2 hpd g hp1 hg1
  · have hK' : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
    exact qGen_of_qPerf (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompExport_twE6_field
      (fun q hv => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isEmpty_cat_alt6 ⟨.twistedE6 q, hv⟩
        (Or.inl rfl)) q.prime_p q.exponent_pos hK' σ hσ hp hp2 Θ hΘ _ hβ' hΘβ).toComps
      (qPerf_twE6_field q.prime_p (by omega) q.exponent_pos hK' σ hσ hp hp2 Θ hΘ _ hβ' hΘβ)

theorem qGenExc_of_inndiag (hI : QGenExcInndiag) (hT : QGenTwE6Inndiag) (hD : QGenTriD4Rest) :
    Inputs256e.QGenExc :=
  qGenExc_of_residuals hI (qGenTwE6_of_inndiag hT) (qGenTriD4_of_rest hD)

end ExcField

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256f

end
