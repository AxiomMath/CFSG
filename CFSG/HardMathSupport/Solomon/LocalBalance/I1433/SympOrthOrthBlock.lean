module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthSymp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Open
open scoped commutatorElement

theorem orth_component_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hpℓ : p ≠ ringChar K) (x : ↥(orthDerived Q)) (hxp : x ^ p = 1)
    (hcent : Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q)) =
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))
    (J : Subgroup (ProjOrthDerived Q))
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({(QuotientGroup.mk x :
      ProjOrthDerived Q)} : Set (ProjOrthDerived Q)))) :
    (∃ h : K[X], h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧ h ≠ X - 1 ∧
        CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h) ∧
        J = componentImage Q (x : V ≃ₗ[K] V) h) ∨
      ∃ F : Subgroup (V ≃ₗ[K] V), F ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
        J = (F.subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) := oddOrderIsometry_of_pow_eq_one hp hpℓ hQ x hxp
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  have hNeq : Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
      Set (ProjOrthDerived Q)) = N := by
    rw [hcent]
    exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x
  rw [hNeq] at hJ
  obtain ⟨n, F, hFq, hFsup, hFn0⟩ := exists_fixedFactors hx
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N :=
    sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ hp hp2 x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left
        (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := component_mem_named_factors Fm hFm
    (fun P hPN hP => hiSup ▸ hperf P hPN hP) hJ
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · exact Or.inl ⟨h, hRep.1 hh, hne, hq, rfl⟩
  · exact Or.inr ⟨F i, (hFq i).2.1, rfl⟩

section Block

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def orthCentralizerHom (x : ↥(orthDerived Q)) :
    ↥(Subgroup.centralizer ({x} : Set ↥(orthDerived Q))) →*
      ↥(Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) :=
  ((orthDerived Q).subtype.comp
      (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).subtype).codRestrict
    _ (fun g => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2))

@[expose] noncomputable def orthBlockRestrict (x : ↥(orthDerived Q)) (h : K[X]) :
    ↥(Subgroup.centralizer ({x} : Set ↥(orthDerived Q))) →* BlockGL (x : V ≃ₗ[K] V) h :=
  (centralizerGL (x : V ≃ₗ[K] V) h).comp (orthCentralizerHom x)

theorem orthBlockRestrict_self (x : ↥(orthDerived Q)) (h : K[X])
    (u : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) :
    ((orthBlockRestrict x h (selfCentralizer x) : BlockGL (x : V ≃ₗ[K] V) h) :
      Module.End (AdjoinRoot h) (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h)) u =
        AdjoinRoot.root h • u := by
  apply Subtype.ext
  rw [coe_root_smul_primaryComponent]
  rfl

theorem orth_hnormal {p : ℕ} {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} (x : ↥(orthDerived Q))
    (h : K[X]) (hSB : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q)
    (hPC : (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q) ≤
      Subgroup.centralizer ({x} : Set ↥(orthDerived Q)))
    (g₀ : ↥(supportedBlock Q (x : V ≃ₗ[K] V) h)) (g : ↥(orthDerived Q))
    (hg : g ∈ (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)) :
    ∃ g' : ↥(orthDerived Q), ∃ hg' : g' ∈ (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf
        (orthDerived Q),
      orthBlockRestrict x h ⟨g', hPC hg'⟩ =
        blockGL Q (x : V ≃ₗ[K] V) h g₀ * orthBlockRestrict x h ⟨g, hPC hg⟩ *
          (blockGL Q (x : V ≃ₗ[K] V) h g₀)⁻¹ := by
  have hgS : (g : V ≃ₗ[K] V) ∈ specialBlock Q (x : V ≃ₗ[K] V) h := Subgroup.mem_subgroupOf.mp hg
  have hg₀ : (g₀ : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
    supportedBlock_le_isometryCentralizer h g₀.2
  have hconj := conj_mem_specialBlock hg₀ hgS
  have hconjΩ : (g₀ : V ≃ₗ[K] V) * g * (g₀ : V ≃ₗ[K] V)⁻¹ ∈ orthDerived Q := hSB hconj
  have hSBsup : (g₀ : V ≃ₗ[K] V) * g * (g₀ : V ≃ₗ[K] V)⁻¹ ∈ supportedBlock Q (x : V ≃ₗ[K] V) h :=
    specialBlock_le_supportedBlock h hconj
  refine ⟨⟨_, hconjΩ⟩, Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
  have h1 : (⟨(g₀ : V ≃ₗ[K] V) * g * (g₀ : V ≃ₗ[K] V)⁻¹, hSBsup⟩ :
      ↥(supportedBlock Q (x : V ≃ₗ[K] V) h)) =
      g₀ * ⟨g, specialBlock_le_supportedBlock h hgS⟩ * g₀⁻¹ := rfl
  have h2 : orthBlockRestrict x h ⟨⟨_, hconjΩ⟩, hPC (Subgroup.mem_subgroupOf.mpr hconj)⟩ =
      blockGL Q (x : V ≃ₗ[K] V) h ⟨(g₀ : V ≃ₗ[K] V) * g * (g₀ : V ≃ₗ[K] V)⁻¹, hSBsup⟩ := rfl
  have h3 : orthBlockRestrict x h ⟨g, hPC hg⟩ =
      blockGL Q (x : V ≃ₗ[K] V) h ⟨g, specialBlock_le_supportedBlock h hgS⟩ := rfl
  rw [h2, h3, h1, map_mul, map_mul, map_inv]

theorem orth_hasLowRankBlock_of_special {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hpℓ : 3 ≠ ringChar K) {S : Type} [Group S]
    (π : ↥(orthDerived Q) →* S) (x : ↥(orthDerived Q)) (hx3 : x ^ 3 = 1)
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[K] V) h)) {J : Subgroup S}
    (hJ : ((specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q)).map π ≤ J) :
    HasLowRankBlock π x J := by
  classical
  have hx : OddOrderIsometry Q 3 (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ x hx3
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨hω0, hordu⟩ := hx.orderOf_root Nat.prime_three hh hne1
  have hord : orderOf (AdjoinRoot.root h) = 3 := by
    rw [← hordu]; exact orderOf_units (y := Units.mk0 (AdjoinRoot.root h) hω0)
  have hω3 : (AdjoinRoot.root h) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (AdjoinRoot.root h)
    rwa [hord] at this
  have hω1 : AdjoinRoot.root h ≠ 1 := by
    intro e; rw [e, orderOf_one] at hord; omega
  have hSB : specialBlock Q (x : V ≃ₗ[K] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  set P := (specialBlock Q (x : V ≃ₗ[K] V) h).subgroupOf (orthDerived Q) with hPdef
  have hPC : P ≤ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hgS := Subgroup.mem_subgroupOf.mp hg
    have : (g : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({(x : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) :=
      supportedBlock_le_centralizer h (specialBlock_le_supportedBlock h hgS)
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hqP : CFSG.IsQuasisimple ↥P :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSB).symm hq
  have hperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hqP.1
  have hinj : ∀ g₁ g₂ : ↥(orthDerived Q), ∀ (h₁ : g₁ ∈ P) (h₂ : g₂ ∈ P),
      orthBlockRestrict x h ⟨g₁, hPC h₁⟩ = orthBlockRestrict x h ⟨g₂, hPC h₂⟩ → g₁ = g₂ := by
    intro g₁ g₂ h₁ h₂ heq
    have h1S := Subgroup.mem_subgroupOf.mp h₁
    have h2S := Subgroup.mem_subgroupOf.mp h₂
    have := hx.specialBlockGL_injective hh (a₁ := ⟨g₁, h1S⟩) (a₂ := ⟨g₂, h2S⟩) heq
    have h' : (g₁ : V ≃ₗ[K] V) = (g₂ : V ≃ₗ[K] V) :=
      congrArg (fun a : ↥(specialBlock Q (x : V ≃ₗ[K] V) h) => (a : V ≃ₗ[K] V)) this
    exact Subtype.ext h'
  have hnonab : ∃ g₁ g₂ : ↥(orthDerived Q), ∃ (h₁ : g₁ ∈ P) (h₂ : g₂ ∈ P),
      orthBlockRestrict x h ⟨g₁, hPC h₁⟩ * orthBlockRestrict x h ⟨g₂, hPC h₂⟩ ≠
        orthBlockRestrict x h ⟨g₂, hPC h₂⟩ * orthBlockRestrict x h ⟨g₁, hPC h₁⟩ := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hqP
    refine ⟨a.1, b.1, a.2, b.2, fun heq => hab ?_⟩
    rw [← map_mul, ← map_mul] at heq
    have := hinj _ _ (P.mul_mem a.2 b.2) (P.mul_mem b.2 a.2) heq
    exact Subtype.ext this
  have hPimg_range : ∀ g (hg : g ∈ P), orthBlockRestrict x h ⟨g, hPC hg⟩ ∈
      (blockGL Q (x : V ≃ₗ[K] V) h).range := fun g hg =>
    ⟨⟨g, specialBlock_le_supportedBlock h (Subgroup.mem_subgroupOf.mp hg)⟩, rfl⟩
  by_cases hself : h = reciprocalPolynomial h
  ·
    obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
      hx.exists_selfDual_hermitian (by decide : Odd 3) hh hne1 hself
    have hirr := irreducible_of_mem_primaryFactors hh
    have hd : finrank K (AdjoinRoot h) = 2 * d := by
      rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
    obtain ⟨ℓ, f, hU, hq0, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
    have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
      rw [hbar, frobPow_apply]
    let B : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h →ₛₗ[hU.bar]
        primaryComponent (x : V ≃ₗ[K] V).toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
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
    obtain ⟨eb, heb⟩ := hU.exists_orthonormal_basis hBsymm hBl
    have hrange : ∀ γ : BlockGL (x : V ≃ₗ[K] V) h,
        γ ∈ (blockGL Q (x : V ≃ₗ[K] V) h).range ↔ γ ∈ sesqUnitaryGroup B := fun γ =>
      (hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH γ).trans
        (by rw [mem_sesqUnitaryGroup]; exact Iff.rfl)
    have hωn : hU.bar (AdjoinRoot.root h) * AdjoinRoot.root h = 1 := by
      rw [← hbar', frobPow_apply, hroot, inv_mul_cancel₀ hω0]
    refine hasLowRankBlock_of_perfect π x J (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) (orthBlockRestrict x h) (AdjoinRoot.root h)
      hω1 hω3 (orthBlockRestrict_self x h) P hPC hJ hperf hnonab (sesqUnitaryGroup B)
      (fun g hg => (hrange _).mp (hPimg_range g hg)) (fun f hf g hg => ?_)
      (fun N hNle hN hna => ?_)
    · obtain ⟨g₀, rfl⟩ := (hrange f).mpr hf
      exact orth_hnormal (p := 3) x h hSB hPC g₀ g hg
    · exact exists_lowRank_of_normal_nonabelian_unitary eb heb hω1 hωn hN hna
  ·
    have hbij := hx.blockGL_bijective_paired hh hself
    refine hasLowRankBlock_of_perfect π x J (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) (orthBlockRestrict x h) (AdjoinRoot.root h)
      hω1 hω3 (orthBlockRestrict_self x h) P hPC hJ hperf hnonab ⊤ (fun _ _ => Subgroup.mem_top _)
      (fun f _ g hg => ?_) (fun N hNle hN hna => ?_)
    · obtain ⟨g₀, rfl⟩ := hbij.2 f
      exact orth_hnormal (p := 3) x h hSB hPC g₀ g hg
    · exact exists_lowRank_of_normal_nonabelian_gl
        (Module.finBasis (AdjoinRoot h) (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h))
        hω1 hω0 (fun f n hn => hN f (Subgroup.mem_top _) n hn) hna

end Block

theorem eq_one_of_mem_supportedBlock_fixed {p : ℕ} {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hxF : x ∈ supportedBlock Q x (X - 1)) : x = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨w, hw, r, hr, rfl⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_add_of_isCompl hx.fixed_others.1 v
  rw [map_add, mem_fixedSpace.mp hw, (mem_supportedBlock.mp hxF).2 r hr]
  rfl

theorem map_centralizer_equiv {S T : Type*} [Group S] [Group T] (e : S ≃* T) (s : S) :
    (Subgroup.centralizer ({s} : Set S)).map (e : S →* T) =
      Subgroup.centralizer ({e s} : Set T) := by
  ext g
  refine Iff.trans (Subgroup.mem_map_equiv (f := e)) ?_
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    apply e.injective
    simpa using h

section Final

open CFSG.RankThree.Classical

theorem orth_exists_blockModel' {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S]
    {n ℓ f : ℕ} (hG : StatedClassicalModel S t n ℓ f) (hℓ3 : ℓ ≠ 3) :
    ∃ (G : Type) (_ : Group G) (π : G →* S), Function.Surjective π ∧
      π.ker ≤ Subgroup.center G ∧ (∀ z ∈ π.ker, z ^ 2 = 1) ∧
      ∀ X : G, X ^ 3 = 1 → π X ≠ 1 → ∀ J : Subgroup S,
        IsComponentOf J (Subgroup.centralizer ({π X} : Set S)) → π X ∈ J →
          HasLowRankBlock π X J := by
  classical
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, hring, ⟨e⟩⟩ := exists_projOrth_model ht hG
  have hpℓ : 3 ≠ ringChar K := by rw [hring]; exact fun h => hℓ3 h.symm
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, hcenter, hcard, -, -, -, -, -, hlift⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hkerρ : ρ.ker = (scalars K V).subgroupOf (orthDerived Q) := QuotientGroup.ker_mk' _
  have hkerc : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by rw [hkerρ, hcenter]
  have hkerq : ∀ z ∈ ρ.ker, z ^ 2 = 1 := by
    intro z hz
    rw [hkerρ] at hz
    have h1 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
      have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
      interval_cases hc : Nat.card ↥((scalars K V).subgroupOf (orthDerived Q))
      · exact h1.trans (one_dvd _)
      · exact h1
    have h3 := orderOf_dvd_iff_pow_eq_one.mp h2
    exact congrArg Subtype.val h3
  refine ⟨↥(orthDerived Q), inferInstance, (e.symm : ProjOrthDerived Q →* S).comp ρ, ?_, ?_, ?_, ?_⟩
  · exact e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro z hz
    apply hkerc
    rw [MonoidHom.mem_ker] at hz ⊢
    simpa using hz
  · intro z hz
    apply hkerq
    rw [MonoidHom.mem_ker] at hz ⊢
    simpa using hz
  · intro X hX3 hX1 J hJ hXJ
    set π : ↥(orthDerived Q) →* S := (e.symm : ProjOrthDerived Q →* S).comp ρ with hπ
    have hρX1 : ρ X ≠ 1 := fun h => hX1 (by simp [hπ, h])
    have hX1' : X ≠ 1 := fun h => hρX1 (by rw [h, map_one])
    have hXord : orderOf X = 3 := orderOf_eq_prime hX3 hX1'
    have hord : orderOf (ρ X) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hX3, map_one]) hρX1
    obtain ⟨x', ⟨hxa, hxp⟩, huniq, hcent⟩ := hlift 3 Nat.prime_three (by norm_num) (ρ X) hord
    have hXx : X = x' := huniq X rfl hXord
    subst hXx
    have hπXρ : e (π X) = ρ X := by simp [hπ]
    have hJT : CFSG.Open.IsComponentOf (J.map (e : S →* ProjOrthDerived Q))
        (Subgroup.centralizer ({(QuotientGroup.mk X : ProjOrthDerived Q)} :
          Set (ProjOrthDerived Q))) := by
      have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJ
      rw [map_centralizer_equiv, hπXρ] at h1
      exact h1
    have hJmap : ∀ g : ↥(orthDerived Q), ρ g ∈ J.map (e : S →* ProjOrthDerived Q) →
        π g ∈ J := by
      rintro g ⟨j, hj, hjg⟩
      have : π g = j := by
        apply e.injective
        simpa [hπ] using hjg.symm
      rw [this]; exact hj
    rcases orth_component_cases Nat.prime_three (by norm_num) hQ hpℓ X hX3 hcent _ hJT with
      ⟨h, hh, hne1, hq, hJh⟩ | ⟨F, hF, hJF⟩
    · refine orth_hasLowRankBlock_of_special hQ hpℓ π X hX3 hh hne1 hq ?_
      rintro _ ⟨g, hg, rfl⟩
      apply hJmap
      rw [hJh]
      exact ⟨g, hg, rfl⟩
    · exfalso
      have hρXJ : ρ X ∈ (F.subgroupOf (orthDerived Q)).map ρ := by
        rw [← hJF]; exact ⟨π X, hXJ, hπXρ⟩
      have hXF : X ∈ F.subgroupOf (orthDerived Q) :=
        mem_of_map_mem_of_cube ρ hkerc hkerq hX3 hρXJ
      have hxF : (X : V ≃ₗ[K] V) ∈
          supportedBlock Q (X : V ≃ₗ[K] V) (Polynomial.X - 1 : K[X]) :=
        supportedFixedDerived_le_supportedBlock (hF (Subgroup.mem_subgroupOf.mp hXF))
      have hx : OddOrderIsometry Q 3 (X : V ≃ₗ[K] V) :=
        oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ X hX3
      exact hX1' (Subtype.ext (eq_one_of_mem_supportedBlock_fixed hx hxF))

end Final

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
