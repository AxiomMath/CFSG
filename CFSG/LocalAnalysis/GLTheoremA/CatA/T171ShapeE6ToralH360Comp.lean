module

import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreKerDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36U4Twin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtExact
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpU4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4SteinU
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUFour
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecLinearHigh
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPair
public import Certificates.Certificate10050
public import Certificates.Certificate8117

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.GroupActions
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped Pointwise


theorem conj_mem_rationalComponent_of_mem_torus
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {t : ModGL τ L} (ht : t ∈ S.D.torus)
    {r : ModGL τ L} (hr : r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    t * r * t⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have htH : t ∈ torusGroup τ L := (mem_twistedTorusOf.1 ht).1
  have htF : S.D.step t = t := by
    simpa [LangDatum.step, MulAut.conj_apply] using (mem_twistedTorusOf.1 ht).2
  let φ : ModGL τ L →* ModGL τ L := (MulAut.conj t).toMonoidHom
  have hφ : ∀ g, φ g = t * g * t⁻¹ := fun g => rfl
  have htM : t ∈ S.D.model := ⟨torusGroup_le_adjointGroup' htH, htF⟩
  have hM : S.D.model.map φ ≤ S.D.model := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    exact mul_mem (mul_mem htM hg) (inv_mem htM)
  have hΓ : S.Γ.map φ ≤ S.Γ := by
    have h1 : (⁅S.D.model, S.D.model⁆).map φ ≤ ⁅S.D.model, S.D.model⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hM hM
    exact h1
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), S.ρ γ ∈ kernelRoots (rootCharHom a) :=
    rho_mem_kernelRoots_of_mem_torus S hT
  have hroot : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, IsRoot τ γ :=
    fun γ hγ => (rationalRoots_subset_kernelRoots hker i hγ).1
  have hS : (rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i)).map φ ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (L := L) (τ := τ) hroot htH) g).1 hg
  have hrs : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    (Subgroup.map_inf_le _ _ _).trans (inf_le_inf hS hΓ)
  have hcomp : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalComponent
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hrs hrs
  exact hcomp ⟨r, hr, rfl⟩

structure T171ToralLangComp (n : ℕ) (K : Type) [Field K] [Finite K]
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (G : Type) [Group G] (φ : G →* G) (Kc : Subgroup G)
    (hnorm : ∀ x ∈ Kc, φ x ∈ Kc) : Type where
  i : KernelComponent (rootCharHom a)
  e : ↥Kc ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
  y : ModGL Tag.E6 (AlgebraicClosure K)
  hyZ : y ∈ torusGroup Tag.E6 (AlgebraicClosure K) ⊔
    rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom a))
  hyF : S.D.step y = y
  hyStab : MulAut.conj y ∈ subgroupStabAut
    (rationalComponent S.ρ S.Γ (rootCharHom a) i)
  hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)
  hact : ∀ x : ↥Kc, e ⟨φ x, hnorm x x.2⟩ =
    y * (e x : ModGL Tag.E6 (AlgebraicClosure K)) * y⁻¹

theorem nonempty_toralLangComp {n : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {φ : G →* G} {Kc : Subgroup G}
    {hnorm : ∀ x ∈ Kc, φ x ∈ Kc}
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    {C : Type} [Group C] [Finite C]
    (ιLang : C →* ModGL Tag.E6 (AlgebraicClosure K))
    (hιLang_inj : Function.Injective ιLang)
    (hιLang_range : ιLang.range = S.Γ)
    (βd : MulAut C)
    (hβd : ∀ c : C, ιLang (βd c) =
      rootDiagUnit Tag.E6 a * ιLang c * (rootDiagUnit Tag.E6 a)⁻¹)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {ρR : C ≃* G} (βb : MulAut C) {y : ModGL Tag.E6 (AlgebraicClosure K)}
    (hβb : ∀ c : C, ιLang (βb c) = y * ιLang c * y⁻¹)
    (he_b : ∀ c : C, ρR (βb c) = φ (ρR c))
    (hK : CFSG.Open.IsComponentOf (Kc.comap ρR.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup βd))
    (hy : y ∈ S.D.torus)
    (hyZ : y ∈ torusGroup Tag.E6 (AlgebraicClosure K) ⊔
      rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y) :
    Nonempty (T171ToralLangComp n K S a G φ Kc hnorm) := by
  classical
  obtain ⟨i, hQS, hKR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S Nat.prime_three
      ιLang hιLang_inj hιLang_range βd hβd hT hap h1 hTame hK
  let eKc' : ↥(Kc.comap ρR.toMonoidHom) ≃* ↥Kc :=
    (Subgroup.equivMapOfInjective (Kc.comap ρR.toMonoidHom) ρR.toMonoidHom
      ρR.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self (by simp)))
  let eKc : ↥Kc ≃* ↥(Kc.comap ρR.toMonoidHom) := eKc'.symm
  have eKc'_coe : ∀ k : ↥(Kc.comap ρR.toMonoidHom),
      ((eKc' k : ↥Kc) : G) = ρR k := fun k => rfl
  have eKc_coe : ∀ x : ↥Kc, ((eKc x : ↥(Kc.comap ρR.toMonoidHom)) : C) = ρR.symm x := by
    intro x
    apply ρR.injective
    calc ρR (eKc x : C) = ((eKc' (eKc x) : ↥Kc) : G) := (eKc'_coe (eKc x)).symm
      _ = (x : G) := by rw [eKc'.apply_symm_apply]
      _ = ρR (ρR.symm x) := (ρR.apply_symm_apply x).symm
  let eK : ↥(Kc.comap ρR.toMonoidHom) ≃*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (Subgroup.equivMapOfInjective (Kc.comap ρR.toMonoidHom) ιLang hιLang_inj).trans
      (MulEquiv.subgroupCongr hKR)
  have eK_coe : ∀ k : ↥(Kc.comap ρR.toMonoidHom),
      ((eK k : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
        ModGL Tag.E6 (AlgebraicClosure K)) = ιLang k := fun k => rfl
  let e : ↥Kc ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := eKc.trans eK
  have e_coe : ∀ x : ↥Kc,
      ((e x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
        ModGL Tag.E6 (AlgebraicClosure K)) = ιLang (eKc x) := fun x => eK_coe (eKc x)
  have hρeKc : ∀ z : ↥Kc, ρR (eKc z) = (z : G) := by
    intro z
    rw [eKc_coe, ρR.apply_symm_apply]
  have hk : ∀ x : ↥Kc, eKc ⟨φ x, hnorm x x.2⟩ = βb (eKc x) := by
    intro x
    apply ρR.injective
    rw [hρeKc, he_b, hρeKc]
  have hact : ∀ x : ↥Kc, e ⟨φ x, hnorm x x.2⟩ =
      y * (e x : ModGL Tag.E6 (AlgebraicClosure K)) * y⁻¹ := by
    intro x
    rw [e_coe, e_coe, hk]
    exact hβb (eKc x)
  have hyStab : MulAut.conj y ∈
      subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    have hyinv : y⁻¹ ∈ S.D.torus := inv_mem hy
    apply le_antisymm
    · rintro r ⟨x, hx, rfl⟩
      exact conj_mem_rationalComponent_of_mem_torus S hT i hy hx
    · intro r hr
      refine ⟨y⁻¹ * r * y, conj_mem_rationalComponent_of_mem_torus S hT i hyinv hr, ?_⟩
      show y * (y⁻¹ * r * y) * y⁻¹ = r
      group
  exact ⟨{
    i := i
    e := e
    y := y
    hyZ := hyZ
    hyF := hyF
    hyStab := hyStab
    hQS := hQS
    hact := hact }⟩

theorem T171ToralLangComp.card_centerQuot_eq {n : ℕ} {K : Type} [Field K] [Finite K]
    {S : LangSetup Tag.E6 (AlgebraicClosure K) 5}
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    {G : Type} [Group G] {φ : G →* G} {Kc : Subgroup G}
    {hnorm : ∀ x ∈ Kc, φ x ∈ Kc} (D : T171ToralLangComp n K S a G φ Kc hnorm) :
    Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) =
      Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) D.i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) D.i)) :=
  Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥Kc)
    (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) D.i)) D.e
    (Subgroup.map_center_eq D.e)).toEquiv

theorem T171ToralLangComp.centerQuot_ne_360 {n : ℕ} {K : Type} [Field K] [Finite K]
    {S : LangSetup Tag.E6 (AlgebraicClosure K) 5}
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ}
    {G : Type} [Group G] {φ : G →* G} {Kc : Subgroup G}
    {hnorm : ∀ x ∈ Kc, φ x ∈ Kc} (D : T171ToralLangComp n K S a G φ Kc hnorm)
    (h360 : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ≠ 360) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) D.i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) D.i)) ≠ 360 :=
  fun h => h360 (by rw [D.card_centerQuot_eq, h])

theorem nonempty_e6ToralLangComp (n : ℕ) (K : Type) [Field K] [Finite K]
    [CharP (AlgebraicClosure K) 2]
    (hn : 1 ≤ n) (hKcard : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1)
    (wd wb : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)) (hwd3 : wd ^ 3 = 1) (hwd1 : wd ≠ 1)
    (hwb3 : wb ^ 3 = 1) (w : WeylGroup Tag.E6)
    (g0 : ModGL Tag.E6 (AlgebraicClosure K))
    (hg0 : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hF : entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
    (htorus : ∀ x ∈ ({(wd : ModGL Tag.E6 K), (wb : ModGL Tag.E6 K)} :
        Set (ModGL Tag.E6 K)),
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) w)
          (entrywiseFrobGL Tag.E6 (AlgebraicClosure K) 2 n)).map
          (MulAut.conj g0).toMonoidHom)
    (Kc : Subgroup (TableBExc.RecipeGroup Tag.E6 K))
    (hKc : CFSG.Assembly.IsComponentOf Kc (fixedSubgroup (e6RecipeConj wd)))
    (hnorm : ∀ x ∈ Kc, e6RecipeConj wb x ∈ Kc) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (D : T171ToralLangComp n K S a (TableBExc.RecipeGroup Tag.E6 K)
        (e6RecipeConj wb).toMonoidHom Kc hnorm),
      S.D.q = 2 ^ n ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
      rootDiagUnit Tag.E6 a ^ 3 = 1 ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (wd : ModGL Tag.E6 K) =
        S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ := by
  classical
  let L := AlgebraicClosure K
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hFr, hKcard]
  let D : LangDatum Tag.E6 L := LangDatum.ofFrobenius Fr (2 ^ n) hFr w hg0 hF
  have hDq : D.q = 2 ^ n := rfl
  have hDΦ : D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hperf : commutator ↥(adjointGroup Tag.E6 K) = ⊤ :=
    commutator_adjointGroup_E6_eq_top K
  set ι₀ : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E6 K).subtype with hι₀def
  have hd : LangDescent D 5 ι₀ :=
    langDescent_untw 3 (Or.inl ⟨rfl, rfl⟩) hFrK D hDΦ Nat.prime_five (by norm_num) hperf
  have hfin : Finite D.model := hd.finite_model
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := hd.Γ_eq
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 L D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    constructor
    · rw [hDq]
      exact Nat.prime_two.isPrimePow.pow (by omega)
    · rw [hDq]
      exact (CharP.cast_eq_zero_iff L 2 (2 ^ n)).2 (dvd_pow_self 2 (by omega))
  have hpq : ¬ 5 ∣ D.q := by
    rw [hDq]
    intro h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5) (by norm_num)
  let S : LangSetup Tag.E6 L 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl (by norm_num)) hqpow hpq hfin
  have hmemd : (baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K)) ∈
      S.D.torus.map (MulAut.conj S.D.g0).toMonoidHom :=
    htorus wd (by simp)
  obtain ⟨z, hz, hzu⟩ := hmemd
  have hzH : z ∈ torusGroup Tag.E6 L := (mem_twistedTorusOf.1 hz).1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzH
  have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := ha ▸ hz
  have hwd : baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) =
      S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ := by
    rw [← ha]
    exact hzu.symm
  have hwd3' : (wd : ModGL Tag.E6 K) ^ 3 = 1 := by
    simpa using congrArg (fun x : ↥(TableBExc.E6Three.hatGroup Tag.E6 K) =>
      (x : ModGL Tag.E6 K)) hwd3
  have hu3 : (baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K)) ^ 3 = 1 := by
    rw [← map_pow, hwd3', map_one]
  have hz3 : z ^ 3 = 1 := by
    have h : z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) * S.D.g0 := by
      have hh : S.D.g0 * z * S.D.g0⁻¹ =
          baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) := by
        have h := hzu
        change (MulAut.conj S.D.g0) z = _ at h
        simpa only [MulAut.conj_apply] using h
      calc z = S.D.g0⁻¹ * (S.D.g0 * z * S.D.g0⁻¹) * S.D.g0 := by group
        _ = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) * S.D.g0 := by
            rw [hh]
    have hc : (S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) * S.D.g0) ^ 3 =
        S.D.g0⁻¹ * (baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K)) ^ 3 * S.D.g0 := by
      rw [show S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) * S.D.g0 =
        S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) * (S.D.g0⁻¹)⁻¹ by
          rw [inv_inv]]
      exact conj_pow
    rw [h, hc, hu3, mul_one, inv_mul_cancel]
  have hap : ∀ j, a j ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
      have hmap : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
        (rootDiagUnitHom Tag.E6 L).map_pow a 3
      rw [hmap, ← ha, hz3, rootDiagUnit_one]
    exact fun j => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) j
  have hpow : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro hz1
    have hu1 : baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) = 1 := by
      rw [hwd, hz1]
      group
    apply hwd1
    exact Subtype.ext (baseChangeGL_injective (algebraMap K L) (by simpa using hu1))
  have hmemb : (baseChangeGL (algebraMap K L) (wb : ModGL Tag.E6 K)) ∈
      S.D.torus.map (MulAut.conj S.D.g0).toMonoidHom :=
    htorus wb (by simp)
  obtain ⟨y, hy, hyu⟩ := hmemb
  have hy_eq : y = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wb : ModGL Tag.E6 K) * S.D.g0 := by
    have hh : S.D.g0 * y * S.D.g0⁻¹ =
        baseChangeGL (algebraMap K L) (wb : ModGL Tag.E6 K) := by
      have h := hyu
      change (MulAut.conj S.D.g0) y = _ at h
      simpa only [MulAut.conj_apply] using h
    calc y = S.D.g0⁻¹ * (S.D.g0 * y * S.D.g0⁻¹) * S.D.g0 := by group
      _ = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (wb : ModGL Tag.E6 K) * S.D.g0 := by
          rw [hh]
  have hyZ : y ∈ torusGroup Tag.E6 L ⊔
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_left (mem_twistedTorusOf.1 hy).1
  have hyF : S.D.step y = y := by
    simpa [LangDatum.step, MulAut.conj_apply] using (mem_twistedTorusOf.1 hy).2
  let ιLang : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 L :=
    (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp ι₀
  have hιLang_inj : Function.Injective ιLang :=
    (MulAut.conj S.D.g0⁻¹).injective.comp ((baseChangeGL_injective _).comp
      (Subgroup.subtype_injective _))
  have hιLang_range : ιLang.range = S.Γ := by
    change ιLang.range = D.Γ
    rw [show ιLang = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp ι₀ from rfl,
      MonoidHom.range_comp]
    exact hΓ.symm
  have hβd : ∀ c : ↥(adjointGroup Tag.E6 K),
      ιLang (TableBExc.E6Three.hatAut Tag.E6 K wd c) =
        rootDiagUnit Tag.E6 a * ιLang c * (rootDiagUnit Tag.E6 a)⁻¹ := by
    intro c
    have hb : ι₀ (TableBExc.E6Three.hatAut Tag.E6 K wd c) =
        baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K) *
          baseChangeGL (algebraMap K L) (c : ModGL Tag.E6 K) *
          (baseChangeGL (algebraMap K L) (wd : ModGL Tag.E6 K))⁻¹ := by
      rw [hι₀def]
      change baseChangeGL (algebraMap K L)
          ((TableBExc.E6Three.hatAut Tag.E6 K wd c : ModGL Tag.E6 K)) = _
      rw [TableBExc.E6Three.coe_hatAut_apply, map_mul, map_mul, map_inv]
    change S.D.g0⁻¹ * ι₀ (TableBExc.E6Three.hatAut Tag.E6 K wd c) * S.D.g0 =
      rootDiagUnit Tag.E6 a * (S.D.g0⁻¹ * baseChangeGL (algebraMap K L)
        (c : ModGL Tag.E6 K) * S.D.g0) * (rootDiagUnit Tag.E6 a)⁻¹
    rw [hb, hwd]
    group
  have hβb : ∀ c : ↥(adjointGroup Tag.E6 K),
      ιLang (TableBExc.E6Three.hatAut Tag.E6 K wb c) = y * ιLang c * y⁻¹ := by
    intro c
    have hb : ι₀ (TableBExc.E6Three.hatAut Tag.E6 K wb c) =
        baseChangeGL (algebraMap K L) (wb : ModGL Tag.E6 K) *
          baseChangeGL (algebraMap K L) (c : ModGL Tag.E6 K) *
          (baseChangeGL (algebraMap K L) (wb : ModGL Tag.E6 K))⁻¹ := by
      rw [hι₀def]
      change baseChangeGL (algebraMap K L)
          ((TableBExc.E6Three.hatAut Tag.E6 K wb c : ModGL Tag.E6 K)) = _
      rw [TableBExc.E6Three.coe_hatAut_apply, map_mul, map_mul, map_inv]
    change S.D.g0⁻¹ * ι₀ (TableBExc.E6Three.hatAut Tag.E6 K wb c) * S.D.g0 =
      y * (S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL Tag.E6 K) * S.D.g0) * y⁻¹
    rw [hb, hy_eq]
    group
  have h3L : (3 : L) ≠ 0 := by
    intro h0
    have h23 : 2 ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h0
    omega
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3L (fun h => by cases h) hT hap h1
  let C := ↥(adjointGroup Tag.E6 K)
  let ρR : C ≃* TableBExc.RecipeGroup Tag.E6 K := (TableBExc.recipeEquiv Tag.E6 K).symm
  let βd : MulAut C := TableBExc.E6Three.hatAut Tag.E6 K wd
  let βb : MulAut C := TableBExc.E6Three.hatAut Tag.E6 K wb
  have he_d : ∀ c : C, ρR (βd c) = e6RecipeConj wd (ρR c) := by
    intro c
    change ρR (βd c) = MulAut.congr ρR βd (ρR c)
    simp [MulAut.congr_apply]
  have he_b : ∀ c : C, ρR (βb c) = e6RecipeConj wb (ρR c) := by
    intro c
    change ρR (βb c) = MulAut.congr ρR βb (ρR c)
    simp [MulAut.congr_apply]
  have hρRrange : Kc ≤ ρR.toMonoidHom.range := by
    rintro x -
    exact ⟨ρR.symm x, ρR.apply_symm_apply x⟩
  have hKsub : CFSG.Assembly.IsComponentOf (Kc.comap ρR.toMonoidHom) (fixedSubgroup βd) :=
    CFSG.ComponentClassification.GSThmB.Catalog7L4EU.HarrisN36.isComponentOf_comap_of_intertwine
      ρR.toMonoidHom ρR.injective he_d hKc hρRrange
  have hKsub' : CFSG.Open.IsComponentOf (Kc.comap ρR.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup βd) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hKsub
  obtain ⟨Dc⟩ := nonempty_toralLangComp (φ := (e6RecipeConj wb).toMonoidHom)
    (hnorm := hnorm) S a ιLang hιLang_inj hιLang_range βd hβd hT hap h1 hTame (ρR := ρR) βb
    hβb he_b hKsub' hy hyZ hyF
  exact ⟨S, a, Dc, rfl, hT, hap, hpow, h1, hwd⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
