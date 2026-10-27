module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement


theorem excAdjCompInnAut_of (hK : ExcKernelCompAction)
    (hE : E6CentralizerConnOddExcKernels) : ExcAdjCompInnAut := by
  intro τ hτ K _ _ _ p hp hp2 hG2 hE6 x w hx1 hxp hwp hxw Kc hKc h360 hw
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hqK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hqK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hqK]
    intro h
    have h2 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
    norm_num at h2
  have hτD4 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h | h <;> simp [h]
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτD4 hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    (isPerfect_adjointGroup τ K (fun h => le_trans (by norm_num) (hG2 h))).commutator_eq_top
  let β : MulAut ↥(adjointGroup τ K) := MulAut.conj x
  have hβ : ∀ c, (β c : ModGL τ K) = (x : ModGL τ K) * c * (x : ModGL τ K)⁻¹ := by
    intro c
    change (MulAut.conj x c : ModGL τ K) = _
    rw [MulAut.conj_apply]
    rfl
  have hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) ∈
      adjointGroup τ (AlgebraicClosure K) :=
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ x.2
  have hxp' : (x : ModGL τ K) ^ p = 1 := by
    simpa using congrArg (fun z : ↥(adjointGroup τ K) => (z : ModGL τ K)) hxp
  have hxne : (x : ModGL τ K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨S, a, ι, hq, huntw, hT, hap, h1, hinj, hrange, hconjι⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ hp hpK Nat.prime_five h5K (Or.inl le_rfl)
      hmon hperf β (x : ModGL τ K) hhL hβ hxp' hxne
  let L := AlgebraicClosure K
  have hfixEq : fixSubgroup (MulAut.conj x) =
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x) :=
    Subgroup.ext fun _ => Iff.rfl
  have hKc' : CFSG.Open.IsComponentOf Kc (fixSubgroup (MulAut.conj x)) := by
    rw [hfixEq]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hKc
  have hsmallTame : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := fun h =>
    Or.inr (by rw [hq]; exact hG2 h)
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure hp hpK
  have hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    langSetup_hTame_of_prime S hp hpL hsmallTame hT hap h1
  obtain ⟨i, hqs, hKR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S hp ι hinj hrange
      (MulAut.conj x) hconjι hT hap h1 hTame hKc'
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  let eJ : ↥Kc ≃* ↥R :=
    (Kc.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hKR)
  have heJ : ∀ k : Kc, (eJ k : ModGL τ (AlgebraicClosure K)) = ι k := fun k => rfl
  have hc : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) =
      Nat.card (↥R ⧸ Subgroup.center ↥R) :=
    Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥Kc) (Subgroup.center ↥R) eJ
      (Subgroup.map_center_eq eJ)).toEquiv
  have hNR : Nat.card (↥R ⧸ Subgroup.center ↥R) ≠ 360 := fun h => h360 (hc.trans h)
  set y : ModGL τ (AlgebraicClosure K) := ι w with hydef
  have hyΓ : y ∈ S.Γ := by
    rw [hydef, ← hrange]
    exact ⟨w, rfl⟩
  have hyF : S.D.step y = y := ((Subgroup.commutator_le_self S.D.model) hyΓ).2
  have hyG : y ∈ adjointGroup τ L := ((Subgroup.commutator_le_self S.D.model) hyΓ).1
  have hγconj : ∀ c, rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ =
      ι x * ι c * (ι x)⁻¹ := by
    intro c
    rw [← hconjι c]
    change ι ((MulAut.conj x) c) = ι x * ι c * (ι x)⁻¹
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hιxw : ι x * y * (ι x)⁻¹ = y := by
    have hxwx : x * w * x⁻¹ = w := by rw [hxw, mul_inv_cancel_right]
    have h1' : ι (x * w * x⁻¹) = ι w := by rw [hxwx]
    rw [hydef]
    simpa only [map_mul, map_inv] using h1'
  have hyd : rootDiagUnit τ a * y * (rootDiagUnit τ a)⁻¹ = y := by
    rw [hydef, hγconj w]
    exact hιxw
  have hφy : ∀ c, ι ((MulAut.conj w) c) = y * ι c * y⁻¹ := by
    intro c
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hydef]
  have hyC : y ∈ toralCentralizer τ L a := mem_toralCentralizer.2 ⟨hyG, hyd⟩
  have hTp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  have hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := by
    by_cases hcase : τ = .E6 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hcase
      have hconn := e6CentralizerConnOdd_holds (hsmall := hE)
      have hq3 : ¬ 3 ∣ S.D.q - 1 := by
        rw [hq]
        simpa using hE6 rfl rfl
      have huntw' : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
          (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) := by
        obtain ⟨Fr, hFr, hΦ⟩ := huntw
        exact ⟨Fr, fun c => by rw [hq, hFr], hΦ⟩
      exact hconn (L := L) (p₀ := 5) S huntw' hq3 a hT hap y hyC hyF
    · have hE6' : τ = .E6 → p ≠ 3 := fun h h3 => hcase ⟨h, h3⟩
      have hW := rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2 hτD4
        hE6' hap
      have hZeq := toralCentralizer_eq_toralRootGroup_of_stabilizer_le τ L a hW
      rwa [hZeq] at hyC
  have hyR : MulAut.conj y ∈ subgroupStabAut R := by
    change R.map (MulAut.conj y).toMonoidHom = R
    have hcomp : (MulAut.conj y).toMonoidHom.comp ι =
        ι.comp (MulAut.conj w).toMonoidHom := by
      ext c
      simp [MonoidHom.comp_apply, MulAut.conj_apply, hφy, hydef]
    have hwK : Kc.map (MulAut.conj w).toMonoidHom = Kc := hw
    rw [← hKR, Subgroup.map_map, hcomp, ← Subgroup.map_map, hwK]
  have hmain : centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hyR⟩) ∈
      innAutDerived (↥R ⧸ Subgroup.center ↥R) :=
    hK S (by norm_num) (by norm_num) hp hp2 hτD4 hT hap hTp h1
      (fun h => by rw [hq]; exact hG2 h) i hqs hNR hyZ hyF hyR
  refine centerQuotientHom_mem_innAutDerived_of_mulEquiv_kd264alg eJ ?_ hmain
  intro k
  apply Subtype.ext
  rw [heJ, subgroupStabRestrict_apply, subgroupStabRestrict_apply, heJ, MulAut.conj_apply]
  exact hφy k

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
