module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsGlue
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141d2
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
public import CFSG.RankThree.PartOne.F106.OddRadOrthInner
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitBasic
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
import CFSG.Quasithin.Vol2.Ch11SecOE5B
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open Module Polynomial
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.RankThree.PartOne (map_centralizer_eq_centralizerImage)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
open CFSG.ClassicalGroups.Orthogonal
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d
  (exists_fixedFactors_comm supportedBlock_le_orthDerived
    mem_supportedFixedDerived_of_mem_orthDerived orth_component_cases)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem fixSubgroup_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem exists_decomp_supportedBlock {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} [CharP K 2]
    {p : ℕ} {x : V ≃ₗ[K] V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hx : OddOrderIsometry Q p x) (hp : Odd p) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {y : V ≃ₗ[K] V}
    (hy : y ∈ isometryCentralizer Q x) (hyΩ : y ∈ orthDerived Q) :
    ∃ w ∈ supportedBlock Q x (X - 1), w ∈ orthDerived Q ∧
      ∃ z ∈ ⨆ r : {r : ↥Rep // (r : K[X]) ≠ X - 1}, supportedBlock Q x ((r.1 : K[X])),
        y = w * z ∧ ∀ g ∈ supportedBlock Q x (X - 1), Commute g z := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set A : {r : ↥Rep // (r : K[X]) ≠ X - 1} → Subgroup (V ≃ₗ[K] V) :=
    fun r => supportedBlock Q x ((r.1 : K[X]))
  have hle : isometryCentralizer Q x ≤ supportedBlock Q x (X - 1) ⊔ ⨆ r, A r := by
    rw [← hx.blocks_iSup_eq hRep]
    refine iSup_le fun i => ?_
    by_cases hi : (i : K[X]) = X - 1
    · rw [hi]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup A ⟨i, hi⟩)
  have hcomm : ∀ a ∈ supportedBlock Q x (X - 1), ∀ c ∈ ⨆ r, A r, a * c = c * a := by
    intro a ha c hc
    by_cases hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
    · have hle' : (⨆ r, A r) ≤
          Subgroup.centralizer (supportedBlock Q x (X - 1) : Set (V ≃ₗ[K] V)) :=
        iSup_le fun r g hg => Subgroup.mem_centralizer_iff.2 fun a ha =>
          (hx.commute_supportedBlock hX (hRep.1 r.1.2) r.2
            (by rw [reciprocalPolynomial_X_sub_one]; exact r.2) ha hg).eq
      exact Subgroup.mem_centralizer_iff.1 (hle' hc) a ha
    · have ha1 : a = 1 := by
        refine hx.eq_one_of_restrictFixed_eq_one ha (LinearEquiv.ext fun v => Subtype.ext ?_)
        have hv : (v : V) ∈ (⊥ : Submodule K V) := by
          rw [← fixedSpace_eq_bot_of_not_mem hX]
          exact v.2
        have h0 : (v : V) = 0 := (Submodule.mem_bot K).1 hv
        have h1 : ((restrictFixed Q x ⟨a, ha⟩ v : fixedSpace x) : V) ∈ (⊥ : Submodule K V) := by
          rw [← fixedSpace_eq_bot_of_not_mem hX]
          exact (restrictFixed Q x ⟨a, ha⟩ v).2
        rw [(Submodule.mem_bot K).1 h1]
        exact h0.symm
      rw [ha1, one_mul, mul_one]
  obtain ⟨w, hw, z, hz, hyz⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input183.mem_sup_of_commute hcomm (hle hy)
  have hzΩ : z ∈ orthDerived Q :=
    iSup_le (fun r => supportedBlock_le_orthDerived hQ hT hx hp (hRep.1 r.1.2) r.2) hz
  have hwΩ : w ∈ orthDerived Q := by
    have hw_eq : w = y * z⁻¹ := by rw [hyz]; group
    rw [hw_eq]
    exact mul_mem hyΩ (inv_mem hzΩ)
  exact ⟨w, hw, hwΩ, z, hz, hyz, fun g hg => hcomm g hg z hz⟩

private theorem conj_mem_fixedFactor {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} [CharP K 2]
    {p : ℕ} {x : V ≃ₗ[K] V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hx : OddOrderIsometry Q p x) (hp : Odd p) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {n : ℕ} {F : Fin n → Subgroup (V ≃ₗ[K] V)}
    (hFq : ∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
      ((F i).subgroupOf (supportedFixedDerived Q x)).Normal)
    (hFn0 : ¬ FixedLayerListed Q x → n = 0)
    {c g : V ≃ₗ[K] V} (hc : c ∈ isometryCentralizer Q x) (hcΩ : c ∈ orthDerived Q)
    {i : Fin n} (hg : g ∈ F i) : c * g * c⁻¹ ∈ F i := by
  have hlist : FixedLayerListed Q x := by
    by_contra h
    exact Fin.elim0 (hFn0 h ▸ i)
  obtain ⟨w, hw, hwΩ, z, hz, hyz, hzcomm⟩ :=
    exists_decomp_supportedBlock hQ hT hx hp hRep hc hcΩ
  have hw' : w ∈ supportedFixedDerived Q x :=
    mem_supportedFixedDerived_of_mem_orthDerived hQ hx hp hlist hw hwΩ
  have hg' : g ∈ supportedFixedDerived Q x := (hFq i).2.1 hg
  have hgf : g ∈ supportedBlock Q x (X - 1) :=
    (hFq i).2.1.trans supportedFixedDerived_le_supportedBlock hg
  have hconj : w * g * w⁻¹ ∈ F i :=
    (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 g w hg hw'
  have hz1 : z * g * z⁻¹ = g := by
    rw [← (hzcomm g hgf).eq, mul_inv_cancel_right]
  have hmain : c * g * c⁻¹ = w * g * w⁻¹ := by
    rw [hyz, mul_inv_rev]
    calc (w * z) * g * (z⁻¹ * w⁻¹) = w * (z * g * z⁻¹) * w⁻¹ := by
          simp only [mul_assoc]
      _ = w * g * w⁻¹ := by rw [hz1]
  rw [hmain]
  exact hconj

private noncomputable def projImage {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (H : Subgroup ↥(orthDerived Q)) : Subgroup (ProjOrthDerived Q) :=
  H.map (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))

private theorem exists_factor_image_of_isComponentOf {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : ↥(orthDerived Q)}
    (hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V)) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep) {n : ℕ}
    {F : Fin n → Subgroup (V ≃ₗ[K] V)}
    (hFq : ∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q (x : V ≃ₗ[K] V) ∧
      ((F i).subgroupOf (supportedFixedDerived Q (x : V ≃ₗ[K] V))).Normal)
    (hFsup : FixedLayerListed Q (x : V ≃ₗ[K] V) →
      ⨆ i, F i = supportedFixedDerived Q (x : V ≃ₗ[K] V))
    (hFn0 : ¬ FixedLayerListed Q (x : V ≃ₗ[K] V) → n = 0)
    (Fm : ↥Rep ⊕ Fin n → Subgroup ↥(orthDerived Q))
    (hFm_inl : ∀ r, Fm (Sum.inl r) =
      (specialBlock Q (x : V ≃ₗ[K] V) r.1).subgroupOf (orthDerived Q))
    (hFm_inr : ∀ i, Fm (Sum.inr i) = (F i).subgroupOf (orthDerived Q))
    {a : ProjOrthDerived Q}
    (hfix : fixSubgroup (MulAut.conj a) = centralizerImage Q (x : V ≃ₗ[K] V))
    {J : Subgroup (ProjOrthDerived Q)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a))) :
    ∃ i, J = projImage (Fm i) := by
  rw [hfix] at hJ
  rcases orth_component_cases hp hp2 hQ x hx hRep hFq hFsup hFn0 hJ with
    ⟨r, hr, -, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨Sum.inl ⟨r, hr⟩, by rw [hFm_inl]; rfl⟩
  · exact ⟨Sum.inr i, by rw [hFm_inr]; rfl⟩

theorem compNormal_conj_projOrth_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (a : ProjOrthDerived Q) (ha : a ^ p = 1) (ha1 : a ≠ 1) :
    CFSG.LocalAnalysis.GLTheoremA.S267.Gen.CompNormal (MulAut.conj a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcenter, hZ2, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hpℓ : p ≠ ringChar K := by rw [ringChar.eq (R := K) 2]; exact hp2
  obtain ⟨x, ⟨hxa, hxp⟩, -, hcent⟩ := hlift p hp hp2 a (orderOf_eq_prime ha ha1)
  have hx : OddOrderIsometry Q p (x : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived hp hpℓ hQ x hxp
  have hxp1 : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hFq, hFcomm, hFsup, hFn0⟩ := exists_fixedFactors_comm hx
  let Fm : ↥Rep ⊕ Fin n → Subgroup ↥(orthDerived Q) :=
    Sum.elim (fun r => (specialBlock Q (x : V ≃ₗ[K] V) r.1).subgroupOf (orthDerived Q))
      (fun i => (F i).subgroupOf (orthDerived Q))
  have hFn : ∀ i, ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ g ∈ Fm i, c * g * c⁻¹ ∈ Fm i := by
    intro i c hc g hg
    have hcx : c * x = x * c := by
      have h := mem_fixSubgroup.mp hc
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hcI : (c : V ≃ₗ[K] V) ∈ isometryCentralizer Q (x : V ≃ₗ[K] V) :=
      Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup c.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcx)⟩
    rcases i with r | i
    · exact Subgroup.mem_subgroupOf.mpr
        (conj_mem_specialBlock hcI (Subgroup.mem_subgroupOf.mp hg))
    · exact Subgroup.mem_subgroupOf.mpr
        (conj_mem_fixedFactor hQ hT hx (hp.odd_of_ne_two hp2) hRep hFq hFn0 hcI c.2
          (Subgroup.mem_subgroupOf.mp hg))
  have hfix : fixSubgroup (MulAut.conj a) = centralizerImage Q (x : V ≃ₗ[K] V) := by
    rw [fixSubgroup_conj_eq_centralizer, hcent]
    exact map_centralizer_eq_centralizerImage x
  have hcomp : ∀ J : Subgroup (ProjOrthDerived Q),
      CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)) → ∃ i, J = projImage (Fm i) :=
    fun J hJ => exists_factor_image_of_isComponentOf hp hp2 hQ hx hRep hFq hFsup hFn0 Fm
      (fun r => rfl) (fun i => rfl) hfix hJ
  have hαβ : ∀ g, (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
      (MulAut.conj x g) =
      MulAut.conj a ((QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) g) := by
    intro g
    simp only [MulAut.conj_apply, map_mul, map_inv, QuotientGroup.mk'_apply, hxa]
  have hαp : (MulAut.conj x) ^ p = 1 := by rw [← map_pow, hxp1, map_one]
  have hαZ : ∀ z ∈ (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker,
      MulAut.conj x z = z := by
    intro z hz
    rw [QuotientGroup.ker_mk', ← hcenter] at hz
    rw [MulAut.conj_apply, Subgroup.mem_center_iff.mp hz x, mul_inv_cancel_right]
  have hZp : ∀ z ∈ (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker,
      z ^ p = 1 → z = 1 := by
    intro z hz hzp
    rw [QuotientGroup.ker_mk'] at hz
    have h1 : orderOf z ∣ Nat.card ((scalars K V).subgroupOf (orthDerived Q)) :=
      Subgroup.orderOf_dvd_natCard _ hz
    have hle := Nat.le_of_dvd Nat.card_pos h1
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzp) with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have := hp.two_le
      omega
  exact CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_of_lift
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
    (QuotientGroup.mk'_surjective _) (MulAut.conj x) (MulAut.conj a) hαβ (p := p)
    hαp hαZ hZp Fm hFn hcomp

theorem shapeModelNormAt_projOrth_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    ShapeModelNormAt (ProjOrthDerived Q) p := by
  have : Fact p.Prime := ⟨hp⟩
  intro x y hx1 hxp hyp hxy J hJ
  have hpℓ : p ≠ ringChar K := by rw [ringChar.eq (R := K) 2]; exact hp2
  have hPL :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_projOrth_of_orderOf
      hQ hT hp hp2 hpℓ x (orderOf_eq_prime hxp hx1)
  have hCN := compNormal_conj_projOrth_two hp hp2 hQ hT x hxp hx1
  have hfix := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.fixSubgroup_conj_eq x
  rw [← hfix] at hJ
  have hperf := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hJ
  have hle := hPL J hJ.1 hperf
  have hcomp :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hle).1
  have hy : y ∈ fixSubgroup (MulAut.conj x) := by
    rw [hfix, Subgroup.mem_centralizer_singleton_iff]
    exact hxy.symm.eq
  exact hCN J hcomp hy

end CFSG.LocalAnalysis.GLTheoremA.F151

end
