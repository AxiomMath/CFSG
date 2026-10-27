module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedStd
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.LocalAnalysis.GLTheoremA.T173X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ} {U : Fin l → Submodule F V}
  {ρ : Fin l → ↥(orthDerived Q)} {i j : Fin l} {A : Subgroup ↥(orthDerived Q)} {d : ↥(orthDerived Q)}

theorem mul_comm_of_mem_torus {T : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ T) {a b : ↥(orthDerived Q)}
    (ha : a ∈ T) (hb : b ∈ T) : a * b = b * a := by
  have h := hF.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem mem_orthDerived_of_odd_pow_of_six_le {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (R : QuadraticForm F W) (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h6 : 6 ≤ Module.finrank F W)
    {g : W ≃ₗ[F] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) :
    g ∈ orthDerived R := by
  have hΩ := CFSG.RankThree.PartOne.mem_omegaGroup_of_pow_eq_one hR hn hg hgn
  by_cases hT : ∃ T : Submodule F W, Module.finrank F T = 3 ∧ ∀ x ∈ T, R x = 0
  · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT hΩ
  · have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have hAlt : (QuadraticMap.polarBilin R).IsAlt := fun v => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul,
        CharTwo.add_self_eq_zero]
    obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank (B := QuadraticMap.polarBilin R) hAlt hR
    have hdim : Module.finrank F W = 2 * m := by omega
    have hm3 : 3 ≤ m := by omega
    by_cases hm4 : 4 ≤ m
    · exact absurd (CFSG.RankThree.PartOne.exists_threeSingular_of_dim R hR hm4 hdim) hT
    · have hdim6 : Module.finrank F W = 6 := by omega
      have hts : ∀ T : Submodule F W, Module.finrank F T = 3 → ∃ u ∈ T, R u ≠ 0 := by
        intro T hT3
        by_contra h
        push Not at h
        exact hT ⟨T, hT3, fun u hu => h u hu⟩
      exact CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six hR hdim6 hts hΩ

private theorem rho_mem_supportedFixedDerived_aux1 (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : IsStdElt p A d)
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j)) {k : Fin l} (hki : k ≠ i) (hkj : k ≠ j) :
    (ρ k : V ≃ₗ[F] V) ∈ supportedBlock Q (d : V ≃ₗ[F] V) (X - 1) := by
  have hx := oddOrderIsometry_of_std hQ hp hp2 hd
  have hcomm : (ρ k : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V) = (d : V ≃ₗ[F] V) * (ρ k : V ≃ₗ[F] V) := by
    have h := mul_comm_of_mem_torus hM.frame (Subgroup.subset_closure ⟨k, rfl⟩) (hM.le_torus hd.1)
    exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) h
  have hfix : ∀ v ∈ othersSpace (d : V ≃ₗ[F] V).toLinearMap (X - 1), (ρ k : V ≃ₗ[F] V) v = v := by
    intro v hv
    rw [← CFSG.RankThree.PartOne.KCOrthogonalD4.orthPerp_fixedSpace hx, hfs] at hv
    change v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (U i ⊔ U j)) at hv
    rw [LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q)] at hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    congr 1
    · refine hM.frame.apply_of_perp k a (mem_polarPerp_iff.2 fun y hy => ?_)
      rw [QuadraticMap.polar_comm]
      exact hM.frame.perp i k (fun h => hki h.symm) a ha y hy
    · refine hM.frame.apply_of_perp k b (mem_polarPerp_iff.2 fun y hy => ?_)
      rw [QuadraticMap.polar_comm]
      exact hM.frame.perp j k (fun h => hkj h.symm) b hb y hy
  refine mem_supportedBlock.mpr ⟨?_, hfix⟩
  refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (ρ k).2) v
  · have hv := congrFun (congrArg (fun e : V ≃ₗ[F] V => (e : V → V)) hcomm) v
    simpa only [LinearEquiv.mul_apply] using hv

theorem rho_mem_supportedFixedDerived (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl5 : 5 ≤ l)
    (hp : p.Prime) (hp2 : p ≠ 2) (hd : IsStdElt p A d)
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j)) {k : Fin l} (hki : k ≠ i) (hkj : k ≠ j) :
    (ρ k : V ≃ₗ[F] V) ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V) := by
  have hblock := rho_mem_supportedFixedDerived_aux1 hM hQ hp hp2 hd hfs hki hkj
  have hx := oddOrderIsometry_of_std hQ hp hp2 hd
  have hW : (QuadraticMap.polarBilin (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have h4 : Module.finrank F (U i ⊔ U j : Submodule F V) = 4 := by
    have h := hM.frame.toIsPlaneSystem.finrank_biSup ({i, j} : Finset (Fin l))
    have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k) = U i ⊔ U j := by
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    rw [e] at h
    rw [Finset.card_pair hM.ne] at h
    omega
  have hdimW : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * l - 4 := by
    rw [hfs, finrank_polarPerp hQ, h4, hdim]
  have h6 : 6 ≤ Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) := by omega
  refine mem_supportedFixedDerived.mpr ⟨hblock, ?_⟩
  refine mem_orthDerived_of_odd_pow_of_six_le (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)
    hW h6 ?_ (hp.odd_of_ne_two hp2) ?_
  · exact restrictFixed_mem_orthogonalGroup (Q := Q) (x := (d : V ≃ₗ[F] V)) ⟨(ρ k : V ≃ₗ[F] V), hblock⟩
  · have hρp_sub : (ρ k) ^ p = 1 := by
      rw [← hM.frame.orderOf_eq k]
      exact pow_orderOf_eq_one _
    have hρp : ((ρ k : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p = 1 := by
      simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hρp_sub
    have hpow : (⟨(ρ k : V ≃ₗ[F] V), hblock⟩ : ↥(supportedBlock Q (d : V ≃ₗ[F] V) (X - 1))) ^ p = 1 :=
      Subtype.ext hρp
    rw [← map_pow, hpow, map_one]

private theorem layer_fixes_pair_aux1 (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d)
    (hdz : d ∈ Subgroup.zpowers (ρ i * ρ j)) (hi : ∀ x ∈ U i, (d : V ≃ₗ[F] V) x = x) : d = 1 := by
  have hj := (hM.apply_eq_iff hp hp2 hpq hd.1).1 hi
  refine hM.frame.eq_one_of_forall_apply_eq (hM.le_torus hd.1) ?_
  intro k x hx
  by_cases hki : k = i
  · subst hki
    exact hi x hx
  by_cases hkj : k = j
  · subst hkj
    exact hj x hx
  have hπfix : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
    show (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) x) = x
    have hxj : x ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
      hM.frame.perp j k (fun h => hkj h.symm) y hy x hx
    have hxi : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy =>
      hM.frame.perp i k (fun h => hki h.symm) y hy x hx
    rw [hM.frame.apply_of_perp j x hxj, hM.frame.apply_of_perp i x hxi]
  have hπst : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) ∈
      MulAction.stabilizer (V ≃ₗ[F] V) x :=
    (MulAction.mem_stabilizer_iff).2 hπfix
  have hdst : (d : V ≃ₗ[F] V) ∈ MulAction.stabilizer (V ≃ₗ[F] V) x := by
    have hdz' : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers
        (((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V)) := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hdz
      refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
      rw [← Subgroup.coe_zpow]
      exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hm
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (V ≃ₗ[F] V) x)).2 hπst hdz'
  exact (MulAction.mem_stabilizer_iff).1 hdst

theorem layer_fixes_pair (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d) (hdz : d ∈ Subgroup.zpowers (ρ i * ρ j))
    (hL : stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    ∀ g ∈ stdLayer d, ∀ v ∈ U i ⊔ U j, (g : V ≃ₗ[F] V) v = v := by
  have hnontriv_i : ¬ ∀ x ∈ U i, (d : V ≃ₗ[F] V) x = x := fun hi => hd.2.1 (layer_fixes_pair_aux1 hM hp hp2 hpq hd hdz hi)
  have hnontriv_j : ¬ ∀ x ∈ U j, (d : V ≃ₗ[F] V) x = x := fun hj =>
    hd.2.1 (layer_fixes_pair_aux1 hM hp hp2 hpq hd hdz ((hM.apply_eq_iff hp hp2 hpq hd.1).2 hj))
  have hfixi : ∀ g ∈ stdLayer d, ∀ v ∈ U i, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    obtain ⟨k, hk, hUk⟩ := hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) i
    have hk1 : k ≠ X - 1 := by
      rintro rfl
      refine hnontriv_i fun w hw => ?_
      have hw' : w ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - 1) := hUk hw
      rw [← fixedSpace_eq_primaryComponent] at hw'
      exact mem_fixedSpace.1 hw'
    exact fixes_of_layer_omega (G := supportedFixedDerived Q (d : V ≃ₗ[F] V)) le_rfl hk hk1 hL g hg v (hUk hv)
  have hfixj : ∀ g ∈ stdLayer d, ∀ v ∈ U j, (g : V ≃ₗ[F] V) v = v := by
    intro g hg v hv
    obtain ⟨k, hk, hUk⟩ := hM.frame.exists_le_primaryComponent hp hp2 hpq (hM.le_torus hd.1) j
    have hk1 : k ≠ X - 1 := by
      rintro rfl
      refine hnontriv_j fun w hw => ?_
      have hw' : w ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - 1) := hUk hw
      rw [← fixedSpace_eq_primaryComponent] at hw'
      exact mem_fixedSpace.1 hw'
    exact fixes_of_layer_omega (G := supportedFixedDerived Q (d : V ≃ₗ[F] V)) le_rfl hk hk1 hL g hg v (hUk hv)
  intro g hg v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, hfixi g hg x hx, hfixj g hg y hy]

private theorem stdExtends_of_pair_part1 (hM : IsMixedFrame Q p U ρ i j A) :
    (QuadraticMap.polarBilin (Q.comp (U i ⊔ U j).subtype)).Nondegenerate := by
  have e : (⨆ k ∈ ({i, j} : Finset (Fin l)), U k : Submodule F V) = U i ⊔ U j := by
    rw [Finset.iSup_insert, Finset.iSup_singleton]
  rw [← e]
  exact hM.frame.toIsPlaneSystem.nondeg_biSup ({i, j} : Finset (Fin l))

private theorem stdExtends_of_pair_part2 (hM : IsMixedFrame Q p U ρ i j A)
    (hP : (QuadraticMap.polarBilin (Q.comp (U i ⊔ U j).subtype)).Nondegenerate)
    (hfix : ∀ g ∈ stdLayer d, ∀ v ∈ U i ⊔ U j, (g : V ≃ₗ[F] V) v = v) :
    ρ i * ρ j ∈ Subgroup.centralizer (stdLayer d : Set ↥(orthDerived Q)) := by
  refine Subgroup.mem_centralizer_iff.2 fun g hg => Subtype.ext ?_
  refine commute_of_apply_eq hP (orthDerived_le_orthogonalGroup g.2) (hfix g hg) ?_ ?_
  · intro x hx
    obtain ⟨xi, hxi, xj, hxj, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : (ρ i : V ≃ₗ[F] V) xi ∈ U i := hM.frame.maps_to i xi hxi
    have h2 : (ρ j : V ≃ₗ[F] V) xj ∈ U j := hM.frame.maps_to j xj hxj
    have h3 : (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) xj) = (ρ j : V ≃ₗ[F] V) xj :=
      hM.frame.apply_of_perp i _ (mem_polarPerp_iff.2 fun y hy => hM.frame.perp i j hM.ne y hy _ h2)
    have h4 : (ρ j : V ≃ₗ[F] V) xi = xi :=
      hM.frame.apply_of_perp j xi (mem_polarPerp_iff.2 fun y hy => hM.frame.perp j i (Ne.symm hM.ne) y hy xi hxi)
    show (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) (xi + xj)) ∈ U i ⊔ U j
    rw [map_add, h4, map_add, h3]
    exact Submodule.add_mem_sup h1 h2
  · intro x hx
    have hxi : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy =>
      mem_polarPerp_iff.1 hx y (Submodule.mem_sup_left hy)
    have hxj : x ∈ polarPerp Q (U j) := mem_polarPerp_iff.2 fun y hy =>
      mem_polarPerp_iff.1 hx y (Submodule.mem_sup_right hy)
    show (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) x) = x
    rw [hM.frame.apply_of_perp j x hxj, hM.frame.apply_of_perp i x hxi]

theorem stdExtends_of_pair (hM : IsMixedFrame Q p U ρ i j A)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank F V = 2 * l) (hl5 : 5 ≤ l)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hd : IsStdElt p A d)
    (hdz : d ∈ Subgroup.zpowers (ρ i * ρ j)) (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U i ⊔ U j))
    (hL : stdLayer d = (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :
    StdExtends p A d := by
  have hOg : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => orthDerived_le_orthogonalGroup g.2
  have hfix := layer_fixes_pair hM hp hp2 hpq hd hdz hL
  have hP := stdExtends_of_pair_part1 hM
  have hπ := stdExtends_of_pair_part2 hM hP hfix
  refine ⟨?_, ρ i, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    conv_lhs => rw [hM.eq_closure]
    rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨k, ⟨hki, hkj⟩, rfl⟩)
    · exact Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hM.pair_mem, hπ⟩)
    · refine Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hM.rho_mem hki hkj, ?_⟩)
      rw [hL]
      exact Subgroup.mem_subgroupOf.2 (rho_mem_supportedFixedDerived hM hQ hdim hl5 hp hp2 hd hfs hki hkj)
  · refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
    exact mul_comm_of_mem_torus hM.frame (hM.le_torus ha) (Subgroup.subset_closure ⟨i, rfl⟩)
  · refine Subgroup.mem_centralizer_iff.2 fun g hg => Subtype.ext ?_
    exact commute_of_apply_eq (hM.frame.nondeg i) (hOg g)
      (fun v hv => hfix g hg v (Submodule.mem_sup_left hv)) (hM.frame.maps_to i) (hM.frame.apply_of_perp i)
  · rw [← hM.frame.orderOf_eq i]
    exact pow_orderOf_eq_one _
  · intro hA'
    have hj : ∀ x ∈ U j, (ρ i : V ≃ₗ[F] V) x = x := fun x hx =>
      hM.frame.apply_of_perp i x (mem_polarPerp_iff.2 fun y hy => hM.frame.perp i j hM.ne y hy x hx)
    have hi := (hM.apply_eq_iff hp hp2 hpq hA').2 hj
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hM.frame.finrank_eq i)
    exact hv0 (hM.frame.eq_zero_of_apply_eq i v hv (hi v hv))

end CFSG.LocalAnalysis.GLTheoremA.T173M

end
