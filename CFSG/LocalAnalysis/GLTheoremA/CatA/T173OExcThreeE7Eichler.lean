module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniVanish
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedPair
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRankR

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCOrthogonalD4 CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.LocalAnalysis.GLTheoremA.T173M CFSG.LocalAnalysis.GLTheoremA.T173U

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_eichler_ne_one_of_three_le (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {W : Submodule F V} (hW : 3 ≤ Module.finrank F W) :
    ∃ u ∈ W, ∃ w ∈ W, Q u = 0 ∧ QuadraticMap.polar Q u w = 0 ∧ eichler Q u w ≠ 1 := by
  obtain ⟨u, huW, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) hW
  obtain ⟨w, hwW, huw, hwspan⟩ := exists_mem_orth_not_span (Q := Q) (S := W) hW u
  refine ⟨u, huW, w, hwW, huQ, huw, fun h => ?_⟩
  obtain ⟨a, ha⟩ := (eichler_eq_one_iff hQ huQ hu0 huw).1 h
  exact hwspan (Submodule.mem_span_singleton.2 ⟨a, ha.symm⟩)

theorem zpowers_eichler_ne_bot_and_isPGroup {u w : V} (hu : Q u = 0)
    (huw : QuadraticMap.polar Q u w = 0) (hE : eichler Q u w ∈ orthDerived Q)
    (hE1 : eichler Q u w ≠ 1) :
    Subgroup.zpowers (⟨eichler Q u w, hE⟩ : ↥(orthDerived Q)) ≠ ⊥ ∧
      IsPGroup 2 (Subgroup.zpowers (⟨eichler Q u w, hE⟩ : ↥(orthDerived Q))) := by
  have hww : w + w = 0 := by
    rw [← two_smul F w, CharTwo.two_eq_zero, zero_smul]
  have hsq : eichler Q u w ^ 2 = 1 := by
    rw [pow_two, eichler_mul huw huw, hww, eichler_zero_right]
  have hsq' : (⟨eichler Q u w, hE⟩ : ↥(orthDerived Q)) ^ 2 = 1 := by
    refine Subtype.ext ?_
    simpa using hsq
  have hord : orderOf (⟨eichler Q u w, hE⟩ : ↥(orthDerived Q)) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.2 hsq'
  refine ⟨?_, ?_⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    exact fun h => hE1 (by simpa using congrArg Subtype.val h)
  · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using hord

private theorem mem_supportedBlock_of_weightOne_aux (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) {U : Fin n → Submodule F V}
    {e : Fin n → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (hd1 : d ≠ 1) {j : Fin n}
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j)) {i : Fin n} (hij : i ≠ j) :
    (e i : V ≃ₗ[F] V) ∈ supportedBlock Q (d : V ≃ₗ[F] V) (X - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have hcomm : (e i : V ≃ₗ[F] V) * (d : V ≃ₗ[F] V) = (d : V ≃ₗ[F] V) * (e i : V ≃ₗ[F] V) := by
    have h := mul_comm_of_mem_torus hF (hF.mem i) hd
    exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) h
  have hfix : ∀ v ∈ othersSpace (d : V ≃ₗ[F] V).toLinearMap (X - 1),
      (e i : V ≃ₗ[F] V) v = v := by
    intro v hv
    rw [← CFSG.RankThree.PartOne.KCOrthogonalD4.orthPerp_fixedSpace hx, hfs] at hv
    change v ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (U j)) at hv
    rw [LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q)] at hv
    exact hF.apply_of_perp i v (mem_polarPerp_iff.2 fun y hy => hF.perp i j hij y hy v hv)
  refine mem_supportedBlock.mpr ⟨?_, hfix⟩
  refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (orthDerived_le_orthogonalGroup (e i).2) v
  · have hv := congrFun (congrArg (fun z : V ≃ₗ[F] V => (z : V → V)) hcomm) v
    simpa only [LinearEquiv.mul_apply] using hv

theorem mem_supportedFixedDerived_of_weightOne (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)} (hd : d ∈ Bb) (hd1 : d ≠ 1) {j : Fin n}
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j)) {i : Fin n} (hij : i ≠ j) :
    (e i : V ≃ₗ[F] V) ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hblock := mem_supportedBlock_of_weightOne_aux hQ hn hp hp2 hF hd hd1 hfs hij
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have hW : (QuadraticMap.polarBilin (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    hx.polarBilin_fixed_nondegenerate
  have hdimW : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * n - 2 := by
    rw [hfs, finrank_polarPerp hQ (U j), hF.finrank_eq j, hdim]
  have h6 : 6 ≤ Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) := by
    rw [hdimW]
    omega
  refine mem_supportedFixedDerived.mpr ⟨hblock, ?_⟩
  refine mem_orthDerived_of_odd_pow_of_six_le (Q.comp (fixedSpace (d : V ≃ₗ[F] V)).subtype)
    hW h6 ?_ (hp.odd_of_ne_two hp2) ?_
  · exact restrictFixed_mem_orthogonalGroup (Q := Q) (x := (d : V ≃ₗ[F] V))
      ⟨(e i : V ≃ₗ[F] V), hblock⟩
  · have hep : (e i) ^ p = 1 := by
      rw [← hF.orderOf_eq i]
      exact pow_orderOf_eq_one _
    have hcoe : ((e i : ↥(orthDerived Q)) : V ≃ₗ[F] V) ^ p = 1 := by
      simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hep
    have hpow : (⟨(e i : V ≃ₗ[F] V), hblock⟩ :
        ↥(supportedBlock Q (d : V ≃ₗ[F] V) (X - 1))) ^ p = 1 :=
      Subtype.ext hcoe
    rw [← map_pow, hpow, map_one]

theorem mem_centralizer_supportedFixedDerived_of_weightOne (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {n : ℕ} {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) {j : Fin n} (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j))
    (hdj : ¬ ∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v) :
    e j ∈ Subgroup.centralizer
      (((supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) :
        Subgroup ↥(orthDerived Q)) : Set ↥(orthDerived Q)) := by
  refine Subgroup.mem_centralizer_iff.2 fun g hg => Subtype.ext ?_
  have hg' : (g : V ≃ₗ[F] V) ∈ supportedFixedDerived Q (d : V ≃ₗ[F] V) :=
    Subgroup.mem_subgroupOf.1 hg
  obtain ⟨k, hk, hUk⟩ := hF.exists_le_primaryComponent hp hp2 hpq hd j
  have hk1 : k ≠ X - 1 := by
    rintro rfl
    refine hdj fun v hv => ?_
    have hv' : v ∈ primaryComponent (d : V ≃ₗ[F] V).toLinearMap (X - 1) := hUk hv
    rw [← fixedSpace_eq_primaryComponent] at hv'
    exact mem_fixedSpace.1 hv'
  have hfix : ∀ v ∈ U j, (g : V ≃ₗ[F] V) v = v := fun v hv =>
    apply_eq_of_mem_supportedFixedDerived hk hk1 hg' (hUk hv)
  exact commute_of_apply_eq (hF.nondeg j) (orthDerived_le_orthogonalGroup g.2) hfix
    (hF.maps_to j) (hF.apply_of_perp j)

theorem exists_twoGroup_le_supportedFixedDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 3 ≤ n) {x : V ≃ₗ[F] V}
    (hx : OddOrderIsometry Q p x) {m : ℕ} (hm : 3 ≤ m)
    (hfd : Module.finrank F (fixedSpace x) = 2 * m) :
    ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T ≤ (supportedFixedDerived Q x).subgroupOf (orthDerived Q) := by
  have hW : 3 ≤ Module.finrank F (fixedSpace x) := by
    rw [hfd]
    omega
  obtain ⟨u, hu, w, hw, huQ, huw, hE1⟩ := exists_eichler_ne_one_of_three_le hQ hW
  have hE : eichler Q u w ∈ orthDerived Q := eichler_mem_orthDerived hQ hn hdim u w
  obtain ⟨hne, h2⟩ := zpowers_eichler_ne_bot_and_isPGroup huQ huw hE hE1
  have hle : eichler Q u w ∈ supportedFixedDerived Q x :=
    eichlerGroupOn_fixedSpace_le_supportedFixedDerived hx hm hfd
      (eichler_mem_eichlerGroupOn hu hw)
  exact ⟨Subgroup.zpowers (⟨eichler Q u w, hE⟩ : ↥(orthDerived Q)), hne, h2,
    Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hle)⟩

theorem exists_twoGroup_decomp_weightOne (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {U : Fin n → Submodule F V} {e : Fin n → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) {d : ↥(orthDerived Q)}
    (hd : d ∈ Bb) (hd1 : d ≠ 1) {j : Fin n} (hdj : d ∈ Subgroup.zpowers (e j))
    (hfs : fixedSpace (d : V ≃ₗ[F] V) = polarPerp Q (U j)) :
    ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T ≤ (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) ∧
      Bb = (Bb ⊓ (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ⊔
        (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf d = p := orderOf_eq_prime (hF.isElemAbelian.2 d hd) hd1
  have hx : OddOrderIsometry Q p (d : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ d hord
  have hfd : Module.finrank F (fixedSpace (d : V ≃ₗ[F] V)) = 2 * (n - 1) := by
    rw [hfs, finrank_polarPerp hQ (U j), hF.finrank_eq j, hdim]
    omega
  obtain ⟨T, hTne, hT2, hTL⟩ := exists_twoGroup_le_supportedFixedDerived hQ hdim (by omega) hx
    (m := n - 1) (by omega) hfd
  have hdj' : ¬ ∀ v ∈ U j, (d : V ≃ₗ[F] V) v = v := by
    intro hfix
    apply hd1
    refine hF.eq_one_of_forall_apply_eq hd ?_
    intro i x hxU
    by_cases hij : i = j
    · subst hij
      exact hfix x hxU
    · have hxperp : x ∈ polarPerp Q (U j) :=
        mem_polarPerp_iff.2 fun y hy => hF.perp j i (fun h => hij h.symm) y hy x hxU
      have hfixj : (e j : V ≃ₗ[F] V) x = x := hF.apply_of_perp j x hxperp
      have hstab : Subgroup.zpowers ((e j : V ≃ₗ[F] V)) ≤ MulAction.stabilizer (V ≃ₗ[F] V) x :=
        Subgroup.zpowers_le.2 ((MulAction.mem_stabilizer_iff).2 hfixj)
      have hdz : (d : V ≃ₗ[F] V) ∈ Subgroup.zpowers ((e j : V ≃ₗ[F] V)) := by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hdj
        exact Subgroup.mem_zpowers_iff.2 ⟨m, by rw [← hm]; simp⟩
      exact (MulAction.mem_stabilizer_iff).1 (hstab hdz)
  refine ⟨T, hTne, hT2, hTL, ?_⟩
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  have hgen : Subgroup.closure (Set.range e) ≤
      (Bb ⊓ (supportedFixedDerived Q (d : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) ⊔
        (Bb ⊓ Subgroup.normalizer (T : Set ↥(orthDerived Q))) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    by_cases hij : i = j
    · subst hij
      refine Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hF.mem i, ?_⟩)
      exact (Subgroup.centralizer_le_normalizer (T : Set ↥(orthDerived Q)))
        (Subgroup.centralizer_le hTL
          (mem_centralizer_supportedFixedDerived_of_weightOne hp hp2 hpq hF hd hfs hdj'))
    · refine Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hF.mem i, ?_⟩)
      exact Subgroup.mem_subgroupOf.2
        (mem_supportedFixedDerived_of_weightOne hQ hdim hn hp hp2 hF hd hd1 hfs hij)
  rwa [hF.closure_eq] at hgen

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
