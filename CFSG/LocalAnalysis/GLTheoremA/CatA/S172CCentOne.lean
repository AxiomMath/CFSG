module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_threeSingular_polarPerp (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (htype : IsPlusType Q ↔ Odd n)
    {W : Submodule F V} (hW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hW2 : Module.finrank F W = 2) (hWm : ¬ IsPlusType (Q.comp W.subtype)) :
    ∃ T : Submodule F ↥(polarPerp Q W), Module.finrank F T = 3 ∧
      ∀ u ∈ T, (Q.comp (polarPerp Q W).subtype) u = 0 := by
  have hdimW : Module.finrank F (polarPerp Q W) = 2 * (n - 1) := by
    rw [finrank_polarPerp hQ W, hdim, hW2]
    omega
  have hiff := isPlusType_comp_polarPerp_iff hQ hdim (by omega) hW hW2 hWm
  refine exists_threeSingular (nondeg_comp_polarPerp hQ hW) hdimW ?_
  by_cases hQp : IsPlusType Q
  · right
    refine ⟨fun h => ?_, ?_⟩
    · exact (hiff.1 h) hQp
    · obtain ⟨k, hk⟩ := htype.1 hQp
      omega
  · left
    refine ⟨hiff.2 hQp, ?_⟩
    omega

private theorem layerIs_centralizer_rot_aux1 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (htype : IsPlusType Q ↔ Odd n)
    {U : Fin (n - 1) → Submodule F V} {e : Fin (n - 1) → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U e Bb) (j : Fin (n - 1)) :
    ∃ T : Submodule F ↥(fixedSpace (e j : V ≃ₗ[F] V)), Module.finrank F T = 3 ∧
      ∀ u ∈ T, (Q.comp (fixedSpace (e j : V ≃ₗ[F] V)).subtype) u = 0 := by
  rw [hF.fixedSpace_eq_polarPerp j]
  exact exists_threeSingular_polarPerp hQ hdim hn htype (hF.nondeg j) (hF.finrank_eq j)
    (hF.not_isPlusType j)

private theorem layerIs_centralizer_rot_aux2 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (j : Fin (n - 1))
    (hT : ∃ T : Submodule F ↥(fixedSpace (e j : V ≃ₗ[F] V)), finrank F T = 3 ∧
      ∀ u ∈ T, (Q.comp (fixedSpace (e j : V ≃ₗ[F] V)).subtype) u = 0) :
    CFSG.IsQuasisimple ↥((supportedFixedDerived Q (e j : V ≃ₗ[F] V)).subgroupOf
      (orthDerived Q)) := by
  have hy : orderOf (e j) = p := hF.orderOf_eq j
  have hx : OddOrderIsometry Q p (e j : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ (e j) hy
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hx.supportedFixedDerived_le_orthDerived).symm
    (hx.isQuasisimple_supportedFixedDerived hT)

private theorem layerIs_centralizer_rot_aux3 (x : ↥(orthDerived Q)) :
    ∀ g ∈ (supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q),
      g ∈ Subgroup.centralizer ({x} : Set ↥(orthDerived Q)) := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  have h1 := mem_isometryCentralizer.1 (supportedFixedDerived_le_isometryCentralizer hg)
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  exact h1.2 v

private theorem layerIs_centralizer_rot_aux4 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (j : Fin (n - 1)) {Q₁ : TauCeti.CFSGIndex → Prop}
    (hcat : catalogIs (PSimple p (⊤ : Subgroup
      ↥(orthDerived (Q.comp (polarPerp Q (U j)).subtype)))) Q₁) :
    catalogIs (PSimple p ((supportedFixedDerived Q (e j : V ≃ₗ[F] V)).subgroupOf
      (orthDerived Q))) Q₁ := by
  have hy : orderOf (e j) = p := hF.orderOf_eq j
  have hx : OddOrderIsometry Q p (e j : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ (e j) hy
  refine catalogIs_pSimple_supportedFixedDerived hx ?_
  rw [hF.fixedSpace_eq_polarPerp j]
  exact hcat

private theorem layerIs_centralizer_rot_aux5 {n : ℕ} {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (j : Fin (n - 1))
    (hx : OddOrderIsometry Q p (e j : V ≃ₗ[F] V))
    (hT : ∃ T : Submodule F ↥(fixedSpace (e j : V ≃ₗ[F] V)), finrank F T = 3 ∧
      ∀ u ∈ T, (Q.comp (fixedSpace (e j : V ≃ₗ[F] V)).subtype) u = 0) :
    ∀ b ∈ Bb ⊓ Subgroup.centralizer ((supportedFixedDerived Q (e j : V ≃ₗ[F] V)).subgroupOf
      (orthDerived Q) : Set ↥(orthDerived Q)), b ∈ Subgroup.zpowers (e j) := by
  intro b hb
  obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.1 hb
  refine hF.mem_zpowers_of_apply_eq hbB j (fun i hij x hx' => ?_)
  have hxW : x ∈ fixedSpace (e j : V ≃ₗ[F] V) := by
    rw [hF.fixedSpace_eq_polarPerp j, mem_polarPerp_iff]
    intro y hy'
    rw [QuadraticMap.polar_comm]
    exact hF.perp i j hij x hx' y hy'
  have hbc : ((b : V ≃ₗ[F] V)) ∈ isometryCentralizer Q (e j : V ≃ₗ[F] V) := by
    refine mem_isometryCentralizer.2 ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1
      (orthDerived_le_orthogonalGroup b.2), fun v => ?_⟩
    have hcomm : (⟨b, hbB⟩ : ↥Bb) * ⟨e j, hF.mem j⟩ = ⟨e j, hF.mem j⟩ * ⟨b, hbB⟩ :=
      hF.isElemAbelian.1.is_comm.comm _ _
    have := congrArg (fun z : ↥Bb => ((z : ↥(orthDerived Q)) : V ≃ₗ[F] V) v) hcomm
    exact this
  refine apply_eq_of_commute_supportedFixedDerived_gen hx hT hbc (fun g hg => ?_) x hxW
  have hgΩ := hx.supportedFixedDerived_le_orthDerived hg
  have hmem' : (⟨g, hgΩ⟩ : ↥(orthDerived Q)) ∈
      (supportedFixedDerived Q (e j : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := hg
  have := Subgroup.mem_centralizer_iff.1 hbC _ hmem'
  exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) this.symm

private theorem layerIs_centralizer_rot_aux6 {n : ℕ} {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (j : Fin (n - 1))
    (hmemC : ∀ g ∈ (supportedFixedDerived Q (e j : V ≃ₗ[F] V)).subgroupOf (orthDerived Q),
      g ∈ Subgroup.centralizer ({e j} : Set ↥(orthDerived Q))) :
    ∀ b ∈ Subgroup.zpowers (e j), b ∈ Bb ⊓ Subgroup.centralizer
      ((supportedFixedDerived Q (e j : V ≃ₗ[F] V)).subgroupOf
        (orthDerived Q) : Set ↥(orthDerived Q)) := by
  intro b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  refine Subgroup.mem_inf.2 ⟨zpow_mem (hF.mem j) k, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hc : Commute g (e j) := Subgroup.mem_centralizer_singleton_iff.1 (hmemC g hg)
  exact (hc.zpow_right k).eq

theorem layerIs_centralizer_rot (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank F V = 2 * n) (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (htype : IsPlusType Q ↔ Odd n) {U : Fin (n - 1) → Submodule F V}
    {e : Fin (n - 1) → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U e Bb) (j : Fin (n - 1)) {Q₁ : TauCeti.CFSGIndex → Prop}
    (hcat : catalogIs (PSimple p (⊤ : Subgroup
      ↥(orthDerived (Q.comp (polarPerp Q (U j)).subtype)))) Q₁) :
    LayerIs p (Subgroup.centralizer {e j}) Q₁ ∧
      Bb ⊓ Subgroup.centralizer (GLALayer (Subgroup.centralizer {e j}) : Set ↥(orthDerived Q)) =
        Subgroup.zpowers (e j) := by
  have hy : orderOf (e j) = p := hF.orderOf_eq j
  have hx : OddOrderIsometry Q p (e j : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived hp (by rw [ringChar.eq F 2]; exact hp2) hQ (e j) hy
  have hfs : fixedSpace (e j : V ≃ₗ[F] V) = polarPerp Q (U j) := hF.fixedSpace_eq_polarPerp j
  have hdim' : finrank F V = finrank F (fixedSpace (e j : V ≃ₗ[F] V)) + 2 := by
    rw [hfs, finrank_polarPerp hQ (U j), hF.finrank_eq j, hdim]
    omega
  have hT := layerIs_centralizer_rot_aux1 hQ hdim hn htype hF j
  have hNq := layerIs_centralizer_rot_aux2 hQ hp hp2 hF j hT
  have hmemC := layerIs_centralizer_rot_aux3 (e j)
  have hcat' := layerIs_centralizer_rot_aux4 hQ hp hp2 hF j hcat
  obtain ⟨hL, hGL⟩ := layerIs_of_commutator_le (X := Subgroup.centralizer {e j}) hmemC
    (commutator_centralizer_le_supportedFixedDerived_gen hQ hp hp2 hpq hy hdim') hNq hcat'
  refine ⟨hL, ?_⟩
  rw [hGL]
  exact le_antisymm (layerIs_centralizer_rot_aux5 hF j hx hT)
    (layerIs_centralizer_rot_aux6 hF j hmemC)

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
