module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA.S172X

theorem layerIs_of_normal_quasisimple {G : Type} [Group G] [Finite G] {X N : Subgroup G} (hNX : N ≤ X)
    (hn : (N.subgroupOf X).Normal) (hq : CFSG.IsQuasisimple ↥N)
    (hsol : Group.IsSolvable (↥X ⧸ N.subgroupOf X)) {p : ℕ} {Qq : TauCeti.CFSGIndex → Prop}
    (hcat : catalogIs (PSimple p N) Qq) : LayerIs p X Qq ∧ GLALayer X = N := by
  obtain ⟨hc, hl⟩ :=
    Y10F.isComponentOf_and_glaLayer_eq_of_normal_solvable_of_isQuasisimple hNX hn hq hsol
  subst hl
  exact ⟨⟨hc, hcat⟩, rfl⟩

section Commutator

variable {Γ : Type*} [Group Γ] {X H : Subgroup Γ}

theorem commutator_le_subgroupOf_of_commutator_le (h : ⁅X, X⁆ ≤ H) :
    commutator ↥X ≤ H.subgroupOf X := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g _ k _
  rw [Subgroup.mem_subgroupOf]
  exact h (Subgroup.commutator_mem_commutator g.2 k.2)

theorem normal_subgroupOf_of_commutator_le (h : ⁅X, X⁆ ≤ H) : (H.subgroupOf X).Normal :=
  Subgroup.Normal.of_commutator_le ↥X (commutator_le_subgroupOf_of_commutator_le h)

theorem isSolvable_quotient_of_commutator_le [(H.subgroupOf X).Normal] (h : ⁅X, X⁆ ≤ H) :
    Group.IsSolvable (↥X ⧸ H.subgroupOf X) := by
  haveI : IsMulCommutative (↥X ⧸ H.subgroupOf X) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.2
      (commutator_le_subgroupOf_of_commutator_le h)
  infer_instance

theorem centralizer_pair_eq_of_mul_zpow_cent (a b : Γ) (k : ℤ) :
    Subgroup.centralizer ({a * b ^ k, b} : Set Γ) = Subgroup.centralizer ({a, b} : Set Γ) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : Commute b g := h2
    have hk : Commute (b ^ k) g := hb.zpow_left k
    have hab : Commute (a * b ^ k) g := h1
    have : Commute a g := by
      have := hab.mul_left hk.inv_left
      simpa using this
    exact ⟨this, h2⟩
  · rintro ⟨h1, h2⟩
    have hb : Commute b g := h2
    exact ⟨(show Commute a g from h1).mul_left (hb.zpow_left k), h2⟩

end Commutator

theorem layerIs_of_commutator_le {G : Type} [Group G] [Finite G] {X N : Subgroup G} (hNX : N ≤ X)
    (hcomm : ⁅X, X⁆ ≤ N) (hq : CFSG.IsQuasisimple ↥N) {p : ℕ} {Qq : TauCeti.CFSGIndex → Prop}
    (hcat : catalogIs (PSimple p N) Qq) : LayerIs p X Qq ∧ GLALayer X = N := by
  haveI hn : (N.subgroupOf X).Normal := normal_subgroupOf_of_commutator_le hcomm
  exact layerIs_of_normal_quasisimple hNX hn hq (isSolvable_quotient_of_commutator_le hcomm) hcat

theorem layerIs_of_ker_solvable {G : Type} [Group G] [Finite G] {X N : Subgroup G} (hNX : N ≤ X)
    (hq : CFSG.IsQuasisimple ↥N) {A : Type} [Group A] [Group.IsSolvable A] (φ : ↥X →* A)
    (hker : φ.ker = N.subgroupOf X) {p : ℕ} {Qq : TauCeti.CFSGIndex → Prop}
    (hcat : catalogIs (PSimple p N) Qq) : LayerIs p X Qq ∧ GLALayer X = N := by
  haveI hn : (N.subgroupOf X).Normal := hker ▸ φ.normal_ker
  haveI : (φ.ker).Normal := φ.normal_ker
  haveI : Group.IsSolvable ↥φ.range := solvable_of_solvable_injective φ.range.subtype_injective
  have hsol : Group.IsSolvable (↥X ⧸ N.subgroupOf X) :=
    solvable_of_solvable_injective (G' := ↥φ.range)
      (f := ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)).toMonoidHom)
      ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)).injective
  exact layerIs_of_normal_quasisimple hNX hn hq hsol hcat

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
