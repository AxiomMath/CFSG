module

public import CFSG.HardMathSupport.Dickson.Bal207.Restate

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Glue

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem isSubnormal_centralizer_of_glaPComponent {p : ℕ} {X : Type*} [Group X] {K J : Subgroup X}
    (a : X) (hK : CFSG.Open.IsSubnormal K ⊤)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    CFSG.Open.IsSubnormal J (Subgroup.centralizer ({a} : Set X)) := by
  have h2 := hK.inf (Subgroup.centralizer ({a} : Set X))
  rw [top_inf_eq] at h2
  exact hJ.2.1.trans h2

theorem isComponentOf_subgroupOf_of_isSubnormal {X : Type*} [Group X] {J Y : Subgroup X}
    (hJY : J ≤ Y) (hsn : CFSG.Open.IsSubnormal J Y) (hq : CFSG.Open.IsQuasisimple ↥J) :
    CFSG.Open.IsComponentOf (J.subgroupOf Y) ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.top_iff.2 ((CFSG.Open.IsSubnormal.iff_subgroupOf hJY).1 hsn),
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJY) hq⟩

theorem isLieQuot_congr {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {P : TauCeti.LieTypeIndex → Prop} (h : IsLieQuot Y P) : IsLieQuot Y' P := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  exact ⟨d, hd, ⟨(QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y') e
    (Subgroup.map_center_eq e)).symm.trans f⟩⟩

theorem isLieQuot_subgroupOf {X : Type*} [Group X] {J Y : Subgroup X} (hJY : J ≤ Y)
    {P : TauCeti.LieTypeIndex → Prop} (h : IsLieQuot ↥J P) : IsLieQuot ↥(J.subgroupOf Y) P :=
  isLieQuot_congr (Subgroup.subgroupOfEquivOfLe hJY).symm h

theorem bal207PlusHyp_of_isLieQuot {G : ∀ (S : Type) [Group S], MulAut S → Prop} {p : ℕ}
    {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : IsLieQuot ↥K (fun d => Bal207Index p d ∧ ¬ IsG2EightIndex d)) :
    Bal207PlusHyp G p K B := by
  obtain ⟨d, ⟨hd, hg⟩, e⟩ := h
  exact ⟨d, e, Or.inl ⟨hd, fun h => absurd h hg⟩⟩

theorem bal207PlusHyp_of_d4Eight {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (h : IsLieQuot ↥K IsD4EightIdx) (hNT : NoTrialityOn G B K) :
    Bal207PlusHyp G 3 K B := by
  obtain ⟨d, hd, e⟩ := h
  exact ⟨d, e, Or.inr ⟨rfl, hd, hNT⟩⟩

theorem stronglyLocallyOneBalanced_of_body {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : X}
    {B J : Subgroup X} (haB : a ∈ B) (hB : IsSCp p ⊤ B)
    (hJY : J ≤ Subgroup.centralizer ({a} : Set X))
    (hsn : CFSG.Open.IsSubnormal J (Subgroup.centralizer ({a} : Set X)))
    (hq : CFSG.Open.IsQuasisimple ↥J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hbody : Bal207PlusBody G ↥(Subgroup.centralizer ({a} : Set X)))
    (hhyp : Bal207PlusHyp G p (J.subgroupOf (Subgroup.centralizer ({a} : Set X)))
      (B.subgroupOf (Subgroup.centralizer ({a} : Set X)))) :
    IsStronglyLocallyOneBalanced p B a J := by
  set Y := Subgroup.centralizer ({a} : Set X) with hY
  have hBY : B ≤ Y := by
    intro b hb
    rw [hY, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hc := hB.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨h, haB⟩
    have := congrArg Subtype.val hc
    exact this.symm
  have hscp : IsSCp p ⊤ (B.subgroupOf Y) := isSCp_subgroupOf hB hBY
  have hcomp : CFSG.Open.IsComponentOf (J.subgroupOf Y) ⊤ :=
    isComponentOf_subgroupOf_of_isSubnormal hJY hsn hq
  have hnormOf : ∀ {M : Subgroup X}, M ≤ Subgroup.normalizer (J : Set X) →
      M.subgroupOf Y ≤ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro M hM s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hs' : (s : X) ∈ Subgroup.normalizer (J : Set X) := hM hs
    have := Subgroup.mem_normalizer_iff.1 hs' (h : X)
    simpa [Subgroup.mem_subgroupOf] using this
  have hbal := hbody p (J.subgroupOf Y) (B.subgroupOf Y) hp hp2 hcomp hscp (hnormOf hBJ) hhyp
  intro S hS hScop hBS
  have hSY : S ≤ Y := (le_inf_iff.1 hS).2
  have hSJ : S ≤ Subgroup.normalizer (J : Set X) := (le_inf_iff.1 hS).1
  have hS'cop : Nat.Coprime p (Nat.card (S.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv]
    exact hScop
  have hBS' : B.subgroupOf Y ⊓ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.normalizer ((S.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro b hb
    have hbB : (b : X) ∈ B := hb.1
    have hbN : (b : X) ∈ B ⊓ Subgroup.normalizer (J : Set X) := ⟨hbB, hBJ hbB⟩
    have hbS : (b : X) ∈ Subgroup.normalizer (S : Set X) := hBS hbN
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.1 hbS (h : X)
    simpa [Subgroup.mem_subgroupOf] using this
  have hcent := hbal (S.subgroupOf Y) (hnormOf hSJ) hS'cop hBS'
  have hbot : ⁅J, S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsY : (⟨s, hSY hs⟩ : ↥Y) ∈ S.subgroupOf Y := hs
    have hc := Subgroup.mem_centralizer_iff.1 (hcent hsY) ⟨j, hJY hj⟩ hj
    exact (congrArg Subtype.val hc).symm
  rw [hbot]
  exact bot_le

theorem stronglyLocallyOneBalanced_of_ih {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    {X : Type} [Group X] [Finite X] {p : ℕ} {K B A J : Subgroup X}
    (ctx : Bal207PlusCtx G p K B A) (hIH : Bal207PlusIH G A) {a : X} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hq : CFSG.Open.IsQuasisimple ↥J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hhyp : Bal207PlusHyp G p (J.subgroupOf (Subgroup.centralizer ({a} : Set X)))
      (B.subgroupOf (Subgroup.centralizer ({a} : Set X)))) :
    IsStronglyLocallyOneBalanced p B a J :=
  stronglyLocallyOneBalanced_of_body ctx.prime ctx.odd (ctx.le haA) ctx.scp
    (hJ.1.trans inf_le_right) (isSubnormal_centralizer_of_glaPComponent a ctx.comp.2.1 hJ) hq hBJ
    (hIH a haA ha1) hhyp

end CFSG.HardMathSupport.Dickson.Bal207.Glue

end
