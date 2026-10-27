module

public import CFSG.GH74.Generic.BProg.B3.S3Pump306Core
public import CFSG.GH74.Generic.BProg.B3.S3Pump304

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

@[expose] noncomputable def fU (x y : G) : ↥(Ux x y) →* CentralizerBar y :=
  (proj y).comp (Subgroup.inclusion inf_le_right)

theorem fU_odd (g : ↥(Ux x y)) (hg : fU x y g = 1) : Odd (orderOf g) := by
  have h := proj_odd y ⟨g.1, g.2.2⟩ hg
  have hord : orderOf (Subgroup.inclusion (inf_le_right : Ux x y ≤ centralizer ({y} : Set G)) g) =
      orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
  rw [← hord]
  exact h

theorem range_fU (hxy : x ∈ centralizer ({y} : Set G)) (hx2 : x * x = 1) :
    (fU x y).range = centralizer ({proj y ⟨x, hxy⟩} : Set (CentralizerBar y)) := by
  ext b
  constructor
  · rintro ⟨g, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show proj y ⟨g.1, g.2.2⟩ * proj y ⟨x, hxy⟩ = proj y ⟨x, hxy⟩ * proj y ⟨g.1, g.2.2⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2.1)
  · intro hb
    obtain ⟨g, hg, hgb⟩ := proj_cent y (u := ⟨x, hxy⟩) (Subtype.ext hx2) b
      (mem_centralizer_singleton_iff.1 hb)
    have hgx : g.1 ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
    exact ⟨⟨g.1, ⟨hgx, g.2⟩⟩, hgb⟩

theorem layer_isPCompIn (h : Setup30 G x K A y) (hT : IsZT x y T) :
    IsPCompIn 2 (Ux x y) (Ly K y) := by
  have hcfg := cfg_of_setup30 h hT
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hcfg.hK
  have hH : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) := (Setup30.layer h).1
  have hsub : ((K ⊓ centralizer ({y} : Set G)).subgroupOf (Ux x y)).IsSubnormal :=
    B1.isSubnormal_subgroupOf_inf (S := centralizer ({y} : Set G)) (B1.isSubnormal_of_isPCompIn hK)
  exact B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsub hH

theorem layer_bar_isPCompIn (h : Setup30 G x K A y) (hT : IsZT x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {H : Subgroup G} (hLH : Ly K y ≤ H) :
    IsPCompIn 2 (centralizer ({proj y ⟨x, hxy⟩} : Set (CentralizerBar y)) ⊓ barSub y H)
      (barSub y (Ly K y)) := by
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hHU := layer_isPCompIn h hT
  have hs : orderOf (⟨x, hxy⟩ : ↥(centralizer ({y} : Set G))) = 2 :=
    TwoThin.orderOf_mk_centralizer hxy hx
  have hΛC := TwoThin.le_centralizer_mk hHU.1 hxy
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hHU hxy
  have h2 := TwoThin.isTwoComponent_map_barMk hs hΛC hΛ2
  have hle : barSub y (Ly K y) ≤ centralizer ({proj y ⟨x, hxy⟩} : Set (CentralizerBar y)) :=
    (Subgroup.map_mono hΛC).trans (TwoThin.map_centralizer_barMk hs).le
  have h3 : IsPCompIn 2 (centralizer ({proj y ⟨x, hxy⟩} : Set (CentralizerBar y)))
      (barSub y (Ly K y)) := TwoThin.isPCompIn_two_iff.mpr ⟨hle, h2⟩
  exact Lemma212Aux.isPCompIn_of_le h3 (le_inf hle (barSub_mono hLH)) inf_le_left

theorem isPCompIn_of_inf_subnormal {Q : Type} [Group Q] [Finite Q] {X Hb J : Subgroup Q}
    (hsub : Hb.IsSubnormal) (hJ : IsPCompIn 2 (X ⊓ Hb) J) : IsPCompIn 2 X J := by
  have h1 : ((X ⊓ Hb).subgroupOf X).IsSubnormal := by
    have : (X ⊓ Hb).subgroupOf X = Hb.comap X.subtype := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact hsub.comap X.subtype
  exact B1.isPCompIn_of_isSubnormal 2 inf_le_left h1 hJ

theorem layer_bar_eq (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {H : Subgroup G}
    (hHc : IsPCompIn 2 (centralizer ({y} : Set G)) H) (hLH : Ly K y ≤ H) :
    pLayerOf 2 (centralizer ({proj y ⟨x, hxy⟩} : Set (CentralizerBar y)) ⊓ barSub y H) =
      barSub y (Ly K y) := by
  classical
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  refine le_antisymm (sSup_le fun J hJ => ?_) (le_sSup (layer_bar_isPCompIn h hT hxy hLH))
  have hHb : (barSub y H).IsSubnormal := (FalseCtxS45Comp.isComponent_bar hHc).2
  have hJX := isPCompIn_of_inf_subnormal hHb hJ
  have hJr : IsPCompIn 2 (fU x y).range J := by rw [range_fU hxy hx2]; exact hJX
  have hker : ¬ 2 ∣ Nat.card (fU x y).ker := by
    have hodd : Odd (Nat.card (fU x y).ker) :=
      S45.odd_card_of_forall_odd_orderOf (Q := (fU x y).ker) fun q hq => fU_odd q hq
    exact Nat.not_even_iff_odd.2 hodd ∘ even_iff_two_dvd.2
  obtain ⟨hJ₀, hmap⟩ := B1.exists_isPCompIn_lift_of_odd_ker (fU x y) hker hJr
  have hlayer := (S3Pump304.prop304_of_F h hT hF).2
  have hJ₀L : oPrimeResidualOf 2 ((J.comap (fU x y)).map (Ux x y).subtype) ≤ Ly K y := by
    rw [← hlayer]
    exact le_sSup hJ₀
  intro b hb
  rw [← hmap] at hb
  obtain ⟨g, hg, rfl⟩ := hb
  exact proj_mem_barSub g.2.2 (hJ₀L (Subgroup.mem_subgroupOf.1 hg))

theorem hasSL2_bar (h : Setup30 G x K A y)
    (hLO : pPrimeCoreOf 2 (Ly K y) ≤ pPrimeCoreOf 2 (centralizer ({y} : Set G))) :
    HasSL2Model ↥(barSub y (Ly K y)) (fun q => Odd q ∧ 5 ≤ q) := by
  classical
  have hL : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) := (Setup30.layer h).1
  have hLC : Ly K y ≤ centralizer ({y} : Set G) := hL.1.trans inf_le_right
  let φ : ↥(Ly K y) →* CentralizerBar y := (proj y).comp (Subgroup.inclusion hLC)
  have hφr : φ.range = barSub y (Ly K y) := by
    ext b
    constructor
    · rintro ⟨l, rfl⟩
      exact proj_mem_barSub (hLC l.2) l.2
    · intro hb
      obtain ⟨g, hg, hgL, rfl⟩ := mem_barSub.1 hb
      exact ⟨⟨g, hgL⟩, rfl⟩
  have hφk : φ.ker = pPrimeCore 2 ↥(Ly K y) := by
    apply le_antisymm
    · have hodd : Odd (Nat.card φ.ker) := by
        refine S45.odd_card_of_forall_odd_orderOf (Q := φ.ker) fun q hq => ?_
        have h1 := proj_odd y ⟨q.1, hLC q.2⟩ hq
        have hord : orderOf (Subgroup.inclusion hLC q) = orderOf q :=
          orderOf_injective _ (Subgroup.inclusion_injective _) q
        rw [← hord]
        exact h1
      exact le_sSup ⟨inferInstance, Nat.coprime_two_left.2 hodd⟩
    · intro l hl
      have h1 : (l : G) ∈ pPrimeCoreOf 2 (Ly K y) := ⟨l, hl, rfl⟩
      obtain ⟨w, hw, hwl⟩ := hLO h1
      show proj y (Subgroup.inclusion hLC l) = 1
      have e : Subgroup.inclusion hLC l = w := Subtype.ext hwl.symm
      rw [e]
      exact (QuotientGroup.eq_one_iff w).2 hw
  let e₀ : ↥(Ly K y) ⧸ pPrimeCore 2 ↥(Ly K y) ≃* ↥(barSub y (Ly K y)) :=
    ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hφr)
  obtain ⟨F, hFf, hFfin, hP, ⟨e⟩⟩ := (Setup30.layer h).2.2
  exact ⟨F, hFf, hFfin, hP, ⟨e₀.symm.trans e⟩⟩

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
