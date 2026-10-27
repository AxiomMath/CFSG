module

public import CFSG.GH74.Generic.BProg.B3.S3PumpKey
public import CFSG.GH74.Generic.BProg.B3.Thm9S45
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump9

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5 CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Core

theorem eq_bot_of_perfect_comm_ker_sdata {U Y₁ Y₂ : Type} [Group U] [Finite U] [Group Y₁] [Group Y₂]
    (f₁ : U →* Y₁) (f₂ : U →* Y₂) (h₁ : ∀ g, f₁ g = 1 → Odd (orderOf g))
    (h₂ : ∀ g, f₂ g = 1 → Odd (orderOf g)) {Kb : Subgroup Y₁} {u : Y₁} {SX : Subgroup Y₁}
    (hS : S3Fusion.SData Y₁ Kb u SX) {W : Subgroup U} (hWSX : W.map f₁ = SX) {Q : Subgroup U}
    (hQ : ⁅Q, Q⁆ = Q) (hQW : Q.map f₁ ≤ SX)
    (hcomm : ∀ q ∈ Q, ∀ w ∈ W, q * w * q⁻¹ * w⁻¹ ∈ f₂.ker) : Q = ⊥ := by
  set N₂' : Subgroup Y₁ := f₂.ker.map f₁ with hN₂'
  have hA₀ : ∀ a ∈ SX ⊓ N₂', a = 1 := by
    refine hS.odd_normal (SX ⊓ N₂') inf_le_left ?_ ?_
    · intro a ha s hs
      refine ⟨SX.mul_mem (SX.mul_mem hs ha.1) (SX.inv_mem hs), ?_⟩
      obtain ⟨k, hk, rfl⟩ := ha.2
      rw [← hWSX] at hs
      obtain ⟨w, hw, rfl⟩ := hs
      refine ⟨w * k * w⁻¹, ?_, by simp⟩
      have hk' : f₂ k = 1 := hk
      show f₂ (w * k * w⁻¹) = 1
      rw [map_mul, map_mul, hk', mul_one, map_inv, mul_inv_cancel]
    · rintro a ⟨-, k, hk, rfl⟩
      exact (h₂ k hk).of_dvd_nat (orderOf_map_dvd f₁ k)
  have hcommQ : ∀ q ∈ Q, ∀ s ∈ SX, f₁ q * s = s * f₁ q := by
    intro q hq s hs
    have hs' := hs
    rw [← hWSX] at hs'
    obtain ⟨w, hw, rfl⟩ := hs'
    have hqS : f₁ q ∈ SX := hQW ⟨q, hq, rfl⟩
    have h1 : f₁ (q * w * q⁻¹ * w⁻¹) ∈ SX ⊓ N₂' := by
      refine ⟨?_, ⟨_, hcomm q hq w hw, rfl⟩⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact SX.mul_mem (SX.mul_mem (SX.mul_mem hqS hs) (SX.inv_mem hqS)) (SX.inv_mem hs)
    have h2 := hA₀ _ h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 : ⁅f₁ q, f₁ w⁆ = 1 := by
      rw [commutatorElement_def]
      exact h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h3
  have hker : ∀ q ∈ Q, f₁ q = 1 := by
    have hperf : ⁅Q.map f₁, Q.map f₁⁆ = Q.map f₁ := by rw [← Subgroup.map_commutator, hQ]
    have hbot : ⁅Q.map f₁, Q.map f₁⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      obtain ⟨q, hq, rfl⟩ := ha
      exact hcommQ q hq b (hQW hb)
    have hQ1 : Q.map f₁ = ⊥ := by rw [← hperf]; exact le_bot_iff.1 hbot
    intro q hq
    have : f₁ q ∈ Q.map f₁ := ⟨q, hq, rfl⟩
    rw [hQ1, Subgroup.mem_bot] at this
    exact this
  exact eq_bot_of_perfect_of_odd hQ (odd_card_of_forall_odd_orderOf fun q hq => h₁ q (hker q hq))

end Core

section Diagonal

variable {G : Type} [Group G] [Finite G]

theorem false_of_diagonal_L3 {x v : G} (hxord : orderOf x = 2) (hvord : orderOf v = 2)
    (hxv : x ∈ centralizer ({v} : Set G))
    {Kb : Subgroup (CentralizerBar x)} {u : CentralizerBar x} {SX : Subgroup (CentralizerBar x)}
    (hS : S3Fusion.SData (CentralizerBar x) Kb u SX)
    (hperf : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) →
      ⁅R, R⁆ = R → ∀ r ∈ R, piC x r ∈ SX)
    {W : Subgroup G} (hWY : W ≤ centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G))
    (hWSX1 : ∀ w ∈ W, piC x w ∈ SX) (hWSX2 : ∀ s ∈ SX, ∃ w ∈ W, piC x w = s)
    (hxc : proj v ⟨x, hxv⟩ ∈ _root_.commutator (CentralizerBar v))
    {L : Subgroup (CentralizerBar v)} (hL : IsComponent L)
    (hne : conjSub (proj v ⟨x, hxv⟩)⁻¹ L ≠ L) (hAB : ⁅L, conjSub (proj v ⟨x, hxv⟩)⁻¹ L⁆ = ⊥)
    (hle : barSub v W ≤ (swapDiag hAB).range) : False := by
  classical
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hvord, pow_two] at this
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxord, pow_two] at this
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hvord; omega
  set t : CentralizerBar v := proj v ⟨x, hxv⟩ with ht
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul]
    have : (⟨x, hxv⟩ * ⟨x, hxv⟩ : ↥(centralizer ({v} : Set G))) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hinvol : ∀ M : Subgroup (CentralizerBar v), conjSub t⁻¹ (conjSub t⁻¹ M) = M := fun M => by
    rw [← conjSub_mul_comp, ← mul_inv_rev, ht2, inv_one, conjSub_one_comp]
  obtain ⟨B, hB, hBne, hBL, hBLt⟩ := exists_second_swapped hxc ht2 hL hne
  have hAB' : ⁅B, conjSub t⁻¹ B⁆ = ⊥ := commutator_conjSub_eq_bot hB hBne
  have hBt : IsComponent (conjSub t⁻¹ B) := isComponent_conjSub hB t⁻¹
  have hLt : IsComponent (conjSub t⁻¹ L) := isComponent_conjSub hL t⁻¹
  have hBtL : conjSub t⁻¹ B ≠ L := fun h => hBLt (by rw [← h, hinvol])
  have hBtLt : conjSub t⁻¹ B ≠ conjSub t⁻¹ L := fun h => hBL (by
    have := congrArg (conjSub t⁻¹) h
    rwa [hinvol, hinvol] at this)
  have hcomm2 := comm_sup_sup (comm_of_ne_components hB hL hBL) (comm_of_ne_components hB hLt hBLt)
    (comm_of_ne_components hBt hL hBtL) (comm_of_ne_components hBt hLt hBtLt)
  have hBq : CFSG.Assembly.IsQuasisimple ↥B := assembly_isQuasisimple_of_isComponent hB
  have hΔq := isQuasisimple_range_swapDiag hAB' hBq
  have hΔperf : ⁅(swapDiag hAB').range, (swapDiag hAB').range⁆ = (swapDiag hAB').range :=
    Subgroup.isPerfect_iff.1 ⟨hΔq.1⟩
  have hΔne : (swapDiag hAB').range ≠ ⊥ := by
    intro hbot
    have hsimple : IsSimpleGroup (↥(swapDiag hAB').range ⧸ center ↥(swapDiag hAB').range) := hΔq.2
    have hnt : Nontrivial ↥(swapDiag hAB').range :=
      (QuotientGroup.mk'_surjective (center ↥(swapDiag hAB').range)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hbot
  set X₀ : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) with hX₀
  let f₁ : ↥X₀ →* CentralizerBar x := (proj x).comp (Subgroup.inclusion inf_le_left)
  let f₂ : ↥X₀ →* CentralizerBar v := (proj v).comp (Subgroup.inclusion inf_le_right)
  have hf₁ : ∀ g : ↥X₀, f₁ g = proj x ⟨g.1, g.2.1⟩ := fun g => rfl
  have hf₂ : ∀ g : ↥X₀, f₂ g = proj v ⟨g.1, g.2.2⟩ := fun g => rfl
  have h₁ : ∀ g : ↥X₀, f₁ g = 1 → Odd (orderOf g) := by
    intro g hg
    have h := proj_odd x ⟨g.1, g.2.1⟩ hg
    have hord : orderOf (Subgroup.inclusion (inf_le_left : X₀ ≤ centralizer ({x} : Set G)) g) =
        orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
    rw [← hord]
    exact h
  have h₂ : ∀ g : ↥X₀, f₂ g = 1 → Odd (orderOf g) := by
    intro g hg
    have h := proj_odd v ⟨g.1, g.2.2⟩ hg
    have hord : orderOf (Subgroup.inclusion (inf_le_right : X₀ ≤ centralizer ({v} : Set G)) g) =
        orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
    rw [← hord]
    exact h
  have hΔrange : (swapDiag hAB').range ≤ f₂.range := by
    rintro _ ⟨b, rfl⟩
    have hyc : swapDiag hAB' b * t = t * swapDiag hAB' b :=
      mem_centralizer_singleton_iff.1 (swapDiag_mem_centralizer hAB' htinv b)
    obtain ⟨g, hg, hgy⟩ := proj_cent v (u := ⟨x, hxv⟩) (Subtype.ext hx2) (swapDiag hAB' b) hyc
    have hgx : g.1 ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
    exact ⟨⟨g.1, ⟨hgx, g.2⟩⟩, hgy⟩
  obtain ⟨Q, hQperf, hQmap⟩ := exists_perfect_lift_hom f₂ hΔperf hΔrange

  have hQW : Q.map f₁ ≤ SX := by
    rintro _ ⟨q, hq, rfl⟩
    have hR : ⁅Q.map X₀.subtype, Q.map X₀.subtype⁆ = Q.map X₀.subtype := by
      rw [← Subgroup.map_commutator, hQperf]
    have := hperf (Q.map X₀.subtype) (Subgroup.map_subtype_le Q) hR (q : G) ⟨q, hq, rfl⟩
    rw [piC_of_mem x q.2.1] at this
    exact this
  have hWSX : (W.subgroupOf X₀).map f₁ = SX := by
    ext s
    constructor
    · rintro ⟨w, hw, rfl⟩
      have := hWSX1 (w : G) hw
      rw [piC_of_mem x w.2.1] at this
      exact this
    · intro hs
      obtain ⟨w, hw, hws⟩ := hWSX2 s hs
      refine ⟨⟨w, hWY hw⟩, hw, ?_⟩
      rw [hf₁]
      rw [piC_of_mem x (hWY hw).1] at hws
      exact hws
  have hcomm : ∀ q ∈ Q, ∀ w ∈ W.subgroupOf X₀, q * w * q⁻¹ * w⁻¹ ∈ f₂.ker := by
    intro q hq w hw
    have hq' : f₂ q ∈ (swapDiag hAB').range := by rw [← hQmap]; exact ⟨q, hq, rfl⟩
    obtain ⟨b, hb⟩ := hq'
    have hq'' : f₂ q ∈ B ⊔ conjSub t⁻¹ B := by rw [← hb]; exact swapDiag_mem_sup hAB' b
    have hw' : f₂ w ∈ barSub v W := proj_mem_barSub (v := v) (J := W) w.2.2 hw
    obtain ⟨a, ha⟩ := hle hw'
    have hw'' : f₂ w ∈ L ⊔ conjSub t⁻¹ L := by rw [← ha]; exact swapDiag_mem_sup hAB a
    have hc := hcomm2 _ hq'' _ hw''
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.2 hc

  have hQ0 : Q = ⊥ := eq_bot_of_perfect_comm_ker_sdata f₁ f₂ h₁ h₂ hS hWSX hQperf hQW hcomm
  apply hΔne
  rw [← hQmap, hQ0, Subgroup.map_bot]

end Diagonal

section Main

open CFSG.ComponentClassification CFSG.GH74.Generic.BProg

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

theorem imgBar_Th_le_SX (h : S3Fusion.Cfg x y K T) {n : G} (hn : n ∈ normalizer (T : Set G))
    (hnx : n * x * n⁻¹ = x * y) (hny : n * y * n⁻¹ = y) {SX : Subgroup (CentralizerBar x)}
    (hSD : S3Fusion.SData (CentralizerBar x) (S3.imgBar x K) (piC x y) SX) :
    S3.imgBar x (S3Fusion.Th x y) ≤ SX := by
  classical
  have hRperf := S3Fusion.imgBar_Th_perfect x y
  have hperfR : Group.IsPerfect ↥(S3.imgBar x (S3Fusion.Th x y)) := Subgroup.isPerfect_iff.2 hRperf
  have hRle := fun l hl => h.shape.perfect_le hperfR l hl
  have hRu : ∀ l ∈ S3.imgBar x (S3Fusion.Th x y), l * piC x y = piC x y * l := by
    intro l hl
    rw [S3Fusion.imgBar_Th_eq_range] at hl
    obtain ⟨θ, rfl⟩ := hl
    rw [S3Fusion.f0_apply]
    have hθC : (θ : G) ∈ centralizer ({x} : Set G) := S3Fusion.Th_le_C x y θ.2
    have hθy : (θ : G) * y = y * (θ : G) :=
      mem_centralizer_singleton_iff.mp (S3Fusion.maxPerfect_le _ θ.2).2
    rw [← piC_mul x hθC h.hyC, ← piC_mul x h.hyC hθC, hθy]
  have hKc : ∀ k ∈ S3.imgBar x K, (∀ g ∈ S3.imgBar x K, g * k = k * g) → k = 1 := by
    intro k hk hkc
    have hmem : (⟨k, hk⟩ : ↥(S3.imgBar x K)) ∈ center ↥(S3.imgBar x K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hkc g g.2)
    rw [h.shape.centerless, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hRK : S3.imgBar x (S3Fusion.Th x y) ≤ S3.imgBar x K :=
    S3PumpKey.perfect_le_Kb hKc
      (fun P hPC hP => S3PumpKey.Cfg.perfect_C_eq_bot h hn hnx hny hPC hP) hRperf hRle
  exact hSD.max _ hRperf hRK hRu

theorem thm9_l3_rank1_of_F (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T) :
    IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y) ∧
      x ∈ normalizer ((pumpUp 2 (Ly K y) y : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := cfg_of_setup30 h hT
  have hx : orderOf x = 2 := hcfg.hx
  have hy : orderOf y = 2 := hcfg.hy
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hcfg.hK
  have hyK : y ∈ K := hcfg.hyK
  have hyC : y ∈ centralizer ({x} : Set G) := hK.1 hyK
  have hxy : x ∈ centralizer ({y} : Set G) := TwoThin.mem_centralizer_symm hyC
  have hx2 : x * x = 1 := hcfg.hx2
  have hH : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) := (Setup30.layer h).1
  set H : Subgroup G := Ly K y with hHdef
  have hHy : H ≤ centralizer ({y} : Set G) := hH.1.trans inf_le_right
  set W : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) with hW
  have hsub : ((K ⊓ centralizer ({y} : Set G)).subgroupOf W).IsSubnormal :=
    B1.isSubnormal_subgroupOf_inf (S := centralizer ({y} : Set G)) (B1.isSubnormal_of_isPCompIn hK)
  have hHU : IsPCompIn 2 W H := B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hK.1) hsub hH
  set Yc : Subgroup G := centralizer ({y} : Set G) with hYc
  have hs : orderOf (⟨x, hxy⟩ : ↥Yc) = 2 := TwoThin.orderOf_mk_centralizer hxy hx
  have hΛC := TwoThin.le_centralizer_mk hHU.1 hxy
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hHU hxy
  obtain ⟨hΛE, hJsub, L₁, hL₁, hcases, hLJ, hLsJ, hK'⟩ := TwoThin.pumpupY_structure hs hΛC hΛ2
  have hJeq : pumpUp 2 H y = (TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype := by
    rw [TwoThin.pumpUp_eq_map_pumpupY, inf_eq_left.2 hHy, Thm9S45.pLayerOf_self hH]
  refine ⟨?_, ?_⟩
  · rcases hcases with ⟨-, hΛL⟩ | ⟨hne, hAB, hdiag⟩
    ·
      have hJ2 := Thm9S45.pumpupY_isTwoComponent_of_vertical hΛC hΛ2 hJsub hL₁ hΛL hLJ
      rw [hJeq]
      refine TwoThin.isPCompIn_two_iff.mpr ⟨Subgroup.map_subtype_le _, ?_⟩
      have hcm : ((TwoThin.pumpupY (H.subgroupOf Yc)).map Yc.subtype).subgroupOf Yc =
          TwoThin.pumpupY (H.subgroupOf Yc) :=
        Subgroup.comap_map_eq_self_of_injective Yc.subtype_injective _
      rw [hcm]
      exact hJ2
    ·
      exfalso
      obtain ⟨⟨n, hn, hnx⟩, -, -, -, hcomm1⟩ := hF
      have hnT : n ∈ normalizer (T : Set G) := (Subgroup.mem_inf.1 hn).1
      have hny : n * y * n⁻¹ = y := by
        have := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
        rw [this]
        group
      obtain ⟨F, hFf, hFin, S, hLH, hSD⟩ :=
        S3PumpSData.exists_sdata_layer hK hyK hy hcfg.shape
      have hxc : proj y ⟨x, hxy⟩ ∈ _root_.commutator (CentralizerBar y) := by
        obtain ⟨c, hc, hcx⟩ := hcomm1
        have h1 : proj y ⟨x, hxy⟩ ∈
            (_root_.commutator ↥(centralizer ({y} : Set G))).map (proj y) := by
          refine ⟨c, hc, ?_⟩
          have : c = ⟨x, hxy⟩ := Subtype.ext hcx
          rw [this]
        have h2 : (_root_.commutator ↥(centralizer ({y} : Set G))).map (proj y) ≤
            _root_.commutator (CentralizerBar y) := by
          rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
          exact Subgroup.commutator_mono le_top le_top
        exact h2 h1
      have hperf : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) →
          ⁅R, R⁆ = R → ∀ r ∈ R, piC x r ∈ S.map (S3.imgBar x K).subtype := by
        intro R hRU hRperf r hr
        have hrΘ : r ∈ S3Fusion.Th x y := S3Fusion.le_maxPerfect hRU hRperf hr
        have hmem : piC x r ∈ S3.imgBar x (S3Fusion.Th x y) :=
          S3.mem_imgBar.2 ⟨⟨r, S3Fusion.Th_le_C x y hrΘ⟩, hrΘ, (piC_of_mem x _).symm⟩
        exact imgBar_Th_le_SX hcfg hnT hnx hny hSD hmem
      obtain ⟨ψ, hψs, -, hψc⟩ := hLH.psi_data hy hH
      have hWSX1 : ∀ w ∈ H, piC x w ∈ S.map (S3.imgBar x K).subtype := fun w hw =>
        ⟨(ψ ⟨w, hw⟩ : ↥(S3.imgBar x K)), (ψ ⟨w, hw⟩).2, hψc w hw⟩
      have hWSX2 : ∀ s ∈ S.map (S3.imgBar x K).subtype, ∃ w ∈ H, piC x w = s := by
        rintro _ ⟨s₀, hs₀, rfl⟩
        obtain ⟨⟨l, hl⟩, hψl⟩ := hψs ⟨s₀, hs₀⟩
        refine ⟨l, hl, ?_⟩
        rw [← hψc l hl, hψl]
        rfl
      exact false_of_diagonal_L3 hx hy hxy hSD hperf hHU.1 hWSX1 hWSX2 hxc hL₁ hne hAB hdiag
  ·
    have h1 := TwoThin.map_conj_pumpupY_le_of_le_centralizer (H.subgroupOf Yc) hΛC
    have hfwd : ∀ j ∈ pumpUp 2 H y, x * j * x⁻¹ ∈ pumpUp 2 H y := by
      intro j hj
      rw [hJeq] at hj ⊢
      obtain ⟨j', hj', rfl⟩ := hj
      have h2 := h1 ⟨j', hj', rfl⟩
      exact ⟨_, h2, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · exact hfwd j
    · intro hj
      have := hfwd _ hj
      have e : x * (x * j * x⁻¹) * x⁻¹ = j := by
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
        rw [hxinv]
        calc x * (x * j * x) * x = (x * x) * j * (x * x) := by group
          _ = j := by rw [hx2]; group
      rwa [e] at this

end Main

end S3Pump9

end CFSG.GH74.Generic.BProg.B3
