module

public import CFSG.GH74.Generic.BProg.B3.S3Pump306bcAux
public import CFSG.GH74.Generic.BProg.B3.S3Pump305
public import CFSG.GH74.GLS.C3.Layer1.BkIv81Core
public import CFSG.GH74.Generic.BProg.B3.S3Pump306Core

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5 CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

theorem le_CxK {H H₁ : Subgroup G} (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁)
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) H) (hne : H₁ ≠ H) : H₁ ≤ CxK y H :=
  fun _ hg => ⟨hH₁.1 hg, FalseCtxS45Comp.le_cSec_of_ne hH hH₁ hne.symm hg⟩

theorem barSub_comm_of_ne {J J' : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (hJ' : IsPCompIn 2 (centralizer ({y} : Set G)) J') (hne : J ≠ J') :
    ∀ a ∈ barSub y J, ∀ b ∈ barSub y J', a * b = b * a :=
  comm_of_commutator_eq_bot ((FalseCtxS45Comp.pCompIn_eq_or_commute hJ hJ').resolve_left hne)

theorem normalizer_of_ne (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {H₁ : Subgroup G}
    (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁)
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y))
    (hxH : x ∈ normalizer ((pumpUp 2 (Ly K y) y : Subgroup G) : Set G))
    (hne : H₁ ≠ pumpUp 2 (Ly K y) y) : x ∈ normalizer (H₁ : Set G) := by
  classical
  by_contra hxn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  set t : CentralizerBar y := proj y ⟨x, hxy⟩ with ht
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul]
    have : (⟨x, hxy⟩ * ⟨x, hxy⟩ : ↥(centralizer ({y} : Set G))) = 1 := Subtype.ext hx2
    rw [this, map_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set H₁' : Subgroup G := conjSub x H₁ with hH₁'def
  have hH₁' : IsPCompIn 2 (centralizer ({y} : Set G)) H₁' := FalseCtxS45Comp.isPCompIn_conj hH₁ hxy
  have hne' : H₁' ≠ pumpUp 2 (Ly K y) y := by
    intro heq
    apply hne
    have h1 : conjSub x⁻¹ H₁' = conjSub x⁻¹ (pumpUp 2 (Ly K y) y) := by rw [heq]
    rw [hH₁'def, conjSub_inv_conjSub, conjSub_eq_of_mem_normalizer (inv_mem hxH)] at h1
    exact h1
  rcases FalseCtxS45Comp.pCompIn_eq_or_commute hH₁ hH₁' with heq | hcomm
  · exact hxn (mem_normalizer_of_conjSub_eq heq.symm)
  set B : Subgroup (CentralizerBar y) := barSub y H₁ with hBdef
  have hB : IsComponent B := FalseCtxS45Comp.isComponent_bar hH₁
  have hBt : conjSub t⁻¹ B = barSub y H₁' := by
    ext b
    rw [ht, mem_conjSub_barSub_iff hxy, hxinv]
  have hAB' : ⁅B, conjSub t⁻¹ B⁆ = ⊥ := by rw [hBt]; exact hcomm
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
  let f₂ : ↥(Ux x y) →* CentralizerBar y := (proj y).comp (Subgroup.inclusion inf_le_right)
  have hΔrange : (swapDiag hAB').range ≤ f₂.range := by
    rintro _ ⟨b, rfl⟩
    have hyc : swapDiag hAB' b * t = t * swapDiag hAB' b :=
      mem_centralizer_singleton_iff.1 (swapDiag_mem_centralizer hAB' htinv b)
    obtain ⟨g, hg, hgy⟩ := proj_cent y (u := ⟨x, hxy⟩) (Subtype.ext hx2) (swapDiag hAB' b) hyc
    have hgx : g.1 ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
    exact ⟨⟨g.1, ⟨hgx, g.2⟩⟩, hgy⟩
  obtain ⟨Q, hQperf, hQmap⟩ := exists_perfect_lift_hom f₂ hΔperf hΔrange
  have hQ0 : Q = ⊥ := by
    refine S3Pump306.noPerf h hT hF hQperf (fun q hq b hb => ?_)
    have hfq : f₂ q ∈ (swapDiag hAB').range := by rw [← hQmap]; exact ⟨q, hq, rfl⟩
    obtain ⟨a, ha⟩ := hfq
    have hmem : f₂ q ∈ B ⊔ conjSub t⁻¹ B := by rw [← ha]; exact swapDiag_mem_sup hAB' a
    have hbH : b ∈ barSub y (pumpUp 2 (Ly K y) y) := barSub_mono (S3Pump305.le_pumpUp h) hb
    have hsup : B ⊔ conjSub t⁻¹ B ≤ centralizer ({b} : Set (CentralizerBar y)) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · exact mem_centralizer_singleton_iff.2 (barSub_comm_of_ne hH₁ hH hne a ha b hbH)
      · rw [hBt] at ha
        exact mem_centralizer_singleton_iff.2 (barSub_comm_of_ne hH₁' hH hne' a ha b hbH)
    exact mem_centralizer_singleton_iff.1 (hsup hmem)
  apply hΔne
  rw [← hQmap, hQ0, Subgroup.map_bot]

theorem not_mem_cSec (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {H₁ : Subgroup G}
    (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁)
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y))
    (hne : H₁ ≠ pumpUp 2 (Ly K y) y) : x ∉ centralizerSection H₁ (pPrimeCoreOf 2 H₁) := by
  intro hxc
  refine noCent h hT hF hxy (B := barSub y H₁) (FalseCtxS45Comp.isComponent_bar hH₁) ?_ ?_
  · intro b hb c hc
    exact barSub_comm_of_ne hH₁ hH hne b hb c (barSub_mono (S3Pump305.le_pumpUp h) hc)
  · exact bar_comm_of_mem_cSec hH₁ hxy hxc

theorem y_mem (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {H₁ : Subgroup G}
    (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁)
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y))
    (hxH : x ∈ normalizer ((pumpUp 2 (Ly K y) y : Subgroup G) : Set G))
    (hne : H₁ ≠ pumpUp 2 (Ly K y) y) : y ∈ H₁ := by
  classical
  by_contra hyH₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hy : orderOf y = 2 := h.y_ord
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hxN := normalizer_of_ne h hT hF hxy hH₁ hH hxH hne
  have hC0 : H₁ ≤ CxK y (pumpUp 2 (Ly K y) y) := le_CxK hH₁ hH hne
  have hH₁y : ∀ k ∈ H₁, k * y = y * k := fun k hk => mem_centralizer_singleton_iff.1 (hH₁.1 hk)
  have key : ∀ v ∈ H₁, v * v = 1 → v ≠ 1 → x * v = v * x → v = x ∨ v = x * y := by
    intro v hvH hv2 hv1 hxv
    rcases (S3Pump305.prop305_of_F h hT hF).2 v
      ⟨hC0 hvH, mem_centralizer_singleton_iff.2 hxv.symm⟩ hv2 with e | e | e | e
    · exact absurd e hv1
    · exact Or.inl e
    · exact absurd (e ▸ hvH) hyH₁
    · exact Or.inr e
  have hnotboth : x ∈ H₁ → x * y ∈ H₁ → False := by
    intro h1 h2
    apply hyH₁
    have := Subgroup.mul_mem _ (inv_mem h1) h2
    rwa [hxinv, ← mul_assoc, hx2, one_mul] at this
  obtain ⟨u, huH, hu2, hu1, hxu⟩ := KGroups.Bal.exists_fixed_involution (a := x) hx2 (J := H₁)
    (fun z hz => (Subgroup.mem_normalizer_iff.1 hxN z).1 hz)
    (GLS.C3.Layer1.Bk.even_card_of_isPCompIn hH₁)
  have hu : u = x ∨ u = x * y := key u huH hu2 hu1 hxu
  have hiso : ∀ g : ↥H₁, (g * (⟨u, huH⟩ : ↥H₁) * g⁻¹) * ⟨u, huH⟩ =
      ⟨u, huH⟩ * (g * ⟨u, huH⟩ * g⁻¹) → g * (⟨u, huH⟩ : ↥H₁) * g⁻¹ = ⟨u, huH⟩ := by
    intro g hg
    obtain ⟨v, hvdef⟩ : ∃ v : G, v = (g : G) * u * (g : G)⁻¹ := ⟨_, rfl⟩
    have hvH : v ∈ H₁ := by
      rw [hvdef]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 huH) (inv_mem g.2)
    have hv2 : v * v = 1 := by
      calc v * v = (g : G) * (u * u) * (g : G)⁻¹ := by rw [hvdef]; group
        _ = 1 := by rw [hu2]; group
    have hv1 : v ≠ 1 := by
      intro hv
      apply hu1
      have : u = (g : G)⁻¹ * v * (g : G) := by rw [hvdef]; group
      rw [this, hv]
      group
    have hguc : v * u = u * v := by
      have := congrArg Subtype.val hg
      rw [hvdef]
      exact this
    have hvx : x * v = v * x := by
      rcases hu with e | e
      · rw [e] at hguc
        exact hguc.symm
      · have hxe : x = u * y := by rw [e, mul_assoc, hy2, mul_one]
        have hvy := hH₁y v hvH
        rw [hxe]
        calc u * y * v = u * (y * v) := mul_assoc _ _ _
          _ = u * (v * y) := by rw [hvy]
          _ = (u * v) * y := (mul_assoc _ _ _).symm
          _ = (v * u) * y := by rw [hguc]
          _ = v * (u * y) := mul_assoc _ _ _
    have hvc := key v hvH hv2 hv1 hvx
    apply Subtype.ext
    show (g : G) * u * (g : G)⁻¹ = u
    rw [← hvdef]
    rcases hvc with e1 | e1 <;> rcases hu with e2 | e2
    · rw [e1, e2]
    · exfalso
      exact hnotboth (e1 ▸ hvH) (e2 ▸ huH)
    · exfalso
      exact hnotboth (e2 ▸ huH) (e1 ▸ hvH)
    · rw [e1, e2]
  have ht1 : (⟨u, huH⟩ : ↥H₁) ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
  have ht2 : (⟨u, huH⟩ : ↥H₁) * ⟨u, huH⟩ = 1 := Subtype.ext hu2
  have : Fintype ↥H₁ := Fintype.ofFinite _
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar ↥H₁ ⟨u, huH⟩ ht1 ht2 hiso
  have hNle : N ≤ pPrimeCore 2 ↥H₁ := le_sSup ⟨hNn, Nat.coprime_two_left.2 hNodd⟩
  have hucs : u ∈ centralizerSection H₁ (pPrimeCoreOf 2 H₁) := by
    refine ⟨Subgroup.le_normalizer huH, TwoThin.mem_normalizer_pPrimeCoreOf
      (Subgroup.le_normalizer huH), fun k hk => ?_⟩
    exact ⟨_, hNle (hNc ⟨k, hk⟩), rfl⟩
  have hycs : y ∈ centralizerSection H₁ (pPrimeCoreOf 2 H₁) := by
    have hyn : y ∈ normalizer (H₁ : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro k hk
      exact (hH₁y k hk)
    refine ⟨hyn, TwoThin.mem_normalizer_pPrimeCoreOf hyn, fun k hk => ?_⟩
    have : ⁅k, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hH₁y k hk)
    rw [this]
    exact Subgroup.one_mem _
  have hxcs : x ∈ centralizerSection H₁ (pPrimeCoreOf 2 H₁) := by
    rcases hu with e | e
    · rw [← e]; exact hucs
    · have hxe : x = u * y := by rw [e, mul_assoc, hy2, mul_one]
      rw [hxe]
      exact Subgroup.mul_mem _ hucs hycs
  exact not_mem_cSec h hT hF hxy hH₁ hH hne hxcs

theorem unique_invol (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {H₁ H₂ : Subgroup G}
    (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁)
    (hH₂ : IsPCompIn 2 (centralizer ({y} : Set G)) H₂)
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y))
    (hxH : x ∈ normalizer ((pumpUp 2 (Ly K y) y : Subgroup G) : Set G))
    (hne : H₁ ≠ pumpUp 2 (Ly K y) y) (hne₂ : H₂ ≠ H₁) (hne₂H : H₂ ≠ pumpUp 2 (Ly K y) y) :
    ∀ u ∈ H₁ ⊓ centralizer ({x} : Set G), orderOf u = 2 → u = y := by
  classical
  intro u hu hu2'
  by_contra huy
  have hy : orderOf y = 2 := h.y_ord
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy, pow_two] at this
  have hyH₁ : y ∈ H₁ := y_mem h hT hF hxy hH₁ hH hxH hne
  have hC0 : H₁ ≤ CxK y (pumpUp 2 (Ly K y) y) := le_CxK hH₁ hH hne
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2', pow_two] at this
  have hZ := (S3Pump305.prop305_of_F h hT hF).2 u ⟨hC0 hu.1, hu.2⟩ hu2
  have hxH₁ : x ∈ H₁ := by
    rcases hZ with e | e | e | e
    · exfalso
      rw [e, orderOf_one] at hu2'
      omega
    · rw [← e]; exact hu.1
    · exact absurd e huy
    · have hxe : x = u * y := by rw [e, mul_assoc, hy2, mul_one]
      rw [hxe]
      exact Subgroup.mul_mem _ hu.1 hyH₁
  refine noCent h hT hF hxy (B := barSub y H₂) (FalseCtxS45Comp.isComponent_bar hH₂) ?_ ?_
  · intro b hb c hc
    exact barSub_comm_of_ne hH₂ hH hne₂H b hb c (barSub_mono (S3Pump305.le_pumpUp h) hc)
  · intro b hb
    exact barSub_comm_of_ne hH₁ hH₂ hne₂.symm _ (proj_mem_barSub hxy hxH₁) b hb

theorem prop306bc_of_F (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    {H₁ : Subgroup G} (hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) H₁)
    (hne : H₁ ≠ pumpUp 2 (Ly K y) y) :
    x ∈ normalizer (H₁ : Set G) ∧ y ∈ H₁ ∧ x ∉ centralizerSection H₁ (pPrimeCoreOf 2 H₁) ∧
      ((∃ H₂ : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) H₂ ∧ H₂ ≠ H₁ ∧
          H₂ ≠ pumpUp 2 (Ly K y) y) →
        ∀ u ∈ H₁ ⊓ centralizer ({x} : Set G), orderOf u = 2 → u = y) := by
  obtain ⟨hH, hxH⟩ := S3Pump9.thm9_l3_rank1_of_F h hT hF
  have hcfg := cfg_of_setup30 h hT
  have hyC : y ∈ centralizer ({x} : Set G) := hcfg.hK.1 hcfg.hyK
  have hxy : x ∈ centralizer ({y} : Set G) := TwoThin.mem_centralizer_symm hyC
  refine ⟨normalizer_of_ne h hT hF hxy hH₁ hH hxH hne, y_mem h hT hF hxy hH₁ hH hxH hne,
    not_mem_cSec h hT hF hxy hH₁ hH hne, ?_⟩
  rintro ⟨H₂, hH₂, h1, h2⟩
  exact unique_invol h hT hF hxy hH₁ hH₂ hH hxH hne h1 h2

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
