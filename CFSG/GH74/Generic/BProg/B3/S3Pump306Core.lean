module

public import CFSG.GH74.Generic.BProg.B3.S3Pump9

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S45 CFSG.GH74.L5U5 CFSG.ABGLocalTools
  CFSG.Blueprint CFSG.GH74.GLS Subgroup CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K A T : Subgroup G}

abbrev Ux (x y : G) : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G)

theorem noPerf (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    {Q : Subgroup ↥(Ux x y)} (hQ : ⁅Q, Q⁆ = Q)
    (hcomm : ∀ q ∈ Q, ∀ b ∈ barSub y (Ly K y),
      proj y ⟨q.1, q.2.2⟩ * b = b * proj y ⟨q.1, q.2.2⟩) : Q = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcfg := cfg_of_setup30 h hT
  have hx : orderOf x = 2 := hcfg.hx
  have hy : orderOf y = 2 := hcfg.hy
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hcfg.hK
  have hyK : y ∈ K := hcfg.hyK
  have hH : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) := (Setup30.layer h).1
  have hWY : Ly K y ≤ Ux x y := fun g hg =>
    ⟨hK.1 (hH.1 hg).1, (hH.1 hg).2⟩
  obtain ⟨⟨n, hn, hnx⟩, -, -, -, -⟩ := hF
  have hnT : n ∈ normalizer (T : Set G) := (Subgroup.mem_inf.1 hn).1
  have hny : n * y * n⁻¹ = y := by
    have := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
    rw [this]
    group
  obtain ⟨F, hFf, hFin, S, hLH, hSD⟩ := S3PumpSData.exists_sdata_layer hK hyK hy hcfg.shape
  have hperf : ∀ R : Subgroup G, R ≤ Ux x y →
      ⁅R, R⁆ = R → ∀ r ∈ R, piC x r ∈ S.map (S3.imgBar x K).subtype := by
    intro R hRU hRperf r hr
    have hrΘ : r ∈ S3Fusion.Th x y := S3Fusion.le_maxPerfect hRU hRperf hr
    have hmem : piC x r ∈ S3.imgBar x (S3Fusion.Th x y) :=
      S3.mem_imgBar.2 ⟨⟨r, S3Fusion.Th_le_C x y hrΘ⟩, hrΘ, (piC_of_mem x _).symm⟩
    exact S3Pump9.imgBar_Th_le_SX hcfg hnT hnx hny hSD hmem
  obtain ⟨ψ, hψs, -, hψc⟩ := hLH.psi_data hy hH
  have hWSX1 : ∀ w ∈ Ly K y, piC x w ∈ S.map (S3.imgBar x K).subtype := fun w hw =>
    ⟨(ψ ⟨w, hw⟩ : ↥(S3.imgBar x K)), (ψ ⟨w, hw⟩).2, hψc w hw⟩
  have hWSX2 : ∀ s ∈ S.map (S3.imgBar x K).subtype, ∃ w ∈ Ly K y, piC x w = s := by
    rintro _ ⟨s₀, hs₀, rfl⟩
    obtain ⟨⟨l, hl⟩, hψl⟩ := hψs ⟨s₀, hs₀⟩
    refine ⟨l, hl, ?_⟩
    rw [← hψc l hl, hψl]
    rfl
  let f₁ : ↥(Ux x y) →* CentralizerBar x := (proj x).comp (Subgroup.inclusion inf_le_left)
  let f₂ : ↥(Ux x y) →* CentralizerBar y := (proj y).comp (Subgroup.inclusion inf_le_right)
  have hf₁ : ∀ g : ↥(Ux x y), f₁ g = proj x ⟨g.1, g.2.1⟩ := fun g => rfl
  have hf₂ : ∀ g : ↥(Ux x y), f₂ g = proj y ⟨g.1, g.2.2⟩ := fun g => rfl
  have h₁ : ∀ g : ↥(Ux x y), f₁ g = 1 → Odd (orderOf g) := by
    intro g hg
    have h := proj_odd x ⟨g.1, g.2.1⟩ hg
    have hord : orderOf (Subgroup.inclusion (inf_le_left : Ux x y ≤ centralizer ({x} : Set G)) g) =
        orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
    rw [← hord]
    exact h
  have h₂ : ∀ g : ↥(Ux x y), f₂ g = 1 → Odd (orderOf g) := by
    intro g hg
    have h := proj_odd y ⟨g.1, g.2.2⟩ hg
    have hord : orderOf (Subgroup.inclusion (inf_le_right : Ux x y ≤ centralizer ({y} : Set G)) g) =
        orderOf g := orderOf_injective _ (Subgroup.inclusion_injective _) g
    rw [← hord]
    exact h
  have hQW : Q.map f₁ ≤ S.map (S3.imgBar x K).subtype := by
    rintro _ ⟨q, hq, rfl⟩
    have hR : ⁅Q.map (Ux x y).subtype, Q.map (Ux x y).subtype⁆ = Q.map (Ux x y).subtype := by
      rw [← Subgroup.map_commutator, hQ]
    have := hperf (Q.map (Ux x y).subtype) (Subgroup.map_subtype_le Q) hR (q : G) ⟨q, hq, rfl⟩
    rw [piC_of_mem x q.2.1] at this
    exact this
  have hWSX : ((Ly K y).subgroupOf (Ux x y)).map f₁ = S.map (S3.imgBar x K).subtype := by
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
  have hcomm' : ∀ q ∈ Q, ∀ w ∈ (Ly K y).subgroupOf (Ux x y), q * w * q⁻¹ * w⁻¹ ∈ f₂.ker := by
    intro q hq w hw
    have hw' : f₂ w ∈ barSub y (Ly K y) := proj_mem_barSub (v := y) (J := Ly K y) w.2.2 hw
    have hc := hcomm q hq (f₂ w) hw'
    have h3 : f₂ q * f₂ w = f₂ w * f₂ q := hc
    have h4 : ⁅f₂ q, f₂ w⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h3
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv]
    rwa [commutatorElement_def] at h4
  exact S3Pump9.eq_bot_of_perfect_comm_ker_sdata f₁ f₂ h₁ h₂ hSD hWSX hQ hQW hcomm'

theorem noCent (h : Setup30 G x K A y) (hT : IsZT x y T) (hF : Prop301Concl x y T)
    (hxy : x ∈ centralizer ({y} : Set G)) {B : Subgroup (CentralizerBar y)} (hB : IsComponent B)
    (hBL : ∀ b ∈ B, ∀ c ∈ barSub y (Ly K y), b * c = c * b)
    (hBx : ∀ b ∈ B, proj y ⟨x, hxy⟩ * b = b * proj y ⟨x, hxy⟩) : False := by
  classical
  have hx : orderOf x = 2 := h.circ.1.1.1.1
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  let f₂ : ↥(Ux x y) →* CentralizerBar y := (proj y).comp (Subgroup.inclusion inf_le_right)
  have hBperf : ⁅B, B⁆ = B :=
    commutator_self_of_isQuasisimple (assembly_isQuasisimple_of_isComponent hB)
  have hBrange : B ≤ f₂.range := by
    intro b hb
    obtain ⟨g, hg, hgb⟩ := proj_cent y (u := ⟨x, hxy⟩) (Subtype.ext hx2) b (hBx b hb).symm
    have hgx : g.1 ∈ centralizer ({x} : Set G) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val hg)
    exact ⟨⟨g.1, ⟨hgx, g.2⟩⟩, hgb⟩
  obtain ⟨Q, hQperf, hQmap⟩ := exists_perfect_lift_hom f₂ hBperf hBrange
  have hQ0 : Q = ⊥ := noPerf h hT hF hQperf (fun q hq b hb => by
    have hfq : f₂ q ∈ B := by rw [← hQmap]; exact ⟨q, hq, rfl⟩
    exact hBL _ hfq b hb)
  have hB0 : B = ⊥ := by rw [← hQmap, hQ0, Subgroup.map_bot]
  exact FalseCtxS45Comp.false_of_commutator_self_eq_bot hB (by rw [hB0]; simp)

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
