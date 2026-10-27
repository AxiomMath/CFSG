module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7q

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_theta_comm (c : Ctx7 G L) (hb : B5Std c) {a m u : G}
    (ha : a ∈ normIn L c.s.fr.B) (hm : m ∈ M7 c.s) (hu : u ∈ y7bBM c.s)
    (hmu : u⁻¹ * ⁅m, c.s.t⁆ ∈ M3 c.s) :
    (⁅a, u⁆)⁻¹ * ⁅⁅a, m⁆, c.s.t⁆ ∈ M3 c.s := by
  have hM7X7 : M7 c.s ≤ X7 c.s := (y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb)
  haveI hN : ((M3 c.s).subgroupOf (y7bBM c.s)).Normal := y7b_M3_normal_BM c hb
  obtain ⟨θ, hθ1, hθ2⟩ := y7b_exists_theta c hb
  have haH : a ∈ normIn c.s.H c.s.fr.B :=
    ⟨s3_L_le_H c.s hb.hH.hS ha.1, ha.2⟩
  let ym : ↥(X7 c.s) := ⟨m, hM7X7 hm⟩
  let uq : ↥(y7bBM c.s) := ⟨u, hu⟩
  have h1 : θ ym = QuotientGroup.mk uq := (hθ1 ym uq).mpr (by simpa [ym, uq] using hmu)
  have ham : a * m * a⁻¹ ∈ M7 c.s := (y7b_M7_normal c hb).2 a ha m hm
  let yam : ↥(X7 c.s) := ⟨a * m * a⁻¹, hM7X7 ham⟩
  have hau : a * u * a⁻¹ ∈ y7bBM c.s :=
    (Subgroup.mem_normalizer_iff.mp (y7b_normIn_norm_BM c hb haH).1 u).mp hu
  let auq : ↥(y7bBM c.s) := ⟨a * u * a⁻¹, hau⟩
  have h2 : θ yam = QuotientGroup.mk auq := hθ2 a haH ym yam rfl uq auq rfl h1
  have hxM7 : ⁅a, m⁆ ∈ M7 c.s := by
    simpa only [commutatorElement_def] using (M7 c.s).mul_mem ham ((M7 c.s).inv_mem hm)
  let x : ↥(X7 c.s) := ⟨⁅a, m⁆, hM7X7 hxM7⟩
  have hxcomm : ⁅a, u⁆ ∈ y7bBM c.s := by
    simpa only [commutatorElement_def] using
      (y7bBM c.s).mul_mem hau ((y7bBM c.s).inv_mem hu)
  let xuq : ↥(y7bBM c.s) := ⟨⁅a, u⁆, hxcomm⟩
  have hprod : auq * uq⁻¹ = xuq := by
    refine Subtype.ext ?_
    simp only [auq, uq, xuq, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
  have hx' : x = yam * ym⁻¹ := by
    refine Subtype.ext ?_
    simp only [x, yam, ym, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
  have hxeq : θ x = QuotientGroup.mk xuq := by
    calc θ x = θ yam * (θ ym)⁻¹ := by rw [hx', map_mul, map_inv]
      _ = QuotientGroup.mk auq * (QuotientGroup.mk uq)⁻¹ := by rw [h2, h1]
      _ = QuotientGroup.mk (auq * uq⁻¹) := by
            rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      _ = QuotientGroup.mk xuq := by rw [hprod]
  simpa [x, xuq] using (hθ1 x xuq).mp hxeq

theorem y7b_theta_eq (c : Ctx7 G L) (hb : B5Std c) {x u : G} (hx : x ∈ M7 c.s)
    (hu : u ∈ M7 c.s) (h : (⁅x, c.s.t⁆)⁻¹ * ⁅u, c.s.t⁆ ∈ M3 c.s) : x * u⁻¹ ∈ y7bBM c.s := by
  have hM7X7 : M7 c.s ≤ X7 c.s := (y7b_M7_le_C7 c hb).trans (y7b_C7_le_X7 c hb)
  have hxX7 : x ∈ X7 c.s := hM7X7 hx
  have huX7 : u ∈ X7 c.s := hM7X7 hu
  have hxt : ⁅x, c.s.t⁆ ∈ y7bBM c.s :=
    y7b_comm_t_mem_BM c hb x (y7b_X7_le_X c hxX7)
  have hut : ⁅u, c.s.t⁆ ∈ y7bBM c.s :=
    y7b_comm_t_mem_BM c hb u (y7b_X7_le_X c huX7)
  haveI hN : ((M3 c.s).subgroupOf (y7bBM c.s)).Normal := y7b_M3_normal_BM c hb
  obtain ⟨θ, hθ1, -⟩ := y7b_exists_theta c hb
  let X : ↥(X7 c.s) := ⟨x, hxX7⟩
  let U : ↥(X7 c.s) := ⟨u, huX7⟩
  let xr : ↥(y7bBM c.s) := ⟨⁅x, c.s.t⁆, hxt⟩
  let ur : ↥(y7bBM c.s) := ⟨⁅u, c.s.t⁆, hut⟩
  have hθX : θ X = QuotientGroup.mk xr :=
    (hθ1 X xr).mpr (by
      show (xr : G)⁻¹ * ⁅(X : G), c.s.t⁆ ∈ M3 c.s
      rw [show (xr : G) = ⁅(X : G), c.s.t⁆ from rfl, inv_mul_cancel]
      exact (M3 c.s).one_mem)
  have hθU : θ U = QuotientGroup.mk ur :=
    (hθ1 U ur).mpr (by
      show (ur : G)⁻¹ * ⁅(U : G), c.s.t⁆ ∈ M3 c.s
      rw [show (ur : G) = ⁅(U : G), c.s.t⁆ from rfl, inv_mul_cancel]
      exact (M3 c.s).one_mem)
  have hcls : (QuotientGroup.mk xr :
      ↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)) = QuotientGroup.mk ur := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa only [xr, ur, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hker : θ (X * U⁻¹) = 1 := by
    rw [map_mul, map_inv, hθX, hθU, hcls, mul_inv_cancel]
  have hcomm : ⁅x * u⁻¹, c.s.t⁆ ∈ M3 c.s := by
    have h1 := (hθ1 (X * U⁻¹) (1 : ↥(y7bBM c.s))).mp hker
    simpa [X, U] using h1
  have hX0 : x * u⁻¹ ∈ y7bX0 c.s :=
    (y7b_X0_iff c hb ((X7 c.s).mul_mem hxX7 ((X7 c.s).inv_mem huX7))).mpr hcomm
  have hC7 : x * u⁻¹ ∈ C7 c.s :=
    (C7 c.s).mul_mem (y7b_M7_le_C7 c hb hx) ((C7 c.s).inv_mem (y7b_M7_le_C7 c hb hu))
  have hW : x * u⁻¹ ∈ y7bW c.s := by
    have hmemW : x * u⁻¹ ∈ C7 c.s ⊓ y7bX0 c.s := Subgroup.mem_inf.mpr ⟨hC7, hX0⟩
    rwa [y7b_C7_inf_X0 c hb] at hmemW
  have hM7 : x * u⁻¹ ∈ M7 c.s :=
    (M7 c.s).mul_mem hx ((M7 c.s).inv_mem hu)
  have hmemBM : x * u⁻¹ ∈ M7 c.s ⊓ y7bW c.s := Subgroup.mem_inf.mpr ⟨hM7, hW⟩
  rwa [y7b_M7_inf_W c hb] at hmemBM

end CFSG.OddStandard.HigherRank.YamadaG23
