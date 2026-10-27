module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7b_S_le_e4N (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.S ≤ e4N c.s :=
  c.s.S_le_R.trans (y7b_R_le_NHE hb.hH)

private theorem y7b_M4_le_e4Y (c : Ctx7 G L) (hb : B5Std c) :
    M4 c.e ≤ e4Y c.s :=
  (show M4 c.e ≤ C4 c.s from inf_le_left).trans (y56_C4_cand c.toCtx5 hb.hH).2.1

private noncomputable def y7b_phiM4 (c : Ctx7 G L) (hb : B5Std c) :
    ↥(M4 c.e) →* ↥(c.s.fr.E) :=
  MonoidHom.mk'
    (fun m => ⟨f3phi c.s (m : G), y56_phi_mem hb.hH (m : G) (y7b_M4_le_e4Y c hb m.2)⟩)
    (fun a b => Subtype.ext (by
      show f3phi c.s ((a * b : ↥(M4 c.e)) : G) = f3phi c.s (a : G) * f3phi c.s (b : G)
      rw [Subgroup.coe_mul,
        y56_phi_mul hb.hH (a : G) (y7b_M4_le_e4Y c hb a.2) (b : G) (y7b_M4_le_e4Y c hb b.2)]))

private theorem y7b_mem_H_of_f3phi_eq_one (c : Ctx7 G L) {z : G}
    (hz : f3phi c.s z = 1) : z ∈ c.s.H := by
  show z ∈ Subgroup.centralizer ({c.s.t} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : z * c.s.t * z⁻¹ = c.s.t := by
    have h' := congrArg (· * c.s.t) hz
    simpa [f3phi, mul_assoc] using h'
  calc z * c.s.t = z * c.s.t * z⁻¹ * z := by group
    _ = c.s.t * z := by rw [h]

theorem y7b_M4_le_M6 (c : Ctx7 G L) (hb : B5Std c) : M4 c.e ≤ M6 c.e :=
  hb.h71.2.2.2.2

theorem y7b_M4_le_NM3 (c : Ctx7 G L) (hb : B5Std c) :
    M4 c.e ≤ normalizer (M3 c.s : Set G) := by
  intro m hm
  exact Subgroup.mem_normalizer_fintype fun x hx =>
    y7b_M6_norm_M3 c hb m (y7b_M4_le_M6 c hb hm) x hx

theorem y7b_comm_M4_t (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M4 c.e, ⁅m, c.s.t⁆ ∈ c.s.fr.E := by
  intro m hm
  exact y56_phi_mem hb.hH m (y7b_M4_le_e4Y c hb hm)

theorem y7b_E_comm_S (c : Ctx7 G L) (hb : B5Std c) :
    ∀ f ∈ c.s.fr.E, ∀ x ∈ c.s.fr.S, ⁅f, x⁆ ∈ cen c.s.fr.B := by
  have hVE : cen c.s.fr.B ≤ c.s.fr.E := by
    rw [← y7b_E_inf_F hb.hH]; exact inf_le_left
  have h2 : (cen c.s.fr.B).relIndex c.s.fr.E = 2 :=
    relIndex_eq_of_card_eq_mul hVE (by norm_num [y7b_card_E hb.hH, y7b_card_V hb.hH])
  intro f hf x hx
  have hxB : x ∈ normalizer (c.s.fr.B : Set G) := y7b_S_le_normalizer_B hb.hH hx
  have hxV : x ∈ normalizer (cen c.s.fr.B : Set G) := by
    rw [show cen c.s.fr.B = c.s.fr.B ⊓ Subgroup.centralizer (c.s.fr.B : Set G) from rfl]
    exact mem_normalizer_inf hxB (mem_normalizer_centralizer hxB)
  have hxE : x ∈ normalizer (c.s.fr.E : Set G) := (Subgroup.mem_inf.mp (y7b_S_le_e4N c hb hx)).2
  by_cases hfV : f ∈ cen c.s.fr.B
  · have hconj : x * f⁻¹ * x⁻¹ ∈ cen c.s.fr.B :=
      (Subgroup.mem_normalizer_iff.mp hxV f⁻¹).mp ((cen c.s.fr.B).inv_mem hfV)
    rw [commutatorElement_def, show f * x * f⁻¹ * x⁻¹ = f * (x * f⁻¹ * x⁻¹) by group]
    exact (cen c.s.fr.B).mul_mem hfV hconj
  · have huE : x * f * x⁻¹ ∈ c.s.fr.E := (Subgroup.mem_normalizer_iff.mp hxE f).mp hf
    have huV : x * f * x⁻¹ ∉ cen c.s.fr.B := by
      intro hu
      apply hfV
      have hmem : x⁻¹ * (x * f * x⁻¹) * x ∈ cen c.s.fr.B :=
        (Subgroup.mem_normalizer_iff''.mp hxV (x * f * x⁻¹)).mp hu
      rwa [show x⁻¹ * (x * f * x⁻¹) * x = f by group] at hmem
    have hfuV : f⁻¹ * (x * f * x⁻¹) ∈ cen c.s.fr.B :=
      (mem_or_mem_of_relIndex_two hVE h2 (x := f) hf hfV huE).resolve_left huV
    have hmem : (x * f * x⁻¹)⁻¹ * f ∈ cen c.s.fr.B := by
      have h := (cen c.s.fr.B).inv_mem hfuV
      rwa [show (f⁻¹ * (x * f * x⁻¹))⁻¹ = (x * f * x⁻¹)⁻¹ * f by group] at h
    have hcomm : (x * f * x⁻¹)⁻¹ * f = f * (x * f * x⁻¹)⁻¹ :=
      y56_E_comm hb.hH (x * f * x⁻¹)⁻¹ ((c.s.fr.E).inv_mem huE) f hf
    rw [commutatorElement_def, show f * x * f⁻¹ * x⁻¹ = f * (x * f * x⁻¹)⁻¹ by group,
      ← hcomm]
    exact hmem

theorem y7b_comm_V2_t (c : Ctx7 G L) (hb : B5Std c) :
    ∀ v ∈ V2 c.e, ⁅v, c.s.t⁆ ∈ cen c.s.fr.B := by
  intro v hv
  have hvM4 : v ∈ M4 c.e := (show V2 c.e ≤ M4 c.e from inf_le_right) hv
  have hvM3 : v ∈ M3 c.s := (Subgroup.mem_inf.mp hv).1
  have hxE : ⁅v, c.s.t⁆ ∈ c.s.fr.E := y7b_comm_M4_t c hb v hvM4
  have hxM3 : ⁅v, c.s.t⁆ ∈ M3 c.s := by
    have htR : c.s.t ∈ c.s.R := s3_t_mem_R c.s
    have hconj : c.s.t * v⁻¹ * c.s.t⁻¹ ∈ M3 c.s :=
      y54_R_norm_M3 c.toCtx5 hb.hH c.s.t htR v⁻¹ ((M3 c.s).inv_mem hvM3)
    rw [commutatorElement_def, show v * c.s.t * v⁻¹ * c.s.t⁻¹ = v * (c.s.t * v⁻¹ * c.s.t⁻¹)
      by group]
    exact (M3 c.s).mul_mem hvM3 hconj
  have hxF : ⁅v, c.s.t⁆ ∈ c.s.fr.F := by
    have hxH : ⁅v, c.s.t⁆ ∈ c.s.H :=
      ((y56_E_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS)) hxE
    have hmem : ⁅v, c.s.t⁆ ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨hxH, hxM3⟩
    rwa [y54_H_inf_M3 c.toCtx5 hb.hH] at hmem
  rw [← y7b_E_inf_F hb.hH]
  exact Subgroup.mem_inf.mpr ⟨hxE, hxF⟩

theorem y7b_phi_V2 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ f ∈ cen c.s.fr.B, ∃ v ∈ V2 c.e, ⁅v, c.s.t⁆ = f := by
  have hV2M4 : V2 c.e ≤ M4 c.e := inf_le_right
  let ψ : ↥(V2 c.e) →* ↥(cen c.s.fr.B) :=
    MonoidHom.mk'
      (fun v => ⟨f3phi c.s (v : G), y7b_comm_V2_t c hb (v : G) v.2⟩)
      (fun a b => Subtype.ext (by
        show f3phi c.s ((a * b : ↥(V2 c.e)) : G) = f3phi c.s (a : G) * f3phi c.s (b : G)
        rw [Subgroup.coe_mul,
          y56_phi_mul hb.hH (a : G) (y7b_M4_le_e4Y c hb (hV2M4 a.2))
            (b : G) (y7b_M4_le_e4Y c hb (hV2M4 b.2))]))
  have hker : ψ.ker = (cen c.s.fr.B).subgroupOf (V2 c.e) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hvY : (v : G) ∈ e4Y c.s := y7b_M4_le_e4Y c hb (hV2M4 v.2)
    constructor
    · intro h
      have hφ : f3phi c.s (v : G) = 1 := congrArg Subtype.val h
      have hX0 : (v : G) ∈ e4X0 c.s := (y56_phi_eq_one hb.hH (v : G) hvY).mp hφ
      rw [← y7b_H_inf_V2 c hb]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hX0).1, v.2⟩
    · intro hv
      have hv' : (v : G) ∈ c.s.H ⊓ V2 c.e := by rwa [← y7b_H_inf_V2 c hb] at hv
      have hX0 : (v : G) ∈ e4X0 c.s :=
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv').1, (Subgroup.mem_inf.mp hvY).2⟩
      exact Subtype.ext ((y56_phi_eq_one hb.hH (v : G) hvY).mpr hX0)
  have hcard_ker : Nat.card ↥ψ.ker = 4 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (y7b_V_le_V2 c hb)).toEquiv,
      y7b_card_V hb.hH]
  have hcard_range : Nat.card ↥ψ.range = 4 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hcard_ker, hb.h72.1.2.2.2.1] at h
    norm_num at h ⊢
    omega
  have hrange_top : ψ.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [hcard_range, Subgroup.card_top, y7b_card_V hb.hH]
  intro f hf
  have hf' : (⟨f, hf⟩ : ↥(cen c.s.fr.B)) ∈ ψ.range := by
    rw [hrange_top]; exact Subgroup.mem_top _
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hf'
  exact ⟨(v : G), v.2, congrArg Subtype.val hv⟩

theorem y7b_comm_M4_S (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M4 c.e, ∀ x ∈ c.s.fr.S, ⁅m, x⁆ ∈ c.s.fr.E ⊔ V2 c.e := by
  intro m hm x hx
  have hM4Y := y7b_M4_le_e4Y c hb
  have hxR : x ∈ c.s.R := c.s.S_le_R hx
  have hxN4 : x ∈ normalizer (M4 c.e : Set G) := y7b_R_le_NM4 c hb hxR
  have hu4 : x * m⁻¹ * x⁻¹ ∈ M4 c.e :=
    (Subgroup.mem_normalizer_iff.mp hxN4 m⁻¹).mp ((M4 c.e).inv_mem hm)
  have hy4 : ⁅m, x⁆ ∈ M4 c.e := by
    rw [commutatorElement_def, show m * x * m⁻¹ * x⁻¹ = m * (x * m⁻¹ * x⁻¹) by group]
    exact (M4 c.e).mul_mem hm hu4
  have hxN : x ∈ e4N c.s := y7b_S_le_e4N c hb hx
  have hfE : f3phi c.s m ∈ c.s.fr.E := y7b_comm_M4_t c hb m hm
  have hxfxE : x * (f3phi c.s m)⁻¹ * x⁻¹ ∈ c.s.fr.E :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hxN).2 (f3phi c.s m)⁻¹).mp
      ((c.s.fr.E).inv_mem hfE)
  have hphi_y : f3phi c.s ⁅m, x⁆ = ⁅x, (f3phi c.s m)⁻¹⁆ := by
    have h1 : f3phi c.s ⁅m, x⁆ = f3phi c.s m * f3phi c.s (x * m⁻¹ * x⁻¹) := by
      rw [show ⁅m, x⁆ = m * (x * m⁻¹ * x⁻¹) by rw [commutatorElement_def]; group]
      exact y56_phi_mul hb.hH m (hM4Y hm) (x * m⁻¹ * x⁻¹) (hM4Y hu4)
    have h2 : f3phi c.s (x * m⁻¹ * x⁻¹) = x * (f3phi c.s m)⁻¹ * x⁻¹ := by
      have hinv : f3phi c.s m⁻¹ = (f3phi c.s m)⁻¹ := by
        have hmul := y56_phi_mul hb.hH m (hM4Y hm) m⁻¹ ((e4Y c.s).inv_mem (hM4Y hm))
        rw [mul_inv_cancel, show f3phi c.s 1 = 1 by simp [f3phi]] at hmul
        exact eq_inv_of_mul_eq_one_right hmul.symm
      rw [y56_phi_conj hb.hH x hxN m⁻¹, hinv]
    rw [h1, h2, y56_E_comm hb.hH (f3phi c.s m) hfE (x * (f3phi c.s m)⁻¹ * x⁻¹) hxfxE,
      commutatorElement_def]
    group
  have hphi_y_memV : f3phi c.s ⁅m, x⁆ ∈ cen c.s.fr.B := by
    have h := y7b_E_comm_S c hb (f3phi c.s m)⁻¹ ((c.s.fr.E).inv_mem hfE) x hx
    rw [hphi_y, ← commutatorElement_inv (g₁ := (f3phi c.s m)⁻¹) (g₂ := x)]
    exact (cen c.s.fr.B).inv_mem h
  obtain ⟨v, hv2, hvφ⟩ := y7b_phi_V2 c hb (f3phi c.s ⁅m, x⁆) hphi_y_memV
  have hv4 : v ∈ M4 c.e := (show V2 c.e ≤ M4 c.e from inf_le_right) hv2
  have hyv4 : ⁅m, x⁆ * v⁻¹ ∈ M4 c.e := (M4 c.e).mul_mem hy4 ((M4 c.e).inv_mem hv4)
  have hphi_yv : f3phi c.s (⁅m, x⁆ * v⁻¹) = 1 := by
    have hmap : f3phi c.s (⁅m, x⁆ * v⁻¹) =
        f3phi c.s ⁅m, x⁆ * (f3phi c.s v)⁻¹ := by
      have h := map_mul (y7b_phiM4 c hb) (⟨⁅m, x⁆, hy4⟩ : ↥(M4 c.e))
        (⟨v, hv4⟩ : ↥(M4 c.e))⁻¹
      rw [map_inv] at h
      exact congrArg Subtype.val h
    have hvφ' : f3phi c.s v = f3phi c.s ⁅m, x⁆ := hvφ
    rw [hmap, hvφ']
    exact mul_inv_cancel _
  have hyvE : ⁅m, x⁆ * v⁻¹ ∈ c.s.fr.E := by
    have hmem : ⁅m, x⁆ * v⁻¹ ∈ c.s.H ⊓ M4 c.e :=
      Subgroup.mem_inf.mpr ⟨y7b_mem_H_of_f3phi_eq_one c hphi_yv, hyv4⟩
    rwa [y7b_H_inf_M4 c hb] at hmem
  rw [show ⁅m, x⁆ = (⁅m, x⁆ * v⁻¹) * v by group]
  exact (c.s.fr.E ⊔ V2 c.e).mul_mem (Subgroup.mem_sup_left hyvE) (Subgroup.mem_sup_right hv2)

theorem y7b_M4_le_NBM (c : Ctx7 G L) (hb : B5Std c) :
    M4 c.e ≤ normalizer (y7bBM c.s : Set G) := by
  have hle : c.s.fr.E ⊔ V2 c.e ≤ y7bBM c.s :=
    sup_le ((y56_E_le_B hb.hH).trans le_sup_left) (inf_le_left.trans le_sup_right)
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  obtain ⟨b, hbB, m3, hm3, rfl⟩ := (y7b_mem_BM c hb).mp hu
  have hmb : m * b * m⁻¹ ∈ y7bBM c.s := by
    have hc : ⁅m, b⁆ ∈ y7bBM c.s := hle (y7b_comm_M4_S c hb m hm b (s3_B_le_S c.s hbB))
    rw [show m * b * m⁻¹ = ⁅m, b⁆ * b by rw [commutatorElement_def]; group]
    exact (y7bBM c.s).mul_mem hc (Subgroup.mem_sup_left hbB)
  have hm3' : m * m3 * m⁻¹ ∈ y7bBM c.s :=
    Subgroup.mem_sup_right (y7b_M6_norm_M3 c hb m (y7b_M4_le_M6 c hb hm) m3 hm3)
  rw [show m * (b * m3) * m⁻¹ = (m * b * m⁻¹) * (m * m3 * m⁻¹) by group]
  exact (y7bBM c.s).mul_mem hmb hm3'

theorem y7b_M4_le_NW (c : Ctx7 G L) (hb : B5Std c) :
    M4 c.e ≤ normalizer (y7bW c.s : Set G) := by
  intro m hm
  refine Subgroup.mem_normalizer_fintype fun u hu => ?_
  obtain ⟨w, hw, hu'⟩ := (y7b_mem_W c hb).mp hu
  have hwBM : m * w * m⁻¹ ∈ y7bW c.s :=
    y7b_BM_le_W c hb ((Subgroup.mem_normalizer_iff.mp (y7b_M4_le_NBM c hb hm) w).mp hw)
  rcases hu' with huw | huw
  · rw [huw]; exact hwBM
  · rw [huw]
    have hwt : m * (w * c.s.t) * m⁻¹ = (m * w * m⁻¹) * (m * c.s.t * m⁻¹) := by group
    rw [hwt]
    have h2 : m * c.s.t * m⁻¹ ∈ y7bW c.s := by
      rw [show m * c.s.t * m⁻¹ = ⁅m, c.s.t⁆ * c.s.t by rw [commutatorElement_def]; group]
      exact (y7b_mem_W c hb).mpr
        ⟨⁅m, c.s.t⁆, Subgroup.mem_sup_left (y56_E_le_B hb.hH (y7b_comm_M4_t c hb m hm)),
          Or.inr rfl⟩
    exact (y7bW c.s).mul_mem hwBM h2

theorem y7b_M4_le_X (c : Ctx7 G L) (hb : B5Std c) : M4 c.e ≤ y7bX c.s := by
  intro m hm
  exact Subgroup.mem_inf.mpr ⟨y7b_M4_le_NW c hb hm, y7b_M4_le_NM3 c hb hm⟩

theorem y7b_comm_M4_t_mem_BM (c : Ctx7 G L) (hb : B5Std c) :
    ∀ m ∈ M4 c.e, ⁅m, c.s.t⁆ ∈ y7bBM c.s := by
  intro m hm
  exact Subgroup.mem_sup_left (y56_E_le_B hb.hH (y7b_comm_M4_t c hb m hm))

end CFSG.OddStandard.HigherRank.YamadaG23
