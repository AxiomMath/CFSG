module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Cover
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5FrameB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Dihed
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma conj_sq_eq_one {y g : G} (hy : y ^ 2 = 1) : (g * y * g⁻¹) ^ 2 = 1 := by
  rw [pow_two] at hy ⊢
  calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    _ = 1 := by rw [hy]; group

private lemma f3_mem_cen_conj {s : Setting3 G L} {x v : G}
    (hx : x ∈ normalizer (s.fr.B : Set G)) (hv : v ∈ cen s.fr.B) :
    x * v * x⁻¹ ∈ cen s.fr.B := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp hx v).mp hv.1, ?_⟩
  show x * v * x⁻¹ ∈ Subgroup.centralizer (s.fr.B : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb' : x⁻¹ * b * x ∈ s.fr.B := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) b).mp hb
    simpa using h
  have hcomm : v * (x⁻¹ * b * x) = (x⁻¹ * b * x) * v := (hv.2 _ hb').symm
  have hcalc : (x * v * x⁻¹) * b = b * (x * v * x⁻¹) := by
    calc (x * v * x⁻¹) * b = x * (v * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * v) * x⁻¹ := by rw [hcomm]
      _ = b * (x * v * x⁻¹) := by group
  exact hcalc.symm

private lemma f3_P_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ p ∈ f3P s, p ^ 2 ∈ cen s.fr.B := by
  intro p hp
  rcases f3_mem_P p hp with hb | ⟨b, hb, rfl⟩
  · exact y5_B_sq hH p hb
  · have htt : s.t * s.t = 1 := by
      rw [← pow_two, ← s.t_order]; exact pow_orderOf_eq_one s.t
    have hbt : b * s.t = s.t * b := s3_comm_t_of_mem_L s (f3_B_le_L s hb)
    have hsq : (b * s.t) ^ 2 = b ^ 2 := by
      rw [pow_two, pow_two]
      calc b * s.t * (b * s.t) = b * (s.t * b) * s.t := by group
        _ = b * (b * s.t) * s.t := by rw [← hbt]
        _ = b * b * (s.t * s.t) := by group
        _ = b * b := by rw [htt, mul_one]
    rw [hsq]
    exact y5_B_sq hH b hb

private lemma f3_sq_mul_mem {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {y p cc : G} (hp : p ∈ f3P s) (hy2 : y ^ 2 = 1) (hcc : cc ∈ cen s.fr.B)
    (hconj : y * p * y⁻¹ = cc * p) : (p * y) ^ 2 ∈ cen s.fr.B := by
  have hpc : p * cc = cc * p :=
    (Subgroup.mem_centralizer_iff.mp (f3_P_le_cent_V s hp) cc hcc).symm
  have hPsq : p ^ 2 ∈ cen s.fr.B := f3_P_sq hH p hp
  have key : (p * y) ^ 2 = cc * p ^ 2 := by
    rw [pow_two, pow_two]
    calc p * y * (p * y) = p * (y * p * y⁻¹) * y ^ 2 := by group
      _ = p * (cc * p) * y ^ 2 := by rw [hconj]
      _ = p * cc * p := by rw [hy2]; group
      _ = cc * p * p := by rw [hpc]
      _ = cc * (p * p) := by group
  rw [key]
  exact Subgroup.mul_mem (cen s.fr.B) hcc hPsq

private lemma f3_d_conj {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    ∀ p ∈ f3P c.s, ∃ cc ∈ cen c.s.fr.B, c.d * p * c.d⁻¹ = cc * p := by
  obtain ⟨w, hwV, hzV, hwne1, hzne1, hwnez, hwsq, hzsq, hwz, henum⟩ := f3_V_elems hH
  intro p hp
  have hpT1 : p ∈ c.e.T₁ := c.e.T_le (f3_P_le_T c.s hp)
  rcases y5_T1_conj_d hH p hpT1 with h | h
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    have hpd : p * c.d = c.d * p := by
      have h' := congrArg (· * p) h
      simpa [mul_assoc] using h'
    rw [← hpd]; group
  · refine ⟨c.s.fr.z, hzV, ?_⟩
    have hcomm : ⁅p, c.d⁆ = c.s.fr.z := by rw [commutatorElement_def, h]; group
    have hzinv : c.s.fr.z⁻¹ = c.s.fr.z := by
      rw [pow_two] at hzsq
      exact inv_eq_of_mul_eq_one_right hzsq
    have h2 : c.d * p * c.d⁻¹ = ⁅c.d, p⁆ * p := by rw [commutatorElement_def]; group
    rw [h2, ← commutatorElement_inv p c.d, hcomm, hzinv]

private lemma f3_conj_d_conj {c : Ctx5 G L} (hH : F33Hyp c.s c.e) {x : G}
    (hxN : x ∈ f3N c.s) :
    ∀ p ∈ f3P c.s, ∃ cc ∈ cen c.s.fr.B,
      (x * c.d * x⁻¹) * p * (x * c.d * x⁻¹)⁻¹ = cc * p := by
  intro p hp
  have hp' : x⁻¹ * p * x ∈ f3P c.s := by
    have h := (f3_extCtx hH).P_N x⁻¹ (inv_mem hxN) p hp
    simpa using h
  obtain ⟨cc0, hcc0, hconj⟩ := f3_d_conj hH (x⁻¹ * p * x) hp'
  refine ⟨x * cc0 * x⁻¹, f3_mem_cen_conj hxN.2 hcc0, ?_⟩
  have h1 : (x * c.d * x⁻¹) * p * (x * c.d * x⁻¹)⁻¹ =
      x * (c.d * (x⁻¹ * p * x) * c.d⁻¹) * x⁻¹ := by group
  rw [h1, hconj]
  group

theorem y52_sq_mem {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hd : c.d ∈ c.s.C₂) :
    ∀ x ∈ c.s.C₂, x ^ 2 ∈ cen c.s.fr.B := by
  obtain ⟨w, hwV, hzV, hwne1, hzne1, hwnez, hwsq, hzsq, hwz, henum⟩ := f3_V_elems hH
  have hdP : c.d ∉ f3P c.s := by
    intro hdP
    have hdX0 : c.d ∈ f3X0 c.s := f3_P_le_X0 c.s hdP
    have hdY : c.d ∈ f3Y c.s := (f3_extCtx hH).X₀_le hdX0
    have hphi1 : f3phi c.s c.d = 1 := (f3_phi_eq_one hH c.d hdY).mpr hdX0
    have hphiz : f3phi c.s c.d = c.s.fr.z := by
      show c.d * c.s.t * c.d⁻¹ * c.s.t⁻¹ = c.s.fr.z
      rw [y5_dtd hH]; group
    rw [hphiz] at hphi1
    exact hzne1 hphi1
  obtain ⟨k, hk⟩ := y52_exists_K hH
  have hkN : k ∈ f3N c.s := ⟨s3_L_le_H c.s hH.hS hk.mem.1, hk.mem.2⟩
  intro x hx
  obtain ⟨p, hpP, hcases⟩ := y52_cover hH hk hd hdP x hx
  rcases hcases with h | h | h | h
  · rw [h]; exact f3_P_sq hH p hpP
  · rw [h]; obtain ⟨cc, hcc, hconj⟩ := f3_d_conj hH p hpP
    exact f3_sq_mul_mem hH hpP (y5_d_sq c) hcc hconj
  · rw [h]; obtain ⟨cc, hcc, hconj⟩ := f3_conj_d_conj hH hkN p hpP
    exact f3_sq_mul_mem hH hpP (conj_sq_eq_one (y5_d_sq c)) hcc hconj
  · rw [h]; obtain ⟨cc, hcc, hconj⟩ :=
      f3_conj_d_conj hH (x := k ^ 2) (Subgroup.pow_mem (f3N c.s) hkN 2) p hpP
    exact f3_sq_mul_mem hH hpP (conj_sq_eq_one (y5_d_sq c)) hcc hconj

theorem y52_comm_mem {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hd : c.d ∈ c.s.C₂) :
    ∀ x ∈ c.s.C₂, ∀ y ∈ c.s.C₂, ⁅x, y⁆ ∈ cen c.s.fr.B := by
  have hsq : ∀ x ∈ c.s.C₂, x ^ 2 ∈ cen c.s.fr.B := y52_sq_mem hH hd
  have hcent : ∀ z ∈ c.s.C₂, ∀ v ∈ cen c.s.fr.B, z * v = v * z := fun z hz v hv =>
    (Subgroup.mem_centralizer_iff.mp (f3_C₂_le_Y hH hz).2 v hv).symm
  have hVleC : cen c.s.fr.B ≤ c.s.C₂ :=
    (inf_le_left.trans le_sup_left).trans (f3_P_le_C₂ hH)
  have hCtx : ExtCtx (cen c.s.fr.B) (cen c.s.fr.B) c.s.C₂ c.s.C₂ :=
    ⟨le_rfl, hVleC,
      fun n hn y hy => c.s.C₂.mul_mem (c.s.C₂.mul_mem hn hy) (c.s.C₂.inv_mem hn),
      fun y hy p hp => by
        have h : y * p * y⁻¹ = p := by rw [hcent y hy p hp]; group
        rwa [h],
      fun n hn p hp => by
        have h : n * p * n⁻¹ = p := by rw [hcent n hn p hp]; group
        rwa [h],
      fun y hy a ha => by
        have h : y * a * y⁻¹ = a := by rw [hcent y hy a ha]; group
        rwa [h],
      fun n hn a ha => by
        have h : n * a * n⁻¹ = a := by rw [hcent n hn a ha]; group
        rwa [h],
      fun a ha _ _ => Or.inl ha⟩
  exact ext_comm_mem hCtx hsq

private abbrev f3Vsub (s : Setting3 G L) : Subgroup ↥s.C₂ :=
  (cen s.fr.B).subgroupOf s.C₂

theorem y52_sec {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hd : c.d ∈ c.s.C₂) :
    SecProp c.s.C₂ (cen c.s.fr.B) (fun Y _ _ _ => IsElemAbelian 2 (⊤ : Subgroup Y)) := by
  have hsq : ∀ x ∈ c.s.C₂, x ^ 2 ∈ cen c.s.fr.B := y52_sq_mem hH hd
  have hcent : ∀ z ∈ c.s.C₂, ∀ v ∈ cen c.s.fr.B, z * v = v * z := fun z hz v hv =>
    (Subgroup.mem_centralizer_iff.mp (f3_C₂_le_Y hH hz).2 v hv).symm
  have hNnormal : (f3Vsub c.s).Normal := by
    refine Subgroup.normal_of_le_center fun v hv => ?_
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (hcent (w : G) w.2 (v : G) (Subgroup.mem_subgroupOf.mp hv))
  haveI : (f3Vsub c.s).Normal := hNnormal
  refine ⟨hNnormal, ?_⟩
  have hexp : ∀ q : ↥c.s.C₂ ⧸ f3Vsub c.s, q ^ 2 = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (f3Vsub c.s) q
    change (QuotientGroup.mk' (f3Vsub c.s) y) ^ 2 = 1
    rw [← map_pow]
    show ((y ^ 2 : ↥c.s.C₂) : ↥c.s.C₂ ⧸ f3Vsub c.s) = 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq (y : G) y.2
  have hcomm : IsMulCommutative (↥c.s.C₂ ⧸ f3Vsub c.s) := by
    apply IsMulCommutative.of_comm
    intro g h
    have hgh : (g * h) ^ 2 = 1 := hexp (g * h)
    rw [pow_two] at hgh
    calc g * h = (g * h)⁻¹ := (inv_eq_of_mul_eq_one_right hgh).symm
      _ = h⁻¹ * g⁻¹ := mul_inv_rev g h
      _ = h * g := by
        have hg := hexp g
        have hh := hexp h
        rw [pow_two] at hg hh
        rw [inv_eq_of_mul_eq_one_right hg, inv_eq_of_mul_eq_one_right hh]
  haveI : IsMulCommutative (↥c.s.C₂ ⧸ f3Vsub c.s) := hcomm
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    exact mul_comm' (a : ↥c.s.C₂ ⧸ f3Vsub c.s) (b : ↥c.s.C₂ ⧸ f3Vsub c.s)
  · intro x _
    exact hexp x

end CFSG.OddStandard.HigherRank.YamadaG23
