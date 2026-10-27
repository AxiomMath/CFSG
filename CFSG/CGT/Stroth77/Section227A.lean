module

public import CFSG.CGT.Stroth77.Section227Frame
public import CFSG.CGT.Stroth77.Arch76FrameChar
import CFSG.CGT.Stroth76.FrameLemma7
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.CGT.Stroth77

open CFSG.ABGLocalTools (IsSylowOf)

namespace Arch76

theorem d8_subset_d16 : ∀ m ∈ d8, m ∈ d16 := by decide +kernel

theorem matMul_self_of_fix_w : ∀ m ∈ d16, m.1 = (1, 0, 0) → matMul m m = mI := by
  decide +kernel

theorem eq_mI_of_fix_w : ∀ m ∈ d16, m.1 = (1, 0, 0) → matAct m (0, 2, 0) = (0, 2, 0) →
    matAct m (0, 1, 1) = (0, 1, 1) → m = mI := by
  decide +kernel

end Arch76

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame

open Arch76

variable (F : StrothFrame G)

theorem isD_A (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) :
    F.IsD F.A F.dA where
  A_le := le_rfl
  le_S := F.A_le_S
  uv_eq := rfl
  t_eq := rfl
  u_eq := rfl
  ρ_eq := rfl
  cent := by rw [inf_comm]; exact hCA

theorem evG_100 : F.evG (1, 0, 0) = (F.dA.c : G) := by
  show ((F.configN.ev (1, 0, 0) : Subgroup.normalizer (F.A : Set G)) : G) = _
  rw [F.configN.ev_w]; rfl

theorem evG_020 : F.evG (0, 2, 0) = ((F.dA.a : G)⁻¹) ^ 2 := by
  show ((F.configN.ev (0, 2, 0) : Subgroup.normalizer (F.A : Set G)) : G) = _
  rw [show ((0, 2, 0) : Co) = 2 • (0, 1, 0) by decide, F.configN.ev_nsmul, F.configN.ev_x]
  rfl

theorem evG_011 : F.evG (0, 1, 1) = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ := by
  show ((F.configN.ev (0, 1, 1) : Subgroup.normalizer (F.A : Set G)) : G) = _
  rw [F.configN.ev_011]; rfl

theorem mat_mem_d16_of_mem_S (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A)
    (q : Subgroup.normalizer (F.A : Set G)) (hq : (q : G) ∈ (F.S : Subgroup G)) :
    F.configN.mat q ∈ d16 := by
  rcases F.arch76Lemma2 hCA with hS | ⟨s, hsS, hS, hs2, hsc, hsa, hsb, -⟩
  · rw [hS] at hq
    obtain ⟨q', hq'T, hq'q⟩ := F.lift_T hq
    obtain rfl : q' = q := Subtype.ext hq'q
    exact d8_subset_d16 _ (F.configN.mat_mem_d8_of_T hq'T)
  · have hsN : s ∈ Subgroup.normalizer (F.A : Set G) := F.le_normalizer_A hCA hsS
    set s' : Subgroup.normalizer (F.A : Set G) := ⟨s, hsN⟩ with hs'
    have hs2' : s'⁻¹ = s' := Subtype.ext (inv_eq_of_mul_eq_one_right hs2)
    have h1 : F.configN.act s' (1, 0, 0) = (1, 0, 0) := F.configN.act_eq_of (by
      rw [F.configN.ev_w]
      exact Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_configN_w]; exact hsc.symm))
    have h2 : F.configN.act s' X0 = (0, 3, 0) := F.configN.act_eq_of (by
      rw [F.configN.ev_030, show X0 = (0, 1, 0) from rfl, F.configN.ev_x]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_configN_x]
      rw [show s⁻¹ * (F.dA.a : G)⁻¹ * s = (s⁻¹ * (F.dA.a : G) * s)⁻¹ by group, hsa])
    have h3 : F.configN.act s' Y0 = (0, 0, 3) := F.configN.act_eq_of (by
      rw [F.configN.ev_003, show Y0 = (0, 0, 1) from rfl, F.configN.ev_y]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_configN_y]
      rw [show s⁻¹ * (F.dA.b : G)⁻¹ * s = (s⁻¹ * (F.dA.b : G) * s)⁻¹ by group, hsb])
    have hmat : F.configN.mat s' = mS := by
      show (F.configN.act s' (1, 0, 0), F.configN.act s' X0, F.configN.act s' Y0) = mS
      rw [h1, h2, h3]; rfl
    rw [hS, ← F.T_s_map s'] at hq
    obtain ⟨q', hq', hq'q⟩ := Subgroup.mem_map.mp hq
    obtain rfl : q' = q := Subtype.ext hq'q
    exact F.configN.mat_mem_d16_of_T₁ hmat hs2' hq'

theorem act_w_of_mem_centralizer {q : Subgroup.normalizer (F.A : Set G)}
    (hq : (q : G) ∈ Subgroup.centralizer ({(F.dA.c : G)} : Set G)) :
    F.configN.act q (1, 0, 0) = (1, 0, 0) :=
  F.evG_mul_comm_iff.mp (by rw [F.evG_100]; exact Subgroup.mem_centralizer_singleton_iff.mp hq)

theorem sq_mem_A_of_mem_centralizer_w
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) {q : G}
    (hqS : q ∈ (F.S : Subgroup G)) (hqw : q ∈ Subgroup.centralizer ({(F.dA.c : G)} : Set G)) :
    q ^ 2 ∈ F.A := by
  set N := Subgroup.normalizer (F.A : Set G) with hN
  set q' : N := ⟨q, F.le_normalizer_A hCA hqS⟩ with hq'
  have hm := F.mat_mem_d16_of_mem_S hCA q' hqS
  have hsq : F.configN.mat (q' * q') = mI := by
    rw [Config.mat_mul]
    exact matMul_self_of_fix_w _ hm (F.act_w_of_mem_centralizer hqw)
  have hc := F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat hsq)
  rw [pow_two]
  exact F.mem_A_of_centralizer hCA (mul_mem hqS hqS) hc

theorem mem_A_of_commute_of_mem_centralizer_w
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) {q : G}
    (hqS : q ∈ (F.S : Subgroup G)) (hqw : q ∈ Subgroup.centralizer ({(F.dA.c : G)} : Set G))
    (h₁ : q * ((F.dA.a : G)⁻¹) ^ 2 = ((F.dA.a : G)⁻¹) ^ 2 * q)
    (h₂ : q * ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹) = ((F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹) * q) :
    q ∈ F.A := by
  set N := Subgroup.normalizer (F.A : Set G) with hN
  set q' : N := ⟨q, F.le_normalizer_A hCA hqS⟩ with hq'
  have hm := F.mat_mem_d16_of_mem_S hCA q' hqS
  have k₁ : F.configN.act q' (0, 2, 0) = (0, 2, 0) :=
    F.evG_mul_comm_iff.mp (by rw [F.evG_020]; exact h₁)
  have k₂ : F.configN.act q' (0, 1, 1) = (0, 1, 1) :=
    F.evG_mul_comm_iff.mp (by rw [F.evG_011]; exact h₂)
  rw [F.configN.act_eq_matAct] at k₁ k₂
  have hI := eq_mI_of_fix_w _ hm (F.act_w_of_mem_centralizer hqw) k₁ k₂
  exact F.mem_A_of_centralizer hCA hqS
    (F.coe_mem_centralizer (F.configN.mem_centralizer_of_mat hI))

theorem mem_A_iff_of_centralizer_inf_eq
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) (q : G) :
    q ∈ F.A ↔ (q ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G) ∧
      ∀ q' ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G),
        q * q' ^ 2 = q' ^ 2 * q) := by
  set K := F.dA.toConfig with hK
  have hAQ : ∀ a ∈ F.A,
      a ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G) := fun a ha =>
    ⟨F.A_le_S ha, Subgroup.mem_centralizer_singleton_iff.mpr (F.A_comm ha F.dA.c.2)⟩
  constructor
  · intro hq
    refine ⟨hAQ q hq, fun q' hq' => F.A_comm hq ?_⟩
    exact F.sq_mem_A_of_mem_centralizer_w hCA hq'.1 hq'.2
  · rintro ⟨hqQ, hq⟩
    have hx : K.x ∈ F.A := K.x_mem
    have hux : K.u * K.x ∈ (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G) := by
      refine ⟨mul_mem F.u_mem_S (F.A_le_S hx), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have huw : K.u * K.w = K.w * K.u := by
        calc K.u * K.w = K.u * (K.u⁻¹ * K.w * K.u) := by rw [K.hu_w]
          _ = K.w * K.u := by group
      calc K.u * K.x * K.w = K.u * (K.x * K.w) := by group
        _ = K.u * (K.w * K.x) := by rw [F.A_comm hx K.w_mem]
        _ = K.u * K.w * K.x := by group
        _ = K.w * K.u * K.x := by rw [huw]
        _ = K.w * (K.u * K.x) := by group
    have hsq : (K.u * K.x) ^ 2 = K.x * K.y := by
      have hu : K.u⁻¹ = K.u := inv_eq_of_mul_eq_one_right (by rw [← pow_two, K.hu2])
      calc (K.u * K.x) ^ 2 = (K.u⁻¹ * K.x * K.u) * K.x := by rw [pow_two, hu]; group
        _ = K.y * K.x := by rw [K.hu_x]
        _ = K.x * K.y := F.A_comm K.y_mem hx
    refine F.mem_A_of_commute_of_mem_centralizer_w hCA hqQ.1 hqQ.2 (hq _ (hAQ _ hx)) ?_
    have := hq _ hux
    rwa [hsq] at this

theorem mem_normalizer_A_of_mem_normalizer
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A) {g : G}
    (hg : g ∈ Subgroup.normalizer (((F.S : Subgroup G) ⊓
      Subgroup.centralizer ({(F.dA.c : G)} : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (F.A : Set G) := by
  set Q := (F.S : Subgroup G) ⊓ Subgroup.centralizer ({(F.dA.c : G)} : Set G) with hQ
  set σ := MulAut.conj g
  have hσ : ∀ x, σ x ∈ Q ↔ x ∈ Q := fun x => by
    rw [MulAut.conj_apply]; exact ((Subgroup.mem_normalizer_iff.mp hg) x).symm
  have hcharσ : ∀ q, σ q ∈ F.A ↔ q ∈ F.A := by
    intro q
    rw [F.mem_A_iff_of_centralizer_inf_eq hCA, F.mem_A_iff_of_centralizer_inf_eq hCA]
    refine and_congr (hσ q) ?_
    rw [← forall_mem_map_iff σ hσ (fun q' => σ q * q' ^ 2 = q' ^ 2 * σ q)]
    simp only [← map_pow, comm_map_iff σ hσ]
    exact Iff.rfl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [← MulAut.conj_apply, hcharσ]

theorem false_of_centralizer_inf_eq_A_of_isConj
    (hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A)
    (hall : IsConj (F.dA.c : G) ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSA : (F.S : Subgroup G) ≤ Subgroup.normalizer (F.A : Set G) := F.le_normalizer_A hCA
  have hD := F.isD_A hCA
  have hP : IsSylowOf 2 (F.S : Subgroup G) (Subgroup.normalizer (F.A : Set G)) := by
    have h := F.nsylowA
    rw [inf_eq_left.mpr hSA] at h
    exact CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨h.1, h.2.1, h.2.2⟩
  obtain ⟨p, hpN, -, hpA⟩ := F.exists_mem_normalizer_not_mem hP le_rfl le_rfl F.uv_mem_S
    F.t_mem_S (fun s hs => hD.commute_xy_sq hs) hall
  exact hpA (F.mem_normalizer_A_of_mem_normalizer hCA hpN)

theorem centralizer_inf_ne_A : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) ≠ F.A := by
  intro hCA
  by_cases hw : IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)
  · exact F.false_of_centralizer_inf_eq_A_of_isConj hCA hw
  · exact Stroth76.frame_centralizer_inf_ne_A F hw hCA

end StrothFrame

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem ne_A (h : F.IsD D dD) : D ≠ F.A := by
  rintro rfl
  exact F.centralizer_inf_ne_A (by rw [inf_comm]; exact h.cent)

theorem card_ne_32 (h : F.IsD D dD) : Nat.card D ≠ 32 := by
  intro hD
  refine h.ne_A (Subgroup.eq_of_le_of_card_ge h.A_le ?_).symm
  rw [hD, F.dA.card_eq_32]

end StrothFrame.IsD

end CFSG.CGT.Stroth77
