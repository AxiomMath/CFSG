module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB2A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzbs_R_Z
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ r ∈ fzR t x₁ x₂, ∀ z ∈ fourGrp x₁ x₂, r * z * r⁻¹ = z := by
  refine fzl_cent_of_normal_two_group (R := fzR t x₁ x₂) (Z := fourGrp x₁ x₂)
    (rho := rho) (fzl_R_isPGroup t x₁ x₂) (fzl_rho_Z h).2.2.1 ?_ ?_ ?_ ?_
    (fzl_card_Z h) (fun z hz => fzl_Z_sq_eq_one h hz) (fzl_rho_Z h).2.2.2
  · intro r hr
    exact fzl_R_normal t x₁ x₂ rho (fzl_rho_Z h).1 r hr
  · intro z hz z' hz'
    exact congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W
      ⟨z, fzl_Z_le_W h hz⟩ ⟨z', fzl_Z_le_W h hz'⟩)
  · intro r hr z hz
    exact fzbs_conj_Z h (fzl_R_le_N2 t x₁ x₂ hr) hz
  · intro z hz
    exact fzbs_conj_Z h (fzl_rho_Z h).1 hz

theorem fzbs_R_fix_t
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau) {r : G}
    (hr : r ∈ fzR t x₁ x₂) (hrt : r * t * r⁻¹ = t) : r ∈ ctxW t x₁ x₂ ⊔ zpowers tau := by
  exact fzbs_ker_le h (fzl_R_le_N2 t x₁ x₂ hr) hrt (fzbs_R_Z h r hr)

theorem fzbs_R_t_surj
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 4) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f)
    {z : G} (hz : z ∈ fourGrp x₁ x₂) : ∃ r ∈ fzR t x₁ x₂, r * t * r⁻¹ = t * z := by
  have hR_N2 : fzR t x₁ x₂ ≤ fzN2 t x₁ x₂ := fzl_R_le_N2 t x₁ x₂
  have ht2 : t * t = 1 := S4A.t_mul_self h.hyp
  have htt : ∀ x : G, t * (t * x) = x := fun x => by
    rw [← mul_assoc, ht2, one_mul]
  let chi : ↥(fzR t x₁ x₂) →* ↥(fourGrp x₁ x₂) :=
    { toFun := fun r =>
        ⟨t * ((r : G) * t * (r : G)⁻¹), by
          obtain ⟨w, hw, hwr⟩ := fzbs_conj_t h (hR_N2 r.2)
          have hwt : t * ((r : G) * t * (r : G)⁻¹) = w := by rw [hwr, htt w]
          rwa [hwt]⟩
      map_one' := by
        apply Subtype.ext
        show t * ((1 : G) * t * (1 : G)⁻¹) = 1
        simp [ht2]
      map_mul' := by
        intro r r'
        apply Subtype.ext
        show t * (((r : G) * (r' : G)) * t * ((r : G) * (r' : G))⁻¹) =
          (t * ((r : G) * t * (r : G)⁻¹)) * (t * ((r' : G) * t * (r' : G)⁻¹))
        obtain ⟨w, hw, hwr⟩ := fzbs_conj_t h (hR_N2 r.2)
        obtain ⟨w', hw', hwr'⟩ := fzbs_conj_t h (hR_N2 r'.2)
        have hwfix : (r : G) * w' * (r : G)⁻¹ = w' := fzbs_R_Z h r r.2 w' hw'
        have hL : t * (((r : G) * (r' : G)) * t * ((r : G) * (r' : G))⁻¹) =
            w * w' := by
          have h1 : ((r : G) * (r' : G)) * t * ((r : G) * (r' : G))⁻¹ =
              (t * w) * w' := by
            calc ((r : G) * (r' : G)) * t * ((r : G) * (r' : G))⁻¹
                = (r : G) * ((r' : G) * t * (r' : G)⁻¹) * (r : G)⁻¹ := by group
              _ = (r : G) * (t * w') * (r : G)⁻¹ := by rw [hwr']
              _ = ((r : G) * t * (r : G)⁻¹) * ((r : G) * w' * (r : G)⁻¹) := by group
              _ = (t * w) * w' := by rw [hwr, hwfix]
          rw [h1, ← mul_assoc, htt w]
        have hR : (t * ((r : G) * t * (r : G)⁻¹)) *
            (t * ((r' : G) * t * (r' : G)⁻¹)) = w * w' := by
          rw [hwr, hwr', htt w, htt w']
        exact hL.trans hR.symm }
  have hW_le_R : ctxW t x₁ x₂ ≤ fzR t x₁ x₂ := by
    intro w hw
    obtain ⟨hg, hfg⟩ := (fzl_W_mem_iff hF w).mp hw
    refine (fzbs_R_mem_iff h hF w).mpr ⟨Subgroup.le_normalizer hw, ?_⟩
    rw [show (⟨w, Subgroup.le_normalizer hw⟩ : ↥(fzN2 t x₁ x₂)) = ⟨w, hg⟩ from
      Subtype.ext rfl, hfg]
    exact fzlK8.one_mem
  have hWtau_le_R : ctxW t x₁ x₂ ⊔ zpowers tau ≤ fzR t x₁ x₂ :=
    sup_le hW_le_R (Subgroup.zpowers_le.mpr (fzbs_tau_R h hF))
  have hker_eq : chi.ker = (ctxW t x₁ x₂ ⊔ zpowers tau).subgroupOf (fzR t x₁ x₂) := by
    ext r
    rw [MonoidHom.mem_ker]
    constructor
    · intro hr
      have hval : t * ((r : G) * t * (r : G)⁻¹) = 1 := congrArg Subtype.val hr
      have hrt : (r : G) * t * (r : G)⁻¹ = t := by
        calc (r : G) * t * (r : G)⁻¹ = t * (t * ((r : G) * t * (r : G)⁻¹)) :=
              (htt _).symm
          _ = t * 1 := by rw [hval]
          _ = t := mul_one t
      exact Subgroup.mem_subgroupOf.mpr (fzbs_R_fix_t h r.2 hrt)
    · intro hr
      apply Subtype.ext
      show t * ((r : G) * t * (r : G)⁻¹) = 1
      have hrt : (r : G) * t * (r : G)⁻¹ = t :=
        (fzbs_Wtau_act h (Subgroup.mem_subgroupOf.mp hr)).2.1
      rw [hrt, ht2]
  have hker_card : Nat.card chi.ker = 128 := by
    rw [hker_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWtau_le_R).toEquiv]
    exact (fzbs_card_Wtau h hK).2
  have hrange_card : Nat.card chi.range = 4 := by
    have hcard := Subgroup.card_ker_mul_card_range chi
    have hRcard : Nat.card ↥(fzR t x₁ x₂) = 512 := by
      rw [fzbs_card_R h hK hF]; norm_num
    rw [hker_card, hRcard] at hcard
    exact Nat.mul_left_cancel (by norm_num : 0 < 128)
      (hcard.trans (by norm_num : 128 * 4 = 512))
  have htop : chi.range = ⊤ :=
    Subgroup.eq_top_of_card_eq chi.range (by rw [hrange_card, fzl_card_Z h])
  have hzmem : (⟨z, hz⟩ : ↥(fourGrp x₁ x₂)) ∈ chi.range := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hzmem
  refine ⟨r.1, r.2, ?_⟩
  have hval : t * ((r : G) * t * (r : G)⁻¹) = z := congrArg Subtype.val hr
  calc (r : G) * t * (r : G)⁻¹ = t * (t * ((r : G) * t * (r : G)⁻¹)) := (htt _).symm
    _ = t * z := by rw [hval]

end CFSG.OddStandard.SmallF3.FritzII
