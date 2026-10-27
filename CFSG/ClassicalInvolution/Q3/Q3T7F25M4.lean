module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M3
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Data
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Fus

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25

section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Data
variable (hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂)
include hyp
theorem exists_nonfused_of_data {g : G} (hg : g * z * g⁻¹ = t) (ht2 : t * t = 1) {x c₁ ω : G}
    (hc₁R : c₁ ∈ R) (hc₁4 : orderOf c₁ = 4) (hωc₁ : ω * c₁ = c₁ * ω) (hω2 : ω * ω = 1)
    (htω : t * ω = ω * t) (hω1 : ω ≠ 1) (hωz : ω ≠ z) (hxt : x⁻¹ * t * x = t * ω) :
    ∃ s' : G, s' * s' = 1 ∧ s' * z = z * s' ∧ (∃ y : G, y * z * y⁻¹ = s') ∧
      conjSub s' K ≠ K ∧ ¬ ∃ y : G, y * z * y⁻¹ = s' * z := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 := hyp.hE4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  obtain ⟨htS, htz, -⟩ := hyp.ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hs2 : (t * ω) * (t * ω) = 1 := by
    calc (t * ω) * (t * ω) = (t * (ω * t)) * ω := by group
      _ = (t * (t * ω)) * ω := by rw [htω]
      _ = (t * t) * (ω * ω) := by group
      _ = 1 := by rw [ht2, hω2]; group
  have hst : (t * ω) * t = t * (t * ω) := by
    calc (t * ω) * t = t * (ω * t) := by group
      _ = t * (t * ω) := by rw [htω]
  have hsne : t * ω ≠ t := by
    intro h
    apply hω1
    have := congrArg (fun w => t⁻¹ * w) h
    simpa using this
  obtain ⟨hsy⟩ : Nonempty (∃ y : G, y * z * y⁻¹ = t * ω) := by
    refine ⟨⟨x⁻¹ * g, ?_⟩⟩
    calc x⁻¹ * g * z * (x⁻¹ * g)⁻¹ = x⁻¹ * (g * z * g⁻¹) * x := by group
      _ = x⁻¹ * t * x := by rw [hg]
      _ = t * ω := hxt
  have hts : t * (t * ω) = ω := by
    calc t * (t * ω) = (t * t) * ω := by group
      _ = ω := by rw [ht2]; group
  have hnotz : ¬ ∃ y : G, y * z * y⁻¹ = ω := by
    rintro ⟨y, hy⟩
    have := T7ER.not_commute_of_conj hs hW₀ hE4 hK hz (y := y) (by rw [hy]; exact hωz)
      (hRsyl.1 hc₁R) hc₁4
    rw [hy] at this
    exact this hωc₁
  have hnotN : conjSub (t * ω) (conjSub g K) ≠ conjSub g K := by
    intro hN
    have hJt : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
    have htJ : IsUniqueInvolution (conjSub g K) t := by
      have := hz.conj g
      rwa [hg] at this
    have hsN : t * ω ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr hN
    obtain ⟨Rt, hRtsyl, hRtinv⟩ := T3.exists_sylow_normalized (T7ER.isPGroup_zpowers_of_sq hs2)
      (Subgroup.zpowers_le.mpr hsN)
    have hRtmem : Rt ∈ RSet Ω := mem_RSet_of_isSylow2In hJt hRtsyl
    have hRtq : IsQuatSub Rt := hΩ.isQuatSub_of_mem_RSet hRtmem
    have htRt : t ∈ Rt := T7C.mem_of_isSylow2In hΩ hJt hRtsyl htJ
    have hzRt : IsUniqueInvolution Rt t :=
      ⟨htRt, htJ.ne_one, htJ.sq, fun y hy hy2 => htJ.unique y (hRtsyl.1 hy) hy2⟩
    have hsRt : conjSub (t * ω) Rt = Rt := hRtinv _ (Subgroup.mem_zpowers _)
    have hbR : ∀ r ∈ Rt, (t * ω) * r * (t * ω)⁻¹ ∈ Rt := fun r hr => by
      have := conj_mem_conjSub (n := t * ω) hr
      rwa [hsRt] at this
    have hfixt : ∀ r ∈ Rt, orderOf r = 4 → (t * ω) * r * (t * ω)⁻¹ ≠ r := by
      intro r hr hr4 h
      obtain ⟨y, hy⟩ := hsy
      have := T7ER.not_commute_of_conj hs hW₀ hE4 hJt htJ (y := y)
        (by rw [hy]; exact hsne) (hRtsyl.1 hr) hr4
      rw [hy] at this
      apply this
      have h1 := congrArg (fun w => w * (t * ω)) h
      simpa [mul_assoc] using h1
    obtain ⟨ρ, hρ, hρs⟩ := T7ER.exists_conj_eq_mul_inv hRtq hzRt hs2 hbR hfixt
    apply hnotz
    obtain ⟨y, hy⟩ := hsy
    refine ⟨ρ⁻¹ * y, ?_⟩
    calc ρ⁻¹ * y * z * (ρ⁻¹ * y)⁻¹ = ρ⁻¹ * (y * z * y⁻¹) * ρ := by group
      _ = ρ⁻¹ * (t * ω) * ρ := by rw [hy]
      _ = ρ⁻¹ * ((t * ω) * ρ * (t * ω)⁻¹) * (t * ω) := by group
      _ = ρ⁻¹ * (ρ * t) * (t * ω) := by rw [hρs]
      _ = t * (t * ω) := by group
      _ = ω := hts
  refine ⟨g⁻¹ * (t * ω) * g, ?_, ?_, ?_, ?_, ?_⟩
  · calc g⁻¹ * (t * ω) * g * (g⁻¹ * (t * ω) * g) = g⁻¹ * ((t * ω) * (t * ω)) * g := by group
      _ = 1 := by rw [hs2]; group
  · have hzg : z = g⁻¹ * t * g := by rw [← hg]; group
    calc g⁻¹ * (t * ω) * g * z = g⁻¹ * ((t * ω) * t) * g := by rw [hzg]; group
      _ = g⁻¹ * (t * (t * ω)) * g := by rw [hst]
      _ = z * (g⁻¹ * (t * ω) * g) := by rw [hzg]; group
  · obtain ⟨y, hy⟩ := hsy
    refine ⟨g⁻¹ * y, ?_⟩
    calc g⁻¹ * y * z * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * z * y⁻¹) * g := by group
      _ = g⁻¹ * (t * ω) * g := by rw [hy]
  · intro hN
    apply hnotN
    have h1 : conjSub (g * (g⁻¹ * (t * ω) * g)) K = conjSub ((t * ω) * g) K := by
      congr 1; group
    rw [conjSub_mul, hN, conjSub_mul] at h1
    exact h1.symm
  · rintro ⟨y, hy⟩
    apply hnotz
    refine ⟨g * y, ?_⟩
    have hzg : z = g⁻¹ * t * g := by rw [← hg]; group
    have hsz : g⁻¹ * (t * ω) * g * z = g⁻¹ * ω * g := by
      calc g⁻¹ * (t * ω) * g * z = g⁻¹ * ((t * ω) * t) * g := by rw [hzg]; group
        _ = g⁻¹ * (t * (t * ω)) * g := by rw [hst]
        _ = g⁻¹ * ω * g := by rw [hts]
    rw [hsz] at hy
    calc g * y * z * (g * y)⁻¹ = g * (y * z * y⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * ω * g) * g⁻¹ := by rw [hy]
      _ = ω := by group
end Data
section Swap
variable (hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂)
include hyp
theorem not_orderOf_four_of_mem_inf {y : G} (hyR : y ∈ R) (hyR' : y ∈ R') (hy4 : orderOf y = 4)
    (ht2 : t * t = 1) (hRt : conjSub t R = R') : False := by
  have hT : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t := ⟨hyp, hyp.ht.1, ht2, hRt⟩
  have hle : Subgroup.zpowers y ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hyR, hyR'⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hy4, hT.inf_R_R'] at h1
  omega
theorem data_of_swap (ht2 : t * t = 1) (hRt : conjSub t R = R') :
    ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧ t * ω = ω * t ∧
      ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
  have hT : T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t := ⟨hyp, hyp.ht.1, ht2, hRt⟩
  obtain ⟨hu₁R, hu₁4, -⟩ := hyp.hu₁
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set c₂ : G := t * u₁⁻¹ * t with hc₂
  have hc₂R' : c₂ ∈ R' := by
    have := conj_mem_conjSub (n := t) (R.inv_mem hu₁R)
    rw [hRt, hti] at this
    exact this
  have hc₂4 : orderOf c₂ = 4 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj t) u₁⁻¹
    simp only [MulAut.conj_apply, hti] at h
    rw [hc₂, h, orderOf_inv, hu₁4]
  have hcc : u₁ * c₂ = c₂ * u₁ := hT.hcomm u₁ hu₁R c₂ hc₂R'
  have hc₁sq : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hT.hzR hu₁R hu₁4
  have hc₂sq : c₂ * c₂ = z := T7A.sq_eq_of_orderOf_four hT.hzR' hc₂R' hc₂4
  have hzz : z * z = 1 := hyp.std.setting.hz.sq
  have hω2 : (c₂ * u₁) * (c₂ * u₁) = 1 := by
    calc (c₂ * u₁) * (c₂ * u₁) = c₂ * (u₁ * c₂) * u₁ := by group
      _ = c₂ * (c₂ * u₁) * u₁ := by rw [hcc]
      _ = (c₂ * c₂) * (u₁ * u₁) := by group
      _ = 1 := by rw [hc₁sq, hc₂sq, hzz]
  have hωinv : (c₂ * u₁)⁻¹ = c₂ * u₁ := inv_eq_of_mul_eq_one_right hω2
  have h1 : t * c₂ * t = u₁⁻¹ := by
    rw [hc₂]
    calc t * (t * u₁⁻¹ * t) * t = (t * t) * u₁⁻¹ * (t * t) := by group
      _ = u₁⁻¹ := by rw [ht2]; group
  have h2 : t * u₁ * t = c₂⁻¹ := by
    rw [hc₂]
    calc t * u₁ * t = t⁻¹ * u₁ * t⁻¹ := by rw [hti]
      _ = (t * u₁⁻¹ * t)⁻¹ := by group
  have hconj : t * (c₂ * u₁) * t = c₂ * u₁ := by
    calc t * (c₂ * u₁) * t = (t * c₂ * t) * (t * u₁ * t) := by
          calc t * (c₂ * u₁) * t = t * c₂ * (t * t) * u₁ * t := by rw [ht2]; group
            _ = (t * c₂ * t) * (t * u₁ * t) := by group
      _ = u₁⁻¹ * c₂⁻¹ := by rw [h1, h2]
      _ = (c₂ * u₁)⁻¹ := by group
      _ = c₂ * u₁ := hωinv
  refine ⟨u₁, u₁, c₂ * u₁, hu₁R, hu₁4, ?_, hω2, ?_, ?_, ?_, ?_⟩
  · calc (c₂ * u₁) * u₁ = (u₁ * c₂) * u₁ := by rw [hcc]
      _ = u₁ * (c₂ * u₁) := by group
  · calc t * (c₂ * u₁) = (t * (c₂ * u₁) * t) * t := by
          rw [mul_assoc (t * (c₂ * u₁)) t t, ht2, mul_one]
      _ = (c₂ * u₁) * t := by rw [hconj]
  · intro h
    have hu : u₁ = c₂⁻¹ := eq_inv_of_mul_eq_one_right h
    exact not_orderOf_four_of_mem_inf hyp hu₁R (hu ▸ R'.inv_mem hc₂R') hu₁4 ht2 hRt
  · intro h
    have hc₂z : c₂ = z * u₁⁻¹ := by
      have : c₂ * u₁ * u₁⁻¹ = z * u₁⁻¹ := by rw [h]
      simpa using this
    have hc₂R : c₂ ∈ R := by
      rw [hc₂z]
      exact R.mul_mem hT.hzR.mem (R.inv_mem hu₁R)
    exact not_orderOf_four_of_mem_inf hyp hc₂R hc₂R' hc₂4 ht2 hRt
  · calc u₁⁻¹ * t * u₁ = (t * t) * u₁⁻¹ * t * u₁ := by rw [ht2]; group
      _ = t * (c₂ * u₁) := by rw [hc₂]; group
end Swap
end T7G2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7F2
open CFSG.ClassicalInvolution.Asc77.T7F2
section Aux
variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Asc77.T7F2 in
theorem false_of_fusion_gen (U : Set G) (hG : ∀ f : G →* Multiplicative (ZMod 2),
      (∀ u ∈ U, f u = 1) → f = 1)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B.relIndex (S : Subgroup G) = 2) (a : G)
    (haS : a ∈ (S : Subgroup G))
    (h1 : ∀ x : G, x⁻¹ * a * x ∈ (S : Subgroup G) → x⁻¹ * a * x ∉ B)
    (h2 : ∀ (i : ℕ) (x : G), x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G) →
      x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ B)
    (hU : ∀ u ∈ U, u ∈ (S : Subgroup G) ∧
      (∀ x : G, x⁻¹ * u * x ∈ (S : Subgroup G) → x⁻¹ * u * x ∈ B) ∧
      (∀ (i : ℕ) (x : G), x⁻¹ * u ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G) →
        x⁻¹ * u ^ (2 ^ (i + 1)) * x ∈ B)) : False := by
  classical
  set H : Subgroup G := (S : Subgroup G) with hH
  have hidx : (B.subgroupOf H).index = 2 := hB
  let ϕ : ↥H →* Multiplicative (ZMod 2) := charOfIndexTwo (B.subgroupOf H) hidx
  have hϕ1 : ∀ (y : G) (hy : y ∈ H), y ∈ B → ϕ ⟨y, hy⟩ = 1 := fun y hy hyB =>
    charOfIndexTwo_apply_of_mem hidx (Subgroup.mem_subgroupOf.mpr hyB)
  have hϕc : ∀ (y : G) (hy : y ∈ H), y ∉ B → ϕ ⟨y, hy⟩ = Multiplicative.ofAdd 1 := fun y hy hyB =>
    charOfIndexTwo_apply_of_not_mem hidx (fun h => hyB (Subgroup.mem_subgroupOf.mp h))
  have hord : ∀ b : G, b ∈ H → ∃ m : ℕ, orderOf b = 2 ^ m := by
    intro b hb
    have := (IsPGroup.iff_orderOf (p := 2) (G := ↥H)).mp S.isPGroup' ⟨b, hb⟩
    obtain ⟨m, hm⟩ := this
    exact ⟨m, by simpa using hm⟩
  have hc : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
  have hodd : Odd H.index := by
    have h2 : ¬ 2 ∣ H.index := S.not_dvd_index
    rw [Nat.odd_iff]
    omega
  have hone : ϕ.transfer = 1 := by
    refine hG _ (fun u hu => ?_)
    obtain ⟨huS, hu1, hu2⟩ := hU u hu
    obtain ⟨m, hm⟩ := hord u huS
    have hT := transfer_eq_pow_index ϕ u m hm 1 (by simp)
      (fun x hx => hϕ1 _ hx (hu1 x hx)) (fun i x hx => hϕ1 _ hx (hu2 i x hx))
    simpa using hT
  obtain ⟨m, hm⟩ := hord a haS
  have hT := transfer_eq_pow_index ϕ a m hm (Multiplicative.ofAdd (1 : ZMod 2)) hc
    (fun x hx => hϕc _ hx (h1 x hx)) (fun i x hx => hϕ1 _ hx (h2 i x hx))
  have hone' : ϕ.transfer a = 1 := by rw [hone]; rfl
  rw [hone'] at hT
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, hc, one_pow, one_mul] at hT
  exact absurd hT.symm (by decide)
end Aux
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
namespace Hyp25T
open CFSG.ClassicalInvolution.Asc77.T7F2.Hyp25T
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem conj_K_of_mem_C {a : G} (ha : a ∈ Csub S R) : conjSub a K = K := by
  have hcz : a⁻¹⁻¹ * z * a⁻¹ = z := by
    have h1 := (mem_Csub.mp ha).2 z h.hzR.mem
    calc a⁻¹⁻¹ * z * a⁻¹ = a * z * a⁻¹ := by rw [inv_inv]
      _ = (z * a) * a⁻¹ := by rw [h1]
      _ = z := by group
  have hc := h.conj_twin hcz (J := K) (Or.inl rfl)
  rw [inv_inv] at hc
  rcases hc with hc | hc
  · exact hc
  · exfalso
    have hRa : conjSub a R = R := conjSub_eq_of_centralizes (mem_Csub.mp ha).2
    have hle : R ≤ (S : Subgroup G) ⊓ K' := by
      refine le_inf h.hRS ?_
      have := conjSub_mono (n := a) h.hRsyl.1
      rw [hRa, hc] at this
      exact this
    rw [h.S_inf_K'] at hle
    have heq : R = R' :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq h.card_R_eq.symm)
    exact h.hne heq
variable (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z)
include h11
theorem sq_mem_R' {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) : a * a ∈ R' := by
  have haN : a ∈ Nsub S R := h.C_le_N ha
  have haP : a ∈ Psub S R := (le_sup_right : Csub S R ≤ Psub S R) ha
  have h1 : a * a ∈ Psub S R' := by
    rw [mul_mem_iff_of_relIndex_two d.hPi' haN haN]
  have h2 : a * a ∈ Psub S R := (Psub S R).mul_mem haP haP
  have h3 : a * a ∈ R ⊔ R' := h.P_inf_P' h11 ⟨h2, h1⟩
  exact h.mem_R'_of_mem_RR_of_mem_C h11 h3 ((Csub S R).mul_mem ha ha)
omit h h11 in

theorem exists_pow_eq_z {R' : Subgroup G} {z : G} (hR' : IsUniqueInvolution R' z)
    (hR'2 : IsPGroup 2 R') {c : G} (hc : c ∈ R') (hc1 : c ≠ 1) :
    ∃ j : ℕ, c ^ (2 ^ j) = z := by
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥R')).mp hR'2 ⟨c, hc⟩
  have he' : orderOf c = 2 ^ e := by simpa using he
  obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := by
    refine ⟨e - 1, ?_⟩
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exfalso
      subst h0
      exact hc1 (orderOf_eq_one_iff.mp (by simpa using he'))
    · omega
  refine ⟨j, ?_⟩
  have hsq : c ^ (2 ^ j) * c ^ (2 ^ j) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [← he']
    exact pow_orderOf_eq_one c
  rcases hR'.unique (c ^ (2 ^ j)) (R'.pow_mem hc _) hsq with h1 | h1
  · exfalso
    have := orderOf_dvd_of_pow_eq_one h1
    rw [he'] at this
    have h2 : 2 ^ (j + 1) ≤ 2 ^ j := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact h1
omit h h11 in

theorem exists_orderOf_eq {S : Sylow 2 G} {a : G} (ha : a ∈ (S : Subgroup G)) :
    ∃ e : ℕ, orderOf a = 2 ^ e := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥(S : Subgroup G))).mp
    S.isPGroup' ⟨a, ha⟩
  exact ⟨m, by simpa using hm⟩
omit h11 in

theorem exists_fuse {a : G} (ha : a ∈ Csub S R) {x : G} (hx : x⁻¹ * z * x = z)
    (hy : x⁻¹ * a * x ∈ (S : Subgroup G)) :
    ∃ w : G, ∃ κ ∈ R ⊔ R', w⁻¹ * a * w = κ * (x⁻¹ * a * x) ∧
      (w⁻¹ * a * w ∈ Csub S R ∨ w⁻¹ * a * w ∈ Csub S R') := by
  have hK := h.conj_K_of_mem_C ha
  have hyN : x⁻¹ * a * x ∈ Subgroup.normalizer ((conjSub x⁻¹ K : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul,
      show x⁻¹ * a * x * x⁻¹ = x⁻¹ * a by group, conjSub_mul, hK]
  have hR₁ : IsSylow2In (conjSub x⁻¹ R) (conjSub x⁻¹ K) := h.hRsyl.conj x⁻¹
  have hR₁c : ∀ r ∈ conjSub x⁻¹ R, (x⁻¹ * a * x) * r = r * (x⁻¹ * a * x) := by
    intro r hr
    have hr' : x * r * x⁻¹ ∈ R := by
      have := mem_conjSub_iff.mp hr
      simpa using this
    have h1 := (mem_Csub.mp ha).2 _ hr'
    calc (x⁻¹ * a * x) * r = x⁻¹ * (a * (x * r * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * r * x⁻¹) * a) * x := by rw [h1]
      _ = r * (x⁻¹ * a * x) := by group
  rcases h.conj_twin hx (J := K) (Or.inl rfl) with hJ | hJ
  · rw [hJ] at hyN hR₁
    obtain ⟨k, hk, κ, hκ, hkey, hkS, hkc⟩ :=
      fuse_aux hy hyN hR₁ h.hRsyl h.S_inf_K hR₁c
    refine ⟨x * k⁻¹, κ, (le_sup_left : R ≤ R ⊔ R') hκ, ?_, Or.inl ?_⟩
    · rw [← hkey]; group
    · refine mem_Csub.mpr ⟨?_, ?_⟩
      · convert hkS using 1; group
      · intro r hr
        have := hkc r hr
        convert this using 2 <;> group
  · rw [hJ] at hyN hR₁
    obtain ⟨k, hk, κ, hκ, hkey, hkS, hkc⟩ :=
      fuse_aux hy hyN hR₁ h.hR'syl h.S_inf_K' hR₁c
    refine ⟨x * k⁻¹, κ, (le_sup_right : R' ≤ R ⊔ R') hκ, ?_, Or.inr ?_⟩
    · rw [← hkey]; group
    · refine mem_Csub.mpr ⟨?_, ?_⟩
      · convert hkS using 1; group
      · intro r hr
        have := hkc r hr
        convert this using 2 <;> group
include h11
theorem conj_not_mem_B {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) (ha2 : a * a ≠ 1) {x : G} (hy : x⁻¹ * a * x ∈ (S : Subgroup G)) :
    x⁻¹ * a * x ∉ d.B := by
  intro hyB
  have haS : a ∈ (S : Subgroup G) := (mem_Csub.mp ha).1
  have hc : a * a ∈ R' := h.sq_mem_R' h11 d ha
  obtain ⟨j, hzj⟩ := exists_pow_eq_z h.hzR' (h.hR'syl.2.1) hc ha2
  have hyy : (x⁻¹ * a * x) * (x⁻¹ * a * x) ∈ R ⊔ R' := by
    obtain ⟨h1, h2⟩ := d.mul_self_mem hyB
    exact h.P_inf_P' h11 ⟨h1, h2⟩
  have hxz : x⁻¹ * z * x = z := by
    apply h.eq_z_of_conj_mem_RR
    rw [← hzj]
    have e : x⁻¹ * (a * a) ^ (2 ^ j) * x = ((x⁻¹ * a * x) * (x⁻¹ * a * x)) ^ (2 ^ j) := by
      have := (conj_pow (a := x⁻¹) (b := a * a) (i := 2 ^ j)).symm
      rw [inv_inv] at this
      rw [this]
      congr 1
      group
    rw [e]
    exact (R ⊔ R').pow_mem hyy _
  obtain ⟨w, κ, hκ, hwk, hw⟩ := h.exists_fuse ha hxz hy
  have hy'B : w⁻¹ * a * w ∈ d.B := by
    rw [hwk]
    exact d.B.mul_mem (d.D_le_B (h.RR_le_D d hκ)) hyB
  have hy'N : w⁻¹ * a * w ∈ Nsub S R := by
    rcases hw with hw | hw
    exacts [h.C_le_N hw, h.C'_le_N hw]
  have hy'D := d.mem_D_of_mem_B_of_mem_N hy'B hy'N
  have hy'RR : w⁻¹ * a * w ∈ R ⊔ R' := by
    rcases hw with hw | hw
    · have hP : w⁻¹ * a * w ∈ Psub S R := (le_sup_right : Csub S R ≤ Psub S R) hw
      exact h.P_inf_P' h11 ⟨hP, hy'D.2.mp hP⟩
    · have hP' : w⁻¹ * a * w ∈ Psub S R' := (le_sup_right : Csub S R' ≤ Psub S R') hw
      exact h.P_inf_P' h11 ⟨hy'D.2.mpr hP', hP'⟩
  obtain ⟨e, he⟩ := exists_orderOf_eq haS
  have he2 : 2 ≤ e := by
    by_contra hlt
    push Not at hlt
    apply ha2
    have hdvd : orderOf a ∣ 2 := by
      rw [he]
      calc 2 ^ e ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
        _ = 2 := by norm_num
    have := orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa [pow_two] using this
  have hord : orderOf (w⁻¹ * a * w) = 2 ^ e := by
    have := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) a
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, he]
  have hback : (w⁻¹)⁻¹ * (w⁻¹ * a * w) * w⁻¹ = a := by group
  have hmem : a ∈ R ∨ a ∈ R' := by
    rcases hw with hw | hw
    · have hv : w⁻¹ * a * w ∈ R' := h.mem_R'_of_mem_RR_of_mem_C h11 hy'RR hw
      have := h.conj_mem_R_or_R' (J := K') (Or.inr rfl) (h.hR'syl.1 hv) he2 hord (x := w⁻¹)
        (by rw [hback]; exact haS)
      rwa [hback] at this
    · have hv : w⁻¹ * a * w ∈ R := h.mem_R_of_mem_RR_of_mem_C' h11 hy'RR hw
      have := h.conj_mem_R_or_R' (J := K) (Or.inl rfl) (h.hRsyl.1 hv) he2 hord (x := w⁻¹)
        (by rw [hback]; exact haS)
      rwa [hback] at this
  have haP' : a ∈ Psub S R' := by
    rcases hmem with hm | hm
    · exact h.RR_le_P' ((le_sup_left : R ≤ R ⊔ R') hm)
    · exact h.RR_le_P' ((le_sup_right : R' ≤ R ⊔ R') hm)
  exact d.haP' haP'
theorem pow_conj_mem_B {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) (i : ℕ) {x : G}
    (hx : x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G)) :
    x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ d.B := by
  have hc : a * a ∈ R' := h.sq_mem_R' h11 d ha
  have hcpow : a ^ (2 ^ (i + 1)) ∈ R' := by
    have e : a ^ (2 ^ (i + 1)) = (a * a) ^ (2 ^ i) := by
      rw [pow_succ', pow_mul, pow_two]
    rw [e]
    exact R'.pow_mem hc _
  set c := a ^ (2 ^ (i + 1)) with hcdef
  obtain ⟨m, hm⟩ := exists_orderOf_eq (S := S) (h.hR'S hcpow)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · have : c = 1 := orderOf_eq_one_iff.mp (by simpa using hm)
      rw [this]
      simp
    · have hc2 : c * c = 1 := by
        have := pow_orderOf_eq_one c
        rw [hm] at this
        simpa [pow_two] using this
      have hcz : c = z := by
        rcases h.hzR'.unique c hcpow hc2 with h1 | h1
        · exfalso
          rw [h1, orderOf_one] at hm
          norm_num at hm
        · exact h1
      rw [hcz] at hx ⊢
      exact h.z_conj_mem_B d hx
  · have := h.conj_mem_R_or_R' (J := K') (Or.inr rfl) (h.hR'syl.1 hcpow) hm2 hm hx
    rcases this with h1 | h1
    · exact d.D_le_B (h.RR_le_D d ((le_sup_left : R ≤ R ⊔ R') h1))
    · exact d.D_le_B (h.RR_le_D d ((le_sup_right : R' ≤ R ⊔ R') h1))
theorem conj_mem_B_of_mem_R' {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    {c : G} (hcpow : c ∈ R') {x : G} (hx : x⁻¹ * c * x ∈ (S : Subgroup G)) :
    x⁻¹ * c * x ∈ d.B := by
  obtain ⟨m, hm⟩ := exists_orderOf_eq (S := S) (h.hR'S hcpow)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · have : c = 1 := orderOf_eq_one_iff.mp (by simpa using hm)
      rw [this]
      simp
    · have hc2 : c * c = 1 := by
        have := pow_orderOf_eq_one c
        rw [hm] at this
        simpa [pow_two] using this
      have hcz : c = z := by
        rcases h.hzR'.unique c hcpow hc2 with h1 | h1
        · exfalso
          rw [h1, orderOf_one] at hm
          norm_num at hm
        · exact h1
      rw [hcz] at hx ⊢
      exact h.z_conj_mem_B d hx
  · have := h.conj_mem_R_or_R' (J := K') (Or.inr rfl) (h.hR'syl.1 hcpow) hm2 hm hx
    rcases this with h1 | h1
    · exact d.D_le_B (h.RR_le_D d ((le_sup_left : R ≤ R ⊔ R') h1))
    · exact d.D_le_B (h.RR_le_D d ((le_sup_right : R' ≤ R ⊔ R') h1))

end Hyp25T
end T7F2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Swap
variable (hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂)
include hyp
theorem data_of_normalizes {g : G} (hg : g * z * g⁻¹ = t) (ht2 : t * t = 1)
    (hRt : conjSub t R = R) :
    ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧ t * ω = ω * t ∧
      ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hKK' : K' ≠ K := hs.hne
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 := hyp.hE4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz'
    (hRsyl.1) (hR'syl.1) (S.isPGroup'.to_le (sup_le hRS hR'S))
  have hRq : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hyp.hR.1
  have hR'q : IsQuatSub R' := hΩ.isQuatSub_of_mem_RSet hyp.hR'.1
  have hzR : IsUniqueInvolution R z :=
    ⟨T7C.mem_of_isSylow2In hΩ hK hRsyl hz, hz.ne_one, hz.sq,
      fun y hy hy2 => hz.unique y (hRsyl.1 hy) hy2⟩
  have hzR' : IsUniqueInvolution R' z :=
    ⟨T7C.mem_of_isSylow2In hΩ hK' hR'syl hz', hz.ne_one, hz.sq,
      fun y hy hy2 => hz'.unique y (hR'syl.1 hy) hy2⟩
  have hRR'inf : Nat.card ↥(R ⊓ R') ≤ 2 :=
    hΩ.card_le_two_of_le_inf hK hK' hKK'.symm
      (hRsyl.2.1.to_le (inf_le_left : R ⊓ R' ≤ R)) (inf_le_left.trans hRsyl.1)
      (inf_le_right.trans hR'syl.1)
  have hinf : ∀ y ∈ R, y ∈ R' → orderOf y ≠ 4 := by
    intro y hyR hyR' hy4
    have hle : Subgroup.zpowers y ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hyR, hyR'⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hy4] at h1
    omega
  obtain ⟨htS, htz, -⟩ := hyp.ht
  have hRt' : conjSub t R' = R' := by
    have hmem : conjSub t R' ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR'.1 t
    have hle : conjSub t R' ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hR'S hx)) (Subgroup.inv_mem _ htS)
      simpa [mul_assoc] using h1
    rcases hyp.hRS _ hmem hle with h | h
    · exfalso
      have h1 : conjSub t (conjSub t R') = conjSub t R := by rw [h]
      have h2 : conjSub t (conjSub t R') = R' := by
        rw [← conjSub_mul]
        have : t * t = 1 := ht2
        rw [this, conjSub_one]
      rw [h2, hRt] at h1
      have hRR' : R = R' := h1.symm
      have : Nat.card ↥R ≤ 2 := by
        have := hΩ.card_le_two_of_le_inf hK hK' hKK'.symm hRsyl.2.1 hRsyl.1
          (hRR' ▸ hR'syl.1)
        exact this
      have := hRq.eight_le
      omega
    · exact h
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := t) hr
    rwa [hRt] at this
  have htR' : ∀ r ∈ R', t * r * t⁻¹ ∈ R' := fun r hr => by
    have := conj_mem_conjSub (n := t) hr
    rwa [hRt'] at this
  have hfix : ∀ {J : Subgroup G} {a : G}, J ∈ Ω → IsUniqueInvolution J a →
      (∀ y : G, y * z * y⁻¹ = t → t ≠ a → ∀ x ∈ J, orderOf x = 4 → t * x * t⁻¹ ≠ x) := by
    intro J a hJ ha y hy hta x hx hx4 h
    have := T7ER.not_commute_of_conj hs hW₀ hE4 hJ ha (y := y) (by rw [hy]; exact hta) hx hx4
    rw [hy] at this
    apply this
    have h1 := congrArg (fun w => w * t) h
    simpa [mul_assoc] using h1
  have hfixR : ∀ x ∈ R, orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK hz g hg htz x (hRsyl.1 hx) hx4
  have hfixR' : ∀ x ∈ R', orderOf x = 4 → t * x * t⁻¹ ≠ x :=
    fun x hx hx4 => hfix hK' hz' g hg htz x (hR'syl.1 hx) hx4
  obtain ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩ :=
    T7ER.exists_twisted_conj hRq hR'q hzR hzR' hc hinf ht2 htR htR' hfixR hfixR'
  exact ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩
theorem exists_swap_nonfused :
    ∃ t' ∈ (S : Subgroup G), t' * t' = 1 ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
      ¬ ∃ y : G, y * z * y⁻¹ = t' * z := by
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  obtain ⟨htS, htz, g, hg⟩ := hyp.ht
  have ht2 : t * t = 1 := by
    rw [← hg]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have hmem : conjSub t R ∈ RSet Ω := RSet.conj hΩ.conjInvariant hyp.hR.1 t
  have hle : conjSub t R ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have h1 : t * (t⁻¹ * x * t) * t⁻¹ ∈ (S : Subgroup G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ htS (hRS hx)) (Subgroup.inv_mem _ htS)
    simpa [mul_assoc] using h1
  have hdata : ∃ x c₁ ω : G, c₁ ∈ R ∧ orderOf c₁ = 4 ∧ ω * c₁ = c₁ * ω ∧ ω * ω = 1 ∧
      t * ω = ω * t ∧ ω ≠ 1 ∧ ω ≠ z ∧ x⁻¹ * t * x = t * ω := by
    rcases hyp.hRS _ hmem hle with hRt | hRt
    · exact data_of_normalizes hyp hg ht2 hRt
    · exact data_of_swap hyp ht2 hRt
  obtain ⟨x, c₁, ω, hc₁R, hc₁4, hωc₁, hω2, htω, hω1, hωz, hxt⟩ := hdata
  obtain ⟨s', hs'2, hs'z, ⟨y, hy⟩, hs'K, hs'nf⟩ :=
    exists_nonfused_of_data hyp hg ht2 hc₁R hc₁4 hωc₁ hω2 htω hω1 hωz hxt
  obtain ⟨c, hcz, hcS⟩ := T7ER.exists_conj_mem_sylow_of_centralizes S hyp.hzS hs'2 hs'z
  refine ⟨c⁻¹ * s' * c, hcS, ?_, ⟨c⁻¹ * y, ?_⟩, ?_, ?_⟩
  · calc c⁻¹ * s' * c * (c⁻¹ * s' * c) = c⁻¹ * (s' * s') * c := by group
      _ = 1 := by rw [hs'2]; group
  · calc c⁻¹ * y * z * (c⁻¹ * y)⁻¹ = c⁻¹ * (y * z * y⁻¹) * c := by group
      _ = c⁻¹ * s' * c := by rw [hy]
  · have hmem' : conjSub (c⁻¹ * s' * c) R ∈ RSet Ω :=
      RSet.conj hΩ.conjInvariant hyp.hR.1 _
    have hle' : conjSub (c⁻¹ * s' * c) R ≤ (S : Subgroup G) := by
      intro x hx
      rw [mem_conjSub_iff] at hx
      have h1 : (c⁻¹ * s' * c) * ((c⁻¹ * s' * c)⁻¹ * x * (c⁻¹ * s' * c)) * (c⁻¹ * s' * c)⁻¹ ∈
          (S : Subgroup G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hcS (hRS hx)) (Subgroup.inv_mem _ hcS)
      simpa [mul_assoc] using h1
    rcases hyp.hRS _ hmem' hle' with h | h
    · exfalso
      have hKt : conjSub (c⁻¹ * s' * c) K = K := by
        by_contra hne
        have hK2 : conjSub (c⁻¹ * s' * c) K ∈ Ω := hΩ.conjInvariant _ K hK
        have hRK : R ≤ conjSub (c⁻¹ * s' * c) K := h ▸ conjSub_mono hRsyl.1
        have := hΩ.card_le_two_of_le_inf hK hK2 (Ne.symm hne) hRsyl.2.1 hRsyl.1 hRK
        have h8 := (hΩ.isQuatSub_of_mem_RSet hyp.hR.1).eight_le
        omega
      have h1 : conjSub s' (conjSub c K) = conjSub c K := by
        have h2 : conjSub (c * (c⁻¹ * s' * c)) K = conjSub (s' * c) K := by
          congr 1; group
        rw [conjSub_mul, hKt, conjSub_mul] at h2
        exact h2.symm
      rcases T7ER.conjSub_eq_of_centralizes hs hcz with h3 | h3
      · rw [h3] at h1
        exact hs'K h1
      · rw [h3] at h1
        exact hs'K ((T7ER.normalizes_iff_of_centralizes hs hs'z).mpr h1)
    · exact h
  · rintro ⟨y', hy'⟩
    apply hs'nf
    refine ⟨c * y', ?_⟩
    have hsz : c⁻¹ * s' * c * z = c⁻¹ * (s' * z) * c := by
      calc c⁻¹ * s' * c * z = c⁻¹ * s' * (c * z) := by group
        _ = c⁻¹ * s' * (z * c) := by rw [hcz]
        _ = c⁻¹ * (s' * z) * c := by group
    rw [hsz] at hy'
    calc c * y' * z * (c * y')⁻¹ = c * (y' * z * y'⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * (s' * z) * c) * c⁻¹ := by rw [hy']
      _ = s' * z := by group
end Swap
end T7G2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Struct
open CFSG.ClassicalInvolution.Asc77.T7F2
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem conj_mem_RR {x : G} (hx : x ∈ (S : Subgroup G)) {ρ : G} (hρ : ρ ∈ R ⊔ R') :
    x * ρ * x⁻¹ ∈ R ⊔ R' := by
  obtain ⟨r, hr, r', hr', rfl⟩ := Out.exists_mul_of_mem_sup_of_commute h.hcomm hρ
  have e : x * (r * r') * x⁻¹ = (x * r * x⁻¹) * (x * r' * x⁻¹) := by group
  rw [e]
  refine (R ⊔ R').mul_mem ?_ ?_
  · have h1 := conj_mem_conjSub (n := x) hr
    rcases h.perm_R hx with h2 | h2
    · rw [h2] at h1; exact (le_sup_left : R ≤ R ⊔ R') h1
    · rw [h2] at h1; exact (le_sup_right : R' ≤ R ⊔ R') h1
  · have h1 := conj_mem_conjSub (n := x) hr'
    rcases h.perm_R' hx with h2 | h2
    · rw [h2] at h1; exact (le_sup_left : R ≤ R ⊔ R') h1
    · rw [h2] at h1; exact (le_sup_right : R' ≤ R ⊔ R') h1
variable (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
include h11 h16
theorem struct (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')) :
    Csub S R' = R ∧ Csub S R = R' ∧ T7F2.Hyp25T.Psub S R' = R ⊔ R' ∧ T7F2.Hyp25T.Psub S R = R ⊔ R' ∧
      (R ⊔ R').relIndex (Nsub S R) = 2 := by
  have hSN := T7ER.card_eq_two_mul_normalizer h.hyp
  have hNc : Nat.card ↥(Nsub S R) = 2 * Nat.card ↥(R ⊔ R') := by
    have : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(Nsub S R) := hSN
    omega
  have hi := h.relIndex_P'_le h16
  have hc := h.card_C_le h11 h16
  have hq := h.card_P' h11
  have hρ := h.card_RR
  have hn := h.card_N
  have hrr : Nat.card R = Nat.card R' := h.card_R_eq
  have hdvd : Nat.card R ∣ Nat.card ↥(Csub S R') := Subgroup.card_dvd_of_le h.R_le_C'
  rw [hrr] at hdvd hρ
  obtain ⟨k, hk⟩ := hdvd
  have hr : 0 < Nat.card R' := Nat.card_pos
  have hρpos : 0 < Nat.card ↥(R ⊔ R') := Nat.card_pos
  have hcpos : 0 < Nat.card ↥(Csub S R') := Nat.card_pos
  set r := Nat.card R' with hrdef
  set ρ := Nat.card ↥(R ⊔ R') with hρdef
  set c := Nat.card ↥(Csub S R') with hcdef
  set q := Nat.card ↥(T7F2.Hyp25T.Psub S R') with hqdef
  set n := Nat.card ↥(Nsub S R) with hndef
  set i := (T7F2.Hyp25T.Psub S R').relIndex (Nsub S R) with hidef
  have hk2 : k ≤ 2 := by
    have : r * k ≤ r * 2 := by rw [← hk]; linarith
    exact Nat.le_of_mul_le_mul_left this hr
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hqk : q = ρ * k := by
    have h2 : q * 2 = (ρ * k) * 2 := by
      calc q * 2 = r * c := hq
        _ = r * (r * k) := by rw [hk]
        _ = (r * r) * k := by ring
        _ = (ρ * 2) * k := by rw [← hρ]
        _ = (ρ * k) * 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hi0 : i ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hn
    omega
  have hik : i * k = 2 := by
    have h1 : i * (ρ * k) = 2 * ρ := by rw [← hqk, hn, hNc]
    have h2 : ρ * (i * k) = ρ * 2 := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left hρpos h2
  have hcard : Nat.card ↥(T7F2.Hyp25T.Psub S R) = Nat.card ↥(T7F2.Hyp25T.Psub S R') := by
    rw [← h.conj_P', AscL62.natCard_conjSub]
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2' : k = 2 := by omega
    have hi1 : i = 1 := by rw [hk2'] at hik; omega
    have hNP' : Nsub S R ≤ T7F2.Hyp25T.Psub S R' := Subgroup.relIndex_eq_one.mp hi1
    have hNeq : T7F2.Hyp25T.Psub S R' = Nsub S R := le_antisymm h.P'_le_N hNP'
    have hPN : T7F2.Hyp25T.Psub S R = Nsub S R := by
      refine Subgroup.eq_of_le_of_card_ge h.P_le_N ?_
      rw [hcard, hNeq]
    have hCR : Csub S R' ≤ R := by
      intro x hx
      have hxN : x ∈ Nsub S R := h.C'_le_N hx
      have hxP : x ∈ T7F2.Hyp25T.Psub S R := by rw [hPN]; exact hxN
      obtain ⟨ρ₁, hρ₁, m, hm, hxm⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R) (B := Csub S R) (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hxP
      obtain ⟨hmS, hmR⟩ := mem_Csub.mp hm
      obtain ⟨hxS, hxR'⟩ := mem_Csub.mp hx
      have hρ₁S : ρ₁ ∈ (S : Subgroup G) := h.hRS hρ₁
      have hmR' : m ∈ Csub S R' := by
        refine mem_Csub.mpr ⟨hmS, fun y hy => ?_⟩
        have e : m = ρ₁⁻¹ * x := by rw [hxm]; group
        have h1 := h.hcomm ρ₁ hρ₁ y hy
        have h2 := hxR' y hy
        have h3 : y * ρ₁⁻¹ = ρ₁⁻¹ * y := by
          calc y * ρ₁⁻¹ = ρ₁⁻¹ * (ρ₁ * y) * ρ₁⁻¹ := by group
            _ = ρ₁⁻¹ * (y * ρ₁) * ρ₁⁻¹ := by rw [h1]
            _ = ρ₁⁻¹ * y := by group
        rw [e]
        calc y * (ρ₁⁻¹ * x) = (y * ρ₁⁻¹) * x := by group
          _ = (ρ₁⁻¹ * y) * x := by rw [h3]
          _ = ρ₁⁻¹ * (y * x) := by group
          _ = ρ₁⁻¹ * (x * y) := by rw [h2]
          _ = (ρ₁⁻¹ * x) * y := by group
      have hmz : m ∈ Subgroup.zpowers z := h.Csub_inf_Csub_le h11 ⟨hm, hmR'⟩
      have T7F2.Hyp25T.hzR : Subgroup.zpowers z ≤ R := Subgroup.zpowers_le.mpr h.hzR.mem
      rw [hxm]
      exact R.mul_mem hρ₁ (T7F2.Hyp25T.hzR hmz)
    have hle := Subgroup.card_le_of_le hCR
    rw [hk2'] at hk
    rw [hrr, ← hcdef] at hle
    omega
  have hi2 : i = 2 := by rw [hk1] at hik; omega
  have hC' : Csub S R' = R := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.R_le_C' ?_
    have e : Nat.card ↥(Csub S R') = r * k := hk
    rw [hrr, e, hk1, mul_one]
  have hP' : T7F2.Hyp25T.Psub S R' = R ⊔ R' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.RR_le_P' ?_
    have e : Nat.card ↥(T7F2.Hyp25T.Psub S R') = ρ * k := hqk
    rw [e, hk1, mul_one]
  have hP : T7F2.Hyp25T.Psub S R = R ⊔ R' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.RR_le_P ?_
    have e : Nat.card ↥(T7F2.Hyp25T.Psub S R') = ρ * k := hqk
    rw [hcard, e, hk1, mul_one]
  have hC : Csub S R = R' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge h.R'_le_C ?_
    have e : Nat.card ↥(Csub S R') = r * k := hk
    rw [h.card_C_eq, e, hk1, mul_one]
  refine ⟨hC', hC, hP', hP, ?_⟩
  have h2 := Subgroup.relIndex_mul_card (R ⊔ R') (Nsub S R)
  rw [inf_eq_left.mpr (sup_le h.R_le_N h.R'_le_N)] at h2
  have hρ0 : 0 < ρ := hρpos
  have : (R ⊔ R').relIndex (Nsub S R) * ρ = 2 * ρ := by rw [h2]; exact hNc
  exact Nat.eq_of_mul_eq_mul_right hρ0 this
end Struct
end T7G2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Frat
open CFSG.ClassicalInvolution.Asc77.T7F2
variable (h : Asc77.T7F2.Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
include h
theorem inf_R_R'_eq : R ⊓ R' = Subgroup.zpowers z := by
  have hzmem : z ∈ R ⊓ R' := Subgroup.mem_inf.mpr ⟨h.hzR.mem, h.hzR'.mem⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzmem) ?_).symm
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  rw [Nat.card_zpowers, hz2, h.inf_R_R']
theorem eq_one_or_z_of_mem_zpowers {w : G} (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, hk⟩ := hw
  simp only at hk
  subst hk
  have hzz : z * z = 1 := h.hz.sq
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  obtain ⟨m, hm⟩ := Int.even_or_odd' k
  rcases hm with rfl | rfl
  · left
    rw [zpow_mul, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]
theorem exists_conj_form {y w : G} (hw : w ∈ R ⊔ R') (hy : y = w * t') (hy2 : y * y = 1) :
    ∃ q ∈ R, y = q * t' * q⁻¹ ∨ y = q * t' * q⁻¹ * z := by
  have ht2 := h.ht'2
  have hti := h.ht'inv
  obtain ⟨q, hq, q', hq', rfl⟩ := Out.exists_mul_of_mem_sup_of_commute h.hcomm hw
  subst hy
  have hq''R : t' * q' * t' ∈ R := by
    have := conj_mem_conjSub (n := t') hq'
    rw [h.ht'R', hti] at this
    exact this
  have hqsR' : t' * q * t' ∈ R' := by
    have := conj_mem_conjSub (n := t') hq
    rw [h.ht'R, hti] at this
    exact this
  have hc2 : (t' * q' * t') * q' = q' * (t' * q' * t') := h.hcomm _ hq''R q' hq'
  have hc3 : (t' * q' * t') * (t' * q * t') = (t' * q * t') * (t' * q' * t') :=
    h.hcomm _ hq''R _ hqsR'
  have e1 : (q * q' * t') * (q * q' * t') = q * q' * ((t' * q * t') * (t' * q' * t')) := by
    calc (q * q' * t') * (q * q' * t') = q * q' * (t' * q * q' * t') := by group
      _ = q * q' * (t' * q * (t' * t') * q' * t') := by rw [ht2, mul_one]
      _ = q * q' * ((t' * q * t') * (t' * q' * t')) := by group
  have e2 : q * q' * ((t' * q * t') * (t' * q' * t')) =
      (q * (t' * q' * t')) * (q' * (t' * q * t')) := by
    calc q * q' * ((t' * q * t') * (t' * q' * t'))
        = q * (q' * ((t' * q * t') * (t' * q' * t'))) := by group
      _ = q * (q' * ((t' * q' * t') * (t' * q * t'))) := by rw [← hc3]
      _ = q * ((q' * (t' * q' * t')) * (t' * q * t')) := by group
      _ = q * (((t' * q' * t') * q') * (t' * q * t')) := by rw [← hc2]
      _ = (q * (t' * q' * t')) * (q' * (t' * q * t')) := by group
  have hab : (q * (t' * q' * t')) * (q' * (t' * q * t')) = 1 := by rw [← e2, ← e1]; exact hy2
  have ha₁ : q * (t' * q' * t') ∈ R ⊓ R' := by
    refine Subgroup.mem_inf.mpr ⟨R.mul_mem hq hq''R, ?_⟩
    have : q * (t' * q' * t') = (q' * (t' * q * t'))⁻¹ := eq_inv_of_mul_eq_one_left hab
    rw [this]
    exact R'.inv_mem (R'.mul_mem hq' hqsR')
  have hq'eq : q' = t' * (t' * q' * t') * t' := by
    calc q' = (t' * t') * q' * (t' * t') := by rw [ht2]; group
      _ = t' * (t' * q' * t') * t' := by group
  refine ⟨q, hq, ?_⟩
  rcases eq_one_or_z_of_mem_zpowers h (by rw [← inf_R_R'_eq h]; exact ha₁) with h0 | h0
  · left
    have hq'' : t' * q' * t' = q⁻¹ := eq_inv_of_mul_eq_one_right h0
    rw [hq''] at hq'eq
    rw [hq'eq]
    calc q * (t' * q⁻¹ * t') * t' = q * t' * q⁻¹ * (t' * t') := by group
      _ = q * t' * q⁻¹ := by rw [ht2, mul_one]
  · right
    have hq'' : t' * q' * t' = q⁻¹ * z := by
      rw [← h0]; group
    rw [hq''] at hq'eq
    rw [hq'eq]
    calc q * (t' * (q⁻¹ * z) * t') * t' = q * t' * q⁻¹ * z * (t' * t') := by group
      _ = q * t' * q⁻¹ * z := by rw [ht2, mul_one]
variable (h11 : (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
      Subgroup.zpowers z) (h16 : ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a)
  (h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R'))
include h11 h16 h4
theorem commutator_mem_RR {x : G} (hx : x ∈ (S : Subgroup G)) :
    x⁻¹ * t' * x * t'⁻¹ ∈ R ⊔ R' := by
  obtain ⟨-, -, -, -, hidx⟩ := struct h h11 h16 h4
  have ht2 := h.ht'2
  have hti := h.ht'inv
  have hN : ∀ n ∈ Nsub S R, n⁻¹ * t' * n * t'⁻¹ ∈ R ⊔ R' := by
    intro n hn
    have hy : t' * n * t'⁻¹ ∈ Nsub S R := h.N_conj hn
    have hinv : n⁻¹ ∈ Nsub S R := (Nsub S R).inv_mem hn
    have hiff : (n⁻¹ ∈ R ⊔ R' ↔ t' * n * t'⁻¹ ∈ R ⊔ R') := by
      constructor
      · intro h1
        have h2 : n ∈ R ⊔ R' := by simpa using (R ⊔ R').inv_mem h1
        exact conj_mem_RR h h.ht'S h2
      · intro h1
        have h2 := conj_mem_RR h h.ht'S h1
        have e : t' * (t' * n * t'⁻¹) * t'⁻¹ = n := by
          calc t' * (t' * n * t'⁻¹) * t'⁻¹ = (t' * t') * n * (t'⁻¹ * t'⁻¹) := by group
            _ = n := by rw [ht2, hti, ht2]; group
        rw [e] at h2
        exact (R ⊔ R').inv_mem h2
    have key := (mul_mem_iff_of_relIndex_two hidx hinv hy).mpr hiff
    have e : n⁻¹ * (t' * n * t'⁻¹) = n⁻¹ * t' * n * t'⁻¹ := by group
    rw [e] at key
    exact key
  rcases h.S_cover hx with hxN | htxN
  · exact hN x hxN
  · have := hN (t' * x) htxN
    have e : (t' * x)⁻¹ * t' * (t' * x) * t'⁻¹ = x⁻¹ * t' * x * t'⁻¹ := by group
    rw [e] at this
    exact this
variable {g : G} (hg : g * z * g⁻¹ = t') (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t' * z)
include hg hnf
theorem exists_mul_centralizer {x : G} (hx : x ∈ (S : Subgroup G)) :
    ∃ c ∈ (S : Subgroup G), c * t' = t' * c ∧ ∃ q ∈ R, x = c * q⁻¹ := by
  have ht2 := h.ht'2
  have hti := h.ht'inv
  have hw := commutator_mem_RR h h11 h16 h4 hx
  have hy2 : (x⁻¹ * t' * x) * (x⁻¹ * t' * x) = 1 := by
    calc (x⁻¹ * t' * x) * (x⁻¹ * t' * x) = x⁻¹ * (t' * t') * x := by group
      _ = 1 := by rw [ht2]; group
  have hy : x⁻¹ * t' * x = (x⁻¹ * t' * x * t'⁻¹) * t' := by group
  obtain ⟨q, hq, hcase⟩ := exists_conj_form h hw hy hy2
  have hqS : q ∈ (S : Subgroup G) := h.hRS hq
  have hxqS : x * q ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hx hqS
  have hxq : x = (x * q) * q⁻¹ := by group
  rcases hcase with h0 | h0
  · refine ⟨x * q, hxqS, ?_, q, hq, hxq⟩
    calc x * q * t' = x * (q * t' * q⁻¹) * q := by group
      _ = x * (x⁻¹ * t' * x) * q := by rw [← h0]
      _ = t' * (x * q) := by group
  · exfalso
    apply hnf
    refine ⟨(x * q)⁻¹ * g, ?_⟩
    have hzq : q⁻¹ * z * q = z := by
      have := h.hyp.hzS q hqS
      calc q⁻¹ * z * q = q⁻¹ * (z * q) := by group
        _ = q⁻¹ * (q * z) := by rw [this]
        _ = z := by group
    calc (x * q)⁻¹ * g * z * ((x * q)⁻¹ * g)⁻¹ = (x * q)⁻¹ * (g * z * g⁻¹) * (x * q) := by group
      _ = (x * q)⁻¹ * t' * (x * q) := by rw [hg]
      _ = q⁻¹ * (x⁻¹ * t' * x) * q := by group
      _ = q⁻¹ * (q * t' * q⁻¹ * z) * q := by rw [h0]
      _ = t' * (q⁻¹ * z * q) := by group
      _ = t' * z := by rw [hzq]
theorem exists_s : ∃ s ∈ Nsub S R, s ∉ R ⊔ R' ∧ s * t' = t' * s := by
  obtain ⟨-, -, -, -, hidx⟩ := struct h h11 h16 h4
  have hRRN : R ⊔ R' ≤ Nsub S R := sup_le h.R_le_N h.R'_le_N
  have hex : ∃ x₀ ∈ Nsub S R, x₀ ∉ R ⊔ R' := by
    by_contra hcon
    push Not at hcon
    have h1 : Nsub S R ≤ R ⊔ R' := fun x hx => hcon x hx
    have := Subgroup.relIndex_eq_one.mpr h1
    omega
  obtain ⟨x₀, hx₀N, hx₀⟩ := hex
  obtain ⟨c, hcS, hct, q, hq, hxq⟩ := exists_mul_centralizer h h11 h16 h4 hg hnf
    (mem_Nsub.mp hx₀N).1
  have hqN : q ∈ Nsub S R := h.R_le_N hq
  have hcN : c ∈ Nsub S R := by
    have e : c = x₀ * q := by rw [hxq]; group
    rw [e]
    exact (Nsub S R).mul_mem hx₀N hqN
  refine ⟨c, hcN, fun hc => hx₀ ?_, hct⟩
  rw [hxq]
  exact (R ⊔ R').mul_mem hc ((R ⊔ R').inv_mem ((le_sup_left : R ≤ R ⊔ R') hq))
end Frat
end T7G2
end Asc77
end
end CFSG.ClassicalInvolution.T7F25
