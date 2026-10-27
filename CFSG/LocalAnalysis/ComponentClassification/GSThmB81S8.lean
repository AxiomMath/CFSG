module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7a

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

omit [Finite H] in
theorem _root_.CFSG.ComponentClassification.GSThmB.Eight.conj_mul_distrib_right (n x y : H) :
    n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group

theorem conj_c_asigma : h.x * d.g * (h.a * d.sigma) * (h.x * d.g)⁻¹ = d.b := by
  rw [← conj_b]; group

theorem conj_c_a (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    h.x * d.g * h.a * (h.x * d.g)⁻¹ = d.tau := by
  have h1 : d.g * h.a * d.g⁻¹ = h.a * d.tau := by
    have h2 : d.g⁻¹ * (h.a * d.tau) * d.g = h.a := by
      rw [Eight.conj_mul_distrib, d.a_g, d.tau_g, mul_assoc, d.tau_sq, mul_one]
    calc d.g * h.a * d.g⁻¹ = d.g * (d.g⁻¹ * (h.a * d.tau) * d.g) * d.g⁻¹ := by rw [h2]
      _ = h.a * d.tau := by group
  have h2 : h.x * (h.a * d.tau) * h.x⁻¹ = d.tau := by
    rw [← d.tau_x hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F]; group
  rw [show h.x * d.g * h.a * (h.x * d.g)⁻¹ = h.x * (d.g * h.a * d.g⁻¹) * h.x⁻¹ by group, h1, h2]

theorem conj_c_sigma (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (F : d.Facts) :
    h.x * d.g * d.sigma * (h.x * d.g)⁻¹ = d.sigma := by
  have haa : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
  calc h.x * d.g * d.sigma * (h.x * d.g)⁻¹ =
        h.x * d.g * (h.a * (h.a * d.sigma)) * (h.x * d.g)⁻¹ := by
        rw [← mul_assoc h.a h.a d.sigma, haa, one_mul]
    _ = (h.x * d.g * h.a * (h.x * d.g)⁻¹) * (h.x * d.g * (h.a * d.sigma) * (h.x * d.g)⁻¹) :=
        Eight.conj_mul_distrib_right (h.x * d.g) h.a (h.a * d.sigma)
    _ = d.tau * d.b := by rw [conj_c_a hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F, conj_c_asigma]

theorem centralizer_asigma_le_normalizer_L :
    centralizer ({h.a * d.sigma} : Set H) ≤ normalizer (conjugate h.K (h.x * d.g) : Set H) := by
  intro w hw
  set c := h.x * d.g with hc
  have hw' : c * w * c⁻¹ * d.b = d.b * (c * w * c⁻¹) := by
    have h1 := mem_centralizer_singleton_iff.mp hw
    rw [← conj_c_asigma, ← hc]
    calc c * w * c⁻¹ * (c * (h.a * d.sigma) * c⁻¹) = c * (w * (h.a * d.sigma)) * c⁻¹ := by
          group
      _ = c * ((h.a * d.sigma) * w) * c⁻¹ := by rw [h1]
      _ = c * (h.a * d.sigma) * c⁻¹ * (c * w * c⁻¹) := by group
  have hcomm : ∀ k : ℤ, c * w * c⁻¹ * d.b ^ k = d.b ^ k * (c * w * c⁻¹) := fun k =>
    (Commute.zpow_right (show Commute (c * w * c⁻¹) d.b from hw') k).eq
  have hwB : c * w * c⁻¹ ∈ normalizer (h.B : Set H) := by
    rw [d.B_eq, mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [hcomm k, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers _) k
    · intro hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
      have hyk : y = d.b ^ k := by
        calc y = (c * w * c⁻¹)⁻¹ * (c * w * c⁻¹ * y * (c * w * c⁻¹)⁻¹) * (c * w * c⁻¹) := by
              group
          _ = (c * w * c⁻¹)⁻¹ * d.b ^ k * (c * w * c⁻¹) := by rw [hk]
          _ = d.b ^ k := by rw [mul_assoc, ← hcomm k, inv_mul_cancel_left]
      rw [hyk]
      exact zpow_mem (mem_zpowers _) k
  have hwK : c * w * c⁻¹ ∈ normalizer (h.K : Set H) := by
    rw [← H₁.kloc.V_eq_K]
    exact mem_normalizer_layerIn hwB
  refine Eight.mem_normalizer_of_conj_mem fun y hy => ?_
  rw [mem_conjugate_iff] at hy ⊢
  have h1 := (mem_normalizer_iff.mp (inv_mem hwK) _).mp hy
  rwa [show (c * w * c⁻¹)⁻¹ * (c * y * c⁻¹) * (c * w * c⁻¹)⁻¹⁻¹ = c * (w⁻¹ * y * w) * c⁻¹ by
    group] at h1

noncomputable def L_bar_equiv (c : H) :
    ↥(conjugate h.K c) ⧸ pPrimeCore 2 ↥(conjugate h.K c) ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K := by
  let e : ↥h.K ≃* ↥(conjugate h.K c) :=
    h.K.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective
  exact (QuotientGroup.congr (pPrimeCore 2 ↥h.K) (pPrimeCore 2 ↥(conjugate h.K c)) e
    (pPrimeCore_map_iso 2 e)).symm

section Eight

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
  (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
include hv I F

omit F h3 in
theorem E32_le_F {A : Subgroup H} (hAU : A ≤ h.U81 v) (hA2 : ∀ e ∈ A, e * e = 1)
    (hA32 : Nat.card A = 32) : A ≤ h.F32 := by
  rw [← JeN_U_eq hv I.rk]
  exact Eight.le_JeN hAU hA2 hA32

omit h3 in
theorem sigma_mem_E32 {A : Subgroup H} (hAU : A ≤ h.U81 v) (hA2 : ∀ e ∈ A, e * e = 1)
    (hA32 : Nat.card A = 32) : d.sigma ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAF := E32_le_F hv I hAU hA2 hA32
  have hAS : A ≤ h.S := hAF.trans h.F32_le_S
  by_contra hσA
  have hσF := d.F32_le_centralizer_sigma I.rk I.j I.c I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F
  have hc : ∀ x ∈ A, ∀ y ∈ zpowers d.sigma, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (mem_centralizer_singleton_iff.mp (hσF (hAF hx)))
  have hdisj : A ⊓ zpowers d.sigma = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self (mem_inf.mp hy).2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ (mem_inf.mp hy).1) hσA
  have hσ1 : d.sigma ≠ 1 := fun h1 => hσA (h1 ▸ one_mem _)
  have hcσ : Nat.card (zpowers d.sigma) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact d.sigma_mul_self) hσ1
  have hcard := Seven.card_sup_of_commute hc hdisj
  rw [hA32, hcσ] at hcard
  have hsq : ∀ w ∈ A ⊔ zpowers d.sigma, w * w = 1 := by
    refine Seven.sup_sq_eq_one hA2 (fun w hw => ?_) hc
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hw with rfl | rfl
    · rw [one_mul]
    · exact d.sigma_mul_self
  have := d.card_elem_le I.rk (sup_le hAS (zpowers_le.mpr d.sigma_mem_S)) hsq
  omega

include h3 in
theorem exists_mem_E32_P {A : Subgroup H} (hAU : A ≤ h.U81 v) (hA2 : ∀ e ∈ A, e * e = 1)
    (hA32 : Nat.card A = 32) : ∃ t ∈ A ⊓ h.P, t ≠ 1 ∧ t ≠ h.a := by
  have hAF := E32_le_F hv I hAU hA2 hA32
  have hAS : A ≤ h.S := hAF.trans h.F32_le_S
  have hσA := sigma_mem_E32 hv I F hAU hA2 hA32
  have hsplit := d.eq_sup_of_card_eq I.rk I.j I.c I.cf1 I.cf2 F hAS hA2 hA32
  have hcD : ∀ x ∈ A ⊓ h.D, ∀ y ∈ A ⊓ d.R0, x * y = y * x := fun x hx y hy =>
    d.D_comm_R0 F x (mem_inf.mp hx).2 y (mem_inf.mp hy).2
  have hdD : (A ⊓ h.D) ⊓ (A ⊓ d.R0) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf inf_le_right inf_le_right).trans (d.D_inf_R0 I.cf1 I.cf2 F).le)
  have hcard := Seven.card_sup_of_commute hcD hdD
  rw [← hsplit, hA32] at hcard
  have hD4 := d.card_elem_D I.rk I.cf1 I.cf2 F (inf_le_right : A ⊓ h.D ≤ h.D)
    (fun x hx => hA2 x (mem_inf.mp hx).1)
  have hσP : ∀ π ∈ h.P, d.sigma * π = π * d.sigma := fun π hπ => sigma_comm_P I F h3 hπ
  have hle : A ⊓ d.R0 ≤ (A ⊓ h.P) ⊔ zpowers d.sigma := by
    intro r hr
    obtain ⟨π, hπ, hr' | hr'⟩ := d.mem_R0_cases (mem_inf.mp hr).2
    · subst hr'
      exact mem_sup_left (mem_inf.mpr ⟨(mem_inf.mp hr).1, hπ⟩)
    · have hπA : π ∈ A := by
        have := mul_mem (mem_inf.mp hr).1 (inv_mem hσA)
        rwa [hr', mul_inv_cancel_right] at this
      rw [hr']
      exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hπA, hπ⟩)) (mem_sup_right (mem_zpowers _))
  have hc2 : ∀ x ∈ A ⊓ h.P, ∀ y ∈ zpowers d.sigma, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_of_mem_zpowers_of_mul_self d.sigma_mul_self hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hσP x (mem_inf.mp hx).2).symm
  have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc2).1
  have hσ2 : Nat.card (zpowers d.sigma) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact d.sigma_mul_self)
  have h2 : Nat.card ↥((A ⊓ h.P) ⊔ zpowers d.sigma) ≤ Nat.card ↥(A ⊓ h.P) * 2 := by
    have := Nat.le_mul_of_pos_right (Nat.card ↥((A ⊓ h.P) ⊔ zpowers d.sigma))
      (Nat.card_pos (α := ↥((A ⊓ h.P) ⊓ zpowers d.sigma)))
    rw [h1] at this
    exact this.trans (Nat.mul_le_mul_left _ hσ2)
  have h3' := Subgroup.card_le_of_le hle
  have h4 : 4 ≤ Nat.card ↥(A ⊓ h.P) := by
    have := Nat.mul_le_mul_right (Nat.card ↥(A ⊓ d.R0)) hD4
    omega
  by_contra hno
  push Not at hno
  have hle2 : A ⊓ h.P ≤ zpowers h.a := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact one_mem _
    · rw [hno t ht ht1]; exact mem_zpowers _
  have h5 := Subgroup.card_le_of_le hle2
  rw [Nat.card_zpowers, h.orderOf_a] at h5
  omega

include h3 in
theorem isSylowIn_R (h6 : ∃ c : H, c⁻¹ * (h.a * d.sigma) * c = d.z * d.sigma) :
    Seven.IsSylowIn (h.U81 v ⊓ centralizer ({h.a * d.sigma} : Set H))
      (centralizer ({h.a * d.sigma} : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({h.a * d.sigma} : Set H) with hC
  set R := h.U81 v ⊓ C with hR
  have hRC : R ≤ C := inf_le_right
  have hRP : IsPGroup 2 R := (isPGroup_U hv).to_le inf_le_left
  have haσZ : h.a * d.sigma ∈ h.ZF32 := mul_mem (a_mem_ZF I F) (sigma_mem_ZF I F)
  obtain ⟨y₂, hy₂U, hy₂⟩ : ∃ y ∈ h.U81 v, y⁻¹ * (h.a * d.sigma) * y = d.z * d.sigma := by
    obtain ⟨c₂, hc₂⟩ := h6
    have hzσZ : d.z * d.sigma ∈ h.ZF32 := mul_mem (z_mem_ZF I F) (sigma_mem_ZF I F)
    obtain ⟨n₂, hn₂N, hn₂⟩ := exists_normalizer_conj hv I F haσZ (hc₂ ▸ hzσZ)
    rw [hc₂] at hn₂
    have hne2 : d.z * d.sigma ≠ h.a * d.sigma := fun h1 => d.z_ne_a (mul_right_cancel h1)
    exact exists_U_conj_of_orbit hv I F hne2 ⟨n₂, hn₂N, hn₂⟩
      (fun m hm => conj_asigma_cases hv I F h3 hm)
  have hFC : h.F32 ≤ C := fun f hf => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (mem_inf.mp haσZ).2 f hf)
  obtain ⟨Tsyl, hTsyl⟩ := isSylow_U hv I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F
  have key : ∀ T : Subgroup H, IsPGroup 2 T → h.F32 ≤ T → T ≤ C → Nat.card T ≤ Nat.card R := by
    intro T hT2 hFT hTC
    obtain ⟨U', hTU'⟩ := hT2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Tsyl U'
    have hmem : ∀ u ∈ (U' : Subgroup H), g⁻¹ * u * g ∈ h.U81 v := by
      intro u hu
      rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hu
      rw [← hTsyl]
      convert hu using 1
      rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
    have hFg : conjugate h.F32 g ≤ h.U81 v := by
      intro f hf
      rw [mem_conjugate_iff] at hf
      have := hmem _ (hTU' (hFT hf))
      rwa [show g⁻¹ * (g * f * g⁻¹) * g = f by group] at this
    have hgF : g ∈ normalizer (h.F32 : Set H) := by
      have heq := weaklyClosed_F hv I g hFg
      refine Eight.mem_normalizer_of_conj_mem fun x hx => ?_
      rw [← heq, mem_conjugate_iff, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
      exact hx
    have hTg : conjugate T g ≤ h.U81 v := fun u hu => by
      rw [mem_conjugate_iff] at hu
      have := hmem _ (hTU' hu)
      rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group] at this
    have hTgC : ∀ u ∈ conjugate T g, u * (g⁻¹ * (h.a * d.sigma) * g) =
        (g⁻¹ * (h.a * d.sigma) * g) * u := by
      intro u hu
      rw [mem_conjugate_iff] at hu
      have h1 := mem_centralizer_singleton_iff.mp (hTC hu)
      calc u * (g⁻¹ * (h.a * d.sigma) * g) = g⁻¹ * ((g * u * g⁻¹) * (h.a * d.sigma)) * g := by
            group
        _ = g⁻¹ * ((h.a * d.sigma) * (g * u * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * (h.a * d.sigma) * g) * u := by group
    have hcardT : Nat.card T = Nat.card (conjugate T g) := (Eight.card_conjugate' T g).symm
    rcases conj_asigma_cases hv I F h3 hgF with h1 | h1 <;> rw [h1] at hTgC
    · rw [hcardT]
      refine Subgroup.card_le_of_le fun u hu => mem_inf.mpr ⟨hTg hu, ?_⟩
      exact mem_centralizer_singleton_iff.mpr (hTgC u hu)
    ·
      have hle : conjugate (conjugate T g) y₂⁻¹ ≤ R := by
        intro u hu
        rw [mem_conjugate_iff, inv_inv] at hu
        refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
        · have h2 := mul_mem (mul_mem hy₂U (hTg hu)) (inv_mem hy₂U)
          rwa [show y₂ * (y₂⁻¹ * u * y₂) * y₂⁻¹ = u by group] at h2
        · have h2 := hTgC _ hu
          have hza : y₂ * (d.z * d.sigma) * y₂⁻¹ = h.a * d.sigma := by
            rw [← hy₂]; group
          calc u * (h.a * d.sigma) = u * (y₂ * (d.z * d.sigma) * y₂⁻¹) := by rw [hza]
            _ = y₂ * ((y₂⁻¹ * u * y₂) * (d.z * d.sigma)) * y₂⁻¹ := by group
            _ = y₂ * ((d.z * d.sigma) * (y₂⁻¹ * u * y₂)) * y₂⁻¹ := by rw [h2]
            _ = y₂ * (d.z * d.sigma) * y₂⁻¹ * u := by group
            _ = h.a * d.sigma * u := by rw [hza]
      rw [hcardT, ← Eight.card_conjugate' (conjugate T g) y₂⁻¹]
      exact Subgroup.card_le_of_le hle
  have hF2 : IsPGroup 2 h.F32 := h.toHyp52.isPGroup_S.to_le h.F32_le_S
  obtain ⟨T₀, hT₀⟩ := (hF2.comap_subtype (K := C)).exists_le_sylow
  have hT₀card : Nat.card (T₀ : Subgroup ↥C) ≤ Nat.card R := by
    have hT₁ := T₀.isPGroup'.map C.subtype
    have h1 := key ((T₀ : Subgroup ↥C).map C.subtype) hT₁ (fun f hf => ⟨⟨f, hFC hf⟩, hT₀ hf, rfl⟩)
      (map_subtype_le _)
    rwa [Subgroup.card_map_of_injective C.subtype_injective] at h1
  obtain ⟨T₂, hT₂⟩ := (hRP.comap_subtype (K := C)).exists_le_sylow
  refine ⟨hRC, T₂, le_antisymm ?_ hT₂⟩
  have hRcard : Nat.card (R.subgroupOf C) = Nat.card R := by
    rw [Six.card_subgroupOf_eq, inf_eq_left.mpr hRC]
  have hT₂card : Nat.card (T₂ : Subgroup ↥C) = Nat.card (T₀ : Subgroup ↥C) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  refine (eq_of_le_of_card_ge hT₂ ?_).symm.le
  change Nat.card ↥(T₂ : Subgroup ↥C) ≤ Nat.card ↥(R.subgroupOf C)
  rw [hRcard, hT₂card]
  exact hT₀card

end Eight

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
