module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51D
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {𝕊 : Type} [Group 𝕊]

omit [Finite G] in
theorem actImage_mono {A : Subgroup G} (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊) {P P' : Subgroup G}
    (hPP' : P ≤ P') : actImage A ε P ≤ actImage A ε P' :=
  map_mono fun _ hp => mem_subgroupOf.mpr (hPP' (mem_subgroupOf.mp hp))

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) {Lin : Subgroup (MulAut 𝕊)}

@[expose] noncomputable def fixR : Subgroup G where
  carrier := {y | y ∈ normalizer (L : Set G) ∧
    ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε y ρ = ρ}
  one_mem' := ⟨one_mem _, fun ρ _ => by rw [actG_one]; rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun ρ hρ => by
    rw [actG_mul ε ha.1 hb.1, MulAut.mul_apply, hb.2 ρ hρ, ha.2 ρ hρ]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun ρ hρ => by
    calc actG L ε a⁻¹ ρ = (actG L ε a)⁻¹ (actG L ε a ρ) := by
          rw [actG_inv ε ha.1, ha.2 ρ hρ]
      _ = ρ := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]⟩

include h

theorem isSylowOf_fixR (hD : Foote5AutData 𝕊 Lin) {P : Subgroup G} (hPH : P ≤ h.fixR ε)
    (hP2 : IsPGroup 2 P) (hcard : 4 * Nat.card Q ≤ Nat.card P) : IsSylowOf 2 P (h.fixR ε) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_twoPart_le hP2 hPH ?_
  obtain ⟨P₀, hP₀⟩ := exists_isSylowOf 2 (h.fixR ε)
  rw [twoPart, ← hP₀.card_eq]
  have hP₀N : P₀ ≤ normalizer (L : Set G) := fun y hy => (hP₀.le hy).1
  rw [card_eq_card_inf_mul_card_actImage ε hP₀N]
  have h1 : Nat.card ↥(P₀ ⊓ coreActionKernel L) ≤ Nat.card Q := by
    rw [h.sylQ.card_eq]
    exact card_le_twoPart (hP₀.isPGroup.to_le inf_le_left) inf_le_right
  have h2 : Nat.card (actImage L ε P₀) ≤ 4 :=
    (hD.centralizer_sylow (h.Rbar ε) _ (isPGroup_actImage ε hP₀.isPGroup) fun α hα ρ hρ => by
      obtain ⟨p, hp, rfl⟩ := (mem_actImage ε hP₀N).mp hα
      exact (hP₀.le hp).2 ρ hρ).2
  calc _ ≤ Nat.card Q * 4 := Nat.mul_le_mul h1 h2
    _ = 4 * Nat.card Q := mul_comm _ _
    _ ≤ Nat.card P := hcard

variable (hD : Foote5AutData 𝕊 Lin)
  (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {x : G} (hx : x ∈ normalizer (S : Set G))
  (hxQ : x ∉ normalizer (Q : Set G)) (hodd : Odd (orderOf x)) (hxt : x * t * x⁻¹ = t)
include hD hna hx hxQ hodd hxt

theorem isSylowOf_QQx_fixR : IsSylowOf 2 (Q ⊔ conjugate Q x) (h.fixR ε) := by
  have hQxS := h.conjugate_Q_le hx
  have hVS : Q ⊔ conjugate Q x ≤ S := sup_le h.QS hQxS
  have hVH : Q ⊔ conjugate Q x ≤ h.fixR ε := by
    refine sup_le (fun q hq => ⟨h.S_le (h.QS hq), fun ρ _ => ?_⟩) (fun p hp => ⟨h.S_le (hQxS hp),
      fun ρ hρ => h.fix_actImage_conjugate_Q ε hD hna hx hxQ hodd hxt _
        (actG_mem_actImage ε (hQxS.trans h.S_le) hp) ρ hρ⟩)
    rw [(h.actG_eq_one_iff_mem_Q ε (h.QS hq)).mpr hq]
    rfl
  refine h.isSylowOf_fixR ε hD hVH (h.isPGroup_S.to_le hVS) ?_
  have hVN : Q ⊔ conjugate Q x ≤ normalizer (L : Set G) := hVS.trans h.S_le
  rw [card_eq_card_inf_mul_card_actImage ε hVN]
  have h1 : Nat.card Q ≤ Nat.card ↥((Q ⊔ conjugate Q x) ⊓ coreActionKernel L) :=
    card_le_of_le (le_inf le_sup_left h.Q_le)
  have h2 : 4 ≤ Nat.card (actImage L ε (Q ⊔ conjugate Q x)) := by
    rw [← (h.card_Q_eq_four ε hD hna hx hxQ hodd hxt).2]
    exact card_le_of_le (actImage_mono ε le_sup_right)
  calc 4 * Nat.card Q ≤ Nat.card ↥((Q ⊔ conjugate Q x) ⊓ coreActionKernel L) * 4 := by
        rw [mul_comm]; exact Nat.mul_le_mul h1 le_rfl
    _ ≤ _ := Nat.mul_le_mul le_rfl h2

include ε in
theorem exists_conj_t_center_not_mem_R (hB4 : GoldschmidtCorB4) (hST : IsSylowOf 2 S ⊤) :
    ∃ g : G, (∀ s ∈ S, s * (g⁻¹ * t * g) = g⁻¹ * t * g * s) ∧ g⁻¹ * t * g ∉ S ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hgS, hgR⟩ := h.exists_conj_t_not_mem_R hB4 hST
  have ht2 : t * t = 1 := by rw [← sq, ← h.t2]; exact pow_orderOf_eq_one t
  have hy2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    rw [show g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht2]
    group
  have hyN := h.S_le hgS
  have hsq : actG L ε (g⁻¹ * t * g) * actG L ε (g⁻¹ * t * g) = 1 := by
    rw [← actG_mul ε hyN hyN, hy2, actG_one]
  by_cases hinn : actG L ε (g⁻¹ * t * g) ∈ innAut5 𝕊
  · obtain ⟨q, hq, r, hr, hqr⟩ := h.exists_mul_of_inner ε hgS hinn
    have hqZ : ∀ s ∈ S, s * q = q * s := fun s hs =>
      h.Q_le_center ε hD hna hx hxQ hodd hxt hq hs
    by_cases hr1 : r = 1
    · refine ⟨g, fun s hs => ?_, hgR⟩
      rw [hqr, hr1, mul_one]
      exact hqZ s hs
    have hcomm := h.commute_Q_R hq hr
    have hqq : q * q = 1 := by
      have h1 : q * q * (r * r) = 1 := by
        rw [← hy2, hqr, show q * r * (q * r) = q * (r * q) * r by group, ← hcomm]
        group
      have h2 : q * q ∈ Q ⊓ L := by
        refine mem_inf.mpr ⟨mul_mem hq hq, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (mul_mem (mem_inf.mp hr).2 (mem_inf.mp hr).2)
      rw [h.Q_inf_L, mem_bot] at h2
      exact h2
    have hrr : r * r = 1 := by
      rw [← hy2, hqr, show q * r * (q * r) = q * (r * q) * r by group, ← hcomm,
        show q * (q * r) * r = q * q * (r * r) by group, hqq, one_mul]
    have hq1 : q ≠ 1 := fun h1 => hgR (by rw [hqr, h1, one_mul]; exact hr)
    have hq2 : orderOf q = 2 := orderOf_eq_prime (by rw [sq]; exact hqq) hq1
    have hr2 : orderOf r = 2 := orderOf_eq_prime (by rw [sq]; exact hrr) hr1
    have hq' := h.repoint hq hq2 hqZ
    have hRq := h.inf_footeF_eq hq hq2 hqZ
    obtain ⟨k, hkF, hk⟩ := hq'.exists_conj_t (hRq.symm ▸ hr) hr2
    have hkq : k * q = q * k := mem_centralizer_singleton_iff.mp (hq'.zL.2.1 hkF)
    refine ⟨g * k, fun s hs => ?_, ?_⟩
    · rw [show (g * k)⁻¹ * t * (g * k) = k⁻¹ * (g⁻¹ * t * g) * k by group, hqr,
        show k⁻¹ * (q * r) * k = (k⁻¹ * q * k) * (k⁻¹ * r * k) by group, hk,
        show k⁻¹ * q * k = q by rw [mul_assoc, ← hkq]; group]
      rw [show s * (q * t) = (s * q) * t by group, hqZ s hs, mul_assoc, h.tZ s hs]
      group
    · rw [show (g * k)⁻¹ * t * (g * k) = k⁻¹ * (g⁻¹ * t * g) * k by group, hqr,
        show k⁻¹ * (q * r) * k = (k⁻¹ * q * k) * (k⁻¹ * r * k) by group, hk,
        show k⁻¹ * q * k = q by rw [mul_assoc, ← hkq]; group]
      intro hqt
      apply hq1
      have h1 : q ∈ Q ⊓ L := mem_inf.mpr ⟨hq, by
        rw [show q = q * t * t⁻¹ by group]
        exact mul_mem (mem_inf.mp hqt).2 (inv_mem h.tL)⟩
      rwa [h.Q_inf_L, mem_bot] at h1
  · by_cases hlin : actG L ε (g⁻¹ * t * g) ∈ Lin
    · exact absurd (h.mem_innAut_of_mem_lin ε hD hna hx hxQ hodd hxt hgS hlin hsq) hinn
    obtain ⟨γ, hγ⟩ := hD.conj_centralizer (h.Rbar ε) _ hlin hsq
    obtain ⟨l, rfl⟩ := psi_surjective ε γ
    have hlN : (l : G) ∈ normalizer (L : Set G) := le_normalizer l.2
    set y₁ := (l : G) * (g⁻¹ * t * g) * (l : G)⁻¹ with hy₁
    have hy₁N : y₁ ∈ normalizer (L : Set G) := mul_mem (mul_mem hlN hyN) (inv_mem hlN)
    have hact₁ : actG L ε y₁ = MulAut.conj (psi L ε l) * actG L ε (g⁻¹ * t * g) *
        (MulAut.conj (psi L ε l))⁻¹ := by
      rw [hy₁, actG_mul ε (mul_mem hlN hyN) (inv_mem hlN), actG_mul ε hlN hyN,
        actG_inv ε hlN, actG_of_mem_self ε l.2]
    have hy₁H : y₁ ∈ h.fixR ε := ⟨hy₁N, fun ρ hρ => by rw [hact₁]; exact hγ ρ hρ⟩
    have hy₁2 : IsPGroup 2 (zpowers y₁) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, hy₁, orderOf_conj']
      exact orderOf_eq_prime (by rw [sq]; exact hy2) (fun h1 => hgR (by rw [h1]; exact one_mem _))
    obtain ⟨k, hkH, hk⟩ := exists_conj_le_of_isSylowOf
      (h.isSylowOf_QQx_fixR ε hD hna hx hxQ hodd hxt) (zpowers_le.mpr hy₁H) hy₁2
    have hkV := hk y₁ (mem_zpowers y₁)
    have hVC : Q ⊔ conjugate Q x ≤ centralizer (S : Set G) := sup_le
      (fun q hq => mem_centralizer_iff.mpr fun s hs => h.Q_le_center ε hD hna hx hxQ hodd hxt hq hs)
      (fun p hp => mem_centralizer_iff.mpr fun s hs =>
        h.conjugate_Q_le_center ε hD hna hx hxQ hodd hxt hp hs)
    have heq : k⁻¹ * y₁ * k = ((l : G)⁻¹ * k)⁻¹ * (g⁻¹ * t * g) * ((l : G)⁻¹ * k) := by
      rw [hy₁]; group
    refine ⟨g * ((l : G)⁻¹ * k), fun s hs => ?_, ?_⟩
    · rw [show (g * ((l : G)⁻¹ * k))⁻¹ * t * (g * ((l : G)⁻¹ * k)) = k⁻¹ * y₁ * k by
        rw [heq]; group]
      exact mem_centralizer_iff.mp (hVC hkV) s hs
    · rw [show (g * ((l : G)⁻¹ * k))⁻¹ * t * (g * ((l : G)⁻¹ * k)) = k⁻¹ * y₁ * k by
        rw [heq]; group]
      intro hR
      apply hlin
      have hkN := hkH.1
      have h1 : actG L ε (k⁻¹ * y₁ * k) ∈ Lin := by
        rw [actG_of_mem_self ε (mem_inf.mp hR).2]
        exact hD.inn_le ⟨_, rfl⟩
      have h2 : actG L ε y₁ ∈ Lin := by
        have h3 := hD.normal.conj_mem _ h1 (actG L ε k)
        rwa [actG_mul ε (mul_mem (inv_mem hkN) hy₁N) hkN, actG_mul ε (inv_mem hkN) hy₁N,
          actG_inv ε hkN, show actG L ε k * ((actG L ε k)⁻¹ * actG L ε y₁ * actG L ε k) *
            (actG L ε k)⁻¹ = actG L ε y₁ by group] at h3
      have h3 := hD.normal.conj_mem _ h2 (MulAut.conj (psi L ε l))⁻¹
      rwa [hact₁, show (MulAut.conj (psi L ε l))⁻¹ * (MulAut.conj (psi L ε l) *
        actG L ε (g⁻¹ * t * g) * (MulAut.conj (psi L ε l))⁻¹) * (MulAut.conj (psi L ε l))⁻¹⁻¹ =
        actG L ε (g⁻¹ * t * g) by group] at h3

end Sec5

end CFSG.ComponentClassification.Foote5
