module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Zs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53L
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Cent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Sporadic.Th.Max3.Involutions
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem conj_t_mem_Q_or_of_conjugate_R_le {g : G} (hR₂S : conjugate (S ⊓ L) g ≤ S) :
    g⁻¹ * t * g ∈ Q ∨ g⁻¹ * t * g * t ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := H.sec5
  have hD := H.autData
  have hna := H.nonab
  have hR₂N : conjugate (S ⊓ L) g ≤ normalizer (L : Set G) := hR₂S.trans h.S_le
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, g⁻¹ * t * g = t₂ := ⟨_, rfl⟩
  rw [ht₂]
  have ht₂R₂ : t₂ ∈ conjugate (S ⊓ L) g := by
    rw [mem_conjugate_iff, ← ht₂, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
    exact h.tR
  have ht₂S := hR₂S ht₂R₂
  have ht₂Z : ∀ x ∈ conjugate (S ⊓ L) g, t₂ * x = x * t₂ := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := h.tZ _ (mem_inf.mp hx).1
    calc t₂ * x = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [← ht₂]; group
      _ = g⁻¹ * ((g * x * g⁻¹) * t) * g := by rw [h1]
      _ = x * t₂ := by rw [← ht₂]; group
  by_cases hR₂Q : conjugate (S ⊓ L) g ⊓ Q = ⊥
  ·
    have hR₂C : conjugate (S ⊓ L) g ⊓ coreActionKernel L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [← hR₂Q]
      refine mem_inf.mpr ⟨(mem_inf.mp hx).1, ?_⟩
      rw [← h.inf_coreActionKernel]
      exact mem_inf.mpr ⟨hR₂S (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
    have hnaR : ∃ a ∈ (h.Rbar ε : Subgroup 𝕊), ∃ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b ≠ b * a := by
      obtain ⟨a, ha, b, hb, hab⟩ := hna
      exact ⟨_, h.psi_mem_Rbar ε ha, _, h.psi_mem_Rbar ε hb,
        fun h1 => hab ((h.psi_comm_iff ε ha hb).mp h1)⟩
    have hX : (h.Rbar ε : Subgroup 𝕊).map (MulAut.conj : 𝕊 →* MulAut 𝕊) ≤ actImage L ε S := by
      rintro _ ⟨ρ, hρ, rfl⟩
      obtain ⟨r, hrR, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
      have h1 : MulAut.conj (psi L ε r) = actG L ε r := (actG_of_mem_self ε r.2).symm
      rw [h1]
      exact actG_mem_actImage ε h.S_le (mem_inf.mp hrR).1
    obtain ⟨e₁⟩ := nonempty_actImage_equiv ε hR₂N hR₂C
    obtain ⟨e₂⟩ := nonempty_conjugate_equiv (S ⊓ L) g
    obtain ⟨e₃⟩ := h.nonempty_Rbar_equiv ε
    have hcR₁ : actG L ε t₂ ∈ actImage L ε (conjugate (S ⊓ L) g) :=
      actG_mem_actImage ε hR₂N ht₂R₂
    have hcZ : ∀ d ∈ actImage L ε (conjugate (S ⊓ L) g), actG L ε t₂ * d = d * actG L ε t₂ := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := (mem_actImage ε hR₂N).mp hd
      rw [← actG_mul ε (hR₂N ht₂R₂) (hR₂N hx), ← actG_mul ε (hR₂N hx) (hR₂N ht₂R₂), ht₂Z x hx]
    obtain ⟨ρ, hρ, hρZ, hρc⟩ := hD.center_le (h.Rbar ε) hnaR (actImage L ε S)
      (isPGroup_actImage ε h.isPGroup_S) hX _ (actImage_mono ε hR₂S)
      ⟨(e₁.trans e₂).trans e₃.symm⟩ _ hcR₁ hcZ
    obtain ⟨r₀, hr₀R, rfl⟩ := (h.mem_Rbar_iff ε).mp hρ
    have hr₀Z : ∀ s ∈ S ⊓ L, (r₀ : G) * s = s * r₀ := fun s hs =>
      (h.psi_comm_iff ε hr₀R hs).mp (hρZ _ (h.psi_mem_Rbar ε hs))
    have hr₀S := (mem_inf.mp hr₀R).1
    have hq : t₂ * (r₀ : G)⁻¹ ∈ Q := by
      rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem ht₂S (inv_mem hr₀S)),
        actG_mul ε (h.S_le ht₂S) (h.S_le (inv_mem hr₀S)), actG_inv ε (h.S_le hr₀S), hρc,
        actG_of_mem_self ε r₀.2, mul_inv_cancel]
    rcases h.center_R hna hr₀R hr₀Z with h2 | h2
    · left; rwa [h2, inv_one, mul_one] at hq
    · right; rwa [h2, inv_eq_of_mul_eq_one_right H.mul_self_t] at hq
  ·
    left
    have hP : IsPGroup 2 (conjugate (S ⊓ L) g) := h.R_sylow.isPGroup.map _
    have hN : conjugate (S ⊓ L) g ≤
        normalizer ((conjugate (S ⊓ L) g ⊓ Q : Subgroup G) : Set G) := by
      intro x hx
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp hy).1) (inv_mem hx),
          h.conj_mem_Q (hR₂S hx) (mem_inf.mp hy).2⟩
      · intro hy
        have h1 := mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hx) (mem_inf.mp hy).1)
          (inv_mem (inv_mem hx)), h.conj_mem_Q (inv_mem (hR₂S hx)) (mem_inf.mp hy).2⟩
        rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
    obtain ⟨e, he, he2, heZ⟩ := exists_involution_center hP inf_le_left hN hR₂Q
    have hgeR : g * e * g⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp (mem_inf.mp he).1
    have hgeZ : ∀ r ∈ S ⊓ L, g * e * g⁻¹ * r = r * (g * e * g⁻¹) := by
      intro r hr
      have h1 := heZ (g⁻¹ * r * g) (conj_inv_mem_conjugate hr)
      calc g * e * g⁻¹ * r = g * (e * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * e) * g⁻¹ := by rw [h1]
        _ = r * (g * e * g⁻¹) := by group
    rcases h.center_R hna hgeR (fun r hr => hgeZ r hr) with h1 | h1
    · exfalso
      have : e = 1 := by
        calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at he2
      omega
    · have : e = t₂ := by
        rw [← ht₂]
        calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
          _ = g⁻¹ * t * g := by rw [h1]
      rw [← this]
      exact (mem_inf.mp he).2

theorem conj_z_eq_of_conjugate_Rs_le {g : G}
    (hle : conjugate (conjugate (S ⊓ L) s) g ≤ S) : g⁻¹ * z * g = z ∨ g⁻¹ * z * g = t := by
  set y := g⁻¹ * z * g with hy
  have h1 : conjugate (S ⊓ L) (s * g) ≤ S := by
    intro x hx
    apply hle
    rw [mem_conjugate_iff, mem_conjugate_iff]
    rw [mem_conjugate_iff] at hx
    rwa [show s * (g * x * g⁻¹) * s⁻¹ = s * g * x * (s * g)⁻¹ by group]
  have hA := H.conj_t_mem_Q_or_of_conjugate_R_le h1
  rw [show (s * g)⁻¹ * t * (s * g) = g⁻¹ * (s⁻¹ * t * s) * g by group, H.conj_s_inv_t] at hA
  have h2 : conjugate (S ⊓ L) (s * g * s⁻¹) ≤ S := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h3 : s⁻¹ * x * s ∈ conjugate (conjugate (S ⊓ L) s) g := by
      rw [mem_conjugate_iff, mem_conjugate_iff]
      rwa [show s * (g * (s⁻¹ * x * s) * g⁻¹) * s⁻¹ = s * g * s⁻¹ * x * (s * g * s⁻¹)⁻¹ by
        group]
    have h4 := hle h3
    have h5 := conj_mem_of_mem_normalizer (inv_mem H.s_mem_normalizer) h4
    rwa [inv_inv, show s * (s⁻¹ * x * s) * s⁻¹ = x by group] at h5
  have hB := H.conj_t_mem_Q_or_of_conjugate_R_le h2
  rw [show (s * g * s⁻¹)⁻¹ * t * (s * g * s⁻¹) = s * (g⁻¹ * (s⁻¹ * t * s) * g) * s⁻¹ by group,
    H.conj_s_inv_t] at hB
  have hB' : y ∈ conjugate Q s ∨ y * z ∈ conjugate Q s := by
    rcases hB with hB | hB
    · left; exact mem_conjugate_iff.mpr hB
    · right
      rw [mem_conjugate_iff]
      rwa [show s * (y * z) * s⁻¹ = s * y * s⁻¹ * (s * z * s⁻¹) by group, H.conj_s_z]
  have hzQ := H.sec5.zQ
  have htQs : t ∈ conjugate Q s := H.R_le_conjugate_Q H.sec5.tR
  have hQQ : ∀ x, x ∈ Q → x ∈ conjugate Q s → x = 1 := fun x h1 h2 => by
    have h3 : x ∈ Q ⊓ conjugate Q s := mem_inf.mpr ⟨h1, h2⟩
    rwa [H.QQs] at h3
  have hy1 : y ≠ 1 := fun e => H.z_ne_one (by
    calc z = g * y * g⁻¹ := by rw [hy]; group
      _ = 1 := by rw [e]; group)
  rcases hA with hA | hA <;> rcases hB' with hB' | hB'
  · exact absurd (hQQ y hA hB') hy1
  · left
    have h3 := hQQ (y * z) (mul_mem hA hzQ) hB'
    calc y = y * z * z := by rw [mul_assoc, H.mul_self_z, mul_one]
      _ = z := by rw [h3, one_mul]
  · right
    have h3 := hQQ (y * t) hA (mul_mem hB' htQs)
    calc y = y * t * t := by rw [mul_assoc, H.mul_self_t, mul_one]
      _ = t := by rw [h3, one_mul]
  · exfalso
    have h3 : y * t * z ∈ Q := mul_mem hA hzQ
    have h4 : y * t * z ∈ conjugate Q s := by
      rw [show y * t * z = y * z * t by rw [mul_assoc, ← H.z_mul_t, ← mul_assoc]]
      exact mul_mem hB' htQs
    have h5 := hQQ _ h3 h4
    apply H.conj_z_ne_d g
    rw [← hy]
    calc y = y * t * z * (z * t) := by
          rw [show y * t * z * (z * t) = y * t * (z * z) * t by group, H.mul_self_z, mul_one,
            mul_assoc, H.mul_self_t, mul_one]
      _ = z * t := by rw [h5, one_mul]

theorem conjugate_Rs_le_S {g : G} (hle : conjugate (conjugate (S ⊓ L) s) g ≤ T) :
    conjugate (conjugate (S ⊓ L) s) g ≤ S := by
  obtain ⟨ρ, b, j, hD, -⟩ := H.exists_dihData_Rs
  have hinv : ∀ r ∈ conjugate (S ⊓ L) s, r * r = 1 → g⁻¹ * r * g ∈ S := by
    intro r hr hr2
    by_cases hr1 : r = 1
    · rw [hr1, mul_one, inv_mul_cancel]; exact one_mem S
    have h1 : s * r * s⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp hr
    have h2 : orderOf (s * r * s⁻¹) = 2 := by
      rw [orderOf_conj']
      exact orderOf_eq_prime (by rw [sq]; exact hr2) hr1
    obtain ⟨k, -, hk⟩ := H.sec5.exists_conj_t h1 h2
    have h3 : g⁻¹ * r * g = (s * k⁻¹ * s * g)⁻¹ * z * (s * k⁻¹ * s * g) := by
      have h4 : r = s⁻¹ * (k * t * k⁻¹) * s := by rw [← hk]; group
      rw [h4, ← H.conj_s_inv_z]; group
    have h5 : g⁻¹ * r * g ∈ T := hle (conj_inv_mem_conjugate hr)
    rw [h3] at h5 ⊢
    exact H.l512 _ h5
  intro x hx
  have hgx : g * x * g⁻¹ ∈ conjugate (S ⊓ L) s := mem_conjugate_iff.mp hx
  obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, he⟩ := hD.prod_inv _ hgx
  have hx' : x = (g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g) := by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (c₁ * c₂) * g := by rw [he]
      _ = (g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g) := by group
  rw [hx']
  exact mul_mem (hinv c₁ hc₁ h1) (hinv c₂ hc₂ h2)

end Hyp

end CFSG.ComponentClassification.Sol78.F514
