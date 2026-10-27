module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53K
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53I
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53J

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem exists_dihedral_center {a y : G} (ha : a * a = 1) (hy : y * y = 1) (hay : a * y ≠ y * a)
    {k : ℕ} (hk : orderOf (a * y) = 2 ^ k) :
    ∃ x : G, x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ x * a * x⁻¹ = x * x * a ∧
      x * y * x⁻¹ = x * x * y ∧ a * (x * x) = x * x * a ∧ y * (x * x) = x * x * y ∧
      x * x ∈ zpowers (a * y * (a * y)) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hay
    have h0 : 2 ^ k ∣ 2 := by
      have h3 := Nat.pow_dvd_pow 2 (show k ≤ 1 by omega)
      simpa using h3
    have h1 : (a * y) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hk]; exact h0)
    have h2 : (a * y)⁻¹ = a * y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h1)
    rw [mul_inv_rev, hai, hyi] at h2
    exact h2.symm
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, a * y = c := ⟨_, rfl⟩
  rw [hc] at hk ⊢
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    calc y * c * y⁻¹ = y * a := by rw [← hc]; group
      _ = c⁻¹ := by rw [← hc, mul_inv_rev, hai, hyi]
  have hac : a * c * a⁻¹ = c⁻¹ := by
    calc a * c * a⁻¹ = (a * a) * y * a⁻¹ := by rw [← hc]; group
      _ = y * a := by rw [ha, one_mul, hai]
      _ = c⁻¹ := by rw [← hc, mul_inv_rev, hai, hyi]
  obtain ⟨x, hx⟩ : ∃ x, c ^ (2 ^ m) = x := ⟨_, rfl⟩
  have hyx : y * x * y⁻¹ = x⁻¹ := by rw [← hx, ← conj_pow, hyc, inv_pow]
  have hax : a * x * a⁻¹ = x⁻¹ := by rw [← hx, ← conj_pow, hac, inv_pow]
  have hxx : x * x = c ^ (2 ^ (m + 1)) := by
    rw [← hx, ← pow_add, show 2 ^ m + 2 ^ m = 2 ^ (m + 1) by ring]
  have hx1 : x * x ≠ 1 := by
    rw [hxx]
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero) ?_
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hvv : x * x * (x * x) = 1 := by
    rw [hxx, ← pow_add, show 2 ^ (m + 1) + 2 ^ (m + 1) = 2 ^ (m + 2) by ring, ← hk,
      pow_orderOf_eq_one]
  have hv1 : (x * x)⁻¹ = x * x := inv_eq_of_mul_eq_one_right hvv
  refine ⟨x, hx1, hvv, ?_, ?_, ?_, ?_, ?_⟩
  · calc x * a * x⁻¹ = x * (a * x * a⁻¹)⁻¹ * a := by group
      _ = x * x * a := by rw [hax, inv_inv]
  · calc x * y * x⁻¹ = x * (y * x * y⁻¹)⁻¹ * y := by group
      _ = x * x * y := by rw [hyx, inv_inv]
  · have h1 : a * (x * x) * a⁻¹ = x * x := by
      rw [show a * (x * x) * a⁻¹ = (a * x * a⁻¹) * (a * x * a⁻¹) by group, hax, ← mul_inv_rev,
        hv1]
    calc a * (x * x) = a * (x * x) * a⁻¹ * a := by group
      _ = x * x * a := by rw [h1]
  · have h1 : y * (x * x) * y⁻¹ = x * x := by
      rw [show y * (x * x) * y⁻¹ = (y * x * y⁻¹) * (y * x * y⁻¹) by group, hyx, ← mul_inv_rev,
        hv1]
    calc y * (x * x) = y * (x * x) * y⁻¹ * y := by group
      _ = x * x * y := by rw [h1]
  · rw [hxx, show 2 ^ (m + 1) = 2 * 2 ^ m by ring, pow_mul, sq]
    exact npow_mem_zpowers _ _

variable [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem false_of_field_conj (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hss : ∀ y q r : G, IsConj t y → q ∈ Q → r ∈ S ⊓ L → y = q * r → q = 1)
    (hST : IsSylowOf 2 S ⊤) {y : G} (hyS : y ∈ S) (hty : IsConj t y)
    (hylin : actG L ε y ∉ Lin) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hty
    rw [show c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ by group, ht22]; group
  obtain ⟨u, hyu, huR, hulin⟩ := h.exists_conj_centralizer_R ε hD hyS hy2 hylin
  obtain ⟨c, hc⟩ := isConj_iff.mp (hty.trans hyu)
  have hSt : IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    hST.of_le (fun s hs => mem_centralizer_singleton_iff.mpr (h.tZ s hs)) le_top
  have hRc : conjugate (S ⊓ L) c ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 := huR _ hx
    rw [← hc] at h1
    calc x * t = c⁻¹ * ((c * x * c⁻¹) * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * (c * x * c⁻¹)) * c := by rw [h1]
      _ = t * x := by group
  obtain ⟨y₁, hy₁C, hy₁⟩ := exists_conj_le_of_isSylowOf hSt hRc (h.R_sylow.isPGroup.map _)
  obtain ⟨g, hg⟩ : ∃ g, c * y₁ = g := ⟨_, rfl⟩
  have hR₂S : conjugate (S ⊓ L) g ≤ S := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 : y₁ * x * y₁⁻¹ ∈ conjugate (S ⊓ L) c := by
      rw [mem_conjugate_iff, show c * (y₁ * x * y₁⁻¹) * c⁻¹ = g * x * g⁻¹ by rw [← hg]; group]
      exact hx
    have h2 := hy₁ _ h1
    rwa [show y₁⁻¹ * (y₁ * x * y₁⁻¹) * y₁ = x by group] at h2
  have hR₂N : conjugate (S ⊓ L) g ≤ normalizer (L : Set G) := hR₂S.trans h.S_le
  obtain ⟨t₂, ht₂⟩ : ∃ t₂, g⁻¹ * t * g = t₂ := ⟨_, rfl⟩
  have ht₂R₂ : t₂ ∈ conjugate (S ⊓ L) g := by
    rw [mem_conjugate_iff, ← ht₂, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
    exact h.tR
  have ht₂S := hR₂S ht₂R₂
  have htt₂ : IsConj t t₂ := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv, ht₂]⟩
  have ht₂Z : ∀ x ∈ conjugate (S ⊓ L) g, t₂ * x = x * t₂ := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have h1 := h.tZ _ (mem_inf.mp hx).1
    calc t₂ * x = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [← ht₂]; group
      _ = g⁻¹ * ((g * x * g⁻¹) * t) * g := by rw [h1]
      _ = x * t₂ := by rw [← ht₂]; group
  have hR₂Q : conjugate (S ⊓ L) g ⊓ Q = ⊥ := by
    by_contra hne
    obtain ⟨e, he, he2, -⟩ := exists_involution_center (h.isPGroup_Q.to_le inf_le_right) le_rfl
      le_normalizer hne
    have heR : g * e * g⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp (mem_inf.mp he).1
    obtain ⟨k, -, hk⟩ := h.exists_conj_t heR (by rw [orderOf_conj', he2])
    have hte : IsConj t e := isConj_iff.mpr ⟨g⁻¹ * k, by
      rw [show g⁻¹ * k * t * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * t * k⁻¹) * g by group, ← hk]; group⟩
    have h1 := hss e e 1 hte (mem_inf.mp he).2 (one_mem _) (mul_one e).symm
    rw [h1, orderOf_one] at he2
    omega
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
  have h1 := hss t₂ _ _ htt₂ hq hr₀R (by group)
  have ht₂r₀ : t₂ = r₀ := by
    calc t₂ = t₂ * (r₀ : G)⁻¹ * r₀ := by group
      _ = r₀ := by rw [h1, one_mul]
  rcases h.center_R hna hr₀R hr₀Z with h2 | h2
  · apply h.t_ne_one
    calc t = g * t₂ * g⁻¹ := by rw [← ht₂]; group
      _ = 1 := by rw [ht₂r₀, h2]; group
  · rw [h2] at ht₂r₀
    have hy₁t : y₁ * t = t * y₁ := mem_centralizer_singleton_iff.mp hy₁C
    have hct : c * t * c⁻¹ = t := by
      calc c * t * c⁻¹ = c * (y₁ * t * y₁⁻¹) * c⁻¹ := by rw [hy₁t, mul_inv_cancel_right]
        _ = g * t * g⁻¹ := by rw [← hg]; group
        _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [ht₂, ht₂r₀]
        _ = t := by group
    rw [hct] at hc
    apply hulin
    rw [← hc, actG_of_mem_self ε h.tL]
    exact hD.inn_le ⟨_, rfl⟩

end Sec5

end CFSG.ComponentClassification.Foote5
