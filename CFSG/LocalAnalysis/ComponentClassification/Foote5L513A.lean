module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512I
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

theorem conj_mem_innAut5_L513 {𝕊 : Type} [Group 𝕊] (φ : MulAut 𝕊) {α : MulAut 𝕊}
    (hα : α ∈ innAut5 𝕊) : φ * α * φ⁻¹ ∈ innAut5 𝕊 := by
  obtain ⟨a, rfl⟩ := hα
  refine ⟨φ a, ?_⟩
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem conj_t_mem_Qt_L513 (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) {g : G}
    (hR₂S : conjugate (S ⊓ L) g ≤ S) : g⁻¹ * t * g ∈ Q ∨ g⁻¹ * t * g * t ∈ Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hR₂2 : IsPGroup 2 (conjugate (S ⊓ L) g) := h.isPGroup_S.to_le hR₂S
  by_cases hRQ : conjugate (S ⊓ L) g ⊓ Q = ⊥
  ·
    have hR₂C : conjugate (S ⊓ L) g ⊓ coreActionKernel L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [← hRQ]
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
    · left
      rwa [h2, inv_one, mul_one] at hq
    · right
      rwa [h2, inv_eq_of_mul_eq_one_left h.t_mul_self] at hq
  ·
    left
    have hRN : conjugate (S ⊓ L) g ≤ normalizer ((conjugate (S ⊓ L) g ⊓ Q : Subgroup G) :
        Set G) := fun x hx => mem_normalizer_of_conj_mem_L512 fun y hy =>
      mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp hy).1) (inv_mem hx),
        h.conj_mem_Q (hR₂S hx) (mem_inf.mp hy).2⟩
    obtain ⟨e, he, he2, heZ⟩ := exists_involution_center hR₂2 inf_le_left hRN hRQ
    have heR : g * e * g⁻¹ ∈ S ⊓ L := mem_conjugate_iff.mp (mem_inf.mp he).1
    have heZ' : ∀ r ∈ S ⊓ L, g * e * g⁻¹ * r = r * (g * e * g⁻¹) := by
      intro r hr
      have h1 : g⁻¹ * r * g ∈ conjugate (S ⊓ L) g := by
        rw [mem_conjugate_iff, show g * (g⁻¹ * r * g) * g⁻¹ = r by group]
        exact hr
      have h2 := heZ _ h1
      calc g * e * g⁻¹ * r = g * (e * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * e) * g⁻¹ := by rw [h2]
        _ = r * (g * e * g⁻¹) := by group
    rcases h.center_R hna heR heZ' with h1 | h1
    · have h2 : e = 1 := by
        calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [h2, orderOf_one] at he2
      omega
    · have h2 : e = t₂ := by
        calc e = g⁻¹ * (g * e * g⁻¹) * g := by group
          _ = t₂ := by rw [h1, ht₂]
      rw [← h2]
      exact (mem_inf.mp he).2

omit h in
omit [Finite G] in
theorem t_mem_conjugate_Q_L513 (hzQ : z ∈ Q) {s : G} (hz : z = s⁻¹ * t * s) :
    t ∈ conjugate Q s⁻¹ := by
  rw [mem_conjugate_iff, inv_inv, ← hz]
  exact hzQ

theorem inf_conjugate_Q_inv_L513 {s : G} (hsT : s ∈ T) (hz : z = s⁻¹ * t * s) :
    Q ⊓ conjugate Q s⁻¹ = ⊥ := by
  refine h.inf_conjugate_Q_eq_bot_of_ne (inv_mem hsT) fun h1 => h.t_not_mem_Q ?_
  rw [← h1]
  exact t_mem_conjugate_Q_L513 h.zQ hz

theorem conjugate_Q_inv_facts_L513 {s : G} (hsN : s ∈ normalizer (S : Set G)) (hsT : s ∈ T)
    (hz : z = s⁻¹ * t * s) :
    (∀ u ∈ S, ∀ b ∈ conjugate Q s⁻¹, u * b * u⁻¹ ∈ conjugate Q s⁻¹) ∧
      ∀ a ∈ Q, ∀ b ∈ conjugate Q s⁻¹, a * b = b * a := by
  have hn : ∀ u ∈ S, ∀ b ∈ conjugate Q s⁻¹, u * b * u⁻¹ ∈ conjugate Q s⁻¹ := by
    intro u hu b hb
    rw [mem_conjugate_iff, inv_inv] at hb ⊢
    have hu' : s⁻¹ * u * s ∈ S := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hsN) u).mp hu
      rwa [inv_inv] at h1
    rw [show s⁻¹ * (u * b * u⁻¹) * s = (s⁻¹ * u * s) * (s⁻¹ * b * s) * (s⁻¹ * u * s)⁻¹ by
      group]
    exact h.conj_mem_Q hu' hb
  refine ⟨hn, fun a ha b hb => ?_⟩
  have hbS : b ∈ S := by
    have h1 := mem_conjugate_iff.mp hb
    rw [inv_inv] at h1
    have h2 := (mem_normalizer_iff.mp hsN _).mp (h.QS h1)
    rwa [show s * (s⁻¹ * b * s) * s⁻¹ = b by group] at h2
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ Q := by
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem ha (h.conj_mem_Q hbS (inv_mem ha))
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ conjugate Q s⁻¹ :=
    mul_mem (hn a (h.QS ha) b hb) (inv_mem hb)
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ Q ⊓ conjugate Q s⁻¹ := mem_inf.mpr ⟨h1, h2⟩
  rw [h.inf_conjugate_Q_inv_L513 hsT hz, mem_bot] at h3
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem exists_conj_mem_S_of_centralizes_R_L513 {u : G} (huN : u ∈ normalizer (L : Set G))
    (huR : ∀ r ∈ S ⊓ L, u * r = r * u) (hu2 : u * u = 1) :
    ∃ c : G, c ∈ normalizer (L : Set G) ∧ (∀ r ∈ S ⊓ L, c * r = r * c) ∧ c⁻¹ * u * c ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := normalizer (L : Set G) ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) with hXdef
  have hmemX : ∀ x : G, x ∈ normalizer (L : Set G) → (∀ r ∈ S ⊓ L, x * r = r * x) → x ∈ X :=
    fun x hxN hxR => mem_inf.mpr ⟨hxN, mem_centralizer_iff.mpr fun r hr => (hxR r hr).symm⟩
  have hXR : ∀ x ∈ X, ∀ r ∈ S ⊓ L, x * r = r * x := fun x hx r hr =>
    ((mem_centralizer_iff.mp (mem_inf.mp hx).2) r hr).symm
  set C := S ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) with hCdef
  have hCX : C ≤ X := fun x hx => mem_inf.mpr ⟨h.S_le (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  obtain ⟨P, hP, hCP⟩ := exists_isSylowOf_ge_of_le hCX (h.isPGroup_S.to_le inf_le_left)
  have hRN : (S ⊓ L : Subgroup G) ≤ normalizer (P : Set G) := fun r hr =>
    mem_normalizer_of_conj_mem_L512 fun p hp => by
      rw [← hXR p (hP.le hp) r hr, mul_inv_cancel_right]
      exact hp
  have hPR2 := IsPGroup.to_sup_of_normal_left' hP.isPGroup h.R_sylow.isPGroup hRN
  obtain ⟨n, hnN, hn⟩ := exists_conj_le_of_isSylowOf h.sylS
    (sup_le (hP.le.trans inf_le_left) (inf_le_right.trans le_normalizer)) hPR2
  have hnR : ∀ r ∈ S ⊓ L, n⁻¹ * r * n ∈ S ⊓ L := fun r hr => mem_inf.mpr
    ⟨hn r (mem_sup_right hr), by
      have h1 := (mem_normalizer_iff.mp (inv_mem hnN) r).mp (mem_inf.mp hr).2
      rwa [inv_inv] at h1⟩
  have hsurj : ∀ r ∈ S ⊓ L, ∃ r' ∈ S ⊓ L, r = n⁻¹ * r' * n := by
    let f : ↥(S ⊓ L) → ↥(S ⊓ L) := fun r => ⟨n⁻¹ * r * n, hnR r r.2⟩
    have hf : Function.Injective f := fun a b hab => by
      have h1 : n⁻¹ * (a : G) * n = n⁻¹ * b * n := congrArg Subtype.val hab
      rw [mul_left_inj, mul_right_inj] at h1
      exact Subtype.ext h1
    intro r hr
    obtain ⟨r', hr'⟩ := Finite.surjective_of_injective hf ⟨r, hr⟩
    exact ⟨r', r'.2, (congrArg Subtype.val hr').symm⟩
  have hPC : conjugate P n ≤ C := by
    intro x hx
    rw [mem_conjugate_iff] at hx
    have hxS : x ∈ S := by
      have h1 := hn _ (mem_sup_left hx)
      rwa [show n⁻¹ * (n * x * n⁻¹) * n = x by group] at h1
    refine mem_inf.mpr ⟨hxS, mem_centralizer_iff.mpr fun r hr => ?_⟩
    obtain ⟨r', hr', rfl⟩ := hsurj r hr
    have h1 := hXR _ (hP.le hx) r' hr'
    calc n⁻¹ * r' * n * x = n⁻¹ * (r' * (n * x * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * x * n⁻¹) * r') * n := by rw [h1]
      _ = x * (n⁻¹ * r' * n) := by group
  have hCeq : C = P := eq_of_le_of_card_ge hCP
    (by rw [← card_conjugate_eq_card P n]; exact card_le_of_le hPC)
  have hu2g : IsPGroup 2 (zpowers u) := isPGroup_zpowers_of_pow_two (k := 1)
    (by rw [pow_one, sq]; exact hu2)
  obtain ⟨c, hcX, hc⟩ := exists_conj_le_of_isSylowOf hP
    (zpowers_le.mpr (hmemX u huN huR)) hu2g
  have h1 := hc u (mem_zpowers u)
  rw [← hCeq] at h1
  exact ⟨c, (mem_inf.mp hcX).1, hXR c hcX, (mem_inf.mp h1).1⟩

end Sec5

end CFSG.ComponentClassification.Foote5
