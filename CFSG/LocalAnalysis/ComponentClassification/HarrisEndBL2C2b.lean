module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2C2a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitMacWilliams

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem qc_conj_tbeta (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W)
    (hSV : S.relIndex V = 2) {𝒮 Y : Subgroup X} (hV𝒮 : V ≤ 𝒮)
    (h𝒮β : 𝒮 ⊓ centralizer ({β₀} : Set X) = W) (hYn : ∀ g ∈ 𝒮, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (htβY : t * β₀ ∈ Y)
    (hYX : ∀ x ∈ Y, x ∈ X₈ → x = 1 ∨ x = z ∨ x = t * β₀ ∨ x = t * (β₀ * z)) {n : X}
    (hn𝒮 : n ∈ 𝒮) (hnV : n ∈ normalizer (V : Set X)) :
    n * (t * β₀) * n⁻¹ = t * β₀ ∨ n * (t * β₀) * n⁻¹ = t * β₀ * z := by
  have hconj : ∀ g y : X, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun g y => rfl
  have htX : t ∈ X₈ := subset_closure (by simp)
  have htβX : t * β₀ ∈ X₈ := mul_mem htX (beta_mem_X i j)
  have hX8c : ∀ a ∈ X₈, ∀ b ∈ X₈, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hs.setup.X_le_center_T ha).2 b (hs.setup.X_le_T hb)).symm
  have hVX : ∀ v ∈ V, ∀ x ∈ X₈, v * x * v⁻¹ ∈ X₈ := fun v hv x hx =>
    (mem_normalizer_iff.mp (hs.setup.normalizer_T_le_normalizer_X (hs.sylow_V.le hv)) x).mp hx
  have hX𝒮 : X₈ ≤ 𝒮 := (hs.setup.X_le_T.trans (hs.setup.T_le.trans hs.le_V)).trans hV𝒮
  have hnX : n * (t * β₀) * n⁻¹ ∈ X₈ := by
    by_cases hall : ∀ x ∈ X₈, n * x * n⁻¹ ∈ X₈
    · exact hall _ htβX
    · set Y₁ := (X₈).map (MulAut.conj n⁻¹).toMonoidHom with hY₁
      have hVY₁ : ∀ v ∈ V, ∀ y ∈ Y₁, v * y * v⁻¹ ∈ Y₁ := by
        rintro v hv _ ⟨x, hx, rfl⟩
        have hv' : n * v * n⁻¹ ∈ V := (mem_normalizer_iff.mp hnV v).mp hv
        refine ⟨(n * v * n⁻¹) * x * (n * v * n⁻¹)⁻¹, hVX _ hv' x hx, ?_⟩
        rw [hconj, hconj]
        group
      have hY₁c : ∀ a ∈ Y₁, ∀ b ∈ Y₁, a * b = b * a := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hX8c a ha b hb]
      have hY₁2 : ∀ y ∈ Y₁, y * y = 1 := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_mul, ← sq, hs.setup.sq_eq_one_of_mem_X ha, map_one]
      have hY₁8 : Nat.card Y₁ = 8 := by
        rw [hY₁, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hs.setup.card_X]
      have hY₁W : β₀ ∈ Y₁ → Y₁ ≤ W := fun hβ a ha => by
        rw [← h𝒮β]
        obtain ⟨x, hx, rfl⟩ := ha
        refine Subgroup.mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr
          (hY₁c _ ⟨x, hx, rfl⟩ _ hβ)⟩
        rw [hconj]
        exact mul_mem (mul_mem (inv_mem hn𝒮) (hX𝒮 hx)) (inv_mem (inv_mem hn𝒮))
      have hY₁X : ¬ Y₁ ≤ X₈ := fun hle => hall fun x hx => by
        have heq : Y₁ = X₈ := Subgroup.eq_of_le_of_card_ge hle (by rw [hY₁8, hs.setup.card_X])
        have hxY : x ∈ Y₁ := heq ▸ hx
        obtain ⟨x', hx', hxx'⟩ := hxY
        rw [hconj] at hxx'
        rw [← hxx', show n * (n⁻¹ * x' * n⁻¹⁻¹) * n⁻¹ = x' by group]
        exact hx'
      obtain ⟨⟨x, hx, hxe⟩, -⟩ := hc.qc_inf_X hKG hKC hFC hKF hSV hVY₁ hY₁c hY₁2 hY₁8 hY₁W hY₁X
      rw [hconj] at hxe
      rw [← hxe, show n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ = x by group]
      exact hx
  have hz := hs.conj_z_of_normalizer_V hKC (hc.qc_beta_not_mem hKF hSV) hnV
  rcases hYX _ (hYn n hn𝒮 _ htβY) hnX with h | h | h | h
  · exfalso
    have : t * β₀ = 1 := by
      have := congrArg (fun y => n⁻¹ * y * n) h
      simpa [mul_assoc] using this
    exact hs.beta.not_mem (by
      have e : β₀ = t⁻¹ * (t * β₀) := by group
      rw [e, this, mul_one]
      exact inv_mem (mem_sup_left (mem_zpowers t)))
  · exfalso
    have : t * β₀ = z := by
      have h' : n * (t * β₀) * n⁻¹ = n * z * n⁻¹ := by rw [h, hz]
      simpa [mul_assoc] using congrArg (fun y => n⁻¹ * y * n) h'
    exact hs.beta.not_mem (by
      have e : β₀ = t⁻¹ * (t * β₀) := by group
      rw [e, this]
      exact mul_mem (inv_mem (mem_sup_left (mem_zpowers t))) (mem_sup_right hs.setup.z_mem))
  · exact Or.inl h
  · exact Or.inr (by rw [h]; group)

theorem false_of_not_isSylowOf_two
    (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W)
    (hV : ¬ IsSylowOf 2 V ⊤) (hSV : S.relIndex V = 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hWS, hST2⟩ := hc.qc_structure hKF hSV
  obtain ⟨hWV, -⟩ := hc.qc_relIndex hKF hSV
  have hST := hc.qc_S_ne hKF hSV
  obtain ⟨𝒮, h𝒮, hV𝒮⟩ := exists_isSylowOf_ge hs.sylow_V.isPGroup (le_top : V ≤ ⊤)
  have hne : V ≠ 𝒮 := fun h => hV (h ▸ h𝒮)
  have h𝒮β : 𝒮 ⊓ centralizer ({β₀} : Set X) = W :=
    hc.sylow.eq_of_le (le_inf (hWV.trans hV𝒮) hc.sylow.le) inf_le_right
      (h𝒮.isPGroup.to_le inf_le_left)
  obtain ⟨Y, hY𝒮, hYn, hYc, hY2, hY8⟩ := exists_normal_E8 hs.standing.sect h𝒮
  have hY2' : ∀ y ∈ Y, y * y = 1 := fun y hy => by rw [← sq]; exact hY2 y hy
  have hTV : T₀ ≤ V := hs.setup.T_le.trans hs.le_V
  have hYX : ¬ Y ≤ X₈ := by
    intro hle
    have heq : Y = X₈ := Subgroup.eq_of_le_of_card_ge hle (by rw [hY8, hs.setup.card_X])
    have hN := hs.le_normalizer_T (hTV.trans hV𝒮) h𝒮.isPGroup fun g hg x hx => by
      rw [← heq] at hx ⊢
      exact hYn g hg x hx
    exact hne (hs.sylow_V.eq_of_le hV𝒮 hN h𝒮.isPGroup).symm
  have hYW : β₀ ∈ Y → Y ≤ W := fun hβ a ha => by
    rw [← h𝒮β]
    exact Subgroup.mem_inf.mpr ⟨hY𝒮 ha, mem_centralizer_singleton_iff.mpr (hYc a ha _ hβ)⟩
  obtain ⟨htβY, hYX8⟩ := hc.qc_inf_X hKG hKC hFC hKF hSV
    (fun v hv y hy => hYn v (hV𝒮 hv) y hy) hYc hY2' hY8 hYW hYX
  have hVP : V ≤ 𝒮 ⊓ normalizer (V : Set X) := le_inf hV𝒮 Subgroup.le_normalizer
  have hP2 : IsPGroup 2 ↥(𝒮 ⊓ normalizer (V : Set X)) := h𝒮.isPGroup.to_le inf_le_left
  have h2V : 2 * Nat.card V ≤ Nat.card ↥(𝒮 ⊓ normalizer (V : Set X)) := by
    obtain ⟨n, hn, hnV, hnN⟩ :=
      L415.exists_mem_normalizer_of_lt h𝒮.isPGroup (lt_of_le_of_ne hV𝒮 hne)
    have hlt : Nat.card V < Nat.card ↥(𝒮 ⊓ normalizer (V : Set X)) := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hVP) fun h => hnV ?_
      rw [Subgroup.eq_of_le_of_card_ge hVP h.ge]
      exact Subgroup.mem_inf.mpr ⟨hn, hnN⟩
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hVP
    rw [hk] at hlt ⊢
    have hpos : 0 < Nat.card V := Nat.card_pos
    have hk2 : 2 ≤ k := by
      by_contra h
      push Not at h
      interval_cases k <;> omega
    nlinarith
  have hfib := L415.card_le_of_fiber (A := 𝒮 ⊓ normalizer (V : Set X))
    (K := centralizer ({t * β₀} : Set X)) (fun g => g * (t * β₀) * g⁻¹)
    (fun a _ b _ h => by
      rw [mem_centralizer_singleton_iff]
      calc a⁻¹ * b * (t * β₀) = a⁻¹ * (b * (t * β₀) * b⁻¹) * b := by group
        _ = a⁻¹ * (a * (t * β₀) * a⁻¹) * b := by rw [h]
        _ = t * β₀ * (a⁻¹ * b) := by group)
    ({t * β₀, t * β₀ * z} : Finset X) (fun g hg => by
      rcases hc.qc_conj_tbeta hKG hKC hFC hKF hSV hV𝒮 h𝒮β hYn htβY hYX8 hg.1 hg.2 with h | h <;>
        simp [h])
  have hcard2 : ({t * β₀, t * β₀ * z} : Finset X).card ≤ 2 := Finset.card_le_two
  have hCP : Nat.card V ≤
      Nat.card ↥((𝒮 ⊓ normalizer (V : Set X)) ⊓ centralizer ({t * β₀} : Set X)) := by
    have := hfib.trans (Nat.mul_le_mul_left _ hcard2)
    omega
  have hC := hCP.trans (card_le_twoPart (hP2.to_le inf_le_left) inf_le_right)
  have hVS := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hs.le_V, hSV] at hVS
  have hTpos : 0 < Nat.card T₀ := Nat.card_pos
  have hβc : twoPart (centralizer ({β₀} : Set X)) = Nat.card W := hc.card_eq.symm
  have hle4 := hs.beta.twoPart_le
  have hmax := hs.twoPart_le_of_fus hKF hKC (hs.fus_of_qc hKF hSV hST) (beta_mem_X i j)
    hs.beta.not_mem (by omega) (by omega)
  omega

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
