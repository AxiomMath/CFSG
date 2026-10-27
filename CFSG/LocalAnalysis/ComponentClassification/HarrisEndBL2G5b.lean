module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2G5a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitMacWilliams

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

local notation "Q₀" => qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W
local notation "A₀" => (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z : Subgroup X)

theorem card_qTilde_le_four_of_sq (hc : L2Ctx hs W) (hnc : ¬ IsCyclic ↥(pCore 2 (MBar β₀)))
    (hQ2 : ∀ q ∈ Q₀, q * q = 1) : Nat.card ↥(Q₀) ≤ 4 := by
  rcases hc.qTilde_shape with hcyc | ⟨k, -, ⟨e⟩⟩
  · exact absurd (isCyclic_of_surjective hc.qTildeEquiv.toMonoidHom
      hc.qTildeEquiv.surjective) hnc
  · have hx := hQ2 _ (e.symm (DihedralGroup.r 1)).2
    have hord : orderOf ((e.symm (DihedralGroup.r 1) : ↥(Q₀)) : X) = 2 ^ k := by
      have h1 : orderOf (e.symm (DihedralGroup.r 1)) =
          orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ k)) :=
        orderOf_injective e.symm.toMonoidHom e.symm.injective _
      rw [Subgroup.orderOf_coe, h1, DihedralGroup.orderOf_r_one]
    have hdvd : orderOf ((e.symm (DihedralGroup.r 1) : ↥(Q₀)) : X) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [sq, hx])
    rw [hord] at hdvd
    have hk : k ≤ 1 := by
      by_contra hk
      push Not at hk
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
    omega

theorem false_of_not_isSylowOf_four
    (hKG : AutPSL2SylowInput) (hKC : AutPSL2CentralizerInput)
    (hFC : AutPSL2FieldCentralizerInput) (hc : L2Ctx hs W) (hV : ¬ IsSylowOf 2 V ⊤)
    (hSV : S.relIndex V = 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ℰ, hℰ, hWℰ⟩ := exists_isSylowOf_ge hc.sylow.isPGroup (le_top : W ≤ ⊤)
  obtain ⟨Y, hYℰ, hYn, hYc, hY2, hY8⟩ := exists_normal_E8 hs.standing.sect hℰ
  obtain ⟨hnt, hβY⟩ := hc.beta_mem_of_normal hV hSV hℰ hWℰ hYℰ hYn hYc hY2 hY8
  have hℰβ : ℰ ⊓ centralizer ({β₀} : Set X) = W :=
    hc.sylow.eq_of_le (le_inf hWℰ hc.sylow.le) inf_le_right (hℰ.isPGroup.to_le inf_le_left)
  have hYW : Y ≤ W := fun a ha => by
    rw [← hℰβ]
    exact Subgroup.mem_inf.mpr ⟨hYℰ ha, mem_centralizer_singleton_iff.mpr (hYc a ha _ hβY)⟩
  have hY2' : ∀ y ∈ Y, y * y = 1 := fun y hy => by rw [← sq]; exact hY2 y hy
  have hYnW : ∀ g ∈ W, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy => hYn g (hWℰ hg) y hy
  have hnc := hc.qd_not_cyclic hSV
  have hQ2 := hc.qTilde_sq_of_normal hKG hKC hFC hnc hYW hYnW hY2' (by rw [hY8])
  have h4 := hc.card_qTilde_eq_four hnc (hc.card_qTilde_le_four_of_sq hnc hQ2)
  have h4' : Nat.card ↥(pCore 2 (MBar β₀)) = 4 := by rw [← hc.card_qTilde, h4]
  have hYN := hc.le_N0_of_normal hKG hKC hFC hYW hYnW hY2'
  have hYA : Y = A₀ := by
    rcases hc.eq_X_or_eq_A hKC h4' hQ2 hYN hYc hY2' hY8 with h | h
    · exfalso
      apply hnt 1
      rw [h, one_mul, inv_one, mul_one]
      exact subset_closure (by simp)
    · exact h
  obtain ⟨y₀, hy₀, -, hty₀⟩ := hc.exists_y0 h4
  have hβe : β₀ = y₀⁻¹ * (t * y₀ * t⁻¹) := by rw [hty₀]; group
  have hN : ∀ n ∈ ℰ, n ∈ normalizer (W : Set X) → n ∈ W := by
    intro n hn hnW
    have hnt' : n * t * n⁻¹ ∈ W := (mem_normalizer_iff.mp hnW t).mp hc.t_mem_W
    have hna : n * y₀ * n⁻¹ ∈ A₀ := hYA ▸ hYn n hn y₀ (hYA ▸ mem_sup_left hy₀)
    have hm := hc.A_comm_mem hKC h4 hnt' hna
    have hnaW : n * y₀ * n⁻¹ ∈ W := hYW (hYA ▸ hna)
    have h1 : n * β₀ * n⁻¹ = (n * y₀ * n⁻¹)⁻¹ *
        ((n * t * n⁻¹) * (n * y₀ * n⁻¹) * (n * t * n⁻¹)⁻¹ * (n * y₀ * n⁻¹)⁻¹) *
        (n * y₀ * n⁻¹)⁻¹⁻¹ := by
      rw [hβe]
      group
    have h2 : n * β₀ * n⁻¹ ∈ zpowers β₀ := by
      rw [h1, hc.conj_zpowers_eq (W.inv_mem hnaW) hm]
      exact hm
    rw [← hℰβ]
    refine Subgroup.mem_inf.mpr ⟨hn, mem_centralizer_singleton_iff.mpr ?_⟩
    rcases L415.mem_zpowers_two hc.beta_sq h2 with h3 | h3
    · exfalso
      apply hs.beta.ne_one
      have := congrArg (fun y => n⁻¹ * y * n) h3
      simpa [mul_assoc] using this
    · calc n * β₀ = n * β₀ * n⁻¹ * n := by group
        _ = β₀ * n := by rw [h3]
  have hWeq : W = ℰ := by
    by_contra hne
    obtain ⟨n, hn, hnW, hnN⟩ :=
      L415.exists_mem_normalizer_of_lt hℰ.isPGroup (lt_of_le_of_ne hWℰ hne)
    exact hnW (hN n hn hnN)
  have hWS : IsSylowOf 2 W ⊤ := hWeq ▸ hℰ
  have hWU := hc.eq_U_of_normal_X fun g hg x hx => hc.X_normal hKG hKC hFC h4' hQ2 hg hx
  have hWV : W ≤ V := hWU ▸ inf_le_left
  apply hV
  rw [hWS.eq_of_le hWV le_top hs.sylow_V.isPGroup]
  exact hWS

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
