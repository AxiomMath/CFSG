module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2E4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

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

local notation "Q₀" => qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W
local notation "A₀" => (qTilde (w ^ (orderOf w / 2) * t ^ i * z ^ j) W ⊔ zpowers z : Subgroup X)

theorem map_conj_eq_T (hc : L2Ctx hs W) (hST : S = T₀) {g : X}
    (hcent : ∀ c ∈ W ⊓ centralizer ({t} : Set X),
      g⁻¹ * c * g ∈ W ⊓ centralizer ({g⁻¹ * t * g} : Set X)) :
    (W ⊓ centralizer ({g⁻¹ * t * g} : Set X)).map (MulAut.conj g).toMonoidHom = T₀ := by
  have hconj : ∀ y, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun y => rfl
  have hH'C : (W ⊓ centralizer ({g⁻¹ * t * g} : Set X)).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({t} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj, mem_centralizer_singleton_iff]
    have h1 : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := mem_centralizer_singleton_iff.mp hx.2
    calc g * x * g⁻¹ * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [h1]
      _ = t * (g * x * g⁻¹) := by group
  have hTH' : T₀ ≤ (W ⊓ centralizer ({g⁻¹ * t * g} : Set X)).map
      (MulAut.conj g).toMonoidHom := by
    intro c hcT
    have hcW : c ∈ W ⊓ centralizer ({t} : Set X) := by rw [hc.inf_centralizer_t]; exact hcT
    refine ⟨g⁻¹ * c * g, hcent c hcW, ?_⟩
    rw [hconj]
    group
  have hH'2 : IsPGroup 2 ↥((W ⊓ centralizer ({g⁻¹ * t * g} : Set X)).map
      (MulAut.conj g).toMonoidHom) := (hc.sylow.isPGroup.to_le inf_le_left).map _
  have hcard := (card_le_twoPart hH'2 hH'C).trans_eq hs.sylow.card_eq.symm
  rw [hST] at hcard
  exact (Subgroup.eq_of_le_of_card_ge hTH' hcard).symm

theorem false_of_mem_center [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKC : AutPSL2CentralizerInput) (hc : L2Ctx hs W) (hV : IsSylowOf 2 V ⊤)
    (hβZ : β₀ ∈ V ⊓ centralizer (V : Set X)) (hSV : S.relIndex V = 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ g y : X, (MulAut.conj g).toMonoidHom y = g * y * g⁻¹ := fun g y => rfl
  have hVβ : V ≤ centralizer ({β₀} : Set X) := fun v hv =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hβZ.2 v hv)
  have hU : V ⊓ centralizer ({β₀} : Set X) = V := inf_of_le_left hVβ
  have hVW : V ≤ W := hU ▸ hc.le
  have hWV : W = V := hV.eq_of_le hVW le_top hc.sylow.isPGroup
  have hVS := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hs.le_V, hSV] at hVS
  have hST : S = T₀ := by
    have h1 := hs.card_U_le_four_mul hKC
    rw [hU] at h1
    exact (Subgroup.eq_of_le_of_card_ge hs.setup.T_le (by omega)).symm
  have htX : t ∈ X₈ := subset_closure (by simp)
  have hnc := hc.qd_not_cyclic hSV
  have h4 : Nat.card ↥(Q₀) = 4 := hc.card_qTilde_eq_four hnc (hc.card_qTilde_le_four
    fun y hy => (mem_normalizer_iff.mp (hs.setup.normalizer_T_le_normalizer_X
      (hs.sylow_V.le (hWV ▸ hc.qTilde_le hy))) t).mp htX)
  have hQ2 := fun q (hq : q ∈ Q₀) => hc.qTilde_sq h4 hnc hq
  obtain ⟨y₀, hy₀, hy₀b, hty₀⟩ := hc.exists_y0 h4
  have hidx := hc.relIndex_centralizer_eq h4 hy₀ hty₀
  have htN : t ∉ W ⊓ centralizer ({y₀} : Set X) := fun h' => by
    have h1 : t * y₀ = y₀ * t := mem_centralizer_singleton_iff.mp h'.2
    have : y₀ * β₀ = y₀ * 1 := by rw [← hty₀, h1, mul_one]; group
    exact hs.beta.ne_one (mul_left_cancel this)
  have hWidx : ¬ 2 ∣ W.index := by
    have := (isSylowOf_iff.mp hV).2.2
    rwa [Subgroup.relIndex_top_right, ← hWV] at this
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  obtain ⟨g, hτN, -, hcent⟩ := exists_extremal_conj_of_relIndex_two hnab hc.sylow.isPGroup
    hWidx inf_le_left hidx hc.t_mem_W htN ht2
  have hHT := hc.map_conj_eq_T hST hcent
  set τ := g⁻¹ * t * g with hτ
  have hcardH : Nat.card ↥(W ⊓ centralizer ({τ} : Set X)) = Nat.card T₀ := by
    rw [← hHT, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hτW : τ ∈ W := hτN.1
  have hτy₀ : τ * y₀ = y₀ * τ := mem_centralizer_singleton_iff.mp hτN.2
  have hAτ : A₀ ≤ centralizer ({τ} : Set X) := hc.A_le_centralizer hKC h4 hy₀ hy₀b hτW hτy₀
  obtain ⟨hAc, hA2, hA8⟩ := hc.A_elem hKC h4 hQ2
  have hτA : τ ∉ A₀ := by
    intro hτA'
    have hNH : W ⊓ centralizer ({y₀} : Set X) ≤ W ⊓ centralizer ({τ} : Set X) := fun n hn =>
      ⟨hn.1, mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp
        ((hc.A_le_centralizer hKC h4 hy₀ hy₀b hn.1
          (mem_centralizer_singleton_iff.mp hn.2)) hτA')).symm⟩
    have h1 := Subgroup.card_le_of_le hNH
    have h2 := Subgroup.relIndex_mul_card (W ⊓ centralizer ({y₀} : Set X)) W
    rw [inf_of_le_left inf_le_left, hidx] at h2
    have hSc : Nat.card S = Nat.card T₀ := congrArg (fun H : Subgroup X => Nat.card ↥H) hST
    have hWc : Nat.card W = Nat.card V := by rw [hWV]
    have hpos : 0 < Nat.card T₀ := Nat.card_pos
    omega
  have hτ2 : τ * τ = 1 := by
    have ht2' : t * t = 1 := by rw [← sq, ht2]
    calc τ * τ = g⁻¹ * (t * t) * g := by rw [hτ]; group
      _ = 1 := by rw [ht2']; group
  obtain ⟨-, hE2, hE16⟩ := L415.elem_sup hAc hA2 hτ2 hτA fun a ha =>
    mem_centralizer_singleton_iff.mp (hAτ ha)
  have hEH : A₀ ⊔ zpowers τ ≤ W ⊓ centralizer ({τ} : Set X) :=
    le_inf (sup_le (sup_le hc.qTilde_le (zpowers_le.mpr hc.z_mem_W)) (zpowers_le.mpr hτW))
      (sup_le hAτ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)))
  have hEn : ∀ h ∈ W ⊓ centralizer ({τ} : Set X), ∀ e ∈ A₀ ⊔ zpowers τ,
      h * e * h⁻¹ ∈ A₀ ⊔ zpowers τ := by
    intro h hh e he
    have hle : (A₀ ⊔ zpowers τ).map (MulAut.conj h).toMonoidHom ≤ A₀ ⊔ zpowers τ := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [hconj]
        exact hc.A_normal hKC hh.1 ha
      · rw [MonoidHom.map_zpowers, hconj, (mem_centralizer_singleton_iff.mp hh.2),
          mul_inv_cancel_right]
    exact hle ⟨e, he, rfl⟩
  have hFT : (A₀ ⊔ zpowers τ).map (MulAut.conj g).toMonoidHom ≤ T₀ := by
    rw [← hHT]
    exact map_mono hEH
  have hFn : ∀ d ∈ S ⊓ L, ∀ x ∈ (A₀ ⊔ zpowers τ).map (MulAut.conj g).toMonoidHom,
      d * x * d⁻¹ ∈ (A₀ ⊔ zpowers τ).map (MulAut.conj g).toMonoidHom := by
    rintro d hd _ ⟨e, he, rfl⟩
    have hdW : d ∈ W ⊓ centralizer ({t} : Set X) := by
      rw [hc.inf_centralizer_t]
      exact mem_sup_left (mem_sup_right hd)
    refine ⟨(g⁻¹ * d * g) * e * (g⁻¹ * d * g)⁻¹, hEn _ (hcent d hdW) e he, ?_⟩
    rw [hconj, hconj]
    group
  have hF2 : ∀ x ∈ (A₀ ⊔ zpowers τ).map (MulAut.conj g).toMonoidHom, x ^ 2 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, sq, hE2 e he, map_one]
  have hFX := hs.setup.le_X_of_normal_T hFT hFn hF2
  have h16 := Subgroup.card_le_of_le hFX
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE16, hA8,
    hs.setup.card_X] at h16
  omega

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
