module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2BigB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Beta

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

theorem EndB.card_le_mul_self {G : Type*} [Group G] [Finite G] {Y : Subgroup G}
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ a ∈ Y, a * a = 1) {t : G}
    (ht2 : t * t = 1) (htY : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y) :
    Nat.card Y ≤ Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) *
      Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) := by
  classical
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hfin := Set.toFinite ((Y ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)
  have h := L415.card_le_of_fiber (A := Y) (K := centralizer ({t} : Set G))
    (fun a => a⁻¹ * (t * a * t⁻¹)) (fun a ha a' ha' h => by
      have hc' : t * a' * t⁻¹ = a' * a⁻¹ * (t * a * t⁻¹) := by
        calc t * a' * t⁻¹ = a' * (a'⁻¹ * (t * a' * t⁻¹)) := by group
          _ = a' * (a⁻¹ * (t * a * t⁻¹)) := by rw [h]
          _ = a' * a⁻¹ * (t * a * t⁻¹) := by group
      have hca := hYc _ (htY a ha) _ (mul_mem ha' (inv_mem ha))
      have haa := hYc _ (inv_mem ha) _ ha'
      rw [mem_centralizer_singleton_iff]
      calc a⁻¹ * a' * t = (a' * a⁻¹) * t := by rw [haa]
        _ = (t * a * t⁻¹)⁻¹ * (a' * a⁻¹ * (t * a * t⁻¹)) * t := by rw [← hca]; group
        _ = (t * a * t⁻¹)⁻¹ * (t * a' * t⁻¹) * t := by rw [← hc']
        _ = t * (a⁻¹ * a') := by group) hfin.toFinset (fun a ha => by
      rw [Set.Finite.mem_toFinset]
      show a⁻¹ * (t * a * t⁻¹) ∈ Y ⊓ centralizer ({t} : Set G)
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) (htY a ha), ?_⟩
      have hac := hYc a ha _ (htY a ha)
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hY2 a ha)
      rw [hti] at hac
      show a⁻¹ * (t * a * t⁻¹) ∈ centralizer ({t} : Set G)
      rw [mem_centralizer_singleton_iff, hti, hai]
      calc a * (t * a * t) * t = a * t * a * (t * t) := by group
        _ = a * t * a := by rw [ht2, mul_one]
        _ = (t * t) * (a * t * a) := by rw [ht2, one_mul]
        _ = t * ((t * a * t) * a) := by group
        _ = t * (a * (t * a * t)) := by rw [← hac])
  rwa [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq] at h

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem beta_mem_of_normal (hc : L2Ctx hs W) (hV : ¬ IsSylowOf 2 V ⊤)
    (hSV : S.relIndex V = 4) {ℰ Y : Subgroup X} (hℰ : IsSylowOf 2 ℰ ⊤) (hWℰ : W ≤ ℰ)
    (hYℰ : Y ≤ ℰ) (hYn : ∀ g ∈ ℰ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hY2 : ∀ y ∈ Y, y ^ 2 = 1)
    (hY8 : Nat.card Y = 8) : (∀ g : X, g * t * g⁻¹ ∉ Y) ∧ β₀ ∈ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY2' : ∀ y ∈ Y, y * y = 1 := fun y hy => by rw [← sq]; exact hY2 y hy
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by
    have := hs.standing.config.orderOf_eq
    rw [h, orderOf_one] at this
    omega
  have hVS := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hs.le_V, hSV] at hVS
  have hVlt : Nat.card V < twoPart (⊤ : Subgroup X) := by
    refine lt_of_le_of_ne (card_le_twoPart hs.sylow_V.isPGroup le_top) fun h => hV ?_
    exact isSylowOf_of_card le_top h
  have hnt : ∀ g : X, g * t * g⁻¹ ∉ Y := by
    intro g hg
    have h1 := twoPart_le_of_mem hℰ hYℰ hYn hY8 hg (fun h => ht1 (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group))
    have h2 : twoPart (centralizer ({t} : Set X)) = Nat.card S := hs.sylow.card_eq.symm
    rw [L415.twoPart_centralizer_conj, h2] at h1
    omega
  refine ⟨hnt, ?_⟩
  have hTℰ := hc.T_le.trans hWℰ
  have hCX : Y ⊓ centralizer ({t} : Set X) ≤ X₈ :=
    hs.setup.le_X_of_elem_centralizer inf_le_right (fun x hx => hY2 x hx.1)
      fun g hg x hx => by
        have hgC : g ∈ centralizer ({t} : Set X) := hs.sylow.le (hs.setup.T_le hg)
        exact Subgroup.mem_inf.mpr ⟨hYn g (hTℰ hg) x hx.1, mul_mem (mul_mem hgC hx.2) (inv_mem hgC)⟩
  have htY : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y := fun a ha => hYn t (hTℰ (mem_sup_left (mem_sup_left
    (mem_zpowers t)))) a ha
  have hsq := EndB.card_le_mul_self hYc hY2' ht2 htY
  rw [hY8] at hsq
  have hC4 : 4 ≤ Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) := by
    have hdvd : Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) ∣ 8 := by
      rw [← hY8]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hpos : 0 < Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    interval_cases h : Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) <;> omega
  by_contra hβY
  have hSC : V ⊓ centralizer ({t} : Set X) = S :=
    hs.sylow.eq_of_le (le_inf hs.le_V hs.sylow.le) inf_le_right
      (hs.sylow_V.isPGroup.to_le inf_le_left)
  have htV : t ∈ V := hs.le_V (hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t))))
  have htX : t ∈ X₈ := subset_closure (by simp)
  have hO4 : {y : X | ∃ a ∈ V, a * t * a⁻¹ = y}.ncard = 4 := by
    rw [ncard_conj_orbit V htV, ← Subgroup.inf_relIndex_right, inf_comm, hSC, hSV]
  have hdisj1 : Disjoint (((Y ⊓ centralizer ({t} : Set X) : Subgroup X)) : Set X)
      {y : X | ∃ a ∈ V, a * t * a⁻¹ = y} := by
    rw [Set.disjoint_left]
    rintro y hyC ⟨a, -, rfl⟩
    exact hnt a hyC.1
  have hdisj2 : Disjoint ((((Y ⊓ centralizer ({t} : Set X) : Subgroup X)) : Set X) ∪
      {y : X | ∃ a ∈ V, a * t * a⁻¹ = y}) {β₀} := by
    rw [Set.disjoint_singleton_right]
    rintro (h | ⟨a, -, ha⟩)
    · exact hβY h.1
    · exact hs.beta.not_conj a ha
  have hsub : (((Y ⊓ centralizer ({t} : Set X) : Subgroup X)) : Set X) ∪
      {y : X | ∃ a ∈ V, a * t * a⁻¹ = y} ∪ {β₀} ⊆ (X₈ : Set X) := by
    rintro y ((h | ⟨a, ha, rfl⟩) | h)
    · exact hCX h
    · exact (mem_normalizer_iff.mp (hs.setup.normalizer_T_le_normalizer_X
        (hs.sylow_V.le ha)) t).mp htX
    · rw [Set.mem_singleton_iff.mp h]
      exact beta_mem_X i j
  have hX8 : (X₈ : Set X).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hs.setup.card_X
  have hCn : (((Y ⊓ centralizer ({t} : Set X) : Subgroup X)) : Set X).ncard =
      Nat.card ↥(Y ⊓ centralizer ({t} : Set X)) := (Nat.card_coe_set_eq _).symm
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hdisj2, Set.ncard_union_eq hdisj1, Set.ncard_singleton, hO4, hCn,
    hX8] at h1
  omega

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
