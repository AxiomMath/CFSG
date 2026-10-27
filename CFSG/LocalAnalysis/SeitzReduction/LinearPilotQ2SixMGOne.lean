module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFModule
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveMData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Data

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

@[expose] def LinearTwoSwapModuleData (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (c : Fin n)
    (W X : Subgroup G) : Prop :=
  (∀ w ∈ W, w * w = 1) ∧ Nat.card W = 2 ^ (2 * (n - 1)) ∧
    W ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical (K := K) c) ∧
    t ∈ normalizer (W : Set G) ∧
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (W : Set G) ∧
    ⁅X, X⁆ = X ∧ X ≤ normalizer (W : Set G) ∧ W ≤ normalizer (X : Set G) ∧
    ⁅X, X.map (MulAut.conj t).toMonoidHom⁆ ≤ W ∧ X ⊓ X.map (MulAut.conj t).toMonoidHom ≤ W ∧
    modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤
      (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W ∧
    W ⊓ centralizer (X : Set G) ≠ ⊥

theorem LinearTwoSwapModuleData.map_conj {e : L ≃* LinearFlag.projectiveSL n K} {t : G}
    {c : Fin n} {W X : Subgroup G} (h : LinearTwoSwapModuleData e t c W X) (ht : t * t = 1) :
    LinearTwoSwapModuleData e t c W (X.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨hW2, hWc, hWt, htW, hLW, hXp, hXW, hWX, hXY, hXYW, hD, hne⟩ := h
  have htt := map_conj_map_conj_eq_of_mul_self ht X
  have hconj : ∀ g ∈ normalizer (W : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (mem_normalizer_iff.1 hg w).1 hw
  refine ⟨hW2, hWc, hWt, htW, hLW, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_commutator, hXp]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem htW (hXW hx)) (inv_mem htW)
  · apply le_normalizer_of_mul_mul_inv_mem
    rintro w hw _ ⟨x, hx, rfl⟩
    have hu : t⁻¹ * w * t⁻¹⁻¹ ∈ W := hconj t⁻¹ (inv_mem htW) w hw
    rw [inv_inv] at hu
    have hux : (t⁻¹ * w * t) * x * (t⁻¹ * w * t)⁻¹ ∈ X :=
      (mem_normalizer_iff.1 (hWX hu) x).1 hx
    refine ⟨(t⁻¹ * w * t) * x * (t⁻¹ * w * t)⁻¹, hux, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [htt, commutator_comm]
    exact hXY
  · rw [htt, inf_comm]
    exact hXYW
  · rw [htt, sup_comm (X.map (MulAut.conj t).toMonoidHom)]
    exact hD
  · intro hbot
    apply hne
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwX⟩ := mem_inf.1 hw
    have h1 : t * w * t⁻¹ ∈ W ⊓ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G) := by
      refine mem_inf.2 ⟨hconj t htW w hwW, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hxw : x * w = w * x := mem_centralizer_iff.1 hwX x hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc t * x * t⁻¹ * (t * w * t⁻¹) = t * (x * w) * t⁻¹ := by group
        _ = t * (w * x) * t⁻¹ := by rw [hxw]
        _ = t * w * t⁻¹ * (t * x * t⁻¹) := by group
    rw [hbot, mem_bot] at h1
    rw [mem_bot]
    calc w = t⁻¹ * (t * w * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group

end Data

section GOne

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem exists_gOne_of_swapModuleData_of_levi (hset : SeitzSetting G L) (hn : 4 ≤ n)
    (hK : Nat.card K = 2) (e : Fin 2 → (L ≃* LinearFlag.projectiveSL n K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {c : Fin 2 → Fin n} (hc : c 0 ≠ c 1)
    (hlevi : ∀ i, modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) =
      modelToG (e 0) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))))
    {W X : Fin 2 → Subgroup G} (hdata : ∀ i, LinearTwoSwapModuleData (e i) t (c i) (W i) (X i))
    (h01 : (X 1).map (MulAut.conj t).toMonoidHom ≤ centralizer (X 0 : Set G)) :
    ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
      G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y := by
  choose hW2 hWc hWt htW hLW hXp hXW hWX hXY hXYW hD hne using hdata
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  have hDt : ∀ i, modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) ≤
      centralizer ({t} : Set G) := fun i x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC x (modelToG_le (e i) _ hx))
  have hW : ∀ i, ∀ v ∈ W i, ∀ w ∈ W i, v * w = w * v := fun i v hv w hw =>
    mul_comm_of_forall_mul_self_eq_one (hW2 i) hv hw
  have hirr : ∀ i, ∀ S : Subgroup G, S ≤ W i ⊓ centralizer ({t} : Set G) →
      modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) ≤ normalizer (S : Set G) →
      S = ⊥ ∨ S = W i ⊓ centralizer ({t} : Set G) := by
    intro i S hS hN
    rw [hWt i] at hS ⊢
    exact modelToG_pointRadical_irreducible hK (e i) (c i) hS hN
  have hVc : ∀ i, Nat.card (W i ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ (n - 1) :=
    fun i => card_inf_centralizer_eq_of_pointRadical hK (e i) (hWt i)
  have hnt : ∀ i, ¬ (W i ⊓ centralizer ({t} : Set G) ≤
      centralizer (modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) : Set G)) := by
    intro i
    have h4 : 4 < Nat.card (modelToG (e i) (pointRadical (K := K) (c i))) := by
      rw [← hWt i, hVc i]
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hWt i]
    exact not_modelToG_pointRadical_le_centralizer hK (e i) (c i) h4
  have hfix : ∀ i, W i ⊓ centralizer
      (modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) : Set G) = ⊥ := fun i =>
    inf_centralizer_eq_bot_of_irreducible (hW i) (hW2 i) htt (htW i) (hDt i) (hLW i) (hirr i)
      (hnt i)
  have hWV : ∀ i, Nat.card (W i) =
      Nat.card (W i ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    intro i
    rw [hWc i, hVc i, ← pow_mul, mul_comm]
  have hW1 : ∀ i, 1 < Nat.card (W i) := by
    intro i
    rw [hWc i]
    exact Nat.one_lt_two_pow (by omega)
  have hcard : ∀ i, Nat.card (W i ⊓ centralizer (X i : Set G) : Subgroup G) = 2 ^ (n - 1) := by
    intro i
    rw [← hVc i]
    exact card_inf_centralizer_eq_of_ne_bot_of_irreducible (hW i) (hW2 i) htt (htW i) (hDt i)
      (hLW i) (hirr i) (hXW i) (hXY i) (hD i) (hfix i) (hWV i) (hW1 i) (hne i)
  have hDp : ∀ i, ⁅modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))),
      modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n)))⁆ =
        modelToG (e i) (blockSL (K := K) ({c i}ᶜ : Finset (Fin n))) := by
    intro i
    have hcard3 : 3 ≤ (({c i}ᶜ : Finset (Fin n))).card := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
      omega
    rw [modelToG, ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      commutator_blockSL_eq_of_three_le hcard3]
  have hdec : ∀ i, ∀ w ∈ W i,
      ∃ w₁ ∈ W i ⊓ centralizer ((X i).map (MulAut.conj t).toMonoidHom : Set G),
        ∃ w₂ ∈ W i ⊓ centralizer (X i : Set G), w = w₁ * w₂ := fun i =>
    forall_eq_mul_of_card_inf_centralizer (hW i) (htW i)
      (by rw [hcard i, hWc i, ← pow_mul, Nat.mul_comm]) (hD i) (hfix i)
  have hfac := fun i => swapFactor_of_decomposition (hW i) (hXp i) (hXW i) (htW i) (hWX i)
    (hXY i) (hXYW i) (hdec i) (hDp i) (hD i) (hfix i)
  choose F hFA hFperf hFδ hFsurj using fun i =>
    exists_firstFactor_of_le_sup htt (hfac i).1 (hfac i).2.1 (hfac i).2.2 (hDt i) (hDp i)
  have hAt : ∀ i j, (X j).map (MulAut.conj t).toMonoidHom ≤ centralizer (X i : Set G) := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact (hfac 0).1
    · exact h01
    · exact map_conj_le_centralizer_comm htt h01
    · exact (hfac 1).1
  exact exists_gOne_of_firstFactors (by omega) (SeitzQ2.isSimpleGroup_of_seitzSetting hset) (e 0)
    hc hFperf
    (fun i j => (map_mono (hFA j)).trans ((hAt i j).trans (centralizer_le (hFA i))))
    (fun i x hx => by rw [← hlevi i]; exact hFδ i x hx)
    (fun i y hy => hFsurj i y (by rw [hlevi i]; exact hy))

end GOne

end CFSG.SeitzReduction.LinearPilot
