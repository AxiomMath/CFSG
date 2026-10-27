module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFSplit
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBLevi

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

section Module

variable {G : Type*} [Group G] {W D : Subgroup G} {t : G}

@[expose] noncomputable def tMulConjHom (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (htW : t ∈ normalizer (W : Set G)) {S : Subgroup G} (hSW : S ≤ W) : S →* G where
  toFun s := (s : G) * (t * s * t⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have hta : t * (a : G) * t⁻¹ ∈ W := (mem_normalizer_iff.1 htW a).1 (hSW a.2)
    have hc : (b : G) * (t * a * t⁻¹) = (t * a * t⁻¹) * b := hW _ (hSW b.2) _ hta
    simp only [Subgroup.coe_mul]
    calc (a : G) * b * (t * (a * b) * t⁻¹)
        = a * ((b : G) * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
      _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group

theorem tMulConjHom_apply (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (htW : t ∈ normalizer (W : Set G)) {S : Subgroup G} (hSW : S ≤ W) (s : S) :
    tMulConjHom hW htW hSW s = (s : G) * (t * s * t⁻¹) :=
  rfl

theorem tMulConjHom_mem (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) {S : Subgroup G} (hSW : S ≤ W) (s : S) :
    tMulConjHom hW htW hSW s ∈ W ⊓ centralizer ({t} : Set G) := by
  rw [tMulConjHom_apply]
  have hsW : (s : G) ∈ W := hSW s.2
  have hta : t * (s : G) * t⁻¹ ∈ W := (mem_normalizer_iff.1 htW s).1 hsW
  refine mem_inf.2 ⟨W.mul_mem hsW hta, ?_⟩
  rw [mem_centralizer_singleton_iff]
  have hc : (s : G) * (t * s * t⁻¹) = (t * s * t⁻¹) * s := hW _ hsW _ hta
  have h2 : t * (t * (s : G) * t⁻¹) * t⁻¹ = s := by
    calc t * (t * (s : G) * t⁻¹) * t⁻¹ = (t * t) * s * (t * t)⁻¹ := by group
      _ = s := by rw [ht, one_mul, inv_one, mul_one]
  have h3 : t * ((s : G) * (t * s * t⁻¹)) * t⁻¹ = (s : G) * (t * s * t⁻¹) := by
    calc t * ((s : G) * (t * s * t⁻¹)) * t⁻¹
        = (t * s * t⁻¹) * (t * (t * (s : G) * t⁻¹) * t⁻¹) := by group
      _ = (t * s * t⁻¹) * s := by rw [h2]
      _ = (s : G) * (t * s * t⁻¹) := hc.symm
  calc (s : G) * (t * s * t⁻¹) * t = (t * ((s : G) * (t * s * t⁻¹)) * t⁻¹) * t := by rw [h3]
    _ = t * ((s : G) * (t * s * t⁻¹)) := by group

theorem mem_ker_tMulConjHom_iff (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (hW2 : ∀ w ∈ W, w * w = 1) (htW : t ∈ normalizer (W : Set G)) {S : Subgroup G}
    (hSW : S ≤ W) (s : S) :
    s ∈ (tMulConjHom hW htW hSW).ker ↔ (s : G) ∈ centralizer ({t} : Set G) := by
  rw [MonoidHom.mem_ker, tMulConjHom_apply, mem_centralizer_singleton_iff]
  have hsinv : (s : G)⁻¹ = s := inv_eq_of_mul_eq_one_right (hW2 s (hSW s.2))
  constructor
  · intro h
    have h1 : t * (s : G) * t⁻¹ = s := by rw [eq_inv_of_mul_eq_one_right h, hsinv]
    calc (s : G) * t = t * s * t⁻¹ * t := by rw [h1]
      _ = t * s := by group
  · intro h
    have h1 : t * (s : G) * t⁻¹ = s := by rw [← h]; group
    rw [h1]
    exact hW2 s (hSW s.2)

theorem le_normalizer_inf_of_le_normalizer {A B C : Subgroup G} (hB : A ≤ normalizer (B : Set G))
    (hC : A ≤ normalizer (C : Set G)) : A ≤ normalizer ((B ⊓ C : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro a ha g hg
  obtain ⟨hgB, hgC⟩ := mem_inf.1 hg
  exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hB ha) g).1 hgB, (mem_normalizer_iff.1 (hC ha) g).1 hgC⟩

theorem le_normalizer_centralizer_self' {A : Subgroup G} :
    A ≤ normalizer ((centralizer (A : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro a ha g hg
  rw [mem_centralizer_iff.1 hg a ha, mul_inv_cancel_right]
  exact hg

theorem le_normalizer_inf_centralizer_singleton (hDt : D ≤ centralizer ({t} : Set G))
    (hDW : D ≤ normalizer (W : Set G)) :
    D ≤ normalizer ((W ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_of_mul_mul_inv_mem
  intro d hd g hg
  obtain ⟨hgW, hgt⟩ := mem_inf.1 hg
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hDW hd) g).1 hgW, ?_⟩
  rw [mem_centralizer_singleton_iff] at hgt ⊢
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 (hDt hd)
  calc d * g * d⁻¹ * t = d * g * (d⁻¹ * (t * d)) * d⁻¹ := by group
    _ = d * g * (d⁻¹ * (d * t)) * d⁻¹ := by rw [hdt]
    _ = d * (g * t) * d⁻¹ := by group
    _ = d * (t * g) * d⁻¹ := by rw [hgt]
    _ = (d * t) * g * d⁻¹ := by group
    _ = (t * d) * g * d⁻¹ := by rw [hdt]
    _ = t * (d * g * d⁻¹) := by group

theorem card_eq_of_le_normalizer_of_irreducible [Finite G]
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hW2 : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) (hDt : D ≤ centralizer ({t} : Set G))
    (hDW : D ≤ normalizer (W : Set G))
    (hirr : ∀ S : Subgroup G, S ≤ W ⊓ centralizer ({t} : Set G) → D ≤ normalizer (S : Set G) →
      S = ⊥ ∨ S = W ⊓ centralizer ({t} : Set G))
    {S : Subgroup G} (hSW : S ≤ W) (hDS : D ≤ normalizer (S : Set G)) :
    Nat.card S = 1 ∨ Nat.card S = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ∨
      Nat.card S = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
  set V := W ⊓ centralizer ({t} : Set G) with hV
  have hcard := Subgroup.card_ker_mul_card_range (tMulConjHom hW htW hSW)
  have hker : (tMulConjHom hW htW hSW).ker.map S.subtype = S ⊓ V := by
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_inf.2 ⟨s.2, mem_inf.2 ⟨hSW s.2, (mem_ker_tMulConjHom_iff hW hW2 htW hSW s).1 hs⟩⟩
    · intro hg
      obtain ⟨hgS, hgV⟩ := mem_inf.1 hg
      exact ⟨⟨g, hgS⟩, (mem_ker_tMulConjHom_iff hW hW2 htW hSW ⟨g, hgS⟩).2 (mem_inf.1 hgV).2, rfl⟩
  have hkc : Nat.card (tMulConjHom hW htW hSW).ker = Nat.card (S ⊓ V : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective S.subtype_injective]
  have hDV : D ≤ normalizer (V : Set G) := le_normalizer_inf_centralizer_singleton hDt hDW
  have h1 := hirr (S ⊓ V) inf_le_right (le_normalizer_inf_of_le_normalizer hDS hDV)
  have hRV : (tMulConjHom hW htW hSW).range ≤ V := by
    rintro _ ⟨s, rfl⟩
    exact tMulConjHom_mem hW ht htW hSW s
  have hDR : D ≤ normalizer ((tMulConjHom hW htW hSW).range : Set G) := by
    apply le_normalizer_of_mul_mul_inv_mem
    rintro d hd _ ⟨s, rfl⟩
    have hds : d * s * d⁻¹ ∈ S := (mem_normalizer_iff.1 (hDS hd) s).1 s.2
    refine ⟨⟨d * s * d⁻¹, hds⟩, ?_⟩
    have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 (hDt hd)
    show (d * s * d⁻¹) * (t * (d * s * d⁻¹) * t⁻¹) = d * ((s : G) * (t * s * t⁻¹)) * d⁻¹
    calc (d * s * d⁻¹) * (t * (d * s * d⁻¹) * t⁻¹)
        = (d * s * d⁻¹) * ((t * d) * s * (t * d)⁻¹) := by group
      _ = (d * s * d⁻¹) * ((d * t) * s * (d * t)⁻¹) := by rw [hdt]
      _ = d * ((s : G) * (t * s * t⁻¹)) * d⁻¹ := by group
  have h2 := hirr _ hRV hDR
  rw [← hcard, hkc]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
  · left
    simp
  · right; left
    simp
  · right; left
    simp
  · right; right
    rw [sq]

theorem inf_centralizer_eq_bot_of_irreducible
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hW2 : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) (hDt : D ≤ centralizer ({t} : Set G))
    (hDW : D ≤ normalizer (W : Set G))
    (hirr : ∀ S : Subgroup G, S ≤ W ⊓ centralizer ({t} : Set G) → D ≤ normalizer (S : Set G) →
      S = ⊥ ∨ S = W ⊓ centralizer ({t} : Set G))
    (hnt : ¬ (W ⊓ centralizer ({t} : Set G) ≤ centralizer (D : Set G))) :
    W ⊓ centralizer (D : Set G) = ⊥ := by
  set V := W ⊓ centralizer ({t} : Set G) with hV
  have hDV : D ≤ normalizer (V : Set G) := le_normalizer_inf_centralizer_singleton hDt hDW
  have hCV : V ⊓ centralizer (D : Set G) = ⊥ := by
    rcases hirr (V ⊓ centralizer (D : Set G)) inf_le_left
      (le_normalizer_inf_of_le_normalizer hDV le_normalizer_centralizer_self') with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hnt
  rw [eq_bot_iff, ← hCV]
  intro g hg
  obtain ⟨hgW, hgD⟩ := mem_inf.1 hg
  have hle : W ⊓ centralizer (D : Set G) ≤ W := inf_le_left
  have hψ := tMulConjHom_mem hW ht htW hle ⟨g, hg⟩
  have hψD : tMulConjHom hW htW hle ⟨g, hg⟩ ∈ centralizer (D : Set G) := by
    rw [tMulConjHom_apply]
    refine mul_mem hgD ?_
    rw [mem_centralizer_iff]
    intro d hd
    have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 (hDt hd)
    have hdg : d * g = g * d := mem_centralizer_iff.1 hgD d hd
    calc d * (t * g * t⁻¹) = (d * t) * g * t⁻¹ := by group
      _ = (t * d) * g * t⁻¹ := by rw [hdt]
      _ = t * (d * g) * t⁻¹ := by group
      _ = t * (g * d) * t⁻¹ := by rw [hdg]
      _ = t * g * (t⁻¹ * (t * d)) * t⁻¹ := by group
      _ = t * g * (t⁻¹ * (d * t)) * t⁻¹ := by rw [hdt]
      _ = t * g * t⁻¹ * d := by group
  have h1 : tMulConjHom hW htW hle ⟨g, hg⟩ = 1 := by
    have h := mem_inf.2 ⟨hψ, hψD⟩
    rw [hCV, mem_bot] at h
    exact h
  have hgt := (mem_ker_tMulConjHom_iff hW hW2 htW hle ⟨g, hg⟩).1 h1
  exact mem_inf.2 ⟨mem_inf.2 ⟨hgW, hgt⟩, hgD⟩

theorem card_inf_centralizer_eq_of_ne_bot_of_irreducible [Finite G] {X : Subgroup G}
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (hW2 : ∀ w ∈ W, w * w = 1) (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set G)) (hDt : D ≤ centralizer ({t} : Set G))
    (hDW : D ≤ normalizer (W : Set G))
    (hirr : ∀ S : Subgroup G, S ≤ W ⊓ centralizer ({t} : Set G) → D ≤ normalizer (S : Set G) →
      S = ⊥ ∨ S = W ⊓ centralizer ({t} : Set G))
    (hXW : X ≤ normalizer (W : Set G)) (hXY : ⁅X, X.map (MulAut.conj t).toMonoidHom⁆ ≤ W)
    (hD : D ≤ (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W)
    (hfix : W ⊓ centralizer (D : Set G) = ⊥)
    (hWc : Nat.card W = Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2)
    (hW1 : 1 < Nat.card W) (hne : W ⊓ centralizer (X : Set G) ≠ ⊥) :
    Nat.card (W ⊓ centralizer (X : Set G) : Subgroup G) =
      Nat.card (W ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have hYW : X.map (MulAut.conj t).toMonoidHom ≤ normalizer (W : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem htW (hXW hx)) (inv_mem htW)
  have hDS : D ≤ normalizer ((W ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
    refine hD.trans (sup_le (sup_le le_normalizer_inf_centralizer_self ?_) ?_)
    · exact le_normalizer_inf_centralizer_of_commutator_le hW hYW (by rw [commutator_comm]; exact hXY)
    · apply le_normalizer_of_mul_mul_inv_mem
      intro w hw g hg
      rw [hW w hw g (mem_inf.1 hg).1, mul_inv_cancel_right]
      exact hg
  rcases card_eq_of_le_normalizer_of_irreducible hW hW2 ht htW hDt hDW hirr inf_le_left hDS with
    h | h | h
  · exact absurd (Subgroup.card_eq_one.1 h) hne
  · exact h
  · exfalso
    have hSW : W ⊓ centralizer (X : Set G) = W :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hWc])
    have hWX : W ≤ centralizer (X : Set G) := hSW ▸ inf_le_right
    have hWY : W ≤ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G) := by
      intro w hw
      rw [mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hu : t⁻¹ * w * t⁻¹⁻¹ ∈ W := (mem_normalizer_iff.1 (inv_mem htW) w).1 hw
      rw [inv_inv] at hu
      have hxu : x * (t⁻¹ * w * t) = (t⁻¹ * w * t) * x := mem_centralizer_iff.1 (hWX hu) x hx
      calc t * x * t⁻¹ * w = t * (x * (t⁻¹ * w * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * w * t) * x) * t⁻¹ := by rw [hxu]
        _ = w * (t * x * t⁻¹) := by group
    have hWD : W ≤ W ⊓ centralizer (D : Set G) := fun w hw =>
      mem_inf.2 ⟨hw, mem_centralizer_of_le_sup_sup hW hD hw (hWX hw) (hWY hw)⟩
    rw [hfix] at hWD
    have h1 : Nat.card W = 1 := by
      rw [le_bot_iff.1 hWD, Subgroup.card_bot]
    omega

end Module

section Model

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem modelToG_pointRadical_irreducible {n : ℕ} (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n) {S : Subgroup G}
    (hS : S ≤ modelToG e (pointRadical (K := K) c))
    (hN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) ≤ normalizer (S : Set G)) :
    S = ⊥ ∨ S = modelToG e (pointRadical (K := K) c) := by
  rcases Subgroup.bot_or_exists_ne_one S with h | ⟨s, hsS, hs1⟩
  · exact Or.inl h
  right
  refine le_antisymm hS fun g hg => ?_
  obtain ⟨v, hv, rfl⟩ := (mem_modelToG e).1 (hS hsS)
  obtain ⟨w, hw, rfl⟩ := (mem_modelToG e).1 hg
  have hv1 : v ≠ 1 := fun h => hs1 (by rw [h, map_one, Subgroup.coe_one])
  by_cases hw1 : w = 1
  · rw [hw1, map_one, Subgroup.coe_one]
    exact S.one_mem
  obtain ⟨l, hl, hlvw⟩ := exists_mem_blockSL_conj_eq_of_mem_pointRadical hK c hv hw hv1 hw1
  rw [← hlvw, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact (mem_normalizer_iff.1 (hN (symm_mem_modelToG e hl)) _).1 hsS

theorem not_modelToG_pointRadical_le_centralizer [Finite G] {n : ℕ} (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (c : Fin n)
    (hcard : 4 < Nat.card (modelToG e (pointRadical (K := K) c))) :
    ¬ (modelToG e (pointRadical (K := K) c) ≤
      centralizer (modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin n))) : Set G)) := by
  intro hle
  obtain ⟨v₁, hv₁, v₂, hv₂, -, -, h1, h2, h21, -⟩ := exists_three_of_four_lt hcard
  obtain ⟨a, ha, rfl⟩ := (mem_modelToG e).1 hv₁
  obtain ⟨b, hb, rfl⟩ := (mem_modelToG e).1 hv₂
  have ha1 : a ≠ 1 := fun h => h1 (by rw [h, map_one, Subgroup.coe_one])
  have hb1 : b ≠ 1 := fun h => h2 (by rw [h, map_one, Subgroup.coe_one])
  obtain ⟨l, hl, hlab⟩ := exists_mem_blockSL_conj_eq_of_mem_pointRadical hK c ha hb ha1 hb1
  have hcomm := mem_centralizer_iff.1 (hle hv₁) _ (symm_mem_modelToG e hl)
  apply h21
  rw [← hlab, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    hcomm, mul_inv_cancel_right]

end Model

end CFSG.SeitzReduction.LinearPilot
