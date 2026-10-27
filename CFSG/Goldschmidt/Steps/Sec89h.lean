module

import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec89a
import CFSG.Goldschmidt.Steps.Sec89b
import CFSG.Goldschmidt.Steps.Sec89c
import CFSG.Goldschmidt.Steps.Sec89d
import CFSG.Goldschmidt.Steps.Sec89g
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem false_of_not_commutator_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hrank : CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3)
    (hL : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A → ∀ z ∈ (S : Subgroup G), z * t = t * z →
      z ^ 2 ∈ A → z ^ 2 = 1)
    (hDc : IsMulCommutative (⁅(S : Subgroup G), (S : Subgroup G)⁆ : Subgroup G))
    (hΩD : A = Omega1 ⁅(S : Subgroup G), (S : Subgroup G)⁆)
    (hD : ¬ ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) : False := by
  obtain ⟨x, hxS, hxC, b, hb⟩ := exists_mem_normalizer_pow hset h4
  have hxA := Sec8.normalizer_le_normalizer hset hxS
  obtain ⟨T₁, hT₁S, hAT₁, hST₁, hxT₁, hsq, hself, hinv, hfixT, hx3⟩ :=
    exists_T1_abelian hset h4 hL hDc hΩD hD hxS hxC hb
  obtain ⟨t, htS, ht2, htA, hmT⟩ :=
    exists_orbitProd_mem hset h4 hrank hxS hxA hxC hx3 hT₁S hST₁ hxT₁ hsq hfixT
  obtain ⟨K, hK⟩ := exists_ker hT₁S hST₁ hxS (commutator_mem_of_sq_mem hsq)
  have hKS : K ≤ (S : Subgroup G) := fun s hs => ((hK s).mp hs).1
  have htK : t ∈ K := (hK t).mpr ⟨htS, hmT⟩
  have hT₁K : T₁ ≤ K := fun w hw => (hK w).mpr ⟨hT₁S hw,
    T₁.mul_mem (T₁.mul_mem hw (conj_mem_of_mem_normalizer hxT₁ hw))
      (conj_mem_of_mem_normalizer hxT₁ (conj_mem_of_mem_normalizer hxT₁ hw))⟩
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := Sec8.mem_normalizer_of_conj_le fun k hk => by
    have hkS := hKS hk
    refine (hK _).mpr ⟨conj_mem_of_mem_normalizer hxS hkS, ?_⟩
    have e : orbitProd x (x⁻¹ * k * x) = k⁻¹ * orbitProd x k * k := by
      calc orbitProd x (x⁻¹ * k * x) = (x⁻¹ * k * x) * (x⁻¹ * (x⁻¹ * k * x) * x) *
            (x⁻¹ * (x⁻¹ * (x⁻¹ * k * x) * x) * x) := rfl
        _ = (x⁻¹ * k * x) * (x⁻¹ * (x⁻¹ * k * x) * x) * k := by rw [hx3 k hkS]
        _ = k⁻¹ * orbitProd x k * k := by simp only [orbitProd]; group
    rw [e]
    exact conj_mem_of_mem_normalizer (hST₁ hkS) ((hK k).mp hk).2
  have hfixK : ∀ k ∈ K, x⁻¹ * k * x = k → k = 1 := by
    intro k hk hkx
    have hkS := hKS hk
    have hm := ((hK k).mp hk).2
    have e : orbitProd x k = k ^ 2 * k := by
      simp only [orbitProd, hkx]
      rw [pow_two]
    have hkT : k ∈ T₁ := by
      have e2 : k = (k ^ 2)⁻¹ * orbitProd x k := by rw [e]; group
      rw [e2]
      exact T₁.mul_mem (T₁.inv_mem (hsq k hkS)) hm
    exact hfixT k hkT hkx
  set φ : MulAut K := K.normalizerMonoidHom ⟨x⁻¹, Subgroup.inv_mem _ hxK⟩ with hφ
  have hφapp : ∀ k : K, ((φ k : K) : G) = x⁻¹ * k * x := fun k => by
    change x⁻¹ * k * x⁻¹⁻¹ = x⁻¹ * k * x
    rw [inv_inv]
  have hneu : ∀ a ∈ K, ∀ c ∈ K, ∀ k ∈ K,
      (a⁻¹ * c⁻¹ * a * c) * k = k * (a⁻¹ * c⁻¹ * a * c) := by
    intro a ha c hc k hk
    have h := commute_kappa_of_fixedPointFree φ
      (fun q hq => Subtype.ext (hfixK q q.2 ((hφapp q).symm.trans (congrArg Subtype.val hq))))
      (fun q => Subtype.ext (by rw [hφapp, hφapp, hφapp]; exact hx3 q (hKS q.2)))
      ⟨a, ha⟩ ⟨c, hc⟩ ⟨k, hk⟩
    exact congrArg Subtype.val h.eq
  have hZK : ∀ c ∈ K, (∀ k ∈ K, c * k = k * c) → c ∈ A := by
    have key := mem_of_forall_sq (A := A) (Z := {c | c ∈ K ∧ ∀ k ∈ K, c * k = k * c})
      (fun c hc => ⟨K.pow_mem hc.1 2, fun k hk =>
        (Commute.pow_left (show Commute c k from hc.2 k hk) 2).eq⟩)
      (fun c hc hc2 => hinv c (hself c (hKS hc.1) fun w hw => (hc.2 w (hT₁K hw)).symm) hc2)
      (fun c hc hc2 => hL t htS ht2 htA c (hKS hc.1) (hc.2 t htK) hc2)
    intro c hc hcc
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨c, hKS hc⟩
    exact key k c ⟨hc, hcc⟩ (by simpa using congrArg Subtype.val hk)
  have hyK : (x⁻¹ * t * x) * (x⁻¹ * (x⁻¹ * t * x) * x) ∈ K :=
    K.mul_mem (conj_mem_of_mem_normalizer hxK htK)
      (conj_mem_of_mem_normalizer hxK (conj_mem_of_mem_normalizer hxK htK))
  have hmA : (orbitProd x t)⁻¹ * (x⁻¹ * orbitProd x t * x) ∈ A := by
    have e : (orbitProd x t)⁻¹ * (x⁻¹ * orbitProd x t * x) =
        ((x⁻¹ * t * x) * (x⁻¹ * (x⁻¹ * t * x) * x))⁻¹ * t⁻¹ *
          ((x⁻¹ * t * x) * (x⁻¹ * (x⁻¹ * t * x) * x)) * t := by
      have e1 : (orbitProd x t)⁻¹ * (x⁻¹ * orbitProd x t * x) =
          ((x⁻¹ * t * x) * (x⁻¹ * (x⁻¹ * t * x) * x))⁻¹ * t⁻¹ *
            ((x⁻¹ * t * x) * (x⁻¹ * (x⁻¹ * t * x) * x)) *
              (x⁻¹ * (x⁻¹ * (x⁻¹ * t * x) * x) * x) := by
        simp only [orbitProd]; group
      rw [e1, hx3 t htS]
    rw [e]
    exact hZK _ (K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hyK) (K.inv_mem htK)) hyK) htK)
      fun k hk => hneu _ hyK t htK k hk
  obtain ⟨a, haA, hax⟩ :=
    exists_mul_conj_eq hxA (fun c hc hcx => eq_one_of_conj_eq hset h4 hxA hxC hc hcx) hmA
  have hma1 : orbitProd x t * a = 1 := hfixT _ (T₁.mul_mem hmT (hAT₁ haA)) hax
  have hm : orbitProd x t ∈ A := by
    rw [eq_inv_of_mul_eq_one_left hma1]
    exact A.inv_mem haA
  exact false_of_mul_conj_mem hset h4 hrank hxS hxA htS ht2 htA hm

end CFSG.Goldschmidt.Sec89
