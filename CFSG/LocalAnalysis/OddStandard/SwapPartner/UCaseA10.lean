module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLShape
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UAction
import CFSG.LocalAnalysis.OddStandard.SwapPartner.TrichotomySetup
import CFSG.LocalAnalysis.OddStandard.SwapPartner.USylow

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

theorem card_le_two_of_isPGroup_centralizer {X : Type*} [Group X] [Finite X] {t : X}
    {Sg V K : Subgroup X} (h : SwapShape t Sg V) [K.Normal] [Group.IsPerfect K]
    (hAK : ⁅Sg, Sg⁆ ≤ K) (hne : ⁅Sg, Sg⁆ ≠ K)
    (h4 : ∀ U : Subgroup X, IsPGroup 2 U →
      U ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) → Nat.card U ≤ 4) :
    ∀ U : Subgroup X, IsPGroup 2 U → U ≤ centralizer (K : Set X) → Nat.card U ≤ 2 := by
  intro U hU hUK
  by_contra hnot
  rw [not_le] at hnot
  have hUY : U ≤ centralizer (((⁅Sg, Sg⁆ : Subgroup X)) : Set X) :=
    hUK.trans (Subgroup.centralizer_le hAK)
  have hU4 : Nat.card U ≤ 4 := h4 U hU hUY
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
  have hle : n ≤ 2 :=
    (Nat.pow_le_pow_iff_right (show (1 : ℕ) < 2 by norm_num)).mp (by
      rw [← hn, hpow]
      exact hU4)
  have hgt : 2 < 2 ^ n := by rw [← hn]; exact hnot
  have hn2 : n = 2 := by
    interval_cases n
    · norm_num at hgt
    · norm_num at hgt
    · rfl
  have hUcard : Nat.card U = 4 := by rw [hn, hn2]; norm_num
  have hVY : V ≤ centralizer (((⁅Sg, Sg⁆ : Subgroup X)) : Set X) := by
    rw [← h.centralizer_abar_inf_centralizer]
    exact inf_le_left
  have hVcard : Nat.card ↥V = 2 ^ 2 := by rw [h.card_v, hpow]
  have hmax : ∀ Q : Subgroup X, IsPGroup 2 Q →
      Q ≤ centralizer (((⁅Sg, Sg⁆ : Subgroup X)) : Set X) → Nat.card ↥Q ≤ 2 ^ 2 := by
    intro Q hQ hQY
    rw [hpow]
    exact h4 Q hQ hQY
  obtain ⟨c, hcY, hconj⟩ := exists_conj_le_of_forall_card_le (G := X)
    (Y := centralizer (((⁅Sg, Sg⁆ : Subgroup X)) : Set X)) (D := V) (U := U) (k := 2)
    hVY hVcard hmax hU hUY
  have hmap_le : U.map (MulAut.conj c).toMonoidHom ≤ V := by
    intro x hx
    obtain ⟨u, hu, hfu⟩ := Subgroup.mem_map.mp hx
    rw [← hfu]
    exact hconj u hu
  have hcard_map : Nat.card (U.map (MulAut.conj c).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hUcard]
  have hmap_eq : U.map (MulAut.conj c).toMonoidHom = V :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by rw [h.card_v, hcard_map])
  have htmap : t ∈ U.map (MulAut.conj c).toMonoidHom := by rw [hmap_eq]; exact h.mem_v
  obtain ⟨u0, hu0U, hu0eq⟩ := Subgroup.mem_map.mp htmap
  have hu0 : c * u0 * c⁻¹ = t := hu0eq
  have hK'C : K.map (MulAut.conj c).toMonoidHom ≤ centralizer ({t} : Set X) := by
    intro x hx
    obtain ⟨k, hk, hkf⟩ := Subgroup.mem_map.mp hx
    rw [← hkf, Subgroup.mem_centralizer_singleton_iff]
    have hkcomm : k * u0 = u0 * k :=
      Subgroup.mem_centralizer_iff.mp (hUK hu0U) k hk
    calc (MulAut.conj c).toMonoidHom k * t
        = c * k * c⁻¹ * t := by rfl
      _ = c * k * c⁻¹ * (c * u0 * c⁻¹) := by rw [← hu0]
      _ = c * (k * u0) * c⁻¹ := by group
      _ = c * (u0 * k) * c⁻¹ := by rw [hkcomm]
      _ = c * u0 * c⁻¹ * (c * k * c⁻¹) := by group
      _ = t * (MulAut.conj c).toMonoidHom k := by rw [← hu0]; rfl
  haveI hK'perf : Group.IsPerfect (K.map (MulAut.conj c).toMonoidHom) :=
    Group.IsPerfect.map (f := (MulAut.conj c).toMonoidHom)
  have hK'comm : ⁅K.map (MulAut.conj c).toMonoidHom,
      K.map (MulAut.conj c).toMonoidHom⁆ = K.map (MulAut.conj c).toMonoidHom :=
    Subgroup.commutator_eq_self
  have hK'le : K.map (MulAut.conj c).toMonoidHom ≤ ⁅Sg, Sg⁆ := by
    rw [← hK'comm]
    calc ⁅K.map (MulAut.conj c).toMonoidHom, K.map (MulAut.conj c).toMonoidHom⁆
        ≤ ⁅centralizer ({t} : Set X), centralizer ({t} : Set X)⁆ :=
          Subgroup.commutator_mono hK'C hK'C
      _ = ⁅Sg, Sg⁆ := h.commutator_centralizer_eq
  have hKA : K ≤ ⁅Sg, Sg⁆ := by
    intro k hk
    have hkmap : c * k * c⁻¹ ∈ K.map (MulAut.conj c).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hk
    have hkA : c * k * c⁻¹ ∈ ⁅Sg, Sg⁆ := hK'le hkmap
    have hfix : c⁻¹ * (c * k * c⁻¹) * c = c * k * c⁻¹ := by
      have hca : (c * k * c⁻¹) * c = c * (c * k * c⁻¹) :=
        Subgroup.mem_centralizer_iff.mp hcY (c * k * c⁻¹) hkA
      calc c⁻¹ * (c * k * c⁻¹) * c
          = c⁻¹ * ((c * k * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * k * c⁻¹)) := by rw [hca]
        _ = c * k * c⁻¹ := by group
    have hk_eq : k = c * k * c⁻¹ := by
      rw [← hfix]
      group
    rw [hk_eq]
    exact hkA
  exact hne (le_antisymm hAK hKA)

theorem false_of_alternating_ten {X : Type} [Group X] [Finite X] {t : X} {Sg V K : Subgroup X}
    (h : SwapShape t Sg V) [K.Normal] [Group.IsPerfect K] (hAK : ⁅Sg, Sg⁆ ≤ K)
    (hne : ⁅Sg, Sg⁆ ≠ K) (e : (↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 10))
    (h4 : ∀ U : Subgroup X, IsPGroup 2 U →
      U ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup X) : Set X) → Nat.card U ≤ 4)
    (h10 : 2 ^ 10 ∣ Nat.card X) : False := by
  refine false_of_alternating_action (D := K) (n := 10) (b := 1) (k := 10)
    (by norm_num) (by norm_num) e ?_ h10 ?_
  · intro U hU hUK
    have hlt : Nat.card U ≤ 2 :=
      card_le_two_of_isPGroup_centralizer h hAK hne h4 U hU hUK
    simpa using hlt
  · rw [padicValNat_two_factorial_ten]
    norm_num

end CFSG.OddStandard.AltStdSec.SwapPartner
