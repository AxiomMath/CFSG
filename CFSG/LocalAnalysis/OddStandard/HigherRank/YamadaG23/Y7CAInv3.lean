module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAInv1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAInv2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CANo3c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CASuz

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Pointwise commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

theorem y7c_two_fixed_false (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hKt : conjSub t K = K) {g₂ : Γ}
    (hne : conjSub g₂ K ≠ K) : False := by
  classical
  have hK₂ : CFSG.IsComponent (conjSub g₂ K) := y7c_isComponent_conjSub hK g₂
  have hall : ∀ g : Γ, conjSub g K = K ∨ conjSub g K = conjSub g₂ K :=
    fun g => y7c_conj_cases c hK hJK hne g
  have hK₂t : conjSub t (conjSub g₂ K) = conjSub g₂ K := by
    rcases hall (t * g₂) with h | h
    · exfalso
      apply hne
      calc conjSub g₂ K = conjSub t (conjSub t (conjSub g₂ K)) :=
            (y7c_conjSub_conjSub_of_sq c.t_sq (conjSub g₂ K)).symm
        _ = conjSub t (conjSub (t * g₂) K) := by rw [y7c_conjSub_mul]
        _ = conjSub t K := by rw [h]
        _ = K := hKt
    · rw [← y7c_conjSub_mul t g₂ K]
      exact h
  have hX : ∀ x ∈ conjSub g₂ K, t * x * t⁻¹ ∈ conjSub g₂ K := by
    intro x hx
    have hmem : t * x * t⁻¹ ∈ conjSub t (conjSub g₂ K) := y7c_mul_mem_conjSub hx
    rwa [hK₂t] at hmem
  obtain ⟨W, hW_sylow, hWt⟩ := y7c_exists_inv_sylow c.t_sq hX
  have hW2 : IsPGroup 2 ↥W := hW_sylow.2.1
  set W' : Subgroup Γ := W ⊔ Subgroup.zpowers t with hW'def
  have hW'2 : IsPGroup 2 ↥W' := by
    rw [hW'def]
    exact y7c_two_group_join c.t_sq hW2 hWt
  have htW' : t ∈ W' := by
    rw [hW'def]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  set t' : ↥W' := ⟨t, htW'⟩ with ht'def
  have ht'sq : t' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [ht'def, pow_two] using c.t_sq
  have ht'ne : t' ≠ 1 := by
    intro h
    exact c.t_ne (by
      have := congrArg (fun x : ↥W' => (x : Γ)) h
      simpa [ht'def] using this)
  have hmem : ∀ x : ↥(centralizer ({t'} : Set ↥W')), ((x : ↥W') : Γ) ∈ Q := by
    intro x
    have hxcomm : (x : ↥W') ∈ centralizer ({t'} : Set ↥W') := x.2
    have hxcomm' : ((x : ↥W') : Γ) * t = t * ((x : ↥W') : Γ) := by
      have h1 := (Subgroup.mem_centralizer_iff.mp hxcomm) t' (by simp)
      exact (congrArg (fun y : ↥W' => (y : Γ)) h1).symm
    have ht_inv : t⁻¹ = t := by
      have htt : t * t = 1 := by simpa [pow_two] using c.t_sq
      exact inv_eq_of_mul_eq_one_right htt
    have ht_normW : t ∈ Subgroup.normalizer W := by
      rw [Subgroup.mem_normalizer_iff'']
      intro y
      constructor
      · intro hy
        simpa [ht_inv] using hWt y hy
      · intro hy
        have h := hWt (t⁻¹ * y * t) hy
        convert h using 1
        group
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers t) W
      (Subgroup.zpowers_le.mpr ht_normW)
    have hxprod : ((x : ↥W') : Γ) ∈ (Subgroup.zpowers t : Set Γ) * (W : Set Γ) := by
      rw [← hcoe]
      rw [sup_comm]
      exact (x : ↥W').2
    rw [Set.mem_mul] at hxprod
    obtain ⟨s, hs, w, hw, hsw⟩ := hxprod
    rw [← hsw] at hxcomm' ⊢
    have hst : s * t = t * s := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      calc t ^ n * t = t ^ (n + 1) := by rw [zpow_add, zpow_one]
        _ = t ^ (1 + n) := by rw [add_comm]
        _ = t * t ^ n := by rw [zpow_add, zpow_one]
    have hwt : w * t = t * w := by
      have h1 : s * (w * t) = s * (t * w) := by
        calc s * (w * t) = s * w * t := (mul_assoc s w t).symm
          _ = t * (s * w) := hxcomm'
          _ = t * s * w := (mul_assoc t s w).symm
          _ = s * t * w := by rw [← hst]
          _ = s * (t * w) := mul_assoc s t w
      exact mul_left_cancel h1
    exact Q.mul_mem ((Subgroup.zpowers_le.mpr c.t_mem_Q) hs)
      (y7c_cent_K₂_le_Q c hK hJK hKt hK₂ hne (hW_sylow.1 hw) hwt)
  have hcent_le : Nat.card ↥(centralizer ({t'} : Set ↥W')) ≤ 4 := by
    have hinj : Function.Injective
        (fun x : ↥(centralizer ({t'} : Set ↥W')) =>
          (⟨((x : ↥W') : Γ), hmem x⟩ : ↥Q)) := by
      intro x y hxy
      have hval : ((x : ↥W') : Γ) = ((y : ↥W') : Γ) :=
        congrArg (fun z : ↥Q => (z : Γ)) hxy
      exact Subtype.ext (Subtype.ext hval)
    calc Nat.card ↥(centralizer ({t'} : Set ↥W'))
        ≤ Nat.card ↥Q := Nat.card_le_card_of_injective _ hinj
      _ ≤ 4 := c.Q_card
  have hM6_le_K : M6 ≤ K := y7c_M6_le_K c hK hJK hKt hK₂ hne hall
  have hM6_2 : IsPGroup 2 ↥M6 := by
    rw [IsPGroup.iff_card]
    exact ⟨4, c.M6_E.2⟩
  obtain ⟨h, hhW⟩ := y7c_exists_conj_le_sylow (X := K) (E := M6) (W := W) g₂ hW_sylow
    hM6_le_K hM6_2
  set E : Subgroup Γ := conjSub h M6 with hEdef
  have hE_le_W : E ≤ W := by rw [hEdef]; exact hhW
  have hE_le_W' : E ≤ W' := hE_le_W.trans (by rw [hW'def]; exact le_sup_left)
  have hEcard : Nat.card ↥E = 16 := by
    rw [hEdef, y7c_card_conjSub, c.M6_E.2]
    norm_num
  have hm6sq : ∀ m ∈ M6, m * m = 1 := by
    intro m hm
    have hx : (⟨m, hm⟩ : ↥M6) ^ 2 = 1 := c.M6_E.1.2 _ (Subgroup.mem_top _)
    have := congrArg (fun z : ↥M6 => (z : Γ)) hx
    simpa [pow_two] using this
  have hEsq : ∀ y ∈ E.subgroupOf W', y * y = 1 := by
    intro y hy
    have hyE : (y : Γ) ∈ E := hy
    rw [hEdef, y7c_mem_conjSub] at hyE
    apply Subtype.ext
    show (y : Γ) * (y : Γ) = 1
    have hm2 : (h⁻¹ * (y : Γ) * h) * (h⁻¹ * (y : Γ) * h) = 1 := hm6sq _ hyE
    have hy_eq : (y : Γ) = h * (h⁻¹ * (y : Γ) * h) * h⁻¹ := by group
    rw [hy_eq]
    calc (h * (h⁻¹ * (y : Γ) * h) * h⁻¹) * (h * (h⁻¹ * (y : Γ) * h) * h⁻¹)
        = h * ((h⁻¹ * (y : Γ) * h) * (h⁻¹ * (y : Γ) * h)) * h⁻¹ := by group
      _ = h * 1 * h⁻¹ := by rw [hm2]
      _ = 1 := by group
  have hE'card : Nat.card ↥(E.subgroupOf W') = 16 := by
    calc Nat.card ↥(E.subgroupOf W')
        = Nat.card ↥((E.subgroupOf W').map W'.subtype) :=
          (Subgroup.card_map_of_injective W'.subtype_injective).symm
      _ = Nat.card ↥E := by rw [Subgroup.map_subgroupOf_eq_of_le hE_le_W']
      _ = 16 := hEcard
  have hSuz := y7c_suzuki_le_four hW'2 ht'sq ht'ne hcent_le (E := E.subgroupOf W') hEsq
  rw [hE'card] at hSuz
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
