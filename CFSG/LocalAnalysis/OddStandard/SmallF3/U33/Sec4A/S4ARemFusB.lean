module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AFusA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma conj_t_eq_t_or_t_mul_z (h : Ctx t L S x₁ x₂ lam rho tau) {n : G}
    (hn : n ∈ normalizer (S : Set G)) :
    n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * (x₁ * x₂) ^ 2 := by
  have hnE : n ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G) :=
    normalizer_S_le_normalizer_E h hn
  have hz := normalizer_fixes_z h.toCtx0 hnE
  have hnt : n * t * n⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} :=
    ((Subgroup.mem_set_normalizer_iff).mp hnE t).mp (Subgroup.subset_closure (by simp))
  rcases mem_closure_t_z h.toCtx0 hnt with h1 | h1 | h1 | h1
  · exfalso
    have ht1 : t = 1 := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    exact t_ne_one h.hyp ht1
  · exact Or.inl h1
  · exfalso
    have htz : t = (x₁ * x₂) ^ 2 := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * (n * (x₁ * x₂) ^ 2 * n⁻¹) * n := by rw [h1, hz]
        _ = (x₁ * x₂) ^ 2 := by group
    exact t_not_mem_L h.hyp (htz ▸ (y_z_mem_L h.toCtx0).2)
  · exact Or.inr h1

private lemma mem_zpowers_z_cases {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private lemma sylow_inf_invCent_eq (h : Ctx t L S x₁ x₂ lam rho tau) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) : invCent t ⊓ (𝒮 : Subgroup G) = S := by
  exact eq_of_isPGroup_of_odd_relIndex (H := invCent t)
    (fun s hs => ⟨h.toCtx0.le_invCent hs, h𝒮.le hs⟩) inf_le_left
    ((show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup').to_le inf_le_right)
    h.toCtx0.relIndex_odd

private lemma exists_conj_swap (h : Ctx t L S x₁ x₂ lam rho tau) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) :
    ∃ a ∈ normalizer (S : Set G) ⊓ (𝒮 : Subgroup G),
      a * t * a⁻¹ = t * (x₁ * x₂) ^ 2 := by
  obtain ⟨a, haSyl, haN, ha_notS⟩ :=
    exists_mem_normalizer_not_mem (show IsPGroup 2 (𝒮 : Subgroup G) from 𝒮.isPGroup') h𝒮
  refine ⟨a, ⟨haN, haSyl⟩, ?_⟩
  rcases conj_t_eq_t_or_t_mul_z h haN with h1 | h1
  · exfalso
    have haInv : a ∈ invCent t := mem_invCent_iff.mpr (by
      calc a * t = (a * t * a⁻¹) * a := by group
        _ = t * a := by rw [h1])
    have hEq := sylow_inf_invCent_eq h 𝒮 h𝒮
    exact ha_notS (hEq ▸ ⟨haInv, haSyl⟩)
  · exact h1

private lemma conj_inv_t_of_conj_t (h : Ctx t L S x₁ x₂ lam rho tau) {a : G}
    (haE : a ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G))
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2) :
    a⁻¹ * t * a = t * (x₁ * x₂) ^ 2 := by
  let z : G := (x₁ * x₂) ^ 2
  have hz : z * z = 1 := (z_mul_self_ne_one h.toCtx0).1
  have hazinv : a⁻¹ * z * a = z := by
    simpa [z] using
      normalizer_fixes_z h.toCtx0
        ((normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G)).inv_mem haE)
  have hright : a⁻¹ * (t * z) * a = (a⁻¹ * t * a) * z := by
    calc a⁻¹ * (t * z) * a = (a⁻¹ * t * a) * (a⁻¹ * z * a) := by group
      _ = (a⁻¹ * t * a) * z := by rw [hazinv]
  have ht : t = (a⁻¹ * t * a) * z := by
    have hconj : a⁻¹ * (a * t * a⁻¹) * a = a⁻¹ * (t * z) * a :=
      congrArg (fun u => a⁻¹ * u * a) hat
    have hleft : a⁻¹ * (a * t * a⁻¹) * a = t := by group
    rw [hleft, hright] at hconj
    exact hconj
  have hzz : ((a⁻¹ * t * a) * z) * z = a⁻¹ * t * a := by rw [mul_assoc, hz, mul_one]
  calc a⁻¹ * t * a = ((a⁻¹ * t * a) * z) * z := hzz.symm
    _ = t * z := by rw [← ht]
    _ = t * (x₁ * x₂) ^ 2 := rfl

private lemma conj_inv_mul_mem_invCent (h : Ctx t L S x₁ x₂ lam rho tau) {a m : G}
    (haE : a ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G))
    (hat : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2)
    (hmt : m * t * m⁻¹ = t * (x₁ * x₂) ^ 2) :
    a⁻¹ * m ∈ invCent t := by
  have hatinv := conj_inv_t_of_conj_t h haE hat
  have hazinv : a⁻¹ * (x₁ * x₂) ^ 2 * a = (x₁ * x₂) ^ 2 := by
    simpa using
      normalizer_fixes_z h.toCtx0
        ((normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G)).inv_mem haE)
  have hz : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h.toCtx0).1
  refine mem_invCent_iff.mpr ?_
  have hconj : (a⁻¹ * m) * t * (a⁻¹ * m)⁻¹ = t := by
    calc (a⁻¹ * m) * t * (a⁻¹ * m)⁻¹
        = a⁻¹ * (m * t * m⁻¹) * a := by group
      _ = a⁻¹ * (t * (x₁ * x₂) ^ 2) * a := by rw [hmt]
      _ = (a⁻¹ * t * a) * (a⁻¹ * (x₁ * x₂) ^ 2 * a) := by group
      _ = (t * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [hatinv, hazinv]
      _ = t := by rw [mul_assoc, hz, mul_one]
  calc (a⁻¹ * m) * t = ((a⁻¹ * m) * t * (a⁻¹ * m)⁻¹) * (a⁻¹ * m) := by group
    _ = t * (a⁻¹ * m) := by rw [hconj]

private lemma sylow_relIndex_ctxS1_eq_two (h : Ctx t L S x₁ x₂ lam rho tau)
    (𝒮 : Sylow 2 G) (h𝒮 : S < (𝒮 : Subgroup G)) :
    S.relIndex (ctxS1 S (𝒮 : Subgroup G)) = 2 := by
  obtain ⟨a, haS1, hat⟩ := exists_conj_swap h 𝒮 h𝒮
  have hS_S1 : S ≤ ctxS1 S (𝒮 : Subgroup G) :=
    fun s hs => ⟨Subgroup.le_normalizer (H := S) hs, h𝒮.le hs⟩
  have ha_notS : a ∉ S := by
    intro haS
    have haInv : a ∈ invCent t := h.toCtx0.le_invCent haS
    have ht : a * t = t * a := mem_invCent_iff.mp haInv
    have hfix : a * t * a⁻¹ = t := by rw [ht]; group
    rw [hat] at hfix
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have h' := congrArg (fun u => t⁻¹ * u) hfix
      simpa using h'
    exact (z_mul_self_ne_one h.toCtx0).2 hz1
  have hcover : ∀ m ∈ ctxS1 S (𝒮 : Subgroup G), m ∈ S ∨ a⁻¹ * m ∈ S := by
    intro m hm
    obtain ⟨hmN, hmSyl⟩ := hm
    have hEq := sylow_inf_invCent_eq h 𝒮 h𝒮
    rcases conj_t_eq_t_or_t_mul_z h hmN with hmt | hmt
    · left
      have hmInv : m ∈ invCent t := mem_invCent_iff.mpr (by
        calc m * t = (m * t * m⁻¹) * m := by group
          _ = t * m := by rw [hmt])
      exact hEq ▸ ⟨hmInv, hmSyl⟩
    · right
      have hmInv : a⁻¹ * m ∈ invCent t :=
        conj_inv_mul_mem_invCent h (normalizer_S_le_normalizer_E h haS1.1) hat hmt
      have hmSyl' : a⁻¹ * m ∈ (𝒮 : Subgroup G) :=
        (𝒮 : Subgroup G).mul_mem ((𝒮 : Subgroup G).inv_mem haS1.2) hmSyl
      exact hEq ▸ ⟨hmInv, hmSyl'⟩
  have hle : S.relIndex (ctxS1 S (𝒮 : Subgroup G)) ≤ 2 :=
    relIndex_le_two_of_forall hS_S1 a haS1 hcover
  have hne1 : S.relIndex (ctxS1 S (𝒮 : Subgroup G)) ≠ 1 := by
    intro h1
    exact ha_notS ((Subgroup.relIndex_eq_one.mp h1) haS1)
  haveI : S.IsFiniteRelIndex (ctxS1 S (𝒮 : Subgroup G)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hne0 : S.relIndex (ctxS1 S (𝒮 : Subgroup G)) ≠ 0 := Subgroup.relIndex_ne_zero
  omega

private lemma sylow_relIndex_normalizer_odd (h : Ctx t L S x₁ x₂ lam rho tau)
    (𝒮 : Sylow 2 G) (h𝒮 : S < (𝒮 : Subgroup G)) :
    ¬ 2 ∣ (ctxS1 S (𝒮 : Subgroup G)).relIndex (normalizer (S : Set G)) := by
  let N : Subgroup G := normalizer (S : Set G)
  let NH : Subgroup G := N ⊓ invCent t
  let S₁ : Subgroup G := ctxS1 S (𝒮 : Subgroup G)
  change ¬ 2 ∣ S₁.relIndex N
  obtain ⟨a, haS1, hat⟩ := exists_conj_swap h 𝒮 h𝒮
  have hS_NH : S ≤ NH :=
    fun s hs => ⟨Subgroup.le_normalizer (H := S) hs, h.toCtx0.le_invCent hs⟩
  have hNH_N : NH ≤ N := inf_le_left
  have hNH_inv : NH ≤ invCent t := inf_le_right
  have hS_S1 : S ≤ S₁ := fun s hs => ⟨Subgroup.le_normalizer (H := S) hs, h𝒮.le hs⟩
  have hS1_N : S₁ ≤ N := inf_le_left
  have hS_NH_odd : ¬ 2 ∣ S.relIndex NH := by
    intro h2d
    apply h.toCtx0.relIndex_odd
    rw [← Subgroup.relIndex_mul_relIndex S NH (invCent t) hS_NH hNH_inv]
    exact dvd_mul_of_dvd_left h2d _
  have haN : a ∈ N := haS1.1
  have haE : a ∈ normalizer ((closure {t, (x₁ * x₂) ^ 2} : Subgroup G) : Set G) :=
    normalizer_S_le_normalizer_E h haN
  have hNH_N_le2 : NH.relIndex N ≤ 2 := by
    refine relIndex_le_two_of_forall hNH_N a haN ?_
    intro m hm
    rcases conj_t_eq_t_or_t_mul_z h hm with hmt | hmt
    · left
      have hmInv : m ∈ invCent t := mem_invCent_iff.mpr (by
        calc m * t = (m * t * m⁻¹) * m := by group
          _ = t * m := by rw [hmt])
      exact ⟨hm, hmInv⟩
    · right
      exact ⟨N.mul_mem (N.inv_mem haN) hm, conj_inv_mul_mem_invCent h haE hat hmt⟩
  have hNH_N_ne1 : NH.relIndex N ≠ 1 := by
    intro h1
    have haNH : a ∈ NH := (Subgroup.relIndex_eq_one.mp h1) haN
    have haInv : a ∈ invCent t := haNH.2
    have ht : a * t = t * a := mem_invCent_iff.mp haInv
    have hfix : a * t * a⁻¹ = t := by rw [ht]; group
    rw [hat] at hfix
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have h' := congrArg (fun u => t⁻¹ * u) hfix
      simpa using h'
    exact (z_mul_self_ne_one h.toCtx0).2 hz1
  haveI : NH.IsFiniteRelIndex N := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hNH_N_ne0 : NH.relIndex N ≠ 0 := Subgroup.relIndex_ne_zero
  have hNH_N_eq2 : NH.relIndex N = 2 := by omega
  have hS₁rel : S.relIndex S₁ = 2 := sylow_relIndex_ctxS1_eq_two h 𝒮 h𝒮
  have hS_N_eq : S.relIndex N = S.relIndex NH * NH.relIndex N :=
    (Subgroup.relIndex_mul_relIndex S NH N hS_NH hNH_N).symm
  have hS_N_eq2 : S.relIndex N = 2 * S₁.relIndex N := by
    rw [← Subgroup.relIndex_mul_relIndex S S₁ N hS_S1 hS1_N, hS₁rel]
  have hkey : 2 * S₁.relIndex N = S.relIndex NH * 2 := by
    rw [← hS_N_eq2, hS_N_eq, hNH_N_eq2]
  have hcancel : S₁.relIndex N = S.relIndex NH := by omega
  rw [hcancel]
  exact hS_NH_odd

theorem exists_swap_of_l42 (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index) :
    ∃ n ∈ normalizer (S : Set G), n * t * n⁻¹ = t * (x₁ * x₂) ^ 2 := by
  obtain ⟨𝒮, h𝒮⟩ := exists_sylow_gt h.toCtx0.isPGroup h2
  obtain ⟨n, hn, hnt⟩ := exists_conj_swap h 𝒮 h𝒮
  exact ⟨n, hn.1, hnt⟩

theorem fusion_tz_of_l42 (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index) :
    conjIn (normalizer (S : Set G)) t = t • (zpowers ((x₁ * x₂) ^ 2) : Set G) := by
  ext u
  constructor
  · rintro ⟨k, hk, hku⟩
    rw [← hku]
    rcases conj_t_eq_t_or_t_mul_z h hk with h1 | h1
    · rw [h1]
      exact Set.mem_smul_set.mpr ⟨1, Subgroup.one_mem _, by simp⟩
    · rw [h1]
      exact Set.mem_smul_set.mpr ⟨(x₁ * x₂) ^ 2, Subgroup.mem_zpowers _, by simp⟩
  · intro hu
    obtain ⟨w, hw, hwu⟩ := Set.mem_smul_set.mp hu
    rw [← hwu]
    rcases mem_zpowers_z_cases (z_mul_self_ne_one h.toCtx0).1 hw with hw1 | hwz
    · rw [hw1]
      exact ⟨1, Subgroup.one_mem _, by simp⟩
    · rw [hwz]
      exact exists_swap_of_l42 h h2

theorem sylow_facts_of_l42 (h : Ctx t L S x₁ x₂ lam rho tau) (h2 : 2 ∣ S.index) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) :
    invCent t ⊓ (𝒮 : Subgroup G) = S ∧ S.relIndex (ctxS1 S (𝒮 : Subgroup G)) = 2 ∧
    ¬ 2 ∣ (ctxS1 S (𝒮 : Subgroup G)).relIndex (normalizer (S : Set G)) :=
  ⟨sylow_inf_invCent_eq h 𝒮 h𝒮, sylow_relIndex_ctxS1_eq_two h 𝒮 h𝒮,
    sylow_relIndex_normalizer_odd h 𝒮 h𝒮⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
