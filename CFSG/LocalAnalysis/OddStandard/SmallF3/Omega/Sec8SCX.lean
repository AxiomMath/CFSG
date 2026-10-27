module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SCE
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem sec8scx_conj_mem_centralizer {G : Type} [Group G] {E : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (E : Set G)) (hc : c ∈ centralizer (E : Set G)) :
    n * c * n⁻¹ ∈ centralizer (E : Set G) :=
  (Subgroup.normal_subgroupOf_iff (Subgroup.centralizer_le_normalizer (E : Set G))).mp
    (Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G)) c n hc hn

theorem asc82FinkCX_of (hSyl : Asc82FinkSylow) : Asc82FinkCX := by
  intro G _ _ t L S z g B E hE x hxX hxt
  classical
  have hS : Sec3SettingLB G t L := hE.ctx.toSec3SettingLB
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.involution, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hCE := asc82FinkCE_of hSyl G t L S z g B E hE
  let C : Subgroup G := centralizer (E : Set G)
  let X : Subgroup G := normalizer (E : Set G)
  let O : Subgroup G := oddCoreIn X
  have hCeq : C = E ⊔ O := hCE.1
  have hOleC : O ≤ C := hCE.2
  let t'' : G := x⁻¹ * t * x
  let c₂ : G := t'' * t⁻¹
  have ht''def : t'' = x⁻¹ * t * x := rfl
  have hc₂def : c₂ = t'' * t⁻¹ := rfl
  have htX : t ∈ X := by
    show t ∈ normalizer (E : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hE.t_norm h hh
    · intro hh
      have h2 := hE.t_norm (t * h * t⁻¹) hh
      have h3 : t * (t * h * t⁻¹) * t⁻¹ = h := by
        rw [htinv]
        calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
          _ = h := by simp [ht2]
      rwa [h3] at h2
  have hEO : E ⊓ O = ⊥ := by
    show E ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    have heE : e ∈ E := he.1
    have heO : e ∈ oddCoreIn (normalizer (E : Set G)) := he.2
    have h2 : e ^ 2 = 1 := hE.elem.1.2 e heE
    have hdvd : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hodd : Odd (orderOf e) := odd_orderOf_of_mem_oddCoreIn heO
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · obtain ⟨k, hk⟩ := hodd
      omega
  have hcommEO : ∀ e ∈ E, ∀ o ∈ O, e * o = o * e := by
    intro e he o ho
    exact Subgroup.mem_centralizer_iff.mp (hOleC ho) e he
  have hc₂C : c₂ ∈ C := by
    rw [hc₂def, ht''def]
    have hxinvX : x⁻¹ ∈ X := X.inv_mem hxX
    have h1 := sec8scx_conj_mem_centralizer hxinvX hxt
    have heq : (x⁻¹ * (x * t * x⁻¹ * t⁻¹) * (x⁻¹)⁻¹)⁻¹ = (x⁻¹ * t * x) * t⁻¹ := by
      group
    rw [← heq]
    exact C.inv_mem h1
  have ht''2 : t'' * t'' = 1 := by
    rw [ht''def]
    calc (x⁻¹ * t * x) * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
      _ = 1 := by rw [ht2]; group
  have ht''eq : t'' = c₂ * t := by
    rw [ht''def, hc₂def, ht''def]
    group
  have hcomp : c₂ * (t * c₂ * t⁻¹) = 1 := by
    have h : t'' * t'' = c₂ * (t * c₂ * t⁻¹) * (t * t) := by
      rw [ht''def, hc₂def, ht''def]
      group
    rw [ht2, mul_one] at h
    rw [← h]
    exact ht''2
  have hc₂sup : c₂ ∈ E ⊔ O := by
    rw [← hCeq]
    exact hc₂C
  obtain ⟨e₂, he₂E, o₂, ho₂O, hc₂eq⟩ := exists_mul_of_mem_sup_of_commute hcommEO hc₂sup
  have hte : t * e₂ * t⁻¹ ∈ E := hE.t_norm e₂ he₂E
  have hto : t * o₂ * t⁻¹ ∈ O := by
    show t * o₂ * t⁻¹ ∈ oddCoreIn (normalizer (E : Set G))
    exact (Subgroup.normal_subgroupOf_iff
      (oddCoreIn_normal (normalizer (E : Set G))).1).mp
        (oddCoreIn_normal (normalizer (E : Set G))).2 o₂ t ho₂O htX
  have hsplit : c₂ * (t * c₂ * t⁻¹) =
      (e₂ * (t * e₂ * t⁻¹)) * (o₂ * (t * o₂ * t⁻¹)) := by
    have hcomm2 : o₂ * (t * e₂ * t⁻¹) = (t * e₂ * t⁻¹) * o₂ :=
      (hcommEO (t * e₂ * t⁻¹) hte o₂ ho₂O).symm
    rw [hc₂eq]
    calc (e₂ * o₂) * (t * (e₂ * o₂) * t⁻¹)
        = e₂ * (o₂ * (t * e₂ * t⁻¹)) * (t * o₂ * t⁻¹) := by group
      _ = e₂ * ((t * e₂ * t⁻¹) * o₂) * (t * o₂ * t⁻¹) := by rw [hcomm2]
      _ = (e₂ * (t * e₂ * t⁻¹)) * (o₂ * (t * o₂ * t⁻¹)) := by group
  have haE : e₂ * (t * e₂ * t⁻¹) ∈ E := E.mul_mem he₂E hte
  have hbO : o₂ * (t * o₂ * t⁻¹) ∈ O := O.mul_mem ho₂O hto
  have hab1 : (e₂ * (t * e₂ * t⁻¹)) * (o₂ * (t * o₂ * t⁻¹)) = 1 := by
    rw [← hsplit]
    exact hcomp
  have ha1 : e₂ * (t * e₂ * t⁻¹) = 1 := by
    have hainf : e₂ * (t * e₂ * t⁻¹) ∈ E ⊓ O := by
      refine ⟨haE, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hab1]
      exact O.inv_mem hbO
    rw [hEO] at hainf
    exact Subgroup.mem_bot.mp hainf
  have hb1 : o₂ * (t * o₂ * t⁻¹) = 1 := by
    rw [ha1, one_mul] at hab1
    exact hab1
  have he₂sq : e₂ * e₂ = 1 := by
    have h := hE.elem.1.2 e₂ he₂E
    rwa [pow_two] at h
  have hte₂inv : t * e₂ * t⁻¹ = e₂ := by
    have h := eq_inv_of_mul_eq_one_right ha1
    rwa [inv_eq_of_mul_eq_one_right he₂sq] at h
  have he₂cent : e₂ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : e₂ = (t * e₂) * t⁻¹ := hte₂inv.symm
    exact eq_mul_inv_iff_mul_eq.mp h
  have he₂B : e₂ ∈ B := by
    have h : e₂ ∈ E ⊓ centralizer ({t} : Set G) := ⟨he₂E, he₂cent⟩
    rwa [hE.cent_t] at h
  have hb1' : t * o₂ * t⁻¹ = o₂⁻¹ := eq_inv_of_mul_eq_one_right hb1
  have ho₂odd : Odd (orderOf o₂) := odd_orderOf_of_mem_oddCoreIn ho₂O
  obtain ⟨j, hj⟩ := ho₂odd
  let o₁ : G := o₂ ^ ((orderOf o₂ + 1) / 2)
  have ho₁def : o₁ = o₂ ^ ((orderOf o₂ + 1) / 2) := rfl
  have ho₁O : o₁ ∈ O := by
    rw [ho₁def]
    exact O.pow_mem ho₂O _
  have ho₁sq : o₁ * o₁ = o₂ := by
    rw [ho₁def]
    have hkk : (orderOf o₂ + 1) / 2 + (orderOf o₂ + 1) / 2 = orderOf o₂ + 1 := by
      rw [hj]
      omega
    calc o₂ ^ ((orderOf o₂ + 1) / 2) * o₂ ^ ((orderOf o₂ + 1) / 2)
        = o₂ ^ ((orderOf o₂ + 1) / 2 + (orderOf o₂ + 1) / 2) := (pow_add _ _ _).symm
      _ = o₂ ^ (orderOf o₂ + 1) := by rw [hkk]
      _ = o₂ ^ orderOf o₂ * o₂ := pow_succ _ _
      _ = 1 * o₂ := by rw [pow_orderOf_eq_one]
      _ = o₂ := one_mul _
  have ho₁inv : t * o₁ * t⁻¹ = o₁⁻¹ := by
    rw [ho₁def]
    calc t * o₂ ^ ((orderOf o₂ + 1) / 2) * t⁻¹
        = (t * o₂ * t⁻¹) ^ ((orderOf o₂ + 1) / 2) := by
          simpa only [MulAut.conj_apply] using map_pow (MulAut.conj t) o₂ _
      _ = (o₂⁻¹) ^ ((orderOf o₂ + 1) / 2) := by rw [hb1']
      _ = (o₂ ^ ((orderOf o₂ + 1) / 2))⁻¹ := by rw [inv_pow]
  have hmain : o₁ * t * o₁⁻¹ = o₂ * t := by
    calc o₁ * t * o₁⁻¹
        = o₁ * (t * o₁⁻¹ * t⁻¹) * t := by group
      _ = o₁ * (t * o₁ * t⁻¹)⁻¹ * t := by group
      _ = o₁ * o₁ * t := by rw [ho₁inv, inv_inv]
      _ = o₂ * t := by rw [ho₁sq]
  obtain ⟨e', he'E, he'eq⟩ := hE.comm_onto e₂ he₂B
  have he'conj : e' * t * e'⁻¹ = e₂ * t := by
    have h := eq_mul_inv_iff_mul_eq.mp he'eq.symm
    exact h.symm
  let y : G := o₁ * e'
  have hydef : y = o₁ * e' := rfl
  have he'C : e' ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hE.elem.1.comm ha he'E
  have ho₁C : o₁ ∈ C := hOleC ho₁O
  have hyC : y ∈ C := by
    rw [hydef]
    exact C.mul_mem ho₁C he'C
  have hyconj : y * t * y⁻¹ = t'' := by
    have ho₁e₂ : o₁ * e₂ = e₂ * o₁ := (hcommEO e₂ he₂E o₁ ho₁O).symm
    show (o₁ * e') * t * (o₁ * e')⁻¹ = t''
    calc (o₁ * e') * t * (o₁ * e')⁻¹
        = o₁ * (e' * t * e'⁻¹) * o₁⁻¹ := by group
      _ = o₁ * (e₂ * t) * o₁⁻¹ := by rw [he'conj]
      _ = e₂ * (o₁ * t * o₁⁻¹) := by
            rw [← mul_assoc, ho₁e₂]
            group
      _ = e₂ * (o₂ * t) := by rw [hmain]
      _ = (e₂ * o₂) * t := by group
      _ = c₂ * t := by rw [← hc₂eq]
      _ = t'' := ht''eq.symm
  refine ⟨y, hyC, ?_⟩
  have hxy : (x * y) * t = t * (x * y) := by
    have h : (x * y) * t * (x * y)⁻¹ = t := by
      calc (x * y) * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
        _ = x * t'' * x⁻¹ := by rw [hyconj]
        _ = t := by rw [ht''def]; group
    exact mul_inv_eq_iff_eq_mul.mp h
  exact hxy

end CFSG.OddStandard.SmallF3.Omega
