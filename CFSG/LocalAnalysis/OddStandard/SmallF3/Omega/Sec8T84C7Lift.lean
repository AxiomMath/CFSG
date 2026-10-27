module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C1Set

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem exists_conj_normalizer (F : Sec8T84Base) (hE : Sec8E G t L S z g B E) {m : G}
    (hmL : m ∈ L) (hmB : m ∈ normalizer (B : Set G)) (hm2 : m * m = 1) :
    ∃ (s : G) (hs : s ∈ normalizer (E : Set G)), IsConj t s ∧
      E.normalizerMonoidHom ⟨s, hs⟩ = B89.rhoG hE t * B89.rhoG hE m := by
  classical
  have hm_inv : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
  have hLt : L ≤ centralizer ({t} : Set G) := hE.ctx.toSec3SettingLB.component.le
  have hmt : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.mp (hLt hmL)
  rcases eq_or_ne m 1 with hm1 | hm1
  · subst hm1
    refine ⟨t, B89.t_mem_X hE, IsConj.refl t, ?_⟩
    rw [kappa_t hE, B89.rhoG_one, mul_one]
  · have hord : orderOf m = 2 := orderOf_eq_prime (by rwa [pow_two]) hm1
    have hmN : m ∈ Nsub8 t B := B89.mem_N_of_comm hmt hmB
    let O : Subgroup G := oddCoreIn (Nsub8 t B)
    have hON : O ≤ Nsub8 t B := (oddCoreIn_normal (Nsub8 t B)).1
    have hOnorm : (O.subgroupOf (Nsub8 t B)).Normal := (oddCoreIn_normal (Nsub8 t B)).2
    have hOnormN : Nsub8 t B ≤ normalizer (O : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mp hOnorm
    obtain ⟨o, hoO, hxX⟩ := sec8s_conj_oddCore hE hmt hmB
    have hoN : o ∈ Nsub8 t B := hON hoO
    let x : G := o⁻¹ * m
    have hxX' : x ∈ normalizer (E : Set G) := hxX
    have hxN : x ∈ Nsub8 t B := (Nsub8 t B).mul_mem ((Nsub8 t B).inv_mem hoN) hmN
    have hot : o * t = t * o := B89.O_comm_A F.h8A hE.ctx hoO sec8t84a1_t_mem_A
    have hot_inv : o⁻¹ * t = t * o⁻¹ := by
      calc o⁻¹ * t = o⁻¹ * (t * o) * o⁻¹ := by group
        _ = o⁻¹ * (o * t) * o⁻¹ := by rw [hot]
        _ = t * o⁻¹ := by group
    have hxt : x * t = t * x := by
      show (o⁻¹ * m) * t = t * (o⁻¹ * m)
      calc (o⁻¹ * m) * t = o⁻¹ * (m * t) := by group
        _ = o⁻¹ * (t * m) := by rw [hmt]
        _ = (o⁻¹ * t) * m := by group
        _ = (t * o⁻¹) * m := by rw [hot_inv]
        _ = t * (o⁻¹ * m) := by group
    have hρx : B89.rhoG hE x = B89.rhoG hE m := by
      show B89.rhoG hE (o⁻¹ * m) = B89.rhoG hE m
      rw [B89.rhoG_mul hE ((Nsub8 t B).inv_mem hoN) hmN,
        B89.rhoG_inv hE hoN, B89.rhoG_of_mem_O hE hoO, inv_one, one_mul]
    have hκx : E.normalizerMonoidHom ⟨x, hxX'⟩ = B89.rhoG hE m :=
      (kappa_eq_rhoG hE hxX' hxN).trans hρx
    let w : G := x * x
    have hwO : w ∈ O := by
      have hw_eq : x * x = o⁻¹ * (m * o⁻¹ * m⁻¹) := by
        show (o⁻¹ * m) * (o⁻¹ * m) = o⁻¹ * (m * o⁻¹ * m⁻¹)
        rw [hm_inv]
        group
      change x * x ∈ O
      rw [hw_eq]
      exact O.mul_mem (O.inv_mem hoO)
        ((Subgroup.mem_normalizer_iff.mp (hOnormN hmN) o⁻¹).mp (O.inv_mem hoO))
    let r : ℕ := orderOf w
    have hrodd : Odd r :=
      Odd.of_dvd_nat (odd_card_oddCoreIn (Nsub8 t B))
        (Subgroup.orderOf_dvd_natCard O hwO)
    obtain ⟨j, hj⟩ := hrodd
    have hxr : x ^ r = w ^ j * x := by
      rw [hj, pow_succ, pow_mul, sq]
    have hxr_sq : x ^ r * x ^ r = 1 := by
      rw [← pow_two, ← pow_mul, Nat.mul_comm r 2, pow_mul, pow_two,
        show x * x = w from rfl, pow_orderOf_eq_one]
    let o' : G := w ^ j * o⁻¹
    have ho'O : o' ∈ O := O.mul_mem (O.pow_mem hwO j) (O.inv_mem hoO)
    have hxr' : x ^ r = o' * m := by
      rw [hxr]
      show w ^ j * (o⁻¹ * m) = (w ^ j * o⁻¹) * m
      group
    have hm_o' : m * o' * m⁻¹ = o'⁻¹ := by
      have hsquare : (o' * m) * (o' * m) = 1 := by
        rw [← hxr']
        exact hxr_sq
      have h5 : o' * m * o' = m⁻¹ := by
        calc o' * m * o' = (o' * m) * (o' * m) * m⁻¹ := by group
          _ = 1 * m⁻¹ := by rw [hsquare]
          _ = m⁻¹ := one_mul _
      have h4 : m * o' * m * o' = 1 := by
        calc m * o' * m * o' = m * (o' * m * o') := by group
          _ = m * m⁻¹ := by rw [h5]
          _ = 1 := by group
      rw [hm_inv]
      exact eq_inv_of_mul_eq_one_left h4
    let e : ℕ := (Nat.card O + 1) / 2
    let p : G := o' ^ e
    have h2e : 2 * e = Nat.card O + 1 := by
      show 2 * ((Nat.card O + 1) / 2) = Nat.card O + 1
      exact Nat.mul_div_cancel' (by
        obtain ⟨Nj, hNj⟩ := odd_card_oddCoreIn (Nsub8 t B)
        rw [hNj]
        exact ⟨Nj + 1, by ring⟩)
    have ho'_card : o' ^ Nat.card O = 1 :=
      (orderOf_dvd_iff_pow_eq_one (x := o') (n := Nat.card O)).mp
        (Subgroup.orderOf_dvd_natCard O ho'O)
    have hpp : p * p = o' := by
      show o' ^ e * o' ^ e = o'
      rw [← pow_add, ← two_mul, h2e, pow_succ, ho'_card, one_mul]
    have hpO : p ∈ O := O.pow_mem ho'O e
    have hmp : m * p * m⁻¹ = p⁻¹ := by
      show m * o' ^ e * m⁻¹ = (o' ^ e)⁻¹
      rw [← conj_pow, hm_o', inv_pow]
    have hpconj : p * m * p⁻¹ = o' * m := by
      calc p * m * p⁻¹ = p * m * (m * p * m⁻¹) := by rw [hmp]
        _ = p * (m * m) * p * m⁻¹ := by group
        _ = p * p * m⁻¹ := by rw [hm2]; group
        _ = o' * m := by rw [hpp, hm_inv]
    let s : G := t * x ^ r
    have hs : s ∈ normalizer (E : Set G) :=
      (normalizer (E : Set G)).mul_mem (B89.t_mem_X hE) ((normalizer (E : Set G)).pow_mem hxX' r)
    have hκs : E.normalizerMonoidHom ⟨s, hs⟩ = B89.rhoG hE t * B89.rhoG hE m := by
      have hs_eq : (⟨s, hs⟩ : ↥(normalizer (E : Set G))) =
          ⟨t, B89.t_mem_X hE⟩ * ⟨x ^ r, (normalizer (E : Set G)).pow_mem hxX' r⟩ :=
        Subtype.ext rfl
      have hpow : (⟨x ^ r, (normalizer (E : Set G)).pow_mem hxX' r⟩ : ↥(normalizer (E : Set G))) =
          ⟨x, hxX'⟩ ^ r :=
        Subtype.ext rfl
      rw [hs_eq, map_mul, kappa_t hE]
      congr 1
      rw [hpow, map_pow, hκx]
      have hρm_sq : B89.rhoG hE m * B89.rhoG hE m = 1 := by
        rw [← B89.rhoG_mul hE hmN hmN, hm2, B89.rhoG_one]
      rw [hj, pow_succ, pow_mul, sq, hρm_sq, one_pow, one_mul]
    have hconj : IsConj (t * m) s := by
      rw [isConj_iff]
      refine ⟨p, ?_⟩
      show p * (t * m) * p⁻¹ = t * x ^ r
      have hpt : p * t = t * p :=
        B89.O_comm_A F.h8A hE.ctx hpO sec8t84a1_t_mem_A
      calc p * (t * m) * p⁻¹ = (p * t) * m * p⁻¹ := by group
        _ = (t * p) * m * p⁻¹ := by rw [hpt]
        _ = t * (p * m * p⁻¹) := by group
        _ = t * (o' * m) := by rw [hpconj]
        _ = t * x ^ r := by rw [hxr']
    have h83 : IsConj t (t * m) :=
      F.h83 G t L hE.ctx.toSec3SettingLB hE.ctx.omega6m m hord hmL
    exact ⟨s, hs, h83.trans hconj, hκs⟩

end C10

end CFSG.OddStandard.SmallF3.Omega
