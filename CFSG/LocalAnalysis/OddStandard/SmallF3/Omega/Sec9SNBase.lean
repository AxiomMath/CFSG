module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Early
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68b
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

private theorem sec9n_priv_mem_zpowers_two {x y : G} (hx2 : x * x = 1) (hy : y ∈ zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : x ^ (2 : ℕ) = 1 := by simpa [pow_two] using hx2
  have hmod : x ^ k = x ^ (k % (2 : ℤ)) := zpow_eq_zpow_emod' k h2
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [hmod, hk]; simp
  · right; rw [hmod, hk]; simp

theorem sec9n_mem_normalizer_of_conjugate_eq {H : Subgroup G} {c : G}
    (h : CFSG.conjugate H c = H) : c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff' (H := H) (g := c) (x := x), h]

theorem sec9n_t_sq (hctx : Sec9Ctx G t L S z g B t₀) : t * t = 1 := by
  rw [← pow_two, ← hctx.toSec3SettingLB.involution, pow_orderOf_eq_one]

theorem sec9n_t0_sq (hctx : Sec9Ctx G t L S z g B t₀) : t₀ * t₀ = 1 := by
  rw [← pow_two, ← hctx.t0_inv, pow_orderOf_eq_one]

theorem sec9n_t_mem_cent (hctx : Sec9Ctx G t L S z g B t₀) : t ∈ centralizer (L : Set G) :=
  sec68_t_mem_centralizer hctx.toSec3SettingLB

theorem sec9n_t0_mem_normalizer (hctx : Sec9Ctx G t L S z g B t₀) :
    t₀ ∈ normalizer (L : Set G) := by
  obtain ⟨α, V, _, _, _, Q, hQ, e, x, -, -, hind, -⟩ := hctx.t0_type
  exact hind.1

theorem sec9n_t_t0 (hctx : Sec9Ctx G t L S z g B t₀) : t * t₀ = t₀ * t :=
  (Subgroup.mem_centralizer_singleton_iff.mp hctx.t0_cent).symm

theorem sec9n_t_B (hctx : Sec9Ctx G t L S z g B t₀) : ∀ b ∈ B, t * b = b * t := fun b hb =>
  (Subgroup.mem_centralizer_iff.mp (sec9n_t_mem_cent hctx) b (hctx.B_le hb).1).symm

private theorem sec9n_priv_comm_t_t0 (hctx : Sec9Ctx G t L S z g B t₀) :
    ∀ a ∈ zpowers t, ∀ b ∈ zpowers t₀, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ((show Commute t t₀ from sec9n_t_t0 hctx).zpow_zpow k l).eq

private theorem sec9n_priv_comm_A8_B (hctx : Sec9Ctx G t L S z g B t₀) :
    ∀ a ∈ zpowers t ⊔ zpowers t₀, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (sec9n_priv_comm_t_t0 hctx) ha
  have hub : u * b = b * u := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((show Commute t b from sec9n_t_B hctx b hb).zpow_left k).eq
  have hvb : v * b = b * v := by
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute t₀ b from hctx.t0_B b hb).zpow_left l).eq
  rw [mul_assoc, hvb, ← mul_assoc, hub, mul_assoc]

private theorem sec9n_priv_centMod_conj_mem {A B : Subgroup G} (hBA : B ≤ A) {x : G}
    (hx : x ∈ centMod A B) {a : G} (ha : a ∈ A) : x * a * x⁻¹ ∈ A := by
  obtain ⟨-, hx'⟩ := hx
  have hcomm : x * a * x⁻¹ * a⁻¹ ∈ B := hx' a ha
  rw [show x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a by group]
  exact A.mul_mem (hBA hcomm) ha

theorem sec9n_centMod_le_normalizer {A B : Subgroup G} (hBA : B ≤ A) :
    centMod A B ≤ normalizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact sec9n_priv_centMod_conj_mem hBA hx
  · intro ha
    have hxinv : x⁻¹ ∈ centMod A B := (centMod A B).inv_mem hx
    have h := sec9n_priv_centMod_conj_mem hBA hxinv ha
    rwa [show x⁻¹ * (x * a * x⁻¹) * (x⁻¹)⁻¹ = a by group] at h

theorem sec9n_le_centMod {A B : Subgroup G} (hBA : B ≤ A)
    (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) : A ≤ centMod A B := by
  intro a ha
  constructor
  · rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [show a * b * a⁻¹ = b by rw [hcomm a ha b (hBA hb)]; group]
      exact hb
    · intro hb
      have hb' : a⁻¹ * (a * b * a⁻¹) * a = a * b * a⁻¹ := by
        rw [hcomm a⁻¹ (A.inv_mem ha) (a * b * a⁻¹) (hBA hb)]
        group
      rwa [show b = a⁻¹ * (a * b * a⁻¹) * a by group, hb']
  · intro a' ha'
    have h : a * a' * a⁻¹ * a'⁻¹ = 1 := by rw [hcomm a ha a' ha']; group
    rw [h]
    exact B.one_mem

theorem sec9n_A_elem (hctx : Sec9Ctx G t L S z g B t₀) :
    CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) := by
  have ht : CFSG.Open.IsElemAbelian 2 (zpowers t) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) (by rw [pow_two]; exact sec9n_t_sq hctx)
  have ht0 : CFSG.Open.IsElemAbelian 2 (zpowers t₀) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) (by rw [pow_two]; exact sec9n_t0_sq hctx)
  have hsup := CFSG.Open.IsElemAbelian.sup_of_commute ht ht0 (sec9n_priv_comm_t_t0 hctx)
  rw [Asub9]
  exact CFSG.Open.IsElemAbelian.sup_of_commute hsup hctx.B_e16.1 (sec9n_priv_comm_A8_B hctx)

theorem sec9n_mem_A (hctx : Sec9Ctx G t L S z g B t₀) {a : G} (ha : a ∈ Asub9 t t₀ B) :
    ∃ b ∈ B, a = b ∨ a = t * b ∨ a = t₀ * b ∨ a = t * (t₀ * b) := by
  rw [Asub9] at ha
  obtain ⟨u, hu, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (sec9n_priv_comm_A8_B hctx) ha
  obtain ⟨s, hs, s0, hs0, rfl⟩ :=
    exists_mul_of_mem_sup_of_commute (sec9n_priv_comm_t_t0 hctx) hu
  rcases sec9n_priv_mem_zpowers_two (sec9n_t_sq hctx) hs with h1 | h1
  · rcases sec9n_priv_mem_zpowers_two (sec9n_t0_sq hctx) hs0 with h2 | h2
    · rw [h1, h2]; exact ⟨b, hb, Or.inl (by simp)⟩
    · rw [h1, h2]; exact ⟨b, hb, Or.inr (Or.inr (Or.inl (by simp)))⟩
  · rcases sec9n_priv_mem_zpowers_two (sec9n_t0_sq hctx) hs0 with h2 | h2
    · rw [h1, h2]; exact ⟨b, hb, Or.inr (Or.inl (by simp))⟩
    · rw [h1, h2]
      exact ⟨b, hb, Or.inr (Or.inr (Or.inr (by simp [mul_assoc])))⟩

theorem sec9n_A_mem_normalizer (hctx : Sec9Ctx G t L S z g B t₀) :
    ∀ a ∈ Asub9 t t₀ B, a ∈ normalizer (L : Set G) := by
  have htN : t ∈ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G) (sec9n_t_mem_cent hctx)
  have ht0N : t₀ ∈ normalizer (L : Set G) := sec9n_t0_mem_normalizer hctx
  intro a ha
  obtain ⟨b, hb, h | h | h | h⟩ := sec9n_mem_A hctx ha
  · rw [h]; exact Subgroup.le_normalizer (hctx.B_le hb).1
  · rw [h]; exact (normalizer (L : Set G)).mul_mem htN
      (Subgroup.le_normalizer (hctx.B_le hb).1)
  · rw [h]; exact (normalizer (L : Set G)).mul_mem ht0N
      (Subgroup.le_normalizer (hctx.B_le hb).1)
  · rw [h]; exact (normalizer (L : Set G)).mul_mem htN
      ((normalizer (L : Set G)).mul_mem ht0N (Subgroup.le_normalizer (hctx.B_le hb).1))

theorem sec9n_A8_le_inner (hctx : Sec9Ctx G t L S z g B t₀) :
    zpowers t ⊔ B ≤ L ⊔ centralizer (L : Set G) := by
  refine sup_le ?_ ?_
  · rw [zpowers_le]
    exact Subgroup.mem_sup_right (sec9n_t_mem_cent hctx)
  · intro b hb
    exact Subgroup.mem_sup_left (hctx.B_le hb).1

theorem sec9n_B_inf_cent (hctx : Sec9Ctx G t L S z g B t₀) :
    ∀ b ∈ B, b ∈ centralizer (L : Set G) → b = 1 := by
  intro b hb hbc
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  have hodd : Odd (orderOf b) :=
    sec66_odd_of_mem_inf hLM ⟨(hctx.B_le hb).1, hbc⟩
  have hb2 : b * b = 1 := hctx.B_e16.1.mul_self_eq_one hb
  have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hle : orderOf b ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  have hone : orderOf b = 1 := by omega
  exact orderOf_eq_one_iff.mp hone

theorem sec9n_t0_not_mem_A8 (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀) :
    t₀ ∉ zpowers t ⊔ B := by
  intro h
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  exact (hT.i3_outer G L hLM t₀ (sec9n_t0_mem_normalizer hctx) hctx.t0_type)
    (sec9n_A8_le_inner hctx h)

theorem sec9n_A_inf_L (hT : Asc82Tab9M) (hctx : Sec9Ctx G t L S z g B t₀) :
    ∀ a ∈ Asub9 t t₀ B, a ∈ L → a ∈ B := by
  have hLM : IsOm6M L := ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩
  intro a ha haL
  obtain ⟨b, hb, h | h | h | h⟩ := sec9n_mem_A hctx ha
  · rw [h]; exact hb
  · exfalso
    have hbL : b ∈ L := (hctx.B_le hb).1
    have htL : t ∈ L := by
      have ht_eq : t = a * b⁻¹ := by rw [h]; group
      rw [ht_eq]
      exact L.mul_mem haL (L.inv_mem hbL)
    have hodd : Odd (orderOf t) :=
      sec66_odd_of_mem_inf hLM ⟨htL, sec9n_t_mem_cent hctx⟩
    rw [hctx.toSec3SettingLB.involution] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  · exfalso
    have hbL : b ∈ L := (hctx.B_le hb).1
    have ht0L : t₀ ∈ L := by
      have ht0_eq : t₀ = a * b⁻¹ := by rw [h]; group
      rw [ht0_eq]
      exact L.mul_mem haL (L.inv_mem hbL)
    exact (hT.i3_outer G L hLM t₀ (sec9n_t0_mem_normalizer hctx) hctx.t0_type)
      (Subgroup.mem_sup_left ht0L)
  · exfalso
    have hbL : b ∈ L := (hctx.B_le hb).1
    have habL : a * b⁻¹ ∈ L := L.mul_mem haL (L.inv_mem hbL)
    have ht0_eq : t₀ = t * (a * b⁻¹) := by
      rw [h]
      rw [show t * (t * (t₀ * b) * b⁻¹) = t₀ by
        calc t * (t * (t₀ * b) * b⁻¹) = (t * t) * (t₀ * b) * b⁻¹ := by group
          _ = (t₀ * b) * b⁻¹ := by rw [sec9n_t_sq hctx, one_mul]
          _ = t₀ := by group]
    have hmem : t₀ ∈ centralizer (L : Set G) ⊔ L := by
      rw [ht0_eq]
      exact Subgroup.mul_mem_sup (sec9n_t_mem_cent hctx) habL
    exact (hT.i3_outer G L hLM t₀ (sec9n_t0_mem_normalizer hctx) hctx.t0_type)
      (by rw [InnerOn, sup_comm]; exact hmem)

theorem sec9n_mem_normalizer_conj_of_comm (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {g a : G} (ha : a * (g⁻¹ * t * g) = (g⁻¹ * t * g) * a) :
    a ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  have hcomm : (g * a * g⁻¹) * t = t * (g * a * g⁻¹) := by
    calc (g * a * g⁻¹) * t
        = g * (a * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * a) * g⁻¹ := by rw [ha]
      _ = t * (g * a * g⁻¹) := by group
  have hmem : g * a * g⁻¹ ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hn : g * a * g⁻¹ ∈ normalizer (L : Set G) :=
    sec9n_mem_normalizer_of_conjugate_eq
      (conjugate_eq_self_of_lemma36 h36 hS (g * a * g⁻¹) hmem)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [mem_conjugate_iff' (H := L) (g := g) (x := h),
    mem_conjugate_iff' (H := L) (g := g) (x := a * h * a⁻¹)]
  have heq : g * (a * h * a⁻¹) * g⁻¹ =
      (g * a * g⁻¹) * (g * h * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
  rw [heq]
  exact Subgroup.mem_normalizer_iff.mp hn (g * h * g⁻¹)

theorem sec9n_A_mem_normalizer_conj (h36 : Asc82Lemma36) (hB : Asc82Sec8B)
    (hctx : Sec9Ctx G t L S z g B t₀) :
    ∀ a ∈ Asub9 t t₀ B, a ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hzB : z ∈ B := (hB G t L S z g B hctx.toSec8Base).1
  have hzA : z ∈ Asub9 t t₀ B := by
    rw [Asub9]; exact Subgroup.mem_sup_right hzB
  have htA : t ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  intro a ha
  have htzA : t * z ∈ Asub9 t t₀ B := (Asub9 t t₀ B).mul_mem htA hzA
  have htza : a * (t * z) = (t * z) * a := (sec9n_A_elem hctx).comm ha htzA
  exact sec9n_mem_normalizer_conj_of_comm h36 hS (by rw [hctx.tz]; exact htza)

theorem sec9n_inf_le_centMod {A B H : Subgroup G} (hBA : B ≤ A) (hBH : B ≤ H)
    (hAH : ∀ a ∈ A, a ∈ H → a ∈ B) (hAN : ∀ a ∈ A, a ∈ normalizer (H : Set G)) :
    H ⊓ normalizer (A : Set G) ≤ centMod A B := by
  intro x hx
  obtain ⟨hxH, hxN⟩ := hx
  constructor
  · rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have hxA : x * b * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN b).mp (hBA hb)
      have hxH' : x * b * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH (hBH hb)) (H.inv_mem hxH)
      exact hAH _ hxA hxH'
    · intro hb
      have hxinv : x⁻¹ ∈ H ⊓ normalizer (A : Set G) :=
        ⟨H.inv_mem hxH, (normalizer (A : Set G)).inv_mem hxN⟩
      have hbA : x * b * x⁻¹ ∈ A := hBA hb
      have hxA : x⁻¹ * (x * b * x⁻¹) * (x⁻¹)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hxinv.2 (x * b * x⁻¹)).mp hbA
      have hxH' : x⁻¹ * (x * b * x⁻¹) * (x⁻¹)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hxinv.1 (hBH hb)) (H.inv_mem hxinv.1)
      have hB := hAH _ hxA hxH'
      rwa [show x⁻¹ * (x * b * x⁻¹) * (x⁻¹)⁻¹ = b by group] at hB
  · intro a ha
    have hxA : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
    have hcommA : x * a * x⁻¹ * a⁻¹ ∈ A := A.mul_mem hxA (A.inv_mem ha)
    have haxH : a * x⁻¹ * a⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hAN a ha) (x⁻¹)).mp (H.inv_mem hxH)
    have hcommH : x * a * x⁻¹ * a⁻¹ ∈ H := by
      rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
      exact H.mul_mem hxH haxH
    exact hAH _ hcommA hcommH

theorem sec9n_N0_le (h36 : Asc82Lemma36) (hB : Asc82Sec8B) (hT : Asc82Tab9M)
    (hctx : Sec9Choice G t L S z g B t₀) :
    (L ⊓ normalizer (Asub9 t t₀ B : Set G)) ⊔
        (CFSG.conjugate L g ⊓ normalizer (Asub9 t t₀ B : Set G)) ≤
      centMod (Asub9 t t₀ B) B := by
  have hctx' : Sec9Ctx G t L S z g B t₀ := hctx.toSec9Ctx
  have hAL : ∀ a ∈ Asub9 t t₀ B, a ∈ L → a ∈ B := sec9n_A_inf_L hT hctx'
  have hALg : ∀ a ∈ Asub9 t t₀ B, a ∈ CFSG.conjugate L g → a ∈ B :=
    fun a ha haLg => hctx.choice.ge ⟨ha, haLg⟩
  refine sup_le ?_ ?_
  · exact sec9n_inf_le_centMod (A := Asub9 t t₀ B) (B := B) (H := L) le_sup_right
      (fun b hb => (hctx.B_le hb).1) hAL (fun a ha => sec9n_A_mem_normalizer hctx' a ha)
  · exact sec9n_inf_le_centMod (A := Asub9 t t₀ B) (B := B) (H := CFSG.conjugate L g)
      le_sup_right (fun b hb => (hctx.choice.le hb).2) hALg
      (fun a ha => sec9n_A_mem_normalizer_conj h36 hB hctx' a ha)

end CFSG.OddStandard.SmallF3.Omega
