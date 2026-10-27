module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec4FC_mem_sup_iff {D O : Subgroup G} (hc : ∀ o ∈ O, ∀ d ∈ D, o * d = d * o) {x : G} :
    x ∈ D ⊔ O ↔ ∃ d ∈ D, ∃ o ∈ O, x = d * o := by
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x : G | ∃ d ∈ D, ∃ o ∈ O, x = d * o}
        mul_mem' := by
          rintro a b ⟨d₁, hd₁, o₁, ho₁, rfl⟩ ⟨d₂, hd₂, o₂, ho₂, rfl⟩
          exact ⟨d₁ * d₂, D.mul_mem hd₁ hd₂, o₁ * o₂, O.mul_mem ho₁ ho₂, by
            calc d₁ * o₁ * (d₂ * o₂) = d₁ * (o₁ * d₂) * o₂ := by group
              _ = d₁ * (d₂ * o₁) * o₂ := by rw [hc o₁ ho₁ d₂ hd₂]
              _ = (d₁ * d₂) * (o₁ * o₂) := by group⟩
        inv_mem' := by
          rintro a ⟨d, hd, o, ho, rfl⟩
          refine ⟨d⁻¹, D.inv_mem hd, o⁻¹, O.inv_mem ho, ?_⟩
          rw [mul_inv_rev]
          exact ((commute_iff_eq o d).mpr (hc o ho d hd)).inv_inv.eq
        one_mem' := ⟨1, D.one_mem, 1, O.one_mem, by simp⟩ }
    have hle : D ⊔ O ≤ P :=
      sup_le (fun d hd => ⟨d, hd, 1, O.one_mem, by simp⟩)
        (fun o ho => ⟨1, D.one_mem, o, ho, by simp⟩)
    exact hle hx
  · rintro ⟨d, hd, o, ho, rfl⟩
    exact (D ⊔ O).mul_mem (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right ho)

private theorem sec4FC_mem_left_of_mem_sup_of_orderOf_eq_two {D Z : Subgroup G}
    (hc : ∀ z ∈ Z, ∀ d ∈ D, z * d = d * z) (hodd : Odd (Nat.card Z))
    {v : G} (hv : v ∈ D ⊔ Z) (hv2 : orderOf v = 2) : v ∈ D := by
  obtain ⟨d, hd, o, ho, hvo⟩ := (sec4FC_mem_sup_iff hc).mp hv
  have ho_pow : o ^ Nat.card Z = 1 := by
    have h : (⟨o, ho⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hv2' : v ^ 2 = 1 := by
    have h := pow_orderOf_eq_one v
    rwa [hv2] at h
  have hv_pow : v ^ Nat.card Z = v := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul v 2 k, hv2', one_pow, one_mul]
  have hdo : Commute d o := (hc o ho d hd).symm
  have hv_eq : v = d ^ Nat.card Z := by
    calc v = v ^ Nat.card Z := hv_pow.symm
      _ = (d * o) ^ Nat.card Z := by rw [hvo]
      _ = d ^ Nat.card Z * o ^ Nat.card Z := hdo.mul_pow _
      _ = d ^ Nat.card Z := by rw [ho_pow, mul_one]
  rw [hv_eq]
  exact D.pow_mem hd _

private theorem le_of_isPerfect_le_sup_of_central {H Z K : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ x ∈ H ⊔ Z, z * x = x * z) (hKH : K ≤ H ⊔ Z)
    (hperf : Group.IsPerfect K) : K ≤ H := by
  have hc : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z :=
    fun z hz h hh => hZ z hz h (Subgroup.mem_sup_left hh)
  rw [← Subgroup.isPerfect_iff.mp hperf]
  refine Subgroup.commutator_le.mpr ?_
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨d₁, hd₁, o₁, ho₁, rfl⟩ := (sec4FC_mem_sup_iff hc).mp (hKH hk₁)
  obtain ⟨d₂, hd₂, o₂, ho₂, rfl⟩ := (sec4FC_mem_sup_iff hc).mp (hKH hk₂)
  have hxb : Commute o₁ d₂ := hZ o₁ ho₁ d₂ (Subgroup.mem_sup_left hd₂)
  have hay : Commute d₁ o₂ := (hZ o₂ ho₂ d₁ (Subgroup.mem_sup_left hd₁)).symm
  have hxy : Commute o₁ o₂ := hZ o₁ ho₁ o₂ (Subgroup.mem_sup_right ho₂)
  have hcomm : ⁅d₁ * o₁, d₂ * o₂⁆ = ⁅d₁, d₂⁆ := by
    simp only [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_left_eq_conj_mul, hxb.commutator_eq, hxy.commutator_eq,
      hay.commutator_eq]
    group
  rw [hcomm, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hd₁ hd₂) (H.inv_mem hd₁)) (H.inv_mem hd₂)

private theorem isComponentIn_sup_central_iff {H Z : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ x ∈ H ⊔ Z, z * x = x * z) {K : Subgroup G} :
    IsComponentIn K (H ⊔ Z) ↔ IsComponentIn K H := by
  constructor
  · intro h
    have hKH : K ≤ H := le_of_isPerfect_le_sup_of_central hZ h.1 h.isQuasisimple.1
    exact h.mono hKH le_sup_left
  · intro h
    have hZcent : Z ≤ Subgroup.centralizer (H : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (hZ z hz x (Subgroup.mem_sup_left hx)).symm
    have hHnormal : (H.subgroupOf (H ⊔ Z)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer
          (hZcent.trans (Subgroup.centralizer_le_normalizer (H : Set G))))
    have hHsn : ((K.subgroupOf (H ⊔ Z)).subgroupOf (H.subgroupOf (H ⊔ Z))).IsSubnormal := by
      have hcom := Subgroup.IsSubnormal.comap
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := H ⊔ Z) le_sup_left).toMonoidHom h.2.2
      have heq : (K.subgroupOf (H ⊔ Z)).subgroupOf (H.subgroupOf (H ⊔ Z)) =
          (K.subgroupOf H).comap
            (Subgroup.subgroupOfEquivOfLe (H := H) (K := H ⊔ Z) le_sup_left).toMonoidHom := by
        ext x
        simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
        rfl
      simpa [heq] using hcom
    have hKsn : (K.subgroupOf (H ⊔ Z)).IsSubnormal :=
      Subgroup.IsSubnormal.trans (fun x hx => h.1 hx) hHsn hHnormal.isSubnormal
    exact isComponentIn_of_subnormal (h.1.trans le_sup_left) h.isQuasisimple hKsn

private theorem sup_inf_central_eq {D Z : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ x ∈ D ⊔ Z, z * x = x * z) (hc : ∀ z ∈ Z, ∀ d ∈ D, z * d = d * z)
    {v : G} (hv : v ∈ D) :
    (D ⊔ Z) ⊓ centralizer ({v} : Set G) = (D ⊓ centralizer ({v} : Set G)) ⊔ Z := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxsup, hxc⟩ := hx
    obtain ⟨d, hd, z, hz, rfl⟩ := (sec4FC_mem_sup_iff hc).mp hxsup
    have hzv : Commute z v := hZ z hz v (Subgroup.mem_sup_left hv)
    have hdzv : Commute (d * z) v := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hdv : Commute d v := by
      have h := hdzv.mul_left hzv.inv_left
      convert h using 1
      group
    exact ((D ⊓ centralizer ({v} : Set G)) ⊔ Z).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
        ⟨hd, Subgroup.mem_centralizer_singleton_iff.mpr hdv⟩)) (Subgroup.mem_sup_right hz)
  · refine sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right) (le_inf le_sup_right ?_)
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hZ z hz v (Subgroup.mem_sup_left hv))

theorem Asc82SetU.sup_central_iff {D Z : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ x ∈ D ⊔ Z, z * x = x * z) (hodd : Odd (Nat.card Z)) {v : G} :
    Asc82SetU (D ⊔ Z) v ↔ Asc82SetU D v := by
  have hc : ∀ z ∈ Z, ∀ d ∈ D, z * d = d * z :=
    fun z hz d hd => hZ z hz d (Subgroup.mem_sup_left hd)
  have hZ' : ∀ z ∈ Z, ∀ x ∈ (D ⊓ centralizer ({v} : Set G)) ⊔ Z, z * x = x * z :=
    fun z hz x hx =>
      hZ z hz x (sup_le_sup (inf_le_left : D ⊓ centralizer ({v} : Set G) ≤ D)
        (le_rfl : Z ≤ Z) hx)
  constructor
  · rintro ⟨hv, hv2, K, hK, hLie⟩
    have hvD : v ∈ D := sec4FC_mem_left_of_mem_sup_of_orderOf_eq_two hc hodd hv hv2
    have hEq : (D ⊔ Z) ⊓ centralizer ({v} : Set G) =
        (D ⊓ centralizer ({v} : Set G)) ⊔ Z := sup_inf_central_eq hZ hc hvD
    rw [hEq] at hK
    exact ⟨hvD, hv2, K,
      (isComponentIn_sup_central_iff (H := D ⊓ centralizer ({v} : Set G)) (Z := Z) hZ').mp hK,
      hLie⟩
  · rintro ⟨hv, hv2, K, hK, hLie⟩
    have hEq : (D ⊔ Z) ⊓ centralizer ({v} : Set G) =
        (D ⊓ centralizer ({v} : Set G)) ⊔ Z := sup_inf_central_eq hZ hc hv
    have hK' : IsComponentIn K ((D ⊔ Z) ⊓ centralizer ({v} : Set G)) := by
      rw [hEq]
      exact (isComponentIn_sup_central_iff (H := D ⊓ centralizer ({v} : Set G))
        (Z := Z) hZ').mpr hK
    exact ⟨Subgroup.mem_sup_left hv, hv2, K, hK', hLie⟩

theorem Asc82SetU.iff_of_oddCent {D E O : Subgroup G} (hDE : D ≤ E) (hEO : E ≤ D ⊔ O)
    (hO : Sec4FOddCent O E) {v : G} : Asc82SetU E v ↔ Asc82SetU D v := by
  obtain ⟨hOc, hOodd⟩ := hO
  have hcOD : ∀ o ∈ O, ∀ d ∈ D, o * d = d * o := fun o ho d hd => hOc o ho d (hDE hd)
  have hEeq : E = D ⊔ (E ⊓ O) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨d, hd, o, ho, rfl⟩ := (sec4FC_mem_sup_iff hcOD).mp (hEO hx)
      have hoE : o ∈ E := by
        have h : d⁻¹ * (d * o) ∈ E := E.mul_mem (E.inv_mem (hDE hd)) hx
        simpa using h
      exact (D ⊔ (E ⊓ O)).mul_mem (Subgroup.mem_sup_left hd)
        (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hoE, ho⟩))
    · exact sup_le hDE inf_le_left
  rw [hEeq]
  refine Asc82SetU.sup_central_iff (D := D) (Z := E ⊓ O) ?_ ?_
  · intro z hz x hx
    exact hOc z hz.2 x (sup_le hDE inf_le_left hx)
  · exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

theorem Asc82SetU.congr_oddCent {D₁ D₂ E O : Subgroup G} (h₁ : D₁ ≤ E) (h₂ : D₂ ≤ E)
    (h₁O : E ≤ D₁ ⊔ O) (h₂O : E ≤ D₂ ⊔ O) (hO : Sec4FOddCent O E) {v : G} :
    Asc82SetU D₁ v ↔ Asc82SetU D₂ v :=
  (Asc82SetU.iff_of_oddCent h₁ h₁O hO).symm.trans (Asc82SetU.iff_of_oddCent h₂ h₂O hO)

end CFSG.OddStandard.SmallF3.Omega
