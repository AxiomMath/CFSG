module

public import CFSG.CGT.PushingUpLit.SolKNA.Prop18

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n (conjSubgroup_eq_self_iff)

variable {X : Type} [Group X] [Finite X]

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N) [N.Normal]
include S

theorem exists_mul_of_conj_mem {x : X}
    (hx : QuotientGroup.mk' N x ∈ Subgroup.normalizer ((R.map (QuotientGroup.mk' N) :
      Subgroup (X ⧸ N)) : Set (X ⧸ N))) {r : X} (hr : r ∈ R) :
    ∃ r' ∈ R, ∃ n ∈ N, x * r * x⁻¹ = r' * n := by
  have h1 : QuotientGroup.mk' N x * QuotientGroup.mk' N r * (QuotientGroup.mk' N x)⁻¹ ∈
      R.map (QuotientGroup.mk' N) :=
    (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨r, hr, rfl⟩
  obtain ⟨r', hr', hr'e⟩ := h1
  refine ⟨r', hr', r'⁻¹ * (x * r * x⁻¹), ?_, by group⟩
  rw [← mk_eq_one_iff, map_mul, map_inv, hr'e, map_mul, map_mul, map_inv, inv_mul_cancel]

theorem mem_normalizer_of_image {x : X}
    (hx : QuotientGroup.mk' N x ∈ Subgroup.normalizer ((R.map (QuotientGroup.mk' N) :
      Subgroup (X ⧸ N)) : Set (X ⧸ N))) : x ∈ Subgroup.normalizer (R : Set X) := by
  have hx' : QuotientGroup.mk' N x⁻¹ ∈ Subgroup.normalizer ((R.map (QuotientGroup.mk' N) :
      Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hx
  have hLle : ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro l hl
    have hlN : l ∈ N := S.L_le_N hl
    have hxN : x * l * x⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem l hlN x
    obtain ⟨t, ht, htN⟩ := S.exists_mem_R_notMem_N
    have hcomm : t * (x * l * x⁻¹) = (x * l * x⁻¹) * t := by
      obtain ⟨r', hr', n, hn, hrn⟩ := S.exists_mul_of_conj_mem hx' ht
      rw [inv_inv] at hrn
      have e1 : t * (x * l * x⁻¹) = x * ((r' * n) * l) * x⁻¹ := by
        calc t * (x * l * x⁻¹) = x * (x⁻¹ * t * x) * l * x⁻¹ := by group
          _ = x * ((r' * n) * l) * x⁻¹ := by rw [hrn]; group
      have e2 : (x * l * x⁻¹) * t = x * (l * (r' * n)) * x⁻¹ := by
        calc (x * l * x⁻¹) * t = x * l * (x⁻¹ * t * x) * x⁻¹ := by group
          _ = x * (l * (r' * n)) * x⁻¹ := by rw [hrn]; group
      rw [e1, e2]
      congr 2
      calc r' * n * l = r' * (n * l) := by group
        _ = r' * (l * n) := by rw [S.comm_N hn hlN]
        _ = (r' * l) * n := by group
        _ = (l * r') * n := by rw [(S.L_cent l hl r' hr').symm]
        _ = l * (r' * n) := by group
    have hR : x * l * x⁻¹ ∈ R := S.cent_R ht htN hxN hcomm
    have hRN : x * l * x⁻¹ ∈ R ⊓ N := Subgroup.mem_inf.mpr ⟨hR, hxN⟩
    rwa [S.inf_N] at hRN
  have hle : conjSubgroup x L ≤ L := fun y hy => by
    have h1 := hLle _ (mem_conjSubgroup.mp hy)
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at h1
  have heq : conjSubgroup x L = L :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.RankThree.GF2n.card_conjSubgroup])
  have hne : R ⊓ conjSubgroup x R ≠ ⊥ := by
    intro hbot
    apply S.ne_bot
    rw [eq_bot_iff, ← hbot]
    refine le_inf S.L_le ?_
    calc L = conjSubgroup x L := heq.symm
      _ ≤ conjSubgroup x R := Subgroup.map_mono S.L_le
  exact conjSubgroup_eq_self_iff.mp (CFSG.RankThree.GF2n.conjSubgroup_eq_of_isTI S.ti hne)

theorem comm_mem_L_of_image_centralizes {p : X}
    (hp : ∀ r ∈ R, QuotientGroup.mk' N p * QuotientGroup.mk' N r =
      QuotientGroup.mk' N r * QuotientGroup.mk' N p) {r : X} (hr : r ∈ R) :
    p * r * p⁻¹ * r⁻¹ ∈ L := by
  have hpn : p ∈ Subgroup.normalizer (R : Set X) := by
    refine S.mem_normalizer_of_image (Subgroup.mem_normalizer_iff.mpr fun y => ?_)
    have key : ∀ z ∈ R.map (QuotientGroup.mk' N),
        QuotientGroup.mk' N p * z * (QuotientGroup.mk' N p)⁻¹ = z := by
      rintro _ ⟨r', hr', rfl⟩
      rw [hp r' hr']
      group
    constructor
    · intro hy
      rw [key y hy]
      exact hy
    · intro hy
      have h1 := key _ hy
      have h2 : QuotientGroup.mk' N p * y * (QuotientGroup.mk' N p)⁻¹ = y := by
        calc QuotientGroup.mk' N p * y * (QuotientGroup.mk' N p)⁻¹
            = (QuotientGroup.mk' N p)⁻¹ * (QuotientGroup.mk' N p *
                (QuotientGroup.mk' N p * y * (QuotientGroup.mk' N p)⁻¹) *
                (QuotientGroup.mk' N p)⁻¹) * QuotientGroup.mk' N p := by group
          _ = (QuotientGroup.mk' N p)⁻¹ * (QuotientGroup.mk' N p * y *
                (QuotientGroup.mk' N p)⁻¹) * QuotientGroup.mk' N p := by rw [h1]
          _ = y := by group
      rw [h2] at hy
      exact hy
  have h1 : p * r * p⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hpn r).mp hr
  have h2 : p * r * p⁻¹ * r⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem hr)
  have h3 : p * r * p⁻¹ * r⁻¹ ∈ N := by
    rw [← mk_eq_one_iff]
    simp only [map_mul, map_inv]
    rw [hp r hr]
    group
  have := Subgroup.mem_inf.mpr ⟨h2, h3⟩
  rwa [S.inf_N] at this

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
