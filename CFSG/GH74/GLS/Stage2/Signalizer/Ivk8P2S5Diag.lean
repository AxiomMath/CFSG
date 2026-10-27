module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Proj
public import CFSG.GH74.AS16.Standard
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Diag

variable {G : Type} [Group G] [Finite G]

theorem diag_one {K L J : Subgroup G} (hKL : ∀ a ∈ K, ∀ b ∈ L, a * b = b * a)
    (hK : CFSG.IsQuasisimple ↥K) (hJ : CFSG.IsQuasisimple ↥J) (hJle : J ≤ K ⊔ L)
    (hJL : ¬ J ≤ L) (hord : ordq K ≤ ordq J) {g : G} (hgK : g ∈ normalizer (K : Set G))
    (hgL : g ∈ normalizer (L : Set G)) (hgJ : ∀ j ∈ J, g * j * g⁻¹ = j) :
    g ∈ centralizer (K : Set G) := by
  have : Group.IsPerfect ↥K := hK.1
  obtain ⟨-, hsurj⟩ := proj_onto hKL hJ hJle hJL
  refine mem_centralizer_of_comm_central hgK fun j hj k hk => ?_
  obtain ⟨a', ha', b, hb, hab, hcen⟩ := hsurj hord j hj
  have hz : CenK K (a'⁻¹ * j) := by
    have := hcen.inv
    simpa using this
  have hu : g * a' * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hgK a').1 ha'
  have hv : g * b * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgL b).1 hb
  have hprod : g * a' * g⁻¹ * (g * b * g⁻¹) = a' * b := by
    have := hgJ _ hab
    calc g * a' * g⁻¹ * (g * b * g⁻¹) = g * (a' * b) * g⁻¹ := by group
      _ = a' * b := this
  have hc : a'⁻¹ * (g * a' * g⁻¹) = b * (g * b * g⁻¹)⁻¹ := by
    calc a'⁻¹ * (g * a' * g⁻¹) = a'⁻¹ * (g * a' * g⁻¹ * (g * b * g⁻¹)) * (g * b * g⁻¹)⁻¹ := by
          group
      _ = b * (g * b * g⁻¹)⁻¹ := by rw [hprod]; group
  have hcK : a'⁻¹ * (g * a' * g⁻¹) ∈ K := K.mul_mem (K.inv_mem ha') hu
  have hcL : a'⁻¹ * (g * a' * g⁻¹) ∈ L := by
    rw [hc]
    exact L.mul_mem hb (L.inv_mem hv)
  have hcc : CenK K (a'⁻¹ * (g * a' * g⁻¹)) := CenK.of_mem_inf hKL hcK hcL
  have hw : CenK K (g * (a'⁻¹ * j) * g⁻¹) := hz.conj hgK
  have hζ : CenK K ((a'⁻¹ * (g * a' * g⁻¹)) * (g * (a'⁻¹ * j) * g⁻¹) * (a'⁻¹ * j)⁻¹) :=
    (hcc.mul hw).mul hz.inv
  have e : g * j * g⁻¹ * j⁻¹ = a' * ((a'⁻¹ * (g * a' * g⁻¹)) * (g * (a'⁻¹ * j) * g⁻¹) *
      (a'⁻¹ * j)⁻¹) * a'⁻¹ := by group
  have hcomm := hζ.2 a' ha'
  have e2 : a' * ((a'⁻¹ * (g * a' * g⁻¹)) * (g * (a'⁻¹ * j) * g⁻¹) * (a'⁻¹ * j)⁻¹) * a'⁻¹ =
      (a'⁻¹ * (g * a' * g⁻¹)) * (g * (a'⁻¹ * j) * g⁻¹) * (a'⁻¹ * j)⁻¹ := by
    calc _ = ((a'⁻¹ * (g * a' * g⁻¹)) * (g * (a'⁻¹ * j) * g⁻¹) * (a'⁻¹ * j)⁻¹) * a' * a'⁻¹ := by
          rw [← hcomm]
      _ = _ := by group
  rw [e, e2]
  exact hζ.2 k hk

end Diag

section Comp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cj_cj (b c : G) (X : Subgroup G) : cj b (cj c X) = cj (b * c) X := by
  unfold cj
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem isCompIn_cj {Y K : Subgroup G} {v : G} (hv : v ∈ normalizer (Y : Set G))
    (hK : IsCompIn Y K) : IsCompIn Y (cj v K) := by
  have h := CFSG.GH74.AS16.isCompIn_conj hK v⁻¹
  have hY : conjugate Y v⁻¹ = Y := by
    simpa [conjugate, cj] using cj_eq_of_mem_normalizer hv
  rw [hY] at h
  simpa [conjugate, cj] using h

omit [Finite G] in
theorem cj_fix_of_odd {Y K₁ K₂ : Subgroup G} (hall : ∀ K, IsCompIn Y K → K = K₁ ∨ K = K₂)
    (h12 : K₁ ≠ K₂) (hK₁ : IsCompIn Y K₁) (hK₂ : IsCompIn Y K₂) {v : G}
    (hv : v ∈ normalizer (Y : Set G)) (hodd : Odd (orderOf v)) :
    v ∈ normalizer (K₁ : Set G) := by
  have key : cj v K₁ = K₁ := by
    by_contra hne
    have h1 : cj v K₁ = K₂ := (hall _ (isCompIn_cj hv hK₁)).resolve_left hne
    have h2 : cj v K₂ = K₁ := by
      rcases hall _ (isCompIn_cj hv hK₂) with h | h
      · exact h
      · exact absurd (cj_inj (h1.trans h.symm)) h12
    have hsq : v ^ 2 ∈ normalizer (K₁ : Set G) := by
      refine mem_normalizer_of_cj_eq ?_
      rw [pow_two, ← cj_cj, h1, h2]
    exact hne (cj_eq_of_mem_normalizer
      (mem_of_sq_mem (N := orderOf v) hodd (pow_orderOf_eq_one v) hsq))
  exact mem_normalizer_of_cj_eq key

theorem commute_of_isCompIn {Y K₁ K₂ : Subgroup G} (h1 : IsCompIn Y K₁) (h2 : IsCompIn Y K₂)
    (hne : K₁ ≠ K₂) : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
  rcases CFSG.LocalCores.distinct_components_commute h1.2 h2.2 with h | h
  · exfalso
    apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_eq_left.2 h1.1, inf_eq_left.2 h2.1] at this
  · intro a ha b hb
    have hx : (⟨a, h1.1 ha⟩ : ↥Y) ∈ K₁.subgroupOf Y := ha
    have hy : (⟨b, h2.1 hb⟩ : ↥Y) ∈ K₂.subgroupOf Y := hb
    have hc := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at hc
    have := commutatorElement_eq_one_iff_mul_comm.1 hc
    exact congrArg Subtype.val this

end Comp

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
