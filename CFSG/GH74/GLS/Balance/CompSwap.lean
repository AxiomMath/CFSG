module

public import CFSG.GH74.GLS.Balance.CompNormalizes

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG
open scoped commutatorElement

namespace Comp

section Swap

variable {X : Type*} [Group X] [Finite X]

theorem swap_commute {x : X} {K : Subgroup X} (hK : IsComponent K)
    (hKx : x ∉ normalizer (K : Set X)) :
    ∀ a ∈ K, ∀ b ∈ K, a * (x * b * x⁻¹) = (x * b * x⁻¹) * a := by
  have hK' : IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
  have hne : K ≠ K.map (MulAut.conj x).toMonoidHom := by
    intro h
    apply hKx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hne
  have hle : K ≤ centralizer (K.map (MulAut.conj x).toMonoidHom : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro a ha b hb
  have hmem : x * b * x⁻¹ ∈ K.map (MulAut.conj x).toMonoidHom := ⟨b, hb, rfl⟩
  exact (mem_centralizer_iff.mp (hle ha) _ hmem).symm

end Swap

section Diag

variable {X : Type*} [Group X]

theorem exists_diagHom {x : X} {K : Subgroup X}
    (hc : ∀ a ∈ K, ∀ b ∈ K, a * (x * b * x⁻¹) = (x * b * x⁻¹) * a) :
    ∃ φ : K →* X, ∀ k : K, φ k = (k : X) * (x * k * x⁻¹) := by
  refine ⟨MonoidHom.mk' (fun k : K => (k : X) * (x * k * x⁻¹)) ?_, fun k => rfl⟩
  intro a b
  have h := hc b b.2 a a.2
  show ((a : X) * b) * (x * ((a : X) * b) * x⁻¹) = ((a : X) * (x * a * x⁻¹)) * ((b : X) * (x * b * x⁻¹))
  calc ((a : X) * b) * (x * ((a : X) * b) * x⁻¹)
      = a * (b * (x * a * x⁻¹)) * (x * b * x⁻¹) := by group
    _ = a * ((x * a * x⁻¹) * b) * (x * b * x⁻¹) := by rw [h]
    _ = ((a : X) * (x * a * x⁻¹)) * ((b : X) * (x * b * x⁻¹)) := by group

theorem diagHom_ker_le_center {x : X} {K : Subgroup X}
    (hc : ∀ a ∈ K, ∀ b ∈ K, a * (x * b * x⁻¹) = (x * b * x⁻¹) * a) {φ : K →* X}
    (hφ : ∀ k : K, φ k = (k : X) * (x * k * x⁻¹)) : φ.ker ≤ center K := by
  intro a ha
  rw [MonoidHom.mem_ker, hφ] at ha
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have h1 : x * (a : X) * x⁻¹ = (a : X)⁻¹ := eq_inv_of_mul_eq_one_right ha
  have h2 := hc g g.2 a a.2
  rw [h1] at h2
  change (g : X) * a = a * g
  calc (g : X) * a = a * ((a : X)⁻¹ * g) * a := by group
    _ = a * (g * (a : X)⁻¹) * a := by rw [← h2]
    _ = a * g := by group

theorem diagHom_mem_centralizer {x : X} {K : Subgroup X} (hx2 : x * x = 1)
    (hc : ∀ a ∈ K, ∀ b ∈ K, a * (x * b * x⁻¹) = (x * b * x⁻¹) * a) {φ : K →* X}
    (hφ : ∀ k : K, φ k = (k : X) * (x * k * x⁻¹)) (k : K) :
    φ k ∈ centralizer ({x} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff, hφ]
  have h := hc k k.2 k k.2
  have h0 : x * (x * (k : X) * x⁻¹) * x⁻¹ = k := by
    calc x * (x * (k : X) * x⁻¹) * x⁻¹ = (x * x) * k * (x * x)⁻¹ := by group
      _ = k := by rw [hx2]; group
  have h1 : x * ((k : X) * (x * k * x⁻¹)) * x⁻¹ = (k : X) * (x * k * x⁻¹) := by
    calc x * ((k : X) * (x * k * x⁻¹)) * x⁻¹
        = (x * k * x⁻¹) * (x * (x * (k : X) * x⁻¹) * x⁻¹) := by group
      _ = (x * k * x⁻¹) * k := by rw [h0]
      _ = (k : X) * (x * k * x⁻¹) := h.symm
  calc (k : X) * (x * k * x⁻¹) * x = (x * ((k : X) * (x * k * x⁻¹)) * x⁻¹) * x := by rw [h1]
    _ = x * ((k : X) * (x * k * x⁻¹)) := by group

end Diag

section Commutator

variable {X : Type*} [Group X]

theorem commutator_mem {K : Subgroup X} {r k : X} (hrK : r ∈ normalizer (K : Set X)) (hk : k ∈ K) :
    ⁅k, r⁆ ∈ K := by
  have h1 : r * k⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hrK k⁻¹).mp (inv_mem hk)
  have : ⁅k, r⁆ = k * (r * k⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem hk h1

theorem commutator_mul_of_commute {k k' r : X}
    (h1 : (r * k⁻¹ * r⁻¹) * k' = k' * (r * k⁻¹ * r⁻¹))
    (h2 : (r * k'⁻¹ * r⁻¹) * (r * k⁻¹ * r⁻¹) = (r * k⁻¹ * r⁻¹) * (r * k'⁻¹ * r⁻¹)) :
    ⁅k * k', r⁆ = ⁅k, r⁆ * ⁅k', r⁆ := by
  simp only [commutatorElement_def]
  calc k * k' * r * (k * k')⁻¹ * r⁻¹
      = k * k' * ((r * k'⁻¹ * r⁻¹) * (r * k⁻¹ * r⁻¹)) := by group
    _ = k * k' * ((r * k⁻¹ * r⁻¹) * (r * k'⁻¹ * r⁻¹)) := by rw [h2]
    _ = k * (k' * (r * k⁻¹ * r⁻¹)) * (r * k'⁻¹ * r⁻¹) := by group
    _ = k * ((r * k⁻¹ * r⁻¹) * k') * (r * k'⁻¹ * r⁻¹) := by rw [h1]
    _ = k * r * k⁻¹ * r⁻¹ * (k' * r * k'⁻¹ * r⁻¹) := by group

theorem commutator_diag {x r k : X} {K : Subgroup X} (hxr : x * r = r * x) (hk : k ∈ K)
    (hrK : r ∈ normalizer (K : Set X))
    (hc : ∀ a ∈ K, ∀ b ∈ K, a * (x * b * x⁻¹) = (x * b * x⁻¹) * a) :
    ⁅k * (x * k * x⁻¹), r⁆ = ⁅k, r⁆ * (x * ⁅k, r⁆ * x⁻¹) := by
  have hxr' : x * r * x⁻¹ = r := by rw [hxr]; group
  have hu : r * k⁻¹ * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hrK k⁻¹).mp (inv_mem hk)
  have hconj : x * ⁅k, r⁆ * x⁻¹ = ⁅x * k * x⁻¹, r⁆ := by
    simp only [commutatorElement_def]
    calc x * (k * r * k⁻¹ * r⁻¹) * x⁻¹
        = (x * k * x⁻¹) * (x * r * x⁻¹) * (x * k * x⁻¹)⁻¹ * (x * r * x⁻¹)⁻¹ := by group
      _ = (x * k * x⁻¹) * r * (x * k * x⁻¹)⁻¹ * r⁻¹ := by rw [hxr']
  have hv : x * (r * k⁻¹ * r⁻¹) * x⁻¹ = r * (x * k * x⁻¹)⁻¹ * r⁻¹ := by
    calc x * (r * k⁻¹ * r⁻¹) * x⁻¹
        = (x * r * x⁻¹) * (x * k * x⁻¹)⁻¹ * (x * r * x⁻¹)⁻¹ := by group
      _ = r * (x * k * x⁻¹)⁻¹ * r⁻¹ := by rw [hxr']
  rw [hconj]
  apply commutator_mul_of_commute
  · exact hc _ hu k hk
  · rw [← hv]
    exact (hc _ hu _ hu).symm

theorem commute_of_commutator_central {K : Subgroup X} (hperf : Group.IsPerfect K) {r : X}
    (hrK : r ∈ normalizer (K : Set X))
    (hc : ∀ k ∈ K, ∀ g ∈ K, g * ⁅k, r⁆ = ⁅k, r⁆ * g) : ∀ y ∈ K, r * y = y * r := by
  let ψ : K →* center K :=
    { toFun := fun k => ⟨⟨⁅(k : X), r⁆, commutator_mem hrK k.2⟩,
        mem_center_iff.mpr fun g => Subtype.ext (hc k k.2 g g.2)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        change ⁅((a : X) * b), r⁆ = ⁅(a : X), r⁆ * ⁅(b : X), r⁆
        have h1 := hc b b.2 a a.2
        have h2 := hc a a.2 ⁅(b : X), r⁆ (commutator_mem hrK b.2)
        have h3 : ⁅(a : X) * b, r⁆ = (a : X) * ⁅(b : X), r⁆ * (a : X)⁻¹ * ⁅(a : X), r⁆ := by
          simp only [commutatorElement_def]
          group
        calc ⁅(a : X) * b, r⁆ = (a : X) * ⁅(b : X), r⁆ * (a : X)⁻¹ * ⁅(a : X), r⁆ := h3
          _ = ⁅(b : X), r⁆ * (a : X) * (a : X)⁻¹ * ⁅(a : X), r⁆ := by rw [h1]
          _ = ⁅(b : X), r⁆ * ⁅(a : X), r⁆ := by group
          _ = ⁅(a : X), r⁆ * ⁅(b : X), r⁆ := h2 }
  have hker : commutator K ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  rw [Group.isPerfect_def.mp hperf] at hker
  intro y hy
  have h0 : ψ ⟨y, hy⟩ = 1 := MonoidHom.mem_ker.mp (hker (mem_top _))
  have h1 : ⁅y, r⁆ = 1 := congrArg (fun z : center K => ((z : K) : X)) h0
  have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
  exact h2.symm

end Commutator

end Comp

variable {X : Type} [Group X] [Finite X]

theorem commute_of_swap {x r : X} (hx : orderOf x = 2) (hxr : x * r = r * x) {K : Subgroup X}
    (hK : IsComponent K) (hKx : x ∉ normalizer (K : Set X)) (hrK : r ∈ normalizer (K : Set X))
    (O : Subgroup X) (hOodd : Odd (Nat.card O))
    (hOn : centralizer ({x} : Set X) ≤ normalizer (O : Set X))
    (hcomm : ∀ k ∈ K, ⁅k * (x * k * x⁻¹), r⁆ ∈ O) : ∀ y ∈ K, r * y = y * r := by
  have hx2 : x * x = 1 := by
    have : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    rwa [pow_two] at this
  have hc := Comp.swap_commute hK hKx
  obtain ⟨φ, hφ⟩ := Comp.exists_diagHom hc
  have hker := Comp.diagHom_ker_le_center hc hφ
  have hcen := Comp.diagHom_mem_centralizer hx2 hc hφ
  have hN : (O.comap φ).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_comap] at ha ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hOn (hcen g)) (φ a)).mp ha⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hN with htop | hle
  · exfalso
    have hrange : φ.range ≤ O := by
      rintro _ ⟨a, rfl⟩
      have : a ∈ O.comap φ := by rw [htop]; exact mem_top a
      exact this
    have hoddr : Odd (Nat.card φ.range) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hrange)
    have hdiv : (center K).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
    rw [Subgroup.index_ker] at hdiv
    have hodd' : Odd (Nat.card (K ⧸ center K)) := by
      rw [← Subgroup.index_eq_card]
      exact Odd.of_dvd_nat hoddr hdiv
    exact Comp.false_of_odd_quotient_center hK.1 hodd'
  · refine Comp.commute_of_commutator_central hK.1.1 hrK ?_
    intro k hk g hg
    have hk' : (⟨⁅k, r⁆, Comp.commutator_mem hrK hk⟩ : K) ∈ O.comap φ := by
      rw [Subgroup.mem_comap, hφ]
      change ⁅k, r⁆ * (x * ⁅k, r⁆ * x⁻¹) ∈ O
      rw [← Comp.commutator_diag hxr hk hrK hc]
      exact hcomm k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hle hk') ⟨g, hg⟩)

end CFSG.GH74.GLS.Balance
