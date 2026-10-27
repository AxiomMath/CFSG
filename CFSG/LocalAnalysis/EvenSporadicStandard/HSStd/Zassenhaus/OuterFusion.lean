module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Section

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard
open scoped commutatorElement

@[expose] def F {G : Type*} [Group G] (v t : G) : Prop :=
  ¬ ∃ g ∈ centralizer ({v} : Set G), g * t * g⁻¹ = t * v

@[expose] def bp {G : Type*} [Group G] (x : G) (a : Bool) : G := if a then x else 1

theorem bp_mul_bp {G : Type*} [Group G] {x : G} (hx : x * x = 1) (a : Bool) :
    bp x a * bp x a = 1 := by
  cases a <;> simp [bp, hx]

theorem exists_three_distinct : ∀ i j : Fin 8, ∃ a b c : Fin 8, a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧
    b ≠ a ∧ c ≠ i ∧ c ≠ j ∧ c ≠ a ∧ c ≠ b := by decide +kernel

theorem perm8_eq_one_of_comm {σ : Perm (Fin 8)}
    (h : ∀ τ ∈ alternatingGroup (Fin 8), σ * τ = τ * σ) : σ = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  obtain ⟨a, b, c, hai, haj, hbi, hbj, hba, hci, hcj, hca, hcb⟩ := exists_three_distinct i (σ i)
  set τ := swap i a * swap b c with hτ
  have hτA : τ ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, hτ, map_mul, Equiv.Perm.sign_swap hai.symm,
      Equiv.Perm.sign_swap hcb.symm]
    decide
  have hτi : τ i = a := by
    rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne hbi.symm hci.symm, swap_apply_left]
  have hτj : τ (σ i) = σ i := by
    rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne hbj.symm hcj.symm,
      swap_apply_of_ne_of_ne hi haj.symm]
  have h1 := congrArg (fun f => f i) (h τ hτA)
  simp only [Perm.mul_apply, hτi, hτj] at h1
  exact hai (σ.injective h1)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

theorem t_sq (h : HSOuterSetup G L t S z n v s) : t * t = 1 := by
  rw [← pow_two]
  exact h.t_two ▸ pow_orderOf_eq_one t

omit [Finite G] in
theorem derivedCentralizerIn_eq_commutator (L : Subgroup G) (v : G) :
    derivedCentralizerIn L v =
      ⁅centralizer ({v} : Set G) ⊓ L, centralizer ({v} : Set G) ⊓ L⁆ := by
  unfold derivedCentralizerIn
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem eq_one_of_comm_derived (h : HSOuterSetup G L t S z n v s) {y : G}
    (hy : y ∈ centralizer ({v} : Set G) ⊓ L)
    (hc : ∀ l ∈ derivedCentralizerIn L v, y * l = l * y) : y = 1 := by
  obtain ⟨e⟩ := h.ctx.v_cls
  set T := centralizer ({v} : Set G) ⊓ L with hT
  let ψ : Perm (Fin 8) →* G := T.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hrange : ψ.range = T := by
    ext g
    constructor
    · rintro ⟨σ, rfl⟩
      exact (e.symm σ).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [ψ]⟩
  have hΛ : derivedCentralizerIn L v = (alternatingGroup (Fin 8)).map ψ :=
    map_commutator_range ψ hψ T hrange
  have hψσ₀ : ψ (e ⟨y, hy⟩) = y := by simp [ψ]
  have h1 : e ⟨y, hy⟩ = 1 := perm8_eq_one_of_comm (fun τ hτ => by
    apply hψ
    rw [map_mul, map_mul, hψσ₀]
    exact hc _ (hΛ ▸ ⟨τ, hτ, rfl⟩))
  rw [← hψσ₀, h1, map_one]

theorem v_mem_centralizer_t (h : HSOuterSetup G L t S z n v s) :
    v ∈ centralizer ({t} : Set G) := h.ctx.fusion.le h.ctx.v_mem

theorem exists_decomp (h : HSOuterSetup G L t S z n v s) {d : G}
    (hd : d ∈ centralizer ({t} : Set G)) :
    ∃ β ∈ L, ∃ a b : Bool, d = β * bp t a * bp v b := by
  have hv2 : v * v = 1 := h.ctx.v_sq
  have ht2 : t * t = 1 := t_sq h
  have hvt : v ∈ centralizer ({t} : Set G) := v_mem_centralizer_t h
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have hidx : ((L ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))).index = 2 := h.index
  have hdich : d ∈ L ⊔ zpowers t ∨ d * v ∈ L ⊔ zpowers t := by
    by_contra hcon
    push Not at hcon
    let N : Subgroup ↥(centralizer ({t} : Set G)) :=
      (L ⊔ zpowers t).subgroupOf (centralizer {t})
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨d, hd⟩ : ↥(centralizer ({t} : Set G)))) (b := (⟨v, hvt⟩ : ↥(centralizer {t})))
    have hdN : (⟨d, hd⟩ : ↥(centralizer ({t} : Set G))) ∉ N := hcon.1
    have hvN : (⟨v, hvt⟩ : ↥(centralizer ({t} : Set G))) ∉ N := fun hv => h.ctx.v_outer hv
    have hdvN : (⟨d, hd⟩ * ⟨v, hvt⟩ : ↥(centralizer ({t} : Set G))) ∉ N := hcon.2
    exact hdvN (h1.2 (iff_of_false hdN hvN))
  obtain ⟨b, hb⟩ : ∃ b : Bool, d * bp v b ∈ L ⊔ zpowers t := by
    rcases hdich with hd' | hd'
    · exact ⟨false, by simpa [bp] using hd'⟩
    · exact ⟨true, by simpa [bp] using hd'⟩
  obtain ⟨β, hβ, j, hj⟩ := (mem_sup_zpowers_iff (fun β hβ => (htcomm β hβ : Commute β t))).1 hb
  obtain ⟨a, ha⟩ : ∃ a : Bool, t ^ j = bp t a := by
    rcases zpow_eq_one_or_self ht2 j with h1 | h1
    · exact ⟨false, by simpa [bp] using h1⟩
    · exact ⟨true, by simpa [bp] using h1⟩
  rw [ha] at hj
  refine ⟨β, hβ, a, b, ?_⟩
  calc d = d * (bp v b * bp v b) := by rw [bp_mul_bp hv2, mul_one]
    _ = (d * bp v b) * bp v b := by rw [mul_assoc]
    _ = β * bp t a * bp v b := by rw [← hj]

theorem centralizer_t_le_normalizer (h : HSOuterSetup G L t S z n v s) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  h.setting.1.centralizer_le_normalizer h.t_mem h.t_two

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
