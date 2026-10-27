module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

variable {p : ℕ} [hp : Fact p.Prime]

theorem isPGroup_of_coprime_eq_one {A : Type*} [Group A] [Finite A]
    (h : ∀ a : A, (orderOf a).Coprime p → a = 1) : IsPGroup p A := by
  intro a
  obtain ⟨k, m, hm, hdecomp⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a).ne' p hp.out.ne_one
  refine ⟨k, h _ ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero k hp.out.ne_zero) ⟨m, hdecomp⟩, hdecomp,
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm

variable {P : Type*} [Group P] [Finite P]

theorem odd_critical_exponent_subgroup (hp2 : p ≠ 2) (hP : IsPGroup p P) [Nontrivial P] :
    ∃ D : Subgroup P, D.Characteristic ∧ D ≠ ⊥ ∧
      ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P) ∧ (∀ x ∈ D, x ^ p = 1) ∧
      IsPGroup p (fixingSubgroup (MulAut P) (D : Set P)) := by
  obtain ⟨⟨C, hC⟩, hne⟩ := thompson_critical_subgroup hP
  have hCbot : C ≠ ⊥ := hne C hC inferInstance
  obtain ⟨hCchar, hCΦ, hCcomm, hCcen⟩ := hC
  have hCp : IsPGroup p C := hP.to_subgroup C
  have hΦ : frattini C ≤ center C := by
    intro x hx
    rw [mem_center_iff]
    intro g
    have hxZ := hCΦ (mem_map_of_mem C.subtype hx)
    exact Subtype.ext (mem_centralizer_iff.1 hxZ.2 g g.2)
  have hCnt : Nontrivial C := (nontrivial_iff_ne_bot C).2 hCbot
  obtain ⟨-, -, -, hset, hΩchar, hΩne⟩ := central_frattini_odd_power_map hp2 hCp hΦ
  set Ω := omega₁ (G := C) (p := p) with hΩdef
  have hΩpow : ∀ y : C, y ∈ Ω → y ^ p = 1 := fun y hy => by
    rw [← SetLike.mem_coe, hset] at hy
    exact hy
  set D := Ω.map C.subtype with hDdef
  have hDchar : D.Characteristic := inferInstance
  have hDC : D ≤ C := map_subtype_le Ω
  refine ⟨D, hDchar, ?_, ?_, ?_, ?_⟩
  · rw [Ne, map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact hΩne hCnt
  · rw [commutator_le]
    intro d hd g _
    have hdC := hDC hd
    have hz : ⁅d, g⁆ ∈ C ⊓ centralizer (C : Set P) :=
      commutatorElement_mem_swap (hCcomm (commutator_mem_commutator (mem_top g) hdC))
    refine ⟨?_, centralizer_le (SetLike.coe_subset_coe.2 hDC) hz.2⟩
    have e : ⁅d, g⁆ = d * (g * d⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hd (Normal.conj_mem inferInstance _ (inv_mem hd) g)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    rw [subtype_apply, ← coe_pow, hΩpow y hy, coe_one]
  · apply isPGroup_of_coprime_eq_one
    rintro ⟨α, hα⟩ hcop
    rw [orderOf_mk] at hcop
    have hfixD : ∀ x ∈ D, α x = x := fun x hx =>
      ((mem_fixingSubgroup_iff (MulAut P)).1 hα) x hx
    set αC := MulAut.characteristic C α with hαC
    have hαCcop : (orderOf αC).Coprime p :=
      Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ α) hcop
    have hαCfix : ∀ y ∈ Ω, αC y = y := fun y hy =>
      Subtype.ext (hfixD (y : P) (mem_map_of_mem C.subtype hy))
    have hαC1 : αC = 1 := central_frattini_odd_aut_detection hp2 hCp hΦ αC hαCcop hαCfix
    have hfixC : ∀ c ∈ C, α c = c := fun c hc => by
      have := congrArg (fun β : MulAut C => ((β ⟨c, hc⟩ : C) : P)) hαC1
      exact this
    have hself : centralizer (C : Set P) ≤ C := by
      rw [hCcen]
      exact inf_le_left
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hcopP : (orderOf α).Coprime (Nat.card P) := by
      rw [hn]
      exact Nat.Coprime.pow_right n hcop
    have h1 := CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing p hP
      C hself α (orderOf α) (pow_orderOf_eq_one α) hcopP hfixC
    exact Subtype.ext h1

end CFSG.SectionRank.Ccomm
