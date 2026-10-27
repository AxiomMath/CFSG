module

public import CFSG.GH74.Generic.BProg.B3.S3Pump306aR5
public import CFSG.GH74.Generic.S3.LyVertCore
public import CFSG.Quasithin.Background.B5FinOutAlt
public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Pump306

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.LocalAnalysis.ComponentInitial Equiv
  Equiv.Perm Subgroup
open scoped commutatorElement

variable {n : ℕ}

theorem cj_cj (σ : Perm (Fin n)) (a : alternatingGroup (Fin n)) : cj σ (cj σ a) = cj (σ * σ) a := by
  apply Subtype.ext
  show σ * (σ * (a : Perm (Fin n)) * σ⁻¹) * σ⁻¹ = (σ * σ) * (a : Perm (Fin n)) * (σ * σ)⁻¹
  group

theorem false_of_alt_pair {Y : Type} [Group Y] [Finite Y] (hgen : Gen4 Y) (hn7 : 7 ≤ n) (hn8 : n ≤ 8)
    {ι : alternatingGroup (Fin n) →* Y} (hι : Function.Injective ι) (hL : CFSG.IsComponent ι.range)
    {s : Y} (hs2 : s * s = 1) {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hodd : Perm.sign σ = -1)
    (hs : ActsAs s ι σ) (hcomm : s ∈ _root_.commutator Y) : False := by
  classical
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hmemL : ∀ a, ι a ∈ ι.range := fun a => ⟨a, rfl⟩
  have hsN : s ∈ normalizer (ι.range : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨a, rfl⟩
      rw [hs a]
      exact hmemL _
    · rintro ⟨b, hb⟩
      have h1 : s * (s * z * s⁻¹) * s⁻¹ = z := by
        rw [hsinv]
        calc s * (s * z * s) * s = (s * s) * z * (s * s) := by group
          _ = z := by rw [hs2]; group
      have h2 : z = ι (cj σ b) := by
        rw [← hs b, hb, h1]
      rw [h2]
      exact hmemL _
  let e : alternatingGroup (Fin n) ≃* ↥ι.range := MonoidHom.ofInjective hι
  have hOut : CFSG.Quasithin.OutAbelian ↥ι.range :=
    CFSG.Quasithin.outAbelian_of_mulEquiv e (CFSG.Quasithin.outAbelian_alternatingGroup (by omega) hn8)
  have hN₁ : _root_.commutator (MulAut ↥ι.range) ≤ (MulAut.conj : ↥ι.range →* MulAut ↥ι.range).range := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.2 fun φ _ ψ _ => hOut φ ψ
  have hout' : ι.range.normalizerMonoidHom ⟨s, hsN⟩ ∉
      (MulAut.conj : ↥ι.range →* MulAut ↥ι.range).range := by
    rintro ⟨ℓ, hℓ⟩
    obtain ⟨a₀, ha₀⟩ := ℓ.2
    have key : ∀ a, cj σ a = a₀ * a * a₀⁻¹ := by
      intro a
      apply hι
      have h1 := congrArg (fun f : MulAut ↥ι.range => ((f ⟨ι a, hmemL a⟩ : ↥ι.range) : Y)) hℓ
      have h2 : (ℓ : Y) * ι a * (ℓ : Y)⁻¹ = s * ι a * s⁻¹ := h1
      rw [← hs a, ← h2, ← ha₀, map_mul, map_mul, map_inv]
    have := sign_eq_one_of_cj (by omega) a₀ key
    rw [hodd] at this
    exact absurd this (by decide)
  have hsL : conjSub s ι.range = ι.range := (mem_normalizer_iff_conjSub s).mp hsN
  have hsL' : conjSub s⁻¹ ι.range = ι.range :=
    (mem_normalizer_iff_conjSub s⁻¹).mp ((normalizer (ι.range : Set Y)).inv_mem hsN)
  have hx : ∀ c : Y, c⁻¹ * s * c ∈ normalizer (ι.range : Set Y) := by
    intro c
    rw [mem_normalizer_iff_conjSub, conjSub_mul, conjSub_mul]
    by_cases hcL : conjSub c ι.range = ι.range
    · rw [hcL, hsL]
      have := conjSub_inv_conjSub c ι.range
      rwa [hcL] at this
    · have hJc : CFSG.IsComponent (conjSub c ι.range) := isComponent_conjSub hL c
      have hcomp : ∀ M : Subgroup Y, CFSG.IsComponent M → M = ι.range ∨ M = conjSub c ι.range := by
        intro M hM
        have hLs : conjSub (c⁻¹)⁻¹ ι.range ≠ ι.range := by rwa [inv_inv]
        have := eq_or_eq_conj_of_gen4 hgen hL hLs hM
        rwa [inv_inv] at this
      have hsJ : conjSub s (conjSub c ι.range) = conjSub c ι.range := by
        rcases hcomp _ (isComponent_conjSub hJc s) with h | h
        · exfalso
          apply hcL
          have := conjSub_inv_conjSub s (conjSub c ι.range)
          rw [h, hsL'] at this
          exact this.symm
        · exact h
      rw [hsJ]
      exact conjSub_inv_conjSub c ι.range
  have hxi_false : ¬ (∀ (c : Y) (hc : c⁻¹ * s * c ∈ normalizer (ι.range : Set Y)),
      c ∉ normalizer (ι.range : Set Y) →
      ι.range.normalizerMonoidHom ⟨c⁻¹ * s * c, hc⟩ ∈
        (MulAut.conj : ↥ι.range →* MulAut ↥ι.range).range) := fun hxi =>
    (not_mem_commutator_of_conj_actions ι.range _ hN₁ s hx hsN hout' hxi) hcomm
  push Not at hxi_false
  obtain ⟨c, hc, hcn, hcout⟩ := hxi_false
  let ι₂ : alternatingGroup (Fin n) →* Y := (MulAut.conj c).toMonoidHom.comp ι
  have hι₂ : Function.Injective ι₂ := (MulAut.conj c).injective.comp hι
  have hcL : conjSub c ι.range ≠ ι.range := fun h => hcn ((mem_normalizer_iff_conjSub c).mpr h)
  have hJ : CFSG.IsComponent (conjSub c ι.range) := isComponent_conjSub hL c
  have hLJ : ⁅ι.range, conjSub c ι.range⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL hJ).resolve_left (fun h => hcL h.symm)
  have hcomm₂ : ∀ a b, ι a * ι₂ b = ι₂ b * ι a := fun a b =>
    mul_comm_of_commutator_eq_bot' hLJ (hmemL a) ⟨ι b, hmemL b, rfl⟩
  obtain ⟨σ', hσ'⟩ := CFSG.Quasithin.SteinbergCB.conjPerm_surjective (n := n) (Or.inr hn7)
    (MulAut.congr e.symm (ι.range.normalizerMonoidHom ⟨c⁻¹ * s * c, hc⟩))
  have hg_act : ∀ a, (c⁻¹ * s * c) * ι a * (c⁻¹ * s * c)⁻¹ = ι (cj σ' a) := by
    intro a
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin n)) =>
      ((f a : alternatingGroup (Fin n)) : Perm (Fin n))) hσ'
    simp only [CFSG.Quasithin.SteinbergCB.conjPerm_apply, MulAut.congr_apply] at h1
    have h2 : e.symm (ι.range.normalizerMonoidHom ⟨c⁻¹ * s * c, hc⟩ (e.symm.symm a)) = cj σ' a :=
      Subtype.ext h1.symm
    have h3 : ι.range.normalizerMonoidHom ⟨c⁻¹ * s * c, hc⟩ (e a) = e (cj σ' a) := by
      have := congrArg e h2
      simpa using this
    exact congrArg Subtype.val h3
  have hg2 : (c⁻¹ * s * c) * (c⁻¹ * s * c) = 1 := by
    calc (c⁻¹ * s * c) * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c := by group
      _ = 1 := by rw [hs2]; group
  have hσ'2 : σ' * σ' = 1 := by
    apply perm_eq_one_of_cj (by omega)
    intro a
    rw [← cj_cj]
    apply hι
    have hginv : (c⁻¹ * s * c)⁻¹ = c⁻¹ * s * c := inv_eq_of_mul_eq_one_right hg2
    rw [← hg_act (cj σ' a), ← hg_act a, hginv]
    calc (c⁻¹ * s * c) * ((c⁻¹ * s * c) * ι a * (c⁻¹ * s * c)) * (c⁻¹ * s * c)
        = ((c⁻¹ * s * c) * (c⁻¹ * s * c)) * ι a * ((c⁻¹ * s * c) * (c⁻¹ * s * c)) := by group
      _ = ι a := by rw [hg2]; group
  have hodd' : Perm.sign σ' = -1 := by
    by_contra hne
    have h1 : Perm.sign σ' = 1 := by
      rcases Int.units_eq_one_or (Perm.sign σ') with h | h
      · exact h
      · exact absurd h hne
    apply hcout
    refine ⟨e ⟨σ', Perm.mem_alternatingGroup.2 h1⟩, ?_⟩
    refine MulEquiv.ext fun x => Subtype.ext ?_
    obtain ⟨a, rfl⟩ := e.surjective x
    have h2 := hg_act a
    have h3 : cj σ' a = ⟨σ', Perm.mem_alternatingGroup.2 h1⟩ * a *
        (⟨σ', Perm.mem_alternatingGroup.2 h1⟩ : alternatingGroup (Fin n))⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_inv] at h2
    show ((e ⟨σ', _⟩ : ↥ι.range) : Y) * ((e a : ↥ι.range) : Y) * ((e ⟨σ', _⟩ : ↥ι.range) : Y)⁻¹ =
      (c⁻¹ * s * c) * ((e a : ↥ι.range) : Y) * (c⁻¹ * s * c)⁻¹
    exact h2.symm
  have hs₂ : ActsAs s ι₂ σ' := by
    intro a
    have h1 := hg_act a
    show s * (c * ι a * c⁻¹) * s⁻¹ = c * ι (cj σ' a) * c⁻¹
    rw [← h1]
    group
  exact not_gen4_of_two_alt (by omega) hι hι₂ hcomm₂ hs2 hσ hσ'2 hodd hodd' hs hs₂ hgen

end S3Pump306

end CFSG.GH74.Generic.BProg.B3
