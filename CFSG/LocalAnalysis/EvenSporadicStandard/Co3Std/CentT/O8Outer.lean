module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Defs
public import Certificates.Certificate450003
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeMain

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

private theorem o8Outer_congr_apply {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (ζ : MulAut K) (x : K') : MulAut.congr e ζ x = e (ζ (e.symm x)) := rfl

private theorem o8Outer_mem_fixedSubgroup {G : Type*} [Group G] {α : MulAut G} {s : G} :
    s ∈ fixedSubgroup α ↔ α s = s := Iff.rfl

private theorem o8Outer_congr_conj {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (q : K) :
    MulAut.congr e (MulAut.conj q) = MulAut.conj (e q) := by
  ext y
  rw [o8Outer_congr_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    e.apply_symm_apply]

private theorem o8Outer_map_fixedSubgroup {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (ζ : MulAut K) :
    (fixedSubgroup ζ).map e.toMonoidHom = fixedSubgroup (MulAut.congr e ζ) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [o8Outer_mem_fixedSubgroup, o8Outer_congr_apply]
    change e (ζ (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    exact congrArg e (o8Outer_mem_fixedSubgroup.mp hx)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [o8Outer_mem_fixedSubgroup]
    apply e.injective
    have hy' := o8Outer_mem_fixedSubgroup.mp hy
    rw [o8Outer_congr_apply] at hy'
    rw [hy', e.apply_symm_apply]

private theorem o8Outer_transport {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    (h : ∀ ζ : MulAut K', ζ * ζ = 1 → (∀ q : K', ζ ≠ MulAut.conj q) →
      4 < Nat.card (fixedSubgroup ζ)) :
    ∀ ζ : MulAut K, ζ * ζ = 1 → (∀ q : K, ζ ≠ MulAut.conj q) →
      4 < Nat.card (fixedSubgroup ζ) := by
  intro ζ hζ hout
  have hζ' : MulAut.congr e ζ * MulAut.congr e ζ = 1 := by
    rw [← map_mul, hζ, map_one]
  have hout' : ∀ q' : K', MulAut.congr e ζ ≠ MulAut.conj q' := by
    intro q' hq
    apply hout (e.symm q')
    apply (MulAut.congr e).injective
    rw [o8Outer_congr_conj, e.apply_symm_apply]
    exact hq
  calc 4 < Nat.card (fixedSubgroup (MulAut.congr e ζ)) := h _ hζ' hout'
    _ = Nat.card (fixedSubgroup ζ) := by
      rw [← o8Outer_map_fixedSubgroup, Subgroup.card_map_of_injective e.injective]

theorem o8OuterCent_check : o8OuterCentCheck () = true :=
  Certificates.certificate450003

private noncomputable def o8OuterCentU (i : ℕ) : ℕ → Equiv.Perm (Fin 360)
  | 0 => 1
  | k + 1 => centPerm i k

private theorem o8Outer_cent0Words_length {i : ℕ} (hi : i < 5) :
    (cent0Words.getD i []).length = 4 := by
  interval_cases i <;> rfl

private theorem o8Outer_rep_centU {i : ℕ} (hi : i < 5) (j : ℕ) :
    CFSG.Monster.B.Co2.Rep 360 (o8OuterCentArr i j) (o8OuterCentU i j) := by
  cases j with
  | zero => exact rep_idA
  | succ k => exact (centPerm_spec hi k).1

private theorem o8Outer_centU_mem {i : ℕ} (hi : i < 5) (j : ℕ) :
    o8OuterCentU i j ∈ omegaT := by
  cases j with
  | zero => exact omegaT.one_mem
  | succ k => exact (centPerm_spec hi k).2

private theorem o8Outer_centU_comm {i : ℕ} (hi : i < 5) {j : ℕ}
    (hj : j < 5) : o8OuterCentU i j * mainPerm i = mainPerm i * o8OuterCentU i j := by
  cases j with
  | zero => simp [o8OuterCentU]
  | succ k => exact centPerm_comm hi (by rw [o8Outer_cent0Words_length hi]; omega)

private theorem o8Outer_centU_injOn
    {i : ℕ} (hi : i = 3 ∨ i = 4) {a b : ℕ} (ha : a < 5) (hb : b < 5)
    (hab : o8OuterCentU i a = o8OuterCentU i b) : a = b := by
  have hi5 : i < 5 := by omega
  have hcheck : ∀ i ∈ [3, 4], ∀ a < 5, ∀ b < a,
      eqA 360 (o8OuterCentArr i a) (o8OuterCentArr i b) = false := by
    have h := o8OuterCent_check
    simpa only [o8OuterCentCheck, List.all_eq_true, List.mem_range, Bool.not_eq_true'] using h
  have hi' : i ∈ [3, 4] := by rcases hi with rfl | rfl <;> simp
  have key : ∀ a b : ℕ, a < 5 → b < a → o8OuterCentU i a ≠ o8OuterCentU i b := by
    intro a b ha hb heq
    have h1 := hcheck i hi' a ha b hb
    have h2 := (eqA_iff (o8Outer_rep_centU hi5 a) (o8Outer_rep_centU hi5 b)).2 heq
    rw [h1] at h2
    exact Bool.noConfusion h2
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab.symm (key b a hb h)
  · exact h
  · exact absurd hab (key a b ha h)

private theorem o8Outer_fixed_large_omegaT :
    ∀ φ : MulAut omegaT, φ * φ = 1 → (∀ w : omegaT, φ ≠ MulAut.conj w) →
      4 < Nat.card (fixedSubgroup φ) := by
  intro φ hφ hout
  set a : autT := autEquiv.symm φ with hadef
  have hφa : autEquiv a = φ := autEquiv.apply_symm_apply φ
  have ha2 : (a : Equiv.Perm (Fin 360)) * a = 1 := by
    have : a * a = 1 := autEquiv.injective (by rw [map_mul, hφa, hφ, map_one])
    exact congrArg Subtype.val this
  have ha1 : (a : Equiv.Perm (Fin 360)) ≠ 1 := by
    intro h
    apply hout 1
    rw [← hφa, show a = 1 from Subtype.ext h, map_one, map_one]
  have hnot : (a : Equiv.Perm (Fin 360)) ∉ omegaT := by
    intro h
    apply hout ⟨a, h⟩
    rw [← hφa, ← autEquiv_omegaT]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hao : orderOf (a : Equiv.Perm (Fin 360)) = 2 := orderOf_eq_prime (by rw [sq, ha2]) ha1
  obtain ⟨i, hi, g, hg, hx, hiff⟩ := exists_conj_main a.2 hao
  have hi3 : 3 ≤ i := by
    by_contra hlt
    exact hnot (hiff.2 (by omega))
  have hi34 : i = 3 ∨ i = 4 := by omega
  have hmem : ∀ j, g * o8OuterCentU i j * g⁻¹ ∈ omegaT := fun j =>
    (conj_mem_omegaT hg).1 (o8Outer_centU_mem hi j)
  have hfix : ∀ j < 5, φ ⟨g * o8OuterCentU i j * g⁻¹, hmem j⟩ =
      ⟨g * o8OuterCentU i j * g⁻¹, hmem j⟩ := by
    intro j hj
    apply Subtype.ext
    rw [← hφa, autEquiv_apply]
    change (a : Equiv.Perm (Fin 360)) * (g * o8OuterCentU i j * g⁻¹) *
      (a : Equiv.Perm (Fin 360))⁻¹ = _
    rw [hx]
    have hc := o8Outer_centU_comm hi hj
    calc g * mainPerm i * g⁻¹ * (g * o8OuterCentU i j * g⁻¹) * (g * mainPerm i * g⁻¹)⁻¹
        = g * (mainPerm i * o8OuterCentU i j * (mainPerm i)⁻¹) * g⁻¹ := by group
      _ = g * o8OuterCentU i j * g⁻¹ := by rw [← hc]; group
  let f : Fin 5 → fixedSubgroup φ := fun j =>
    ⟨⟨g * o8OuterCentU i j * g⁻¹, hmem j⟩, o8Outer_mem_fixedSubgroup.2 (hfix j j.2)⟩
  have hf : Function.Injective f := by
    intro j j' hjj'
    have h1 : g * o8OuterCentU i j * g⁻¹ = g * o8OuterCentU i j' * g⁻¹ :=
      congrArg (fun z : fixedSubgroup φ => ((z : omegaT) : Equiv.Perm (Fin 360))) hjj'
    have h2 : o8OuterCentU i j = o8OuterCentU i j' := by simpa using h1
    exact Fin.ext (o8Outer_centU_injOn hi34 j.2 j'.2 h2)
  have h5 : 5 ≤ Nat.card (fixedSubgroup φ) :=
    calc 5 = Nat.card (Fin 5) := by simp
      _ ≤ Nat.card (fixedSubgroup φ) := Nat.card_le_card_of_injective f hf
  omega

theorem o8Plus2OuterInvolutions_holds :
    O8Plus2OuterInvolutions := by
  intro Q _ _ hQ σ hσ hout
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  exact o8Outer_transport e o8Outer_fixed_large_omegaT σ hσ hout

end CFSG.EvenSporadicStandard.Co3Std.CentT
