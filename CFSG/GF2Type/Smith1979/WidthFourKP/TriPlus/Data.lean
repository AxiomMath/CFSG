module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Fpf
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Monomial

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.TriPlus

open Subgroup Module CFSG.Open CFSG.GroupTheory CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type} [Group G] [Finite G]

structure TriData (S : Setting G) (g : G) : Type where
  σ : Multiplicative (Fin 3 → ZMod 3) →* S.O
  l : Fin 3 → S.O
  perm : S.Mbar →* Equiv.Perm (Fin 3)
  basis : EigenBasis (S7.Obar S) (S.Lbar g) σ l
  cent : ∀ x ∈ S.Mbar, (∀ y ∈ S7.Obar S, x * y = y * x) → x ∈ S7.Obar S
  fpf_iff : ∀ c : Fin 3 → ZMod 3,
    (∀ v : S.Qt, ((σ (Multiplicative.ofAdd c) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) ↔
      ∃ i, c i ≠ 0 ∧ ∀ j, j ≠ i → c j = 0
  fix_cl : ∀ c : Fin 3 → ZMod 3,
    ((σ (Multiplicative.ofAdd c) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) → c = 0
  conj_e : ∀ (x : S.Mbar) (i : Fin 3), ∃ s : ZMod 3, s ≠ 0 ∧
    (x : S.O) * eb σ i * (x : S.O)⁻¹ = σ (Multiplicative.ofAdd (Pi.single (perm x i) s))
  ker_iff : ∀ x : S.Mbar, perm x = 1 ↔ (x : S.O) ∈ S7.Obar S ⊔ S.Lbar g
  conj_l : ∀ x : S.Mbar, ∃ c : Fin 3 → ZMod 3, ∀ i, (x : S.O) * l i * (x : S.O)⁻¹ =
    σ (Multiplicative.ofAdd c) * l (perm x i) * (σ (Multiplicative.ofAdd c))⁻¹
  card_Mbar : Nat.card S.Mbar = 216 * Nat.card perm.range

theorem nonempty_triData {S : Setting G} (hw : S.width = 4) (hirr : ¬ S.IsReducible) {g : G}
    (H : Hyp4 S g) (C : Cons311 S g) (hE : timmesfeldLayer S.Mbar = ⊥)
    (h27 : Nat.card (timmesfeldOddCore S.Mbar) = 3 ^ 3) : Nonempty (TriData S g) := by
  obtain ⟨σ, l, E⟩ := (eigenHyp_Obar hw H C hE h27).exists_eigenBasis
  have hL : Nat.card (S.Lbar g) = 8 := by
    rw [C.card_Lbar, hw]
    norm_num
  have hL2 : ∀ s ∈ S.Lbar g, s * s = 1 := fun s hs =>
    S4.mul_self_of_mem_Lbar S H.conj_mem hs
  have hYM : S7.Obar S ≤ S.Mbar := S7.Obar_le_Mbar
  have hLM : S.Lbar g ≤ S.Mbar := S.Lbar_le_Mbar g
  have hnorm : ∀ x ∈ S.Mbar, ∀ y ∈ S7.Obar S, x * y * x⁻¹ ∈ S7.Obar S := fun x hx y hy =>
    S7.conj_mem_Obar hx hy
  have hcent : ∀ x ∈ S.Mbar, (∀ y ∈ S7.Obar S, x * y = y * x) → x ∈ S7.Obar S :=
    fun x hx hc => mem_Obar_of_commute hE h27 hx hc
  let F : S.O → Prop := fun y =>
    ∀ v : S.Qt, ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0)
  have hF : ∀ c : Fin 3 → ZMod 3, F (σ (Multiplicative.ofAdd c)) ↔
      ∃ i, c i ≠ 0 ∧ ∀ j, j ≠ i → c j = 0 :=
    fun c => fpf_iff_of_eigenBasis hirr H E c
  have hFconj : ∀ x ∈ S.Mbar, ∀ y : S.O, F y → F (x * y * x⁻¹) := by
    intro x hx y hy v hv
    let A : S.Qt ≃ₗ[ZMod 2] S.Qt := (x : S.O)
    let B : S.Qt ≃ₗ[ZMod 2] S.Qt := (y : S.O)
    have hC : ((x * y * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = A * B * A⁻¹ := rfl
    rw [hC, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv
    have hv' : B (A⁻¹ v) = A⁻¹ v := by
      simpa using congrArg A.symm hv
    exact A⁻¹.injective (by simpa using hy _ hv')
  obtain ⟨perm, hconj_e, hker, hconj_l, hcard⟩ :=
    exists_monomial E hL hL2 hYM hLM hnorm hcent hFconj hF
  let T : TriData S g :=
    { σ := σ, l := l, perm := perm, basis := E,
      cent := hcent,
      fpf_iff := hF,
      fix_cl := fun c hc => fix_cl_of_eigenBasis hirr H E c hc,
      conj_e := hconj_e, ker_iff := hker, conj_l := hconj_l, card_Mbar := hcard }
  exact ⟨T⟩

end CFSG.GF2Type.Smith1979.TriPlus

end
