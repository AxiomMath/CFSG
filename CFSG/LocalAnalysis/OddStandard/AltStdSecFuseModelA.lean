module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGam
import all CFSG.LocalAnalysis.OddStandard.AltStdSecSylowModel
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowModel
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def ptsG (l : List ℕ) : ℕ := (l.map (fun a => 2 ^ a)).sum

theorem ptsG_cons (a : ℕ) (l : List ℕ) : ptsG (a :: l) = 2 ^ a + ptsG l := by
  simp [ptsG]

theorem card_fixedPoints_sumCongr {α β : Type*} [Finite α] [Finite β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Nat.card (Function.fixedPoints (Equiv.Perm.sumCongr σ τ)) =
      Nat.card (Function.fixedPoints σ) + Nat.card (Function.fixedPoints τ) := by
  have e : Function.fixedPoints (Equiv.Perm.sumCongr σ τ) ≃
      Function.fixedPoints σ ⊕ Function.fixedPoints τ :=
    (Equiv.subtypeSum (p := fun x => x ∈ Function.fixedPoints (Equiv.Perm.sumCongr σ τ))).trans
      (Equiv.sumCongr
        (Equiv.subtypeEquivRight (fun a => by simp [Function.IsFixedPt]))
        (Equiv.subtypeEquivRight (fun b => by simp [Function.IsFixedPt])))
  rw [Nat.card_congr e, Nat.card_sum]

theorem fixG_eq_card (l : List ℕ) (γ : Gam l) :
    fixG l γ = Nat.card (Function.fixedPoints (embG l γ)) := by
  induction l with
  | nil =>
    have : IsEmpty (BlockType []) := inferInstanceAs (IsEmpty Empty)
    rw [Nat.card_of_isEmpty]
    rfl
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    show fixW a x + fixG l γ = Nat.card (Function.fixedPoints
      (Equiv.Perm.sumCongr (repW a x) (embG l γ)))
    rw [card_fixedPoints_sumCongr, ih γ]
    rfl

theorem fixG_even (l : List ℕ) (hl : ∀ a ∈ l, 1 ≤ a) (γ : Gam l) : Even (fixG l γ) := by
  induction l with
  | nil => exact Even.zero
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    exact (fixW_even a (hl a List.mem_cons_self) x).add
      (ih (fun b hb => hl b (List.mem_cons_of_mem a hb)) γ)

theorem fixG_le (l : List ℕ) (γ : Gam l) : fixG l γ ≤ ptsG l := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    rw [ptsG_cons]
    exact Nat.add_le_add (fixW_le a x) (ih γ)

theorem even_ptsG_sub_fixG (l : List ℕ) (γ : Gam l) : (ptsG l - fixG l γ) % 2 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    have h1 := even_sub_fixW a x
    have h2 := ih γ
    have h3 := fixW_le a x
    have h4 := fixG_le l γ
    have h5 : fixG (a :: l) (Gam.cons x γ) = fixW a x + fixG l γ := rfl
    rw [ptsG_cons, h5]
    omega

theorem sgG_invol (l : List ℕ) (γ : Gam l) (hγ : γ * γ = 1) :
    sgG l γ = (-1) ^ ((ptsG l - fixG l γ) / 2) := by
  induction l with
  | nil => simp [sgG_nil, ptsG, fixG]
  | cons a l ih =>
    obtain ⟨x, γ⟩ := γ
    obtain ⟨hx, hγ'⟩ := sq_cons (y₁ := x) (y₂ := γ) hγ
    rw [sgG_cons, sgW_invol a x hx, ih γ hγ', ← pow_add]
    congr 1
    have h1 := even_sub_fixW a x
    have h2 := even_ptsG_sub_fixG l γ
    have h3 := fixW_le a x
    have h4 := fixG_le l γ
    have h5 : fixG (a :: l) (Gam.cons x γ) = fixW a x + fixG l γ := rfl
    rw [ptsG_cons, h5]
    omega

theorem exists_model (n : ℕ) (P : Subgroup (Equiv.Perm (Fin n)))
    (hP : P ≤ alternatingGroup (Fin n)) (hp : IsPGroup 2 P)
    (hmax : ∀ P' : Subgroup (Equiv.Perm (Fin n)), P' ≤ alternatingGroup (Fin n) →
      IsPGroup 2 P' → P ≤ P' → P' = P) :
    ∃ ι : Gam n.bitIndices →* Equiv.Perm (Fin n), Function.Injective ι ∧
      (∀ γ, Equiv.Perm.sign (ι γ) = sgG _ γ) ∧
      (∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG _ γ) ∧
      (∀ x, x ∈ P ↔ ∃ γ, sgG _ γ = 1 ∧ ι γ = x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set l := n.bitIndices with hl
  have hcardB : Fintype.card (BlockType l) = n := by
    rw [card_BlockType, hl, Nat.sum_map_two_pow_bitIndices]
  let e : BlockType l ≃ Fin n := Fintype.equivFinOfCardEq hcardB
  let f : Gam l →* Equiv.Perm (Fin n) := (Equiv.permCongrHom e).toMonoidHom.comp (embG l)
  have hf : Function.Injective f := by
    intro a b hab
    exact embG_injective l ((Equiv.permCongrHom e).injective hab)
  have hfsign : ∀ γ, Equiv.Perm.sign (f γ) = sgG l γ := by
    intro γ
    show Equiv.Perm.sign (e.permCongr (embG l γ)) = _
    rw [Equiv.Perm.sign_permCongr, sign_embG]
  have hcard : Nat.card f.range = 2 ^ (Nat.card (Equiv.Perm (Fin n))).factorization 2 := by
    rw [Nat.card_perm, Nat.card_fin, ← card_Gam_bitIndices n,
      ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  let M : Sylow 2 (Equiv.Perm (Fin n)) := Sylow.ofCard f.range hcard
  obtain ⟨S, hSP⟩ := hp.exists_le_sylow
  have hSA : (S : Subgroup (Equiv.Perm (Fin n))) ⊓ alternatingGroup (Fin n) = P :=
    hmax _ inf_le_right S.isPGroup'.to_inf_left (le_inf hSP hP)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin n)) M S
  let ι : Gam l →* Equiv.Perm (Fin n) := (MulAut.conj g).toMonoidHom.comp f
  have hSmem : ∀ x, x ∈ (S : Subgroup (Equiv.Perm (Fin n))) ↔ ∃ γ, ι γ = x := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : s ∈ f.range := by simpa [M] using hs
      obtain ⟨γ, rfl⟩ := hs'
      exact ⟨γ, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨f γ, by simp [M], rfl⟩
  have hιinj : Function.Injective ι := (MulAut.conj g).injective.comp hf
  have hιsign : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ := by
    intro γ
    show Equiv.Perm.sign (g * f γ * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign g) (Equiv.Perm.sign (f γ)),
      mul_assoc, mul_inv_cancel, mul_one, hfsign]
  have hιfix : ∀ γ, Nat.card (Function.fixedPoints (ι γ)) = fixG l γ := by
    intro γ
    show Nat.card (Function.fixedPoints (g * f γ * g⁻¹)) = _
    rw [card_fixedPoints_conj]
    show Nat.card (Function.fixedPoints (e.permCongr (embG l γ))) = _
    rw [card_fixedPoints_permCongr, ← fixG_eq_card]
  refine ⟨ι, hιinj, hιsign, hιfix, fun x => ?_⟩
  rw [← hSA, Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, hSmem]
  constructor
  · rintro ⟨⟨γ, rfl⟩, h⟩
    exact ⟨γ, by rw [← hιsign]; exact h, rfl⟩
  · rintro ⟨γ, h1, rfl⟩
    exact ⟨⟨γ, rfl⟩, by rw [hιsign]; exact h1⟩

end CFSG.OddStandard.AltStdSec.SylowSn
