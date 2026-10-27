module

public import CFSG.Certificates.Kernel.E6TT.RowSound

public section

namespace CFSG.KC.E6TT

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus (componentOrbitLength)
open CFSG.StandardType.TablePThreeKG (E6Admissible)

local notation "V6" => Fin Tag.E6.rank → ℤ

@[expose] def negRho (ρ : Equiv.Perm V6) : Equiv.Perm V6 := ρ.trans (Equiv.neg _)

theorem negRho_apply (ρ : Equiv.Perm V6) (x : V6) : negRho ρ x = -ρ x := rfl

theorem rho_neg (ρ : Equiv.Perm V6) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (x : V6) :
    ρ (-x) = -ρ x :=
  map_neg (AddMonoidHom.mk' ρ hadd) x

theorem negRho_add (ρ : Equiv.Perm V6) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (x y : V6) :
    negRho ρ (x + y) = negRho ρ x + negRho ρ y := by
  rw [negRho_apply, negRho_apply, negRho_apply, hadd, neg_add]

theorem negRho_root (ρ : Equiv.Perm V6) (hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ))
    (γ : V6) (hγ : IsRoot Tag.E6 γ) : IsRoot Tag.E6 (negRho ρ γ) :=
  isRoot_neg_iff.2 (hroot γ hγ)

theorem negRho_adm (ρ : Equiv.Perm V6)
    (v : Fin Tag.E6.rank → ZMod 3)
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) v 1) :
    E6Admissible (fun i => negRho ρ (Pi.single i 1)) v 2 := by
  obtain ⟨h1, h2, h3⟩ := hadm
  refine ⟨fun i => isRoot_neg_iff.2 (h1 i), fun i j => ?_, fun i => ?_⟩
  · have e := h2 i j
    simp only at e ⊢
    rw [negRho_apply, negRho_apply, ← neg_one_zsmul (ρ (Pi.single i 1)),
      ← neg_one_zsmul (ρ (Pi.single j 1)), CFSG.LieType.Steinberg.Adjoint.iform_smul_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_right, e]
    ring
  · have e : ∑ k, ((ρ (Pi.single i 1) k : ℤ) : ZMod 3) * v k = 1 * v i := h3 i
    have e4 : ∀ k, ((negRho ρ (Pi.single i 1) k : ℤ) : ZMod 3) * v k =
        2 * (((ρ (Pi.single i 1) k : ℤ) : ZMod 3) * v k) := fun k => by
      rw [negRho_apply, Pi.neg_apply, ← mul_assoc]
      congr 1
      have e5 : ((-(ρ (Pi.single i 1) k) : ℤ) : ZMod 3) = ((2 * ρ (Pi.single i 1) k : ℤ) : ZMod 3) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 3).2 (Dvd.intro (ρ (Pi.single i 1) k) (by ring))
      simp only [e5, Int.cast_mul, Int.cast_ofNat]
    change ∑ k, ((negRho ρ (Pi.single i 1) k : ℤ) : ZMod 3) * v k = 2 * v i
    rw [Finset.sum_congr rfl fun k _ => e4 k, ← Finset.mul_sum, e, one_mul]

theorem negRho_iterate (ρ : Equiv.Perm V6) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) :
    ∀ k : ℕ, ((negRho ρ : V6 → V6)^[k] = (ρ : V6 → V6)^[k]) ∨
      ((negRho ρ : V6 → V6)^[k] = fun x => -(ρ : V6 → V6)^[k] x)
  | 0 => Or.inl rfl
  | k + 1 => by
    rcases negRho_iterate ρ hadd k with h | h
    · right
      funext x
      rw [Function.iterate_succ_apply', h, Function.iterate_succ_apply', negRho_apply]
    · left
      funext x
      rw [Function.iterate_succ_apply', h, Function.iterate_succ_apply', negRho_apply,
        rho_neg ρ hadd, neg_neg]

theorem negRho_iterate_three (ρ : Equiv.Perm V6) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (x : V6) :
    (negRho ρ : V6 → V6)^[3] x = -(ρ : V6 → V6)^[3] x := by
  change negRho ρ (negRho ρ (negRho ρ x)) = -ρ (ρ (ρ x))
  simp only [negRho_apply, rho_neg ρ hadd, neg_neg]

theorem image_neg_of_closed {S : Set V6} (h : ∀ x ∈ S, -x ∈ S) : (fun x => -x) '' S = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h y hy
  · intro hx
    exact ⟨-x, h x hx, neg_neg x⟩

theorem neg_image_eq_iff {S T : Set V6} (h : ∀ x ∈ S, -x ∈ S) :
    (fun x => -x) '' T = S ↔ T = S := by
  constructor
  · intro e
    have hT : (fun x => -x) '' ((fun x => -x) '' T) = T := by
      rw [Set.image_image]
      simp only [neg_neg, Set.image_id']
    rw [← hT, e, image_neg_of_closed h]
  · intro e
    rw [e, image_neg_of_closed h]

theorem negRho_image (ρ : Equiv.Perm V6) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (k : ℕ)
    {S : Set V6} (hS : ∀ x ∈ (ρ : V6 → V6)^[k] '' S, -x ∈ (ρ : V6 → V6)^[k] '' S) :
    (negRho ρ : V6 → V6)^[k] '' S = (ρ : V6 → V6)^[k] '' S := by
  rcases negRho_iterate ρ hadd k with h | h
  · rw [h]
  · rw [h, ← image_neg_of_closed hS, Set.image_image]

theorem negRho_orbitLength (ρ : Equiv.Perm V6) (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    {Ψ : Set V6} (hneg : ∀ x ∈ Ψ, -x ∈ Ψ) :
    componentOrbitLength (negRho ρ) Ψ = componentOrbitLength ρ Ψ := by
  unfold componentOrbitLength
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ?_
  rcases negRho_iterate ρ hadd s with h | h
  · rw [h]
  · rw [h, ← Set.image_image (fun x => -x) ((ρ : V6 → V6)^[s]), neg_image_eq_iff hneg]

theorem iterate_image_of_orbitLength {ρ : Equiv.Perm V6} {Ψ : Set V6} {L : ℕ}
    (hL : componentOrbitLength ρ Ψ = L) (hpos : 0 < L) : (ρ : V6 → V6)^[L] '' Ψ = Ψ := by
  unfold componentOrbitLength at hL
  have hne : {s : ℕ | 0 < s ∧ (ρ : V6 → V6)^[s] '' Ψ = Ψ}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, Nat.sInf_empty] at hL
    omega
  have hm := Nat.sInf_mem hne
  rw [hL] at hm
  exact hm.2

theorem iterate_image_mod {f : V6 → V6} {S : Set V6} {L : ℕ} (h : f^[L] '' S = S) (k : ℕ) :
    f^[k] '' S = f^[k % L] '' S := by
  have hm : ∀ m, f^[L * m] '' S = S := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, Function.iterate_add, Set.image_comp, h, ih]
  conv_lhs => rw [← Nat.mod_add_div k L, Function.iterate_add, Set.image_comp, hm]

theorem orbitLength_ne {ρ : Equiv.Perm V6} {Ψ A B C : Set V6}
    (hA : ∃ k, (ρ : V6 → V6)^[k] '' Ψ = A) (hB : ∃ k, (ρ : V6 → V6)^[k] '' Ψ = B)
    (hC : ∃ k, (ρ : V6 → V6)^[k] '' Ψ = C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    componentOrbitLength ρ Ψ ≠ 1 ∧ componentOrbitLength ρ Ψ ≠ 2 := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨c, rfl⟩ := hC
  constructor
  · intro h1
    have h := iterate_image_of_orbitLength h1 one_pos
    have e : ∀ k, (ρ : V6 → V6)^[k] '' Ψ = Ψ := fun k => by
      rw [iterate_image_mod h k, Nat.mod_one]
      simp
    exact hAB (by rw [e a, e b])
  · intro h2
    have h := iterate_image_of_orbitLength h2 two_pos
    have e : ∀ k, (ρ : V6 → V6)^[k] '' Ψ = Ψ ∨ (ρ : V6 → V6)^[k] '' Ψ = (ρ : V6 → V6) '' Ψ :=
      fun k => by
        rw [iterate_image_mod h k]
        rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
        · left
          rw [h0]
          simp
        · right
          rw [h0]
          simp
    rcases e a with ha | ha <;> rcases e b with hb | hb <;> rcases e c with hc | hc <;>
      first
        | exact absurd (ha.trans hb.symm) hAB
        | exact absurd (ha.trans hc.symm) hAC
        | exact absurd (hb.trans hc.symm) hBC

end CFSG.KC.E6TT

end
