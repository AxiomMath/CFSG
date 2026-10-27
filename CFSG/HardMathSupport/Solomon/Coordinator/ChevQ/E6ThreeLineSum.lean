module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open Module LinearMap

section LineSum

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem lineFix_iff {g : Module.End K V} {x : V} : x ∈ ker (g - 1) ↔ g x = x := by
  rw [mem_ker, sub_apply, Module.End.one_apply, sub_eq_zero]

private def lineNorm (g : Module.End K V) : Module.End K V := 1 + g + g ^ 2

private theorem mul_lineNorm {g : Module.End K V} (hg : g ^ 3 = 1) :
    g * lineNorm g = lineNorm g := by
  have h : g * lineNorm g = g + g ^ 2 + g ^ 3 := by
    unfold lineNorm
    noncomm_ring
  rw [h, hg, lineNorm]
  abel

private theorem lineNorm_mem {g : Module.End K V} (hg : g ^ 3 = 1) (x : V) :
    lineNorm g x ∈ ker (g - 1) := by
  rw [lineFix_iff, ← Module.End.mul_apply, mul_lineNorm hg]

private theorem lineNorm_fixed {g h : Module.End K V} (hgh : Commute g h) {x : V}
    (hx : h x = x) : h (lineNorm g x) = lineNorm g x := by
  have hc : Commute h (lineNorm g) :=
    ((Commute.one_right h).add_right hgh.symm).add_right (hgh.symm.pow_right 2)
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hx]

private theorem lineNorm_apply_of_fixed {g : Module.End K V} {x : V} (hx : g x = x) :
    lineNorm g x = (3 : K) • x := by
  rw [lineNorm, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
    Module.End.mul_apply, hx, hx, show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul,
    one_smul]

private theorem three_eq_lineNorm {a b : Module.End K V} (ha : a ^ 3 = 1) (hab : Commute a b) :
    (1 + 1 + 1 : Module.End K V) = lineNorm a * (1 - lineNorm b) + lineNorm b +
      lineNorm (a * b) + lineNorm (a ^ 2 * b) := by
  have h1 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := hab.mul_pow 2
  have h2 : (a ^ 2 * b) ^ 2 = a * b ^ 2 := by
    rw [(hab.pow_left 2).mul_pow 2, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ha,
      one_mul]
  unfold lineNorm
  rw [h1, h2]
  noncomm_ring

theorem finrank_lineSum [FiniteDimensional K V] (h3 : (3 : K) ≠ 0) {a b : Module.End K V}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : Commute a b) :
    finrank K (ker (a - 1)) + finrank K (ker (b - 1)) + finrank K (ker (a * b - 1)) +
        finrank K (ker (a ^ 2 * b - 1)) =
      finrank K V + 3 * finrank K ↥(ker (a - 1) ⊓ ker (b - 1)) := by
  have hab3 : (a * b) ^ 3 = 1 := by rw [hab.mul_pow, ha, hb, one_mul]
  have ha2b3 : (a ^ 2 * b) ^ 3 = 1 := by
    rw [(hab.pow_left 2).mul_pow, ← pow_mul, pow_mul', ha, one_pow, hb, one_mul]
  have hc1 : Commute (a * b) a := (Commute.refl a).mul_left hab.symm
  have hc2 : Commute (a * b) b := hab.mul_left (Commute.refl b)
  have hc3 : Commute (a ^ 2 * b) a := ((Commute.refl a).pow_left 2).mul_left hab.symm
  have hc4 : Commute (a ^ 2 * b) b := (hab.pow_left 2).mul_left (Commute.refl b)
  have hc5 : Commute (a ^ 2 * b) (a * b) := hc3.mul_right hc4
  set A := ker (a - 1) with hA
  set B := ker (b - 1) with hB
  set C := ker (a * b - 1) with hC
  set D := ker (a ^ 2 * b - 1) with hD
  have hW : ∀ x, x ∈ A ⊓ B ↔ a x = x ∧ b x = x := fun x => by
    rw [Submodule.mem_inf, lineFix_iff, lineFix_iff]
  have p1 : ∀ x : V, (a * b) x = x → a x = x → x ∈ A ⊓ B := fun x h1 h2 => by
    refine (hW x).2 ⟨h2, ?_⟩
    calc b x = b (a x) := by rw [h2]
      _ = (a * b) x := by rw [hab.eq]; rfl
      _ = x := h1
  have p2 : ∀ x : V, (a * b) x = x → b x = x → x ∈ A ⊓ B := fun x h1 h2 => by
    refine (hW x).2 ⟨?_, h2⟩
    calc a x = a (b x) := by rw [h2]
      _ = x := h1
  have ha2 : ∀ x : V, a x = x → (a ^ 2) x = x := fun x h => by
    rw [pow_two, Module.End.mul_apply, h, h]
  have p3 : ∀ x : V, (a ^ 2 * b) x = x → a x = x → x ∈ A ⊓ B := fun x h1 h2 => by
    refine (hW x).2 ⟨h2, ?_⟩
    calc b x = b ((a ^ 2) x) := by rw [ha2 x h2]
      _ = (a ^ 2 * b) x := by rw [(hab.pow_left 2).eq]; rfl
      _ = x := h1
  have p4 : ∀ x : V, (a ^ 2 * b) x = x → b x = x → x ∈ A ⊓ B := fun x h1 h2 => by
    have h' : (a ^ 2) x = x := by
      calc (a ^ 2) x = (a ^ 2) (b x) := by rw [h2]
        _ = x := h1
    refine (hW x).2 ⟨?_, h2⟩
    calc a x = a ((a ^ 2) x) := by rw [h']
      _ = (a ^ 3) x := by rw [pow_succ' a 2]; rfl
      _ = x := by rw [ha, Module.End.one_apply]
  have p5 : ∀ x : V, (a ^ 2 * b) x = x → (a * b) x = x → x ∈ A ⊓ B := fun x h1 h2 => by
    have h' : a x = x := by
      calc a x = a ((a * b) x) := by rw [h2]
        _ = (a ^ 2 * b) x := by rw [pow_two, mul_assoc]; rfl
        _ = x := h1
    exact p1 x h2 h'
  have htop : A ⊔ B ⊔ C ⊔ D = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have h : (1 + 1 + 1 : Module.End K V) u ∈ A ⊔ B ⊔ C ⊔ D := by
      rw [three_eq_lineNorm ha hab, LinearMap.add_apply, LinearMap.add_apply,
        LinearMap.add_apply, Module.End.mul_apply]
      exact add_mem (add_mem (add_mem
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
          (lineNorm_mem ha _))))
        (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
          (lineNorm_mem hb _)))))
        (Submodule.mem_sup_left (Submodule.mem_sup_right (lineNorm_mem hab3 _))))
        (Submodule.mem_sup_right (lineNorm_mem ha2b3 _))
    have h' : (1 + 1 + 1 : Module.End K V) u = (3 : K) • u := by
      rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
        show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    rw [h'] at h
    exact (Submodule.smul_mem_iff _ h3).1 h
  have hABC : (A ⊔ B) ⊓ C = A ⊓ B := by
    refine le_antisymm (fun x hx => ?_) (le_inf (inf_le_left.trans le_sup_left) fun x hx => ?_)
    · obtain ⟨hxAB, hxC⟩ := Submodule.mem_inf.1 hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hxAB
      rw [← Submodule.smul_mem_iff _ h3, ← lineNorm_apply_of_fixed (lineFix_iff.1 hxC),
        map_add]
      exact add_mem
        (p1 _ (lineFix_iff.1 (lineNorm_mem hab3 y)) (lineNorm_fixed hc1 (lineFix_iff.1 hy)))
        (p2 _ (lineFix_iff.1 (lineNorm_mem hab3 z)) (lineNorm_fixed hc2 (lineFix_iff.1 hz)))
    · obtain ⟨h1, h2⟩ := (hW x).1 hx
      rw [hC, lineFix_iff, Module.End.mul_apply, h2, h1]
  have hABCD : (A ⊔ B ⊔ C) ⊓ D = A ⊓ B := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf ((inf_le_left.trans le_sup_left).trans le_sup_left) fun x hx => ?_)
    · obtain ⟨hxABC, hxD⟩ := Submodule.mem_inf.1 hx
      obtain ⟨yz, hyz, w, hw, rfl⟩ := Submodule.mem_sup.1 hxABC
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hyz
      rw [← Submodule.smul_mem_iff _ h3, ← lineNorm_apply_of_fixed (lineFix_iff.1 hxD),
        map_add, map_add]
      exact add_mem (add_mem
        (p3 _ (lineFix_iff.1 (lineNorm_mem ha2b3 y)) (lineNorm_fixed hc3 (lineFix_iff.1 hy)))
        (p4 _ (lineFix_iff.1 (lineNorm_mem ha2b3 z)) (lineNorm_fixed hc4 (lineFix_iff.1 hz))))
        (p5 _ (lineFix_iff.1 (lineNorm_mem ha2b3 w)) (lineNorm_fixed hc5 (lineFix_iff.1 hw)))
    · obtain ⟨h1, h2⟩ := (hW x).1 hx
      rw [hD, lineFix_iff, Module.End.mul_apply, h2, ha2 x h1]
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) C
  have e3 := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B ⊔ C) D
  rw [hABC] at e2
  rw [hABCD, htop, finrank_top] at e3
  omega

end LineSum

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
