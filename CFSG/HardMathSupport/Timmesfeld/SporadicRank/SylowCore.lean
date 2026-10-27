module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordSound

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3

section

variable {X : Type} [Group X] {p : ℕ} [Fact p.Prime]

theorem injective_mul_of_actsBy (D : ModuleSpec X p) (P C : Subgroup X) (hCP : C ≤ P)
    (hC : ∀ x ∈ C, ∀ i, x * D.a i = D.a i * x) {k : ℕ} (g : Fin k → X)
    (A : Fin k → Matrix (Fin D.n) (Fin D.n) (ZMod p)) (hg : ∀ a, g a ∈ P)
    (hA : ∀ a, ActsBy D (g a) (A a)) (hd : ∀ a b : Fin k, a ≠ b → A a ≠ A b) :
    Function.Injective
      (fun x : Fin k × C => (⟨g x.1 * (x.2 : X), P.mul_mem (hg x.1) (hCP x.2.2)⟩ : P)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rintro ⟨a, e⟩ ⟨b, e'⟩ h
  have h' : g a * (e : X) = g b * (e' : X) := congrArg Subtype.val h
  have hab : a = b := by
    by_contra hne
    apply hd a b hne
    ext r i
    have hcol : g a * D.a i * (g a)⁻¹ = g b * D.a i * (g b)⁻¹ := by
      have hga : g a = g b * ((e' : X) * (e : X)⁻¹) := by
        rw [← mul_assoc]
        exact eq_mul_inv_of_mul_eq h'
      have hc : ((e' : X) * (e : X)⁻¹) * D.a i = D.a i * ((e' : X) * (e : X)⁻¹) :=
        hC _ (C.mul_mem e'.2 (C.inv_mem e.2)) i
      calc g a * D.a i * (g a)⁻¹
          = g b * (((e' : X) * (e : X)⁻¹) * D.a i * ((e' : X) * (e : X)⁻¹)⁻¹) *
              (g b)⁻¹ := by rw [hga]; group
        _ = g b * D.a i * (g b)⁻¹ := by rw [hc]; group
    have := D.elt_injective (show D.elt (fun r => A a r i) = D.elt (fun r => A b r i) from by
      rw [← hA a i, ← hA b i, hcol])
    exact congrFun this r
  subst hab
  have : (e : X) = e' := mul_left_cancel h'
  exact Prod.ext rfl (Subtype.ext this)

theorem card_mul_le_of_actsBy [Finite X] (D : ModuleSpec X p) (P C : Subgroup X) (hCP : C ≤ P)
    (hC : ∀ x ∈ C, ∀ i, x * D.a i = D.a i * x) {k : ℕ} (g : Fin k → X)
    (A : Fin k → Matrix (Fin D.n) (Fin D.n) (ZMod p)) (hg : ∀ a, g a ∈ P)
    (hA : ∀ a, ActsBy D (g a) (A a)) (hd : ∀ a b : Fin k, a ≠ b → A a ≠ A b) :
    k * Nat.card C ≤ Nat.card P := by
  calc k * Nat.card C = Nat.card (Fin k × C) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    _ ≤ Nat.card P :=
        Nat.card_le_card_of_injective _ (injective_mul_of_actsBy D P C hCP hC g A hg hA hd)

theorem sylow_selfCentralizing [Finite X] (D : ModuleSpec X p) (P : Subgroup X)
    (hspan : D.span ≤ P) (hPgrp : IsPGroup p P) {N s k : ℕ} (hN : Nat.card X = N)
    (hv : p ^ s ∣ N ∧ ¬ p ^ (s + 1) ∣ N) (hs : p ^ s ≤ k * p ^ D.n) (g : Fin k → X)
    (A : Fin k → Matrix (Fin D.n) (Fin D.n) (ZMod p)) (hg : ∀ a, g a ∈ P)
    (hA : ∀ a, ActsBy D (g a) (A a)) (hd : ∀ a b : Fin k, a ≠ b → A a ≠ A b) :
    Nat.card P = p ^ (Nat.card X).factorization p ∧
      (∀ x ∈ P, (∀ a ∈ D.span, x * a = a * x) → x ∈ D.span) ∧
      ∀ x ∈ P, ∃ a : Fin k, ∃ α ∈ D.span, x = g a * α := by
  have hp : p.Prime := Fact.out
  set C : Subgroup X := P ⊓ Subgroup.centralizer (D.span : Set X) with hCdef
  have hCc : ∀ x ∈ C, ∀ i, x * D.a i = D.a i * x := fun x hx i =>
    (Subgroup.mem_centralizer_iff.mp hx.2 (D.a i) (D.a_mem_span i)).symm
  have hspanC : D.span ≤ C := fun x hx =>
    ⟨hspan hx, Subgroup.mem_centralizer_iff.mpr fun h hh => D.mul_comm_of_mem hh hx⟩
  have hlow := card_mul_le_of_actsBy D P C inf_le_left hCc g A hg hA hd
  have hspcard : Nat.card D.span ≤ Nat.card C := Subgroup.card_le_of_le hspanC
  have hN0 : N ≠ 0 := by
    rw [← hN]
    exact Nat.card_pos.ne'
  obtain ⟨kk, hk⟩ := hPgrp.exists_card_eq
  have hdvd : Nat.card P ∣ N := hN ▸ Subgroup.card_subgroup_dvd_card P
  have hspn : Nat.card D.span = p ^ D.n := D.card_span hp
  have hs1 : s ≤ kk := by
    have : p ^ s ≤ p ^ kk := by
      rw [← hk]
      calc p ^ s ≤ k * p ^ D.n := hs
        _ = k * Nat.card D.span := by rw [hspn]
        _ ≤ k * Nat.card C := Nat.mul_le_mul_left k hspcard
        _ ≤ Nat.card P := hlow
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
  have hs2 : kk ≤ s := by
    by_contra hlt
    apply hv.2
    exact (Nat.pow_dvd_pow p (not_le.1 hlt)).trans (hk ▸ hdvd)
  have hkeq : kk = s := le_antisymm hs2 hs1
  have hfact : N.factorization p = s := by
    have h1 := (hp.pow_dvd_iff_le_factorization hN0).1 hv.1
    have h2 : ¬ s + 1 ≤ N.factorization p :=
      fun h => hv.2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
    omega
  have hcard : Nat.card P = p ^ (Nat.card X).factorization p := by
    rw [hN, hfact, hk, hkeq]
  refine ⟨hcard, ?_⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, zero_mul] at hs
      exact absurd hs (not_le.2 (pow_pos hp.pos s))
    · exact h
  have hCs : Nat.card C ≤ Nat.card D.span := by
    have h1 : k * Nat.card C ≤ k * Nat.card D.span := by
      calc k * Nat.card C ≤ Nat.card P := hlow
        _ = p ^ s := by rw [hcard, hN, hfact]
        _ ≤ k * p ^ D.n := hs
        _ = k * Nat.card D.span := by rw [hspn]
    exact Nat.le_of_mul_le_mul_left h1 hk0
  have hCeq : D.span = C := Subgroup.eq_of_le_of_card_ge hspanC hCs
  refine ⟨fun x hx hxc => ?_, fun x hx => ?_⟩
  · rw [hCeq]
    exact ⟨hx, Subgroup.mem_centralizer_iff.mpr fun h hh => (hxc h hh).symm⟩
  ·
    have hinj := injective_mul_of_actsBy D P C inf_le_left hCc g A hg hA hd
    have hcardeq : Nat.card P ≤ Nat.card (Fin k × C) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin, hcard, hN,
        hfact]
      calc p ^ s ≤ k * p ^ D.n := hs
        _ = k * Nat.card D.span := by rw [hspn]
        _ ≤ k * Nat.card C := Nat.mul_le_mul_left k hspcard
    have hbij := hinj.bijective_of_nat_card_le hcardeq
    obtain ⟨⟨a, c⟩, hac⟩ := hbij.2 ⟨x, hx⟩
    have hx' : x = g a * (c : X) := (congrArg Subtype.val hac).symm
    exact ⟨a, c, by rw [hCeq]; exact c.2, hx'⟩

end

end CFSG.HardMathSupport.Timmesfeld.SporadicRank
