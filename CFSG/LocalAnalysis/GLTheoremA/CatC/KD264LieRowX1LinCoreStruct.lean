module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreCnt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

open CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem card_eq_pow_three {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) :
    ∃ k : ℕ, Nat.card E = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP : IsPGroup 3 E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    exact hE.2 g.1 g.2
  exact hP.exists_card_eq

instance finite_linearEquiv_struct : Finite (V ≃ₗ[ZMod 2] V) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

theorem exists_struct (E : Subgroup (V ≃ₗ[ZMod 2] V)) [Fintype E] (hE : IsElemAbelian 3 E)
    (hge : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E) :
    ∃ (k : ℕ) (X : Fin k → Submodule (ZMod 2) V) (ρf : Fin k → (V ≃ₗ[ZMod 2] V)),
      (∀ i, Inv2 E (X i) ∧ IsIrrE E (X i)) ∧ iSupIndep X ∧ iSup X = ⊤ ∧
      (∀ i, ρf i ∈ E ∧
        ((Module.finrank (ZMod 2) (X i) = 1 ∧ ∀ g ∈ E, ∀ x ∈ X i, g x = x) ∨
          (Module.finrank (ZMod 2) (X i) = 2 ∧ (∀ x ∈ X i, ρf i x = x → x = 0) ∧
            (∀ x ∈ X i, ρf i (ρf i x) + ρf i x + x = 0) ∧
            (∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (k : ℕ)) x)))) ∧
      Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} = Module.finrank (ZMod 2) V / 2 ∧
      ∀ p : {i // Module.finrank (ZMod 2) (X i) = 2}, ∃ e ∈ E, ∀ q : {i // Module.finrank (ZMod 2) (X i) = 2},
        expo ρf X q.1 e = if q = p then 1 else 0 := by
  classical
  obtain ⟨kE, hkE⟩ := card_eq_pow_three hE
  have hodd : Odd (Fintype.card E) := by
    rw [← Nat.card_eq_fintype_card, hkE]
    exact Odd.pow (by decide)
  have hinvtop : Inv2 E (⊤ : Submodule (ZMod 2) V) := fun _ _ _ _ => trivial
  obtain ⟨k, X, hXprop, hXle, hind, hsup, hfr⟩ :=
    exists_decomp E hodd _ ⊤ hinvtop rfl
  have hdim : Module.finrank (ZMod 2) V = ∑ i, Module.finrank (ZMod 2) (X i) := by
    rw [← finrank_top (ZMod 2) V]
    exact hfr
  obtain ⟨ρf, hρf⟩ := exists_gen_data hE (fun i => (hXprop i).1) (fun i => (hXprop i).2)
  obtain ⟨hcardle, hdimle⟩ := card_le_planes hE hρf hsup hdim
  have hm1 : Module.finrank (ZMod 2) V / 2 ≤ Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
    have h3 : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ 3 ^ Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} :=
      le_trans hge hcardle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have hm2 : Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} ≤ Module.finrank (ZMod 2) V / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num)).2
    omega
  have hPcard : Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} = Module.finrank (ZMod 2) V / 2 := le_antisymm hm2 hm1
  let Θ : E → ({i // Module.finrank (ZMod 2) (X i) = 2} → Fin 3) :=
    fun g p => expo ρf X p.1 (g : V ≃ₗ[ZMod 2] V)
  have hΘinj : Function.Injective Θ := by
    intro g h hgh
    apply Subtype.ext
    apply eq_of_expo_eq hE hρf hsup g.2 h.2
    intro i hi
    exact congrFun hgh ⟨i, hi⟩
  have hcard : Fintype.card E = 3 ^ (Module.finrank (ZMod 2) V / 2) := by
    apply le_antisymm
    · rw [← hPcard]
      exact hcardle
    · exact hge
  have hΘbij : Function.Bijective Θ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hΘinj, ?_⟩
    rw [Fintype.card_fun, Fintype.card_fin, hcard, hPcard]
  refine ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, ?_⟩
  intro p
  obtain ⟨g, hg⟩ := hΘbij.2 (fun q => if q = p then 1 else 0)
  refine ⟨g.1, g.2, fun q => ?_⟩
  exact congrFun hg q

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

end
