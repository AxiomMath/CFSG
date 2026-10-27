module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreStruct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open Module CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

section Struct

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem card_eq_three_pow {G : Type*} [Group G] {E : Subgroup G} [Finite E]
    (hE : IsElemAbelian 3 E) : ∃ k : ℕ, Nat.card E = 3 ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [pow_one]
    exact hE.2 g.1 g.2
  exact hP.exists_card_eq

theorem card_le_three_pow_half (E : Subgroup (W ≃ₗ[ZMod 2] W)) [Fintype E]
    (hE : IsElemAbelian 3 E) :
    Fintype.card E ≤ 3 ^ (Module.finrank (ZMod 2) W / 2) := by
  obtain ⟨j, hj⟩ := card_eq_three_pow hE
  have hodd : Odd (Fintype.card E) := by
    rw [← Nat.card_eq_fintype_card, hj]
    exact Odd.pow (by decide)
  have hinvtop : Inv2 E (⊤ : Submodule (ZMod 2) W) := fun _ _ _ _ => trivial
  obtain ⟨k, X, hXprop, -, hind, hsup, hfr⟩ :=
    exists_decomp E hodd _ ⊤ hinvtop rfl
  have hdim : Module.finrank (ZMod 2) W = ∑ i, Module.finrank (ZMod 2) (X i) := by
    rw [← finrank_top (ZMod 2) W]
    exact hfr
  obtain ⟨ρf, hρf⟩ := exists_gen_data hE (fun i => (hXprop i).1) (fun i => (hXprop i).2)
  obtain ⟨hcardle, hdimle⟩ := card_le_planes hE hρf hsup hdim
  calc Fintype.card E
      ≤ 3 ^ Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := hcardle
    _ ≤ 3 ^ (Module.finrank (ZMod 2) W / 2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by linarith [hdimle])

theorem sp_struct (E : Subgroup (W ≃ₗ[ZMod 2] W)) [Fintype E] (hE : IsElemAbelian 3 E) (n : ℕ)
    (hdim : Module.finrank (ZMod 2) W = 2 * n) (hcard : Fintype.card E = 3 ^ n) :
    ∃ (X : Fin n → Submodule (ZMod 2) W) (ρ : Fin n → (W ≃ₗ[ZMod 2] W)),
      (∀ i, Module.finrank (ZMod 2) (X i) = 2) ∧ iSupIndep X ∧ iSup X = ⊤ ∧
      (∀ i, Inv2 E (X i)) ∧ (∀ i, ρ i ∈ E) ∧
      (∀ i, ∀ x ∈ X i, ρ i (ρ i x) + ρ i x + x = 0) ∧
      (∀ i, ∀ x ∈ X i, ρ i x = x → x = 0) ∧
      (∀ i, ∀ g ∈ E, ∃ k : Fin 3, ∀ x ∈ X i, g x = (ρ i ^ (k : ℕ)) x) ∧
      (∀ p : Fin n, ∃ e ∈ E, ∀ q : Fin n, ∀ x ∈ X q, e x = if q = p then ρ q x else x) := by
  classical
  have hodd : Odd (Fintype.card E) := by
    rw [hcard]
    exact Odd.pow (by decide)
  have hinvtop : Inv2 E (⊤ : Submodule (ZMod 2) W) := fun _ _ _ _ => trivial
  obtain ⟨k, X, hXprop, -, hind, hsup, hfr⟩ :=
    exists_decomp E hodd _ ⊤ hinvtop rfl
  have hdimk : Module.finrank (ZMod 2) W = ∑ i, Module.finrank (ZMod 2) (X i) := by
    rw [← finrank_top (ZMod 2) W]
    exact hfr
  obtain ⟨ρf, hρf⟩ := exists_gen_data hE (fun i => (hXprop i).1) (fun i => (hXprop i).2)
  obtain ⟨hcardle, hdimle⟩ := card_le_planes hE hρf hsup hdimk
  have hPcard : Fintype.card {i : Fin k // Module.finrank (ZMod 2) (X i) = 2} = n := by
    have h1 : n ≤ Fintype.card {i : Fin k // Module.finrank (ZMod 2) (X i) = 2} := by
      have h3 : 3 ^ n ≤ 3 ^ Fintype.card {i : Fin k // Module.finrank (ZMod 2) (X i) = 2} := by
        rw [← hcard]
        exact hcardle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
    have h2 : Fintype.card {i : Fin k // Module.finrank (ZMod 2) (X i) = 2} ≤ n := by
      omega
    omega
  have hsum : ∑ i, Module.finrank (ZMod 2) (X i) =
      k + Fintype.card {i : Fin k // Module.finrank (ZMod 2) (X i) = 2} := by
    have hterm : ∀ i : Fin k, Module.finrank (ZMod 2) (X i) =
        1 + (if Module.finrank (ZMod 2) (X i) = 2 then 1 else 0) := by
      intro i
      rcases (hρf i).2 with h | h
      · rw [h.1]
        simp
      · rw [h.1]
        simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
    simp [Finset.sum_boole, Fintype.card_subtype]
  have hk : k = n := by omega
  subst hk
  have hall : ∀ i : Fin k, Module.finrank (ZMod 2) (X i) = 2 := by
    intro i
    have hfull : Finset.univ.filter (fun i : Fin k => Module.finrank (ZMod 2) (X i) = 2) =
        Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← Fintype.card_subtype]
      simpa using hPcard
    have hi : i ∈ Finset.univ.filter (fun i : Fin k => Module.finrank (ZMod 2) (X i) = 2) := by
      rw [hfull]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.1 hi).2
  let Θ : E → ({i : Fin k // Module.finrank (ZMod 2) (X i) = 2} → Fin 3) :=
    fun g p => expo ρf X p.1 (g : W ≃ₗ[ZMod 2] W)
  have hΘinj : Function.Injective Θ := by
    intro g h hgh
    apply Subtype.ext
    apply eq_of_expo_eq hE hρf hsup g.2 h.2
    intro i hi
    exact congrFun hgh ⟨i, hi⟩
  have hΘbij : Function.Bijective Θ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hΘinj, ?_⟩
    rw [Fintype.card_fun, Fintype.card_fin, hcard, hPcard]
  have hgen : ∀ i : Fin k, ∀ g ∈ E, ∃ j : Fin 3, ∀ x ∈ X i, g x = (ρf i ^ (j : ℕ)) x :=
    fun i g hg => ((hρf i).2.resolve_left (fun h => by rw [hall i] at h; exact absurd h.1 (by norm_num))).2.2.2 g hg
  refine ⟨X, ρf, hall, hind, hsup, fun i => (hXprop i).1, fun i => (hρf i).1,
    fun i => ((hρf i).2.resolve_left (fun h => by rw [hall i] at h; exact absurd h.1 (by norm_num))).2.2.1,
    fun i => ((hρf i).2.resolve_left (fun h => by rw [hall i] at h; exact absurd h.1 (by norm_num))).2.1,
    hgen, ?_⟩
  intro p
  obtain ⟨g, hg⟩ := hΘbij.2 (fun q => if q = (⟨p, hall p⟩ : {i : Fin k // Module.finrank (ZMod 2) (X i) = 2}) then 1 else 0)
  refine ⟨g.1, g.2, fun q x hx => ?_⟩
  have hexp : expo ρf X q g.1 =
      (if (⟨q, hall q⟩ : {i : Fin k // Module.finrank (ZMod 2) (X i) = 2}) = ⟨p, hall p⟩ then 1 else 0) :=
    congrFun hg ⟨q, hall q⟩
  simp only [Subtype.mk.injEq] at hexp
  by_cases hqp : q = p
  · subst hqp
    have h1 : expo ρf X q g.1 = 1 := by rw [hexp]; simp
    have he := expo_spec (hgen q g.1 g.2) x hx
    simp [h1] at he
    simpa using he
  · have h0 : expo ρf X q g.1 = 0 := by rw [hexp, if_neg hqp]
    have he := expo_spec (hgen q g.1 g.2) x hx
    simp [h0] at he
    simpa [hqp] using he

end Struct

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end
