module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

theorem card_monoidHom_units_le (G K : Type*) [Group G] [Finite G] [Field K] :
    Nat.card (G →* Kˣ) ≤ Nat.card G := by
  classical
  cases nonempty_fintype G
  have hli := linearIndependent_monoidHom G K
  have hinj : Function.Injective (fun f : G →* Kˣ => (Units.coeHom K).comp f) := by
    intro f g h
    ext x
    exact congrArg (fun φ : G →* K => φ x) h
  have : Finite (G →* K) := hli.finite
  cases nonempty_fintype (G →* K)
  calc Nat.card (G →* Kˣ) ≤ Nat.card (G →* K) := Nat.card_le_card_of_injective _ hinj
    _ ≤ Module.finrank K (G → K) := by
        rw [Nat.card_eq_fintype_card]; exact hli.fintype_card_le_finrank
    _ = Nat.card G := by rw [Module.finrank_pi, Nat.card_eq_fintype_card]

theorem card_mul_le_of_fiberwise_const {ι Q T K : Type*} [Field K] [Finite K] [Finite Q]
    {p : ℕ} (hp : 0 < p) {q : ι → Q} (hq : Function.Surjective q) (i₀ : ι)
    {ev : T → ι → Kˣ} (hev : Function.Injective ev)
    (hcon : ∀ t i j, q i = q j → ev t i = ev t j)
    (hpow : ∀ t, ∃ c : Kˣ, ∀ i, ev t i ^ p = c) :
    Nat.card T * p ≤ Nat.card Kˣ * p ^ Nat.card Q := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  set s : Q → ι := Function.surjInv hq with hs
  have hqs : ∀ O, q (s O) = O := Function.surjInv_eq hq
  let φ : T → Kˣ × ({O : Q // O ≠ q i₀} → rootsOfUnity p K) := fun t =>
    (ev t i₀, fun O => ⟨ev t (s O.1) / ev t i₀, by
      obtain ⟨c, hc⟩ := hpow t
      rw [mem_rootsOfUnity, div_pow, hc, hc, div_self']⟩)
  have hφ : Function.Injective φ := by
    intro t u h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply hev
    funext i
    by_cases hi : q i = q i₀
    · rw [hcon t i i₀ hi, hcon u i i₀ hi, h1]
    · have h3 := congrArg Subtype.val (congrFun h2 ⟨q i, hi⟩)
      simp only at h3
      rw [h1, div_left_inj] at h3
      rw [hcon t i (s (q i)) (hqs _).symm, hcon u i (s (q i)) (hqs _).symm, h3]
  have hcard : Nat.card T ≤ Nat.card Kˣ * p ^ Nat.card {O : Q // O ≠ q i₀} :=
    calc Nat.card T ≤ Nat.card (Kˣ × ({O : Q // O ≠ q i₀} → rootsOfUnity p K)) :=
          Nat.card_le_card_of_injective φ hφ
      _ = Nat.card Kˣ * Nat.card (rootsOfUnity p K) ^ Nat.card {O : Q // O ≠ q i₀} := by
          rw [Nat.card_prod, Nat.card_fun]
      _ ≤ Nat.card Kˣ * p ^ Nat.card {O : Q // O ≠ q i₀} := by
          gcongr; exact card_rootsOfUnity K p
  have hm : Nat.card Q = Nat.card {O : Q // O ≠ q i₀} + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe (q i₀)), Finite.card_option]
  rw [hm, pow_succ, ← mul_assoc]
  exact Nat.mul_le_mul_right p hcard

theorem card_twisted_le {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (F : Subgroup (Equiv.Perm (Fin n)))
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (S : Subgroup (Fin n → Kˣ))
    (hC : ∀ c : Kˣ, (fun _ => c) ∈ S)
    (hpow : ∀ d ∈ S, ∃ c : Kˣ, ∀ i, d i ^ p = c)
    (hF : ∀ σ ∈ F, ∀ d ∈ S, ∃ c : Kˣ, ∀ i, d (σ i) = c * d i) :
    Nat.card S * p ≤
      Nat.card Kˣ * Nat.card F * p ^ Nat.card (MulAction.orbitRel.Quotient F (Fin n)) := by
  set i₀ : Fin n := ⟨0, hn⟩
  have key : ∀ d ∈ S, ∀ σ ∈ F, ∀ i, d (σ i) = d (σ i₀) / d i₀ * d i := by
    intro d hd σ hσ i
    obtain ⟨c, hc⟩ := hF σ hσ d hd
    rw [hc i, hc i₀, mul_div_cancel_right]
  let χ : S → F →* Kˣ := fun d =>
    { toFun := fun σ => d.1 (σ.1 i₀) / d.1 i₀
      map_one' := by simp
      map_mul' := fun σ τ => by
        change d.1 (σ.1 (τ.1 i₀)) / d.1 i₀ = _
        rw [key d.1 d.2 σ.1 σ.2 (τ.1 i₀), mul_div_assoc] }
  let α : S →* (F →* Kˣ) :=
    { toFun := χ
      map_one' := by ext σ; simp [χ]
      map_mul' := fun d e => by ext σ; simp [χ, mul_div_mul_comm] }
  have hker : ∀ x ∈ α.ker, ∀ σ ∈ F, ∀ i, (x : S).1 (σ i) = (x : S).1 i := by
    intro x hx σ hσ i
    have h1 : (x : S).1 (σ i₀) / (x : S).1 i₀ = 1 := DFunLike.congr_fun hx ⟨σ, hσ⟩
    rw [key _ (x : S).2 σ hσ i, h1, one_mul]
  have h1 : Nat.card α.ker * p ≤
      Nat.card Kˣ * p ^ Nat.card (MulAction.orbitRel.Quotient F (Fin n)) := by
    refine card_mul_le_of_fiberwise_const hp.pos
      (q := Quotient.mk (MulAction.orbitRel F (Fin n))) Quotient.mk_surjective i₀
      (ev := fun x : α.ker => ((x : S) : Fin n → Kˣ)) ?_ ?_ ?_
    · intro x y h
      exact Subtype.ext (Subtype.ext h)
    · intro x i j hij
      obtain ⟨σ, rfl⟩ := Quotient.exact hij
      exact hker x x.2 σ.1 σ.2 j
    · intro x
      exact hpow _ (x : S).2
  have h2 : Nat.card α.range ≤ Nat.card F :=
    (Subgroup.card_le_card_group α.range).trans (card_monoidHom_units_le F K)
  calc Nat.card S * p = Nat.card α.ker * p * Nat.card α.range := by
        rw [← Subgroup.card_ker_mul_card_range α]; ring
    _ ≤ Nat.card Kˣ * p ^ Nat.card (MulAction.orbitRel.Quotient F (Fin n)) * Nat.card F :=
        Nat.mul_le_mul h1 h2
    _ = _ := by ring

end CFSG.HardMathSupport.Timmesfeld.LinearRank
