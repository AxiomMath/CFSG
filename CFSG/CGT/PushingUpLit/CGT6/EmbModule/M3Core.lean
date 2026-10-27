module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Orbit
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Numerics
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Trace
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Natural
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Herm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest CFSG.CGT.PushingUpLit.CGT6.TwoEight
open scoped TensorProduct MonoidAlgebra

section Core

variable {n : ℕ} {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
  (σ : Representation (ZMod 2) (SLm F) W)

theorem m3_shape_data (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) (SLm F)) σ.asModule) (hnt : ∃ g, σ g ≠ 1)
    (hfin : Module.finrank (ZMod 2) W ≤ 2 * n) :
    Module.finrank (ZMod 2) W = 2 * n ∧
      ((∃ N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule,
          Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F 1).asModule)) ∨
        (∃ k : ℕ, n = 2 * k ∧ 0 < k ∧
          ∃ N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule,
            Nonempty (↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F (1 + 2 ^ k)).asModule))) := by
  obtain ⟨N, A, hA, hA0, ⟨ι⟩, hsimple, hlow⟩ := m3_descent_data σ hn hF hW hnt
  obtain ⟨hge, hshape⟩ := m3_numerics hn hA hA0 (hlow.trans hfin)
  refine ⟨le_antisymm hfin (hge.trans hlow), ?_⟩
  rcases hshape with ⟨s, hs⟩ | ⟨k, hk, hk0, s, hs⟩
  · left
    obtain ⟨-, ⟨e⟩⟩ := m3_orbSub_label σ hn hF N hA ι s
    rw [hs] at e
    exact ⟨orbSub σ N s, ⟨e⟩⟩
  · right
    obtain ⟨-, ⟨e⟩⟩ := m3_orbSub_label σ hn hF N hA ι s
    rw [hs] at e
    exact ⟨k, hk, hk0, orbSub σ N s, ⟨e⟩⟩

theorem m3_two_mul_le_finrank (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hW : IsSimpleModule (MonoidAlgebra (ZMod 2) (SLm F)) σ.asModule) (hnt : ∃ g, σ g ≠ 1) :
    2 * n ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨N, A, hA, hA0, -, -, hlow⟩ := m3_descent_data σ hn hF hW hnt
  exact (m3_two_mul_le hn hA hA0).trans hlow

omit [CharP F 2] [Module.Finite (ZMod 2) W] in
theorem m3_natural_hom (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule}
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F 1).asModule) :
    ∃ T : (Fin 2 → F) →+ W,
      (∀ (s : SLm F) (u : Fin 2 → F),
        T ((s : Matrix (Fin 2) (Fin 2) F).mulVec u) = σ s (T u)) ∧ T ≠ 0 := by
  have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow hn.ne'
  obtain ⟨ψ, hψ⟩ := m3_exists_intertwining σ hF h1 ι
  have hirr : (steinbergRep F F 1).IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
      (m3_simple Nat.prime_two hF h1)
  exact m3_exists_equivariant_hom σ (steinbergRep F F 1) ψ hψ
    (fun s u => (s : Matrix (Fin 2) (Fin 2) F).mulVec u) natHom
    (fun g u => natHom_equivariant g u) natHom_ne_zero

omit [Finite F] [Algebra (ZMod 2) F] [CharP F 2] [Module.Finite (ZMod 2) W] in
theorem m3_bijective_of_hom [Finite W] {M : Type} [AddCommGroup M] [Finite M]
    (τ : SLm F → M → M) (T : M →+ W) (hT : ∀ s m, T (τ s m) = σ s (T m)) (hT0 : T ≠ 0)
    (hsimple : ∀ U : AddSubgroup W, (∀ s, ∀ w ∈ U, σ s w ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcard : Nat.card M ≤ Nat.card W) : Function.Bijective T := by
  have hU : ∀ s, ∀ w ∈ T.range, σ s w ∈ T.range := by
    rintro s _ ⟨m, rfl⟩
    exact ⟨τ s m, hT s m⟩
  rcases hsimple T.range hU with h | h
  · exfalso
    apply hT0
    ext m
    have : T m ∈ T.range := ⟨m, rfl⟩
    rw [h] at this
    exact (AddSubgroup.mem_bot.mp this)
  · have hsurj : Function.Surjective T := fun w => by
      have : w ∈ T.range := by rw [h]; trivial
      exact this
    exact hsurj.bijective_of_nat_card_le hcard

end Core

section Herm

variable {k : ℕ} [NeZero k] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Module.Finite (ZMod 2) W]
  (σ : Representation (ZMod 2) (SLm (Fq (2 * k))) W)

omit [Module.Finite (ZMod 2) W] in
theorem m3_herm_hom (hF : Nat.card (Fq (2 * k)) = 2 ^ (2 * k))
    {N : Submodule (MonoidAlgebra (Fq (2 * k)) (SLm (Fq (2 * k)))) (repXT σ).asModule}
    (ι : ↥N ≃ₗ[MonoidAlgebra (Fq (2 * k)) (SLm (Fq (2 * k)))]
      (stRep (Fq (2 * k)) (1 + 2 ^ k)).asModule) :
    ∃ T : ↥(hermSub k) →+ W,
      (∀ (s : SLm (Fq (2 * k))) (M : ↥(hermSub k)),
        T ⟨(s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * M.1 *
          cstar k (s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))), herm_act_mem k s M⟩ =
          σ s (T M)) ∧ T ≠ 0 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hA : 1 + 2 ^ k < 2 ^ (2 * k) := by
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h3 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
    nlinarith
  obtain ⟨ψ, hψ⟩ := m3_exists_intertwining σ hF hA ι
  have hirr : (steinbergRep (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k)).IsIrreducible :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
      (m3_simple Nat.prime_two hF hA)
  have := Fintype.ofFinite (Fq (2 * k))
  have hFc : Fintype.card (Fq (2 * k)) = 2 ^ (2 * k) := by
    rw [← Nat.card_eq_fintype_card]; exact hF
  let τ : SLm (Fq (2 * k)) → ↥(hermSub k) → ↥(hermSub k) := fun s M =>
    ⟨(s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))) * M.1 *
      cstar k (s : Matrix (Fin 2) (Fin 2) (Fq (2 * k))), herm_act_mem k s M⟩
  have hΦ : ∀ g M, hermHom k hFc (τ g M) =
      steinbergRep (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k) g (hermHom k hFc M) :=
    fun g M => hermHom_equivariant k hFc g M
  exact m3_exists_equivariant_hom (M := ↥(hermSub k)) σ
    (steinbergRep (Fq (2 * k)) (Fq (2 * k)) (1 + 2 ^ k)) ψ hψ τ (hermHom k hFc) hΦ
    (hermHom_ne_zero k hFc)

end Herm

end CFSG.CGT.PushingUpLit.CGT6
