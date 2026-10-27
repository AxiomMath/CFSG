module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std.CResH2

open Matrix CFSG.Assembly.LowTwoRank

theorem exists_injective_proj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) {A : Type*} [Group A] (φ : A →* GL ι K) (hφ : ∀ a, φ a ∈ H)
    (hs : ∀ (a : A) (c : Kˣ), Matrix.GeneralLinearGroup.scalar ι c = φ a → a = 1) :
    ∃ ψ : A →* StatedProj H, Function.Injective ψ := by
  refine ⟨(QuotientGroup.mk' _).comp (φ.codRestrict H hφ),
    (injective_iff_map_eq_one _).2 fun a ha => ?_⟩
  have h1 : (⟨φ a, hφ a⟩ : H) ∈ (StatedScalars ι K).subgroupOf H :=
    (QuotientGroup.eq_one_iff _).1 ha
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h1
  exact hs a c hc

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {K : Type} [Field K]

@[expose] def blockMatHom : Multiplicative (Matrix m n K) →* Matrix (m ⊕ n) (m ⊕ n) K where
  toFun X := Matrix.fromBlocks 1 (Multiplicative.toAdd X) 0 1
  map_one' := by simp
  map_mul' X Y := by
    simp [Matrix.fromBlocks_multiply, add_comm]

@[expose] def blockHom : Multiplicative (Matrix m n K) →* GL (m ⊕ n) K :=
  MonoidHom.toHomUnits blockMatHom

theorem blockHom_coe (X : Multiplicative (Matrix m n K)) :
    ((blockHom X : GL (m ⊕ n) K) : Matrix (m ⊕ n) (m ⊕ n) K) =
      Matrix.fromBlocks 1 (Multiplicative.toAdd X) 0 1 := rfl

theorem eq_one_of_scalar_blockHom {c : Kˣ} {X : Multiplicative (Matrix m n K)}
    (h : Matrix.GeneralLinearGroup.scalar (m ⊕ n) c = blockHom X) : X = 1 := by
  apply Multiplicative.toAdd.injective
  ext i j
  have h' := congrArg (fun g : GL (m ⊕ n) K => (g : Matrix (m ⊕ n) (m ⊕ n) K) (Sum.inl i)
    (Sum.inr j)) h
  simpa [blockHom_coe, Matrix.GeneralLinearGroup.scalar] using h'.symm

end CFSG.EvenSporadicStandard.M24Std.CResH2
