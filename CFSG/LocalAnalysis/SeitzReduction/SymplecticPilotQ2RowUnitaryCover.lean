module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldCT

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Cover

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {N : ℕ}

@[expose] def NsUnitaryCover (e : L ≃* StatedSp N K) (r : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ ψ : StatedSU r 2 F →* G, ψ.range = nsGlobal e ∧ ψ.ker ≤ center (StatedSU r 2 F)

open CFSG.LieType.BorelTits (unitaryInvolution) in
theorem nsUnitaryCover_of_SU {e : L ≃* StatedSp N K} {r : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = (2 ^ 1) ^ 2)
    (ψ : CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 1) r →* G)
    (hψ : ψ.range = nsGlobal e)
    (hker : ψ.ker ≤ center (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 1) r)) :
    NsUnitaryCover e r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := CFSG.LieType.Universal.Unitary.equivStatedSU (p := 2) (f := 1) hF r with hφ
  refine ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num, ψ.comp φ.symm.toMonoidHom, ?_,
    ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 φ.symm.surjective,
      ← MonoidHom.range_eq_map, hψ]
  · intro x hx
    have h1 : φ.symm x ∈ center (CFSG.LieType.Universal.Unitary.SU (unitaryInvolution F 2 1) r) :=
      hker hx
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro y
    have h2 := congrArg φ (h1 (φ.symm y))
    simpa using h2

theorem exists_surjective_of_nsUnitaryCover {e : L ≃* StatedSp N K} {r : ℕ}
    (hcov : NsUnitaryCover e r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ 1) ^ 2 ∧
      ∃ ψ : StatedSU r (2 ^ 1) F →* nsGlobal e, Function.Surjective ψ ∧
        ψ.ker ≤ center (StatedSU r (2 ^ 1) F) := by
  obtain ⟨F, _, _, hF, ψ, hψ, hker⟩ := hcov
  have hmem : ∀ x : StatedSU r 2 F, ψ x ∈ nsGlobal e := fun x => hψ ▸ ⟨x, rfl⟩
  refine ⟨F, inferInstance, inferInstance, by rw [hF]; norm_num, ψ.codRestrict _ hmem, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← hψ] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  · intro x hx
    refine hker ?_
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx

end Cover

@[expose] def SpTwoUnitaryCoverInput (κ : Sp2mKind) (ε : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsUnitaryCover e (2 * (n + 1) + ε)

end CFSG.SeitzReduction.SymplecticPilot
