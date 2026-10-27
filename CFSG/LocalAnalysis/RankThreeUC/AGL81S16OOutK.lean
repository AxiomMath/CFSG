module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16ONormA
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix

namespace OutLin

variable {F : Type} [Field F] [Finite F]

theorem card_ker_le (ν : Matrix (Fin 2) (Fin 2) F) (hν : ν ≠ 0) :
    Nat.card {m : Fin 2 → F // ν *ᵥ m = 0} ≤ Nat.card F := by
  classical
  set K : Submodule F (Fin 2 → F) := LinearMap.ker (Matrix.mulVecLin ν) with hKdef
  have hmem : ∀ m : Fin 2 → F, m ∈ K ↔ ν *ᵥ m = 0 := fun m => by
    rw [hKdef, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hK : K ≠ ⊤ := by
    intro htop
    apply hν
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.zero_mulVec]
    have hall : (Pi.single j (1 : F) : Fin 2 → F) ∈ K := by
      rw [htop]
      exact Submodule.mem_top
    exact (hmem _).1 hall
  have hlt : Module.finrank F K < Module.finrank F (Fin 2 → F) := Submodule.finrank_lt hK
  have hfin : Module.finrank F (Fin 2 → F) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hle : Module.finrank F K ≤ 1 := by omega
  have hcard : Nat.card K = Nat.card F ^ Module.finrank F K := Module.natCard_eq_pow_finrank
  have hequiv : Nat.card {m : Fin 2 → F // ν *ᵥ m = 0} = Nat.card K :=
    Nat.card_congr (Equiv.subtypeEquivRight fun m => (hmem m).symm)
  have hpos : 0 < Nat.card F := Nat.card_pos
  rw [hequiv, hcard]
  calc Nat.card F ^ Module.finrank F K ≤ Nat.card F ^ 1 := Nat.pow_le_pow_right hpos hle
    _ = Nat.card F := pow_one _

theorem card_pair_le (ν : Matrix (Fin 2) (Fin 2) F) (hν : ν ≠ 0) (t : F) :
    Nat.card {mm : (Fin 2 → F) × (Fin 2 → F) // ν *ᵥ mm.2 = 0 ∧ ν *ᵥ mm.1 = t • mm.2} ≤
      Nat.card F ^ 2 := by
  classical
  by_cases ht : t = 0
  ·
    subst ht
    have hk := card_ker_le ν hν
    let f : {mm : (Fin 2 → F) × (Fin 2 → F) // ν *ᵥ mm.2 = 0 ∧ ν *ᵥ mm.1 = (0 : F) • mm.2} →
        {m : Fin 2 → F // ν *ᵥ m = 0} × {m : Fin 2 → F // ν *ᵥ m = 0} :=
      fun mm => (⟨mm.1.1, by simpa using mm.2.2⟩, ⟨mm.1.2, mm.2.1⟩)
    have hf : Function.Injective f := by
      intro mm mm' h
      have h1 : mm.1.1 = mm'.1.1 := congrArg (fun p : _ × _ => p.1.val) h
      have h2 : mm.1.2 = mm'.1.2 := congrArg (fun p : _ × _ => p.2.val) h
      exact Subtype.ext (Prod.ext h1 h2)
    calc Nat.card {mm : (Fin 2 → F) × (Fin 2 → F) //
          ν *ᵥ mm.2 = 0 ∧ ν *ᵥ mm.1 = (0 : F) • mm.2}
        ≤ Nat.card ({m : Fin 2 → F // ν *ᵥ m = 0} × {m : Fin 2 → F // ν *ᵥ m = 0}) :=
          Nat.card_le_card_of_injective f hf
      _ = Nat.card {m : Fin 2 → F // ν *ᵥ m = 0} * Nat.card {m : Fin 2 → F // ν *ᵥ m = 0} :=
          Nat.card_prod _ _
      _ ≤ Nat.card F * Nat.card F := Nat.mul_le_mul hk hk
      _ = Nat.card F ^ 2 := (sq _).symm
  ·
    let f : {mm : (Fin 2 → F) × (Fin 2 → F) // ν *ᵥ mm.2 = 0 ∧ ν *ᵥ mm.1 = t • mm.2} →
        (Fin 2 → F) := fun mm => mm.1.1
    have hf : Function.Injective f := by
      intro mm mm' h
      have h1 : mm.1.1 = mm'.1.1 := h
      have h2 : ν *ᵥ mm.1.1 = t • mm.1.2 := mm.2.2
      have h2' : ν *ᵥ mm'.1.1 = t • mm'.1.2 := mm'.2.2
      have h3 : t • mm.1.2 = t • mm'.1.2 := by rw [← h2, ← h2', h1]
      have h4 : mm.1.2 = mm'.1.2 := smul_right_injective _ ht h3
      exact Subtype.ext (Prod.ext h1 h4)
    calc Nat.card {mm : (Fin 2 → F) × (Fin 2 → F) // ν *ᵥ mm.2 = 0 ∧ ν *ᵥ mm.1 = t • mm.2}
        ≤ Nat.card (Fin 2 → F) := Nat.card_le_card_of_injective f hf
      _ = Nat.card F ^ 2 := by simp [Nat.card_fun]

theorem card_pair_le' (ν : Matrix (Fin 2) (Fin 2) F) (hν : ν ≠ 0) :
    Nat.card {mm : (Fin 2 → F) × (Fin 2 → F) // mm.2 = 0 ∧ ν *ᵥ mm.1 = 0} ≤ Nat.card F := by
  classical
  have hk := card_ker_le ν hν
  let f : {mm : (Fin 2 → F) × (Fin 2 → F) // mm.2 = 0 ∧ ν *ᵥ mm.1 = 0} →
      {m : Fin 2 → F // ν *ᵥ m = 0} := fun mm => ⟨mm.1.1, mm.2.2⟩
  have hf : Function.Injective f := by
    intro mm mm' h
    have h1 : mm.1.1 = mm'.1.1 := congrArg Subtype.val h
    have h2 : mm.1.2 = mm'.1.2 := mm.2.1.trans mm'.2.1.symm
    exact Subtype.ext (Prod.ext h1 h2)
  exact (Nat.card_le_card_of_injective f hf).trans hk

end OutLin

end CFSG.LocalAnalysis.RankThreeUC
