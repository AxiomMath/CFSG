module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.FixedVector

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.TrivialTwo

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open scoped commutatorElement
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)

variable {r : ℕ} {I : Set ℕ}

@[expose] def actHom (h2 : 2 ∈ I) :
    ↥(SymplecticHigher.flagStabilizer r (ZMod 2) I) →*
      Equiv.Perm ↥(SymplecticFlag.flag r (ZMod 2) 2) :=
  MonoidHom.mk'
    (fun g =>
      { toFun := fun x => ⟨spMat g.1 *ᵥ x.1, spMat_mulVec_mem_of_mem_stabilizer
          (SymplecticHigher.mem_flagStabilizer.mp g.2 2 h2) x.2⟩
        invFun := fun x => ⟨spMat g.1⁻¹ *ᵥ x.1, spMat_mulVec_mem_of_mem_stabilizer
          (SymplecticHigher.mem_flagStabilizer.mp (inv_mem g.2) 2 h2) x.2⟩
        left_inv := fun x => Subtype.ext (by
          simp only [mulVec_mulVec, spMat_inv_mul, one_mulVec])
        right_inv := fun x => Subtype.ext (by
          simp only [mulVec_mulVec, spMat_mul_inv, one_mulVec]) })
    (fun g h => Equiv.ext fun x => Subtype.ext (by
      simp only [Equiv.Perm.mul_apply, Equiv.coe_fn_mk, Subgroup.coe_mul,
        spMat_mul, mulVec_mulVec]))

theorem actHom_apply (h2 : 2 ∈ I) (g : ↥(SymplecticHigher.flagStabilizer r (ZMod 2) I))
    (x : ↥(SymplecticFlag.flag r (ZMod 2) 2)) :
    ((actHom h2 g x : ↥(SymplecticFlag.flag r (ZMod 2) 2)) : Fin r ⊕ Fin r → ZMod 2) =
      spMat g.1 *ᵥ x.1 := rfl

theorem card_flag_two_le (hr : 2 ≤ r) :
    Finite ↥(SymplecticFlag.flag r (ZMod 2) 2) ∧ Nat.card ↥(SymplecticFlag.flag r (ZMod 2) 2) ≤ 4 := by
  let f : ↥(SymplecticFlag.flag r (ZMod 2) 2) → (Fin 2 → ZMod 2) :=
    fun x i => x.1 (Sum.inl ⟨i.1, lt_of_lt_of_le i.2 hr⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx := (SymplecticFlag.mem_isoFlag.mp ((SymplecticFlag.mem_flag_of_le hr).mp x.2))
    have hy := (SymplecticFlag.mem_isoFlag.mp ((SymplecticFlag.mem_flag_of_le hr).mp y.2))
    funext c
    rcases c with j | j
    · by_cases hj : (j : ℕ) < 2
      · exact congrFun hxy ⟨j.1, hj⟩
      · rw [hx.2 j (by omega), hy.2 j (by omega)]
    · rw [hx.1 j, hy.1 j]
  refine ⟨Finite.of_injective f hf, ?_⟩
  calc Nat.card ↥(SymplecticFlag.flag r (ZMod 2) 2) ≤ Nat.card (Fin 2 → ZMod 2) :=
        Nat.card_le_card_of_injective f hf
    _ = 4 := by simp

theorem fixes_flag_two_of_mem_perfectJoin {r : ℕ} {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    (h2 : 2 ∈ I) {v : StatedSp r (ZMod 2)}
    (hv : v ∈ CFSG.AGLEmbedding.ParabPrime.perfectJoin
      (SymplecticHigher.flagStabilizer r (ZMod 2) I)) :
    ∀ x ∈ SymplecticFlag.flag r (ZMod 2) 2, spMat v *ᵥ x = x := by
  have hr : 2 ≤ r := (hI 2 h2).2
  obtain ⟨hfin, hcard⟩ := card_flag_two_le hr
  have hsolv : Group.IsSolvable (Equiv.Perm ↥(SymplecticFlag.flag r (ZMod 2) 2)) :=
    Equiv.Perm.isSolvable hcard
  set J := SymplecticHigher.flagStabilizer r (ZMod 2) I with hJ
  set P : Subgroup ↥J := (perfectJoin J).subgroupOf J with hP
  have hPmap : P.map J.subtype = perfectJoin J :=
    Subgroup.map_subgroupOf_eq_of_le (perfectJoin_le J)
  have hPP : ⁅P, P⁆ = P := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, hPmap, perfectJoin_perfect]
  set H : Subgroup (Equiv.Perm ↥(SymplecticFlag.flag r (ZMod 2) 2)) := P.map (actHom h2) with hH
  have hHH : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, hPP]
  have hbot : H = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hHH
  have hvJ : v ∈ J := perfectJoin_le J hv
  have hvP : (⟨v, hvJ⟩ : ↥J) ∈ P := hv
  have h1 : actHom h2 ⟨v, hvJ⟩ = 1 := by
    have : actHom h2 ⟨v, hvJ⟩ ∈ H := Subgroup.mem_map_of_mem _ hvP
    rwa [hbot, Subgroup.mem_bot] at this
  intro x hx
  have := congrArg (fun p => ((p ⟨x, hx⟩ : ↥(SymplecticFlag.flag r (ZMod 2) 2)) :
    Fin r ⊕ Fin r → ZMod 2)) h1
  rw [actHom_apply] at this
  exact this

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.TrivialTwo
