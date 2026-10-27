module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import TauCeti.Data.Finset.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem signChange_injective {c : ZMod 3} (fr : NFrame Q (Fin 5) c) :
    Function.Injective (fun J : Finset (Fin 5) => fr.signChange J) := by
  intro J K h
  apply Finset.ext
  intro i
  have hb := congrArg (fun g : OGroup Q => ((g : V ≃ₗ[ZMod 3] V) (fr.b i))) h
  rw [fr.signChange_basis J i, fr.signChange_basis K i] at hb
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K
  · exact iff_of_true hJ hK
  · exfalso
    have hneg : -fr.b i = fr.b i := by simpa [hJ, hK] using hb
    have hx : fr.b i = -fr.b i := hneg.symm
    have hsum : fr.b i + fr.b i = 0 := by
      nth_rewrite 1 [hx]
      exact neg_add_cancel _
    have hsmul : (2 : ZMod 3) • fr.b i = 0 := by rw [two_smul]; exact hsum
    rcases (fr.b.smul_eq_zero (c := (2 : ZMod 3)) (x := fr.b i)).mp hsmul with h2 | hx0
    · exact absurd h2 (by decide)
    · exact fr.b.ne_zero i hx0
  · exfalso
    have hneg : fr.b i = -fr.b i := by simpa [hJ, hK] using hb
    have hsum : fr.b i + fr.b i = 0 := by
      nth_rewrite 1 [hneg]
      exact neg_add_cancel _
    have hsmul : (2 : ZMod 3) • fr.b i = 0 := by rw [two_smul]; exact hsum
    rcases (fr.b.smul_eq_zero (c := (2 : ZMod 3)) (x := fr.b i)).mp hsmul with h2 | hx0
    · exact absurd h2 (by decide)
    · exact fr.b.ne_zero i hx0
  · exact iff_of_false hJ hK

theorem t5_exists_E16 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5) :
    ∃ E : Subgroup (OGroup Q), E ≤ omegaGroup hQ ∧ IsElemAb2 E 4 := by
  obtain ⟨c, _hc, ⟨fr⟩⟩ := exists_nframe_five hQ hdim
  let E : Subgroup (OGroup Q) :=
    { carrier := {g | ∃ J : Finset (Fin 5), Even J.card ∧ g = fr.signChange J}
      mul_mem' := by
        rintro a b ⟨J, hJ, rfl⟩ ⟨K, hK, rfl⟩
        exact ⟨symmDiff J K, (Finset.even_card_symmDiff_iff J K).mpr (iff_of_true hJ hK),
          fr.signChange_mul J K⟩
      one_mem' := ⟨∅, by simp, fr.signChange_empty.symm⟩
      inv_mem' := by
        rintro a ⟨J, hJ, rfl⟩
        exact ⟨J, hJ, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)⟩ }
  have hmem : ∀ g : OGroup Q, g ∈ E ↔
      ∃ J : Finset (Fin 5), Even J.card ∧ g = fr.signChange J := fun _ => Iff.rfl
  refine ⟨E, ?_⟩
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨J, hJ, rfl⟩ := (hmem g).mp hg
    exact fr.signChange_mem_omegaGroup hQ J hJ
  · have hElem : CFSG.Open.IsElemAbelian 2 E := by
      refine ⟨?_, ?_⟩
      · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
        obtain ⟨J, hJ, ha⟩ := (hmem a.1).mp a.2
        obtain ⟨K, hK, hb⟩ := (hmem b.1).mp b.2
        change a.1 * b.1 = b.1 * a.1
        rw [ha, hb, fr.signChange_comm]
      · intro x hx
        obtain ⟨J, hJ, rfl⟩ := (hmem x).mp hx
        rw [pow_two]
        exact fr.signChange_mul_self J
    have hcard : Nat.card E = 2 ^ 4 := by
      have hbij : Nat.card E = Nat.card {J : Finset (Fin 5) // Even J.card} := by
        refine (Nat.card_congr ?_).symm
        refine Equiv.ofBijective
          (fun J : {J : Finset (Fin 5) // Even J.card} =>
            (⟨fr.signChange J.1, (hmem _).mpr ⟨J.1, J.2, rfl⟩⟩ : E)) ?_
        refine ⟨?_, ?_⟩
        · intro J K h
          apply Subtype.ext
          exact signChange_injective fr (Subtype.ext_iff.mp h)
        · intro g
          obtain ⟨J, hJ, hg⟩ := (hmem g.1).mp g.2
          exact ⟨⟨J, hJ⟩, Subtype.ext hg.symm⟩
      rw [hbij, Nat.card_eq_fintype_card]
      decide
    exact ⟨hElem, hcard⟩

end CFSG.OddStandard.SmallF3.Omega
