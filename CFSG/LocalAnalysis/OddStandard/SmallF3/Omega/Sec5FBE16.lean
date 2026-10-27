module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import TauCeti.Data.Finset.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5fb_signChange_injective {c : ZMod 3} (fr : NFrame Q (Fin 5) c) :
    Function.Injective (fun J : Finset (Fin 5) => fr.signChange J) := by
  intro J K h
  apply Finset.ext
  intro i
  have hb := congrArg (fun g : OGroup Q => ((g : V ≃ₗ[ZMod 3] V) (fr.b i))) h
  rw [fr.signChange_basis J i, fr.signChange_basis K i] at hb
  have hne : ∀ {x : V}, x ≠ 0 → x = -x → False := by
    intro x hx0 hx
    have hsum : x + x = 0 := by
      nth_rewrite 1 [hx]
      exact neg_add_cancel _
    have hsmul : (2 : ZMod 3) • x = 0 := by rw [two_smul]; exact hsum
    rcases smul_eq_zero.mp hsmul with h2 | hx0'
    · exact absurd h2 (by decide)
    · exact hx0 hx0'
  by_cases hJ : i ∈ J <;> by_cases hK : i ∈ K
  · exact iff_of_true hJ hK
  · exfalso
    have hneg : -fr.b i = fr.b i := by simpa [hJ, hK] using hb
    exact hne (fr.b.ne_zero i) hneg.symm
  · exfalso
    have hneg : fr.b i = -fr.b i := by simpa [hJ, hK] using hb
    exact hne (fr.b.ne_zero i) hneg
  · exact iff_of_false hJ hK

theorem sec5fb_exists_E16_mem (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) {u : OGroup Q} (hu : u * u = 1)
    (htype : invType u = (4, 1) ∨ invType u = (2, -1)) :
    ∃ E : Subgroup (OGroup Q), E ≤ omegaGroup hQ ∧ IsElemAb2 E 4 ∧ u ∈ E := by
  obtain ⟨c, _hc, ⟨fr⟩⟩ := exists_nframe_five hQ hdim
  let E₀ : Subgroup (OGroup Q) :=
    { carrier := {g | ∃ J : Finset (Fin 5), Even J.card ∧ g = fr.signChange J}
      mul_mem' := by
        rintro a b ⟨J, hJ, rfl⟩ ⟨K, hK, rfl⟩
        exact ⟨symmDiff J K, (Finset.even_card_symmDiff_iff J K).mpr (iff_of_true hJ hK),
          fr.signChange_mul J K⟩
      one_mem' := ⟨∅, by simp, fr.signChange_empty.symm⟩
      inv_mem' := by
        rintro a ⟨J, hJ, rfl⟩
        exact ⟨J, hJ, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)⟩ }
  have hmem : ∀ g : OGroup Q, g ∈ E₀ ↔
      ∃ J : Finset (Fin 5), Even J.card ∧ g = fr.signChange J := fun _ => Iff.rfl
  have hE₀Ω : E₀ ≤ omegaGroup hQ := by
    intro g hg
    obtain ⟨J, hJ, rfl⟩ := (hmem g).mp hg
    exact fr.signChange_mem_omegaGroup hQ J hJ
  have hE₀el : CFSG.Open.IsElemAbelian 2 E₀ := by
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
  have hE₀card : Nat.card E₀ = 2 ^ 4 := by
    have hbij : Nat.card E₀ = Nat.card {J : Finset (Fin 5) // Even J.card} := by
      refine (Nat.card_congr ?_).symm
      refine Equiv.ofBijective
        (fun J : {J : Finset (Fin 5) // Even J.card} =>
          (⟨fr.signChange J.1, (hmem _).mpr ⟨J.1, J.2, rfl⟩⟩ : E₀)) ?_
      refine ⟨?_, ?_⟩
      · intro J K h
        apply Subtype.ext
        exact sec5fb_signChange_injective fr (Subtype.ext_iff.mp h)
      · intro g
        obtain ⟨J, hJ, hg⟩ := (hmem g.1).mp g.2
        exact ⟨⟨J, hJ⟩, Subtype.ext hg.symm⟩
    rw [hbij, Nat.card_eq_fintype_card]
    decide
  obtain ⟨J₀, hJ₀, hJ₀type⟩ : ∃ J₀ : Finset (Fin 5), Even J₀.card ∧
      invType (fr.signChange J₀) = invType u := by
    rcases htype with h | h
    · refine ⟨{0, 1, 2, 3}, by decide, ?_⟩
      rw [fr.invType_signChange hQ _ (by decide), h]
      decide
    · refine ⟨{0, 1}, by decide, ?_⟩
      rw [fr.invType_signChange hQ _ (by decide), h]
      decide
  obtain ⟨g, hgΩ, hg⟩ := exists_mem_omegaGroup_conj hQ (by rw [hdim]; norm_num)
    (fr.signChange_mul_self J₀) hu hJ₀type
  let E : Subgroup (OGroup Q) := E₀.map (MulAut.conj g).toMonoidHom
  have hEmem : ∀ x : OGroup Q, x ∈ E ↔ ∃ e ∈ E₀, g * e * g⁻¹ = x := by
    intro x
    simp only [E, Subgroup.mem_map]
    rfl
  refine ⟨E, ?_, ⟨hE₀el.map _, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := (hEmem x).mp hx
    exact (omegaGroup hQ).mul_mem ((omegaGroup hQ).mul_mem hgΩ (hE₀Ω he))
      ((omegaGroup hQ).inv_mem hgΩ)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀card]
  · exact (hEmem u).mpr ⟨fr.signChange J₀, (hmem _).mpr ⟨J₀, hJ₀, rfl⟩, hg⟩

end CFSG.OddStandard.SmallF3.Omega
