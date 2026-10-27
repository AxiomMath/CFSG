module

public import CFSG.HardMathSupport.Foote.FamilyReduction.Transport
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafAltS
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem false_of_index_small {A : Type} [Group A] [Finite A] [IsSimpleGroup A] {H : Subgroup A}
    (hH : H ≠ ⊤) (hidx : H.index.factorial < Nat.card A) : False := by
  classical
  let φ : A →* Perm (A ⧸ H) := MulAction.toPermHom A (A ⧸ H)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
    have : Fintype (A ⧸ H) := Fintype.ofFinite _
    have h1 : Nat.card A ≤ Nat.card (Perm (A ⧸ H)) := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := Perm (A ⧸ H)), Fintype.card_perm,
      ← Nat.card_eq_fintype_card] at h1
    exact absurd h1 (not_le.mpr hidx)
  · apply hH
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ φ.ker := h ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    have h2 : φ g (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by rw [hg]; rfl
    have h3 : (QuotientGroup.mk (g * 1) : A ⧸ H) = QuotientGroup.mk 1 := h2
    rw [mul_one] at h3
    simpa using (QuotientGroup.eq.mp h3.symm)

theorem not_comp5_alternating {Q : Type} [Group Q] {n : ℕ} (hn : 5 ≤ n)
    (e : Q ≃* alternatingGroup (Fin n)) : ¬ Comp5 Q := by
  intro h
  obtain ⟨α, hα, K, hK, ⟨eK⟩⟩ := Comp5.congr e h
  have hK2 : IsPComponent 2 K :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hK
  have hα2 : α * α = 1 := by
    have : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    rwa [sq] at this
  by_cases hn6 : n = 6
  · subst hn6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    set K₀ : Subgroup (alternatingGroup (Fin 6)) := K.map (fixedSubgroup α).subtype with hK₀
    have hcard : Nat.card K₀ = 120 := by
      rw [hK₀, Subgroup.card_map_of_injective (fixedSubgroup α).subtype_injective]
      exact CFSG.GH74.GLS.LU.Local.Five.sl2_five_card eK.symm
    have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hidx : K₀.index = 3 := by
      have := Subgroup.card_mul_index K₀
      rw [hcard, hA] at this
      omega
    have hK₀top : K₀ ≠ ⊤ := by
      intro h1
      rw [h1, Subgroup.card_top, hA] at hcard
      omega
    exact false_of_index_small hK₀top (by rw [hidx, hA]; decide)
  · have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
    obtain ⟨τ, hτ⟩ := hbij.2 α
    have hττ : τ * τ = 1 := by
      apply hbij.1
      rw [map_mul, hτ, hα2, map_one]
    have hτ1 : τ ≠ 1 := by
      rintro rfl
      rw [map_one] at hτ
      rw [← hτ, orderOf_one] at hα
      exact absurd hα (by norm_num)
    subst hτ
    set P : Subgroup (alternatingGroup (Fin n)) :=
      K.map (fixedSubgroup (MulAut.conjNormal τ)).subtype with hPdef
    have hPF : P ≤ fixedSubgroup (MulAut.conjNormal τ) := by
      rintro _ ⟨k, -, rfl⟩
      exact k.2
    have hPK : P.subgroupOf (fixedSubgroup (MulAut.conjNormal τ)) = K :=
      Subgroup.comap_map_eq_self_of_injective (fixedSubgroup _).subtype_injective K
    have hP : IsPComponent 2 (P.subgroupOf (fixedSubgroup (MulAut.conjNormal τ))) := by
      rw [hPK]
      exact hK2
    obtain ⟨hsimple, -, -⟩ :=
      CFSG.ComponentClassification.GSThmB.Pump516.alt_fixed_component_structure hττ hτ1 hPF hP
    let eP : P ≃* K :=
      (K.equivMapOfInjective _ (fixedSubgroup (MulAut.conjNormal τ)).subtype_injective).symm
    exact not_isSimpleGroup_sl2_five (eK.symm.trans eP.symm) hsimple

end CFSG.HardMathSupport.Foote.FamilyReduction
