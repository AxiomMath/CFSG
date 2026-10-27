module

public import CFSG.GH74.Uniqueness.SU.KI7Ext
public import CFSG.GH74.Uniqueness.SU.KI7Perm
public import CFSG.GH74.Uniqueness.SU.KInputsR3

public section

namespace CFSG.GH74.Uniqueness.SU.KI7

open Subgroup Equiv Equiv.Perm

theorem exists_elemAb16 {X : Type*} [Group X] [Finite X] (ρ : X →* alternatingGroup (Fin 9))
    (hρ : Function.Surjective ρ) (hc : ρ.ker ≤ center X) (h2 : Nat.card ρ.ker = 2) :
    ∃ E : Subgroup X, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  let π : X →* Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype.comp ρ
  have hπker : π.ker = ρ.ker :=
    MonoidHom.ker_comp_of_injective ρ _ (alternatingGroup (Fin 9)).subtype_injective
  obtain ⟨z, hK⟩ := exists_centralKernel π (hπker.le.trans hc) (by rw [hπker]; exact h2)
  have hlift : ∀ s ∈ alternatingGroup (Fin 9), ∃ y : X, π y = s := by
    intro s hs
    obtain ⟨y, hy⟩ := hρ ⟨s, hs⟩
    refine ⟨y, ?_⟩
    show ((ρ y : alternatingGroup (Fin 9)) : Perm (Fin 9)) = s
    rw [hy]
  obtain ⟨y₁, hy₁⟩ := hlift pa (E_le_alternatingGroup pa_mem_E)
  obtain ⟨y₂, hy₂⟩ := hlift pb (E_le_alternatingGroup pb_mem_E)
  obtain ⟨y₃, hy₃⟩ := hlift pc (E_le_alternatingGroup pc_mem_E)
  obtain ⟨ĉ, hĉ⟩ := hlift pt pt_mem_alternatingGroup
  have g0 : π 1 * pa * (π 1)⁻¹ = pa := by simp
  have g1 := conj_step hĉ g0 pt_pa
  have g2 := conj_step hĉ g1 pt_pb
  have g3 := conj_step hĉ g2 pt_pc
  have g4 := conj_step hĉ g3 pt_pab
  have g5 := conj_step hĉ g4 pt_pbc
  have g6 := conj_step hĉ g5 pt_pabc
  have htrans : ∀ s ∈ E, s ≠ 1 → ∃ g : X, π g * pa * (π g)⁻¹ = s := by
    intro s hs hne
    rcases mem_E_iff.mp hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ⟨_, g0⟩
    · exact ⟨_, g1⟩
    · exact ⟨_, g2⟩
    · exact ⟨_, g3⟩
    · exact ⟨_, g6⟩
    · exact ⟨_, g4⟩
    · exact ⟨_, g5⟩
  have hsq := sq_eq_one_of_transitive hK E (fun s hs => E_sq hs) pa htrans
    (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) (by rw [hy₁]; exact pa_mem_E)
    (by rw [hy₂]; exact pb_mem_E) (by rw [hy₃]; exact pc_mem_E)
    (by rw [hy₁]; exact pa_ne_one) (by rw [hy₂]; exact pb_ne_one)
    (by rw [hy₃]; exact pc_ne_one)
    (by rw [map_mul, hy₁, hy₂]; exact pa_mul_pb_ne_one)
    (by rw [map_mul, hy₁, hy₃]; exact pa_mul_pc_ne_one)
    (by rw [map_mul, hy₂, hy₃]; exact pb_mul_pc_ne_one)
    (by rw [map_mul, map_mul, hy₁, hy₂, hy₃]; exact pa_mul_pb_mul_pc_ne_one)
  have hmem : ∀ y : X, y ∈ (E.subgroupOf (alternatingGroup (Fin 9))).comap ρ ↔ π y ∈ E :=
    fun y => Iff.rfl
  refine ⟨(E.subgroupOf (alternatingGroup (Fin 9))).comap ρ,
    SU1.isElemAbelian_iff.mpr ⟨fun a ha b hb => comm_of_sq_eq_one E hsq ((hmem a).mp ha)
      ((hmem b).mp hb), fun a ha => ?_⟩, ?_⟩
  · rw [pow_two]
    exact hsq a ((hmem a).mp ha)
  · have h8 : Nat.card (E.subgroupOf (alternatingGroup (Fin 9))) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe E_le_alternatingGroup).toEquiv, card_E]
    rw [card_comap_of_surjective ρ hρ, h2, h8]

theorem exists_elemAb16_of_twoAlt9 {X : Type} [Group X] [Finite X] (hX : K.IsTwoAlt X 9) :
    ∃ E : Subgroup X, Open.IsElemAbelian 2 E ∧ Nat.card E = 16 := by
  obtain ⟨-, -, hZcard, ⟨e⟩⟩ := hX
  let ρ : X →* alternatingGroup (Fin 9) :=
    (e : X ⧸ center X →* alternatingGroup (Fin 9)).comp (QuotientGroup.mk' (center X))
  have hρsurj : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = center X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact exists_elemAb16 ρ hρsurj hker.le (by rw [hker]; exact hZcard)

end CFSG.GH74.Uniqueness.SU.KI7

namespace CFSG.GH74.Uniqueness.SU.K

theorem ki7b9 : KI7b9 := by
  intro X _ _ hX
  obtain ⟨E, hE, hcard⟩ := KI7.exists_elemAb16_of_twoAlt9 hX
  exact SU1.le_pRank (p := 2) (by norm_num) (le_top : E ≤ ⊤) hE (k := 4) (by rw [hcard]; norm_num)

end CFSG.GH74.Uniqueness.SU.K
