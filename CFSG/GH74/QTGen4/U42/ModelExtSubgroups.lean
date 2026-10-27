module

public import CFSG.GH74.QTGen4.U42.ModelExtAligned
public import CFSG.GH74.QTGen4.U42.ModelCoordsB

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431
open CFSG.Quasithin.H13.F431.U42Aut

theorem extAlignedPerm_mul (g h : ↥P2h) :
    extAlignedPerm (g * h) = extAlignedPerm g * extAlignedPerm h := by
  simp only [extAlignedPerm, permHat4, permHat_mul]
  group

theorem extAlignedPerm_inclP2 (g : ↥P2) :
    extAlignedPerm (inclP2 g) = extAlignTau * permOf4 g * extAlignTau⁻¹ := by
  rw [extAlignedPerm, permHat4_inclP2]

theorem extAligned_K4_InD (σ : Equiv.Perm (Fin 5)) (hσ : InK4 σ) :
    InD (extAlignTau * σ * extAlignTau⁻¹) := by
  have h := (extAlign_K4 σ).mpr hσ
  rcases h with h | h | h | h <;> rw [h] <;> decide +kernel

theorem mem_That_two_cosets (g : Ah) (hg : g ∈ That) :
    (∃ t : Y, t ∈ T ∧ incl t = g) ∨
    ∃ t : Y, t ∈ T ∧ incl t * fhatA = g := by
  obtain ⟨l, hl, hrep⟩ := (mem_That_iff g).mp hg
  rcases List.mem_append.mp hl with h | h
  · obtain ⟨t, ht, hr⟩ := exists_T_of_mem_Tl h
    exact Or.inl ⟨t, ht, Subtype.ext (eq_of_repL hr hrep)⟩
  · obtain ⟨tL, htL, rfl⟩ := List.mem_map.mp h
    obtain ⟨t, ht, hr⟩ := exists_T_of_mem_Tl htL
    exact Or.inr ⟨t, ht, Subtype.ext (eq_of_repL (repL_mul hr repL_fhat) hrep)⟩


theorem model_Bh_aligned_iff (g : ↥P2h) :
    (g : Ah) ∈ Bh ↔ extAlignedPerm g 4 = 4 := by
  rw [extAlignedPerm, extAlign_fix_four]
  have h4 : ∀ q : Equiv.Perm (Fin 5),
      (sigma0 * q * sigma0⁻¹) 4 = Equiv.swap 0 4 (q 0) := by
    intro q
    have hi : sigma0⁻¹ 4 = 0 := by decide
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hi]
  rw [permHat4, h4, Equiv.swap_apply_eq_iff]
  have h40 : Equiv.swap (0 : Fin 5) 4 4 = 0 := by decide
  rw [h40]
  change (g : Ah) ∈ P1h ∧ (g : Ah) ∈ P2h ↔ permHat g 0 = 0
  constructor
  · intro h
    apply ptL_inj
    rw [ptL_permHat, ptL_zero]
    exact (mem_P1h_iff _).mp h.1
  · intro h
    refine ⟨(mem_P1h_iff _).mpr ?_, g.2⟩
    have hp := ptL_permHat g 0
    rw [h, ptL_zero] at hp
    exact hp.symm

theorem map_That_aligned
    (e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (he : ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = extAlignedPerm g) :
    (That.subgroupOf P2h).map ((Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp
      e.toMonoidHom) = Thc := by
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hle : (That.subgroupOf P2h).map φ ≤ Thc := by
    rintro _ ⟨g, hg, rfl⟩
    change InD ((e g : Mof _) : Mc).right
    rw [he]
    rcases mem_That_two_cosets (g : Ah) (Subgroup.mem_subgroupOf.mp hg) with
      ⟨t, ht, htg⟩ | ⟨t, ht, htg⟩
    · have hsub : g = inclP2 ⟨t, T_le_P2' ht⟩ := Subtype.ext htg.symm
      rw [hsub, extAlignedPerm_inclP2]
      exact extAligned_K4_InD _ ((model_T_iff ⟨t, T_le_P2' ht⟩).mp ht)
    · have hsub : g = inclP2 ⟨t, T_le_P2' ht⟩ * ⟨fhatA, fhatA_mem_P2h⟩ :=
        Subtype.ext htg.symm
      rw [hsub, extAlignedPerm_mul, extAlignedPerm_inclP2, extAlignedPerm_fhat]
      exact InD_mul _ _ (extAligned_K4_InD _ ((model_T_iff ⟨t, T_le_P2' ht⟩).mp ht))
        (by decide +kernel)
  have hcard : Nat.card ((That.subgroupOf P2h).map φ) = 128 := by
    rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (That_le_Bh.trans (show Bh ≤ P2h from inf_le_right))).toEquiv, card_That]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_Thc])

theorem model_That_aligned_iff (g : ↥P2h) :
    (g : Ah) ∈ That ↔ InD (extAlignedPerm g) := by
  obtain ⟨e, _, he⟩ := exists_model_coords_aligned
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hmap : (That.subgroupOf P2h).map φ = Thc := map_That_aligned e he
  constructor
  · intro hg
    have h := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hg)
    rw [hmap] at h
    change InD ((e g : Mof _) : Mc).right at h
    rwa [he] at h
  · intro hg
    have h : φ g ∈ Thc := by change InD ((e g : Mof _) : Mc).right; rwa [he]
    rw [← hmap] at h
    obtain ⟨t, ht, htg⟩ := Subgroup.mem_map.mp h
    exact Subgroup.mem_subgroupOf.mp (hφ htg ▸ ht)

theorem map_Bh_aligned
    (e : ↥P2h ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))))
    (he : ∀ g : ↥P2h, ((e g : Mof _) : Mc).right = extAlignedPerm g) :
    (Bh.subgroupOf P2h).map ((Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp
      e.toMonoidHom) = Bhc := by
  let φ : ↥P2h →* Mc := (Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hle : (Bh.subgroupOf P2h).map φ ≤ Bhc := by
    rintro _ ⟨g, hg, rfl⟩
    change ((e g : Mof _) : Mc).right 4 = 4
    rw [he]
    exact (model_Bh_aligned_iff g).mp (Subgroup.mem_subgroupOf.mp hg)
  have hcard : Nat.card ((Bh.subgroupOf P2h).map φ) = 384 := by
    rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Bh ≤ P2h from inf_le_right)).toEquiv, card_Bh]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_Bhc])

end CFSG.GH74.QTGen4.U42
