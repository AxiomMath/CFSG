module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL312a
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisMb2
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL310a

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

section Ybar

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

theorem piX_ne_one_of_inv {u : D.Y1} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : (u : Y) ≠ D.z) :
    D.piX u ≠ 1 := by
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, D.mem_zpowers_l_iff] at h
  have hu2' : (u : Y) * (u : Y) = 1 := congrArg Subtype.val hu2
  rcases h with h | h | h | h
  · exact hu1 (Subtype.ext h)
  · rw [h, D.l_mul_l] at hu2'
    exact D.z_ne_one hu2'
  · exact huz h
  · rw [h, D.lz_sq] at hu2'
    exact D.z_ne_one hu2'

omit [Finite Y] in
theorem E_le_S1 : D.E ≤ D.S1 := by
  rintro _ ⟨e, he, rfl⟩
  exact D.toG_mem_S1 (SE.Esub.mem_carrier.mp he).1


theorem conj_t_of_mem_E_Y (hC : GorensteinHaradaThmCInput) (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y)
    (hA : pCore 2 D.Xt ≠ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt))
    {u : D.Y1} (hu : (u : Y) ∈ D.E) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : (u : Y) ≠ D.z) :
    ∃ h : D.Y1, h⁻¹ * ⟨D.t, D.E_le_Y1 (D.toG_mem_E_iff.mpr (by decide))⟩ * h = u := by
  obtain ⟨-, -, -, htr⟩ := D.prop38A_of hC hO hz hA
  set t₁ : D.Y1 := ⟨D.t, D.E_le_Y1 (D.toG_mem_E_iff.mpr (by decide))⟩ with ht₁
  have htE : (t₁ : Y) ∈ D.E := D.toG_mem_E_iff.mpr (by decide)
  have ht2 : t₁ * t₁ = 1 := Subtype.ext D.t_mul_t
  have ht1 : t₁ ≠ 1 := fun h => D.t_ne_one (congrArg Subtype.val h)
  have htz : (t₁ : Y) ≠ D.z := fun h => D.z_ne_t h.symm
  obtain ⟨g, hg⟩ := htr (D.piX t₁) ((D.piX_mem_Et_iff _).mpr htE) (D.piX u)
    ((D.piX_mem_Et_iff _).mpr hu) (D.piX_ne_one_of_inv ht2 ht1 htz)
    (D.piX_ne_one_of_inv hu2 hu1 huz)
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective (zpowers D.lY) g
  exact D.exists_conj_Y1_of_conj_Xt (D.E_le_S1 hu) ht2 hu2 hu1 huz
    (by rw [map_mul, map_mul, map_inv]; exact hg)

end GHSylow

end Ybar

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

theorem conj_t_of_mem_E_A (hC : GorensteinHaradaThmCInput) (hA : ¬ D.caseB) {u : G}
    (hu : u ∈ D.E) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ D.z) :
    ∃ m ∈ D.M, m⁻¹ * D.t * m = u := by
  obtain ⟨e, he, rfl⟩ := hu
  have he2 : e * e = 1 := D.toG_injective (by rw [map_mul, hu2, map_one])
  have heY : D.toMb.toG e ∈ D.toMb.Y1 := D.toMb.E_le_Y1 ⟨e, he, rfl⟩
  obtain ⟨h, hh⟩ := D.toMb.conj_t_of_mem_E_Y hC D.pPrimeCore_Mb D.z_comm_Mb hA
    (u := ⟨D.toMb.toG e, heY⟩) ⟨e, he, rfl⟩
    (Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, he2, map_one]; rfl))
    (fun h1 => hu1 (by
      have h1' : D.toMb.toG e = D.toMb.toG 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      rw [D.toMb.toG_injective h1', map_one]))
    (fun h1 => huz (by rw [D.toMb.toG_injective h1]))
  obtain ⟨m, hm⟩ := D.exists_conj_M_of_conj_Mb (u := ⟨D.t, D.S_le_M (D.toG_mem _)⟩)
    (v := ⟨D.toG e, D.S_le_M (D.toG_mem _)⟩) (Subtype.ext D.t_mul_t) (Subtype.ext hu2)
    (g := (h : D.Mb)) (congrArg Subtype.val hh)
  exact ⟨m, m.2, congrArg Subtype.val hm⟩

theorem conj_t_invRep_A (hC : GorensteinHaradaThmCInput) (hA : ¬ D.caseB) {i : Fin 9}
    (hi : i = 2 ∨ i = 3 ∨ i = 4) : ∃ m ∈ D.M, m⁻¹ * D.t * m = D.toG (SE.invRep i) := by
  have key : SE.predE (SE.invRep i) ∧ SE.invRep i ≠ 1 ∧ SE.invRep i ≠ SE.gen 0 := by
    rcases hi with rfl | rfl | rfl <;> decide
  obtain ⟨hE, h1, hz⟩ := key
  refine D.conj_t_of_mem_E_A hC hA (D.toG_mem_E_iff.mpr hE)
    (by rw [← map_mul, SE.invRep_mul_self' i, map_one])
    (fun h => h1 (D.toG_eq_one_iff.mp h)) (fun h => hz (D.toG_injective h))


theorem fusion_A (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) :
    (∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i)) ∧
      (∃ g ∈ D.M, g⁻¹ * D.y * g = D.x) ∧
      ∃ n : G, n⁻¹ * D.a * n = D.z ∧ n⁻¹ * D.t * n = D.t ∧
        (n⁻¹ * D.x * n = D.x ∨ n⁻¹ * (D.x * D.z) * n = D.x * D.z) ∧
        ∃ s₁ ∈ (D.S : Subgroup G), ∃ s₂ ∈ (D.S : Subgroup G),
          n⁻¹ * (s₁⁻¹ * D.x * s₁) * n = s₂⁻¹ * D.al * s₂ := by
  have hT : ∀ i : Fin 9, (i = 2 ∨ i = 3 ∨ i = 4) → D.FusN 1 i := fun i hi => by
    obtain ⟨m, -, hm⟩ := D.conj_t_invRep_A hC hA hi
    exact D.fusN_of_conj_rep (i := 1) hm
  rcases D.a_fusion hidx hxa with ⟨g, hgu, hgood, hgC⟩ | ⟨g, -, -, -, hsyl⟩
  · obtain ⟨h17, -, hedge, s, hsS, hst, hsx⟩ := D.aZ_decode hgu hgC hgood
    have h70 : D.FusN 7 0 := D.fusN_of_conj_rep (i := 7) (j := 0)
      (by rw [show SE.invRep 0 = SE.gen 0 by decide]; exact hgu)
    have h10 : D.FusN 1 0 := D.fusN_trans h17 h70
    have h58 : D.FusN 5 8 := by
      refine D.fusN_of_edge (g := g) ?_
      rw [show SE.invRep (Fin.ofNat 9 5) = SE.gen 6 by decide]
      exact hedge
    have hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i) := by
      intro i hi
      interval_cases i
      · exact D.fusN_refl 0
      · exact h10
      · exact D.fusN_trans (D.fusN_symm (hT 2 (by decide))) h10
      · exact D.fusN_trans (D.fusN_symm (hT 3 (by decide))) h10
      · exact D.fusN_trans (D.fusN_symm (hT 4 (by decide))) h10
      · exact D.fusN_refl 5
      · exact D.fusN_refl 6
      · exact h70
      · exact D.fusN_symm h58
    refine ⟨hP, D.y_fusion_A hidx (fun hg hu hS => D.conj_mem_E_of_M hC hg hu hS) hP,
      g * s, ?_, hst, hsx, ?_⟩
    · rw [conj_conj, hgu, D.conj_z_S hsS]
    · obtain ⟨s₁, hs₁, s₂, hs₂, h⟩ := hedge
      refine ⟨s₁, hs₁, s₂ * s, mul_mem hs₂ hsS, ?_⟩
      rw [conj_conj, h]
      group
  · exact absurd (hT 3 (by decide)) (D.not_fusN_of_lt (i := 3) (j := 1) hsyl (by decide)).2

end GHSylow

end CFSG.ComponentClassification.GHarris
