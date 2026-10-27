module

public import CFSG.GH74.QTGen4.U42.GSideCoords
public import CFSG.GH74.QTGen4.U42.MSplitGenF

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem frame_V_le_L (S : A5.Setting G T L V) : V ≤ L := by
  rw [← S.irr.2.2.2.1]
  refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
  have hN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer S.T_le_NL
  change v * l * v⁻¹ * l⁻¹ ∈ L
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN (V_le_LT S hv)) l).mp hl)
    (L.inv_mem hl)

theorem exists_coords_LT (S : A5.Setting G T L V) (hO : pCoreOf 2 (L ⊔ T) = V) :
    ∃ e : ↥(L ⊔ T) ≃* Mof (coordData S hO).ρ.range, IsCoords S e := by
  classical
  obtain ⟨A, hAM, hAV, hVA⟩ := Setting.exists_complement_of_le S (frame_V_le_L S) hO
  have hA0V : A.subgroupOf (L ⊔ T) ⊓ (coordData S hO).V = ⊥ := by
    apply le_antisymm ?_ bot_le
    rintro m ⟨hmA, hmV⟩
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hm : (m : G) ∈ A ⊓ V :=
      ⟨Subgroup.mem_subgroupOf.mp hmA, (mem_coordData_V S hO m).mp hmV⟩
    simpa only [hAV, Subgroup.mem_bot, Subgroup.coe_one] using hm
  have hVA0 : (coordData S hO).V ⊔ A.subgroupOf (L ⊔ T) = ⊤ := by
    rw [coordData_V]
    rw [← Subgroup.subgroupOf_sup (V_le_LT S) hAM, hVA, Subgroup.subgroupOf_self]
  obtain ⟨e, heV, heR⟩ := (coordData S hO).equiv_of_complement
    (A.subgroupOf (L ⊔ T)) hA0V hVA0
  refine ⟨e, IsCoords.mk e ?_ ?_⟩
  · intro v hv
    have hvc : (⟨v, V_le_LT S hv⟩ : ↥(L ⊔ T)) ∈ (coordData S hO).V :=
      (mem_coordData_V S hO _).mpr hv
    have h := heV ⟨⟨v, V_le_LT S hv⟩, hvc⟩
    rw [coordData_psi_apply] at h
    exact h
  · intro m
    exact (heR m).trans (coordData_rho_apply S hO m)

private theorem odd_sign_mul (u v : ℤˣ) (hu : u ≠ 1) (hv : v ≠ 1) : u * v = 1 := by
  rcases Int.units_eq_one_or u with h | h
  · exact (hu h).elim
  · rcases Int.units_eq_one_or v with h' | h'
    · exact (hv h').elim
    · rw [h, h']
      decide

theorem rho_range_LT_extension (S : A5.Setting G T L V)
    (hO : pCoreOf 2 (L ⊔ T) = V) (hE : ¬ Setting.PlainCase S) :
    (coordData S hO).ρ.range = ⊤ := by
  have hodd : ∃ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ∧ (S.frame.ρ g).sign ≠ 1 := by
    by_contra hn
    push Not at hn
    exact hE (fun g hg => InK4_of_InD _ (S.frame.T_D g hg) (hn g hg))
  obtain ⟨t, ht, hts⟩ := hodd
  apply eq_top_iff.mpr
  intro σ _
  by_cases hs : σ.sign = 1
  · obtain ⟨g, hg, hρ⟩ := (S.frame.image_L σ).mpr hs
    refine MonoidHom.mem_range.mpr ⟨⟨(g : G), (le_sup_left : L ≤ L ⊔ T) hg⟩, ?_⟩
    rw [coordData_rho_apply]
    exact hρ
  · have hsgn : (σ * (S.frame.ρ t)⁻¹).sign = 1 := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
      exact odd_sign_mul _ _ hs hts
    obtain ⟨g, hg, hρ⟩ := (S.frame.image_L _).mpr hsgn
    refine MonoidHom.mem_range.mpr ⟨⟨(g : G) * (t : G),
      (L ⊔ T).mul_mem ((le_sup_left : L ≤ L ⊔ T) hg) ((le_sup_right : T ≤ L ⊔ T) ht)⟩, ?_⟩
    rw [coordData_rho_apply]
    change S.frame.ρ (g * t) = σ
    rw [map_mul, hρ]
    group

theorem exists_coords_extension (S : A5.Setting G T L V)
    (hO : pCoreOf 2 (L ⊔ T) = V) (hE : ¬ Setting.PlainCase S) :
    ∃ e : ↥(L ⊔ T) ≃* Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))), IsCoords S e := by
  obtain ⟨e, he⟩ := exists_coords_LT S hO
  let e' := e.trans (MulEquiv.subgroupCongr (congrArg Mof (rho_range_LT_extension S hO hE)))
  refine ⟨e', IsCoords.mk e' ?_ ?_⟩
  · intro v hv
    exact IsCoords.left he v hv
  · intro m
    exact IsCoords.right he m

end CFSG.GH74.QTGen4.U42
