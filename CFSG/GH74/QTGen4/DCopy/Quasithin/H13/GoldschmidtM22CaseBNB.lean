module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBNBS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBQL

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace BCtx_F4

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)

include c in
theorem exists_rho_NB {a : G} (haN : a ∈ Subgroup.normalizer (V : Set G))
    (has : Equiv.Perm.sign (c.ρ a) = -1) (ha2 : a * a = 1) (σ : Equiv.Perm (Fin 5)) :
    ∃ x ∈ L ⊔ Subgroup.zpowers a, c.ρ x = σ := by
  have haa : c.ρ a * c.ρ a = 1 := by
    rw [← PermRho.apply_mul haN haN, ha2, PermRho.apply_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · obtain ⟨l, hl, hlσ⟩ := c.exists_rho_L σ (Equiv.Perm.mem_alternatingGroup.mpr hs)
    exact ⟨l, Subgroup.mem_sup_left hl, hlσ⟩
  · have hs' : Equiv.Perm.sign (σ * c.ρ a) = 1 := by
      rw [map_mul, hs, has]
      rfl
    obtain ⟨l, hl, hlσ⟩ := c.exists_rho_L _ (Equiv.Perm.mem_alternatingGroup.mpr hs')
    refine ⟨l * a, (L ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left hl)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)), ?_⟩
    rw [PermRho.apply_mul (c.L_le_N hl) haN, hlσ, mul_assoc, haa, mul_one]

include c in
theorem NB_inf_Q_le_V {a : G} (haN : a ∈ Subgroup.normalizer (V : Set G))
    (has : Equiv.Perm.sign (c.ρ a) = -1) (ha2 : a * a = 1) {x : G}
    (hx : x ∈ L ⊔ Subgroup.zpowers a) (hxQ : x ∈ Subgroup.centralizer (V : Set G)) : x ∈ V := by
  rcases (mem_sup_zpowers_iff_F4 (c.N_le_normalizer_L haN) ha2).mp hx with hxL | ⟨l, hl, rfl⟩
  · exact c.inf_Q_L_le_V hxQ hxL
  · exfalso
    have hxN : l * a ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).mul_mem (c.L_le_N hl) haN
    have h1 := (c.ρ.eq_one_iff hxN).mpr hxQ
    have h2 := congrArg Equiv.Perm.sign h1
    rw [PermRho.apply_mul (c.L_le_N hl) haN, map_mul, c.sign_rho_L l hl, has, map_one] at h2
    exact absurd h2 (by decide)

include c in
theorem exists_r (h2 : V.relIndex (Subgroup.centralizer (V : Set G)) = 2) :
    ∃ r ∈ Subgroup.centralizer (V : Set G), r ∉ V ∧ r * r = 1 ∧
      ∀ b ∈ Subgroup.centralizer (V : Set G), b ∈ V ∨ r⁻¹ * b ∈ V := by
  obtain ⟨a, haQ, ha⟩ := Subgroup.relIndex_eq_two_iff'.mp h2
  have haV : a ∉ V := by
    intro h
    have := ha 1 (Subgroup.centralizer (V : Set G)).one_mem
    simp only [mul_one] at this
    rcases this with ⟨h1, h3⟩ | ⟨h1, h3⟩
    · exact h3 V.one_mem
    · exact h3 h
  refine ⟨a⁻¹, (Subgroup.centralizer (V : Set G)).inv_mem haQ,
    fun h => haV (by simpa using V.inv_mem h), ?_, fun b hb => ?_⟩
  · rw [← pow_two]
    exact c.isElemAbelian_Q.2 _ ((Subgroup.centralizer (V : Set G)).inv_mem haQ)
  · by_cases hbV : b ∈ V
    · exact Or.inl hbV
    · right
      rcases ha b hb with ⟨h1, -⟩ | ⟨h1, h3⟩
      · simpa using h1
      · exact absurd h1 hbV

include c in
theorem relIndex_T0 {a r : G} (haN : a ∈ Subgroup.normalizer (V : Set G))
    (has : Equiv.Perm.sign (c.ρ a) = -1) (ha2 : a * a = 1)
    (hrQ : r ∈ Subgroup.centralizer (V : Set G)) (hr2 : r * r = 1)
    (hQ : ∀ b ∈ Subgroup.centralizer (V : Set G), b ∈ V ∨ r⁻¹ * b ∈ V)
    (hrV : r ∉ V) :
    (T ⊓ (L ⊔ Subgroup.zpowers a)).relIndex T = 2 := by
  have hVNB : V ≤ L ⊔ Subgroup.zpowers a := c.V_le_L.trans le_sup_left
  have hr_not : r ∉ T ⊓ (L ⊔ Subgroup.zpowers a) := fun h =>
    hrV (c.NB_inf_Q_le_V haN has ha2 (Subgroup.mem_inf.mp h).2 hrQ)
  refine Subgroup.relIndex_eq_two_iff.mpr ⟨r, c.Q_le_T hrQ, fun b hb => ?_⟩
  by_cases hb0 : b ∈ T ⊓ (L ⊔ Subgroup.zpowers a)
  · right
    refine ⟨hb0, fun h => hr_not ?_⟩
    have := (T ⊓ (L ⊔ Subgroup.zpowers a)).mul_mem ((T ⊓ (L ⊔ Subgroup.zpowers a)).inv_mem hb0) h
    simpa using this
  · left
    refine ⟨?_, hb0⟩
    obtain ⟨x, hxNB, hxb⟩ := c.exists_rho_NB haN has ha2 (c.ρ b)
    have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
      sup_le c.L_le_N (Subgroup.zpowers_le.mpr haN) hxNB
    have hbN := c.T_le_N hb
    have hq : x⁻¹ * b ∈ Subgroup.centralizer (V : Set G) := (c.ρ.eq_iff hxN hbN).mp hxb
    have hxT : x ∈ T := by
      have : b * (x⁻¹ * b)⁻¹ ∈ T := T.mul_mem hb (T.inv_mem (c.Q_le_T hq))
      simpa [mul_assoc] using this
    have hx0 : x ∈ T ⊓ (L ⊔ Subgroup.zpowers a) := ⟨hxT, hxNB⟩
    rcases hQ _ hq with hqV | hqV
    · exact absurd (by
        have := (T ⊓ (L ⊔ Subgroup.zpowers a)).mul_mem hx0
          ⟨c.h.toHyp611.le_T hqV, hVNB hqV⟩
        simpa using this) hb0
    · have hcomm : (r⁻¹ * (x⁻¹ * b)) * r = r * (r⁻¹ * (x⁻¹ * b)) :=
        Subgroup.mem_centralizer_iff.mp hrQ _ hqV
      have : b * r = x * (r⁻¹ * (x⁻¹ * b)) := by
        calc b * r = x * (x⁻¹ * b) * r := by group
          _ = x * (r * (r⁻¹ * (x⁻¹ * b))) * r := by group
          _ = x * ((r⁻¹ * (x⁻¹ * b)) * r) * r := by rw [hcomm]
          _ = x * (r⁻¹ * (x⁻¹ * b)) * (r * r) := by group
          _ = x * (r⁻¹ * (x⁻¹ * b)) := by rw [hr2, mul_one]
      rw [this]
      exact (T ⊓ (L ⊔ Subgroup.zpowers a)).mul_mem hx0
        ⟨c.h.toHyp611.le_T hqV, hVNB hqV⟩

end BCtx_F4

end CFSG.Quasithin.H13.GM22
