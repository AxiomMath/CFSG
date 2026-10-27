module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5EA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5Cut
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5EFF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem inf_eq_borelL_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n) :
    (borelL T L ⊔ H) ⊓ L = borelL T L := by
  classical
  have h := c.hyp
  refine le_antisymm (fun g hg => ?_) (le_inf le_sup_left inf_le_left)
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨F, _, _, _, -, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [c.V_eq]; exact hS.centralizer_le
  have hLN := hc.le_normalizer
  by_cases hup : (ψ (autHom hLN ⟨g, hg.2⟩) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact hc.mem_borelL_of_upper_ch615 hCV hg.2 hup
  exfalso
  set X := borelL T L ⊔ H with hXdef
  set φ : ↥L →* SL(2, F) := ψ.toMonoidHom.comp (autHom hLN) with hφ

  have htop : ((X ⊓ L).subgroupOf L).map φ = ⊤ := by
    refine eq_top_of_upper_ch615 (fun A hA => ?_)
      ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩ hup
    obtain ⟨b, hb, hbA⟩ := hc.exists_mem_borelL_eq_ch615 hCV hA
    exact ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_sup_left hb, hb.1⟩, hbA⟩

  have hLX : L ≤ X := by
    intro l hl
    have hmem : φ ⟨l, hl⟩ ∈ ((X ⊓ L).subgroupOf L).map φ := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxl⟩ := hmem
    have hx' : (x : G) ∈ X ⊓ L := Subgroup.mem_subgroupOf.mp hx
    have h1 : autHom hLN (x⁻¹ * ⟨l, hl⟩) = 1 := by
      have h2 : φ (x⁻¹ * ⟨l, hl⟩) = 1 := by rw [map_mul, map_inv, hxl, inv_mul_cancel]
      apply ψ.injective
      rw [map_one]
      exact h2
    have hcen := mem_centralizer_of_autHom_eq_one hLN h1
    have hxlT : ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ T :=
      hCV ⟨Subgroup.mem_sup_left (x⁻¹ * ⟨l, hl⟩).2, hcen⟩
    have hxlX : ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) ∈ X :=
      Subgroup.mem_sup_left (Hyp5_0_1.inf_le_borel T L ⟨hxlT, (x⁻¹ * ⟨l, hl⟩).2⟩)
    have e : l = (x : G) * ((x⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e]
    exact X.mul_mem hx'.1 hxlX

  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
    ⟨pCoreOf 2 X, c.X_O2, pCoreOf_isPGroup 2 X, rfl⟩
  have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := le_normalizer_pCoreOf 2 X
  have hTX : T ≤ X := c.hH.1.1.trans le_sup_right
  exact c.hH.2.1 ((le_sup_right.trans hXN).trans (le_of_isUniqueM_of_le_twoLocal
    (h.isUniqueM_F4 h432) (sup_le (hLX.trans hXN) (hTX.trans hXN)) hloc))

end Cx615C

theorem res615E_of_F4 (h432 : Stmt4_3_2_F4) (hFF : Res615EFF_F4) : Res615E_F4 := by
  intro G _ _ T M L V H n c hN
  have h := c.hyp
  obtain ⟨z, hz, hz1, ⟨d, hdB, hdodd, hd1, hdz⟩, hnot⟩ := hFF G T M L V H n c hN
  apply hnot
  have hzZ := mem_quasithinOmegaOneCenter_iff.mp hz.1
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := c.CZd d hdB hdodd hd1 ⟨hz.1, hzd⟩

  have hord : orderOf z = 2 := orderOf_eq_prime hzZ.2.2 hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers z ≠ ⊥ := fun h0 => hz1 (by
    have := Subgroup.mem_zpowers z
    rw [h0] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (fun l hl => Cx615C.mem_normalizer_zpowers_ch615
      (Subgroup.mem_centralizer_iff.mp hzL l hl))
      (fun t ht => Cx615C.mem_normalizer_zpowers_ch615
        (Subgroup.mem_centralizer_iff.mp hzZ.2.1 t ht))
  have hNM := le_of_isUniqueM_of_le_twoLocal (h.isUniqueM_F4 h432) hLT hloc

  intro x hx
  have hxz : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hx.2 z rfl).symm
  have hxM : x ∈ M := hNM (Cx615C.mem_normalizer_zpowers_ch615 hxz)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := h.normal hxM
  have hxX : x ∈ Subgroup.normalizer ((borelL T L ⊔ H : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hx.1
  have hxXL := Subgroup.inf_normalizer_le_normalizer_inf ⟨hxX, hxL⟩
  rwa [c.inf_eq_borelL_ch615_F4 h432] at hxXL

end CFSG.Quasithin.H13
