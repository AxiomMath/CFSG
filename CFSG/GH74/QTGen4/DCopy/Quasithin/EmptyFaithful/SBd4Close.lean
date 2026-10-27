module

public import CFSG.Quasithin.EmptyFaithful.SBd4Close
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153G23

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def L3ClosingQ_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → IsLnTwoQuot L 3 → Concl15312Two Yp L →
      ⁅VZ T M, YL153 Yp L⁆ ≠ ⊥ → Yp = Y153 Mc M →
      Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → B6.conjSub t' (YL153 Yp L) = YC153 Yp L →
        ⁅B6.conjSub t' ⁅pCoreOf 2 (L ⊔ R153 T V₁ Yp), L⁆, L⁆ ≤ ⁅pCoreOf 2 (L ⊔ R153 T V₁ Yp), L⁆

namespace SBd4

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

open CFSG.Quasithin.S153D in

theorem l3Closing_of_named_inputs_F4 (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kL : L3YLLabel) (kQ : L3ClosingQ_F4) : L3Closing_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp := pCoreOf_sup_R153_le c.facts hLI hLq hRN
  have hlab := kL G T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY

  obtain ⟨t', ht'T, ht'S, hswap⟩ := szN3_exists_swap hyp hh.decomp hlab
  have hTS : T ≤ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp hh.decomp
  have hSV₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) := by
    obtain ⟨hc1, -⟩ := szN3_conj_V_swap hyp hh.decomp ht'T ht'S
    intro s hs
    have h1 : t'⁻¹ * s * t' ∈ Sgp153 T V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTS (inv_mem ht'T)) s).mp hs
      simpa using this
    rw [← hc1]
    exact mem_normalizer_conjSub (hSV₁ h1)

  have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL153 Yp L : Set G) := by
    rcases hlab with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₁
    · rw [h1]; exact szN3_S_le_normalizer_oTwoUpper hyp inf_le_left hSV₂
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) :=
    szN3_S_le_normalizer_L h37 h38 c hSYL
  have hcomm := kQ G T Mc M V₁ V₂ Yp I L t c hq c12 hV hYY hSL t' ht'T ht'S hswap

  set R : Subgroup G := R153 T V₁ Yp with hR
  set O : Subgroup G := pCoreOf 2 (L ⊔ R) with hOdef
  set Q : Subgroup G := ⁅O, L⁆ with hQ
  have hOL : L ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (L ⊔ R) (Subgroup.mem_sup_left hl)
  have hYpR : Yp ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hSR : Sgp153 T V₁ ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hNO : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.normalizer (R : Set G) →
      g ∈ Subgroup.normalizer (O : Set G) := fun g h1 h2 =>
    normalizer_le_normalizer_pCoreOf 2 (L ⊔ R)
      (Subgroup.inf_normalizer_le_normalizer_sup L R ⟨h1, h2⟩)
  have hQL : Q ≤ L := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRN (hO hx)) l).mp hl
    rw [commutatorElement_def]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hQO : Q ≤ O := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hOL hl) _).mp (O.inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact O.mul_mem hx h1
  have hQ2 : IsPGroup 2 Q := (pCoreOf_isPGroup 2 (L ⊔ R)).to_le hQO
  have hUQ : ⁅WL153 T M L, L⁆ ≤ Q := by
    have hWc : WL153 T M L ≤ centerOf O := WL_le_centerOf hh c.ctx c.facts hLI hO
    exact Subgroup.commutator_mono (fun x hx => (hWc hx).1) le_rfl
  have hU0 : ⁅WL153 T M L, L⁆ ≠ ⊥ := by
    intro h0
    apply not_le_centralizer_WL hh hLle hLn
    have h1 : ⁅L, WL153 T M L⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h0
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hQ0 : Q ≠ ⊥ := fun h => hU0 (eq_bot_iff.mpr (h ▸ hUQ))
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := fun l hl =>
    mem_normalizer_commutator' (hOL hl) (Subgroup.le_normalizer hl)
  have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    mem_normalizer_commutator' (hNO s (hSL hs) (hSR hs)) (hSL hs)
  have hYQ : Y153 Mc M ≤ Subgroup.normalizer (Q : Set G) := fun y hy => by
    have hy' : y ∈ Yp := hYY ▸ hy
    exact mem_normalizer_commutator' (hNO y (hYpL hy') (hYpR hy')) (hYpL hy')
  have hTY : T ≤ Subgroup.normalizer (Y153 Mc M : Set G) := fun x hx =>
    le_normalizer_Y153 Mc M (hyp.T_le hx)
  have hidx : (Sgp153 T V₁).relIndex T = 2 := hh.decomp.relIndex_nS hyp
  have hprod : ∀ a ∈ T, ∀ b ∈ T, a ∉ Sgp153 T V₁ → b ∉ Sgp153 T V₁ → a * b ∈ Sgp153 T V₁ := by
    intro a ha b hb haS hbS
    have h2 : ((Sgp153 T V₁).subgroupOf T).index = 2 := hidx
    have h3 := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    have hiff : (⟨a, ha⟩ * ⟨b, hb⟩ : ↥T) ∈ (Sgp153 T V₁).subgroupOf T := by
      rw [h3]
      exact iff_of_false (fun h => haS h) (fun h => hbS h)
    exact hiff
  exact closing_core hQL hQ2 hQ0 hLQ hSQ hYQ hTS hTY ht'T ht'S hprod hcomm

end Main

end SBd4

end CFSG.Quasithin
