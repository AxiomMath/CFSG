module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153G23
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBd4B1
public import CFSG.Quasithin.EmptyFaithful.S153D16
public import CFSG.Quasithin.EmptyFaithful.S153F19
public import CFSG.Quasithin.EmptyFaithful.SBd4B1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd5

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

open CFSG.Quasithin.S153D in

theorem l3Branch1_of_dichotomy_F4 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (kV : V2CommutatorYp) (kD : L3ULDichotomy_F4) : L3Branch1_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq c12 hV0
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYpL : Yp ≤ Subgroup.normalizer (L : Set G) := Yp_le_normalizer h37 h38 hh c.ctx.inH hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    pCoreOf_sup_R153_le c.facts hLI hLq hRN
  have hYpeq : Yp = YL153 Yp L ⊔ YC153 Yp L := c12.1
  have hE9 : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) := c12.2.2.2

  have hYLle : YL153 Yp L ≤ Yp ⊓ L := oTwoUpper_le _
  have hYLV : YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G) := by
    intro y hy
    have hVc : VZ T M ≤ Subgroup.centralizer (YL153 Yp L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV0
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hVc hv)) y hy).symm

  have hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := by
    rcases hh.cases with hY | hU
    · exfalso
      rcases Hyp153.lemma_15_3_7_cases h113 hh.hyp with ⟨hcore, -⟩ | ⟨hP, -⟩
      · apply c.c16.YL_ne
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨hx, hxo⟩
        have hxY : x ∈ Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G) :=
          ⟨hY ▸ hx.1, hYLV (Subgroup.subset_closure ⟨hx, hxo⟩)⟩
        exact Subgroup.mem_bot.mpr (S153F.eq_one_of_mem_pCoreOf_of_odd (hcore ▸ hxY) hxo)
      · have h9 := S153F.card_eq_nine_of_isElemAbelianOfRank hE9
        rw [hY] at h9
        have h27 := hP.2.1
        rw [h9] at h27
        norm_num at h27
    · exact hU
  obtain ⟨hN1, hN2⟩ := Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU.1
  have hYpY : Yp ≤ Y153 Mc M := by
    have := (oTwoUpper_le (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))).trans inf_le_left
    rwa [← hU.2] at this
  have hYpC1 : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
    have := (oTwoUpper_le (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))).trans inf_le_right
    rwa [← hU.2] at this
  have hYpM : Yp ≤ M := hYpY.trans (Y153_le Mc M)
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer
  have hYCle : YC153 Yp L ≤ Yp := fun y hy => by
    obtain ⟨hyYp, -⟩ := (Subgroup.closure_le _).mpr (fun z hz => hz.1) hy
    exact hyYp
  have hYCsec : YC153 Yp L ≤ centralizerSection Yp L (pCoreOf 2 L) := oTwoUpper_le _
  have hYCcomm : ∀ y ∈ YC153 Yp L, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L :=
    fun y hy l hl => (hYCsec hy).2.2.2 l hl

  set W : Subgroup G := WL153 T M L with hW
  have hWc : W ≤ centerOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) := WL_le_centerOf hh c.ctx c.facts hLI hO
  have hWR : W ≤ R153 T V₁ Yp := fun x hx => hO (hWc hx).1
  have hWN : W ≤ Subgroup.normalizer (L : Set G) := hWR.trans hRN
  have hUL : ⁅W, L⁆ ≤ L := by
    refine Subgroup.commutator_le.mpr fun w hw l hl => ?_
    have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hWN hw) l).mp hl
    rw [commutatorElement_def]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hUW : ⁅W, L⁆ ≤ W := by
    refine Subgroup.commutator_le.mpr fun w hw l hl => ?_
    have h1 : l * w⁻¹ * l⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (VZ T M) L hl) _).mp (W.inv_mem hw)
    rw [commutatorElement_def]
    have e : w * l * w⁻¹ * l⁻¹ = w * (l * w⁻¹ * l⁻¹) := by group
    rw [e]
    exact W.mul_mem hw h1
  have hYCN : YC153 Yp L ≤ Subgroup.normalizer (W : Set G) := by
    intro y hy
    refine SBd4.mem_normalizer_conjClosure (hYpL (hYCle hy)) ?_
    exact hMN (hYpM (hYCle hy))
  have hYCL : YC153 Yp L ≤ Subgroup.normalizer (L : Set G) := fun y hy => hYpL (hYCle hy)
  have hV : VZ T M ≤ W := le_conjClosure _ _

  have hOW : ∀ x ∈ pCoreOf 2 L, ∀ w ∈ W, w * x = x * w := by
    intro x hx w hw
    have hxO : x ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) := pCoreOf_le_pCoreOf_sup hRN hx
    exact (Subgroup.mem_centralizer_iff.mp (hWc hw).2 x hxO).symm
  rcases kD G T Mc M V₁ V₂ Yp I L t c hq c12 hV0 with hA | ⟨y₀, hy₀, hfix⟩
  ·
    have hWYC : ⁅W, YC153 Yp L⁆ ≤ Subgroup.centralizer (L : Set G) := by
      have h1 : ⁅⁅W, YC153 Yp L⁆, L⁆ = ⊥ := by
        refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := W) (H₂ := YC153 Yp L)
          (H₃ := L) ?_ ?_
        · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          refine Subgroup.commutator_le.mpr fun y hy l hl => ?_
          have h2 : l * y * l⁻¹ * y⁻¹ ∈ pCoreOf 2 L := hYCcomm y hy l hl
          have h3 : ⁅y, l⁆ = (l * y * l⁻¹ * y⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [h3]
          refine Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
          exact hOW _ h2 w hw
        · rw [Subgroup.commutator_comm L W]
          exact hA
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have hV₂ : V₂ ≤ Subgroup.centralizer (L : Set G) := by
      have e : ⁅V₂, Yp⁆ = ⁅V₂, YL153 Yp L ⊔ YC153 Yp L⁆ := congrArg (fun Z => ⁅V₂, Z⁆) hYpeq
      have hcomm' : ⁅V₂, YL153 Yp L ⊔ YC153 Yp L⁆ ≤ Subgroup.centralizer (L : Set G) := by
        refine S153F.commutator_sup_le (K := Subgroup.centralizer (L : Set G)) ?_ ?_ ?_ ?_
        · intro g hg
          exact S153F.mem_normalizer_centralizer_of_mem_normalizer
            (Subgroup.le_normalizer ((hYLle hg).2))
        · intro g hg
          exact S153F.mem_normalizer_centralizer_of_mem_normalizer (hYCL hg)
        · intro x hx y hy
          have hxy := Subgroup.mem_centralizer_iff.mp (hYLV hy) x (hh.decomp.le₂ hx)
          rw [commutatorElement_eq_one_iff_mul_comm.mpr hxy]
          exact one_mem _
        · intro x hx y hy
          exact hWYC (Subgroup.commutator_mem_commutator (hV (hh.decomp.le₂ hx)) hy)
      have h2 := kV G T Mc M V₁ V₂ Yp t hh
      rw [e] at h2
      exact h2 ▸ hcomm'
    have hLN : L ≤ Subgroup.normalizer (V₂ : Set G) := fun l hl =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
        ((Subgroup.mem_centralizer_iff.mp (hV₂ hv)) l hl).symm)
    exact hLn (le_inf (hLN.trans hN2) hLle)
  ·
    have hV₁ : V₁ ≤ Subgroup.centralizer (L : Set G) := by
      intro v hv
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      have hvW : v ∈ W := hV (hh.decomp.le₁ hv)
      have hcW : ⁅v, l⁆ ∈ ⁅W, L⁆ := Subgroup.commutator_mem_commutator hvW hl
      have hvy : v * y₀ = y₀ * v := Subgroup.mem_centralizer_iff.mp (hYpC1 (hYCle hy₀)) v hv
      set o : G := y₀ * l * y₀⁻¹ * l⁻¹ with ho
      have ho2 : o ∈ pCoreOf 2 L := by
        have h2 := (pCoreOf 2 L).inv_mem (hYCcomm y₀ hy₀ l hl)
        have e : (l * y₀ * l⁻¹ * y₀⁻¹)⁻¹ = o := by rw [ho]; group
        rwa [e] at h2
      have hov : v * o = o * v := hOW o ho2 v hvW
      have hoc : ∀ w ∈ W, o * w = w * o := fun w hw => (hOW o ho2 w hw).symm
      have hy₀c : y₀ * ⁅v, l⁆ * y₀⁻¹ = ⁅v, l⁆ := by
        have e1 : y₀ * v * y₀⁻¹ = v := by rw [← hvy]; group
        have e2 : y₀ * l * y₀⁻¹ = o * l := by rw [ho]; group
        have e3 : y₀ * ⁅v, l⁆ * y₀⁻¹ = (y₀ * v * y₀⁻¹) * (y₀ * l * y₀⁻¹) * (y₀ * v * y₀⁻¹)⁻¹ *
            (y₀ * l * y₀⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e3, e1, e2]
        have hcW' : ⁅v, l⁆ ∈ W := hUW hcW
        have e4 : v * (o * l) * v⁻¹ * (o * l)⁻¹ = o * ⁅v, l⁆ * o⁻¹ := by
          have : v * o = o * v := hov
          calc v * (o * l) * v⁻¹ * (o * l)⁻¹ = (v * o) * l * v⁻¹ * l⁻¹ * o⁻¹ := by group
            _ = (o * v) * l * v⁻¹ * l⁻¹ * o⁻¹ := by rw [this]
            _ = o * ⁅v, l⁆ * o⁻¹ := by simp only [commutatorElement_def]; group
        rw [e4]
        have e5 : o * ⁅v, l⁆ = ⁅v, l⁆ * o := hoc _ hcW'
        rw [e5]
        group
      have h1 := hfix _ hcW hy₀c
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    have hLN : L ≤ Subgroup.normalizer (V₁ : Set G) := fun l hl =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
        ((Subgroup.mem_centralizer_iff.mp (hV₁ hv)) l hl).symm)
    exact hLn (le_inf (hLN.trans hN1) hLle)

end Main

end SBd5

end CFSG.Quasithin
