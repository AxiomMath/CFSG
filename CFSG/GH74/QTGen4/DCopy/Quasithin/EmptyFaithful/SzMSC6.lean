module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBd4B1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134
public import CFSG.Quasithin.EmptyFaithful.S153F19
public import CFSG.Quasithin.EmptyFaithful.SBd5Perf
public import CFSG.Quasithin.EmptyFaithful.SBd5UL

public section

namespace CFSG.Quasithin

namespace SBd5

section Apply

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_c134Case_of_ctx_corr_F4 (hMS : MS93.AS_C_1_34_corr_F4) {T Mc M V₁ V₂ Yp I L : Subgroup G}
    {t : G} (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hq : IsLnTwoQuot L 3) :
    ∃ i : ℕ, MS93.IsC134CaseCorr i (L ⊔ R153 T V₁ Yp) (R153 T V₁ Yp) L := by
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hMSp : IsMSPair (L ⊔ R153 T V₁ Yp) (R153 T V₁ Yp) := c27_caseG hq c.c16.desc
  have hcomp : L ∈ cComp (L ⊔ R153 T V₁ Yp) := mem_cComp_sup' hLI hRN
  have hset : ((L ⊔ R153 T V₁ Yp : Subgroup G) : Set G) =
      (L : Set G) * (R153 T V₁ Yp : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left L _ hRN
  obtain ⟨e⟩ := hq
  let α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hα : IsModO2Surj L α := by
    refine ⟨e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
    show (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).ker = CFSG.pCore 2 ↥L
    rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) e.toMonoidHom
      e.injective, QuotientGroup.ker_mk']
  exact hMS G (L ⊔ R153 T V₁ Yp) (R153 T V₁ Yp) L hMSp hcomp hset
    ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

end Apply

section Main

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

theorem l3ULDichotomy_holds_corr_F4 (hMS : MS93.AS_C_1_34_corr_F4) : L3ULDichotomy_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hq _ _
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  obtain ⟨hLc, hLn, -, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLI
  have hRN : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := c.c16.R_norm
  have hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp :=
    S153D.pCoreOf_sup_R153_le c.facts hLI hLq hRN
  obtain ⟨i, hi⟩ := exists_c134Case_of_ctx_corr_F4 hMS c hq
  set R : Subgroup G := R153 T V₁ Yp with hR
  set O : Subgroup G := pCoreOf 2 (L ⊔ R) with hOdef
  set Q : Subgroup G := ⁅O, L⁆ with hQ
  set W : Subgroup G := WL153 T M L with hW
  have hOL : L ≤ Subgroup.normalizer (O : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (L ⊔ R) (Subgroup.mem_sup_left hl)
  have hYpR : Yp ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  have hNO : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) → g ∈ Subgroup.normalizer (R : Set G) →
      g ∈ Subgroup.normalizer (O : Set G) := fun g h1 h2 =>
    normalizer_le_normalizer_pCoreOf 2 (L ⊔ R)
      (Subgroup.inf_normalizer_le_normalizer_sup L R ⟨h1, h2⟩)
  have hQO : Q ≤ O := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hOL hl) _).mp (O.inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact O.mul_mem hx h1
  have hWc : W ≤ centerOf O := S153D.WL_le_centerOf hh c.ctx c.facts hLI hO
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    le_normalizer_conjClosure (VZ T M) L hl
  have hWab : IsElemAbelian 2 W := c.c16.reduced_LR.2.2.1
  have hWcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => by
    have := hWab.1
    exact setLike_mul_comm hx hy
  have hUW : ⁅W, L⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hLW
  have hAQ : ⁅W, L⁆ ≤ Q := Subgroup.commutator_mono (fun x hx => (hWc hx).1) le_rfl
  have hAZ : ⁅W, L⁆ ≤ centerOf Q := by
    refine le_inf hAQ ?_
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun q hq' => ?_
    exact Subgroup.mem_centralizer_iff.mp (hWc (hUW ha)).2 q (hQO hq')
  have hAc : ∀ a ∈ ⁅W, L⁆, ∀ q ∈ Q, a * q = q * a := fun a ha q hq' =>
    (Subgroup.mem_centralizer_iff.mp (hAZ ha).2 q hq').symm
  have hAA : ⁅⁅W, L⁆, L⁆ = ⁅W, L⁆ := commutator_commutator_eq_self hperf hLW hWcomm

  have KC : ∀ y ∈ centralizerSection Yp L (pCoreOf 2 L), Odd (orderOf y) →
      (∀ a ∈ ⁅W, L⁆, y * a * y⁻¹ = a) ∨ (∀ a ∈ ⁅W, L⁆, y * a * y⁻¹ = a → a = 1) := by
    intro y hy hodd
    obtain ⟨hyYp, hyL, -, hyc⟩ := hy
    have hyO : y ∈ Subgroup.normalizer (O : Set G) := hNO y hyL (hYpR hyYp)
    have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := mem_normalizer_commutator_of hyO hyL
    have hyZQ : y ∈ Subgroup.normalizer (centerOf Q : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hyQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hyQ⟩
    match i, hi with
    | 0, hi => exact hi.elim
    | 1, hi =>
      obtain ⟨-, n, F, _, _, hFc, hNS⟩ := hi
      obtain ⟨α, hαs, hαk, hZ⟩ :=
        (isNaturalSection_iff_isSumOfNaturalModules_one (CFSG.pCore 2 ↥L)
          (CFSG.Assembly.LowTwoRank.StatedSL 3 F) bot_le).mp hNS
      exact kc_of_module (Or.inl rfl) hFc ⟨hαs, hαk⟩ hq hZ hyQ hyL hyc hodd hAQ
    | 2, hi =>
      obtain ⟨⟨n, F, _, _, α, hFc, hα, hZ⟩, -⟩ := hi
      exact kc_of_module (Or.inr rfl) hFc hα hq hZ hyQ hyL hyc hodd hAQ
    | 3, hi =>
      obtain ⟨⟨n, F, _, _, α, hFc, hα, hZ, -⟩, -⟩ := hi
      exact kc_of_module (Or.inl rfl) hFc hα hq hZ hyZQ hyL hyc hodd hAZ
    | 4, hi =>
      obtain ⟨⟨n, F, _, _, α, hFc, hα, -, -, -, hZ, -⟩, -⟩ := hi
      have hyU : y ∈ Subgroup.normalizer ((⁅centerOf Q, L⁆ : Subgroup G) : Set G) :=
        mem_normalizer_commutator_of hyZQ hyL
      have hAU : ⁅W, L⁆ ≤ ⁅centerOf Q, L⁆ := by
        rw [← hAA]
        exact Subgroup.commutator_mono hAZ le_rfl
      exact kc_of_module (Or.inl rfl) hFc hα hq hZ hyU hyL hyc hodd hAU
    | 5, hi =>
      obtain ⟨⟨α, hα, hC2, hZ⟩, -⟩ := hi
      have hyC : y ∈ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hyQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hyL⟩
      exact Or.inl (kc_of_module5 hα hC2 hZ hyQ hyC hyL hyc hodd hAQ hAc)
    | n + 6, hi => exact hi.elim

  by_cases hall : ∀ y ∈ centralizerSection Yp L (pCoreOf 2 L), Odd (orderOf y) →
      ∀ a ∈ ⁅W, L⁆, y * a * y⁻¹ = a
  · left
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    have hg' : g ∈ Subgroup.centralizer ({a} : Set G) := by
      refine (Subgroup.closure_le (Subgroup.centralizer ({a} : Set G))).mpr ?_ hg
      rintro y ⟨hyX, hyodd⟩
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 := hall y hyX hyodd z ha
      calc z * y = (y * z * y⁻¹) * y := by rw [h1]
        _ = y * z := by group
    exact (Subgroup.mem_centralizer_iff.mp hg' a (Set.mem_singleton a)).symm
  · right
    push Not at hall
    obtain ⟨y, hyX, hyodd, a₀, ha₀, ha₀ne⟩ := hall
    refine ⟨y, mem_oTwoUpper_of_odd hyX hyodd, ?_⟩
    rcases KC y hyX hyodd with h | h
    · exact absurd (h a₀ ha₀) ha₀ne
    · exact h

end Main

end SBd5

end CFSG.Quasithin
