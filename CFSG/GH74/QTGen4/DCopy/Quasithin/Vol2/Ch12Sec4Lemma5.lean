module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Cx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Lemma3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G]

theorem pCoreOf_sup_eq_of_hyp1223_F4 (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight) [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} (hyp : Hyp1223 G T L V) :
    pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨-, hTV, -, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
  rwa [hyp.conjClosure_eq, conjClosure_eq_of_le_normalizer hTV] at hO

theorem lemma12_4_5_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9_F4) (h51 : AsB51) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Cx1242 G T L V →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∀ E : Subgroup G, E ≤ V → Nat.card E = 4 → T ≤ Subgroup.normalizer (E : Set G) →
        ⁅quasithinOmegaOneCenter T, L⁆ = ⊥ ∧
        omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) = quasithinOmegaOneCenter T ⊔ V ∧
        ∀ A : Subgroup G, IsMaxElemAbelian (T ⊓ Subgroup.centralizer (E : Set G)) A →
          ¬ A ≤ pCoreOf 2 (L ⊔ T) → autOn A V = autOn (T ⊓ Subgroup.centralizer (E : Set G)) V := by
  intro G _ _ T L V hcx h3' E hEV hE4 _hTE
  classical
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hcx (Or.inl h3')
  have := hf.comm
  obtain ⟨hV16, hGrs, hGr, hnat⟩ := cx_l3_module_F4 h1222 hcx hf h3'
  have hQ := pCoreOf_sup_eq_of_hyp1223_F4 h1222 h3228 hyp
  obtain ⟨-, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
  have hTmem : ∀ t ∈ T, ∃ l ∈ T ⊓ L, l⁻¹ * t ∈ T ⊓ Subgroup.centralizer (V : Set G) :=
    fun t ht => cx_mem_mul_of_mem_T hf hTeq ht
  have hJ : L = ⁅L, thompsonJ T⁆ :=
    lemma12_4_3_two_of_F4 h1229 (lemma12_4_3_one_of_pre_F4 hpre) G T L V hcx
  have hZQ := zQ_le_sup h51 hcx hf h3' hV16 hGrs hGr hQ hTmem hJ
  obtain ⟨hWT, hWel, hVW, hZW⟩ := omegaOneCenter_pCore_facts hf hQ
  have hQW : pCoreOf 2 (L ⊔ T) ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) : Set G) :=
    Subgroup.le_centralizer_iff.1 ((A4.omegaOneCenterOf_le_centerOf _).trans
      (A4.centerOf_le_centralizer _))

  have hWZ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓ Subgroup.centralizer (L : Set G) ≤
      quasithinOmegaOneCenter T := by
    intro x hx
    refine Subgroup.subset_closure ⟨⟨hWT hx.1, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩,
      hWel.2 x hx.1⟩
    obtain ⟨l, hl, hly⟩ := hTmem t ht
    have hlyQ : l⁻¹ * t ∈ pCoreOf 2 (L ⊔ T) := hQ ▸ hly
    have h1 := Subgroup.mem_centralizer_iff.1 (hQW hlyQ) x hx.1
    have h2 := Subgroup.mem_centralizer_iff.1 hx.2 l hl.2
    calc t * x = l * ((l⁻¹ * t) * x) := by group
      _ = l * (x * (l⁻¹ * t)) := by rw [← h1]
      _ = (l * x) * (l⁻¹ * t) := by group
      _ = (x * l) * (l⁻¹ * t) := by rw [h2]
      _ = x * t := by group
  have hZT : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_right
  refine ⟨?_, ?_, fun A hA hAQ => lemma12_4_5_three hcx hf hV16 hGr hnat hEV hE4 hA (hQ ▸ hAQ)⟩
  ·
    have := hWel.1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    have hxW := hZQ (hZW hx)
    have hVN : V ≤ Subgroup.normalizer ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
        Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mul_comm' (⟨y, hy.1⟩ : ↥(omegaOneCenterOf (pCoreOf 2 (L ⊔ T))))
        ⟨v, hVW hv⟩)
    have hxmem : x ∈ (V : Set G) * ((omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ⊓
        Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN]
      exact hxW
    obtain ⟨v, hv, c, hc, rfl⟩ := hxmem
    have hcT : c ∈ Subgroup.centralizer (T : Set G) := hZT (hWZ hc)
    have hvT : v ∈ Subgroup.centralizer (T : Set G) := by
      have h1 := (Subgroup.centralizer (T : Set G)).mul_mem (hZT hx)
        ((Subgroup.centralizer (T : Set G)).inv_mem hcT)
      rwa [mul_inv_cancel_right] at h1
    exact Subgroup.mul_mem _ (cx_inf_centralizer_T_le hcx hf hV16 hnat ⟨hv, hvT⟩) hc.2
  ·
    refine le_antisymm (hZQ.trans ?_) (sup_le hZW hVW)
    rw [sup_comm]
    exact sup_le_sup_right hWZ V

end CFSG.Quasithin.H13
