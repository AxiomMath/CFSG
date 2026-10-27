module

public import CFSG.Quasithin.Background.C1PackS15207
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem stageLemma15207_of_15203_F4 (h3 : StageLemma15203_F4) : StageLemma15207_F4 := by
  intro G _ _ T Mc M hs Y₁ hY₁
  have c3 := h3 G T Mc M hs
  have hTM : T ≤ M := hs.mf.1.1.2
  have hYM : yOf152 T Mc M ≤ M := yOf152_le_M hs
  have hle : Y₁ ⊔ T ≤ yOf152 T Mc M ⊔ T := sup_le_sup_right hY₁.le T
  have hunique : IsUniqueM (yOf152 T Mc M ⊔ T) M := by
    refine ⟨⟨hY₁.unique.1.1, sup_le hYM hTM⟩, fun M' hM' => ?_⟩
    exact hY₁.unique.2 M' ⟨hM'.1, hle.trans hM'.2⟩
  have hSyl : IsSylowTwoOf T M := isSylowTwoOf_of_le151 hs.qtfe.sylow hTM
  have hPT : pCoreOf 2 M ≤ T := pCoreOf_le_of_isSylowTwoOf hSyl
  have hP2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hPM : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := le_normalizer_pCoreOf 2 M

  have hcomm : ∀ y ∈ yOf152 T Mc M, ∀ x ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G),
      y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 M := fun y hy x hx =>
    c3.centralizes (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_right hy) hx)
  have hAct : ∀ X : Subgroup G, X = oTwoUpper X →
      X ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) →
      T ≤ Subgroup.normalizer (X : Set G) → yOf152 T Mc M ≤ Subgroup.normalizer (X : Set G) :=
    fun X hXO hXC hTN =>
      C1Pack152.normalizes_of_commutator_le hP2 (hPT.trans hTN) (hYM.trans hPM) hXO
        (fun y hy x hx => hcomm y hy x (hXC hx))
  refine ⟨hunique, ?_, ?_⟩
  · intro X hX1 hXO hXC hTN
    have hYN := hAct X hXO hXC hTN

    have hXM : X ≤ M := hXC.trans inf_le_left
    have hK : X ⊔ T ≤ M := sup_le hXM hTM
    have hcharM : CharTwo M := by
      obtain ⟨S, hS⟩ := hs.qtfe.exists_sylow
      have hSM : (S : Subgroup G) ≤ M := hS ▸ hTM
      exact hs.qtfe.qtke.2.1 M hs.mf.1.1.1.1 ⟨S, hSM⟩
    have hCT : CharTwo (X ⊔ T) :=
      C1Pack152.charTwo_of_le hcharM hK (hPT.trans le_sup_right)
    have hXn : X ⊔ T ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hTN
    have hne : pCoreOf 2 X ≠ ⊥ :=
      C1Pack153.pCoreOf_ne_bot_of_normal hCT le_sup_left hXn hX1 hXO.symm
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 X : Set G)) :=
      ⟨pCoreOf 2 X, hne, pCoreOf_isPGroup 2 X, rfl⟩
    obtain ⟨M', hM'max, hM'le⟩ := exists_maxTwoLocal_ge hloc
    have hNle : Subgroup.normalizer (X : Set G) ≤ M' :=
      (normalizer_le_normalizer_pCoreOf (r := 2) X).trans hM'le
    have hM'eq : M' = M :=
      hunique.2 M' ⟨hM'max, sup_le (hYN.trans hNle) (hTN.trans hNle)⟩
    rw [← hM'eq]
    exact hNle
  · intro X _ hXO hXC hTN _
    refine C1Pack152.normalizes_of_commutator_le hP2 (hPT.trans hY₁.normalized)
      (hXC.trans inf_le_left |>.trans hPM) hY₁.eq_oTwo (fun x hx y hy => ?_)
    have h1 := hcomm y (hY₁.le hy) x (hXC hx)
    have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 M).inv_mem h1

end CFSG.Quasithin
