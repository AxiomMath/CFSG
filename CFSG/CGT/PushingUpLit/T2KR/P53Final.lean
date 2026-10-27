module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.CGT6.SixFiveJ
public import CFSG.CGT.PushingUpLit.NineChoiceSteps
public import CFSG.CGT.PushingUpLit.T2K.Global

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.Nine CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.Glue
open CFSG.CGT.PushingUpLit.T2K (T2Hyp)
open CFSG.Assembly (KProper InCatalog)

section Conj

variable {G : Type} [Group G]

theorem maximalTwoLocalsContaining_map_conj [Finite G] {X N : Subgroup G}
    (h : maximalTwoLocalsContaining (X : Set G) = {N}) (g : G) :
    maximalTwoLocalsContaining ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      {N.map (MulAut.conj g).toMonoidHom} := by
  have hN : N ∈ maximalTwoLocalsContaining (X : Set G) := by rw [h]; rfl
  ext N'
  constructor
  · rintro ⟨hN', hsub⟩
    have hN'' : IsMaximalTwoLocal (N'.map (MulAut.conj g⁻¹).toMonoidHom) :=
      isMaximalTwoLocal_map_conj hN' g⁻¹
    have hX'' : (X : Set G) ⊆ (N'.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) := by
      intro x hx
      refine ⟨g * x * g⁻¹, hsub ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hmem : N'.map (MulAut.conj g⁻¹).toMonoidHom ∈ maximalTwoLocalsContaining (X : Set G) :=
      ⟨hN'', hX''⟩
    rw [h, Set.mem_singleton_iff] at hmem
    have e : (N'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = N' := by
      ext x
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
        have : g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a := by group
        rw [this]
        exact ha
      · intro hx
        exact ⟨g⁻¹ * x * g, ⟨x, hx, by group⟩, by group⟩
    rw [Set.mem_singleton_iff, ← e, hmem]
  · rintro rfl
    exact ⟨isMaximalTwoLocal_map_conj hN.1 g, fun x hx =>
      Subgroup.map_mono (fun y hy => hN.2 hy) hx⟩

end Conj

variable {G : Type} [Group G] [Finite G]

theorem conclusion_of_block {L M : Subgroup G} {n : ℕ} (h : T2Hyp G L M n) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) {I H S X : Subgroup G} (hc : NineChoice M I H S)
    (hXM : ¬ X ≤ M) (hIX : I ≤ Subgroup.normalizer (X : Set G)) (hX1 : InClassX ↥X)
    (hX3 : ∃ N' : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {N'} ∧
      (X.subgroupOf N').IsSubnormal) :
    ∃ N K : Subgroup G, IsMaximalTwoLocal N ∧ N ≠ M ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ((T : Subgroup G) ⊓ N) N ∧ InClassX ↥K ∧
      (K.subgroupOf N).IsSubnormal ∧ maximalTwoLocalsContaining (K : Set G) = {N} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N', hN'u, hXsub⟩ := hX3
  have hOne : oTwoIn X ≠ ⊥ := ThreeFromEight.oTwoIn_ne_bot_of_isShortGroup hX1.1
  obtain ⟨N, hNle, hNmax⟩ := exists_isMaximalTwoLocal_ge
    (isPLocal_normalizer_of_isPGroup (isPGroup_oTwoIn X) hOne)
  have hXN : X ≤ N :=
    Subgroup.le_normalizer.trans ((normalizer_le_normalizer_oTwoIn X).trans hNle)
  have hIN : I ≤ N := hIX.trans ((normalizer_le_normalizer_oTwoIn X).trans hNle)
  have hNM : ¬ N ≤ M := fun hle => hXM (hXN.trans hle)
  have hNN' : N = N' := by
    have : N ∈ maximalTwoLocalsContaining (X : Set G) := ⟨hNmax, fun x hx => hXN hx⟩
    rw [hN'u] at this
    exact this
  subst hNN'
  obtain ⟨P, hP, hIP⟩ := exists_isSylowOf_ge hc.isPGroup hIN
  have hNchar : IsCharacteristicP 2 ↥N := isCharacteristicP_of_isPLocal h.charTwo hNmax.1
  have hPM : P ≤ M := (hc.sylow_jIn N P hNchar hIN hNM hP hIP).2.trans hc.normalizer_le
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isPGroup T hTM hP.2.1 hPM
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  have hP' : IsSylowOf 2 (P.map (MulAut.conj m).toMonoidHom)
      (N.map (MulAut.conj m).toMonoidHom) := by
    refine ⟨Subgroup.map_mono hP.1, hP.2.1.map _, ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hP.2.2
  have hle : P.map (MulAut.conj m).toMonoidHom ≤
      (T : Subgroup G) ⊓ N.map (MulAut.conj m).toMonoidHom :=
    le_inf hm (Subgroup.map_mono hP.1)
  have hTN : (T : Subgroup G) ⊓ N.map (MulAut.conj m).toMonoidHom =
      P.map (MulAut.conj m).toMonoidHom :=
    le_antisymm (le_of_isSylowOf_of_le hP' (T.isPGroup'.to_le inf_le_left) hle inf_le_right) hle
  refine ⟨N.map (MulAut.conj m).toMonoidHom, X.map (MulAut.conj m).toMonoidHom,
    isMaximalTwoLocal_map_conj hNmax m, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    exact not_map_conj_le hNM hmM (heq ▸ le_rfl)
  · rw [hTN]
    exact CFSG.ABGLocalTools.isSylowOf_iff.2 hP'
  · have := inClassX_conjugate hX1 m⁻¹
    rwa [ThreeFromEight.conjugate_inv_eq_map] at this
  · have := CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate m⁻¹ hXsub
    rwa [ThreeFromEight.conjugate_inv_eq_map, ThreeFromEight.conjugate_inv_eq_map] at this
  · exact maximalTwoLocalsContaining_map_conj hN'u m

end CFSG.CGT.PushingUpLit.T2KR.P53
