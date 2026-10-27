module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalComm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryPieces
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedNorm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono)
open CFSG.Quasithin (perfectCore)
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

local instance f4PilotGraphTwistedLeviCommNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Torus

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem uPiece_paramT3 (p : h.fixedFieldˣ × h.fixedFieldˣ) (i : Fin 3) :
    Units.map (h.fixedField.subtype : h.fixedField →* F) (sp6ParamT3 _ p i) =
      sp6ParamT3 F (((Units.map (h.fixedField.subtype : h.fixedField →* F)).prodMap
        (Units.map (h.fixedField.subtype : h.fixedField →* F))) p) i := by
  obtain ⟨a, b⟩ := p
  rw [sp6ParamT3_apply]
  change _ = sp6ParamT3 F (Units.map (h.fixedField.subtype : h.fixedField →* F) a,
    Units.map (h.fixedField.subtype : h.fixedField →* F) b) i
  rw [sp6ParamT3_apply]
  fin_cases i <;> rfl

theorem uPiece_map_torus3_6 :
    ((sp6Torus3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map (gramSUToSL h _) =
      lin6Torus3 (uPieceUnits h) := by
  rw [sp6Torus3, uPiece_map_torus h (uEmbed6 h) _ (lin6Torus F) (gramSUToSL_uEmbed6_sp6Diag h)
    _ (sp6ParamT3 _) (sp6ParamT3 F) _ (uPiece_paramT3 h), lin6Torus3, uPiece_top_prod_map]

end Torus

section General

theorem rigid_of_rigid_map {M P : Type*} [Group M] [Group P] (j : M →* P)
    (hj : Function.Injective j) (hjZ : ∀ z ∈ center M, j z ∈ center P) (S : Subgroup M)
    (hrig : ∀ y : P, (∀ s ∈ S.map j, ⁅y, s⁆ ∈ center P) →
      y ∈ centralizer ((S.map j : Subgroup P) : Set P))
    (x : M) (hx : ∀ s ∈ S, ⁅x, s⁆ ∈ center M) : x ∈ centralizer (S : Set M) := by
  apply uPiece_comap_centralizer_le j hj S
  rw [mem_comap]
  apply hrig
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_commutatorElement]
  exact hjZ _ (hx s hs)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem pieceCore_eq_map_of_cover' (e : L ≃* adjointGroup .F4 K) {M : Type*} [Group M]
    [Finite M]
    {Ψ : M →* G} (hr : Ψ.range = neighbourCore e .X) (hk : Ψ.ker ≤ center M)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ AmalgamNeighbour.X.nodes) {S : Subgroup M}
    (hS : leviTorusG e J ⊓ neighbourLeviG e .X = S.map Ψ)
    (hrig : ∀ x : M, (∀ s ∈ S, ⁅x, s⁆ ∈ center M) → x ∈ centralizer (S : Set M)) :
    pieceCore e J = (perfectCore (centralizer (S : Set M))).map Ψ := by
  rw [pieceCore_eq e .X hJ]
  change perfectCore (neighbourCore e .X ⊓ centralizer (leviTorusG e J : Set G)) = _
  rw [inf_centralizer_eq_of_sup_eq (leviTorusG_sup_centralizer_eq e hJ), hS, ← hr,
    uPiece_range_inf_centralizer_map_eq Ψ hk hrig, CFSG.Quasithin.map_perfectCore]

end General

section UnitarySix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem commute_pieceCore_one_three_of_unitary6 {t : G} {f : ℕ} (hw : F4Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .unitary6) :
    ∀ g ∈ pieceCore e {1}, ∀ g' ∈ pieceCore e {3}, Commute g g' := by
  classical
  obtain ⟨F, _, _, _, h, ε, ΦX, hrX, hkX, -, hnX⟩ := exists_twParamX_normalized_X hw hf e hX
  have hF := uPiece_four_le_card h hf
  have hq := uPiece_four_le_pow hf
  obtain ⟨a₀, ha₀, hsq⟩ := uPiece_exists_mem_units h hf
  set Θ := twParamEquiv h with hΘ
  set Ψ : uGroup6 h →* G := ΦX.comp Θ.toMonoidHom with hΨ
  have hr : Ψ.range = neighbourCore e .X := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Θ.surjective,
      ← MonoidHom.range_eq_map, hrX]
  have hk : Ψ.ker ≤ center (uGroup6 h) := by
    intro x hx
    have h1 : Θ x ∈ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) := hkX hx
    rw [← Subgroup.map_center_eq Θ.symm]
    exact ⟨Θ x, h1, Θ.symm_apply_apply x⟩
  have hn : Ψ.comp (uEmbed6 h) = levi6Hom e ε := MonoidHom.ext fun s => hnX s
  have h1 : leviTorusG e {1} ⊓ neighbourLeviG e .X =
      ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Ψ := by
    rw [← map_levi6Hom_sp6TorusM2 e ε, ← hn, ← Subgroup.map_map]
  have h3 : leviTorusG e {3} ⊓ neighbourLeviG e .X =
      ((sp6Torus3 (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Ψ := by
    rw [← map_levi6Hom_sp6Torus3 e ε, ← hn, ← Subgroup.map_map]
  have hC := isPermGram_graphGram6 F
  have hnq : ¬(6 = 3 ∧ 2 ^ f = 2) := by omega
  have hjZ : ∀ z ∈ center (uGroup6 h),
      gramSUToSL h _ z ∈ center (SpecialLinearGroup (Fin 6) F) :=
    fun z hz => gramSUToSL_mem_center h (isPrimeFormGram_graphGram6 F) (by norm_num) hnq hz
  have hj := gramSUToSL_injective h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hrig1 := rigid_of_rigid_map _ hj hjZ ((sp6TorusM2 (⊤ : Subgroup h.fixedFieldˣ)).map
    (uEmbed6 h)) (by rw [uPiece_map_torusM2_6 h]; exact rigid_lin6 (.inr (.inl rfl)) ha₀ hsq)
  have hrig3 := rigid_of_rigid_map _ hj hjZ ((sp6Torus3 (⊤ : Subgroup h.fixedFieldˣ)).map
    (uEmbed6 h)) (by rw [uPiece_map_torus3_6 h]; exact rigid_lin6Torus3 ha₀ hsq)
  have hM1 := pieceCore_eq_map_of_cover' e hr hk (by decide) h1 hrig1
  have hM3 := pieceCore_eq_map_of_cover' e hr hk (by decide) h3 hrig3
  have hperf1 := (hC.natCard_and_commutator_range_inf_blockSpecialLinear h (I := lin6BlockM2)
    (by decide) (by decide) ⟨fun _ => hq, fun _ => by omega⟩).2
  have hE : ∀ i, i ∈ ({3, 4} : Finset (Fin 6)) ↔ uPiecePerm6 i ∈ ({0, 1} : Finset (Fin 6)) := by
    decide
  have hE' : ∀ i, i ∈ ({0, 1} : Finset (Fin 6)) ↔ uPiecePerm6 i ∈ ({3, 4} : Finset (Fin 6)) := by
    decide
  have hd : Disjoint ({0, 1} : Finset (Fin 6)) {3, 4} := by decide
  have hperfE := CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
    (I := ({0, 1} : Finset (Fin 6))) (by decide) hF
  have hperf3 := commutator_range_inf_sup h hC hd hE hE' hperfE
  set j := gramSUToSL h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hjdef
  have hcomap : ∀ B : Subgroup (SpecialLinearGroup (Fin 6) F),
      ⁅j.range ⊓ B, j.range ⊓ B⁆ = j.range ⊓ B →
        ⁅B.comap j, B.comap j⁆ = B.comap j := by
    intro B hB
    apply Subgroup.map_injective hj
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, hB]
  have hP1 := uPiece_perfectCore_centralizer_eq_comap _ hj _
    (by rw [uPiece_map_torusM2_6 h]; exact perfectCore_centralizer_lin6TorusM2 hF ha₀ hsq)
    (hcomap _ hperf1)
  have hP3 := uPiece_perfectCore_centralizer_eq_comap _ hj _
    (by rw [uPiece_map_torus3_6 h]; exact perfectCore_centralizer_lin6Torus3 hF ha₀ hsq)
    (hcomap _ hperf3)
  rw [hP1] at hM1
  rw [hP3] at hM3
  intro g hg g' hg'
  rw [hM1] at hg
  rw [hM3] at hg'
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨y, hy, rfl⟩ := hg'
  refine Commute.map ?_ Ψ
  have hc := commute_lin6BlockM2_of_mem_sup hx hy
  exact hj (by rw [map_mul, map_mul]; exact hc.eq)

theorem commute_pieceCore_zero_three_of_twistedE6RowKinds {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K)
    (hk : TwistedE6RowKinds e t f) :
    ∀ g ∈ pieceCore e {0}, ∀ g' ∈ pieceCore e {3}, Commute g g' := by
  rcases hk with ⟨hX, -⟩ | ⟨-, hY⟩
  · exact commute_of_le_map_conj (pieceCore_zero_le_map_conj e) (pieceCore_three_le_map_conj e)
      (commute_pieceCore_one_three_of_unitary6 hw hf e hX)
  · have hc : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
    have hX' : HR8Kind (e.trans (graphAutF4 K).symm) t f .X .unitary6 := (hr8Kind_Y_iff_X e).1 hY
    have h := commute_of_le_map_conj (pieceCore_zero_le_map_conj _)
      (pieceCore_three_le_map_conj _) (commute_pieceCore_one_three_of_unitary6 hw hf _ hX')
    have h0 : pieceCore (e.trans (graphAutF4 K).symm) {0} = pieceCore e {3} := by
      rw [pieceCore_trans_graphAutF4_symm]
      congr 1
    have h3 : pieceCore (e.trans (graphAutF4 K).symm) {3} = pieceCore e {0} :=
      pieceCore_three_trans_graphAutF4_symm e
    intro g hg g' hg'
    rw [← h3] at hg
    rw [← h0] at hg'
    exact (h g' hg' g hg).symm

end UnitarySix

section InputHolds

theorem twistedE6RowPieceCommInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
      (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f →
      TwistedE6RowKinds e t f → ∀ g ∈ pieceCore e {0}, ∀ g' ∈ pieceCore e {3}, Commute g g' :=
  fun _ _ _ _ _ _ _ _ _ _ _ hw hf hk => commute_pieceCore_zero_three_of_twistedE6RowKinds hw hf _ hk

end InputHolds

end CFSG.SeitzReduction.F4Pilot
