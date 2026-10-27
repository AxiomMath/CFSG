module

public import CFSG.HardMathSupport.Lang.AnisoE8.D8Psi

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem exists_e8D8_family (K : Type) [Field K] [Finite K] : E8D8Family K := by
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n := weylWordElt .E8 K e8D8Word with hn
  let ρ : Fin 8 → SL(2, K) →* adjointGroup .E8 K := fun k =>
    if k = 0 then (MulAut.conj n).toMonoidHom.comp (ρF (e8Node 6)) else ρF (e8D8Node k)
  have hρ0 : ρ 0 = (MulAut.conj n).toMonoidHom.comp (ρF (e8Node 6)) := by simp [ρ]
  have hρk : ∀ k, k ≠ 0 → ρ k = ρF (e8D8Node k) := fun k hk => by simp [ρ, hk]
  have hU0 : e8D8Chain K 0 =
      (e8Datum K).rootGroup e8D8Root ⊔ (e8Datum K).rootGroup (-e8D8Root) := by
    simp [e8D8Chain]
  have hUk : ∀ k, k ≠ 0 → e8D8Chain K k = rankOne (e8Datum K).rootGroup (e8D8Node k) :=
    fun k hk => by simp [e8D8Chain, hk]
  have hr0 : (ρ 0).range = e8D8Chain K 0 := by
    rw [hρ0, hU0, MonoidHom.range_comp, hρFr]
    change ((e8Datum K).rootGroup (Pi.single (e8Node 6) 1) ⊔
      (e8Datum K).rootGroup (-Pi.single (e8Node 6) 1)).map _ = _
    rw [map_conj_weylWordElt_rootPair e8D8Word (isRoot_single _ _), wordReflect_e8D8Word]
  have hρ' : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = e8D8Chain K k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      refine ⟨?_, hr0⟩
      rw [hρ0]
      exact (MulAut.conj n).injective.comp (hρFi _)
    · rw [hρk k hk, hUk k hk]
      exact ⟨hρFi _, hρFr _⟩
  have h0 : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → Commutes (e8D8Chain K 0) (e8D8Chain K j) := by
    intro j hj0 hj1
    rw [hU0, hUk j hj0]
    obtain ⟨h1, h2, h3, h4, h5⟩ := e8D8_root_orth j hj0 hj1
    exact commutes_rootPair_of_noG2 noG2_E8 isRoot_e8D8Root (isRoot_single _ _) h1 h2 h3 h4 h5
  have hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeD 8 i j → ¬ edgeD 8 j i →
      ∀ u ∈ e8D8Chain K i, ∀ v ∈ e8D8Chain K j, u * v = v * u := by
    intro i j hij h1 h2 u hu v hv
    by_cases hi : i = 0
    · subst hi
      exact h0 j (fun h => hij h.symm) (e8D8_ne_one_of_nadj j h1) u hu v hv
    · by_cases hj : j = 0
      · subst hj
        exact (h0 i hi (e8D8_ne_one_of_nadj i h2) v hv u hu).symm
      · rw [hUk i hi] at hu
        rw [hUk j hj] at hv
        obtain ⟨hne, hc1, hc2⟩ := e8D8_nadj i j hij h1 h2 hi hj
        exact commutes_rankOne_of_cartan_eq_zero hE rfl hne hc1 hc2 u hu v hv
  have hψ : ∀ i j : Fin 8, edgeD 8 i j → ∃ ψ : SL(3, K) →* adjointGroup .E8 K,
      ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j := by
    intro i j hij
    have hj0 : j ≠ 0 := fun h => e8D8_not_edge_to_zero i (h ▸ hij)
    by_cases hi : i = 0
    · subst hi
      obtain rfl := e8D8_edge_zero j hij
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (k := e8Node 5) e8Node_six_ne_seven
        e8_cartan_67 e8_cartan_76 e8_sl3_witness_67
      obtain ⟨h0', h1'⟩ := sl3_comp_blk hv (hρFv (e8Node 6)) (hρFv (e8Node 7))
      refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
      · rw [hρ0, MonoidHom.comp_assoc, h0']
      · rw [hρk 1 (by decide), MonoidHom.comp_assoc, h1']
        refine MonoidHom.ext fun A => ?_
        have hA : ρF (e8Node 7) A ∈ rankOne (e8Datum K).rootGroup (e8Node 7) := by
          rw [← hρFr]
          exact ⟨A, rfl⟩
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          (commute_weylWordElt hE e8D8Word e8D8Word_orth hA).eq, mul_inv_cancel_right]
        rfl
    · obtain ⟨hne, hc1, hc2, l, hl⟩ := e8D8_adj i j hij hi
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl hne hc1 hc2 hl
      rw [hρk i hi, hρk j hj0]
      exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩
  exact ⟨ρ, hρ', hcomm, hψ⟩

end CFSG.HardMathSupport.Lang.AnisoE8
