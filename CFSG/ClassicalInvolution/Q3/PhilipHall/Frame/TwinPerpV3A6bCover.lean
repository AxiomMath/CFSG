module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.Sec13AECoverEven
public import CFSG.ClassicalInvolution.Q3.TL3T61

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

section Twins

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem aeCoverHyp_of_twins (hn : 5 ≤ n) (hn8 : n ≠ 8) (hS : Q8Section X Φ) (I : AEIdent Φ n)
    {K K' : Subgroup X} (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {z : X}
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z) : TL4.AECoverHyp I := by
  have hk := AE5.ker_pGroupN hS I
  have h2 := AE5.members_twoN hn hS I
  have h8 := AE5.members_card8 hn hS I
  have hgenΦ : pSpan Φ = ⊤ := AE5.hgen_of hS
  have hinj : ∀ L ∈ Φ, ∀ L' ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map I.φ = (L'.subgroupOf (pSpan Φ)).map I.φ → L = L' :=
    fun L hL L' hL' h => AE5.same_of_image_n hn hS I hL hL' h
  have hconj : ∀ L ∈ Φ, ∀ x ∈ pSpan Φ, conjSub x L ∈ Φ :=
    fun L hL x _ => hS.hyp.conjInvariant x L hL
  have htrans : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ x ∈ pSpan Φ, conjSub x L = L' := by
    intro L hL L' hL'
    obtain ⟨g, hg⟩ := AE5.trans_of_aeIdent hn hS I L hL L' hL'
    exact ⟨g, by rw [hgenΦ]; exact Subgroup.mem_top g, hg⟩
  obtain ⟨δ, hδ, c, hlab⟩ := I.label K hK
  obtain ⟨γ, hγ, c', hlab'⟩ := I.label K' hK'
  have e1 := I.map_eq_zBar hn hK (h8 K hK) hlab hzK
  have e2 := I.map_eq_zBar hn hK' (h8 K' hK') hlab' hzK'
  have hγδ : γ = δ := AE.eq_of_zBar_eq hn8 (e2.symm.trans e1)
  subst hγδ
  have hc' : c' = !c := by
    by_contra hcc
    have : c' = c := by cases c <;> cases c' <;> simp_all
    subst this
    exact hne (hinj K' hK' K hK (hlab'.trans hlab.symm))
  subst hc'
  have hz₀ : ∀ u u' : X, IsUniqueInvolution K u → IsUniqueInvolution K' u' → u = u' := by
    intro u u' hu hu'
    rw [hu.eq hzK, hu'.eq hzK']
  exact
    { ker_two := hk
      card := h8
      conj_mem := hconj
      label_inj := hinj
      twin_comm := by
        intro α h L hL L' hL' hl hl'
        refine aeIdent_comm_of_map_comm hS.hyp h2 (subset_refl Φ) I hk hL hL' ?_ ?_
        · intro e
          subst e
          rw [hl] at hl'
          exact AE.memBar_true_ne_false hn α h hl'
        · rw [hl, hl']
          exact memBar_twin_comm α h true
      twin_z := I.twin_z_of_trans hn hn8 hconj hinj htrans hK hK' hlab hlab' hz₀ }

end Twins

section PCore

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)}

theorem card_even_vectors_six :
    Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0} = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_aeSub_six_perm_one :
    Nat.card {w : ↥(aeSub 6) // (w : Wr 6).perm = 1} = 32 := by
  rw [← card_even_vectors_six]
  refine Nat.card_congr
    { toFun := fun w => ⟨(w : Wr 6).vec, w.1.2.1⟩
      invFun := fun v => ⟨⟨ofVec v.1, ⟨v.2, by simp [ofVec]⟩⟩, rfl⟩
      left_inv := fun w => Subtype.ext (Subtype.ext (Wr.ext rfl w.2.symm))
      right_inv := fun v => rfl }

theorem pCore_cover_AE6 {I : AEIdent P 6} (hH : TL4.AECoverHyp I) (hker : I.φ.ker ≠ ⊥) :
    Nat.card (pCore 2 ↥(pSpan P)) = 32 ∧ (∀ a ∈ pCore 2 ↥(pSpan P), a * a = 1) ∧
      I.φ.ker ≤ pCore 2 ↥(pSpan P) ∧
      ∀ L (hL : L ∈ P) (u : G) (hu : IsUniqueInvolution L u),
        (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan P)) ∈ pCore 2 ↥(pSpan P) := by
  have hk6 : 5 ≤ 6 := by norm_num
  obtain ⟨hU1, hU2⟩ := Sec13.EvenCov.ker_permHom_elem hH hk6
  set U := (TL4.AECov.permHom I).ker with hUdef
  have hUnorm : U.Normal := MonoidHom.normal_ker _
  have hU2grp : IsPGroup 2 U := fun a => ⟨1, by
    apply Subtype.ext
    simpa [sq] using (hU1 a a.2 a a.2).2⟩
  have hpc : pCore 2 ↥(pSpan P) = U := by
    apply le_antisymm
    · exact TL4.AECov.le_ker_permHom_of_normal I hk6 (pCore_normal (p := 2) (G := ↥(pSpan P)))
        (pCore_isPGroup (p := 2) (G := ↥(pSpan P)))
    · exact le_sSup ⟨hUnorm, hU2grp⟩
  obtain ⟨-, hbot | ⟨ψ, hψ, -⟩⟩ := Sec13.aeCover_ker hH hk6
  · exact absurd hbot hker
  have hequiv : U ≃ {w : ↥(aeSub 6) // (w : Wr 6).perm = 1} :=
    Equiv.subtypeEquiv ψ.toEquiv (fun x => by
      rw [hUdef, TL4.AECov.mem_ker_permHom, ← hψ x]
      exact Iff.rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpc, Nat.card_congr hequiv]
    exact card_aeSub_six_perm_one
  · intro a ha
    rw [hpc] at ha
    exact (hU1 a ha a ha).2
  · rw [hpc]
    intro z hz
    rw [hUdef, TL4.AECov.mem_ker_permHom]
    rw [MonoidHom.mem_ker.mp hz, map_one]
  · intro L hL u hu
    rw [hpc]
    exact TL4.AECov.zSpan_le_ker_permHom I hk6 hH.card (Subgroup.subset_closure ⟨L, hL, hu⟩)

end PCore

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6b
