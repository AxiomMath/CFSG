module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.TL3T32
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE

namespace TwinDisc

namespace AE5

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem ker_pGroup (hS : Q8Section X Φ) (I : AEIdent Φ 5) : IsPGroup 2 I.φ.ker := by
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  let e : ↥(pSpan Φ) ≃* X := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hodd : classicalInvolutionOddCore ↥(pSpan Φ) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv e.symm hS.oddFree
  exact (Vtx.isPGroup_center_of_oddFree hodd).to_le I.ker_le

theorem members_two (hS : Q8Section X Φ) (I : AEIdent Φ 5) : ∀ L ∈ Φ, IsPGroup 2 L := by
  intro L hL x
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  set y : ↥(pSpan Φ) := ⟨(x : X), le_pSpan hL x.2⟩ with hy
  have hmem : I.φ y ∈ memBar α h b := by
    rw [← hlab]
    exact I.mem_map hL x.2
  have h8 : (⟨I.φ y, hmem⟩ : ↥(memBar α h b)) ^ 8 = 1 := by
    have := pow_card_eq_one' (G := ↥(memBar α h b)) (x := ⟨I.φ y, hmem⟩)
    rwa [natCard_memBar (le_refl 5)] at this
  have hker : y ^ 8 ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    simpa using congrArg (fun z : ↥(memBar α h b) => (z : AEQ 5)) h8
  obtain ⟨k, hk⟩ := ker_pGroup hS I ⟨y ^ 8, hker⟩
  refine ⟨k + 3, ?_⟩
  apply Subtype.ext
  have h1 := congrArg (fun z : ↥I.φ.ker => ((z : ↥(pSpan Φ)) : X)) hk
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
  have e : ((x : X)) ^ 2 ^ (k + 3) = (((y ^ 8) ^ 2 ^ k : ↥(pSpan Φ)) : X) := by
    simp only [Subgroup.coe_pow, hy]
    rw [← pow_mul]
    congr 1
    rw [pow_add]
    ring
  simpa [e] using h1

theorem q8Fam_of_aeIdent (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (I : AEIdent Φ 5) :
    ExitO2.Q8Fam X Φ := by
  have h2 := members_two hS I
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  refine ⟨hS.hyp, h2, fun J hJ => ?_, hS.aEmpty, hgen, htrans, hS.oddFree, ?_⟩
  · have hKS : IsSylow2In J J := ⟨le_rfl, h2 J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hS.q8 _ hJ _ hKS
  · intro L hL u hu
    set ψ : ↥(pSpan Φ) →* Equiv.Perm (Fin 5) := (permQ 5).comp I.φ with hψ
    have hker2 : IsPGroup 2 ψ.ker := by
      intro g
      have hg : I.φ g.1 * I.φ g.1 = 1 := by
        have h3 : permQ 5 (I.φ g.1) = 1 := MonoidHom.mem_ker.mp g.2
        exact mul_self_of_mem_ker_permQ (MonoidHom.mem_ker.mpr h3)
      have hsq : (g.1 * g.1) ∈ I.φ.ker := by
        rw [MonoidHom.mem_ker, map_mul]; exact hg
      obtain ⟨k, hk⟩ := ker_pGroup hS I ⟨g.1 * g.1, hsq⟩
      refine ⟨k + 1, ?_⟩
      apply Subtype.ext
      have h1 := congrArg (fun z : ↥I.φ.ker => ((z : ↥(pSpan Φ))) ) hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
      show (g.1 ^ 2 ^ (k + 1)) = 1
      rw [pow_succ, pow_mul', pow_two]
      exact h1
    refine ⟨ψ.ker.map (pSpan Φ).subtype, ?_, ?_, ?_⟩
    · refine Subgroup.Normal.map inferInstance _ ?_
      intro y
      exact ⟨⟨y, by rw [hgen]; trivial⟩, rfl⟩
    · exact hker2.map _
    · obtain ⟨α, h, b, hlab⟩ := I.label L hL
      have hmem : I.φ ⟨u, le_pSpan hL hu.mem⟩ ∈ memBar α h b := by
        rw [← hlab]; exact I.mem_map hL hu.mem
      have hsq : I.φ ⟨u, le_pSpan hL hu.mem⟩ * I.φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
        rw [← map_mul]
        have : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan Φ)) = 1 :=
          Subtype.ext hu.sq
        rw [this, map_one]
      refine ⟨⟨u, le_pSpan hL hu.mem⟩, ?_, rfl⟩
      refine MonoidHom.mem_ker.mpr ?_
      show permQ 5 (I.φ _) = 1
      rcases eq_of_mem_memBar_mul_self (le_refl 5) hmem hsq with h1 | h1
      · rw [h1, map_one]
      · rw [h1]
        exact zOf_perm _

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
