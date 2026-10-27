module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Phi

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

namespace TwinDisc

namespace ExitO2

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

theorem fam_false_of_ae5 (F : Q8Fam Y Δ) (I : AEIdent Δ 5) (htt : TwinTriple Δ) : False := by
  classical
  obtain ⟨K, hK, K', ⟨hK', z, hzK, hzK'⟩, hne, J, hJK, hJK'⟩ := htt
  have hm : 5 ≤ 5 := le_rfl
  have h8 : ∀ L ∈ Δ, Nat.card ↥L = 8 := fun L hL => (F.card L hL).trans (by norm_num)
  have hlab' : ∀ L ∈ Δ, ∃ (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Δ)).map I.φ = AE.memBar α h b := I.label
  have hsame : ∀ L ∈ Δ, ∀ M ∈ Δ, (L.subgroupOf (pSpan Δ)).map I.φ =
      (M.subgroupOf (pSpan Δ)).map I.φ → L = M := by
    intro L hL M hM hLM
    obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
    refine fam_eq_of_phi_mem I.φ F hm I.ker_le hlab' hL hM haL ha2 ?_
    rw [← hLM]
    exact I.mem_map hL haL
  have hinv : ∀ L ∈ Δ, ∀ u : Y, ∀ (hu : IsUniqueInvolution L u) (hL : L ∈ Δ)
      (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan Δ)).map I.φ = AE.memBar α h b →
      I.φ ⟨u, le_pSpan hL hu.mem⟩ = AE.zBar α h := by
    intro L _ u hu hL α h b hlab
    have hmem : I.φ ⟨u, le_pSpan hL hu.mem⟩ ∈ AE.memBar α h b := by
      rw [← hlab]
      exact I.mem_map hL hu.mem
    have hsq : I.φ ⟨u, le_pSpan hL hu.mem⟩ * I.φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
      rw [← map_mul]
      have : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan Δ)) = 1 :=
        Subtype.ext hu.sq
      rw [this, map_one]
    rcases AE.eq_of_mem_memBar_mul_self hm hmem hsq with h1 | h1
    · exfalso
      refine hu.ne_one (phi_injOn I.φ hm hL (h8 L hL) hlab hu.mem L.one_mem ?_)
      exact h1.trans (map_one I.φ).symm
    · exact h1
  obtain ⟨α, h, b, hl⟩ := hlab' K hK
  obtain ⟨α', h', b', hl'⟩ := hlab' K' hK'
  obtain ⟨β, hβ, c, hlJ⟩ := hlab' J hJK.1
  have hzα := hinv K hK z hzK hK α h b hl
  have hzα' := hinv K' hK' z hzK' hK' α' h' b' hl'
  obtain rfl : α = α' := AE.eq_of_zBar_eq (by norm_num) (hzα.symm.trans hzα')
  have hbb : b ≠ b' := by
    intro e
    apply hne
    refine hsame K' hK' K hK ?_
    rw [hl, hl', e]
  by_cases hβα : β = α
  · subst hβα
    have hc : c = b ∨ c = b' := by
      revert hbb
      cases b <;> cases b' <;> cases c <;> simp
    rcases hc with rfl | rfl
    · exact hJK.2.1 (hsame J hJK.1 K hK (by rw [hlJ, hl]))
    · exact hJK'.2.1 (hsame J hJK.1 K' hK' (by rw [hlJ, hl']))
  · have hJN : J ≤ Subgroup.normalizer (K : Set Y) :=
      ((TC.mem_omegaNbr_iff F.hyp F.two).mp hJK).2.2
    have hcomm : ∀ y ∈ AE.memBar β hβ c, AE.zBar α h * y = y * AE.zBar α h := by
      intro y hy
      rw [← hlJ] at hy
      obtain ⟨⟨x, hxP⟩, hxJ, rfl⟩ := hy
      have hxJ' : x ∈ J := Subgroup.mem_subgroupOf.mp hxJ
      have hxz : x * z * x⁻¹ = z :=
        hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hJN hxJ'))
      have hxz' : z * x = x * z := by
        calc z * x = (x * z * x⁻¹) * x := by rw [hxz]
          _ = x * z := by group
      rw [← hzα, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxz'
    have hd := AE.disjoint_of_zBar_comm (Ne.symm hβα) hcomm
    have hcard : (α ∪ β).card = 8 := by rw [Finset.card_union_of_disjoint hd, h, hβ]
    have hle : (α ∪ β).card ≤ 5 := by
      have := Finset.card_le_univ (α ∪ β)
      rwa [Fintype.card_fin] at this
    omega

end ExitO2

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
