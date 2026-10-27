module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalClauses
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalEmbed
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalMax
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalPerm
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSolv
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalSylow

public section

namespace CFSG.AGLEmbedding

namespace A9Local

open Equiv

@[expose] def eqPt : Fin 9 ≃ Pt := (finProdFinEquiv (m := 3) (n := 3)).symm

theorem exists_embedding_pt {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 9)) (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    ∃ φ : Y →* Perm Pt, Function.Injective φ ∧ alternatingGroup Pt ≤ φ.range := by
  obtain ⟨φ, hφ, hA⟩ := exists_embedding_alternating K e hC
  refine ⟨eqPt.permCongrHom.toMonoidHom.comp φ, eqPt.permCongrHom.injective.comp hφ, ?_⟩
  intro τ hτ
  have hσ : eqPt.permCongrHom.symm τ ∈ alternatingGroup (Fin 9) := by
    rw [Perm.mem_alternatingGroup] at hτ ⊢
    rw [← hτ]
    exact Perm.sign_permCongr eqPt.symm τ
  obtain ⟨y, hy⟩ := hA hσ
  refine ⟨y, ?_⟩
  show eqPt.permCongrHom (φ y) = τ
  rw [hy]
  exact eqPt.permCongrHom.apply_symm_apply τ

theorem a9InSitu_inf_nrm {Y : Subgroup (Perm Pt)} (hA : alternatingGroup Pt ≤ Y)
    (T : Subgroup (Perm Pt)) : A9InSitu T baseGroup (Y ⊓ nrm) := by
  have hEM : alternatingGroup Pt ⊓ nrm ≤ Y ⊓ nrm := inf_le_inf_right _ hA
  have hMN : Y ⊓ nrm ≤ nrm := inf_le_right
  exact
    { le_normalizer := hMN
      primeCore := fun W hW hN hc => eq_bot_of_coprime hEM hMN hW hN hc
      normal_dichotomy := fun W hW hN => eq_bot_or_baseGroup_le hEM hMN hW hN
      centralizer_le := inf_centralizer_le
      pcore_le := fun W hW hN hp =>
        le_baseGroup_of_isPGroup (fun Q hQ h => eq_sylowT_of_le hQ h) hEM hMN hW hN hp
      solvable := isSolvable_of_le_nrm hMN
      pRank_le := pRank_top_le_three }

end A9Local

open A9Local CFSG.Open Equiv

theorem kFactA9Local : KFactA9Local := by
  intro Y _ _ K hK e hC T B Y₀ hBT hB hBc hW hY₀
  have : K.Normal := hK
  obtain ⟨e⟩ := e
  obtain ⟨φ₁, hφ₁, hA₁⟩ := exists_embedding_pt K e hC
  have hel : IsElemAbelian 3 (B.map φ₁) := CFSG.SectionRank.isElemAbelian_map hB φ₁
  have hcard : Nat.card (B.map φ₁) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hφ₁]
    exact hBc
  obtain ⟨g, hg⟩ := exists_conj_eq_baseGroup hel hcard
  let φ : Y →* Perm Pt := (MulAut.conj g).toMonoidHom.comp φ₁
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp hφ₁
  have hBφ : B.map φ = baseGroup := by
    rw [← hg, Subgroup.map_map]
  have hAφ : alternatingGroup Pt ≤ φ.range := by
    intro τ hτ
    have hτ' : g⁻¹ * τ * g ∈ alternatingGroup Pt := by
      have := (Perm.mem_alternatingGroup (f := τ)).1 hτ
      rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, this]
      simp
    obtain ⟨y, hy⟩ := hA₁ hτ'
    refine ⟨y, ?_⟩
    show g * φ₁ y * g⁻¹ = τ
    rw [hy]
    group
  have hNB : Subgroup.normalizer (B : Set Y) ≤ Y₀ := by
    refine le_trans ?_ hW
    have h3 : 3 ≤ CFSG.Open.pRank 3 B := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hB hBc
    refine le_sSup ⟨B, hBT, h3.trans' (by norm_num), ?_, rfl⟩
    exact h3.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_left)
  have hle1 : φ.range ⊓ nrm ≤ Y₀.map φ := by
    intro x hx
    obtain ⟨hxr, hxn⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, rfl⟩ := hxr
    refine Subgroup.mem_map.2 ⟨y, hNB ?_, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    have h1 := (Subgroup.mem_set_normalizer_iff.1 hxn) (φ n)
    rw [← hBφ] at h1
    simp only [SetLike.mem_coe, Subgroup.mem_map_iff_mem hφ, ← map_inv, ← map_mul] at h1 ⊢
    exact h1
  have hY₀φ : Y₀.map φ = φ.range ⊓ nrm := by
    refine le_antisymm (le_inf (Subgroup.map_le_range φ Y₀) ?_) hle1
    rcases le_nrm_or_eq hAφ hle1 (Subgroup.map_le_range φ Y₀) with h | h
    · exact h
    · exfalso
      apply hY₀
      refine Subgroup.map_injective hφ ?_
      rw [h, ← MonoidHom.range_eq_map]
  exact A9InSitu.of_map φ hφ hBφ hY₀φ (a9InSitu_inf_nrm hAφ ⊥)

end CFSG.AGLEmbedding
