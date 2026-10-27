module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar3
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def c25GammaCl {Y : Type} [Group Y] [Finite Y] (A : Subgroup (MulAut Y)) : Subgroup Y :=
  ⨆ (S : Subgroup (MulAut Y)) (_ : S ≤ A ∧ Nat.card A ≤ 3 * Nat.card S),
    GLAPPrimeCoreOf 3 (c25Fix S) ⊔ GLAPLayer 3 (c25Fix S)

structure Input23_20Facts : Prop where
  l34 : ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeFour Y → ∀ A : Subgroup (MulAut Y),
    IsElemAbelian 3 A → Nat.card A = 9 → ¬ A ≤ innerAut Y → ⊤ ≤ c25GammaCl A
  sl34 : ∀ (Y : Type) [Group Y] [Finite Y], IsSLThreeFour Y → ∀ A : Subgroup (MulAut Y),
    IsElemAbelian 3 A → Nat.card A = 9 → ¬ A ≤ innerAut Y → ⊤ ≤ c25GammaCl A

variable {G : Type} [Group G] [Finite G]

theorem input23_20_of_facts (F : Input23_20Facts) : Input23_20 := by
  intro G _ _ X K B hK hKbar hBX hBel hBN
  have hqs := isQuasisimple_quotient_of_glaPComponent Nat.prime_three hK
  set A := c25Img K B with hA
  have hAel : IsElemAbelian 3 A := c25Img_isElemAbelian hBel
  have hcard : Nat.card A = (dQ K).relIndex B := card_c25Img hBN
  obtain ⟨k, hk⟩ := (c25_isPGroup_of_elemAbelian hAel).exists_card_eq
  have hk2 : k ≤ 2 := by
    have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : A ≤ ⊤) hAel hk
    exact h1.trans (pRank_mulAut_le_two_of_L34 hKbar hqs.1)
  by_cases hk2' : k = 2
  ·
    have hA9 : Nat.card A = 9 := by rw [hk, hk2']; norm_num
    by_cases hinn : A ≤ innerAut (barOf 3 K)
    ·
      right
      refine ⟨fun b hb => ?_, by rw [← hcard, hA9]⟩
      have hbA : c25Rho hBN ⟨b, hb⟩ ∈ A := by
        rw [hA, ← c25Rho_range hBN]
        exact ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨yb, hyb⟩ := hinn hbA
      obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective yb
      refine ⟨(k₀ : G), k₀.2, fun y hy => ?_⟩
      set x : ↥K := k₀ * ⟨y, hy⟩ * k₀⁻¹ with hxdef
      set z : ↥K := K.normalizerMonoidHom (Subgroup.inclusion hBN ⟨b, hb⟩) ⟨y, hy⟩ with hz
      have hmk : (QuotientGroup.mk x : barOf 3 K) = QuotientGroup.mk z := by
        rw [hz, ← c25Rho_apply_mk hBN ⟨b, hb⟩ ⟨y, hy⟩, ← hyb, MulAut.conj_apply]
        rfl
      have h3 : x⁻¹ * z ∈ GLAPPrimeCore 3 ↥K := QuotientGroup.eq.1 hmk
      have h4 : (x : G)⁻¹ * (z : G) ∈ GLAPPrimeCoreOf 3 K := ⟨_, h3, rfl⟩
      have h5 := conj_mem_glaPPrimeCoreOf (A := K) (a := (x : G)) x.2 h4
      have hzG : (z : G) = b * y * b⁻¹ := rfl
      have hxG : (x : G) = (k₀ : G) * y * (k₀ : G)⁻¹ := rfl
      have : b * y * b⁻¹ * ((k₀ : G) * y * (k₀ : G)⁻¹)⁻¹ =
          (x : G) * ((x : G)⁻¹ * (z : G)) * (x : G)⁻¹ := by
        rw [hzG, hxG]
        group
      rw [this]
      exact h5
    ·
      left
      have hfact : ⊤ ≤ c25GammaCl A :=
        hKbar.elim (fun h => F.l34 _ h A hAel hA9 hinn) (fun h => F.sl34 _ h A hAel hA9 hinn)
      exact c25_transfer hBel hBN (fun X => GLAPPrimeCoreOf 3 X ⊔ GLAPLayer 3 X)
        (fun X => GLAPPrimeCoreOf 3 X ⊔ GLAPLayer 3 X)
        (fun X => sup_le (glaPPrimeCoreOf_le X) (sSup_le fun L hL => hL.1))
        (fun E _ => sup_le ((c25_core_le inf_le_left).trans (barX_mono 3 le_sup_left))
          ((c25_layer_le inf_le_left).trans (barX_mono 3 le_sup_right))) hfact
  ·
    left
    have hk1 : k ≤ 1 := by omega
    have h3 : Nat.card A ≤ 3 * Nat.card (⊥ : Subgroup (MulAut (barOf 3 K))) := by
      rw [Subgroup.card_bot, hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 * 1 := by norm_num
    obtain ⟨E, hEB, hES, hrk⟩ := c25_exists_sub hBel hBN (S := ⊥) bot_le h3
    have hEN : E ≤ Subgroup.normalizer (K : Set G) := hEB.trans hBN
    have hE3 : IsPGroup 3 ↥E := c25_isPGroup_of_elemAbelian (c25_isElemAbelian_mono hEB hBel)
    have hEd : E ≤ dQ K := by
      intro e he
      refine (LocalBalance.Lemma54Ns.mem_centralizerQuot_iff_barAut' 3 (J := K)
        ⟨e, hEN he⟩).2 ?_
      have : barAut 3 K ⟨e, hEN he⟩ ∈ c25Img K E :=
        ⟨⟨e, hEN he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [hES, Subgroup.mem_bot] at this
      exact this
    obtain ⟨J, hJ, hKJ, -, -⟩ := coverStmt G X K E hK hE3 hEd
    have hJle : J ≤ gammaClBelow B K := by
      refine le_trans ?_ (le_iSup₂_of_le E ⟨hEB, hrk⟩ le_rfl)
      exact le_sup_of_le_right (le_sSup hJ)
    exact hKJ.trans (sup_le_sup_right hJle _)

end CFSG.HardMathSupport.Solomon.Coordinator
