module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Elem
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace GL83

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section PConstrained

variable {X : Type} [Group X] [Finite X] {p : ℕ}

noncomputable def quotTopEquiv (p : ℕ) (X : Type) [Group X] :
    (X ⧸ CFSG.pPrimeCore p X) ≃* (↥(⊤ : Subgroup X) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup X)) :=
  QuotientGroup.congr (CFSG.pPrimeCore p X) (GLAPPrimeCore p ↥(⊤ : Subgroup X))
    (Subgroup.topEquiv (G := X)).symm
    (glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X)).symm)

theorem layer_quotient_eq_bot_of_glaPLayer_eq_bot (hlayer : GLAPLayer p (⊤ : Subgroup X) = ⊥) :
    CFSG.layer (X ⧸ CFSG.pPrimeCore p X) = ⊥ := by
  simp only [CFSG.layer.eq_sSup]
  rw [sSup_eq_bot]
  intro Q hQ
  exfalso
  have hQ' : IsComponentOf Q ⊤ := (CFSG.isComponent_iff_open Q).1 hQ
  have hK : IsComponentOf (Q.map (quotTopEquiv p X).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (quotTopEquiv p X) Q).2 hQ'
  obtain ⟨L, hL, hbar⟩ := exists_glaPComponent_barX_eq (p := p) (⊤ : Subgroup X) hK
  have hLle : L ≤ GLAPLayer p (⊤ : Subgroup X) := le_sSup hL
  rw [hlayer, le_bot_iff] at hLle
  subst hLle
  have hbot : barX p (⊤ : Subgroup X) ⊥ = ⊥ := by
    unfold barX
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at hbar
  have hnt : Nontrivial (Q.map (quotTopEquiv p X).toMonoidHom) :=
    CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hbar.symm

theorem hasPrimeConstraint_of_glaPLayer_eq_bot (hp : p.Prime)
    (hlayer : GLAPLayer p (⊤ : Subgroup X) = ⊥) :
    CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint (G := X) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CFSG.IsCharacteristicP p (X ⧸ CFSG.pPrimeCore p X) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ p
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p)
      (layer_quotient_eq_bot_of_glaPLayer_eq_bot hlayer)
  exact ⟨CFSG.pCore p (X ⧸ CFSG.pPrimeCore p X), CFSG.pCore_normal, CFSG.pCore_isPGroup, hchar⟩

theorem glaPPrimeCoreOf_top_eq (p : ℕ) (X : Type) [Group X] :
    GLAPPrimeCoreOf p (⊤ : Subgroup X) =
      CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) p := by
  have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv (G := X))
  have hsub : (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  unfold GLAPPrimeCoreOf
  rw [hsub, h]
  rfl

end PConstrained

@[expose] def I_20_1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    GLAPLayer p (⊤ : Subgroup X) = ⊥ → ∀ B : Subgroup X, IsElemAbelian p B →
      (∀ E : Subgroup X, IsElemAbelian p E → B ≤ E → E = B) →
        (⨆ (Y : Subgroup X) (_ : Nat.Coprime p (Nat.card Y))
          (_ : B ≤ Subgroup.normalizer (Y : Set X)), Y) = GLAPPrimeCoreOf p (⊤ : Subgroup X)

theorem I_20_1_proved : I_20_1 := by
  intro X _ _ p hp hp2 hlayer B hBel hBmax
  have : Fact p.Prime := ⟨hp⟩
  have hcons := hasPrimeConstraint_of_glaPLayer_eq_bot hp hlayer
  have hcont : ∀ x ∈ Subgroup.centralizer (B : Set X), orderOf x = p → x ∈ B := by
    intro x hx hord
    have hxp : x ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
    have hc : ∀ b ∈ B, ∀ k ∈ Subgroup.zpowers x, b * k = k * b :=
      GL83.CompFam.zpowers_commute fun b hb => Subgroup.mem_centralizer_iff.1 hx b hb
    have hE := GL83.PiGen.isElemAbelian_sup hBel (GL83.PiGen.isElemAbelian_zpowers hxp) hc
    have hEB := hBmax _ hE le_sup_left
    rw [← hEB]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rw [glaPPrimeCoreOf_top_eq]
  refine le_antisymm (iSup_le fun Y => iSup_le fun hY => iSup_le fun hBY => ?_) ?_
  · exact CFSG.RankThreeCoreUniqueness.Helpers.prime_constraint_signalizer_le_primeComplementCore
      p hp hp2 hcons B Y (GL83.CompFam.isPGroup_of_elem hBel) hY hBY hcont
  · exact le_iSup_of_le _ (le_iSup_of_le
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime p)
      (le_iSup_of_le (fun b _ => by rw [Subgroup.normalizer_eq_top]; trivial) le_rfl))

end GL83
