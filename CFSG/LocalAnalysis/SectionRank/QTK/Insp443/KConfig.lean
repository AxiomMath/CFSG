module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin

structure KConfig (K : Type) [Group K] (L V MK : Subgroup K) : Prop where
  ne_bot : V ≠ ⊥
  elemAbelian : IsElemAbelian 2 V
  perfect : ⁅L, L⁆ = L
  le_normalizer : L ≤ Subgroup.normalizer (V : Set K)
  le_pCoreOf : V ≤ pCoreOf 2 L
  pCoreOf_le : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set K)
  eq_commutator : V = ⁅V, L⁆
  le_MK : L ≤ MK
  MK_le_normalizer : MK ≤ Subgroup.normalizer (L : Set K)
  MK_ne_top : MK ≠ ⊤
  normalizer_le : ∀ Q : Subgroup K, Q ≠ ⊥ → IsPGroup 2 Q →
    (∀ σ : K ≃* K, V.map σ.toMonoidHom = V → L.map σ.toMonoidHom = L →
      MK.map σ.toMonoidHom = MK → Q.map σ.toMonoidHom = Q) →
    Subgroup.normalizer (Q : Set K) ≤ MK

variable {K : Type} [Group K] {L V MK : Subgroup K}

theorem KConf.kConfig [Finite K] (h : KConf K L V MK) : KConfig K L V MK where
  ne_bot := h.ne_bot
  elemAbelian := h.elemAbelian
  perfect := h.perfect
  le_normalizer := h.le_normalizer
  le_pCoreOf := h.le_pCoreOf
  pCoreOf_le := h.pCoreOf_le
  eq_commutator := h.eq_commutator
  le_MK := h.le_MK
  MK_le_normalizer := h.MK_le_normalizer
  MK_ne_top := h.MK_ne_top
  normalizer_le := h.normalizer_le

theorem KConfig.normalizer_le_MK (h : KConfig K L V MK) :
    Subgroup.normalizer (V : Set K) ≤ MK :=
  h.normalizer_le V h.ne_bot h.elemAbelian.isPGroup fun _ hV _ _ => hV

@[expose] def ForKbar (P : (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (L V MK : Subgroup K),
    KConfig K L V MK → P K → ConclK K L V MK

theorem ForKbar.mono {P Q : (S : Type) → [Group S] → Prop}
    (h : ∀ (S : Type) [Group S], P S → Q S) (hQ : ForKbar Q) : ForKbar P :=
  fun K _ _ L V MK hK hP => hQ K L V MK hK (h _ hP)

end CFSG.SectionRank.QTK.Insp443
