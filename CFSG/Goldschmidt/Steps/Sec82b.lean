module

public import CFSG.Goldschmidt.Steps.Sec82a
import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec8Bender
import CFSG.Goldschmidt.Steps.Sec81c
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Goldschmidt.Steps.AxB
import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.Walter.Bender1970.S4.Types
import CFSG.Walter.Bender1970.S38.JR

public section

namespace CFSG.Goldschmidt.Sec82

open CFSG.Open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G} {a : G}
  {H : Subgroup G} {p : ℕ} {M L : Subgroup G}

theorem componentLayerOf_eq_bot (h37 : S_G37) (c : Ctx S A a H p M L) :
    componentLayerOf H = ⊥ := by
  set E := componentLayerOf H with hEdef
  have hEH : E ≤ H := (componentLayerOf_isNormalIn H).1
  have hHE : H ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_of_isNormalIn (componentLayerOf_isNormalIn H)
  have hEM : E ≤ M := (Walter.componentLayerOf_le_centralizer_fitting H).trans
    ((Subgroup.centralizer_le (inf_le_left.trans (qCoreOf_le_fittingSubgroupOf H p c.hp))).trans
      c.hCPM)
  set M₁ := E ⊔ L with hM₁
  have hM₁M : M₁ ≤ M := sup_le hEM c.hLM
  have hM₁top : M₁ ≠ ⊤ := fun h => c.hM.1 (top_le_iff.mp (h ▸ hM₁M))
  have hS₁ := Sec8.sstar_of_le c.hset hM₁top (c.hAL.trans le_sup_right)
  have hLM₁ : GorensteinWalter.IsComponentOf L M₁ :=
    ⟨le_sup_right, Walter.isSubnormal_subgroupOf_of_le le_sup_right hM₁M c.hL.2.1, c.hL.2.2⟩
  have hOH : oddCoreOf M₁ ≤ H :=
    (Subgroup.le_centralizer_iff.mp (G73.le_centralizer_oddCoreOf hLM₁)).trans
      ((Subgroup.centralizer_le c.hAL).trans c.hCH)
  have hXn : M₁ ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    fun y hy => hHE (c.hHa ▸ hy.2)
  obtain ⟨-, h2, -, -⟩ := h37 G M₁ A hS₁ c.hset.elem a c.ha c.ha1 E le_sup_left hXn
    (G73.componentLayerOf_eq_sup H)
  have hKL : ∀ K : Subgroup G, GorensteinWalter.IsComponentOf K E →
      K ≤ Subgroup.centralizer (L : Set G) := by
    intro K hK
    have hYE : E ⊔ oddCoreOf M₁ ≤ Subgroup.normalizer (E : Set G) :=
      sup_le Subgroup.le_normalizer (hOH.trans hHE)
    have hKY : GorensteinWalter.IsComponentOf K (E ⊔ oddCoreOf M₁) :=
      Walter.isComponentOf_of_isSubnormal le_sup_left
        (Walter.isSubnormal_subgroupOf_of_le_normalizer le_sup_left hYE) hK
    have hYO : E ⊔ oddCoreOf M₁ ≤ Subgroup.normalizer (oddCoreOf M₁ : Set G) :=
      sup_le (le_sup_left.trans (Sec8.le_normalizer_oddCoreOf M₁)) Subgroup.le_normalizer
    have hKO : K ≤ Subgroup.centralizer (oddCoreOf M₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Walter.isComponentOf_commutator_eq_bot_of_isSolvable hKY (G73.isSolvable_oddCoreOf M₁)
          le_sup_right hYO)
    obtain ⟨L', hL', hKL', hor⟩ := h2 K hK hKO
    rcases Walter.isComponentOf_eq_or_commutator_eq_bot hL' hLM₁ with heq | hcomm
    · exfalso
      subst heq
      rcases hor with hKeq | ⟨-, -, hJR, -⟩
      · exact c.hLH (hKeq ▸ hK.1.trans hEH)
      · exact Walter.not_isTypeL2Odd_of_isTypeJR hJR c.hL2
    · exact hKL'.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hEE : componentLayerOf E = E := G73.componentLayerOf_componentLayerOf H
  have hEL : E ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hEE]
    exact sSup_le hKL
  have hLN : L ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.le_centralizer_iff.mp hEL).trans (Subgroup.centralizer_le_normalizer _)
  have hlt : H < Subgroup.normalizer (E : Set G) :=
    lt_of_le_of_ne hHE fun h => c.hLH (h ▸ hLN)
  have hNE : Subgroup.normalizer (E : Set G) = ⊤ := c.hHco.2 _ hlt
  have hEn : E.Normal := Subgroup.normalizer_eq_top_iff.mp hNE
  have := c.hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E with h | h
  · exact h
  · exact absurd (top_le_iff.mp (h ▸ hEH)) c.hHco.1

theorem le_centralizer_qCoreOf_of_perfect {K H P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hK : Group.IsPerfect K) (hKH : K ≤ H) (hPO : P ≤ qCoreOf H p)
    (hKP : K ≤ Subgroup.centralizer (P : Set G))
    (hKC : K ≤ Subgroup.centralizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G)) :
    K ≤ Subgroup.centralizer (qCoreOf H p : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hKres : pResidualOf K p = K :=
    le_antisymm (pResidualOf_le K p) (perfect_le_pResidualOf_local K K p hp le_rfl hK)
  have hHO := le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  refine centralizes_of_pResidualOf_eq_self_of_coprime_subgroups K (qCoreOf H p) p hp hKres
    (hKH.trans hHO) fun Q hQ => ?_
  set R := Q.map K.subtype with hR
  have hRK : R ≤ K := Subgroup.map_subtype_le Q
  have hRcop : Nat.Coprime (Nat.card R) p := by
    rw [hR, Subgroup.card_map_of_injective K.subtype_injective]
    exact hQ.symm
  have hPp : IsPGroup p P := (qCoreOf_isPGroup H p).to_le hPO
  have hRP : ⁅R, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hRK.trans hKP)
  have hfix : qCoreOf H p ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mp (hRK.trans hKC)
  have h := N10 G (qCoreOf H p) R P (qCoreOf_isPGroup H p) hRcop hPp
    ((hRK.trans hKH).trans hHO) (hPO.trans Subgroup.le_normalizer) hRP hfix
  exact Subgroup.le_centralizer_iff.mp h

theorem eq_of_isComponentOf (hE : componentLayerOf H = ⊥) (c : Ctx S A a H p M L)
    {K : Subgroup G} (hK : GorensteinWalter.IsComponentOf K M) : K = L := by
  rcases Walter.isComponentOf_eq_or_commutator_eq_bot hK c.hL with h | hKL
  · exact h
  exfalso
  have hKC : K ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKL
  have hKH : K ≤ H := hKC.trans ((Subgroup.centralizer_le c.hAL).trans c.hCH)
  set N := CFSG.fittingSubgroupOf H ⊓ M with hN
  have hFn : H ≤ Subgroup.normalizer (CFSG.fittingSubgroupOf H : Set G) :=
    le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn H)
  have hKN : K ⊔ N ≤ Subgroup.normalizer (N : Set G) :=
    sup_le (fun k hk => Sec8.mem_normalizer_inf (hFn (hKH hk)) (Subgroup.le_normalizer (hK.1 hk)))
      Subgroup.le_normalizer
  have hKY : GorensteinWalter.IsComponentOf K (K ⊔ N) :=
    ⟨le_sup_left, Walter.isSubnormal_subgroupOf_of_le le_sup_left (sup_le hK.1 inf_le_right)
      hK.2.1, hK.2.2⟩
  have hFnil := Sec8.isNilpotent_fittingSubgroupOf H
  have hNsolv : Group.IsSolvable N := by
    have := Walter.isNilpotent_of_le hFnil (inf_le_left : N ≤ CFSG.fittingSubgroupOf H)
    infer_instance
  have hKCN : K ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Walter.isComponentOf_commutator_eq_bot_of_isSolvable hKY hNsolv le_sup_right hKN)
  have hPN : qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) ≤ N :=
    le_inf (inf_le_left.trans (qCoreOf_le_fittingSubgroupOf H p c.hp))
      (Subgroup.le_normalizer.trans c.hPM)
  have hCPN : qCoreOf H p ⊓ Subgroup.centralizer
      ((qCoreOf H p ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) ≤ N :=
    le_inf (inf_le_left.trans (qCoreOf_le_fittingSubgroupOf H p c.hp)) (inf_le_right.trans c.hCPM)
  have hKp : K ≤ Subgroup.centralizer (qCoreOf H p : Set G) :=
    le_centralizer_qCoreOf_of_perfect c.hp (Walter.isPerfect_of_isComponentOf hK) hKH
      inf_le_left (hKCN.trans (Subgroup.centralizer_le hPN))
      (hKCN.trans (Subgroup.centralizer_le hCPN))
  have hKF : K ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf H : Set G) := by
    rw [Subgroup.le_centralizer_iff, Sec8.fittingSubgroupOf_eq_sup H c.hp]
    refine sup_le (Subgroup.le_centralizer_iff.mp hKp) ?_
    refine iSup_le fun q => iSup_le fun hq => iSup_le fun hqp => ?_
    refine (le_inf (qCoreOf_le_fittingSubgroupOf H q hq) ?_).trans
      (Subgroup.le_centralizer_iff.mp hKCN)
    exact (qCoreOf_centralizer_of_ne H c.hp hq (Ne.symm hqp)).trans c.hCOM
  have hFstar : generalizedFittingSubgroupOf H = CFSG.fittingSubgroupOf H := by
    rw [generalizedFittingSubgroupOf, hE, sup_bot_eq]
    rfl
  have hKF' : K ≤ CFSG.fittingSubgroupOf H := fun k hk => by
    rw [← hFstar]
    exact Walter.inf_centralizer_generalizedFitting_le H ⟨hKH hk, hFstar ▸ hKF hk⟩
  have := Walter.isPerfect_of_isComponentOf hK
  have hFsolv : Group.IsSolvable (CFSG.fittingSubgroupOf H) := by
    have := hFnil
    infer_instance
  exact Walter.ne_bot_of_isComponentOf hK (Walter.eq_bot_of_isPerfect_of_le_isSolvable hKF' hFsolv)

theorem componentLayerOf_eq (hE : componentLayerOf H = ⊥) (c : Ctx S A a H p M L) :
    componentLayerOf M = L :=
  le_antisymm (sSup_le fun _ hK => (eq_of_isComponentOf hE c hK).le) (le_sSup c.hL)

end CFSG.Goldschmidt.Sec82
