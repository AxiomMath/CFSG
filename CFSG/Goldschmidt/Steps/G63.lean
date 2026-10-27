module

public import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.Steps.G63Key
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import CFSG.Walter.Bender1970.S3.CoreExchangeRank
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter
open scoped commutatorElement

theorem G63_of (h37 : S_G37) (h312 : S_G312) (h51 : S_G51) (h54 : S_G54) (h62 : S_G62) :
    S_G63 := by
  intro G _ _ S A hG a ha ha1 H hH p hp hp2 hyp a₁ ha₁ ha₁1 H₁ hH₁ hne hQ1
  by_contra hnot
  have hsimple := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have hU := G63.uniquenessA_of h51 hG ha ha1 hH hp hp2 hyp
  have hPnc := G63.not_isCyclic_qCoreOf h54 h62 hG ha ha1 hH hp hp2 hyp
  obtain ⟨hR₁H, hPH₁, hm₁⟩ :=
    G63.key h37 h312 h51 h62 hG ha ha1 hH hp hp2 hU hPnc ha₁ ha₁1 hH₁ hne hQ1 hnot
  set P := qCoreOf H p with hPdef
  set P₁ := qCoreOf H₁ p with hP₁def
  have hHco := isCoatom_of_mem_benderM hH
  have hH₁co := isCoatom_of_mem_benderM hH₁
  have haH : a ∈ H := mem_of_mem_benderM hH
  have haH₁ : a ∈ H₁ := G63.le_of_mem_benderM hG ha₁ hH₁ ha
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hP₁p : IsPGroup p P₁ := qCoreOf_isPGroup H₁ p
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hH₁P₁ : H₁ ≤ Subgroup.normalizer (P₁ : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H₁ p)
  have hP1 : P ≠ ⊥ := fun h => hPnc (h ▸ inferInstance)
  have hFH := G63.not_isPGroup_fstar h62 hG ha ha1 hH hp hp2 hP1
  have hNle : ∀ Y : Subgroup G, Y ≤ qCoreOf (fstarZero H) p → Y ≠ ⊥ →
      a ∈ Subgroup.normalizer (Y : Set G) → Subgroup.normalizer (Y : Set G) ≤ H :=
    fun Y hY hY1 haY => G63.normalizer_le_of_uniqueness hsimple hHco hU hFH hp hY hY1 haY
  have hP₁nc : ¬ IsCyclic P₁ := not_isCyclic_of_two_le_rank hp hP₁p
    (by rw [rank_eq_pRank_of_isPGroup hp hP₁p]; omega)
  have hQ₁cyc : IsCyclic (qCoreOf (fstarZero H₁) p ⊓ H : Subgroup G) := by
    by_contra hc
    have hQ₁1 : qCoreOf (fstarZero H₁) p ⊓ H ≠ ⊥ := fun h => hc (h ▸ inferInstance)
    have hU₁ := G63.uniquenessA_of h51 hG ha₁ ha₁1 hH₁ hp hp2 (Or.inr hm₁)
    obtain ⟨hRH₁, hP₁H, -⟩ := G63.key h37 h312 h51 h62 hG ha₁ ha₁1 hH₁ hp hp2 hU₁ hP₁nc ha ha1
      hH (Ne.symm hne) hQ₁1 fun h => hc h.2
    have h1 : generalizedFittingSubgroupOf H ≤ H₁ :=
      (generalizedFitting_le_qCoreOf_sup_pResidualOf H hp).trans (sup_le hPH₁ hRH₁)
    have h2 : generalizedFittingSubgroupOf H₁ ≤ H :=
      (generalizedFitting_le_qCoreOf_sup_pResidualOf H₁ hp).trans (sup_le hP₁H hR₁H)
    obtain ⟨r, hr, hHr, -⟩ :=
      bender1970_1_6_maximalSubgroups_pGroups hsimple H H₁ hHco hH₁co (Ne.symm hne) h1 h2
    exact hFH r hr hHr
  set 𝔓 := P ⊔ P₁ with h𝔓def
  have hPP₁N : P ≤ Subgroup.normalizer (P₁ : Set G) := hPH₁.trans hH₁P₁
  have h𝔓 : IsPGroup p 𝔓 := hPp.to_sup_of_normal_right' hP₁p hPP₁N
  obtain ⟨X, hXP₁, hXcyc, hXexp, hXN⟩ := exists_noncyclic_exponent_le hp hp2 hP₁p hP₁nc
  have hX𝔓 : X ≤ 𝔓 := hXP₁.trans le_sup_right
  have h𝔓X : 𝔓 ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (hPP₁N.trans hXN) (Subgroup.le_normalizer.trans hXN)
  have haa : a * a = 1 := by rw [← pow_two]; exact hG.elem.2 a ha
  have ha𝔓 : a ∈ Subgroup.normalizer (𝔓 : Set G) := mem_normalizer_sup (hHP haH) (hH₁P₁ haH₁)
  have haX : a ∈ Subgroup.normalizer (X : Set G) := hXN (hH₁P₁ haH₁)
  obtain ⟨z, hzX, x, hxX, hz1, hz𝔓, hxz, hx𝔓, haz, hax⟩ :=
    exists_typePP hp hp2 h𝔓 hX𝔓 h𝔓X hXexp hXcyc haa ha𝔓 haX
  set Vb := Subgroup.zpowers x ⊔ Subgroup.zpowers z with hVbdef
  have hcomm : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hz𝔓) x (hX𝔓 hxX)
  obtain ⟨hVbel, hVbcard⟩ :=
    G63.sup_zpowers_isElemAbelian hp (hXexp x hxX) (hXexp z hzX) hz1 hxz hcomm
  have hVbnc : ¬ IsCyclic Vb := G53.not_isCyclic_of_isElemAbelian hp hVbel hVbcard
  have hVbP₁ : Vb ≤ P₁ :=
    sup_le (Subgroup.zpowers_le.mpr (hXP₁ hxX)) (Subgroup.zpowers_le.mpr (hXP₁ hzX))
  have hzo : orderOf z = p := orderOf_eq_prime (hXexp z hzX) hz1
  have hzVb : z ∈ Vb := (le_sup_right : Subgroup.zpowers z ≤ Vb) (Subgroup.mem_zpowers z)
  have haVb : a ∈ Subgroup.normalizer (Vb : Set G) := by
    refine mem_normalizer_of_map_conj_le ?_
    rw [hVbdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr hax) (Subgroup.zpowers_le.mpr ?_)
    exact (le_sup_right : Subgroup.zpowers z ≤ Vb)
      ((Subgroup.mem_normalizer_iff.mp haz z).mp (Subgroup.mem_zpowers z))
  have hCVb : ∀ y ∈ 𝔓, y ∈ Subgroup.centralizer ({x} : Set G) →
      y ∈ Subgroup.centralizer (Vb : Set G) := by
    intro y hy hyx
    have h1 : Vb ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hyx).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp hz𝔓) y hy).symm
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (h1 hv)
  have hhomP₁ := card_le_and_commutator_le_of_commutator_mem hz𝔓 hx𝔓 (le_sup_right : P₁ ≤ 𝔓)
  have hP₁' : ⁅P₁, P₁⁆ ≤ Subgroup.centralizer (Vb : Set G) := fun y hy =>
    hCVb y ((le_sup_right : P₁ ≤ 𝔓) (Bender35.commutator_self_le P₁ hy)) (hhomP₁.2 hy)
  have hVbB₁ : Vb ≤ qCoreOf (fstarZero H₁) p := G63.le_qCoreOf_fstarZero H₁ hp hVbP₁ hP₁'
  have hVbH : ¬ Vb ≤ H := fun h => hVbnc (G63.isCyclic_of_le hQ₁cyc (le_inf hVbB₁ h))
  have hhomP := card_le_and_commutator_le_of_commutator_mem hz𝔓 hx𝔓 (le_sup_left : P ≤ 𝔓)
  have hP' : ⁅P, P⁆ = ⊥ := by
    by_contra hP'1
    have hP'C : ⁅P, P⁆ ≤ Subgroup.centralizer (Vb : Set G) := fun y hy =>
      hCVb y ((le_sup_left : P ≤ 𝔓) (Bender35.commutator_self_le P hy)) (hhomP.2 hy)
    have hP'n : IsNormalIn ⁅P, P⁆ H := G63.isNormalIn_of_le_normalizer
      ((Bender35.commutator_self_le P).trans (qCoreOf_normal_in H p).1)
      fun h hh => mem_normalizer_commutator (hHP hh) (hHP hh)
    have hN' : Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) = H :=
      normalizer_eq_of_nontrivial_normal_in_coatom hsimple hHco hP'n.1 hP'1
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hP'n.1).mpr
          (le_normalizer_of_isNormalIn hP'n))
    exact hVbH ((Subgroup.le_centralizer_iff.mp hP'C).trans
      ((Subgroup.centralizer_le_normalizer _).trans hN'.le))
  have hPab : P ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hP'
  have hPB : P ≤ qCoreOf (fstarZero H) p :=
    (le_inf le_rfl hPab).trans (G63.center_qCoreOf_le_qCoreOf_fstarZero H hp)
  have hCP : P ⊓ Subgroup.centralizer (Vb : Set G) = ⊥ := by
    by_contra hCP1
    have haCP : a ∈ Subgroup.normalizer
        ((P ⊓ Subgroup.centralizer (Vb : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf (hHP haH) (Bender35.mem_normalizer_centralizer haVb)
    have hN := hNle _ (inf_le_left.trans hPB) hCP1 haCP
    exact hVbH ((Subgroup.le_centralizer_iff.mp inf_le_right).trans
      ((Subgroup.centralizer_le_normalizer _).trans hN))
  have hPcard : Nat.card P ≤ p := by
    have h1 := hhomP.1
    have h2 : P ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
      le_bot_iff.mp (hCP ▸ le_inf inf_le_left fun y hy =>
        hCVb y ((le_sup_left : P ≤ 𝔓) hy.1) hy.2)
    rw [h2, Subgroup.card_bot, Nat.card_zpowers, hzo, mul_one] at h1
    exact h1
  exact hPnc (G63.isCyclic_of_card_le hp hPp hPcard)

end CFSG.Goldschmidt
