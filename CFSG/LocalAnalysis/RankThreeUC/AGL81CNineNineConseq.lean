module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111BaseIndexKappa

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def NineNineOne (M : Subgroup G) (p : ℕ) : Prop :=
  ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
    rankThreeGamma 1 p E ≤ M → E ∈ uniqueSet M

theorem NineNineOne.normalizer_le {M : Subgroup G} {p : ℕ} (hM : rankThreeIsMaxTwoLocal M)
    (h : NineNineOne M p) {E Y : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hΓ : rankThreeGamma 1 p E ≤ M) (hEY : E ≤ Y) (hYM : Y ≤ M) :
    normalizer (Y : Set G) ≤ M :=
  normalizer_le_of_mem_uniqueSet hM (mem_uniqueSet_of_le (h E hEM hE hEc hΓ) hEY hYM)

private theorem exists_conj_le_of_isSylowOf' {p : ℕ} [Fact p.Prime] {P K U : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hU : IsPGroup p U) (hUK : U ≤ K) :
    ∃ x ∈ K, U.map (MulAut.conj x).toMonoidHom ≤ P := by
  classical
  obtain ⟨S, hSP⟩ := hP
  obtain ⟨S', hS'⟩ := (hU.comap_subtype (K := K)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨((m⁻¹ : K) : G), (m⁻¹).2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h1 : (⟨t, hUK ht⟩ : K) ∈ (S' : Subgroup K) := hS' (Subgroup.mem_subgroupOf.mpr ht)
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨y, hy, hyt⟩ := h1
  have hyt' : (m : G) * (y : G) * (m : G)⁻¹ = t := by
    have := congrArg Subtype.val hyt
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hyP : (y : G) ∈ P := by
    rw [← hSP]
    exact ⟨y, hy, rfl⟩
  have : (MulAut.conj ((m⁻¹ : K) : G)).toMonoidHom t = (y : G) := by
    rw [← hyt']
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hyP

theorem QSet.exists_isElemAbelian_card_sq {M Q : Subgroup G} {p : ℕ} (hQ : Q ∈ QSet M p)
    (hp : p ∉ sigmaM G M) :
    ∃ E₀ : Subgroup G, E₀ ≤ Q ∧ IsElemAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧
      rankThreeGamma 1 p E₀ ≤ M := by
  rcases (mem_QSet_iff.mp hQ).2.2.2.2 with ⟨hσ, -⟩ | h₂
  · exact absurd hσ hp
  · exact h₂

theorem isSylowOf_of_NineNineOne {M Q H : Subgroup G} {p : ℕ} (hM : rankThreeIsMaxTwoLocal M)
    (hQ : Q ∈ QSet M p) (hQH : Q ≤ H) (hp : p ∉ sigmaM G M) (hU : NineNineOne M p)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf p P H ∧ normalizer (P : Set G) ≤ M := by
  classical
  have hpp : p.Prime := QSet.prime_of_mem hQ
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c, hE₀Γ⟩ := QSet.exists_isElemAbelian_card_sq hQ hp
  obtain ⟨x, hx, hQx⟩ := exists_conj_le_of_isSylowOf' hP (QSet.isPGroup_of_mem hQ)
    (le_inf hQH (QSet.le_of_mem hQ))
  have hxM : x ∈ M := hx.2
  have hconj : ∀ {Y : Subgroup G}, Y ≤ M → Y.map (MulAut.conj x).toMonoidHom ≤ M := by
    rintro Y hY _ ⟨y, hy, rfl⟩
    simpa using M.mul_mem (M.mul_mem hxM (hY hy)) (M.inv_mem hxM)
  have hE₁P : E₀.map (MulAut.conj x).toMonoidHom ≤ P :=
    (Subgroup.map_mono hE₀Q).trans hQx
  have hE₁M : E₀.map (MulAut.conj x).toMonoidHom ≤ M :=
    hE₁P.trans (hP.le.trans inf_le_right)
  have hE₁ab : IsElemAbelian p (E₀.map (MulAut.conj x).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hE₀ _
  have hE₁c : Nat.card (E₀.map (MulAut.conj x).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hE₀c]
  have hE₁Γ : rankThreeGamma 1 p (E₀.map (MulAut.conj x).toMonoidHom) ≤ M := by
    rw [← gamma_map_automorphism 1 p hpp.one_lt E₀ (MulAut.conj x)]
    exact hconj hE₀Γ
  have hNorm : ∀ U : Subgroup G, P ≤ U → U ≤ M → IsPGroup p U →
      normalizer (U : Set G) ≤ M := fun U hPU hUM _ =>
    hU.normalizer_le hM hE₁M hE₁ab hE₁c hE₁Γ (hE₁P.trans hPU) hUM
  have hPN : normalizer (P : Set G) ≤ M := hNorm P le_rfl (hP.le.trans inf_le_right) hP.isPGroup
  obtain ⟨T, hPT, hTH, hTM, hTp, hmax⟩ := exists_maxPSubgroup_of_normalizer_le
    (p := p) hP.isPGroup (hP.le.trans inf_le_left) (hP.le.trans inf_le_right) hNorm
  have hTP : T = P := hP.eq_of_le hPT (le_inf hTH hTM) hTp
  obtain ⟨S, hS⟩ := (hP.isPGroup.comap_subtype (K := H)).exists_le_sylow
  have hSp : IsPGroup p (S.map H.subtype) := S.isPGroup'.map H.subtype
  have hPS : P ≤ (S : Subgroup H).map H.subtype := fun t ht =>
    ⟨⟨t, hP.le.trans inf_le_left ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hSeq : (S : Subgroup H).map H.subtype = T :=
    hmax _ (Subgroup.map_subtype_le _) hSp (hTP ▸ hPS)
  exact ⟨⟨S, hSeq.trans hTP⟩, hPN⟩

namespace NineSetting

variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem isSylowOf_of_NineNineOne (h : NineSetting G M p Q H E k) (hp : p ∉ sigmaM G M)
    (hU : NineNineOne M p) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (H ⊓ M)) :
    CFSG.ABGLocalTools.IsSylowOf p P H ∧ normalizer (P : Set G) ≤ M :=
  _root_.CFSG.LocalAnalysis.RankThreeUC.AGL81C.isSylowOf_of_NineNineOne h.setting.maxLocal
    h.mem_Q h.Q_le_H hp hU hP

end NineSetting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
