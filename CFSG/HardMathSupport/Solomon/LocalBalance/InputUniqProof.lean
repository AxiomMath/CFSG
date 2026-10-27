module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Sylow

variable {G : Type} [Group G] [Finite G]

private theorem coe_smul_sylow_eq_gLBConj {p : ℕ} (Q : Sylow p G) (g : G) :
    ((g • Q : Sylow p G) : Subgroup G) = GLBConj g⁻¹ (Q : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, GLBConj, inv_inv]
  rfl

private theorem card_gLBConj (g : G) (H : Subgroup G) : Nat.card (GLBConj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem exists_gLBConj_of_card {K A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hA : Nat.card A = 3 ^ (Nat.card K).factorization 3)
    (hB : Nat.card B = 3 ^ (Nat.card K).factorization 3) : ∃ k ∈ K, GLBConj k A = B := by
  have hA' : Nat.card (A.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hB' : Nat.card (B.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (Sylow.ofCard _ hA') (Sylow.ofCard _ hB')
  have h0 := congrArg (fun S : Sylow 3 K => (S : Subgroup K)) hk
  simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, Sylow.coe_ofCard] at h0
  have h1 : (A.subgroupOf K).map (MulAut.conj k).toMonoidHom = B.subgroupOf K := h0
  have h2 := congrArg (Subgroup.map K.subtype) h1
  have h3 : K.subtype.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (k : G)).toMonoidHom.comp K.subtype := rfl
  rw [Subgroup.map_map, h3, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hAK, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBK] at h2
  refine ⟨(k : G)⁻¹, K.inv_mem k.2, ?_⟩
  rw [← h2, GLBConj, inv_inv]

private theorem card_eq_of_le {A K : Subgroup G} (hAK : A ≤ K)
    (hA : Nat.card A = 3 ^ (Nat.card G).factorization 3) :
    Nat.card A = 3 ^ (Nat.card K).factorization 3 := by
  let S : Sylow 3 G := Sylow.ofCard A hA
  obtain ⟨Q, hAQ, -, hQ, hQcard⟩ := exists_sylow_ge Nat.prime_three hAK S.isPGroup'
  have hQA : Q = A := S.3 hQ hAQ
  rwa [hQA] at hQcard

private theorem exists_mem_normalizer_not_mem {S H : Subgroup G} (hS : IsPGroup 3 S) (hHS : H ≤ S)
    (hne : H ≠ S) : ∃ x ∈ S, x ∈ Subgroup.normalizer (H : Set G) ∧ x ∉ H := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc : NormalizerCondition S := Group.normalizerCondition_of_isNilpotent (G := S)
  have hlt : H.subgroupOf S < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hne (le_antisymm hHS (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨x, hxN, hxnot⟩ := SetLike.exists_of_lt (hnc _ hlt)
  refine ⟨x, x.2, ?_, fun hxH => hxnot (Subgroup.mem_subgroupOf.2 hxH)⟩
  have hxsub : x ∈ (Subgroup.normalizer (H : Set G)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hHS]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

private theorem card_eq_of_normalizer_le {K R : Subgroup G} (hRK : R ≤ K) (hR : IsPGroup 3 R)
    (hcard : Nat.card R = 3 ^ (Nat.card K).factorization 3)
    (hN : Subgroup.normalizer (R : Set G) ≤ K) :
    Nat.card R = 3 ^ (Nat.card G).factorization 3 := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  by_cases hEq : R = (S : Subgroup G)
  · rw [hEq]
    exact S.card_eq_multiplicity
  · exfalso
    obtain ⟨x, hxS, hxN, hxR⟩ := exists_mem_normalizer_not_mem S.isPGroup' hRS hEq
    set R' : Subgroup G := R ⊔ Subgroup.zpowers x with hR'
    have hR'S : R' ≤ S := sup_le hRS (Subgroup.zpowers_le.2 hxS)
    have hR'K : R' ≤ K := sup_le hRK (Subgroup.zpowers_le.2 (hN hxN))
    obtain ⟨Q, hR'Q, -, -, hQcard⟩ :=
      exists_sylow_ge Nat.prime_three hR'K (S.isPGroup'.to_le hR'S)
    have hxR' : x ∈ R' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have hlt : R < R' := lt_of_le_of_ne le_sup_left fun h => hxR (h ▸ hxR')
    have h1 : Nat.card R < Nat.card R' :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hlt.le) fun heq =>
        hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le heq.ge)
    have h2 : Nat.card R' ≤ Nat.card Q := Subgroup.card_le_of_le hR'Q
    exact lt_irrefl _ (h1.trans_le (h2.trans_eq (hQcard.trans hcard.symm)))

private theorem pRank_le_pRank_sylow (P : Sylow 3 G) (K : Subgroup G) :
    CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 (P : Subgroup G) := by
  obtain ⟨E, hEK, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) K
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card hEcard).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P Q
  have h1 : CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 (Q : Subgroup G) :=
    CFSG.SectionRank.le_pRank (by norm_num) hEQ hE hEcard
  rwa [← hx, coe_smul_sylow_eq_gLBConj, pRank_gLBConj Nat.prime_three] at h1

end Sylow

section Main

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G}

private theorem normalizer_le_of_le_sylow (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M)
    {X : Subgroup G} (hXP : X ≤ P) (hX : 3 ≤ CFSG.Open.pRank 3 X) :
    Subgroup.normalizer (X : Set G) ≤ M :=
  (normalizer_le_glaWeakCore hX).trans ((glaWeakCore_mono Nat.prime_three hXP).trans hP)

private theorem normalizer_le_of_le (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M)
    (hPM : (P : Subgroup G) ≤ M) {X : Subgroup G} (hXM : X ≤ M) (hX : IsPGroup 3 X)
    (hr : 3 ≤ CFSG.Open.pRank 3 X) : Subgroup.normalizer (X : Set G) ≤ M := by
  have hPcard : Nat.card (P : Subgroup G) = 3 ^ (Nat.card M).factorization 3 :=
    card_eq_of_le hPM P.card_eq_multiplicity
  obtain ⟨Q, hXQ, hQM, -, hQcard⟩ := exists_sylow_ge Nat.prime_three hXM hX
  obtain ⟨k, hkM, hk⟩ := exists_gLBConj_of_card hPM hQM hPcard hQcard
  have hX' : GLBConj k⁻¹ X ≤ P := by
    have := gLBConj_mono k⁻¹ (hk ▸ hXQ)
    rwa [gLBConj_inv_gLBConj] at this
  have hN := normalizer_le_of_le_sylow hP hX'
    (by rw [pRank_gLBConj Nat.prime_three]; exact hr)
  have h5 := gLBConj_mono k hN
  rwa [← normalizer_gLBConj, gLBConj_gLBConj_inv,
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hkM)] at h5

private theorem normalizer_le_of_le_gLBConj (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M)
    (hPM : (P : Subgroup G) ≤ M) {g : G} {X : Subgroup G} (hXM : X ≤ GLBConj g M)
    (hX : IsPGroup 3 X) (hr : 3 ≤ CFSG.Open.pRank 3 X) :
    Subgroup.normalizer (X : Set G) ≤ GLBConj g M := by
  have hX' : GLBConj g⁻¹ X ≤ M := by
    have := gLBConj_mono g⁻¹ hXM
    rwa [gLBConj_inv_gLBConj] at this
  have hN := normalizer_le_of_le hP hPM hX' (hX.map (MulAut.conj g⁻¹⁻¹).toMonoidHom)
    (by rw [pRank_gLBConj Nat.prime_three]; exact hr)
  have h5 := gLBConj_mono g hN
  rwa [← normalizer_gLBConj, gLBConj_gLBConj_inv] at h5

theorem mem_of_weakCore_le_of_pRank_inf (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M) {g : G}
    (hr : 3 ≤ CFSG.Open.pRank 3 (M ⊓ GLBConj g M)) : g ∈ M := by
  have hP3 : 3 ≤ CFSG.Open.pRank 3 (P : Subgroup G) := hr.trans (pRank_le_pRank_sylow P _)
  have hNP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_glaWeakCore hP3).trans hP
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNP
  obtain ⟨E, hEK, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (M ⊓ GLBConj g M)
  obtain ⟨R, hER, hRK, hRp, hRcard⟩ :=
    exists_sylow_ge Nat.prime_three hEK (IsPGroup.of_card hEcard)
  have hRr : 3 ≤ CFSG.Open.pRank 3 R :=
    hr.trans (CFSG.SectionRank.le_pRank (by norm_num) hER hE hEcard)
  have hRM : R ≤ M := hRK.trans inf_le_left
  have hRMg : R ≤ GLBConj g M := hRK.trans inf_le_right
  have hRG : Nat.card R = 3 ^ (Nat.card G).factorization 3 :=
    card_eq_of_normalizer_le hRK hRp hRcard
      (le_inf (normalizer_le_of_le hP hPM hRM hRp hRr)
        (normalizer_le_of_le_gLBConj hP hPM hRMg hRp hRr))
  have hPcard : Nat.card (P : Subgroup G) = 3 ^ (Nat.card M).factorization 3 :=
    card_eq_of_le hPM P.card_eq_multiplicity
  have hRcardM : Nat.card R = 3 ^ (Nat.card M).factorization 3 := card_eq_of_le hRM hRG
  have hTM : GLBConj g⁻¹ R ≤ M := by
    have := gLBConj_mono g⁻¹ hRMg
    rwa [gLBConj_inv_gLBConj] at this
  have hTcard : Nat.card (GLBConj g⁻¹ R) = 3 ^ (Nat.card M).factorization 3 :=
    (card_gLBConj g⁻¹ R).trans hRcardM
  obtain ⟨a, haM, ha⟩ := exists_gLBConj_of_card hPM hRM hPcard hRcardM
  obtain ⟨b, hbM, hb⟩ := exists_gLBConj_of_card hPM hTM hPcard hTcard
  have hab : GLBConj b P = GLBConj (a * g⁻¹) P := by
    rw [hb, ← ha, gLBConj_gLBConj]
  have hn : a * g⁻¹ * b⁻¹ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq, ← gLBConj_gLBConj, ← hab, gLBConj_inv_gLBConj]
  have hg' : g⁻¹ ∈ M := by
    have : g⁻¹ = a⁻¹ * (a * g⁻¹ * b⁻¹) * b := by group
    rw [this]
    exact M.mul_mem (M.mul_mem (M.inv_mem haM) (hNP hn)) hbM
  simpa using M.inv_mem hg'

theorem gLBConj_eq_of_weakCore_le_of_pRank_inf (hP : GLAWeakCore 3 (P : Subgroup G) ≤ M) {g : G}
    (hr : 3 ≤ CFSG.Open.pRank 3 (M ⊓ GLBConj g M)) : GLBConj g M = M :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer (mem_of_weakCore_le_of_pRank_inf hP hr))

end Main

theorem inputUniq_holds : InputUniq := fun _ _ _ _ _ _ _ _ _ _ hP _ hr =>
  gLBConj_eq_of_weakCore_le_of_pRank_inf hP hr

end CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
