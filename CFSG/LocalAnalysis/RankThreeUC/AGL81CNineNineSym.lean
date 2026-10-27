module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem map_conj_mul_eq (X : Subgroup G) (a b : G) :
    X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_inv_map (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [h, Subgroup.map_id]

private theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {P K U : Subgroup G}
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

theorem exists_symmetric_conj_of_not_mem_uniqueSet {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hEM : E ≤ M)
    (hE : IsPGroup p E) (hU : E ∉ uniqueSet M) :
    ∃ (g : G) (Q : Subgroup G), M.map (MulAut.conj g).toMonoidHom ≠ M ∧ IsPGroup p Q ∧
      E ≤ Q ∧ E.map (MulAut.conj g).toMonoidHom ≤ Q ∧ Q ≤ M ∧
      Q ≤ M.map (MulAut.conj g).toMonoidHom := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hex : ∃ g : G, E ≤ M.map (MulAut.conj g).toMonoidHom ∧
      M.map (MulAut.conj g).toMonoidHom ≠ M := by
    by_contra h
    exact hU ⟨hEM, fun g hg => by
      by_contra hne
      exact h ⟨g, hg, hne⟩⟩
  obtain ⟨g₀, hEg₀, hne₀⟩ := hex
  let H₀ : Subgroup G := M.map (MulAut.conj g₀).toMonoidHom
  have hEH₀ : E ≤ H₀ := hEg₀
  have hEg₀H₀ : E.map (MulAut.conj g₀).toMonoidHom ≤ H₀ := Subgroup.map_mono hEM
  let K : Subgroup G := H₀ ⊓ M
  have hEK : E ≤ K := le_inf hEH₀ hEM
  obtain ⟨S, hES⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  let Q : Subgroup G := (S : Subgroup K).map K.subtype
  have hQK : Q ≤ K := Subgroup.map_subtype_le (H := K) S
  have hQH₀ : Q ≤ H₀ := hQK.trans inf_le_left
  have hQM : Q ≤ M := hQK.trans inf_le_right
  have hQp : IsPGroup p Q := S.isPGroup'.map _
  have hEQ : E ≤ Q := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEK]
    exact Subgroup.map_mono hES
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q K := ⟨S, rfl⟩
  by_cases hQH₀syl : CFSG.ABGLocalTools.IsSylowOf p Q H₀
  · obtain ⟨h, hhH₀, hhQ⟩ :=
      exists_conj_le_of_isSylowOf hQH₀syl
        (hE.map (MulAut.conj g₀).toMonoidHom) hEg₀H₀
    have hMg : M.map (MulAut.conj (h * g₀)).toMonoidHom = H₀ := by
      rw [map_conj_mul_eq M h g₀]
      exact mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hhH₀)
    have hEconj : E.map (MulAut.conj (h * g₀)).toMonoidHom
        = (E.map (MulAut.conj g₀).toMonoidHom).map (MulAut.conj h).toMonoidHom :=
      map_conj_mul_eq E h g₀
    refine ⟨h * g₀, Q, ?_, hQp, hEQ, ?_, hQM, ?_⟩
    · rw [hMg]
      exact hne₀
    · rw [hEconj]
      exact hhQ
    · rw [hMg]
      exact hQH₀
  · have hclaim : ¬ H₀ ⊓ normalizer (Q : Set G) ≤ M := by
      intro hle
      obtain ⟨S', hQS'⟩ := (hQp.comap_subtype (K := H₀)).exists_le_sylow
      let T : Subgroup G := (S' : Subgroup H₀).map H₀.subtype
      have hQT : Q ≤ T := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hQH₀]
        exact Subgroup.map_mono hQS'
      have hTsyl : CFSG.ABGLocalTools.IsSylowOf p T H₀ := ⟨S', rfl⟩
      have hTH₀ : T ≤ H₀ := hTsyl.le
      by_cases hTQ : T = Q
      · exact hQH₀syl (hTQ ▸ hTsyl)
      · have hlt : Q < T := lt_of_le_of_ne hQT (fun h => hTQ h.symm)
        have hgrow :=
          pGroup_proper_subgroup_lt_internal_normalizer p hp T Q hTsyl.isPGroup hlt
        have hsub : T ⊓ normalizer (Q : Set G) ≤ H₀ ⊓ normalizer (Q : Set G) :=
          le_inf (inf_le_left.trans hTH₀) inf_le_right
        have heq : T ⊓ normalizer (Q : Set G) = Q :=
          hQsyl.eq_of_le (le_inf hQT Subgroup.le_normalizer)
            (le_inf (inf_le_left.trans hTH₀) (hsub.trans hle))
            hTsyl.isPGroup.to_inf_left
        exact hgrow.ne heq.symm
    obtain ⟨x, hxK, hxM⟩ := Set.not_subset.mp hclaim
    have hxH₀ : x ∈ H₀ := hxK.1
    have hxN : x ∈ normalizer (Q : Set G) := hxK.2
    have hQx : Q.map (MulAut.conj x).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp hxN
    refine ⟨x, Q, ?_, hQp, hEQ, ?_, hQM, ?_⟩
    · intro hMx
      refine hxM ?_
      rw [← maxTwoLocal_self_normalizing M hM]
      exact mem_normalizer_iff_map_conj_eq.mpr hMx
    · calc E.map (MulAut.conj x).toMonoidHom
          ≤ Q.map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hEQ
        _ = Q := hQx
    · calc Q = Q.map (MulAut.conj x).toMonoidHom := hQx.symm
        _ ≤ M.map (MulAut.conj x).toMonoidHom := Subgroup.map_mono hQM

theorem exists_symmetric_conj_ne_pCore {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    {p : ℕ} {E : Subgroup G} {g : G} {Q : Subgroup G}
    (hne : M.map (MulAut.conj g).toMonoidHom ≠ M) (hQ : IsPGroup p Q) (hEQ : E ≤ Q)
    (hEgQ : E.map (MulAut.conj g).toMonoidHom ≤ Q) (hQM : Q ≤ M)
    (hQMg : Q ≤ M.map (MulAut.conj g).toMonoidHom) :
    ∃ (g' : G) (Q' : Subgroup G), M.map (MulAut.conj g').toMonoidHom ≠ M ∧ IsPGroup p Q' ∧
      E ≤ Q' ∧ Q' ≤ M ∧ Q' ≤ M.map (MulAut.conj g').toMonoidHom ∧
      pCoreOf 2 (M.map (MulAut.conj g').toMonoidHom) ≠
        pCoreOf 2 (M.map (MulAut.conj g').toMonoidHom ⊓ M) := by
  classical
  have hHmax : rankThreeIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hM (MulAut.conj g)
  have hdiff : pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom) ≠ pCoreOf 2 M := by
    intro heq
    apply hne
    calc M.map (MulAut.conj g).toMonoidHom
        = Subgroup.normalizer (pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom) : Set G) :=
          maxTwoLocal_eq_normalizer_pCoreOf _ hHmax
      _ = Subgroup.normalizer (pCoreOf 2 M : Set G) := by rw [heq]
      _ = M := (maxTwoLocal_eq_normalizer_pCoreOf M hM).symm
  by_cases hcase : pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom) ≠
      pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom ⊓ M)
  · exact ⟨g, Q, hne, hQ, hEQ, hQM, hQMg, hcase⟩
  · push Not at hcase
    have hcase' : pCoreOf 2 M ≠
        pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom ⊓ M) := by
      intro heq
      exact hdiff (hcase.trans heq.symm)
    have hHeq : (M.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = M := map_conj_inv_map M g
    have hEeq : (E.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom = E := map_conj_inv_map E g
    have h_inf : (M.map (MulAut.conj g).toMonoidHom ⊓ M).map
        (MulAut.conj g⁻¹).toMonoidHom = M.map (MulAut.conj g⁻¹).toMonoidHom ⊓ M := by
      calc (M.map (MulAut.conj g).toMonoidHom ⊓ M).map (MulAut.conj g⁻¹).toMonoidHom
          = (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom ⊓
              M.map (MulAut.conj g⁻¹).toMonoidHom :=
            Subgroup.map_inf (M.map (MulAut.conj g).toMonoidHom) M
              (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
        _ = M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := by rw [hHeq]
        _ = M.map (MulAut.conj g⁻¹).toMonoidHom ⊓ M :=
            inf_comm M (M.map (MulAut.conj g⁻¹).toMonoidHom)
    have hne' : M.map (MulAut.conj g⁻¹).toMonoidHom ≠ M := by
      intro heq
      apply hne
      have h1 : (M.map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj g).toMonoidHom = M := by
        simpa using map_conj_inv_map M g⁻¹
      rw [heq] at h1
      exact h1
    have hcore' : pCoreOf 2 (M.map (MulAut.conj g⁻¹).toMonoidHom) =
        (pCoreOf 2 M).map (MulAut.conj g⁻¹).toMonoidHom :=
      CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2) (MulAut.conj g⁻¹) M
    have hcoreInf : pCoreOf 2 (M.map (MulAut.conj g⁻¹).toMonoidHom ⊓ M) =
        (pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom ⊓ M)).map
          (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← h_inf]
      exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2) (MulAut.conj g⁻¹) _
    refine ⟨g⁻¹, Q.map (MulAut.conj g⁻¹).toMonoidHom, hne', hQ.map _, ?_, ?_, ?_, ?_⟩
    · calc E = (E.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj g⁻¹).toMonoidHom := hEeq.symm
        _ ≤ Q.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hEgQ
    · calc Q.map (MulAut.conj g⁻¹).toMonoidHom
          ≤ (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom :=
            Subgroup.map_mono hQMg
        _ = M := hHeq
    · exact Subgroup.map_mono hQM
    · intro heq
      apply hcase'
      have heq' : (pCoreOf 2 M).map (MulAut.conj g⁻¹).toMonoidHom =
          (pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom ⊓ M)).map
            (MulAut.conj g⁻¹).toMonoidHom := by
        rw [← hcore', ← hcoreInf]
        exact heq
      exact Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective heq'

theorem exists_nineSettingGen_of_not_mem_uniqueSet {M : Subgroup G}
    (hC : CStarSettingGen G M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hΓ : rankThreeGamma 1 p E ≤ M) (hU : E ∉ uniqueSet M) :
    ∃ (g : G) (Q : Subgroup G),
      NineSettingGen G M p Q (M.map (MulAut.conj g).toMonoidHom) E 2 ∧
      M.map (MulAut.conj g).toMonoidHom ∈ H2Fam M Q ∧
      pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom) ≠
        pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom ⊓ M) := by
  haveI := hC.cstar.simple
  have hM := hC.maxLocal
  have hEp : IsPGroup p E := elementary_isPGroup p E hE
  obtain ⟨g₁, Q₁, hne₁, hQp₁, hEQ₁, hEgQ₁, hQ₁M, hQ₁Mg⟩ :=
    exists_symmetric_conj_of_not_mem_uniqueSet hM hp hEM hEp hU
  obtain ⟨g, Q, hne, hQp, hEQ, hQM, hQMg, hcore⟩ :=
    exists_symmetric_conj_ne_pCore hM hne₁ hQp₁ hEQ₁ hEgQ₁ hQ₁M hQ₁Mg
  have hHmax : rankThreeIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hM (MulAut.conj g)
  have hHtwo : IsTwoLocal (M.map (MulAut.conj g).toMonoidHom) := hHmax.1
  have hHtop : M.map (MulAut.conj g).toMonoidHom ≠ ⊤ :=
    twoLocal_ne_top hC.cstar.nonab _ hHtwo
  have hHM : ¬ M.map (MulAut.conj g).toMonoidHom ≤ M := by
    intro hle
    exact hne (hHmax.2 M hM.1 hle).symm
  refine ⟨g, Q, ?_, ?_, hcore⟩
  · refine ⟨hC, mem_QSet_iff.mpr ⟨hp, hp2, hQM, hQp, Or.inr ⟨E, hEQ, hE, hEc, ?_⟩⟩,
      mem_HFam_iff.mpr ⟨hHtop, hQMg, hHM⟩, ⟨Or.inl rfl, hEQ, hE, hEc, ?_⟩⟩
    · simpa using hΓ
    · simpa using hΓ
  · exact mem_H2Fam_iff.mpr ⟨hHtop, hQMg, hHM, hC.cstar.charTwo _ hHtwo⟩

theorem exists_nineSetting_of_not_mem_uniqueSet {M : Subgroup G} (hC : CStarSetting G M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hΓ : rankThreeGamma 1 p E ≤ M) (hU : E ∉ uniqueSet M) :
    ∃ (g : G) (Q : Subgroup G),
      NineSetting G M p Q (M.map (MulAut.conj g).toMonoidHom) E 2 ∧
      M.map (MulAut.conj g).toMonoidHom ∈ H2Fam M Q ∧
      pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom) ≠
        pCoreOf 2 (M.map (MulAut.conj g).toMonoidHom ⊓ M) := by
  haveI := hC.standing.simple
  have hM := hC.maxLocal
  have hEp : IsPGroup p E := elementary_isPGroup p E hE
  obtain ⟨g₁, Q₁, hne₁, hQp₁, hEQ₁, hEgQ₁, hQ₁M, hQ₁Mg⟩ :=
    exists_symmetric_conj_of_not_mem_uniqueSet hM hp hEM hEp hU
  obtain ⟨g, Q, hne, hQp, hEQ, hQM, hQMg, hcore⟩ :=
    exists_symmetric_conj_ne_pCore hM hne₁ hQp₁ hEQ₁ hEgQ₁ hQ₁M hQ₁Mg
  have hHmax : rankThreeIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map hM (MulAut.conj g)
  have hHtwo : IsTwoLocal (M.map (MulAut.conj g).toMonoidHom) := hHmax.1
  have hHtop : M.map (MulAut.conj g).toMonoidHom ≠ ⊤ :=
    twoLocal_ne_top hC.standing.nonab _ hHtwo
  have hHM : ¬ M.map (MulAut.conj g).toMonoidHom ≤ M := by
    intro hle
    exact hne (hHmax.2 M hM.1 hle).symm
  refine ⟨g, Q, ?_, ?_, hcore⟩
  · refine ⟨hC, mem_QSet_iff.mpr ⟨hp, hp2, hQM, hQp, Or.inr ⟨E, hEQ, hE, hEc, ?_⟩⟩,
      mem_HFam_iff.mpr ⟨hHtop, hQMg, hHM⟩, ⟨Or.inl rfl, hEQ, hE, hEc, ?_⟩⟩
    · simpa using hΓ
    · simpa using hΓ
  · exact mem_H2Fam_iff.mpr ⟨hHtop, hQMg, hHM, hC.standing.charTwo _ hHtwo⟩


end CFSG.LocalAnalysis.RankThreeUC.AGL81C
