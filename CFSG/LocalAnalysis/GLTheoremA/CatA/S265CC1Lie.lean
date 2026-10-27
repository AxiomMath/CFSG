module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest14
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264D4EightCaseB2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgE6Res2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265C.C1

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement
open scoped Pointwise

section Plain

theorem isGB_of_kd264KLie {G : Type} [Group G] [Finite G] {p : ℕ} (hKL : KD264KLie p) (hp : p.Prime)
    {B D X L : Subgroup G} (hBab : IsElemAbelian p B) (hDB : D ≤ B)
    (hDL : D ≤ Subgroup.centralizer (L : Set G)) (hD : p ^ 2 ≤ Nat.card D) (hL : GLAPComponent p X L)
    (hKG : CFSG.Open.IsKGroup ↥L) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hpB : p ^ 4 ≤ Nat.card B) (hmax : IsMaxRankIn p B (L ⊔ B))
    (hlev : fullCoverLevel p (PQuot p L) = 4) (hlie : catalogIs (PSimple p L) (onLie fun _ => True)) :
    IsGB p B L := by
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hBab
  set M : Subgroup G := L ⊔ B with hM
  have hLM : L ≤ M := le_sup_left
  have hBM : B ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  haveI hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMN
  have hsn : IsSubnormal L M := IsSubnormal.step hLM hLn (IsSubnormal.refl M)
  have hOL : GLAPPrimeCoreOf p M ≤ L := ys03_glaPPrimeCoreOf_sup_le hp hBp hBN
  have eK : ↥(barX p M L) ≃* (↥L ⧸ GLAPPrimeCore p ↥L) := (quotEquivBarX hp hLM hsn).symm
  have hKq : CFSG.Open.IsQuasisimple ↥(barX p M L) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm
      (isQuasisimple_pQuot_of_glaPComponent hp hL)
  have hKcore : GLAPPrimeCore p ↥(barX p M L) = ⊥ := by
    have h1 := glaPPrimeCore_map_iso p eK
    rw [ys03_glaPPrimeCore_quot_eq_bot hp ↥L] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).1 h1
  have hKlev : fullCoverLevel p ↥(barX p M L) = 4 := by
    rw [fullCoverLevel_congr eK]
    exact hlev
  have hKn : (barX p M L).Normal := by
    show ((L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M))).Normal
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hBab' : IsElemAbelian p (barX p M B) := isElemAbelian_barX hBab
  have hsup : barX p M L ⊔ barX p M B = ⊤ := by
    show (L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) ⊔
      (B.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) = ⊤
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLM hBM]
    have htop : (L ⊔ B).subgroupOf M = ⊤ := by
      rw [← hM, Subgroup.subgroupOf_self]
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hpow : p ^ 4 ≤ Nat.card (barX p M B) := by
    rw [ys03_card_barX_of_isPGroup hp hBp hBM]
    exact hpB
  have hcop : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hmaxY : IsMaxRankIn p (barX p M B) ⊤ := by
    intro E _ hE
    obtain ⟨S, hS, hSE, hSc⟩ := exists_elemAbelian_lift (GLAPPrimeCore p ↥M) hcop hE
    have hS0 : IsElemAbelian p (S.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hS _
    have hle := hmax (S.map M.subtype) (Subgroup.map_subtype_le S) hS0
    have hc1 : Nat.card (S.map M.subtype) = Nat.card S :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [ys03_card_barX_of_isPGroup hp hBp hBM]
    have : Nat.card E = Nat.card S := hSc.symm
    omega
  have hDM : D ≤ M := hDB.trans hBM
  have hDp : IsPGroup p D := hBp.to_le hDB
  have hDcard : Nat.card (barX p M D) = Nat.card D := ys03_card_barX_of_isPGroup hp hDp hDM
  have hDle : barX p M D ≤ barX p M B ⊓ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) := by
    refine le_inf ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact ⟨d, Subgroup.mem_subgroupOf.2 (hDB (Subgroup.mem_subgroupOf.1 hd)), rfl⟩
    · rintro _ ⟨d, hd, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ ⟨u, hu, rfl⟩
      have hdu : (u : G) * (d : G) = (d : G) * (u : G) :=
        Subgroup.mem_centralizer_iff.1 (hDL (Subgroup.mem_subgroupOf.1 hd)) (u : G)
          (Subgroup.mem_subgroupOf.1 hu)
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hdu)
  have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have hcent : barX p M B ⊓ Subgroup.centralizer
      ((barX p M L : Subgroup (PQuot p M)) : Set (PQuot p M)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hDle
    have h1 := Subgroup.card_le_of_le hDle
    rw [Subgroup.card_bot, hDcard] at h1
    omega
  let φ : ↥L →* ↥(barX p M L) :=
    eK.symm.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))
  have hφ : Function.Surjective φ :=
    eK.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hKGroup : CFSG.Open.IsKGroup ↥(barX p M L) := hKG.of_surjective φ hφ
  have hKhat : catalogIs (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) (onLie fun _ => True) :=
    ys03_catalogIs_of_mulEquiv (QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).symm hlie
  rcases hKL (PQuot p M) (barX p M L) (barX p M B) hKn hKq hKGroup hKhat hKcore hKlev hBab' hsup hpow
    hmaxY hcent with
    ⟨E'', hE''B, _hE''ab, hE''card, hE''layer⟩ | ⟨h3, -, hcentcard, -, -⟩
  ·
    obtain ⟨E, hEB, hEq, -⟩ := exists_le_barX_eq hp hBp hBM hE''B
    have hEM : E ≤ M := hEB.trans hBM
    have hEp : IsPGroup p E := hBp.to_le hEB
    have hEcard : Nat.card E = p ^ 3 := by
      rw [← ys03_card_barX_of_isPGroup hp hEp hEM, hEq]
      exact hE''card
    have hcE := ys03_barX_inf_centralizer_eq hp hLM hEM hEp hOL
    rw [hEq] at hcE
    obtain ⟨J', hJ', hJ'ne⟩ := ys03_exists_component_ne_bot hE''layer
    rw [← hcE] at hJ'
    obtain ⟨K₂, hK₂, hK₂J⟩ := exists_glaPComponent_map_eq hp (ys03_qMap p M)
      (ys03_coprime_inf_ker_qMap hp ((L ⊓ Subgroup.centralizer (E : Set G)).subgroupOf M)) hJ'
    have hkerM : Nat.Coprime p (Nat.card ↥((L ⊓ Subgroup.centralizer (E : Set G)).subgroupOf M ⊓
        M.subtype.ker)) := by
      rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have hK₂G := glaPComponent_map hp M.subtype hkerM hK₂
    rw [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 (inf_le_left.trans hLM)] at hK₂G
    have hK₂ne : K₂ ≠ ⊥ := by
      rintro rfl
      apply hJ'ne
      rw [← hK₂J, Subgroup.map_bot]
    have hK₂G_ne : K₂.map M.subtype ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
      exact hK₂ne
    unfold IsGB
    refine ⟨E, hEB, isElemAbelian_mono hBab hEB, hEcard, hEB.trans hBN, ?_⟩
    intro hbot
    have hle : K₂.map M.subtype ≤ GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) :=
      le_sSup hK₂G
    rw [hbot] at hle
    exact hK₂G_ne (le_bot_iff.1 hle)
  ·
    exfalso
    subst h3
    have h1 := Subgroup.card_le_of_le hDle
    rw [hcentcard, hDcard] at h1
    omega

theorem false_of_isGB_of_nl (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {G : Type} [Group G] [Finite G] (hKG : CFSG.Open.IsKGroup G) {B D L : Subgroup G}
    (hD : Nat.card D ≤ 3 ^ 2) (hGB : IsGB 3 B L)
    (hnl : ∀ e ∈ B, e ∉ D → GLAPLayer 3 (L ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥) : False := by
  obtain ⟨E, hEB, hEel, hEcard, hEN, hlay⟩ := hGB
  obtain ⟨e, heE, heD⟩ : ∃ e ∈ E, e ∉ D := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show E ≤ D from fun g hg => hcon g hg)
    rw [hEcard] at h1
    omega
  have hEp : IsPGroup 3 E := isPGroup_of_isElemAbelian hEel
  have hEe : E ≤ Subgroup.centralizer ({e} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hEel hg heE)
  have hle := CFSG.HardMathSupport.Solomon.Proving.kZeroOf_le_layer_inf_centralizer hS
    (HDesc.isKGroup_of_le hKG _) hEp heE hEN hEe
  rw [hnl e (hEB heE) heD, le_bot_iff] at hle
  exact hlay hle

end Plain

section Certs

theorem kd264KLie_of_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264KLie p :=
  KD264Lie.kd264KLie_holds (KD264Lie.kd264LieInputs_of_rest7 (KD264Lie.kd264LieRest7_of_rest8
    (KD264Lie.kd264LieRest8_of_rest9 (KD264Lie.kd264LieRest9_of_rest10 (KD264Lie.kd264LieRest10_of_rest11
      (KD264Lie.kd264LieRest11_of_rest12 (KD264Lie.kd264LieRest12_of_rest13 (KD264Lie.kd264LieRest13_of_rest14
        (KD264Lie.lieCompAlg_classicalBCD (KD264Lie.d4EightCompAlgOuter_of_trialityInnerPairs
          KD264Lie.d4EightTrialityInnerPairs_holds))
        KD264Lie.e6D4OuterNotEight_holds KD264Lie.e6EightCentralizerConn_holds))))))))
    p hp hp2

theorem not_lvData_three_of_f4_te6 {X : Type} [Group X]
    (hc : catalogIs X S9.isF4two ∨ catalogIs X S9.isTE6two) : ¬ HDesc.LvData 3 X := by
  intro hlv
  rcases hc with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      obtain ⟨idx, hv⟩ := d
      cases idx with
      | F4 q =>
        simp only [S9.isF4two, onLie] at hi
        obtain ⟨hq2, -⟩ := HDesc.pp_eq_of_card Nat.prime_two (by norm_num)
          (hi.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        have hx := HDesc.lv_idx HDesc.lvCtx_holds Nat.prime_three (by norm_num) ⟨.F4 q, hv⟩
          (by simpa using hq2) e hlv
        simp [HDesc.ExcT, HDesc.tagOf, HDesc.dimOf] at hx
      | _ => simp [S9.isF4two, onLie] at hi
    | _ => exact hi.elim
  · cases i with
    | lie d =>
      obtain ⟨idx, hv⟩ := d
      cases idx with
      | twistedE6 q =>
        simp only [S9.isTE6two, onLie] at hi
        obtain ⟨hq2, -⟩ := HDesc.pp_eq_of_card Nat.prime_two (by norm_num)
          (hi.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        have hx := HDesc.lv_idx HDesc.lvCtx_holds Nat.prime_three (by norm_num) ⟨.twistedE6 q, hv⟩
          (by simpa using hq2) e hlv
        simp [HDesc.ExcT, HDesc.tagOf, HDesc.dimOf] at hx
      | _ => simp [S9.isTE6two, onLie] at hi
    | _ => exact hi.elim

theorem isChevSimple_two_of_f4_te6 {X : Type} [Group X]
    (hc : catalogIs X S9.isF4two ∨ catalogIs X S9.isTE6two) : IsChevSimple 2 X := by
  left
  rcases hc with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
  · refine ⟨i, ?_, he⟩
    cases i with
    | lie d =>
      obtain ⟨idx, hv⟩ := d
      cases idx with
      | F4 q =>
        simp only [S9.isF4two, onLie] at hi
        obtain ⟨hq2, -⟩ := HDesc.pp_eq_of_card Nat.prime_two (by norm_num)
          (hi.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        simpa [onLie] using hq2
      | _ => simp [S9.isF4two, onLie] at hi
    | _ => exact hi.elim
  · refine ⟨i, ?_, he⟩
    cases i with
    | lie d =>
      obtain ⟨idx, hv⟩ := d
      cases idx with
      | twistedE6 q =>
        simp only [S9.isTE6two, onLie] at hi
        obtain ⟨hq2, -⟩ := HDesc.pp_eq_of_card Nat.prime_two (by norm_num)
          (hi.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
        simpa [onLie] using hq2
      | _ => simp [S9.isTE6two, onLie] at hi
    | _ => exact hi.elim

theorem fullCoverLevel_eq_four_of_f4_te6 {Q : Type} [Group Q]
    (hc : catalogIs (Q ⧸ Subgroup.center Q) S9.isF4two ∨ catalogIs (Q ⧸ Subgroup.center Q) S9.isTE6two) :
    fullCoverLevel 3 Q = 4 := by
  have hnot := not_lvData_three_of_f4_te6 hc
  have h1 : ¬ K1Cover 3 Q := fun hk => hnot (Or.inl hk.2)
  have h2 : ¬ K2Cover 3 Q := fun hk => hnot (Or.inr (k2Cover_imp_catalogIs 3 hk))
  have h3 : ¬ K3Cover 3 Q := fun hk => k3NotChev2At_holds 3 Q hk (isChevSimple_two_of_f4_te6 hc)
  unfold fullCoverLevel
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem false_of_case1_lie {G : Type} [Group G] [Finite G] (hKG : CFSG.Open.IsKGroup G)
    {B D X L : Subgroup G} (hB : IsElemAbelian 3 B) (hB4 : 3 ^ 4 ≤ Nat.card B) (hDB : D ≤ B)
    (hDL : D ≤ Subgroup.centralizer (L : Set G)) (hD : Nat.card D = 3 ^ 2) (hL : GLAPComponent 3 X L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hmax : IsMaxRankIn 3 B (L ⊔ B))
    (hc : catalogIs (PSimple 3 L) S9.isF4two ∨ catalogIs (PSimple 3 L) S9.isTE6two)
    (hnl : ∀ e ∈ B, e ∉ D → GLAPLayer 3 (L ⊓ Subgroup.centralizer ({e} : Set G)) = ⊥) : False := by
  have hlie : catalogIs (PSimple 3 L) (onLie fun _ => True) := by
    rcases hc with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
    · refine ⟨i, ?_, he⟩
      cases i with
      | lie d => trivial
      | _ => exact hi.elim
    · refine ⟨i, ?_, he⟩
      cases i with
      | lie d => trivial
      | _ => exact hi.elim
  have hGB := isGB_of_kd264KLie (kd264KLie_of_odd 3 Nat.prime_three (by norm_num)) Nat.prime_three hB hDB
    hDL hD.ge hL (HDesc.isKGroup_of_le hKG L) hBN hB4 hmax (fullCoverLevel_eq_four_of_f4_te6 hc) hlie
  exact false_of_isGB_of_nl (CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog) hKG hD.le hGB hnl

end Certs

end CFSG.LocalAnalysis.GLTheoremA.S265C.C1

end
