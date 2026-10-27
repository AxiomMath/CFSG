module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SolvableConstraint
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem max65_plane_le {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) : zpowers x ⊔ zpowers z ≤ M :=
  (sup_le (zpowers_le.mpr h.point.mem) (zpowers_le.mpr h.central.mem)).trans
    (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA h.situation.isCoreMaxLocal).1

private theorem max65_plane_isPGroup {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
  IsPGroup.of_card (n := 2)
    (SmallRankPlane.of_situation h.setting h.situation h.point h.central).card_eq

private theorem max65_core_not_dvd (M : Subgroup G) : ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 M) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 M)

private theorem max65_le_normalizer_core (M : Subgroup G) :
    M ≤ normalizer (rankThreePrimeCore 3 M : Set G) :=
  CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M

omit [Finite G] in
private theorem max65_core_le (M : Subgroup G) : rankThreePrimeCore 3 M ≤ M :=
  CFSG.AGLEmbedding.glbPrimeCore_le 3 M

theorem le_primeCore_of_normalizes {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) {F : Subgroup G} (hFM : F ≤ M) (hF3 : ¬ 3 ∣ Nat.card F)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G)) :
    F ≤ rankThreePrimeCore 3 M := by
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z :=
    SmallRankPlane.of_situation h.setting h.situation h.point h.central
  have : Group.IsSolvable M := h.solvable
  exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains Nat.prime_three (by norm_num)
    (solvable_hasPrimeConstraint (G := M) 3 Nat.prime_three) (max65_plane_isPGroup h)
    (max65_plane_le h)
    (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
      rw [← hord]
      exact pow_orderOf_eq_one y)) hFM
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hF3) hBF

set_option linter.unusedVariables false in
theorem exists_invariant_sylow_ge {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) {F : Subgroup G}
    (hF : IsPGroup f F) (hFD : F ≤ rankThreePrimeCore 3 M)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G)) :
    ∃ Fs : Subgroup G, F ≤ Fs ∧ Fs ≤ rankThreePrimeCore 3 M ∧ IsPGroup f Fs ∧
      ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index ∧
      zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G) := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨S, hS, hFS, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hf (max65_plane_isPGroup h) (max65_core_not_dvd M)
    ((max65_plane_le h).trans (max65_le_normalizer_core M)) hFD hF hBF
  refine ⟨S, hFS, hS.1, hS.2.1, ?_, hBS⟩
  obtain ⟨T, hT⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  have hS' : S.subgroupOf (rankThreePrimeCore 3 M) = (T : Subgroup (rankThreePrimeCore 3 M)) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective (rankThreePrimeCore 3 M).subtype_injective _
  rw [hS']
  exact T.not_dvd_index


omit [Finite G] in
private theorem max65_fusionIsSylowIn_of_index {f : ℕ} (hf : f.Prime) {D S : Subgroup G}
    (hSD : S ≤ D) (hS : IsPGroup f S) (hidx : ¬ f ∣ (S.subgroupOf D).index) :
    fusionIsSylowIn f S D := by
  have : Fact f.Prime := ⟨hf⟩
  have h : fusionIsSylowIn f ((S.subgroupOf D).map D.subtype) D :=
    CFSG.Goldschmidt.G310.fusionIsSylowIn_map (hS.comap_subtype.toSylow hidx : Sylow f D)
  rwa [Subgroup.map_subgroupOf_eq_of_le hSD] at h

omit [Finite G] in
private theorem max65_fusionIsSylowIn_map_conj {f : ℕ} {D S : Subgroup G}
    (hS : fusionIsSylowIn f S D) {g : G} (hg : g ∈ normalizer (D : Set G)) :
    fusionIsSylowIn f (S.map (MulAut.conj g).toMonoidHom) D := by
  obtain ⟨hSD, hSp, hmax⟩ := hS
  have hg' : g⁻¹ ∈ normalizer (D : Set G) := inv_mem hg
  refine ⟨?_, hSp.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp (hSD hy)
  · intro Q hQD hQp hSQ
    have h1 : Q.map (MulAut.conj g⁻¹).toMonoidHom = S := by
      refine hmax _ ?_ (hQp.map _) ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp hg' y).mp (hQD hy)
      · intro x hx
        refine ⟨g * x * g⁻¹, hSQ ⟨x, hx, rfl⟩, ?_⟩
        simp [mul_assoc]
    rw [← h1, map_map]
    have : ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) = MonoidHom.id G := by
      ext x; simp [mul_assoc]
    rw [this, map_id]

private theorem max65_exists_conj_sylow {M : Subgroup G} {f : ℕ} (hf : f.Prime) {S S' : Subgroup G}
    (hS : fusionIsSylowIn f S (rankThreePrimeCore 3 M))
    (hS' : fusionIsSylowIn f S' (rankThreePrimeCore 3 M)) :
    ∃ c ∈ rankThreePrimeCore 3 M, S' = S.map (MulAut.conj c).toMonoidHom := by
  have h3 : IsPGroup 3 ↥(⊥ : Subgroup G) := IsPGroup.of_bot
  obtain ⟨c, hc, hEq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    hf h3 (max65_core_not_dvd M) (by simp) hS hS' (by simp) (by simp)
  exact ⟨c, (mem_inf.mp hc).1, hEq⟩

set_option linter.unusedVariables false in
theorem exists_mul_mem_normalizer {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) {f : ℕ} (hf : f.Prime) {Fs : Subgroup G}
    (hFsD : Fs ≤ rankThreePrimeCore 3 M) (hFs : IsPGroup f Fs)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index) :
    ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore 3 M, ∃ n ∈ M ⊓ normalizer (Fs : Set G), m = d * n := by
  intro m hm
  have hS := max65_fusionIsSylowIn_of_index hf hFsD hFs hsyl
  have hS' := max65_fusionIsSylowIn_map_conj hS (max65_le_normalizer_core M hm)
  obtain ⟨c, hc, hcFs⟩ := max65_exists_conj_sylow hf hS' hS
  refine ⟨c⁻¹, inv_mem hc, c * m, mem_inf.mpr ⟨mul_mem (max65_core_le M hc) hm, ?_⟩, by group⟩
  rw [mem_normalizer_iff_map_conj_eq]
  have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      (MulAut.conj (c * m)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have h2 : Fs.map (MulAut.conj (c * m)).toMonoidHom = Fs := by
    rw [← hcomp, ← map_map]
    exact hcFs.symm
  exact h2


local notation "W₃" => Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)

omit [Finite G] in
private theorem max65_card_eq_eighty_one {P : Subgroup G} (e : P ≃* W₃) : Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card]
  simp

private theorem max65_card_le_sylow {H : Type} [Group H] [Finite H] {Q : Subgroup H}
    (hQ : IsPGroup 3 Q) (R : Sylow 3 H) : Nat.card Q ≤ Nat.card R := by
  obtain ⟨R₂, hR₂⟩ := hQ.exists_le_sylow
  rw [R.card_eq_multiplicity, ← R₂.card_eq_multiplicity]
  exact Subgroup.card_le_of_le hR₂

private theorem max65_exists_conj_le_normalizer {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) {f : ℕ} (hf : f.Prime) {Fs : Subgroup G}
    (hFsD : Fs ≤ rankThreePrimeCore 3 M) (hFs : IsPGroup f Fs)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index) :
    ∃ c ∈ rankThreePrimeCore 3 M,
      (P : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ M ⊓ normalizer (Fs : Set G) := by
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA h.situation.isCoreMaxLocal).1
  have hbot : IsPGroup f ↥(⊥ : Subgroup G) := IsPGroup.of_bot
  have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨S, hS, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hf P.isPGroup' (max65_core_not_dvd M)
    (hPM.trans (max65_le_normalizer_core M)) bot_le hbot hPbot
  obtain ⟨c, hc, hFsc⟩ := max65_exists_conj_sylow hf hS
    (max65_fusionIsSylowIn_of_index hf hFsD hFs hsyl)
  refine ⟨c, hc, le_inf ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem (max65_core_le M hc) (hPM ha)) (M.inv_mem (max65_core_le M hc))
  · rw [hFsc, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hPS

set_option linter.unusedVariables false in
theorem exists_sylow_three_normalizing {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65 G P M x z) {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) {Fs : Subgroup G}
    (hFsD : Fs ≤ rankThreePrimeCore 3 M) (hFs : IsPGroup f Fs)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index)
    (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G)) :
    ∃ R : Subgroup G, zpowers x ⊔ zpowers z ≤ R ∧ R ≤ M ∧ R ≤ normalizer (Fs : Set G) ∧
      IsPGroup 3 R ∧ Nat.card R = 81 ∧
      Nonempty (R ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) := by
  obtain ⟨e⟩ := h.wreath
  have hP81 : Nat.card (P : Subgroup G) = 81 := max65_card_eq_eighty_one e
  set N : Subgroup G := M ⊓ normalizer (Fs : Set G) with hN
  have hBN : zpowers x ⊔ zpowers z ≤ N := le_inf (max65_plane_le h) hBFs
  obtain ⟨c, -, hQN⟩ := max65_exists_conj_le_normalizer h hf hFsD hFs hsyl
  set Q : Subgroup G := (P : Subgroup G).map (MulAut.conj c).toMonoidHom with hQ
  have hQ3 : IsPGroup 3 Q := P.isPGroup'.map _
  have hQ81 : Nat.card Q = 81 := by
    rw [hQ, Subgroup.card_map_of_injective (MulAut.conj c).injective, hP81]
  obtain ⟨R, hBR⟩ := ((max65_plane_isPGroup h).comap_subtype (K := N)).exists_le_sylow
  set R' : Subgroup G := (R : Subgroup N).map N.subtype with hR'
  have hBR' : zpowers x ⊔ zpowers z ≤ R' := fun b hb => ⟨⟨b, hBN hb⟩, hBR hb, rfl⟩
  have hR'N : R' ≤ N := Subgroup.map_subtype_le _
  have hR'3 : IsPGroup 3 R' := R.isPGroup'.map _
  have hcardR : Nat.card R' = Nat.card (R : Subgroup N) :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hle : Nat.card R' ≤ 81 := by
    rw [← hP81]
    exact max65_card_le_sylow hR'3 P
  have hge : 81 ≤ Nat.card R' := by
    rw [hcardR, ← hQ81, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
    exact max65_card_le_sylow (hQ3.comap_subtype (K := N)) R
  have hcard : Nat.card R' = 81 := le_antisymm hle hge
  refine ⟨R', hBR', hR'N.trans inf_le_left, hR'N.trans inf_le_right, hR'3, hcard, ?_⟩
  have hcard' : Nat.card R' = 3 ^ (Nat.card G).factorization 3 := by
    rw [hcard, ← P.card_eq_multiplicity, hP81]
  exact ⟨(Sylow.equiv (Sylow.ofCard R' hcard') P).trans e⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
