module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10h1_plane_le {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) : zpowers x ⊔ zpowers z ≤ M :=
  (sup_le (zpowers_le.mpr h.point.mem) (zpowers_le.mpr h.central.mem)).trans
    (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA h.situation.isCoreMaxLocal).1

private theorem r10h1_plane_isPGroup {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) : IsPGroup 3 (zpowers x ⊔ zpowers z : Subgroup G) :=
  IsPGroup.of_card (n := 2)
    (SmallRankPlane.of_situation h.setting h.situation h.point h.central).card_eq

private theorem r10h1_core_not_dvd (M : Subgroup G) :
    ¬ 3 ∣ Nat.card (rankThreePrimeCore 3 M) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 M)

private theorem r10h1_le_normalizer_core (M : Subgroup G) :
    M ≤ normalizer (rankThreePrimeCore 3 M : Set G) :=
  CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M

omit [Finite G] in
private theorem r10h1_core_le (M : Subgroup G) : rankThreePrimeCore 3 M ≤ M :=
  CFSG.AGLEmbedding.glbPrimeCore_le 3 M

theorem le_primeCore_of_normalizes {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {F : Subgroup G} (hFM : F ≤ M) (hF3 : ¬ 3 ∣ Nat.card F)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G)) :
    F ≤ rankThreePrimeCore 3 M := by
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z :=
    SmallRankPlane.of_situation h.setting h.situation h.point h.central
  exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains Nat.prime_three (by norm_num)
    h.constrained (r10h1_plane_isPGroup h) (r10h1_plane_le h)
    (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
      rw [← hord]
      exact pow_orderOf_eq_one y)) hFM
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hF3) hBF

set_option linter.unusedVariables false in
theorem exists_invariant_sylow_ge {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) {F : Subgroup G}
    (hF : IsPGroup f F) (hFD : F ≤ rankThreePrimeCore 3 M)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G)) :
    ∃ Fs : Subgroup G, F ≤ Fs ∧ Fs ≤ rankThreePrimeCore 3 M ∧ IsPGroup f Fs ∧
      ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index ∧
      zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G) := by
  have : Fact f.Prime := ⟨hf⟩
  obtain ⟨S, hS, hFS, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three hf (r10h1_plane_isPGroup h) (r10h1_core_not_dvd M)
    ((r10h1_plane_le h).trans (r10h1_le_normalizer_core M)) hFD hF hBF
  refine ⟨S, hFS, hS.1, hS.2.1, ?_, hBS⟩
  obtain ⟨T, hT⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  have hS' : S.subgroupOf (rankThreePrimeCore 3 M) = (T : Subgroup (rankThreePrimeCore 3 M)) := by
    rw [← hT]
    exact Subgroup.comap_map_eq_self_of_injective (rankThreePrimeCore 3 M).subtype_injective _
  rw [hS']
  exact T.not_dvd_index

omit [Finite G] in
private theorem r10h1_fusionIsSylowIn_of_index {f : ℕ} (hf : f.Prime) {D S : Subgroup G}
    (hSD : S ≤ D) (hS : IsPGroup f S) (hidx : ¬ f ∣ (S.subgroupOf D).index) :
    fusionIsSylowIn f S D := by
  have : Fact f.Prime := ⟨hf⟩
  have h : fusionIsSylowIn f ((S.subgroupOf D).map D.subtype) D :=
    CFSG.Goldschmidt.G310.fusionIsSylowIn_map (hS.comap_subtype.toSylow hidx : Sylow f D)
  rwa [Subgroup.map_subgroupOf_eq_of_le hSD] at h

omit [Finite G] in
private theorem r10h1_fusionIsSylowIn_map_conj {f : ℕ} {D S : Subgroup G}
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

private theorem r10h1_exists_conj_sylow {M : Subgroup G} {f : ℕ} (hf : f.Prime)
    {S S' : Subgroup G}
    (hS : fusionIsSylowIn f S (rankThreePrimeCore 3 M))
    (hS' : fusionIsSylowIn f S' (rankThreePrimeCore 3 M)) :
    ∃ c ∈ rankThreePrimeCore 3 M, S' = S.map (MulAut.conj c).toMonoidHom := by
  have h3 : IsPGroup 3 ↥(⊥ : Subgroup G) := IsPGroup.of_bot
  obtain ⟨c, hc, hEq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    hf h3 (r10h1_core_not_dvd M) (by simp) hS hS' (by simp) (by simp)
  exact ⟨c, (mem_inf.mp hc).1, hEq⟩

set_option linter.unusedVariables false in
theorem exists_mul_mem_normalizer {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {f : ℕ} (hf : f.Prime) {Fs : Subgroup G}
    (hFsD : Fs ≤ rankThreePrimeCore 3 M) (hFs : IsPGroup f Fs)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index) :
    ∀ m ∈ M, ∃ d ∈ rankThreePrimeCore 3 M, ∃ n ∈ M ⊓ normalizer (Fs : Set G), m = d * n := by
  intro m hm
  have hS := r10h1_fusionIsSylowIn_of_index hf hFsD hFs hsyl
  have hS' := r10h1_fusionIsSylowIn_map_conj hS (r10h1_le_normalizer_core M hm)
  obtain ⟨c, hc, hcFs⟩ := r10h1_exists_conj_sylow hf hS' hS
  refine ⟨c⁻¹, inv_mem hc, c * m, mem_inf.mpr ⟨mul_mem (r10h1_core_le M hc) hm, ?_⟩, by group⟩
  rw [mem_normalizer_iff_map_conj_eq]
  have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      (MulAut.conj (c * m)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have h2 : Fs.map (MulAut.conj (c * m)).toMonoidHom = Fs := by
    rw [← hcomp, ← map_map]
    exact hcFs.symm
  exact h2

private theorem r10h1_card_le_sylow {H : Type} [Group H] [Finite H] {Q : Subgroup H}
    (hQ : IsPGroup 3 Q) (R : Sylow 3 H) : Nat.card Q ≤ Nat.card R := by
  obtain ⟨R₂, hR₂⟩ := hQ.exists_le_sylow
  rw [R.card_eq_multiplicity, ← R₂.card_eq_multiplicity]
  exact Subgroup.card_le_of_le hR₂

private theorem r10h1_exists_conj_le_normalizer {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {f : ℕ} (hf : f.Prime) {Fs : Subgroup G}
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
    Nat.prime_three hf P.isPGroup' (r10h1_core_not_dvd M)
    (hPM.trans (r10h1_le_normalizer_core M)) bot_le hbot hPbot
  obtain ⟨c, hc, hFsc⟩ := r10h1_exists_conj_sylow hf hS
    (r10h1_fusionIsSylowIn_of_index hf hFsD hFs hsyl)
  refine ⟨c, hc, le_inf ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem (r10h1_core_le M hc) (hPM ha)) (M.inv_mem (r10h1_core_le M hc))
  · rw [hFsc, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hPS

set_option linter.unusedVariables false in
theorem exists_sylow_three_normalizing {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (h : Setup65A G P M x z) {f : ℕ} (hf : f.Prime) (hf3 : f ≠ 3) {Fs : Subgroup G}
    (hFsD : Fs ≤ rankThreePrimeCore 3 M) (hFs : IsPGroup f Fs)
    (hsyl : ¬ f ∣ (Fs.subgroupOf (rankThreePrimeCore 3 M)).index)
    (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G)) :
    ∃ R : Subgroup G, zpowers x ⊔ zpowers z ≤ R ∧ R ≤ M ∧ R ≤ normalizer (Fs : Set G) ∧
      IsPGroup 3 R ∧ ¬ 3 ∣ (R.subgroupOf (M ⊓ normalizer (Fs : Set G))).index ∧
      ¬ 3 ∣ (R.subgroupOf M).index ∧ CFSG.Open.pRank 3 R = 3 := by
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA h.situation.isCoreMaxLocal).1
  have hP3 : CFSG.Open.pRank 3 (P : Subgroup G) = 3 :=
    (sylow_le_of_isCoreMaxLocal h.setting h.situation.mem_sigmaA h.situation.isCoreMaxLocal).2
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = M ⊓ normalizer (Fs : Set G) := ⟨_, rfl⟩
  have hNM : N ≤ M := by
    rw [hN]
    exact inf_le_left
  have hNFs : N ≤ normalizer (Fs : Set G) := by
    rw [hN]
    exact inf_le_right
  have hBN : zpowers x ⊔ zpowers z ≤ N := by
    rw [hN]
    exact le_inf (r10h1_plane_le h) hBFs
  obtain ⟨c, -, hQN'⟩ := r10h1_exists_conj_le_normalizer h hf hFsD hFs hsyl
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, Q = (P : Subgroup G).map (MulAut.conj c).toMonoidHom :=
    ⟨_, rfl⟩
  have hQN : Q ≤ N := by
    rw [hQ, hN]
    exact hQN'
  have hQ3 : IsPGroup 3 Q := by
    rw [hQ]
    exact P.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card (P : Subgroup G) := by
    rw [hQ]
    exact Subgroup.card_map_of_injective (MulAut.conj c).injective
  obtain ⟨R, hBR⟩ := ((r10h1_plane_isPGroup h).comap_subtype (K := N)).exists_le_sylow
  obtain ⟨R', hR'⟩ : ∃ R' : Subgroup G, R' = (R : Subgroup N).map N.subtype := ⟨_, rfl⟩
  have hBR' : zpowers x ⊔ zpowers z ≤ R' := by
    rw [hR']
    exact fun b hb => ⟨⟨b, hBN hb⟩, hBR hb, rfl⟩
  have hR'N : R' ≤ N := by
    rw [hR']
    exact Subgroup.map_subtype_le _
  have hR'3 : IsPGroup 3 R' := by
    rw [hR']
    exact R.isPGroup'.map _
  have hcardR : Nat.card R' = Nat.card (R : Subgroup N) := by
    rw [hR']
    exact Subgroup.card_map_of_injective N.subtype_injective
  have hle : Nat.card R' ≤ Nat.card (P : Subgroup G) := r10h1_card_le_sylow hR'3 P
  have hge : Nat.card (P : Subgroup G) ≤ Nat.card R' := by
    rw [hcardR, ← hQcard, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
    exact r10h1_card_le_sylow (hQ3.comap_subtype (K := N)) R
  have hcard : Nat.card R' = Nat.card (P : Subgroup G) := le_antisymm hle hge
  have hRsub : R'.subgroupOf N = (R : Subgroup N) := by
    rw [hR', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hv : ¬ 3 ∣ (R'.subgroupOf N).index := by
    rw [hRsub]
    exact R.not_dvd_index
  have hR'M : R' ≤ M := hR'N.trans hNM
  have hPidx : ¬ 3 ∣ (P : Subgroup G).index := P.not_dvd_index
  have hPdvd : ((P : Subgroup G).subgroupOf M).index ∣ (P : Subgroup G).index :=
    Dvd.intro M.index (Subgroup.relIndex_mul_index hPM)
  have hPM' : ¬ 3 ∣ ((P : Subgroup G).subgroupOf M).index := fun hd => hPidx (hd.trans hPdvd)
  have hcardM : ∀ K : Subgroup G, K ≤ M → Nat.card (K.subgroupOf M) = Nat.card K :=
    fun K hK => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hA : Nat.card (R'.subgroupOf M) * (R'.subgroupOf M).index = Nat.card M :=
    Subgroup.card_mul_index (R'.subgroupOf M)
  have hB : Nat.card ((P : Subgroup G).subgroupOf M) *
      ((P : Subgroup G).subgroupOf M).index = Nat.card M :=
    Subgroup.card_mul_index ((P : Subgroup G).subgroupOf M)
  rw [hcardM R' hR'M, hcard] at hA
  rw [hcardM (P : Subgroup G) hPM] at hB
  have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
  have hidx : (R'.subgroupOf M).index = ((P : Subgroup G).subgroupOf M).index :=
    Nat.eq_of_mul_eq_mul_left hPpos (hA.trans hB.symm)
  have hvM : ¬ 3 ∣ (R'.subgroupOf M).index := by
    rw [hidx]
    exact hPM'
  have hpR : CFSG.Open.pRank 3 R' = 3 := by
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow Nat.prime_three hR'M
      hR'3 hvM
    have h2 := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow Nat.prime_three hPM
      P.isPGroup' hPM'
    exact h1.trans (h2.symm.trans hP3)
  rw [← hN]
  exact ⟨R', hBR', hR'M, hR'N.trans hNFs, hR'3, hv, hvM, hpR⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
