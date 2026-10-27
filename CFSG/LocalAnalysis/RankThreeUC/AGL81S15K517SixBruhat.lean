module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517SixComm

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

section Bruhat

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem mem_parabolic_of_mul_nrep_mem {X : Subgroup K} (hU : posUnipotent D ≤ X) :
    ∀ (N : ℕ) (w : (coxeterMatrix D.isFiniteType).Group),
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w = N →
      ∀ t ∈ ⨆ i, H i, t * nrep hct w ∈ X →
        w ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic
          {i | rankOne D.rootGroup i ≤ X} := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w hN t ht hm
    set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem with hcs
    by_cases hw1 : w = 1
    · subst hw1
      exact one_mem _
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hw1
    have hact : ActsAs D (t * nrep hct w) (1 * w) :=
      (actsAs_of_mem_iSup hct ht).mul (actsAs_nrep hct w)
    rw [one_mul] at hact
    have hneg := rootGroup_neg_single_le_of_actsAs hU hm hact hi
    have hpos : D.rootGroup (Pi.single i 1) ≤ X := fun x hx =>
      hU (rootGroup_le_posUnipotent (single_mem_roots i) (ht_single_pos i) hx)
    have hrank : rankOne D.rootGroup i ≤ X := sup_le hpos hneg
    have hiJ : i ∈ {i | rankOne D.rootGroup i ≤ X} := hrank
    set w' := cs.simple i * w with hw'
    have hlen : cs.length w' < cs.length w := hi
    have hw'w : cs.simple i * w' = w := by
      rw [hw', ← mul_assoc, cs.simple_mul_simple_self, one_mul]
    have hnd : ¬ cs.IsLeftDescent w' i := by
      intro h
      have h1 : cs.length (cs.simple i * w') < cs.length w' := h
      rw [hw'w] at h1
      omega
    have hnrep : nrep hct w = n i * nrep hct w' := by
      have := nrep_simple_mul hct hnd
      rwa [hw'w] at this
    have hni : n i ∈ X := hrank (hct.n_mem i)
    have hm' : ((n i)⁻¹ * t * n i) * nrep hct w' ∈ X := by
      have h1 := mul_mem (inv_mem hni) hm
      rw [hnrep] at h1
      have e : (n i)⁻¹ * (t * (n i * nrep hct w')) = ((n i)⁻¹ * t * n i) * nrep hct w' := by group
      rwa [e] at h1
    have ht' : (n i)⁻¹ * t * n i ∈ ⨆ i, H i := by
      have := nrep_inv_conj_mem_iSup hct (cs.simple i) ht
      rwa [nrep_simple hct i] at this
    have hlt : cs.length w' < N := by omega
    have hw'J := ih (cs.length w') hlt w' rfl _ ht' hm'
    have : w = cs.simple i * w' := hw'w.symm
    rw [this]
    exact mul_mem (cs.simple_mem_parabolic hiJ) hw'J

include hct hext in
theorem le_parJ_of_posUnipotent_le {X : Subgroup K} (hU : posUnipotent D ≤ X) :
    X ≤ parJ D H {i | rankOne D.rootGroup i ≤ X} := by
  intro g hg
  obtain ⟨w, hgw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hgw
  have huU : u ∈ posUnipotent D := inversionUnipotent_le_posUnipotent w hu
  have hbn : b * nrep hct w ∈ X := by
    have := mul_mem hg (inv_mem (hU huU))
    simpa [mul_assoc] using this
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨t, ht, v, hv, rfl⟩ := hb
  have htB : t ∈ borel D H := iSup_le_borel ht
  have hv' : t * v * t⁻¹ ∈ posUnipotent D :=
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_posUnipotent hct htB) v).1 hv
  have hm : t * nrep hct w ∈ X := by
    have h1 := mul_mem (inv_mem (hU hv')) hbn
    simpa [mul_assoc] using h1
  have hwJ := mem_parabolic_of_mul_nrep_mem hct hext hU _ w rfl t ht hm
  have hnJ : nrep hct w ∈ parJ D H {i | rankOne D.rootGroup i ≤ X} :=
    (iSup₂_le fun i hi => rankOne_le_parJ hi : leviM D {i | rankOne D.rootGroup i ≤ X} ≤ _)
      (nrep_mem_leviM hct hwJ)
  have htP : t * v ∈ parJ D H {i | rankOne D.rootGroup i ≤ X} :=
    borel_le_parJ _ (mul_mem htB (posUnipotent_le_borel hv))
  exact mul_mem (mul_mem htP hnJ) (borel_le_parJ _ (posUnipotent_le_borel huU))

end Bruhat

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
