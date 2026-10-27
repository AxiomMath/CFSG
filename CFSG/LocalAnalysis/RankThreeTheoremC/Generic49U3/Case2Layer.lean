module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Layer

variable {Y : Type} [Group Y] [Finite Y]

theorem centralizer_layer_inf_centralizer_pCore_le {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := Y) p = ⊥) :
    centralizer (CFSG.layer Y : Set Y) ⊓ centralizer (CFSG.pCore p Y : Set Y) ≤ CFSG.pCore p Y := by
  have hF : CFSG.fittingSubgroup Y = CFSG.pCore p Y := CFSG.Fitting_eq_pcore Y p hcore
  have hbender : centralizer (CFSG.generalizedFitting Y : Set Y) ≤ CFSG.fittingSubgroup Y := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Y
  intro a ha
  rw [← hF]
  apply hbender
  rw [mem_centralizer_iff]
  intro y hy
  have hle : CFSG.generalizedFitting Y ≤ centralizer ({a} : Set Y) := by
    rw [CFSG.generalizedFitting.eq_sup]
    apply sup_le
    · intro z hz
      rw [hF] at hz
      rw [mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (mem_centralizer_iff.mp ha.2 z hz).symm
    · intro z hz
      rw [mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (mem_centralizer_iff.mp ha.1 z hz).symm
  exact (mem_centralizer_iff.mp (hle hy) a (Set.mem_singleton a)).symm

end Layer

namespace Case2Data

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem le_pCore_of_forall_le_centralizer (h : Case2Data p P T D F x)
    (hT : ∀ L : Subgroup Y, IsComponentOf L ⊤ → T ≤ centralizer (L : Set Y)) :
    T ≤ CFSG.pCore p Y := by
  haveI : Fact p.Prime := h.fact
  haveI hOn : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have hTE : T ≤ centralizer (CFSG.layer Y : Set Y) := by
    have hlay : CFSG.layer Y ≤ centralizer (T : Set Y) := by
      rw [CFSG.layer.eq_sSup]
      apply sSup_le
      intro K hK k hk
      rw [mem_centralizer_iff]
      intro t ht
      have h1 : t ∈ centralizer (K : Set Y) := hT K ((CFSG.isComponent_iff_open K).mp hK) ht
      exact (mem_centralizer_iff.mp h1 k hk).symm
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (hlay hz) t ht).symm
  have key : (∀ o ∈ CFSG.pCore p Y, ∀ t ∈ T, o * t = t * o) → T ≤ CFSG.pCore p Y := by
    intro hc t ht
    have h2 : t ∈ centralizer (CFSG.pCore p Y : Set Y) := by
      rw [mem_centralizer_iff]
      intro o ho
      exact hc o ho t ht
    exact centralizer_layer_inf_centralizer_pCore_le h.core ⟨hTE ht, h2⟩
  have hOP : CFSG.pCore p Y ≤ P := by
    obtain ⟨S, hS⟩ := h.sylow
    rw [← hS]
    exact CFSG.pCore_isPGroup.le_sylow_of_normal S
  have hcomm : ∀ o ∈ CFSG.pCore p Y, ∀ t ∈ T,
      o * t * o⁻¹ * t⁻¹ ∈ CFSG.pCore p Y ⊓ zOf T := by
    intro o ho t ht
    refine ⟨?_, ?_⟩
    · have h1 : t * o⁻¹ * t⁻¹ ∈ CFSG.pCore p Y := hOn.conj_mem o⁻¹ (inv_mem ho) t
      have h2 : o * (t * o⁻¹ * t⁻¹) ∈ CFSG.pCore p Y := mul_mem ho h1
      simpa [mul_assoc] using h2
    · obtain ⟨t0, ht0, d0, hd0, rfl⟩ := h.exists_mul o (hOP ho)
      have h1 : d0 * t * d0⁻¹ = t := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (h.pdata.comm t ht d0 hd0).symm
      have h2 : t0 * d0 * t * (t0 * d0)⁻¹ * t⁻¹ = t0 * t * t0⁻¹ * t⁻¹ := by
        calc t0 * d0 * t * (t0 * d0)⁻¹ * t⁻¹
            = t0 * (d0 * t * d0⁻¹) * t0⁻¹ * t⁻¹ := by group
          _ = t0 * t * t0⁻¹ * t⁻¹ := by rw [h1]
      rw [h2]
      exact h.commutator_mem t0 ht0 t ht
  by_cases hbot : CFSG.pCore p Y ⊓ zOf T = ⊥
  ·
    apply key
    intro o ho t ht
    have h1 := hcomm o ho t ht
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : o * t * o⁻¹ = t := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  ·
    have hZO : zOf T ≤ CFSG.pCore p Y := by
      have hdvd : Nat.card (CFSG.pCore p Y ⊓ zOf T : Subgroup Y) ∣ Nat.card (zOf T) :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [h.zOf_card] at hdvd
      rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hbot
      · have h2 : CFSG.pCore p Y ⊓ zOf T = zOf T :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h.zOf_card, h1])
        exact inf_eq_right.mp h2
    have hirr := h.torus.irred (T ⊓ CFSG.pCore p Y) inf_le_left (le_inf h.zOf_le hZO) (by
      intro f hf a ha
      exact ⟨h.torus.F_T f hf a ha.1, hOn.conj_mem a ha.2 f⟩)
    rcases hirr with hA | hA
    ·
      apply key
      intro o ho t ht
      obtain ⟨t0, ht0, d0, hd0, rfl⟩ := h.exists_mul o (hOP ho)
      have ht0Z : t0 ∈ zOf T := by
        apply h.torus.fpf t0 ht0
        intro f hf
        have h1 : f * t0 * f⁻¹ * t0⁻¹ ∈ T ⊓ CFSG.pCore p Y := by
          refine ⟨T.mul_mem (h.torus.F_T f hf t0 ht0) (T.inv_mem ht0), ?_⟩
          have h2 : f * (t0 * d0) * f⁻¹ * (t0 * d0)⁻¹ ∈ CFSG.pCore p Y :=
            mul_mem (hOn.conj_mem _ ho f) (inv_mem ho)
          have h3 : f * (t0 * d0) * f⁻¹ * (t0 * d0)⁻¹ = f * t0 * f⁻¹ * t0⁻¹ := by
            have hfd := h.F_D f hf d0 hd0
            calc f * (t0 * d0) * f⁻¹ * (t0 * d0)⁻¹
                = f * t0 * f⁻¹ * (f * d0 * f⁻¹) * d0⁻¹ * t0⁻¹ := by group
              _ = f * t0 * f⁻¹ * t0⁻¹ := by rw [hfd]; group
          rw [h3] at h2
          exact h2
        rw [hA] at h1
        exact h1
      have hc0 : t * t0 = t0 * t := mem_centralizer_iff.mp ht0Z.2 t ht
      have hct : t * d0 = d0 * t := h.pdata.comm t ht d0 hd0
      calc t0 * d0 * t = t0 * (d0 * t) := by rw [mul_assoc]
        _ = t0 * (t * d0) := by rw [hct]
        _ = (t0 * t) * d0 := by rw [mul_assoc]
        _ = (t * t0) * d0 := by rw [hc0]
        _ = t * (t0 * d0) := by rw [mul_assoc]
    · exact inf_eq_left.mp hA

end Case2Data

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
