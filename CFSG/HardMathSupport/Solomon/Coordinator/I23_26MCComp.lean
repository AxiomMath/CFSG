module

public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26MCAbs
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Component
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open
open scoped commutatorElement

section Basic

theorem mc_commutator_eq_of_qs {Y : Type*} [Group Y] {K : Subgroup Y}
    (hK : CFSG.Open.IsQuasisimple ↥K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) hK.1
  rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h

theorem mc_normal_le_center_or_top {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hQ
  have hnorm : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · left
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center Q) x ∈ N.map (QuotientGroup.mk' (Subgroup.center Q)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  · right
    have h1 : N ⊔ Subgroup.center Q = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center Q))) h
      rwa [Subgroup.comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
    rw [eq_top_iff]
    calc (⊤ : Subgroup Q) = commutator Q := hperf.symm
      _ = ⁅(⊤ : Subgroup Q), ⊤⁆ := commutator_def Q
      _ ≤ N := by
        rw [Subgroup.commutator_le]
        intro g₁ _ g₂ _
        have hg₁ : g₁ ∈ N ⊔ Subgroup.center Q := h1 ▸ Subgroup.mem_top g₁
        have hg₂ : g₂ ∈ N ⊔ Subgroup.center Q := h1 ▸ Subgroup.mem_top g₂
        obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg₁
        obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg₂
        rw [mc_comm_central hz₁ hz₂, commutatorElement_def]
        exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)

end Basic

section Component

variable {Y : Type*} [Group Y] [Finite Y]

theorem mc_glaPComponent_three {S D : Subgroup Y} (hDS : D ≤ S) (hn : (D.subgroupOf S).Normal)
    (hq : CFSG.Open.IsQuasisimple ↥D) (h3 : 3 ∣ Nat.card D) : GLAPComponent 3 S D := by
  classical
  let O : Subgroup ↥S := GLAPPrimeCore 3 ↥S
  let π : ↥S →* ↥S ⧸ O := QuotientGroup.mk' O
  let φ : ↥D →* ↥S ⧸ O := π.comp (Subgroup.inclusion hDS)
  have hcop : Nat.Coprime 3 (Nat.card O) :=
    GL83.PiGen.coprime_card_glaPPrimeCore Nat.prime_three ↥S
  have hφ : ∀ d : ↥D, φ d = 1 ↔ (⟨d, hDS d.2⟩ : ↥S) ∈ O := fun d => by
    show QuotientGroup.mk' O (Subgroup.inclusion hDS d) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hker : φ.ker ≤ Subgroup.center ↥D := by
    rcases mc_normal_le_center_or_top hq φ.ker with h | h
    · exact h
    · exfalso
      have hDO : D.subgroupOf S ≤ O := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥D) ∈ φ.ker := by rw [h]; trivial
        exact (hφ ⟨x, hx⟩).1 (MonoidHom.mem_ker.1 hx')
      have e0 : ↥(D.subgroupOf S) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDS
      have hdvd : 3 ∣ Nat.card O :=
        h3.trans ((Nat.card_congr e0.toEquiv).symm ▸ Subgroup.card_dvd_of_le hDO)
      exact Nat.prime_three.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hrange : (D.subgroupOf S).map π = φ.range := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨⟨d, hDS d.2⟩, d.2, rfl⟩
  have hqφ : CFSG.Open.IsQuasisimple ↥φ.range := by
    have h1 : CFSG.IsQuasisimple ↥D := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq
    have h2 : CFSG.IsQuasisimple ↥φ.range :=
      CFSG.LocalCores.isQuasisimple_of_surjective h1 φ.rangeRestrict φ.rangeRestrict_surjective
        (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp h2
  refine ⟨hDS, IsSubnormal.step hDS hn (IsSubnormal.refl S), ⟨le_top, ?_, ?_⟩, ?_⟩
  · refine IsSubnormal.step le_top ?_ (IsSubnormal.refl _)
    have : ((D.subgroupOf S).map π).Normal :=
      Subgroup.Normal.map hn π (QuotientGroup.mk'_surjective O)
    infer_instance
  · rw [hrange]
    exact hqφ
  · intro J hJD _ heq
    have hperf := mc_commutator_eq_of_qs hq
    have hJdec : ∀ d ∈ D, ∃ j ∈ J, ∃ z ∈ D, (∀ x ∈ D, x * z = z * x) ∧ d = j * z := by
      intro d hd
      have h1 : π ⟨d, hDS hd⟩ ∈ (J.subgroupOf S).map π := by
        change π ⟨d, hDS hd⟩ ∈ (J.subgroupOf S).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)) at *
        rw [heq]
        exact ⟨⟨d, hDS hd⟩, hd, rfl⟩
      obtain ⟨j', hj', hjπ⟩ := h1
      have hz : j'⁻¹ * ⟨d, hDS hd⟩ ∈ O := by
        have := (QuotientGroup.eq (s := O)).1 hjπ
        exact this
      have hjD : (j' : Y) ∈ D := hJD.le hj'
      have hzD : (j' : Y)⁻¹ * d ∈ D := D.mul_mem (D.inv_mem hjD) hd
      have hker' : (⟨(j' : Y)⁻¹ * d, hzD⟩ : ↥D) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hφ]
        exact hz
      have hcen := Subgroup.mem_center_iff.1 (hker hker')
      refine ⟨j', hj', (j' : Y)⁻¹ * d, hzD, fun x hx => ?_, by group⟩
      exact congrArg Subtype.val (hcen ⟨x, hx⟩)
    have hDJ : D ≤ J := by
      calc D = ⁅D, D⁆ := hperf.symm
        _ ≤ J := by
          rw [Subgroup.commutator_le]
          intro d₁ hd₁ d₂ hd₂
          obtain ⟨j₁, hj₁, z₁, hz₁, hc₁, rfl⟩ := hJdec d₁ hd₁
          obtain ⟨j₂, hj₂, z₂, hz₂, hc₂, rfl⟩ := hJdec d₂ hd₂
          have hj₁D : j₁ ∈ D := hJD.le hj₁
          have hj₂D : j₂ ∈ D := hJD.le hj₂
          rw [mc_comm_mul_mul (a := j₁) (b := j₂) (z₁ := z₁) (z₂ := z₂)
            (hc₁ j₂ hj₂D).symm (hc₁ z₂ hz₂).symm (hc₂ j₁ hj₁D).symm, commutatorElement_def]
          exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
    exact absurd hDJ (not_le_of_gt hJD)

end Component

end CFSG.HardMathSupport.Solomon.Coordinator
