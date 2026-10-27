module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf62E4Slot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitE4 CFSG.ClassicalInvolution.Q3.TL4


section Lift

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem pow_four_of_q8 {J : Subgroup X} (hq : Nonempty (↥J ≃* QuaternionGroup 2)) :
    ∀ x ∈ J, x ^ 4 = 1 := by
  obtain ⟨e⟩ := hq
  intro x hx
  have hq4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have h1 : (⟨x, hx⟩ : ↥J) ^ 4 = 1 := by
    have h2 := congrArg e.symm (hq4 (e ⟨x, hx⟩))
    rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
  simpa using congrArg (fun z : ↥J => (z : X)) h1

theorem lift_commute (hC : TwinSecCtx X Φ) {N : Subgroup X} [N.Normal] (hNc : N ≤ Subgroup.center X)
    (hmeet : ∀ J ∈ Φ, J ⊓ N = ⊥) {J : Subgroup X} (hJ : J ∈ Φ) {s : X}
    (hs : IsUniqueInvolution J s) (y : X)
    (hcomm : QuotientGroup.mk' N y * QuotientGroup.mk' N s =
      QuotientGroup.mk' N s * QuotientGroup.mk' N y) : y * s = s * y := by
  have hΩ := hC.S.hyp
  have hc : CentQuotGen Φ N := centQuotGen hΩ hC.two hNc hmeet
  have hA : conjSub y J ∈ Φ := hΩ.conjInvariant y J hJ
  have hAs : IsUniqueInvolution (conjSub y J) (y * s * y⁻¹) := hs.conj y
  obtain ⟨-, -, htw⟩ := twinDatum_quot hΩ hC.two hC.q8 hNc hmeet hJ hs
  have hmem : QuotientGroup.mk' N y ∈ Subgroup.centralizer ({QuotientGroup.mk' N s} : Set (X ⧸ N)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hmapC : (conjSub y J).map (QuotientGroup.mk' N) =
      conjSub (QuotientGroup.mk' N y) (J.map (QuotientGroup.mk' N)) :=
    AscQuot.map_conjSub _ _ _
  suffices h : y * s * y⁻¹ = s by
    calc y * s = (y * s * y⁻¹) * y := by group
      _ = s * y := by rw [h]
  rcases htw _ hmem with h1 | h1
  ·
    have hAJ : conjSub y J = J := hc.eq_of_map _ hA J hJ (by rw [hmapC, h1])
    rw [hAJ] at hAs
    exact (hAs.eq hs)
  · by_cases hAJ : conjSub y J = J
    · rw [hAJ] at hAs
      exact (hAs.eq hs)
    ·
      have hle : conjSub y J ≤ Subgroup.normalizer (J : Set X) := by
        intro b hb
        refine hc.normalizer_of_map J hJ b ?_
        have hbm : QuotientGroup.mk' N b ∈ (conjSub y J).map (QuotientGroup.mk' N) :=
          Subgroup.mem_map_of_mem _ hb
        rw [hmapC] at hbm
        have hg : ∀ x ∈ J.map (QuotientGroup.mk' N),
            QuotientGroup.mk' N b * x = x * QuotientGroup.mk' N b := fun x hx => (h1 x hx _ hbm).symm
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · intro hw
          have h2 : QuotientGroup.mk' N b * w * (QuotientGroup.mk' N b)⁻¹ = w := by
            rw [hg w hw]
            group
          rw [h2]
          exact hw
        · intro hw
          have h3 := hg _ hw
          have h2 : QuotientGroup.mk' N b * w * (QuotientGroup.mk' N b)⁻¹ = w := by
            have h4 : QuotientGroup.mk' N b * (QuotientGroup.mk' N b * w * (QuotientGroup.mk' N b)⁻¹) =
                QuotientGroup.mk' N b * w := by
              rw [h3]
              group
            have := mul_left_cancel h4
            exact this
          rw [h2] at hw
          exact hw
      have hnbr : conjSub y J ∈ omegaNbr Φ J :=
        ⟨hA, hAJ, conjSub y J, TL4.mem_RSet_self hA (hC.two _ hA), le_rfl, hle⟩
      exact (hC.twin_inv hJ hnbr hs hAs).symm

end Lift

section E4

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem false_of_twinE4 (hC : TwinSecCtx X Φ)
    (hno : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z → ¬ TightInO2 z) (hE : TwinE4 X)
    (hO8 : E4O8TwinModel) (hSp : E4Sp6NC4Model) : False := by
  have hΩ := hC.S.hyp
  have hgen := hC.S.gen
  obtain ⟨Q, hQ, f, hfs, hker2, hM⟩ := hE
  have hzN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ f.ker := fun J hJ u hu huN =>
    hno J hJ u hu ⟨f.ker, inferInstance, hker2, huN⟩
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => inf_eq_bot hC.two hΩ hzN hJ
  have hNc : f.ker ≤ Subgroup.center X := center_of_meet hΩ hC.two hgen hker2 hmeet
  have hc : CentQuotGen Φ f.ker := centQuotGen hΩ hC.two hNc hmeet
  let e : (X ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : ExLie (X ⧸ f.ker) :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  obtain ⟨A, hA, A', hA', z, hnbA, hz, hz', hallA⟩ := hC.twin
  obtain ⟨hq8A, hinvA, htwA⟩ := twinDatum_quot hΩ hC.two hC.q8 hNc hmeet hA hz
  have hmapC : ∀ y : X, (conjSub y A).map (QuotientGroup.mk' f.ker) =
      conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) :=
    fun y => AscQuot.map_conjSub _ _ _
  rcases hMq with hSpM | hO8M
  ·
    obtain ⟨yb, hyb, hyb4, gb, hne, hcomm⟩ :=
      hSp (X ⧸ f.ker) hSpM (A.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) hq8A hinvA
        htwA
    obtain ⟨y, hyA, rfl⟩ := hyb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    have hJ : conjSub g A ∈ Φ := hΩ.conjInvariant g A hA
    have hJs : IsUniqueInvolution (conjSub g A) (g * z * g⁻¹) := hz.conj g
    have hcomm' : y * (g * z * g⁻¹) = (g * z * g⁻¹) * y :=
      lift_commute hC hNc hmeet hJ hJs y (by
        simp only [map_mul, map_inv]
        exact hcomm.symm)
    have hyord : orderOf y = 4 := by
      have h1 : orderOf (QuotientGroup.mk' f.ker y) ∣ orderOf y := orderOf_map_dvd _ y
      rw [hyb4] at h1
      have h2 : orderOf y ∣ 4 := orderOf_dvd_of_pow_eq_one (pow_four_of_q8 (hC.q8 A hA) y hyA)
      exact Nat.dvd_antisymm h2 h1
    refine hC.nc4 ⟨A, hA, y, hyA, hyord, conjSub g A, hJ, g * z * g⁻¹, hJs, ?_, hcomm'.symm⟩
    intro h
    apply hne
    have := congrArg (QuotientGroup.mk' f.ker) h
    simp only [map_mul, map_inv] at this
    exact this
  ·
    have hΦ : Φ = CoreAssembly.conjClass A := by
      ext J
      constructor
      · intro hJ
        exact hC.trans A hA J hJ
      · rintro ⟨g, rfl⟩
        exact hΩ.conjInvariant g A hA
    have hnbr : ∀ J, J ∈ omegaNbr Φ A ↔ J ∈ Φ ∧ J ≠ A ∧ J ≤ Subgroup.normalizer (A : Set X) := by
      intro J
      have := Vtx.mem_omegaNbr_conjClass_iff (K₀ := A) (K := A) (J := J) (hC.two A hA)
      rw [← hΦ] at this
      exact this
    have hTO : TwinOnlyNbr Φ := hC.twinOnly
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ₁A, hJ₂A, hJ₁₂, hn₁, hn₂⟩ :=
      hO8 (X ⧸ f.ker) hO8M (A.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) hq8A
        hinvA htwA
    have lift : ∀ J ∈ CoreAssembly.conjClass (A.map (QuotientGroup.mk' f.ker)),
        J ≠ A.map (QuotientGroup.mk' f.ker) →
        J ≤ Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) →
          ∃ B' ∈ omegaNbr Φ A, B'.map (QuotientGroup.mk' f.ker) = J := by
      rintro J ⟨h, rfl⟩ hne hle
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h
      have hne' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≠
          A.map (QuotientGroup.mk' f.ker) := hne
      have hle' : conjSub (QuotientGroup.mk' f.ker y) (A.map (QuotientGroup.mk' f.ker)) ≤
          Subgroup.normalizer ((A.map (QuotientGroup.mk' f.ker) : Subgroup _) : Set _) := hle
      refine ⟨conjSub y A, (hnbr _).mpr ⟨hΩ.conjInvariant y A hA, ?_, ?_⟩, hmapC y⟩
      · intro hyA
        apply hne'
        rw [← hmapC, hyA]
      · intro b hb
        refine hc.normalizer_of_map A hA b (hle' ?_)
        rw [← hmapC]
        exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨B₁, hB₁, hB₁J⟩ := lift J₁ hJ₁ hJ₁A hn₁
    obtain ⟨B₂, hB₂, hB₂J⟩ := lift J₂ hJ₂ hJ₂A hn₂
    exact hJ₁₂ (by rw [← hB₁J, ← hB₂J, hTO A hA B₁ hB₁ B₂ hB₂])

end E4

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
