module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WIso
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WR1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Disconnected.AschTight

section Struct

variable {Y : Type} [Group Y] [Finite Y]

theorem aStar_eq_of_thm3One {Δ : Set (Subgroup Y)} (hΔ : TypeRHyp Δ) {K : Subgroup Y} (hK : K ∈ Δ)
    (hgen : omegaGen (aStar Δ K) = ⊤)
    (h31 : aStar Δ K = vStar Δ K ∧
      ∀ L ∈ Δ, L ∉ vStar Δ K → ∀ M ∈ vStar Δ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M) :
    aStar Δ K = Δ := by
  refine Set.Subset.antisymm (fun J hJ => (mem_aStar_symm hK hJ).1) fun L hL => ?_
  by_contra hLA
  have hLV : L ∉ vStar Δ K := h31.1 ▸ hLA
  have hcomm : ∀ M ∈ aStar Δ K, ⁅L, M⁆ ≤ oddCoreOf L := fun M hM =>
    (h31.2 L hL hLV M (h31.1 ▸ hM)).trans inf_le_left
  have hLn : ∀ M ∈ aStar Δ K, M ≤ Subgroup.normalizer (L : Set Y) := fun M hM =>
    T3.le_normalizer_of_commutator_le (by
      rw [Subgroup.commutator_comm]
      exact (hcomm M hM).trans (oddCoreOf_le_self L))
  have hLN : Subgroup.normalizer (L : Set Y) = ⊤ := top_le_iff.mp (hgen ▸ iSup₂_le hLn)
  have hOn : (oddCoreOf L).Normal :=
    ⟨fun x hx g => Asc77.mem_normalizer_oddCoreOf_of_mem_normalizer (hLN ▸ Subgroup.mem_top g) hx⟩
  have hOY : oddCoreOf L ≤ classicalInvolutionOddCore Y := le_sSup ⟨hOn, oddCoreOf_odd_natCard L⟩
  set π := QuotientGroup.mk' (classicalInvolutionOddCore Y) with hπ
  have hC : ∀ M ∈ aStar Δ K, M ≤ (Subgroup.centralizer ((L.map π : Subgroup _) : Set _)).comap π := by
    intro M hM m hm
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 : l * m * l⁻¹ * m⁻¹ ∈ classicalInvolutionOddCore Y :=
      hOY (hcomm M hM (Subgroup.commutator_mem_commutator hl hm))
    have h2 : π (l * m * l⁻¹ * m⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    simp only [map_mul, map_inv] at h2
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h2)
  have hCtop' : (⊤ : Subgroup Y) ≤
      (Subgroup.centralizer ((L.map π : Subgroup _) : Set _)).comap π := by
    rw [← hgen]
    exact iSup₂_le hC
  have hCtop : ∀ y : Y, y ∈ (Subgroup.centralizer ((L.map π : Subgroup _) : Set _)).comap π :=
    fun y => hCtop' (Subgroup.mem_top y)
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup Y))
    (bot_le : (⊥ : Subgroup Y) ≤ L)
  obtain ⟨e⟩ := hΔ.sylow L hL P hP
  set a : Y := (e.symm (QuaternionGroup.a 1) : Y)
  set b : Y := (e.symm (QuaternionGroup.xa 0) : Y)
  have haP : a ∈ P := (e.symm _).2
  have hbP : b ∈ P := (e.symm _).2
  have hab : π a * π b = π b * π a :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (hCtop b)) (π a) ⟨a, hP.1 haP, rfl⟩
  have hc : a * b * a⁻¹ * b⁻¹ ∈ classicalInvolutionOddCore Y := by
    rw [← QuotientGroup.eq_one_iff]
    show π (a * b * a⁻¹ * b⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [hab]
    group
  have hc1 : a * b * a⁻¹ * b⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (CFSG.ComponentClassification.OddCore.odd_card Y) hc
      (hP.2.1.to_le (Subgroup.zpowers_le.mpr
        (P.mul_mem (P.mul_mem (P.mul_mem haP hbP) (P.inv_mem haP)) (P.inv_mem hbP))))
  have hab' : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
      e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := by
    apply Subtype.ext
    show a * b = b * a
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hc1, one_mul]
  rw [← map_mul, ← map_mul] at hab'
  exact absurd (e.symm.injective hab') (by decide)

end Struct

section Assembly

variable {Y : Type} [Group Y] [Finite Y]

theorem w_secQuot_iso {Δ : Set (Subgroup Y)} (hΔ : TypeRHyp Δ) {K : Subgroup Y} (hK : K ∈ Δ)
    (hA : ¬ AEmpty Δ K) (hgen : omegaGen (aStar Δ K) = ⊤)
    (h31 : aStar Δ K = vStar Δ K ∧
      ∀ L ∈ Δ, L ∉ vStar Δ K → ∀ M ∈ vStar Δ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M)
    (hrow : Thm3RowW Δ (⊤ : Subgroup Y)) : Nonempty (SecQuot (⊤ : Subgroup Y) ≃* G192) := by
  have hall := aStar_eq_of_thm3One hΔ hK hgen h31
  obtain ⟨W, hWn, hW, hD⟩ := hrow
  obtain ⟨hW4, hC⟩ :=
    w_struct hΔ hK hA hall (h31.1.symm.trans hall) (hall ▸ hgen) hW hD
  exact w_iso_of_shape hW4 hC hD

end Assembly

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
