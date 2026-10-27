module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBY
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreMacW

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A} {k : A} (h2 : Δ.CaseTwo k) (φ : Δ.Fusion)

include h2 in
theorem exists_TwoBY
    (hX : ¬ SectionalRankLeFour X) (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) :
    Nonempty (TwoBY φ) := by
  obtain ⟨Y, hYT, hYn, hYel, hY8, v, hvY, hv1, hvS, hvc, hvx⟩ := φ.exists_Y hX
  have htzY : Δ.t * Δ.dz ∈ Y := by
    rw [← TwoB_center_eq h2 φ hD1 hvS hvc hvx (hYel.sq_eq_one v hvY) hv1]
    exact hvY
  have htY := TwoB_t_mem_Y h2 φ hD1 hYT hYn hYel hY8 htzY
  have hzY : Δ.dz ∈ Y := by
    have := mul_mem (inv_mem htY) htzY
    rwa [inv_mul_cancel_left] at this
  exact ⟨⟨Y, hYT, hYn, hYel, hY8, htY, hzY, fun y hy =>
    Δ.mem_S_of_commute_t φ.isPGroup φ.le (hYT hy) (hYel.comm y hy _ htY)⟩⟩

namespace TwoBY

variable {φ} (YD : TwoBY φ)

omit [Finite X] in
theorem conj_mem {y : X} (hy : y ∈ YD.Y) : φ.x * y * φ.x⁻¹ ∈ YD.Y := YD.normal _ φ.mem y hy

omit [Finite X] in
theorem conj_inv_mem {y : X} (hy : y ∈ YD.Y) : φ.x⁻¹ * y * φ.x ∈ YD.Y := by
  simpa using YD.normal _ (inv_mem φ.mem) y hy

omit [Finite X] in
theorem conj_S {s : X} (hs : s ∈ Δ.S) {y : X} (hy : y ∈ YD.Y) : s * y * s⁻¹ ∈ YD.Y :=
  YD.normal _ (φ.le hs) y hy

theorem eq_E8 {y : X} (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz)
    (hytz : y ≠ Δ.t * Δ.dz) : zpowers Δ.t ⊔ zpowers Δ.dz ⊔ zpowers y = YD.Y := by
  have htz1 : Δ.dz ≠ Δ.t := fun h => Δ.t_not_mem_D (h ▸ Δ.dz_mem)
  exact E8_eq YD.card YD.t_mem YD.dz_mem hy (card_E8 Δ.t_sq Δ.dz_sq (YD.elem.sq_eq_one y hy)
    (Δ.commute_t (Δ.D_le Δ.dz_mem)).symm (YD.elem.comm _ YD.t_mem _ hy)
    (YD.elem.comm _ YD.dz_mem _ hy) Δ.t_ne_one Δ.dz_ne_one htz1 ⟨hy1, hyt, hyz, hytz⟩)

theorem cases {y : X} (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz)
    (hytz : y ≠ Δ.t * Δ.dz) {y' : X} (hy' : y' ∈ YD.Y) :
    (y' = 1 ∨ y' = Δ.t ∨ y' = Δ.dz ∨ y' = Δ.t * Δ.dz) ∨
      (y' = y ∨ y' = Δ.t * y ∨ y' = Δ.dz * y ∨ y' = Δ.t * Δ.dz * y) := by
  rw [← YD.eq_E8 hy hy1 hyt hyz hytz] at hy'
  exact mem_E8_cases Δ.t_sq Δ.dz_sq (YD.elem.sq_eq_one y hy) (Δ.commute_t (Δ.D_le Δ.dz_mem)).symm
    (YD.elem.comm _ YD.t_mem _ hy) (YD.elem.comm _ YD.dz_mem _ hy) hy'

theorem ψe_cases {y : X} (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz)
    (hytz : y ≠ Δ.t * Δ.dz) {y' : X} (hy' : y' ∈ YD.Y) :
    Δ.ψe y' = 1 ∨ Δ.ψe y' = Δ.ψe Δ.dz ∨ Δ.ψe y' = Δ.ψe y ∨
      Δ.ψe y' = Δ.ψe Δ.dz * Δ.ψe y := by
  have hzS := Δ.D_le Δ.dz_mem
  have hyS := YD.le_S hy
  rcases YD.cases hy hy1 hyt hyz hytz hy' with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact Or.inl Δ.ψe_one
  · exact Or.inl Δ.ψe_t
  · exact Or.inr (Or.inl rfl)
  · right; left; rw [Δ.ψe_mul Δ.t_mem hzS, Δ.ψe_t, one_mul]
  · right; right; left; rfl
  · right; right; left; rw [Δ.ψe_mul Δ.t_mem hyS, Δ.ψe_t, one_mul]
  · right; right; right; rw [Δ.ψe_mul hzS hyS]
  · right; right; right
    rw [Δ.ψe_mul (mul_mem Δ.t_mem hzS) hyS, Δ.ψe_mul Δ.t_mem hzS, Δ.ψe_t, one_mul]

include h2 in
theorem false_of_Dbar (hD1 : ∀ u ∈ Δ.D, φ.x⁻¹ * u * φ.x ∈ Δ.D → u = 1) {y : X}
    (hy : y ∈ YD.Y) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) (hyz : y ≠ Δ.dz) (hytz : y ≠ Δ.t * Δ.dz)
    (hyD : Δ.ψe y ∈ Δ.Dbar) : False := by
  have hxt := TwoB_conj_t h2 φ hD1
  have hxt' : φ.x⁻¹ * Δ.t * φ.x = Δ.dz := by rw [← TwoB_conj_dz h2 φ hD1]; group
  obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD (YD.le_S hy) hyD
  have hqd : q * d = d * q := Δ.commute_of_mem_Q_D hq hd
  have hy2 := YD.elem.sq_eq_one _ hy
  rw [(show Commute q d from hqd).mul_pow] at hy2
  have hq2 : q ^ 2 = 1 := by
    have hmem : q ^ 2 ∈ Δ.D := by
      rw [show q ^ 2 = (d ^ 2)⁻¹ by rw [← mul_eq_one_iff_eq_inv.mp hy2]]
      exact inv_mem (pow_mem hd 2)
    exact Δ.eq_one_of_mem_Q_D (pow_mem hq 2) hmem
  have hd2 : d ^ 2 = 1 := by rw [hq2, one_mul] at hy2; exact hy2
  have hqY : q ∈ YD.Y := by
    by_cases hq1 : q = 1
    · rw [hq1]; exact one_mem _
    · rw [Δ.eq_t_of_mem_Q hq hq2 hq1]; exact YD.t_mem
  have hdY : d ∈ YD.Y := by
    have := mul_mem (inv_mem hqY) hy
    rwa [inv_mul_cancel_left] at this
  have hd1 : d ≠ 1 := fun h => by
    rw [h, mul_one] at hyt hy1
    exact (by
      by_cases hq1 : q = 1
      · exact hy1 hq1
      · exact hyt (Δ.eq_t_of_mem_Q hq hq2 hq1))
  have hdz : d ≠ Δ.dz := fun h => by
    rw [h] at hyz hytz
    by_cases hq1 : q = 1
    · exact hyz (by rw [hq1, one_mul])
    · exact hytz (by rw [Δ.eq_t_of_mem_Q hq hq2 hq1])
  have hdt : d ≠ Δ.t := fun h => Δ.t_not_mem_D (h ▸ hd)
  have hdtz : d ≠ Δ.t * Δ.dz := fun h => Δ.t_not_mem_D (by
    have := mul_mem (h ▸ hd) (inv_mem Δ.dz_mem)
    rwa [mul_inv_cancel_right] at this)
  have hA : ∀ d' ∈ Δ.D, φ.x * d * φ.x⁻¹ = d' → False := fun d' hd' h => by
    have := hD1 d' hd' (by rw [← h]; simpa [mul_assoc] using hd)
    rw [this] at h
    apply hd1
    calc d = φ.x⁻¹ * (φ.x * d * φ.x⁻¹) * φ.x := by group
      _ = 1 := by rw [h]; group
  have hB : ∀ d' ∈ Δ.D, φ.x * d * φ.x⁻¹ = Δ.t * d' → False := fun d' hd' h => by
    have h0 : φ.x⁻¹ * (Δ.t * d') * φ.x = d := by
      calc φ.x⁻¹ * (Δ.t * d') * φ.x = φ.x⁻¹ * (φ.x * d * φ.x⁻¹) * φ.x := by rw [h]
        _ = d := by group
    have h' : φ.x⁻¹ * d' * φ.x = Δ.dz⁻¹ * d := by
      calc φ.x⁻¹ * d' * φ.x = (φ.x⁻¹ * Δ.t * φ.x)⁻¹ * (φ.x⁻¹ * (Δ.t * d') * φ.x) := by group
        _ = Δ.dz⁻¹ * d := by rw [hxt', h0]
    have := hD1 d' hd' (by rw [h']; exact mul_mem (inv_mem Δ.dz_mem) hd)
    rw [this, mul_one] at h
    apply hdz
    calc d = φ.x⁻¹ * (φ.x * d * φ.x⁻¹) * φ.x := by group
      _ = Δ.dz := by rw [h, hxt']
  rcases YD.cases hdY hd1 hdt hdz hdtz (YD.conj_mem hdY) with
    (h | h | h | h) | (h | h | h | h)
  · exact hA 1 (one_mem _) h
  · exact hB 1 (one_mem _) (by rw [h, mul_one])
  · exact hA _ Δ.dz_mem h
  · exact hB _ Δ.dz_mem h
  · exact hA _ hd h
  · exact hB _ hd h
  · exact hA _ (mul_mem Δ.dz_mem hd) h
  · exact hB _ (mul_mem Δ.dz_mem hd) (by rw [h, mul_assoc])

end TwoBY

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
