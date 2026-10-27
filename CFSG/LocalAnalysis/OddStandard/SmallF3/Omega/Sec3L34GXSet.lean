module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrInnerY
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTInd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_x_cover [Finite G] {H : Subgroup G} (hH : InFStar H) :
    OddCentralCover (QuotientGroup.mk' (oddCore ↥H)) :=
  oddCentralCover_quotient_oddCore (inFStar_isQuasisimple hH) (MulEquiv.refl _)

theorem l34g_x_induced [Finite G] {H : Subgroup G} {x : G} (hx : x * x = 1)
    (hxN : x ∈ normalizer (H : Set G)) :
    ∃ α : MulAut (↥H ⧸ oddCore ↥H), α * α = 1 ∧
      ∀ a : ↥H, (QuotientGroup.mk (conjAut H hx hxN a) : ↥H ⧸ oddCore ↥H) =
        α (QuotientGroup.mk a) := by
  obtain ⟨α, hα, hα2⟩ := sec63PT_exists_induced_aut_quotient
    (MulEquiv.refl (↥H ⧸ oddCore ↥H)) (conjAut_mul_self H hx hxN)
  exact ⟨α, hα2, hα⟩

theorem l34g_x_starQuotient [Finite G] {H : Subgroup G} (hH : InFStar H) :
    L34GStarQuotient (↥H ⧸ oddCore ↥H) := by
  have hq : CFSG.IsQuasisimple ↥H := inFStar_isQuasisimple hH
  unfold InFStar IsFStarGroup IsFGroup at hH
  rcases hH with ⟨-, hQ | hQ⟩ | ⟨-, hS⟩
  · exact Or.inl (Or.inl hQ)
  · exact Or.inr ⟨isQuasisimple_quotient_oddCore hq, hQ⟩
  · exact Or.inl (Or.inr hS)

private theorem l34g_x_mem_normalizer_of_mem {H : Subgroup G} {y : G} (hyH : y ∈ H) :
    y ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact H.mul_mem (H.mul_mem hyH hn) (H.inv_mem hyH)
  · intro hn
    have h2 : y⁻¹ * (y * n * y⁻¹) * y ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hyH) hn) hyH
    rwa [show y⁻¹ * (y * n * y⁻¹) * y = n by group] at h2

private theorem l34g_x_centralizes_of_conj_eq {H : Subgroup G} {y t : G} (hy : y * y = 1)
    (ht : t * t = 1) (hval : ∀ a : ↥H, y * (t * (a : G) * t⁻¹) * y⁻¹ = (a : G)) :
    y⁻¹ * t ∈ centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hval' : y * (t * a * t⁻¹) * y⁻¹ = a := by
    simpa using hval ⟨a, ha⟩
  have hyt : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hta : t * a * t⁻¹ = y⁻¹ * a * y := by
    calc t * a * t⁻¹ = y⁻¹ * (y * (t * a * t⁻¹) * y⁻¹) * y := by group
      _ = y⁻¹ * a * y := by rw [hval']
  have h1' : t * a * t = y * a * y := by
    rw [hti] at hta
    rw [hyt] at hta
    exact hta
  have hcomm : (y * t) * a = a * (y * t) := by
    calc (y * t) * a = y * (t * a) := by group
      _ = y * (t * a) * (t * t) := by rw [ht]; group
      _ = y * (t * a * t) * t := by group
      _ = y * (y * a * y) * t := by rw [h1']
      _ = (y * y) * a * (y * t) := by group
      _ = a * (y * t) := by rw [hy]; group
  rw [hyt]
  exact hcomm.symm

theorem l34g_x_induced_ne_conj [Finite G] {H : Subgroup G} (hH : InFStar H) {y t : G}
    (hyH : y ∈ H) (hy : y * y = 1) (ht : t * t = 1) (htN : t ∈ normalizer (H : Set G))
    (hty : ∀ c ∈ centralizer (H : Set G), t ≠ y * c)
    {α : MulAut (↥H ⧸ oddCore ↥H)}
    (hα : ∀ a : ↥H, (QuotientGroup.mk (conjAut H ht htN a) : ↥H ⧸ oddCore ↥H) =
      α (QuotientGroup.mk a)) :
    α ≠ MulAut.conj (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ oddCore ↥H) := by
  intro hconj
  have hyN : y ∈ normalizer (H : Set G) := l34g_x_mem_normalizer_of_mem hyH
  let ρ : ↥H →* ↥H ⧸ oddCore ↥H := QuotientGroup.mk' (oddCore ↥H)
  let ybar : ↥H ⧸ oddCore ↥H := ρ ⟨y, hyH⟩
  have hρ : ρ = QuotientGroup.mk' (oddCore ↥H) := rfl
  have hybardef : ybar = ρ ⟨y, hyH⟩ := rfl
  have hyy : (⟨y, hyH⟩ : ↥H) * ⟨y, hyH⟩ = 1 := by
    apply Subtype.ext
    simpa using hy
  have hcomp : ∀ b : ↥H,
      conjAut H hy hyN b = (⟨y, hyH⟩ : ↥H) * b * (⟨y, hyH⟩ : ↥H)⁻¹ := by
    intro b
    apply Subtype.ext
    simp [coe_conjAut]
  have hσy : ∀ b : ↥H, ρ (conjAut H hy hyN b) = ybar * ρ b * ybar⁻¹ := by
    intro b
    rw [hcomp b, map_mul, map_mul, map_inv, hybardef]
  have hσt : ∀ b : ↥H, ρ (conjAut H ht htN b) = ybar * ρ b * ybar⁻¹ := by
    intro b
    have hb : ρ (conjAut H ht htN b) = α (ρ b) := by
      rw [hρ]
      simpa only [QuotientGroup.mk'_apply] using hα b
    rw [hb, hconj, MulAut.conj_apply, hybardef]
    simp only [hρ, QuotientGroup.mk'_apply]
  have hybar : ybar * ybar = 1 := by
    rw [hybardef]
    rw [← map_mul, hyy, map_one]
  have hker : ρ.ker ≤ center ↥H := by
    show (QuotientGroup.mk' (oddCore ↥H)).ker ≤ center ↥H
    exact (l34g_x_cover hH).ker_le_center
  have hperf : commutator ↥H = ⊤ := (inFStar_isQuasisimple hH).1.commutator_eq_top
  have hσ : ∀ a : ↥H,
      ρ ((conjAut H hy hyN * conjAut H ht htN) a) = ρ a := by
    intro a
    rw [MulAut.mul_apply, hσy, hσt]
    have hi : ybar⁻¹ = ybar := inv_eq_of_mul_eq_one_right hybar
    rw [hi]
    calc ybar * (ybar * ρ a * ybar) * ybar = (ybar * ybar) * ρ a * (ybar * ybar) := by group
      _ = ρ a := by rw [hybar]; group
  have h1 : conjAut H hy hyN * conjAut H ht htN = 1 :=
    sec63PT_eq_one_of_induced_eq_one hker hperf hσ
  have hval : ∀ a : ↥H, y * (t * (a : G) * t⁻¹) * y⁻¹ = (a : G) := by
    intro a
    have h2 : ((conjAut H hy hyN * conjAut H ht htN) a : ↥H) = a := by
      rw [h1, MulAut.one_apply]
    have h3 := congrArg Subtype.val h2
    rw [MulAut.mul_apply, coe_conjAut, coe_conjAut] at h3
    exact h3
  have hc : y⁻¹ * t ∈ centralizer (H : Set G) := l34g_x_centralizes_of_conj_eq hy ht hval
  exact hty (y⁻¹ * t) hc (by group)

end CFSG.OddStandard.SmallF3.Omega
