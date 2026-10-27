module

public import CFSG.ClassicalInvolution.Q3.TL3S8Mu
public import CFSG.ClassicalInvolution.Q3.TL3DichMain

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.eq_top_of_normal_le (hd : TightDatum R S t) (hgen : TightSelfGen R)
    {M : Subgroup Y} (hMn : M.Normal) (hSM : (S : Subgroup R).map R.subtype ≤ M) : M = ⊤ :=
  hd.eq_top_of_conj hgen fun y x hx => by
    rw [mem_conjSub_iff] at hx
    have := hMn.conj_mem _ (hSM hx) y
    rwa [show y * (y⁻¹ * x * y) * y⁻¹ = x by group] at this

theorem TightDatum.genFittingFStar_eq_top_of_le (hd : TightDatum R S t) (hgen : TightSelfGen R)
    (h : (S : Subgroup R).map R.subtype ≤ genFittingFStar Y) : genFittingFStar Y = ⊤ :=
  TightDatum.eq_top_of_normal_le hd hgen (genFittingFStar_normal Y) h

theorem TightDatum.edgeless_of_forall (hd : TightDatum R S t)
    (h : ∀ P ∈ RSet (CoreAssembly.conjClass (tightCore R)),
      P ≤ Subgroup.centralizer ({t} : Set Y) → t ∈ P) : TightEdgeless R := by
  have hΩ := hd.hypOmegaGen
  have huniq := hd.isUniqueInvolution_core
  have key : ∀ K ∈ CoreAssembly.conjClass (tightCore R),
      ∀ J ∈ CoreAssembly.conjClass (tightCore R),
        J ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) K := by
    rintro K hK J hJ ⟨-, hne, P, hP, hPJ, hPN⟩
    obtain ⟨a, rfl⟩ := CoreAssembly.single_class (tightCore R) K hK
    have hP' : conjSub a⁻¹ P ≤ Subgroup.centralizer ({t} : Set Y) := by
      intro x hx
      rw [mem_conjSub_iff, inv_inv] at hx
      have h1 := (huniq.conj a).conj_eq (conjSub_eq_of_mem_normalizer (hPN hx))
      have h2 : x * t * x⁻¹ = t := by
        have h3 : a * (x * t * x⁻¹) * a⁻¹ = a * t * a⁻¹ := by
          calc a * (x * t * x⁻¹) * a⁻¹
              = a * x * a⁻¹ * (a * t * a⁻¹) * (a * x * a⁻¹)⁻¹ := by group
            _ = a * t * a⁻¹ := h1
        have := congrArg (fun w => a⁻¹ * w * a) h3
        simpa [mul_assoc] using this
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * t = x * t * x⁻¹ * x := by group
        _ = t * x := by rw [h2]
    have ht : t ∈ conjSub a⁻¹ P := h _ (Q3CL.Thompson.conjSub_mem_RSet hΩ hP a⁻¹) hP'
    rw [mem_conjSub_iff, inv_inv] at ht
    obtain ⟨u, hu⟩ := hd.exists_isUniqueInvolution_member hJ
    have hau : a * t * a⁻¹ = u :=
      (hu.unique _ (hPJ ht) (huniq.conj a).sq).resolve_left (huniq.conj a).ne_one
    exact hne (hd.eq_of_isUniqueInvolution_member hJ hK hu (hau ▸ huniq.conj a))
  rintro K hK J hJ (h1 | h1)
  · exact key K hK J hJ h1
  · exact key J hJ K hK h1

theorem TightDatum.not_acts3_of_forall (hd : TightDatum R S t)
    (h : ∀ x ∈ Subgroup.centralizer ({t} : Set Y), ∀ k : ℕ, x ^ 3 ^ k = 1 →
      ∃ o ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)),
        ∃ c ∈ Subgroup.centralizer (R : Set Y), x = o * c) : ¬ TightActs3 R t := by
  rintro ⟨x, k, hxC, hx3, r, hr, hxr⟩
  obtain ⟨o, ho, c, hc, rfl⟩ := h x hxC k hx3
  apply hxr
  have hcr : c * r = r * c := (Subgroup.mem_centralizer_iff.mp hc r hr).symm
  have heq : ⁅o * c, r⁆ = o * (r * o⁻¹ * r⁻¹) := by
    rw [commutatorElement_def]
    calc o * c * r * (o * c)⁻¹ * r⁻¹ = o * (c * r) * c⁻¹ * o⁻¹ * r⁻¹ := by group
      _ = o * (r * c) * c⁻¹ * o⁻¹ * r⁻¹ := by rw [hcr]
      _ = o * (r * o⁻¹ * r⁻¹) := by group
  have hoC : o ∈ Subgroup.centralizer ({t} : Set Y) := oddCoreImg_le _ ho
  have hrC : r ∈ Subgroup.centralizer ({t} : Set Y) := hd.cent hr
  have hmemO : ⁅o * c, r⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y)) := by
    rw [heq]
    exact Subgroup.mul_mem _ ho
      (conj_mem_oddCoreImg (Subgroup.le_normalizer hrC) (Subgroup.inv_mem _ ho))
  have hmemR : ⁅o * c, r⁆ ∈ R := by
    rw [heq, show o * (r * o⁻¹ * r⁻¹) = o * r * o⁻¹ * r⁻¹ by group]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hd.le_normalizer hoC) r).mp hr)
      (R.inv_mem hr)
  exact mem_oddCoreImg_of_le hd.cent hmemR hmemO

end CFSG.ClassicalInvolution.Q3.TA3
