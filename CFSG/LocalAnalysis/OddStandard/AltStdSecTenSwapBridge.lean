module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Concrete

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

@[expose] noncomputable def swapIotaHom (h : Setting G L 10) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10)) : Perm (Fin 10) →* G :=
  (L ⊔ zpowers u).subtype.comp (swapIota h d T e).toMonoidHom

theorem swapIotaHom_apply (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) (σ : Perm (Fin 10)) :
    swapIotaHom h d T e σ = (swapIota h d T e σ : G) :=
  rfl

theorem centData_swapIotaHom (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) : CentData z (swapIotaHom h d T e) where
  order := d.order
  inj := fun σ τ hστ => (swapIota h d T e).injective (Subtype.ext hστ)
  comm := fun σ =>
    (mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer h d T e σ)).symm
  ne_z := fun σ hσ =>
    z_notMem_swapComplement h d T.cent T.outer T.sq (hσ ▸ (swapIota h d T e σ).2)
  cases := fun g hg => ⟨permOf h d e hg, eq_swapIota_or h d T e hg⟩

theorem noSwapConj_swapIotaHom (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10))
    (hP : ∀ (y : G) (hy : y ∈ centralizer ({z} : Set G)), (permOf h d e hy).IsSwap →
      ¬ IsConj z y) :
    NoSwapConj z (swapIotaHom h d T e) := by
  intro σ hσ
  change ¬ IsConj z ((swapIota h d T e σ : G)) ∧
    ¬ IsConj z (z * (swapIota h d T e σ : G))
  have hz : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hy₁ : (swapIota h d T e σ : G) ∈ centralizer ({z} : Set G) :=
    swapIota_mem_centralizer h d T e σ
  have hy₂ : z * (swapIota h d T e σ : G) ∈ centralizer ({z} : Set G) := mul_mem hz hy₁
  have hπ₁ : permOf h d e hy₁ = σ := permOf_swapIota h d T e σ
  have hπ₂ : permOf h d e hy₂ = σ := by
    rw [permOf_mul h d e hz hy₁ hy₂, permOf_self, one_mul, hπ₁]
  exact ⟨hP _ hy₁ (by rw [hπ₁]; exact hσ), hP _ hy₂ (by rw [hπ₂]; exact hσ)⟩

end Concrete

section Sym

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem oneSided_of_symOutcome {x : G} (hx : x = ι τ₀)
    (hzx : z ∈ centralizer ({x} : Set G))
    (hS : SymOutcome (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) 8) :
    ∃ π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10), OneSided z ι x π := by
  obtain ⟨e, he⟩ := hS
  obtain ⟨a, b, hab, hsab⟩ := he
  have hx2 : x * x = 1 := by
    rw [hx, ← map_mul, show τ₀ * τ₀ = 1 from swap_mul_self 8 9, map_one]
  have hconj : IsConj (e.symm (QuotientGroup.mk ⟨z, hzx⟩)) τ₀ := by
    rw [hsab]
    exact Equiv.Perm.isConj_swap hab (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10) :=
    (MulAut.conj c).toMonoidHom.comp
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' (zpowers (selfC x))))
  refine ⟨π, ⟨hx, ⟨?_, ?_⟩, ?_⟩⟩
  · exact (MulAut.conj c).surjective.comp
      (e.symm.surjective.comp (QuotientGroup.mk'_surjective (zpowers (selfC x))))
  · intro c'
    have h1 : π c' = (MulAut.conj c)
        (e.symm (QuotientGroup.mk' (zpowers (selfC x)) c')) := rfl
    rw [h1, (MulAut.conj c).map_eq_one_iff, (e.symm).map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_zpowers_selfC_iff hx2
  · intro hz
    have hmk : (QuotientGroup.mk' (zpowers (selfC x)) ⟨z, hz⟩ : TwoSec x) =
        QuotientGroup.mk ⟨z, hzx⟩ := by
      rw [QuotientGroup.mk'_apply]
    have h1 : π ⟨z, hz⟩ = (MulAut.conj c)
        (e.symm (QuotientGroup.mk' (zpowers (selfC x)) ⟨z, hz⟩)) := rfl
    rw [h1, hmk, MulAut.conj_apply]
    exact hc

end Sym

end CFSG.OddStandard.AltStdSec.SwapPattern
