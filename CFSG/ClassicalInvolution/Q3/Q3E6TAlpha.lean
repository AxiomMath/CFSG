module

public import CFSG.ClassicalInvolution.Q3.Q3E6TChart
public import CFSG.ClassicalInvolution.Q3.Q3NTUnitary

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups
open Matrix

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UCtx3.conj_perm {m : ℕ} (c : UCtx3 m Ω K z) {t : G} (htz : t * z * t⁻¹ = z) :
    (∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z}) ∧
      conjSub t K = K := by
  have hconj := c.hΩ.conjInvariant
  have hconj_t : centralizingMembers Ω {z} = conjSub t '' centralizingMembers Ω {z} := by
    have := centralizingMembers_conj hconj t z
    rwa [htz] at this
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have : conjSub t L ∈ conjSub t '' centralizingMembers Ω {z} := ⟨L, hL, rfl⟩
    rwa [← hconj_t] at this
  refine ⟨hmemΩz, ?_⟩
  have hcK : IsClassicalMember3 (conjSub t K) z := by
    have := c.hz.conj t
    rwa [htz] at this
  have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
    ⟨hconj t K c.hK, isSubnormal_le hcK.subnormal⟩
  exact eq_of_locImg_le_Q₀U3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hmem
    (locImg_self_le_Q₀U3 c.hm (hconj t K c.hK) hcK c.d)

namespace TE6Chart3

variable {c : UCtx3 5 Ω K z} {nd : UNodes3 c} {Θ : Su (GaloisField 3 2) 3 1 6 →* G}

theorem conj_mem_range (hΘ : TE6Chart3 c nd Θ) {t : G} (htz : t * z * t⁻¹ = z) {y : G}
    (hy : y ∈ Θ.range) : t * y * t⁻¹ ∈ Θ.range := by
  obtain ⟨hperm, hK⟩ := UCtx3.conj_perm c htz
  have hK' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hK
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hj : ∀ i : Fin 5, ∀ y ∈ nd.j i.val, t * y * t⁻¹ ∈ Θ.range := by
    intro i y hy
    have hmem := hperm _ (nd.mem i.val (by omega))
    have hne : conjSub t (nd.j i.val) ≠ K := by
      intro h
      apply nd.ne_K i.val (by omega)
      have := congrArg (conjSub t⁻¹) h
      rwa [conjSub_inv_conjSub, hK'] at this
    obtain ⟨R, -, hRe⟩ := hΘ.cover _ hmem hne
    have : t * y * t⁻¹ ∈ conjSub t (nd.j i.val) := conj_mem_conjSub hy
    rw [hRe] at this
    exact Subgroup.map_le_range Θ R this
  have hle : (⨆ i : Fin 5, nd.j i.val) ≤ Θ.range.comap (MulAut.conj t).toMonoidHom :=
    iSup_le fun i y hy => hj i y hy
  rw [← hΘ.range_eq] at hle
  exact hle hy

theorem exists_alpha (hΘ : TE6Chart3 c nd Θ) {t : G} (htz : t * z * t⁻¹ = z) (ht2 : t * t = 1) :
    ∃ (α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6)
      (g : GL (Fin 6) (GaloisField 3 2)) (φ : GaloisField 3 2 ≃+* GaloisField 3 2),
      (∀ x, Θ (α x) = t * Θ x * t⁻¹) ∧
      (∀ x, ((α x : GL (Fin 6) (GaloisField 3 2)) : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
          φ.mapMatrix ((x : GL (Fin 6) (GaloisField 3 2)) :
            Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) *
            ((g⁻¹ : GL (Fin 6) (GaloisField 3 2)) :
              Matrix (Fin 6) (Fin 6) (GaloisField 3 2))) ∧
      ((g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)).map
        (unitaryInvolution (GaloisField 3 2) 3 1))ᵀ *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField 3 2)) = 1 ∧
      (φ = RingEquiv.refl (GaloisField 3 2) ∨ φ = unitaryInvolution (GaloisField 3 2) 3 1) ∧
        α.comp α = MonoidHom.id _ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hσ : ∀ y : G, (MulAut.conj t) ((MulAut.conj t) y) = y := fun y => by
    simp only [MulAut.conj_apply, ht']
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht2]; group
  have hstab : ∀ x, (MulAut.conj t) (Θ x) ∈ Θ.range := fun x =>
    hΘ.conj_mem_range htz ⟨x, rfl⟩
  obtain ⟨α, g, φ, h1, h2, h3, h4, h5⟩ :=
    Q3NT.unitaryAutClassification_ambient_of_odd card_gf9
      (by norm_num : (3 : ℕ) ≠ 2) le_rfl (by norm_num : 3 ≤ 6) Θ hΘ.ker_le (MulAut.conj t) hσ hstab
  exact ⟨α, g, φ, fun x => by rw [h1 x]; rfl, h2, h3, h4, h5⟩

omit [Finite G] in
theorem centralizes_of_fixed {α : Su (GaloisField 3 2) 3 1 6 →* Su (GaloisField 3 2) 3 1 6}
    {t : G} (hα : ∀ x, Θ (α x) = t * Θ x * t⁻¹) {x : Su (GaloisField 3 2) 3 1 6} (hx : α x = x) :
    t * Θ x = Θ x * t := by
  have := hα x
  rw [hx] at this
  rw [eq_mul_inv_iff_mul_eq] at this
  exact this.symm

end TE6Chart3

end CFSG.ClassicalInvolution.Q3.Q3E6T
