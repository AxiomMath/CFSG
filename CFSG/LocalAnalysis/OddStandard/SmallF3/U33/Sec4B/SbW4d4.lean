module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d3

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_conj_mem_V_of_mem_X
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) {a v : G}
    (ha : a ∈ ctxX t tau x₁ x₂) (hv : v ∈ fourGrp x₁ x₂) : a * v * a⁻¹ ∈ fourGrp x₁ x₂ := by
  have hcomm : a * v = v * a := w4_X_comm hc ha (w4_V_le_X t tau x₁ x₂ hv)
  rw [hcomm, mul_inv_cancel_right]
  exact hv

theorem w4_commutator_mem_V_of_gens
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) {g : G}
    (ht : g * t * g⁻¹ * t⁻¹ ∈ fourGrp x₁ x₂)
    (htau : g * tau * g⁻¹ * tau⁻¹ ∈ fourGrp x₁ x₂)
    (hy : g * x₁ ^ 2 * g⁻¹ * (x₁ ^ 2)⁻¹ ∈ fourGrp x₁ x₂)
    (hz : g * (x₁ * x₂) ^ 2 * g⁻¹ * ((x₁ * x₂) ^ 2)⁻¹ ∈ fourGrp x₁ x₂) :
    ∀ x ∈ ctxX t tau x₁ x₂, g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂ := by
  intro x hx
  rw [ctxX] at hx
  refine Subgroup.closure_induction
    (p := fun x _ => g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂) ?_ ?_ ?_ ?_ hx
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    exacts [ht, htau, hy, hz]
  · simpa using one_mem (fourGrp x₁ x₂)
  · intro a b ha hb pa pb
    have hconj : a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ ∈ fourGrp x₁ x₂ :=
      w4_conj_mem_V_of_mem_X hc ha pb
    have heq : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
        (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [heq]; exact mul_mem pa hconj
  · intro a ha pa
    have hconj : a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ ∈ fourGrp x₁ x₂ :=
      w4_conj_mem_V_of_mem_X hc (inv_mem ha) (inv_mem pa)
    have heq : g * a⁻¹ * g⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
    rwa [heq]

theorem w4_O_le_R
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ ≤ ctxR t tau x₁ x₂ := by
  intro g hg
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hgM : g ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hg
  obtain ⟨a, ha, hae⟩ := Set.mem_smul_set.mp (w4_conj_t_mem hc.toW4Ctx0 hgM)
  obtain ⟨b, hb, hbe⟩ := Set.mem_smul_set.mp (w4_O_conj_tau hc hg)
  simp only [smul_eq_mul] at hae hbe
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  refine ⟨hgM, ?_, fun v hv => w4_O_cent_V hc hg hv⟩
  refine w4_commutator_mem_V_of_gens hc4 ?_ ?_ ?_ ?_
  · rw [← hae, w4_t_comm_V hc4 ha, mul_inv_cancel_right]
    exact ha
  · rw [← hbe, w4_tau_comm_V hc4 hb, mul_inv_cancel_right]
    exact hb
  · rw [w4_O_cent_V hc hg hyV, mul_inv_cancel]
    exact one_mem _
  · rw [w4_O_cent_V hc hg hzV, mul_inv_cancel]
    exact one_mem _

theorem w4_R_le_O (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
  intro g hg
  obtain ⟨hgM, -, hgV⟩ := hg
  rw [hc.O_eq_C]
  refine ⟨hgM, ?_⟩
  exact Subgroup.mem_centralizer_iff.mpr (fun v hv => by
    have h := hgV v hv
    calc v * g = (g * v * g⁻¹) * g := by rw [h]
      _ = g * v := by group)

theorem w4_O_eq_R
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ = ctxR t tau x₁ x₂ :=
  le_antisymm (w4_O_le_R hc) (w4_R_le_O hc)

private theorem w4_comm_of_commutator {a b : G} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  have h1 : a * b * a⁻¹ = b := by
    have := congrArg (· * b) h
    simpa [mul_assoc] using this
  have := congrArg (· * a) h1
  simpa [mul_assoc] using this

theorem w4_mem_X_of_mem_R
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) {g : G}
    (hgR : g ∈ ctxR t tau x₁ x₂) (hgt : g * t * g⁻¹ * t⁻¹ = 1)
    (hgtau : g * tau * g⁻¹ * tau⁻¹ = 1) : g ∈ ctxX t tau x₁ x₂ := by
  rw [← S4A.centralizer_X_of hc.toCtx hc.l43 hc.l44.1, Subgroup.mem_centralizer_iff]
  have hX : ctxX t tau x₁ x₂ ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [ctxX, Subgroup.closure_le]
    intro u hu
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    have hgV : ∀ v ∈ fourGrp x₁ x₂, v * g = g * v := fun v hv => by
      have h := hgR.2.2 v hv
      calc v * g = (g * v * g⁻¹) * g := by rw [h]
        _ = g * v := by group
    rcases hu with rfl | rfl | rfl | rfl
    · exact (w4_comm_of_commutator hgt).symm
    · exact (w4_comm_of_commutator hgtau).symm
    · exact hgV _ (Subgroup.subset_closure (by simp))
    · exact hgV _ (Subgroup.subset_closure (by simp))
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hX hx)

theorem w4_exists_hom
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ∃ φ : ↥(ctxR t tau x₁ x₂) →* ↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂),
      ∀ g : ↥(ctxR t tau x₁ x₂), φ g = 1 → (g : G) ∈ ctxX t tau x₁ x₂ := by
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := (hc.wreath.fourGrp_eq_omega).2.1.1
  refine ⟨MonoidHom.mk' (fun g : ↥(ctxR t tau x₁ x₂) =>
      (⟨(g : G) * t * (g : G)⁻¹ * t⁻¹, g.2.2.1 t htX⟩,
       ⟨(g : G) * tau * (g : G)⁻¹ * tau⁻¹, g.2.2.1 tau htauX⟩)) ?_, ?_⟩
  · intro g h
    apply Prod.ext
    · apply Subtype.ext
      have hfix : (g : G) * ((h : G) * t * (h : G)⁻¹ * t⁻¹) * (g : G)⁻¹ =
          (h : G) * t * (h : G)⁻¹ * t⁻¹ :=
        g.2.2.2 _ (h.2.2.1 t htX)
      show (g : G) * (h : G) * t * ((g : G) * (h : G))⁻¹ * t⁻¹ =
          ((g : G) * t * (g : G)⁻¹ * t⁻¹) * ((h : G) * t * (h : G)⁻¹ * t⁻¹)
      rw [show (g : G) * (h : G) * t * ((g : G) * (h : G))⁻¹ * t⁻¹ =
          ((g : G) * ((h : G) * t * (h : G)⁻¹ * t⁻¹) * (g : G)⁻¹) *
            ((g : G) * t * (g : G)⁻¹ * t⁻¹) by group, hfix]
      exact congrArg Subtype.val (mul_comm'
        (⟨_, h.2.2.1 t htX⟩ : ↥(fourGrp x₁ x₂))
        (⟨_, g.2.2.1 t htX⟩ : ↥(fourGrp x₁ x₂)))
    · apply Subtype.ext
      have hfix : (g : G) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹) * (g : G)⁻¹ =
          (h : G) * tau * (h : G)⁻¹ * tau⁻¹ :=
        g.2.2.2 _ (h.2.2.1 tau htauX)
      show (g : G) * (h : G) * tau * ((g : G) * (h : G))⁻¹ * tau⁻¹ =
          ((g : G) * tau * (g : G)⁻¹ * tau⁻¹) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹)
      rw [show (g : G) * (h : G) * tau * ((g : G) * (h : G))⁻¹ * tau⁻¹ =
          ((g : G) * ((h : G) * tau * (h : G)⁻¹ * tau⁻¹) * (g : G)⁻¹) *
            ((g : G) * tau * (g : G)⁻¹ * tau⁻¹) by group, hfix]
      exact congrArg Subtype.val (mul_comm'
        (⟨_, h.2.2.1 tau htauX⟩ : ↥(fourGrp x₁ x₂))
        (⟨_, g.2.2.1 tau htauX⟩ : ↥(fourGrp x₁ x₂)))
  · intro g hg1
    have hct1 : (⟨(g : G) * t * (g : G)⁻¹ * t⁻¹, g.2.2.1 t htX⟩ :
        ↥(fourGrp x₁ x₂)) = 1 := by
      simpa using congrArg Prod.fst hg1
    have hctau1 : (⟨(g : G) * tau * (g : G)⁻¹ * tau⁻¹, g.2.2.1 tau htauX⟩ :
        ↥(fourGrp x₁ x₂)) = 1 := by
      simpa using congrArg Prod.snd hg1
    have hgt : (g : G) * t * (g : G)⁻¹ * t⁻¹ = 1 := by
      have := congrArg Subtype.val hct1
      simpa using this
    have hgtau : (g : G) * tau * (g : G)⁻¹ * tau⁻¹ = 1 := by
      have := congrArg Subtype.val hctau1
      simpa using this
    exact w4_mem_X_of_mem_R hc g.2 hgt hgtau

theorem w4_R_quot
    (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    (∀ a ∈ ctxR t tau x₁ x₂, a ^ 2 ∈ ctxX t tau x₁ x₂) ∧
      ∀ a ∈ ctxR t tau x₁ x₂, ∀ b ∈ ctxR t tau x₁ x₂,
        a * b * a⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂ := by
  obtain ⟨φ, hφ⟩ := w4_exists_hom hc
  haveI : IsMulCommutative ↥(fourGrp x₁ x₂) := (hc.wreath.fourGrp_eq_omega).2.1.1
  have hExpV : ∀ x ∈ fourGrp x₁ x₂, x ^ 2 = 1 :=
    fun x hx => (hc.wreath.fourGrp_eq_omega.2.1).2 x hx
  have hsq_prod : ∀ z : ↥(fourGrp x₁ x₂) × ↥(fourGrp x₁ x₂), z ^ 2 = 1 := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      simpa [Subgroup.coe_pow] using hExpV (z.1 : G) z.1.2
    · apply Subtype.ext
      simpa [Subgroup.coe_pow] using hExpV (z.2 : G) z.2.2
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · let a' : ↥(ctxR t tau x₁ x₂) := ⟨a, ha⟩
    have h1 : φ (a' ^ 2) = 1 := by
      rw [map_pow]
      exact hsq_prod (φ a')
    have hmem : ((a' ^ 2 : ↥(ctxR t tau x₁ x₂)) : G) ∈ ctxX t tau x₁ x₂ := hφ (a' ^ 2) h1
    simpa [a', Subgroup.coe_pow, pow_two] using hmem
  · let a' : ↥(ctxR t tau x₁ x₂) := ⟨a, ha⟩
    let b' : ↥(ctxR t tau x₁ x₂) := ⟨b, hb⟩
    have h1 : φ (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_comm' (φ a') (φ b')]
      group
    have hmem : ((a' * b' * a'⁻¹ * b'⁻¹ : ↥(ctxR t tau x₁ x₂)) : G) ∈ ctxX t tau x₁ x₂ :=
      hφ (a' * b' * a'⁻¹ * b'⁻¹) h1
    simpa [a', b', Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem w4_O_quot
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    (∀ a ∈ ctxO t tau x₁ x₂, a ^ 2 ∈ ctxX t tau x₁ x₂) ∧
      ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂ := by
  have hq := w4_R_quot hc.toCtx10.toCtx4
  exact ⟨fun a ha => hq.1 a (w4_O_le_R hc ha),
    fun a ha b hb => hq.2 a (w4_O_le_R hc ha) b (w4_O_le_R hc hb)⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
