module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem z4j_subgroupOf_closure {K : Subgroup G} (S : Set ↥K) :
    (closure (Subtype.val '' S : Set G)).subgroupOf K = closure S := by
  have hmap : (closure S).map K.subtype = closure (Subtype.val '' S : Set G) := by
    simpa only [Subgroup.coe_subtype] using MonoidHom.map_closure K.subtype S
  rw [← hmap]
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
    obtain ⟨a, ha, hax⟩ := hx
    have hax' : a = x := Subtype.ext hax
    rwa [← hax']
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact ⟨x, hx, rfl⟩

namespace Ctx4Z

@[expose] def z4jY (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨x₁ ^ 2, hz.z4i_Q_le_NQ (pow_mem hz.x₁_mem_Q 2)⟩

@[expose] def z4jZ (hz : Ctx4Z t L S x₁ x₂ lam rho tau) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨(x₁ * x₂) ^ 2, hz.z4i_Q_le_NQ (pow_mem (mul_mem hz.x₁_mem_Q hz.x₂_mem_Q) 2)⟩

@[expose] def z4jV (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {v : G}
    (hv : v ∈ ctxQ t tau x₁ x₂ rho) : ↥(ctxNQ t tau x₁ x₂ rho) :=
  ⟨v, hz.z4i_Q_le_NQ hv⟩

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)

theorem z4j_V_eq :
    hz.z4iSub (fourGrp x₁ x₂) = closure ({hz.z4jY, hz.z4jZ} : Set ↥(ctxNQ t tau x₁ x₂ rho)) := by
  rw [fourGrp]
  exact (congrArg (fun H : Subgroup G => H.subgroupOf (ctxNQ t tau x₁ x₂ rho)) (by
    rw [Set.image_pair]; rfl)).trans
    (z4j_subgroupOf_closure ({hz.z4jY, hz.z4jZ} : Set ↥(ctxNQ t tau x₁ x₂ rho)))

theorem z4j_Y_mem : ∀ q ∈ hz.z4iSub (ctxQ t tau x₁ x₂ rho), q * q = 1 →
    q ∈ hz.z4iSub (ctxYq t tau x₁ x₂ rho) := by
  intro q hq hqq
  rw [hz.z4i_mem_sub] at hq ⊢
  rw [hz.mem_Y_iff]
  refine ⟨hq, ?_⟩
  have h : (q : G) * (q : G) = 1 := by
    simpa using congrArg Subtype.val hqq
  rwa [pow_two]

theorem z4j_y_ne_one : hz.z4jY ≠ 1 := by
  intro h
  exact hz.y_ne_one (by simpa [z4jY] using congrArg Subtype.val h)

theorem z4j_z_ne_one : hz.z4jZ ≠ 1 := by
  intro h
  apply hz.y_ne_x₂_sq
  have hz1 : (x₁ * x₂) ^ 2 = 1 := by simpa [z4jZ] using congrArg Subtype.val h
  rw [hz.x₂_sq, hz1, mul_one]

theorem z4j_y_ne_z : hz.z4jY ≠ hz.z4jZ := by
  intro h
  apply hz.x₂_sq_ne_one
  have hyz : x₁ ^ 2 = (x₁ * x₂) ^ 2 := by simpa [z4jY, z4jZ] using congrArg Subtype.val h
  rw [hz.x₂_sq, ← hyz, ← pow_two, hz.y_sq]

theorem z4j_l_y : hz.z4iLam * hz.z4jY * hz.z4iLam⁻¹ = hz.z4jY * hz.z4jZ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, z4jY, z4jZ, z4iLam, Subtype.coe_mk]
  rw [← hz.x₂_sq, ← conj_pow, hz.wreath.conj_x₁]

theorem z4j_l_z : hz.z4iLam * hz.z4jZ * hz.z4iLam⁻¹ = hz.z4jZ := by
  have hlam : lam * lam = 1 := by
    have := pow_orderOf_eq_one lam
    rw [hz.wreath.ord_lam] at this
    simpa [pow_two] using this
  have hx₂ : lam * x₂ * lam⁻¹ = x₁ :=
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [hz.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
      _ = x₁ := by rw [hlam]; group
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, z4jZ, z4iLam, Subtype.coe_mk]
  calc lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (lam * (x₁ * x₂) * lam⁻¹) ^ 2 := by rw [← conj_pow]
    _ = ((lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹)) ^ 2 := by
        rw [show lam * (x₁ * x₂) * lam⁻¹ = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) by group]
    _ = (x₂ * x₁) ^ 2 := by rw [hz.wreath.conj_x₁, hx₂]
    _ = (x₁ * x₂) ^ 2 := by rw [hz.x₁_comm_x₂]

variable {V' : Subgroup G} {v₁ v₂ : G}

theorem z4j_V'_eq (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho) :
    hz.z4iSub V' = closure ({hz.z4jV hv₁, hz.z4jV hv₂} : Set ↥(ctxNQ t tau x₁ x₂ rho)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hVgen, -, -, -, -⟩ := hV
  rw [hVgen]
  exact (congrArg (fun H : Subgroup G => H.subgroupOf (ctxNQ t tau x₁ x₂ rho)) (by
    rw [Set.image_pair]; rfl)).trans
    (z4j_subgroupOf_closure ({hz.z4jV hv₁, hz.z4jV hv₂} : Set ↥(ctxNQ t tau x₁ x₂ rho)))

theorem z4j_v₁_ne_one (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) : hz.z4jV hv₁ ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hv₁1, -, -, -, -, -, -⟩ := hV
  intro h
  exact hv₁1 (by simpa [z4jV] using congrArg Subtype.val h)

theorem z4j_v₂_ne_one (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho) : hz.z4jV hv₂ ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hv₂nz, -, -, -, -, -⟩ := hV
  intro h
  apply hv₂nz
  rw [show v₂ = 1 by simpa [z4jV] using congrArg Subtype.val h]
  exact one_mem _

theorem z4j_v₁_ne_v₂ (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho) :
    hz.z4jV hv₁ ≠ hz.z4jV hv₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hv₂nz, -, -, -, -, -⟩ := hV
  intro h
  apply hv₂nz
  rw [show v₂ = v₁ by simpa [z4jV] using (congrArg Subtype.val h).symm]
  exact Subgroup.mem_zpowers v₁

theorem z4j_t_v₁ (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) :
    hz.z4iT * hz.z4jV hv₁ * hz.z4iT⁻¹ = hz.z4jV hv₁ * hz.z4jY := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ht₁, -, -, -⟩ := hV
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, z4iT, z4jV, z4jY, Subtype.coe_mk] using ht₁

theorem z4j_t_v₂ (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho) :
    hz.z4iT * hz.z4jV hv₂ * hz.z4iT⁻¹ = hz.z4jV hv₂ * (hz.z4jY * hz.z4jZ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ht₂, -, -⟩ := hV
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, z4iT, z4jV, z4jY, z4jZ, Subtype.coe_mk]
  rw [ht₂, hz.x₂_sq]

theorem z4j_lt_v₁ (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho) :
    (hz.z4iLam * hz.z4iT) * hz.z4jV hv₁ * (hz.z4iLam * hz.z4iT)⁻¹ = hz.z4jV hv₂ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := hV
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, z4iLam, z4iT, z4jV, Subtype.coe_mk] using hlt

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
