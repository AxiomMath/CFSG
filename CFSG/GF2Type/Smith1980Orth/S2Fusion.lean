module

public import CFSG.GF2Type.Smith1980Orth.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions CFSG.Open

theorem odd_ncard_nonzero_singular {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 2 ≤ m) (hV : finrank (ZMod 2) V = 2 * m) :
    Odd {v : V | v ≠ 0 ∧ Q v = 0}.ncard := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hc := S12DW.natCard_eq_four_pow hV
  have h2 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (S12DW.polar_eq_zero_imp hQ) hc
  have h0 := S12DW.ncard_eq_zero_eq Q
  have hsplit : {v : V | Q v = 0}.ncard = {v : V | v ≠ 0 ∧ Q v = 0}.ncard + 1 := by
    have e : {v : V | Q v = 0} = insert 0 {v : V | v ≠ 0 ∧ Q v = 0} := by
      ext v
      by_cases hv : v = 0 <;> simp [hv]
    rw [e, Set.ncard_insert_of_notMem (by simp)]
  have h2m : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have h4m : 4 ^ m = 2 ^ m * 2 ^ m := by
    rw [← mul_pow]
    norm_num
  obtain ⟨b, hb⟩ : ∃ b, 2 ^ m = 4 * b := ⟨_, h2m⟩
  obtain ⟨c, hcc⟩ : ∃ c, 4 ^ m = 16 * c := ⟨b * b, by rw [h4m, hb]; ring⟩
  rw [hc] at h0
  rw [Nat.odd_iff]
  rcases h2 with h2 | h2 <;> omega

variable {G : Type} [Group G] [Finite G]

theorem ncard_cl_preimage (S : Setting G) (A : Set S.Qt) :
    {x : G | x ∈ S.QG ∧ S.cl x ∈ A}.ncard = 2 * A.ncard := by
  classical
  choose σ hσQ hσ using S.exists_cl
  have hσinj : Function.Injective σ := fun v w h => by rw [← hσ v, ← hσ w, h]
  have hτinj : Function.Injective (fun v => σ v * S.z) :=
    fun v w h => hσinj (mul_right_cancel h)
  have hE : {x : G | x ∈ S.QG ∧ S.cl x ∈ A} = σ '' A ∪ (fun v => σ v * S.z) '' A := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hx, hxA⟩
      rcases (S.cl_eq_cl_iff (hσQ (S.cl x)) hx).mp (hσ (S.cl x)) with h | h
      · exact Or.inl ⟨S.cl x, hxA, h.symm⟩
      · exact Or.inr ⟨S.cl x, hxA, h.symm⟩
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · exact ⟨hσQ v, by rw [hσ]; exact hv⟩
      · exact ⟨S.QG.mul_mem (hσQ v) S.z_mem_QG, by rw [S.cl_mul_z (hσQ v), hσ]; exact hv⟩
  have hdisj : Disjoint (σ '' A) ((fun v => σ v * S.z) '' A) := by
    rw [Set.disjoint_left]
    rintro x ⟨v, -, rfl⟩ ⟨w, -, hwv⟩
    have h1 : w = v := by
      have := congrArg S.cl hwv
      simp only at this
      rwa [S.cl_mul_z (hσQ w), hσ, hσ] at this
    subst h1
    exact S.z_ne_one (mul_eq_left.mp hwv)
  rw [hE, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hσinj, Set.ncard_image_of_injective _ hτinj]
  ring

variable {S : Setting G}

namespace S2Pre

variable {M1 : Subgroup S.O} (D : S2Pre S M1)

theorem k_inv : D.k⁻¹ = D.k * D.k :=
  inv_eq_of_mul_eq_one_right ((pow_three D.k).symm.trans D.k_cube)

theorem k_apply_cube (v : S.Qt) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
      v := by
  have h : ((D.k ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by rw [D.k_cube]; rfl
  rwa [pow_three, coe_mul_apply, coe_mul_apply] at h

theorem t_apply_apply (v : S.Qt) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← coe_mul_apply, D.t_mul_t]
  rfl

theorem t_k_apply_of_mem {u : S.Qt} (hu : u ∈ Vt S D.g D.t) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
  rw [D.t_k_apply, D.t_apply_of_mem hu, D.k_inv, coe_mul_apply]

theorem t_kk_apply_of_mem {u : S.Qt} (hu : u ∈ Vt S D.g D.t) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) =
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
  rw [D.t_k_apply, D.t_k_apply_of_mem hu, D.k_inv, coe_mul_apply]
  exact D.k_apply_cube _

end S2Pre

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

@[expose] def singV : Set S.Qt := orbit S D.g D.t

@[expose] def singW : Set S.Qt := (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) '' D.singV

@[expose] def singWt : Set S.Qt := (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) '' D.singW

@[expose] def orbitMbar : Set S.Qt :=
  {v | ∃ x ∈ S.Mbar, v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹))}

theorem singV_subset : D.singV ⊆ Vt S D.g D.t := orbit_subset_Vt D.good.ht D.good.H.conj_mem

theorem zero_notMem_singV : (0 : S.Qt) ∉ D.singV := by
  rintro ⟨x, -, h0⟩
  exact cl_conj_z_ne_zero S D.good.H.conj_mem D.good.H.conj_ne
    ((LinearEquiv.map_eq_zero_iff _).mp h0.symm)

theorem zero_notMem_orbitMbar : (0 : S.Qt) ∉ D.orbitMbar := by
  rintro ⟨x, -, h0⟩
  exact cl_conj_z_ne_zero S D.good.H.conj_mem D.good.H.conj_ne
    ((LinearEquiv.map_eq_zero_iff _).mp h0.symm)

theorem exists_form_singV :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S D.g D.t)) (_ : Q.polarBilin.Nondegenerate),
      D.singV = (Vt S D.g D.t).subtype '' {v : Vt S D.g D.t | v ≠ 0 ∧ Q v = 0} := by
  obtain ⟨Q, hQ, -, -, -, hsing⟩ := D.hΩ.exists_form
  refine ⟨Q, hQ, ?_⟩
  ext w
  constructor
  · intro hw
    have hwV := D.singV_subset hw
    have hv0 : (⟨w, hwV⟩ : Vt S D.g D.t) ≠ 0 := fun h => by
      have hw0 : w = 0 := congrArg Subtype.val h
      exact D.zero_notMem_singV (hw0 ▸ hw)
    exact ⟨⟨w, hwV⟩, ⟨hv0, (hsing _ hv0).mpr
      ((mem_orbitOf_RmodN_iff D.good.H.conj_mem D.good.ht).mpr hw)⟩, rfl⟩
  · rintro ⟨v, ⟨hv0, hvQ⟩, rfl⟩
    exact (mem_orbitOf_RmodN_iff D.good.H.conj_mem D.good.ht).mp ((hsing v hv0).mp hvQ)

theorem ncard_singV_odd : Odd D.singV.ncard := by
  obtain ⟨Q, hQ, hS⟩ := D.exists_form_singV
  rw [hS, Set.ncard_image_of_injective _ (Submodule.injective_subtype _)]
  obtain ⟨m, hm⟩ := even_finrank_Vt D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ
  have h8 := D.four_le
  have hV := D.finrank_Vt
  exact odd_ncard_nonzero_singular Q hQ (m := m) (by omega) (by omega)

theorem ncard_singW : D.singW.ncard = D.singV.ncard :=
  Set.ncard_image_of_injective _ (LinearEquiv.injective _)

theorem ncard_singWt : D.singWt.ncard = D.singV.ncard := by
  rw [singWt, Set.ncard_image_of_injective _ (LinearEquiv.injective _), D.ncard_singW]

theorem disjoint_singV_singW : Disjoint D.singV D.singW := by
  rw [Set.disjoint_left]
  rintro v hv ⟨u, hu, rfl⟩
  exact D.zero_notMem_singV
    (D.eq_zero_of_k_apply_mem (D.singV_subset hu) (D.singV_subset hv) ▸ hu)

theorem disjoint_singV_singWt : Disjoint D.singV D.singWt := by
  rw [Set.disjoint_left]
  rintro v hv ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  have h := D.eq_zero_of_k_apply_mem (D.singV_subset hv)
    (by rw [D.k_apply_cube]; exact D.singV_subset hu)
  exact D.zero_notMem_singV (h ▸ hv)

theorem disjoint_singW_singWt : Disjoint D.singW D.singWt := by
  rw [Set.disjoint_left]
  rintro v ⟨u, hu, rfl⟩ ⟨w, ⟨u', hu', rfl⟩, hw⟩
  have h1 : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u' = u := LinearEquiv.injective _ hw
  exact D.zero_notMem_singV
    (D.eq_zero_of_k_apply_mem (D.singV_subset hu') (h1 ▸ D.singV_subset hu) ▸ hu')

private def setStab (S : Setting G) (U : Set S.Qt) : Subgroup S.O where
  carrier := {s | ∀ u : S.Qt, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U ↔ u ∈ U}
  mul_mem' := fun {a b} ha hb u => by rw [coe_mul_apply, ha, hb]
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {a} ha u => by rw [← ha, apply_inv_apply_O]

theorem k_apply_mem_union {x : S.Qt} (hx : x ∈ D.singV ∪ D.singW ∪ D.singWt) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ D.singV ∪ D.singW ∪ D.singWt := by
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
  · exact Or.inr ⟨x, hx, rfl⟩
  · obtain ⟨w, ⟨u, hu, rfl⟩, rfl⟩ := hx
    rw [D.k_apply_cube]
    exact Or.inl (Or.inl hu)

theorem t_apply_mem_union {x : S.Qt} (hx : x ∈ D.singV ∪ D.singW ∪ D.singWt) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ D.singV ∪ D.singW ∪ D.singWt := by
  rcases hx with (hx | hx) | hx
  · rw [D.t_apply_of_mem (D.singV_subset hx)]
    exact Or.inl (Or.inl hx)
  · obtain ⟨u, hu, rfl⟩ := hx
    rw [D.t_k_apply_of_mem (D.singV_subset hu)]
    exact Or.inr ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  · obtain ⟨w, ⟨u, hu, rfl⟩, rfl⟩ := hx
    rw [D.t_kk_apply_of_mem (D.singV_subset hu)]
    exact Or.inl (Or.inr ⟨u, hu, rfl⟩)

private theorem sup_le_setStab :
    D.Obar ⊔ zpowers D.t ≤ setStab S (D.singV ∪ D.singW ∪ D.singWt) := by
  refine sup_le ?_ (zpowers_le.mpr fun u => ⟨fun h => ?_, D.t_apply_mem_union⟩)
  · rw [D.Obar_eq_zpowers, zpowers_le]
    intro u
    refine ⟨fun h => ?_, D.k_apply_mem_union⟩
    have h1 := D.k_apply_mem_union (D.k_apply_mem_union h)
    rwa [D.k_apply_cube] at h1
  · have h1 := D.t_apply_mem_union h
    rwa [D.t_apply_apply] at h1

theorem orbitMbar_subset :
    D.orbitMbar ⊆ D.singV ∪ D.singW ∪ D.singWt := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := D.rel.orbit x hx
  rw [hxy]
  obtain ⟨s, hs, c, hc, rfl⟩ := D.exists_mul_Cbar_of_mem_M1 hy
  have hcV : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) ∈ D.singV :=
    S7.apply_mem_orbit_of_comm D.good.H D.good.ht
      (dtEqConj_of_omegaCase D.good.H D.good.hNo D.good.C D.hΩ) (D.Cbar_le_Mbar hc)
      (D.comm_of_mem_Cbar hc) cl_a_mem_orbit
  rw [coe_mul_apply]
  exact (D.sup_le_setStab hs _).mpr (Or.inl (Or.inl hcV))

theorem union_subset_orbitMbar : D.singV ∪ D.singW ∪ D.singWt ⊆ D.orbitMbar := by
  have hk := D.k_mem_Mbar
  rintro v ((hv | ⟨u, hu, rfl⟩) | ⟨w, ⟨u, hu, rfl⟩, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨x, Rbar_le_Mbar hx, rfl⟩
  · obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨D.k * x, mul_mem hk (Rbar_le_Mbar hx), rfl⟩
  · obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨D.k * (D.k * x), mul_mem hk (mul_mem hk (Rbar_le_Mbar hx)), rfl⟩

theorem orbitMbar_eq :
    D.orbitMbar = D.singV ∪ D.singW ∪ D.singWt :=
  (D.orbitMbar_subset).antisymm D.union_subset_orbitMbar

theorem ncard_orbitMbar :
    D.orbitMbar.ncard = 3 * D.singV.ncard := by
  rw [D.orbitMbar_eq, Set.ncard_union_eq (D.disjoint_singV_singWt.union_left
    D.disjoint_singW_singWt) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq D.disjoint_singV_singW (Set.toFinite _) (Set.toFinite _), D.ncard_singW,
    D.ncard_singWt]
  ring

theorem exists_conj_eq_of_mem_M1 {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) :
    ∃ m : G, ∃ hm : m ∈ S.M, S.ρ ⟨m, hm⟩ ∈ M1 ∧
      m * (D.g * S.z * D.g⁻¹) * m⁻¹ = h * S.z * h⁻¹ := by
  have hF : FusionCtl S D.g := fusionCtl_of_lemma_3_13 D.good.H D.good.noAll
  obtain ⟨m, hm, hmh⟩ := hF h hQ hne
  obtain ⟨y, hy, hxy⟩ := D.rel.orbit (S.ρ ⟨m, hm⟩) ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨m', hm', rfl⟩ := MonoidHom.mem_range.mp (D.rel.le hy)
  have hQ' : (m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹ ∈ S.QG := by
    rw [show (m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹
      = ((m' : G) * D.g) * S.z * ((m' : G) * D.g)⁻¹ from by group]
    exact conj_mem_QG' S m'.2 D.good.H.conj_mem
  have hm_cl : (S.ρ ⟨m, hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) =
      S.cl (h * S.z * h⁻¹) := by
    rw [S.ρ_cl_conj_z hm D.good.H.conj_mem]
    rw [show (m * D.g) * S.z * (m * D.g)⁻¹ = h * S.z * h⁻¹ from by rw [← hmh]; group]
  have hm'_cl : (S.ρ m' : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) =
      S.cl ((m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹) := by
    rw [S.ρ_cl_conj_z m'.2 D.good.H.conj_mem]
    congr 1
    group
  have hcl : S.cl ((m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹) =
      S.cl (h * S.z * h⁻¹) := by
    rw [← hm'_cl, ← hxy, hm_cl]
  rcases (S.cl_eq_cl_iff hQ' hQ).mp hcl with hcase | hcase
  · exact ⟨(m' : G), m'.2, hy, hcase.symm⟩
  · have ht1 : (m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹ ≠ 1 := by
      rw [show (m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹
        = ((m' : G) * D.g) * S.z * ((m' : G) * D.g)⁻¹ from by group]
      exact conj_z_ne_one S _
    have htz : (m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹ ≠ S.z := by
      rw [show (m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹
        = ((m' : G) * D.g) * S.z * ((m' : G) * D.g)⁻¹ from by group]
      exact conj_ne_z' S m'.2 D.good.H.conj_ne
    obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z hQ' ht1 htz
    obtain ⟨hum, huQ'⟩ := S.mem_QG_iff.mp huQ
    refine ⟨u * (m' : G), S.M.mul_mem hum m'.2, ?_, ?_⟩
    · have hρ : S.ρ ⟨u * (m' : G), S.M.mul_mem hum m'.2⟩ = S.ρ m' := by
        calc S.ρ ⟨u * (m' : G), S.M.mul_mem hum m'.2⟩
            = S.ρ (⟨u, hum⟩ * m') := rfl
          _ = S.ρ ⟨u, hum⟩ * S.ρ m' := map_mul _ _ _
          _ = 1 * S.ρ m' := by rw [S.ρ_eq_one_of_mem_Q huQ']
          _ = S.ρ m' := one_mul _
      rwa [hρ]
    · rw [show u * (m' : G) * (D.g * S.z * D.g⁻¹) * (u * (m' : G))⁻¹
        = u * ((m' : G) * (D.g * S.z * D.g⁻¹) * (m' : G)⁻¹) * u⁻¹ from by group, hu]
      exact hcase.symm

theorem conj_mem_Q_iff {x : G} :
    (IsConj S.z x ∧ x ∈ S.QG) ↔ (x = S.z ∨ (x ∈ S.QG ∧ S.cl x ∈ D.orbitMbar)) := by
  have hF : FusionCtl S D.g := fusionCtl_of_lemma_3_13 D.good.H D.good.noAll
  constructor
  · rintro ⟨hconj, hxQ⟩
    by_cases hxz : x = S.z
    · exact Or.inl hxz
    · refine Or.inr ⟨hxQ, ?_⟩
      obtain ⟨k, hk⟩ := isConj_iff.mp hconj
      obtain ⟨m, hm, hmx⟩ := hF k (hk ▸ hxQ) (hk ▸ hxz)
      refine ⟨S.ρ ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩, ?_⟩
      rw [S4.ρ_cl_conj_z S ⟨m, hm⟩ D.good.H.conj_mem]
      congr 1
      exact ((mul_conj_z S m D.g).trans (hmx.trans hk)).symm
  · rintro (rfl | ⟨hxQ, y, hy, hyx⟩)
    · exact ⟨IsConj.refl _, S.z_mem_QG⟩
    · refine ⟨?_, hxQ⟩
      obtain ⟨κ, rfl⟩ := MonoidHom.mem_range.mp hy
      rw [S4.ρ_cl_conj_z S κ D.good.H.conj_mem] at hyx
      have hbQ : (κ : G) * D.g * S.z * ((κ : G) * D.g)⁻¹ ∈ S.QG :=
        conj_mem_QG' S κ.2 D.good.H.conj_mem
      have hbz : (κ : G) * D.g * S.z * ((κ : G) * D.g)⁻¹ ≠ S.z :=
        conj_ne_z' S κ.2 D.good.H.conj_ne
      have hb1 : (κ : G) * D.g * S.z * ((κ : G) * D.g)⁻¹ ≠ 1 := conj_z_ne_one S _
      rcases (S.cl_eq_cl_iff hbQ hxQ).mp hyx.symm with h | h
      · exact isConj_iff.mpr ⟨(κ : G) * D.g, h.symm⟩
      · obtain ⟨u, -, hu⟩ := S.exists_conj_eq_mul_z hbQ hb1 hbz
        refine isConj_iff.mpr ⟨u * ((κ : G) * D.g), ?_⟩
        rw [h, ← hu]
        group

theorem ncard_conj_mem_Q :
    {x : G | IsConj S.z x ∧ x ∈ S.QG}.ncard = 1 + 6 * D.singV.ncard := by
  have h1 : {x : G | IsConj S.z x ∧ x ∈ S.QG} =
      insert S.z {x : G | x ∈ S.QG ∧ S.cl x ∈ D.orbitMbar} := by
    ext x
    exact D.conj_mem_Q_iff
  have hz : S.z ∉ {x : G | x ∈ S.QG ∧ S.cl x ∈ D.orbitMbar} := fun h =>
    D.zero_notMem_orbitMbar (by have := h.2; rwa [S.cl_z] at this)
  rw [h1, Set.ncard_insert_of_notMem hz (Set.toFinite _), ncard_cl_preimage,
    D.ncard_orbitMbar]
  ring

include D in
theorem card_conj_mem_Q_mod_four :
    Nat.card {x : G | IsConj S.z x ∧ x ∈ S.QG} % 4 = 3 := by
  rw [Nat.card_coe_set_eq, D.ncard_conj_mem_Q]
  obtain ⟨j, hj⟩ := D.ncard_singV_odd
  omega

end S2Data

end CFSG.GF2Type.Smith1980Orth
