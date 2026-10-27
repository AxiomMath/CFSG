module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellFrattiniKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathPerm

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

omit [Finite H] in
theorem rho_mem_wreathAut (x : H) :
    h.rho x ∈ @wreathAut ↥W h.cg (Fin r) (planesIn W I) _ h.planeFamily Pm := by
  rw [← h.rho_range]
  exact ⟨x, rfl⟩

@[expose] noncomputable def piH : H →* Equiv.Perm (Fin r) :=
  letI := h.cg
  (permHom h.planeFamily).comp (h.rho.codRestrict (permuting (planesIn W I)) (fun x =>
    wreathAut_le_permuting h.planeFamily Pm (h.rho_mem_wreathAut x)))

omit [Finite H] in
theorem map_conj_eq_of_smul_eq {x : H} {i j : Fin r}
    (hx : h.rho x • planesIn W I i = planesIn W I j) :
    (I i).map (MulAut.conj x).toMonoidHom = I j := by
  have hcond := (smul_planes_iff (h.rho x) i j).mp hx
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (hcond ⟨y, h.I_le i hy⟩).mpr hy
    rwa [h.rho_apply] at this
  · intro hz
    have hzW : z ∈ W := h.I_le j hz
    have hyW : x⁻¹ * z * x ∈ W := by simpa using h.W_normal.conj_mem z hzW x⁻¹
    refine ⟨x⁻¹ * z * x, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    refine (hcond ⟨x⁻¹ * z * x, hyW⟩).mp ?_
    rw [h.rho_apply]
    simpa [mul_assoc] using hz

omit [Finite H] in
theorem map_conj_plane (x : H) (i : Fin r) :
    (I i).map (MulAut.conj x).toMonoidHom = I (h.piH x i) := by
  let _ := h.cg
  exact h.map_conj_eq_of_smul_eq (permHom_spec h.planeFamily
    ⟨h.rho x, wreathAut_le_permuting h.planeFamily Pm (h.rho_mem_wreathAut x)⟩ i)

omit [Finite H] in
theorem piH_eq_one_iff (x : H) : h.piH x = 1 ↔ h.rho x ∈ h.B := by
  let _ := h.cg
  constructor
  · intro h1
    exact (mem_baseGp_iff_permHom h.planeFamily).mpr ⟨_, h1⟩
  · intro hx
    obtain ⟨hp, h1⟩ := (mem_baseGp_iff_permHom h.planeFamily).mp hx
    exact h1

omit [Finite H] in
theorem piH_mem (x : H) : h.piH x ∈ Pm := by
  let _ := h.cg
  obtain ⟨σ, hσ, hx⟩ := h.image_le' x
  have : h.piH x = σ := (permHom_eq_iff h.planeFamily _ σ).mpr hx
  rw [this]
  exact hσ

omit [Finite H] in
theorem range_piH : h.piH.range = Pm := by
  let _ := h.cg
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact h.piH_mem x
  · intro σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_perm h.planeFamily σ
    have hgw : g ∈ wreathAut h.planeFamily Pm := (mem_wreathAut_iff h.planeFamily).mpr ⟨σ, hσ, hg⟩
    rw [← h.rho_range] at hgw
    obtain ⟨x, rfl⟩ := hgw
    exact ⟨x, (permHom_eq_iff h.planeFamily _ σ).mpr hg⟩

theorem piH_odd {n : H} (hn : n ∈ oddOrderSubgroup (⊤ : Subgroup H)) : h.piH n = 1 :=
  (h.piH_eq_one_iff n).mpr (h.rho_mem_B_of_mem_odd hn)

theorem frattini :
    oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤ ∧
      R ⊓ Subgroup.centralizer (V : Set H) = CFSG.pCore 2 H ∧
      CFSG.pCore 2 H ≤ Subgroup.centralizer (V : Set H) ∧
      Subgroup.centralizer (V : Set H) ≤ kerIn M ⊤ ∧
      (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H))).map
          (oddOrderSubgroup (⊤ : Subgroup H)).subtype =
        oddOrderSubgroup (⊤ : Subgroup H) ⊓ CFSG.pCore 2 H ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
        frattini (H ⧸ CFSG.pCore 2 H) ∧
      (∀ D : Subgroup H, D ≤ kerIn M ⊤ →
        (D.subgroupOf (oddOrderSubgroup (⊤ : Subgroup H))).map
            (QuotientGroup.mk' (CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H)))) ≤
          frattini (oddOrderSubgroup (⊤ : Subgroup H) ⧸
            CFSG.pCore 2 (oddOrderSubgroup (⊤ : Subgroup H)))) :=
  minimal_parabolic_reduced_module_Frattini_kernel_production h.sylow h.nonnormal h.le_M h.M_lt
    h.M_max h.reduced h.not_top_le_centralizer_V

theorem odd_sup_R : oddOrderSubgroup (⊤ : Subgroup H) ⊔ R = ⊤ := h.frattini.1

theorem exists_mul_odd_R (x : H) :
    ∃ n ∈ oddOrderSubgroup (⊤ : Subgroup H), ∃ r ∈ R, x = n * r := by
  have hx : x ∈ oddOrderSubgroup (⊤ : Subgroup H) ⊔ R := by
    rw [h.odd_sup_R]
    exact Subgroup.mem_top x
  exact CFSG.QuasithinUnique.Setup.Layer.mem_sup_mul
    (normal_le_normalizer' (oddOrderSubgroup_top_normal (H := H)) R) hx

theorem exists_R_piH {σ : Equiv.Perm (Fin r)} (hσ : σ ∈ Pm) : ∃ r ∈ R, h.piH r = σ := by
  rw [← h.range_piH] at hσ
  obtain ⟨x, rfl⟩ := hσ
  obtain ⟨n, hn, r, hr, rfl⟩ := h.exists_mul_odd_R x
  exact ⟨r, hr, by rw [map_mul, h.piH_odd hn, one_mul]⟩

theorem transitive_R (i j : Fin r) :
    ∃ x ∈ R, (I i).map (MulAut.conj x).toMonoidHom = I j := by
  obtain ⟨σ, hσ, hij⟩ := h.Pm_trans i j
  obtain ⟨x, hx, hxσ⟩ := h.exists_R_piH hσ
  refine ⟨x, hx, ?_⟩
  rw [h.map_conj_plane, hxσ, hij]

@[expose] noncomputable def T0 : Subgroup (MulAut ↥W) := R.map h.rho ⊓ h.B

omit [Finite H] in
theorem ker_rho : h.rho.ker = Subgroup.centralizer (W : Set H) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx w hw
    have := congrArg (fun a : MulAut ↥W => ((a ⟨w, hw⟩ : ↥W) : H)) hx
    simp only [h.rho_apply, MulAut.one_apply] at this
    have h2 : x * w = w * x := by
      calc x * w = (x * w * x⁻¹) * x := by group
        _ = w * x := by rw [this]
    exact h2.symm
  · intro hx
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    rw [h.rho_apply]
    have := hx w w.2
    show x * (w : H) * x⁻¹ = (w : H)
    calc x * (w : H) * x⁻¹ = (w : H) * x * x⁻¹ := by rw [this]
      _ = (w : H) := by group

omit [Finite H] in
theorem ker_rho_eq_centralizer_V : h.rho.ker = Subgroup.centralizer (V : Set H) := by
  rw [h.ker_rho, h.centralizer_W_eq_V]

omit [Finite H] in
theorem sylow_map_rho : IsSylowTwoOf (R.map h.rho) h.rho.range := by
  have := isSylowTwoOf_map_hom h.sylow (h.rho.comp (⊤ : Subgroup H).subtype)
  have e1 : (R.subgroupOf (⊤ : Subgroup H)).map (h.rho.comp (⊤ : Subgroup H).subtype) =
      R.map h.rho := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le le_top]
  have e2 : (h.rho.comp (⊤ : Subgroup H).subtype).range = h.rho.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.range_eq_map]
  rwa [e1, e2] at this

theorem T0_sylow : IsSylowTwoOf h.T0 h.B := by
  let _ := h.cg
  refine isSylowTwoOf_inf_of_prod (H := h.rho.range) h.sylow_map_rho ?_ ?_
  · rw [h.rho_range]
    exact baseGp_le_wreathAut h.planeFamily Pm
  · rintro g ⟨x, rfl⟩
    obtain ⟨n, hn, r, hr, rfl⟩ := h.exists_mul_odd_R x
    exact ⟨h.rho n, h.rho_mem_B_of_mem_odd hn, h.rho r, ⟨r, hr, rfl⟩, map_mul _ _ _⟩

theorem exists_t : ∃ t : ∀ i, MulAut ↥(planesIn W I i),
    @IsCoordProduct ↥W h.cg (Fin r) (planesIn W I) h.T0 Finset.univ t := by
  let _ := h.cg
  exact exists_isCoordProduct_of_sylow h.planeFamily h.T0_sylow

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
