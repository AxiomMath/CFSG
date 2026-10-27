module

public import CFSG.GF2Type.Smith1980Orth.S2Coord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

theorem cl_base_eq_coord : S.cl (D.g * S.z * D.g⁻¹) = D.coord (aV D.good.ht, 0) := by
  rw [D.coord_apply_zero_right]
  rfl

theorem snd_eq_zero_or_eq_aV_of_mem {u v : Vt S D.g D.t}
    (hx : D.coord (u, v) ∈ S.clSub (S.QG ⊓ S.Qa D.g)) : v = 0 ∨ v = aV D.good.ht := by
  have h := S6.Lbar_apply_sub_mem_span' D.good.H.conj_mem hx D.good.ht
  have e : D.coord (u + v, v) - D.coord (u, v) = D.coord (v, 0) := by
    rw [← map_sub]
    congr 1
    ext <;> simp
  rw [D.t_apply_coord, e, D.cl_base_eq_coord] at h
  rcases S4.mem_span_cl_iff.mp h with h | h
  · left
    exact congrArg Prod.fst (D.coord.injective (h.trans (map_zero _).symm))
  · right
    exact congrArg Prod.fst (D.coord.injective h)

theorem betaV_eq_zero_of_mem {u v : Vt S D.g D.t}
    (hx : D.coord (u, v) ∈ S.clSub (S.QG ⊓ S.Qa D.g)) : D.betaV u v = 0 := by
  rw [← D.q_coord]
  exact S.q_eq_zero_of_mem_clSub_QG_inf_Qa D.good.H.conj_ne hx

theorem coord_zero_mem_iff {u : Vt S D.g D.t} :
    D.coord (u, 0) ∈ S.clSub (S.QG ⊓ S.Qa D.g) ↔ D.betaV (aV D.good.ht) u = 0 := by
  rw [D.coord_apply_zero_right]
  exact (S4.beta_aV_eq_zero_iff D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ u).symm

theorem mem_clSub_QG_inf_Qa_iff {x : S.Qt} :
    x ∈ S.clSub (S.QG ⊓ S.Qa D.g) ↔ ∃ (u : Vt S D.g D.t) (e : ZMod 2),
      D.betaV (aV D.good.ht) u = 0 ∧ x = D.coord (u, e • aV D.good.ht) := by
  have hfwd : ∀ {x : S.Qt}, x ∈ S.clSub (S.QG ⊓ S.Qa D.g) → ∃ (u : Vt S D.g D.t) (e : ZMod 2),
      D.betaV (aV D.good.ht) u = 0 ∧ x = D.coord (u, e • aV D.good.ht) := by
    intro x hx
    obtain ⟨⟨u, v⟩, rfl⟩ := D.coord.surjective x
    rcases D.snd_eq_zero_or_eq_aV_of_mem hx with rfl | rfl
    · exact ⟨u, 0, D.coord_zero_mem_iff.mp hx, by rw [zero_smul]⟩
    · refine ⟨u, 1, ?_, by rw [one_smul]⟩
      rw [D.betaV_symm]
      exact D.betaV_eq_zero_of_mem hx
  refine ⟨hfwd, ?_⟩
  rintro ⟨u, e, hu, rfl⟩
  have horth := S6.orthogonal_clSub_eq D.good.H.conj_mem D.good.H.conj_ne
    D.good.C.card_QG_inf_Qa
  rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨u', e', hu', rfl⟩ := hfwd hn
  rw [polarBilin_apply_apply, D.polar_coord, map_smul, LinearMap.map_smul₂,
    D.betaV_symm u' (aV D.good.ht), hu, hu']
  simp

@[expose] noncomputable def Pfst (σ : Vt S D.g D.t) : Submodule (ZMod 2) S.Qt :=
  Submodule.map (D.coord : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt)
    ((LinearMap.ker (D.betaV σ)).prod (ZMod 2 ∙ σ))

theorem mem_Pfst_iff {σ : Vt S D.g D.t} {x : S.Qt} :
    x ∈ D.Pfst σ ↔ ∃ (u : Vt S D.g D.t) (e : ZMod 2), D.betaV σ u = 0 ∧
      x = D.coord (u, e • σ) := by
  rw [Pfst, Submodule.mem_map]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact ⟨u, e, LinearMap.mem_ker.mp hu, rfl⟩
  · rintro ⟨u, e, hu, rfl⟩
    exact ⟨(u, e • σ), ⟨LinearMap.mem_ker.mpr hu,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self σ)⟩, rfl⟩

@[expose] noncomputable def Psnd (σ : Vt S D.g D.t) : Submodule (ZMod 2) S.Qt :=
  (D.Pfst σ).map ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)

@[expose] noncomputable def Pdiag (σ : Vt S D.g D.t) : Submodule (ZMod 2) S.Qt :=
  (D.Psnd σ).map ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)

private theorem add_add_self_Vt (a b : Vt S D.g D.t) : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, OrthoF2.vec_add_self, zero_add]

theorem mem_Psnd_iff {σ : Vt S D.g D.t} {x : S.Qt} :
    x ∈ D.Psnd σ ↔ ∃ (u : Vt S D.g D.t) (e : ZMod 2), D.betaV σ u = 0 ∧
      x = D.coord (e • σ, u + e • σ) := by
  rw [Psnd, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, e, hu, rfl⟩ := D.mem_Pfst_iff.mp hy
    exact ⟨u, e, hu, D.k_apply_coord _ _⟩
  · rintro ⟨u, e, hu, rfl⟩
    exact ⟨D.coord (u, e • σ), D.mem_Pfst_iff.mpr ⟨u, e, hu, rfl⟩, D.k_apply_coord _ _⟩

theorem mem_Pdiag_iff {σ : Vt S D.g D.t} {x : S.Qt} :
    x ∈ D.Pdiag σ ↔ ∃ (u : Vt S D.g D.t) (e : ZMod 2), D.betaV σ u = 0 ∧
      x = D.coord (u + e • σ, u) := by
  rw [Pdiag, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, e, hu, rfl⟩ := D.mem_Psnd_iff.mp hy
    exact ⟨u, e, hu, by
      show (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (e • σ, u + e • σ)) = _
      rw [D.k_apply_coord, D.add_add_self_Vt]⟩
  · rintro ⟨u, e, hu, rfl⟩
    refine ⟨D.coord (e • σ, u + e • σ), D.mem_Psnd_iff.mpr ⟨u, e, hu, rfl⟩, ?_⟩
    show (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (e • σ, u + e • σ)) = _
    rw [D.k_apply_coord, D.add_add_self_Vt]

theorem clSub_QG_inf_Qa_base_eq_Pfst :
    S.clSub (S.QG ⊓ S.Qa D.g) = D.Pfst (aV D.good.ht) :=
  Submodule.ext fun _ => D.mem_clSub_QG_inf_Qa_iff.trans D.mem_Pfst_iff.symm

private theorem resC_mem_orthogonalGroup (c : D.Cbar) :
    D.resC c ∈ TauCeti.QuadraticMap.orthogonalGroup D.QV :=
  D.range_resC_le_orthogonalGroup (fun _ hv => D.QV_eq_zero_iff hv) ⟨c, rfl⟩

private theorem betaV_resC (c : D.Cbar) (u v : Vt S D.g D.t) :
    D.betaV (D.resC c u) (D.resC c v) =
      D.betaV u v := by
  rw [← D.polar_QV, ← D.polar_QV]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (D.resC_mem_orthogonalGroup c) u v

private theorem map_Pfst_Cbar (c : D.Cbar) (σ : Vt S D.g D.t) :
    (D.Pfst σ).map (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      D.Pfst (D.resC c σ) := by
  ext x
  rw [Submodule.mem_map, D.mem_Pfst_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨u, e, hu, rfl⟩ := D.mem_Pfst_iff.mp hy
    refine ⟨D.resC c u, e, by rw [D.betaV_resC, hu], ?_⟩
    exact (D.Cbar_apply_coord c u (e • σ)).trans (by rw [map_smul])
  · rintro ⟨u, e, hu, rfl⟩
    refine ⟨D.coord ((D.resC c).symm u, e • σ), ?_, ?_⟩
    · refine D.mem_Pfst_iff.mpr ⟨(D.resC c).symm u, e, ?_, rfl⟩
      rw [← D.betaV_resC c, LinearEquiv.apply_symm_apply, hu]
    · exact (D.Cbar_apply_coord c _ (e • σ)).trans
        (by rw [map_smul, LinearEquiv.apply_symm_apply])

private theorem map_Pfst_t (σ : Vt S D.g D.t) :
    (D.Pfst σ).map ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = D.Pfst σ := by
  have key : ∀ x ∈ D.Pfst σ, (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ D.Pfst σ := by
    intro x hx
    obtain ⟨u, e, hu, rfl⟩ := D.mem_Pfst_iff.mp hx
    refine D.mem_Pfst_iff.mpr ⟨u + e • σ, e, ?_, D.t_apply_coord _ _⟩
    rw [map_add, hu, map_smul, D.betaV_isAlt σ, smul_zero, add_zero]
  refine le_antisymm ?_ fun x hx => ⟨(D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) x, key x hx, D.t_apply_apply x⟩
  rintro _ ⟨x, hx, rfl⟩
  exact key x hx

private theorem map_mul_O (x y : S.O) (p : Submodule (ZMod 2) S.Qt) :
    p.map (((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      (p.map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)).map
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
  rw [← Submodule.map_comp]
  rfl

private theorem Obar_cases {s : S.O} (hs : s ∈ D.Obar) :
    s = 1 ∨ s = D.k ∨ s = D.k * D.k := by
  rw [D.Obar_eq_zpowers] at hs
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
  have hpow : D.k ^ n = D.k ^ (n % 3) := by simpa using zpow_eq_zpow_emod' n D.k_cube
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
  · left
    rw [hpow, h, zpow_zero]
  · right
    left
    rw [hpow, h, zpow_one]
  · right
    right
    rw [hpow, h, zpow_two]

private theorem map_base_cases {y : S.O} (hy : y ∈ M1) :
    ∃ σ : Vt S D.g D.t, σ ≠ 0 ∧
      (((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) = D.coord (σ, 0) ∧
          (S.clSub (S.QG ⊓ S.Qa D.g)).map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
            D.Pfst σ) ∨
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) = D.coord (0, σ) ∧
          (S.clSub (S.QG ⊓ S.Qa D.g)).map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
            D.Psnd σ) ∨
        ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) = D.coord (σ, σ) ∧
          (S.clSub (S.QG ⊓ S.Qa D.g)).map ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
            D.Pdiag σ)) := by
  obtain ⟨s, hs, c, hc, rfl⟩ := D.exists_mul_Cbar_of_mem_M1 hy
  set c' : D.Cbar := ⟨c, hc⟩ with hc'
  set σ := D.resC c' (aV D.good.ht) with hσ
  have hσ0 : σ ≠ 0 := fun h =>
    aV_ne_zero D.good.H D.good.ht ((LinearEquiv.map_eq_zero_iff _).mp h)
  have hA : (S.clSub (S.QG ⊓ S.Qa D.g)).map
      ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = D.Pfst σ := by
    rw [D.clSub_QG_inf_Qa_base_eq_Pfst]
    exact D.map_Pfst_Cbar c' _
  have h0 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) = D.coord (σ, 0) := by
    have := D.Cbar_apply_coord c' (aV D.good.ht) 0
    rwa [map_zero] at this
  have hap : ∀ s : S.O, ((s * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (aV D.good.ht, 0)) =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) := fun s => by
    rw [coe_mul_apply, h0]
  have hmp : ∀ s : S.O, (S.clSub (S.QG ⊓ S.Qa D.g)).map
      (((s * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        (D.Pfst σ).map ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := fun s => by
    rw [map_mul_O, hA]
  refine ⟨σ, hσ0, ?_⟩
  rcases D.mem_Obar_sup_cases hs with hso | rfl | rfl | rfl
  · rcases D.Obar_cases hso with rfl | rfl | rfl
    · left
      rw [one_mul]
      exact ⟨h0, hA⟩
    · right
      left
      rw [hap, hmp]
      exact ⟨by rw [D.k_apply_coord, add_zero], rfl⟩
    · right
      right
      rw [hap, hmp, map_mul_O]
      refine ⟨?_, rfl⟩
      rw [coe_mul_apply, D.k_apply_coord, D.k_apply_coord, zero_add, add_zero]
  · left
    rw [hap, hmp]
    refine ⟨by rw [D.t_apply_coord, add_zero], D.map_Pfst_t σ⟩
  · right
    left
    rw [hap, hmp, map_mul_O, D.map_Pfst_t]
    refine ⟨?_, rfl⟩
    rw [coe_mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord, add_zero]
  · right
    right
    rw [hap, hmp, map_mul_O, D.map_Pfst_t, pow_two, map_mul_O]
    refine ⟨?_, rfl⟩
    rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord,
      add_zero, D.k_apply_coord, zero_add]

private theorem clSub_cases {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG) (hne : h * S.z * h⁻¹ ≠ S.z) :
    ∃ σ : Vt S D.g D.t, σ ≠ 0 ∧
      ((S.cl (h * S.z * h⁻¹) = D.coord (σ, 0) ∧ S.clSub (S.QG ⊓ S.Qa h) = D.Pfst σ) ∨
        (S.cl (h * S.z * h⁻¹) = D.coord (0, σ) ∧ S.clSub (S.QG ⊓ S.Qa h) = D.Psnd σ) ∨
        (S.cl (h * S.z * h⁻¹) = D.coord (σ, σ) ∧ S.clSub (S.QG ⊓ S.Qa h) = D.Pdiag σ)) := by
  obtain ⟨m, hm, hm1, hmh⟩ := D.exists_conj_eq_of_mem_M1 hQ hne
  have hmg : (m * D.g) * S.z * (m * D.g)⁻¹ = h * S.z * h⁻¹ := by
    rw [← hmh]
    group
  have hQa : S.Qa h = S.Qa (m * D.g) := (S.Qa_eq_of_conj_eq hmg).symm
  have hcl : S.cl (h * S.z * h⁻¹) =
      ((S.ρ ⟨m, hm⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) := by
    rw [S.ρ_cl_conj_z hm D.good.H.conj_mem, hmg]
  have hmap : S.clSub (S.QG ⊓ S.Qa h) = (S.clSub (S.QG ⊓ S.Qa D.g)).map
      ((((S.ρ ⟨m, hm⟩ : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    rw [hQa]
    ext x
    rw [S6.mem_clSub_Qa_mul_iff (S := S) (g := D.g) ⟨m, hm⟩ (v := x), Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨_, hx, apply_inv_apply_O _ x⟩
    · rintro ⟨y, hy, rfl⟩
      rw [LinearEquiv.coe_coe, inv_apply_apply_O]
      exact hy
  obtain ⟨σ, hσ, H⟩ := D.map_base_cases (y := S.ρ ⟨m, hm⟩) hm1
  rw [hmap, hcl, D.cl_base_eq_coord]
  exact ⟨σ, hσ, H⟩

theorem clSub_QG_inf_Qa_eq_Pfst {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) {σ : Vt S D.g D.t}
    (hcl : S.cl (h * S.z * h⁻¹) = D.coord (σ, 0)) : S.clSub (S.QG ⊓ S.Qa h) = D.Pfst σ := by
  obtain ⟨τ, hτ, H⟩ := D.clSub_cases hQ hne
  rcases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain rfl : σ = τ := congrArg Prod.fst (D.coord.injective (hcl.symm.trans h1))
    exact h2
  · exact absurd (congrArg Prod.snd (D.coord.injective (hcl.symm.trans h1))).symm hτ
  · exact absurd (congrArg Prod.snd (D.coord.injective (hcl.symm.trans h1))).symm hτ

theorem clSub_QG_inf_Qa_eq_Psnd {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) {σ : Vt S D.g D.t}
    (hcl : S.cl (h * S.z * h⁻¹) = D.coord (0, σ)) : S.clSub (S.QG ⊓ S.Qa h) = D.Psnd σ := by
  obtain ⟨τ, hτ, H⟩ := D.clSub_cases hQ hne
  rcases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (congrArg Prod.fst (D.coord.injective (hcl.symm.trans h1))).symm hτ
  · obtain rfl : σ = τ := congrArg Prod.snd (D.coord.injective (hcl.symm.trans h1))
    exact h2
  · exact absurd (congrArg Prod.fst (D.coord.injective (hcl.symm.trans h1))).symm hτ

theorem clSub_QG_inf_Qa_eq_Pdiag {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) {σ : Vt S D.g D.t}
    (hcl : S.cl (h * S.z * h⁻¹) = D.coord (σ, σ)) : S.clSub (S.QG ⊓ S.Qa h) = D.Pdiag σ := by
  obtain ⟨τ, hτ, H⟩ := D.clSub_cases hQ hne
  rcases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := D.coord.injective (hcl.symm.trans h1)
    exact absurd ((congrArg Prod.fst this).symm.trans (congrArg Prod.snd this)) hτ
  · have := D.coord.injective (hcl.symm.trans h1)
    exact absurd ((congrArg Prod.snd this).symm.trans (congrArg Prod.fst this)) hτ
  · obtain rfl : σ = τ := congrArg Prod.fst (D.coord.injective (hcl.symm.trans h1))
    exact h2

end S2Data

end CFSG.GF2Type.Smith1980Orth
