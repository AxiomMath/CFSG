module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def sec4IN (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    Subgroup (ProjOrth Q) :=
  omegaProj hQ ⊓ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q))

theorem sec4IB0_le_sec4IN (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    sec4IB0 fr ≤ sec4IN hQ fr := by
  intro x hx
  exact ⟨sec4IB0_le_omegaProj hQ fr hx, Subgroup.le_normalizer hx⟩

private theorem sec4I_eq_perm_of_toProj_mono_eq (fr : Sec4IFrame Q)
    {σ τ : Equiv.Perm (Fin 7)} {u w : Fin 7 → ZMod 2}
    (h : toProj Q (sec4IMono fr σ u) = toProj Q (sec4IMono fr τ w)) : σ = τ := by
  obtain ⟨z, hz, hz'⟩ := (QuotientGroup.mk'_eq_mk' (N := piGroup Q)).mp h
  rcases (mem_piGroup_iff (Q := Q)).mp hz with rfl | rfl
  · exact (sec4IMono_injective fr (by simpa using hz')).1
  · rw [← sec4IT_ones fr, sec4IT] at hz'
    rw [sec4IMono_mul] at hz'
    exact (mul_one σ).symm.trans (sec4IMono_injective fr hz').1

private theorem sec4I_exists_mono_of_mem_sec4IN (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {x : ProjOrth Q} (hx : x ∈ sec4IN hQ fr) :
    ∃ (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2), x = toProj Q (sec4IMono fr σ u) := by
  obtain ⟨g, hgω, hgx⟩ := (mem_omegaProj_iff hQ).mp hx.1
  have hnorm : toProj Q g ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q)) := by
    rw [hgx]
    exact hx.2
  obtain ⟨σ, u, hgu⟩ := sec4I_mono_of_normalizes_B0 hQ fr hnorm
  exact ⟨σ, u, by rw [← hgx, hgu]⟩

private theorem sec4I_theta_exists_unique (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (x : ↥(sec4IN hQ fr)) :
    ∃! σ : Equiv.Perm (Fin 7), ∃ u : Fin 7 → ZMod 2,
      (x : ProjOrth Q) = toProj Q (sec4IMono fr σ u) := by
  obtain ⟨σ, u, hu⟩ := sec4I_exists_mono_of_mem_sec4IN hQ fr x.2
  refine ⟨σ, ⟨u, hu⟩, ?_⟩
  rintro τ ⟨w, hw⟩
  exact sec4I_eq_perm_of_toProj_mono_eq fr (hw.symm.trans hu)

private noncomputable def sec4IThetaFun (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (x : ↥(sec4IN hQ fr)) : Equiv.Perm (Fin 7) :=
  Classical.choose (sec4I_theta_exists_unique hQ fr x)

private theorem sec4IThetaFun_spec (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (x : ↥(sec4IN hQ fr)) :
    ∃ u : Fin 7 → ZMod 2,
      (x : ProjOrth Q) = toProj Q (sec4IMono fr (sec4IThetaFun hQ fr x) u) :=
  (Classical.choose_spec (sec4I_theta_exists_unique hQ fr x)).1

private theorem sec4IThetaFun_one (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    sec4IThetaFun hQ fr 1 = 1 := by
  have h1 : ∃ u : Fin 7 → ZMod 2,
      ((1 : ↥(sec4IN hQ fr)) : ProjOrth Q) = toProj Q (sec4IMono fr 1 u) :=
    ⟨0, by rw [Subgroup.coe_one, sec4IMono_one, map_one]⟩
  exact ((Classical.choose_spec (sec4I_theta_exists_unique hQ fr 1)).2 1 h1).symm

private theorem sec4IThetaFun_mul (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (x y : ↥(sec4IN hQ fr)) :
    sec4IThetaFun hQ fr (x * y) = sec4IThetaFun hQ fr x * sec4IThetaFun hQ fr y := by
  obtain ⟨u, hu⟩ := sec4IThetaFun_spec hQ fr x
  obtain ⟨w, hw⟩ := sec4IThetaFun_spec hQ fr y
  have hxy : ((x * y : ↥(sec4IN hQ fr)) : ProjOrth Q) =
      toProj Q (sec4IMono fr (sec4IThetaFun hQ fr x * sec4IThetaFun hQ fr y)
        (fun i => w i + u ((sec4IThetaFun hQ fr y) i))) := by
    rw [Subgroup.coe_mul, hu, hw, ← map_mul, sec4IMono_mul]
  exact ((Classical.choose_spec (sec4I_theta_exists_unique hQ fr (x * y))).2
    (sec4IThetaFun hQ fr x * sec4IThetaFun hQ fr y)
    ⟨fun i => w i + u ((sec4IThetaFun hQ fr y) i), hxy⟩).symm

private noncomputable def sec4ITheta (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    ↥(sec4IN hQ fr) →* Equiv.Perm (Fin 7) where
  toFun := sec4IThetaFun hQ fr
  map_one' := sec4IThetaFun_one hQ fr
  map_mul' := sec4IThetaFun_mul hQ fr

private theorem sec4IP_inv (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) :
    (sec4IP fr σ)⁻¹ = sec4IP fr σ⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [sec4IP_mul, mul_inv_cancel, sec4IP_one])

private theorem sec4IPsi_conj_inv_mem_B0 (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7))
    {z : ProjOrth Q} (hz : z ∈ sec4IB0 fr) :
    (toProj Q (sec4IP fr σ))⁻¹ * z * toProj Q (sec4IP fr σ) ∈ sec4IB0 fr := by
  obtain ⟨v, hv, rfl⟩ := (mem_sec4IB0_iff fr).mp hz
  have hinv : (toProj Q (sec4IP fr σ))⁻¹ = toProj Q (sec4IP fr σ⁻¹) := by
    rw [← map_inv, sec4IP_inv]
  have hinv2 : (toProj Q (sec4IP fr σ⁻¹))⁻¹ = toProj Q (sec4IP fr σ) := by
    rw [← map_inv, sec4IP_inv, inv_inv]
  rw [hinv, ← hinv2]
  change toProj Q (sec4IMono fr σ⁻¹ 0) * sec4IPsi fr v *
    (toProj Q (sec4IMono fr σ⁻¹ 0))⁻¹ ∈ sec4IB0 fr
  rw [sec4IPsi_conj_mono fr σ⁻¹ 0 v]
  exact sec4IPsi_mem_sec4IB0 fr (sec4I_isEvenVec_permVec σ⁻¹ hv)

private theorem sec4IP_mem_normalizer_B0 (fr : Sec4IFrame Q) (σ : Equiv.Perm (Fin 7)) :
    toProj Q (sec4IP fr σ) ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q)) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    exact sec4IPsi_conj_inv_mem_B0 fr σ hh
  · intro hh
    have hinv : (toProj Q (sec4IP fr σ))⁻¹ = toProj Q (sec4IP fr σ⁻¹) := by
      rw [← map_inv, sec4IP_inv]
    have heq : (toProj Q (sec4IP fr σ⁻¹))⁻¹ *
        ((toProj Q (sec4IP fr σ))⁻¹ * h * toProj Q (sec4IP fr σ)) *
        toProj Q (sec4IP fr σ⁻¹) = h := by
      rw [← hinv]
      group
    rw [← heq]
    exact sec4IPsi_conj_inv_mem_B0 fr σ⁻¹ hh

private theorem sec4IP_mem_sec4IN (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {σ : Equiv.Perm (Fin 7)} (hσ : Equiv.Perm.sign σ = 1) :
    toProj Q (sec4IP fr σ) ∈ sec4IN hQ fr :=
  ⟨(mem_omegaProj_iff hQ).mpr ⟨sec4IP fr σ,
      (sec4IMono_mem_omegaGroup_iff hQ fr σ 0).mpr ⟨hσ, by simp [IsEvenVec]⟩, rfl⟩,
    sec4IP_mem_normalizer_B0 fr σ⟩

theorem sec4I_exists_perm_hom (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    ∃ θ : ↥(sec4IN hQ fr) →* Equiv.Perm (Fin 7),
      (∀ x : ↥(sec4IN hQ fr), ∃ u : Fin 7 → ZMod 2,
        (x : ProjOrth Q) = toProj Q (sec4IMono fr (θ x) u)) ∧
      (∀ x, Equiv.Perm.sign (θ x) = 1) ∧
      (∀ σ : Equiv.Perm (Fin 7), Equiv.Perm.sign σ = 1 → ∃ x, θ x = σ) ∧
      (∀ x, θ x = 1 ↔ (x : ProjOrth Q) ∈ sec4IB0 fr) := by
  refine ⟨sec4ITheta hQ fr, ?_, ?_, ?_, ?_⟩
  · intro x
    exact sec4IThetaFun_spec hQ fr x
  · intro x
    obtain ⟨g, hgω, hgx⟩ := (mem_omegaProj_iff hQ).mp x.2.1
    have hnorm : toProj Q g ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q)) := by
      rw [hgx]
      exact x.2.2
    obtain ⟨σ', u', hg'⟩ := sec4I_mono_of_normalizes_B0 hQ fr hnorm
    have hsign' : Equiv.Perm.sign σ' = 1 :=
      ((sec4IMono_mem_omegaGroup_iff hQ fr σ' u').mp (by rw [← hg']; exact hgω)).1
    obtain ⟨u, hu⟩ := sec4IThetaFun_spec hQ fr x
    have hσ : σ' = sec4IThetaFun hQ fr x := by
      apply sec4I_eq_perm_of_toProj_mono_eq fr
      rw [← hg', hgx, hu]
    change Equiv.Perm.sign (sec4IThetaFun hQ fr x) = 1
    rw [← hσ]
    exact hsign'
  · intro σ hσ
    let xN : ↥(sec4IN hQ fr) := ⟨toProj Q (sec4IP fr σ), sec4IP_mem_sec4IN hQ fr hσ⟩
    refine ⟨xN, ?_⟩
    have h1 : ∃ u : Fin 7 → ZMod 2, (xN : ProjOrth Q) = toProj Q (sec4IMono fr σ u) := by
      refine ⟨0, ?_⟩
      dsimp only [xN]
      rfl
    exact ((Classical.choose_spec (sec4I_theta_exists_unique hQ fr xN)).2 σ h1).symm
  · intro x
    constructor
    · intro hθ
      obtain ⟨u, hu⟩ := sec4IThetaFun_spec hQ fr x
      have hθ' : sec4IThetaFun hQ fr x = 1 := hθ
      rw [hθ'] at hu
      rw [hu]
      change sec4IPsi fr u ∈ sec4IB0 fr
      rcases em (IsEvenVec u) with hu_even | hu_odd
      · exact sec4IPsi_mem_sec4IB0 fr hu_even
      · rw [← sec4IPsi_add_ones fr u]
        exact sec4IPsi_mem_sec4IB0 fr (sec4I_isEvenVec_add_ones hu_odd)
    · intro hx
      obtain ⟨v, hv, hvx⟩ := (mem_sec4IB0_iff fr).mp hx
      have h1 : ∃ u : Fin 7 → ZMod 2, (x : ProjOrth Q) = toProj Q (sec4IMono fr 1 u) :=
        ⟨v, by rw [← hvx]; rfl⟩
      exact ((Classical.choose_spec (sec4I_theta_exists_unique hQ fr x)).2 1 h1).symm

theorem natCard_sec4IN (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) :
    Nat.card (sec4IN hQ fr) = 2 ^ 6 * 2520 := by
  obtain ⟨θ, -, hsign, hsurj, hker⟩ := sec4I_exists_perm_hom hQ fr
  have hker_eq : θ.ker = (sec4IB0 fr).subgroupOf (sec4IN hQ fr) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker x
  have hcard_ker : Nat.card θ.ker = 2 ^ 6 := by
    rw [hker_eq, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (sec4IB0_le_sec4IN hQ fr)).toEquiv]
    exact sec4IB0_card fr
  have hrange : θ.range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · intro σ hσ
      rw [MonoidHom.mem_range] at hσ
      obtain ⟨x, rfl⟩ := hσ
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hsign x
    · intro σ hσ
      rw [MonoidHom.mem_range]
      exact hsurj σ (Equiv.Perm.mem_alternatingGroup.mp hσ)
  have hcard_range : Nat.card θ.range = 2520 := by
    rw [hrange, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  calc Nat.card (sec4IN hQ fr) = Nat.card θ.ker * Nat.card θ.range :=
        (Subgroup.card_ker_mul_card_range θ).symm
    _ = 2 ^ 6 * 2520 := by rw [hcard_ker, hcard_range]

theorem sec4I_conj_of_mem_sec4IN (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) {x : ProjOrth Q}
    (hx : x ∈ sec4IN hQ fr) :
    ∃ σ : Equiv.Perm (Fin 7), Equiv.Perm.sign σ = 1 ∧
      ∀ v : Fin 7 → ZMod 2, x * sec4IPsi fr v * x⁻¹ = sec4IPsi fr (permVec σ v) := by
  obtain ⟨θ, hspec, hsign, -, -⟩ := sec4I_exists_perm_hom hQ fr
  let xN : ↥(sec4IN hQ fr) := ⟨x, hx⟩
  refine ⟨θ xN, hsign xN, ?_⟩
  intro v
  obtain ⟨u, hu⟩ := hspec xN
  have hu' : x = toProj Q (sec4IMono fr (θ xN) u) := by
    simpa only [xN] using hu
  rw [hu']
  exact sec4IPsi_conj_mono fr (θ xN) u v

theorem sec4I_exists_mem_sec4IN_of_perm (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    {σ : Equiv.Perm (Fin 7)} (hσ : Equiv.Perm.sign σ = 1) :
    ∃ x ∈ sec4IN hQ fr,
      ∀ v : Fin 7 → ZMod 2, x * sec4IPsi fr v * x⁻¹ = sec4IPsi fr (permVec σ v) := by
  refine ⟨toProj Q (sec4IP fr σ), sec4IP_mem_sec4IN hQ fr hσ, ?_⟩
  intro v
  exact sec4IPsi_conj_mono fr σ 0 v

end CFSG.OddStandard.SmallF3.Omega
