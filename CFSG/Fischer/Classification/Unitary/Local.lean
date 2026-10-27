module

import all CFSG.Fischer.F4
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.Fischer.Classification.Unitary.Model

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer CFSG.Fischer

variable {n : ℕ}

noncomputable abbrev Stab (n : ℕ) : Subgroup (SUid frob (n + 2)) := MulAction.stabilizer _ (v₀ n)

theorem herm_v₀_smul_ι {g : SUid frob (n + 2)} (hg : g ∈ Stab n) (z : Fin n → K) :
    herm frob (v₀ n) (g • ι n z) = 0 := by
  rw [← (MulAction.mem_stabilizer_iff.1 hg), herm_smul_smul, herm_v₀_ι]

theorem smul_ι_eq {g : SUid frob (n + 2)} (hg : g ∈ Stab n) (z : Fin n → K) :
    g • ι n z = herm frob (u₀ n) (g • ι n z) • v₀ n + ι n (π n (g • ι n z)) :=
  decomp_of_perp (herm_v₀_smul_ι hg z)

@[expose] noncomputable def rhoL (g : SUid frob (n + 2)) : Module.End K (Fin n → K) :=
  (π n).comp ((Matrix.mulVecLin ((g : GL (Fin (n + 2)) K) : Matrix _ _ K)).comp (ι n))

theorem rhoL_apply (g : SUid frob (n + 2)) (z : Fin n → K) : rhoL g z = π n (g • ι n z) := rfl

theorem rhoL_mul {g h : SUid frob (n + 2)} (hg : g ∈ Stab n) (hh : h ∈ Stab n) :
    rhoL (g * h) = rhoL g * rhoL h := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, rhoL_apply, rhoL_apply, rhoL_apply]
  conv_lhs => rw [mul_smul, smul_ι_eq hh z, smul_add, smul_comm, MulAction.mem_stabilizer_iff.1 hg,
    map_add, map_smul, π_v₀, smul_zero, zero_add]

@[expose] noncomputable def rho (n : ℕ) : Stab n →* GL (Fin n) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrixAlgEquiv' (rhoL (g : SUid frob (n + 2)))
      map_one' := by
        rw [Subgroup.coe_one, ← map_one LinearMap.toMatrixAlgEquiv']
        congr 1
        exact LinearMap.ext fun z => by rw [rhoL_apply, one_smul, π_ι]; rfl
      map_mul' := fun g h => by
        rw [Subgroup.coe_mul, rhoL_mul g.2 h.2, LinearMap.toMatrixAlgEquiv'_mul] }

theorem rho_mulVec (g : Stab n) (z : Fin n → K) :
    ((rho n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z =
      π n ((g : SUid frob (n + 2)) • ι n z) := by
  show LinearMap.toMatrix' (rhoL (g : SUid frob (n + 2))) *ᵥ z = _
  exact LinearMap.toMatrix'_mulVec _ z

theorem rho_smul (g : Stab n) (z : Fin n → K) :
    rho n g • z = π n ((g : SUid frob (n + 2)) • ι n z) :=
  rho_mulVec g z

theorem rho_eq_one_iff (g : Stab n) :
    rho n g = 1 ↔ ∀ z : Fin n → K, π n ((g : SUid frob (n + 2)) • ι n z) = z := by
  constructor
  · intro h z
    rw [← rho_smul, h, one_smul]
  · intro h
    exact Units.ext (Matrix.ext_of_mulVec_single fun j => by
      rw [rho_mulVec, h, Units.val_one, one_mulVec])

theorem tvU_mem_Stab {w : Fin (n + 2) → K} (hw : herm frob w w = 0)
    (hvw : herm frob (v₀ n) w = 0) : tvU w ∈ Stab n :=
  MulAction.mem_stabilizer_iff.2
    (tvU_smul_of_herm_eq_zero hw (herm_eq_zero_comm frob frob_frob hvw))

theorem isotropic_π {w : Fin (n + 2) → K} (hw : herm frob w w = 0)
    (hvw : herm frob (v₀ n) w = 0) : herm frob (π n w) (π n w) = 0 := by
  have := herm_eq_coords w w
  rw [hvw, hw, mul_zero, map_zero, zero_mul, zero_add, zero_add] at this
  exact this.symm

theorem rho_tvU {w : Fin (n + 2) → K} (hw : herm frob w w = 0) (hvw : herm frob (v₀ n) w = 0) :
    (rho n ⟨tvU w, tvU_mem_Stab hw hvw⟩ : GL (Fin n) K) =
      ((tvU (π n w) : SUid frob n) : GL (Fin n) K) := by
  refine Units.ext (Matrix.ext_of_mulVec_single fun j => ?_)
  rw [rho_mulVec, coe_tvU_mulVec (isotropic_π hw hvw), tvU_smul hw, map_add, map_smul, π_ι,
    herm_ι_right]

@[expose] noncomputable def starVec (n : ℕ) : Set (Fin (n + 2) → K) :=
  {w | w ≠ 0 ∧ herm frob w w = 0 ∧ herm frob (v₀ n) w = 0 ∧ ∀ c : K, w ≠ c • v₀ n}

@[expose] noncomputable def L (n : ℕ) : Subgroup (SUid frob (n + 2)) :=
  Subgroup.closure (tvU '' starVec n)

theorem tvU_mem_L {w : Fin (n + 2) → K} (hw : w ∈ starVec n) : tvU w ∈ L n :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem L_le_Stab : L n ≤ Stab n := by
  rw [L, Subgroup.closure_le]
  rintro _ ⟨w, ⟨-, hw, hvw, -⟩, rfl⟩
  exact tvU_mem_Stab hw hvw

theorem smul_v₀_of_mem_L {g : SUid frob (n + 2)} (hg : g ∈ L n) : g • v₀ n = v₀ n :=
  MulAction.mem_stabilizer_iff.1 (L_le_Stab hg)

@[expose] noncomputable def lineVec (x : Fin n → K) (a : K) : Fin (n + 2) → K := a • v₀ n + ι n x

theorem herm_lineVec_left (x : Fin n → K) (a : K) (z : Fin (n + 2) → K) :
    herm frob (lineVec x a) z = frob a * herm frob (v₀ n) z + herm frob (ι n x) z := by
  rw [lineVec, herm_add_left, herm_smul_left]

theorem herm_lineVec_lineVec {x : Fin n → K} (hx : herm frob x x = 0) (a b : K) :
    herm frob (lineVec x a) (lineVec x b) = 0 := by
  rw [herm_lineVec_left, lineVec, herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι,
    herm_add_right, herm_smul_right, herm_ι_v₀, herm_ι_ι, hx]
  ring

theorem π_lineVec (x : Fin n → K) (a : K) : π n (lineVec x a) = x := by
  rw [lineVec, map_add, map_smul, π_v₀, smul_zero, zero_add, π_ι]

theorem herm_v₀_lineVec (x : Fin n → K) (a : K) : herm frob (v₀ n) (lineVec x a) = 0 := by
  rw [lineVec, herm_add_right, herm_smul_right, herm_v₀_v₀, herm_v₀_ι, mul_zero, add_zero]

theorem lineVec_mem_starVec {x : Fin n → K} (hx0 : x ≠ 0) (hx : herm frob x x = 0) (a : K) :
    lineVec x a ∈ starVec n := by
  refine ⟨fun h => hx0 ?_, herm_lineVec_lineVec hx a a, herm_v₀_lineVec x a, fun c h => hx0 ?_⟩
  · rw [← π_lineVec x a, h, map_zero]
  · rw [← π_lineVec x a, h, map_smul, π_v₀, smul_zero]

private theorem scalar_facts :
    frob (frob ω) * frob ω + frob ω * ω + frob 1 * 1 + frob 0 * 0 = 1 ∧
      frob ω + ω + 1 + 0 = (0 : K) ∧ frob (frob ω) + frob ω + frob 1 + frob 0 = (0 : K) ∧
      (1 : K) + 1 + 1 + 1 = 0 := by
  rw [omega_eq]
  simp only [frob_eF4, ← map_mul, ← map_add, ← map_one eF4, ← map_zero eF4, eF4_inj]
  decide

theorem tvU_v₀_eq_prod {x : Fin n → K} (hx : herm frob x x = 0) :
    tvU (v₀ n) = tvU (lineVec x (frob ω)) * tvU (lineVec x ω) * tvU (lineVec x 1) *
      tvU (lineVec x 0) := by
  obtain ⟨f1, f2, f3, f4⟩ := scalar_facts
  have hl : ∀ a, herm frob (lineVec x a) (lineVec x a) = 0 := fun a => herm_lineVec_lineVec hx a a
  refine ext_smul _ fun z => ?_
  rw [mul_smul, mul_smul, mul_smul, tvU_smul (hl 0), tvU_smul (hl 1), tvU_smul (hl ω),
    tvU_smul (hl (frob ω)), tvU_smul herm_v₀_v₀]
  simp only [herm_add_right, herm_smul_right, herm_lineVec_lineVec hx, mul_zero, add_zero]
  simp only [herm_lineVec_left]
  simp only [lineVec]
  match_scalars
  · ring
  · linear_combination herm frob (v₀ n) z * f1 + herm frob (ι n x) z * f2 +
      (herm frob (v₀ n) z * (1 - frob 1 - frob ω * ω - frob ω * frob (frob ω)) -
        herm frob (ι n x) z * (1 + frob ω + ω)) * two_eq_zero
  · linear_combination herm frob (v₀ n) z * f3 + herm frob (ι n x) z * f4 +
      (-herm frob (v₀ n) z * (frob 0 + frob 1 + frob ω + frob (frob ω)) -
        4 * herm frob (ι n x) z) * two_eq_zero

theorem tvU_v₀_mem_L (hn : 2 ≤ n) : tvU (v₀ n) ∈ L n := by
  have hx0 := isoVec_ne_zero hn
  have hx := isoVec_isotropic hn
  rw [tvU_v₀_eq_prod hx]
  exact mul_mem (mul_mem (mul_mem (tvU_mem_L (lineVec_mem_starVec hx0 hx _))
    (tvU_mem_L (lineVec_mem_starVec hx0 hx _))) (tvU_mem_L (lineVec_mem_starVec hx0 hx _)))
    (tvU_mem_L (lineVec_mem_starVec hx0 hx _))

theorem eq_bot_of_isPGroup_of_normalized (hn : 2 ≤ n) {P : Subgroup (GL (Fin n) K)}
    (hP : IsPGroup 2 P)
    (hnorm : ∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∀ p ∈ P,
      ((tvU x : SUid frob n) : GL (Fin n) K)⁻¹ * p * (tvU x : SUid frob n) ∈ P) : P = ⊥ := by
  set F := MulAction.fixedPoints P (Fin n → K)
  have hcard := hP.card_modEq_card_fixedPoints (Fin n → K)
  have h4 : Nat.card (Fin n → K) = 4 ^ n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
      GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h0F : (0 : Fin n → K) ∈ F := fun p => smul_zero _
  obtain ⟨z, hzF, hz0⟩ : ∃ z ∈ F, z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hF : F = {0} := Set.eq_singleton_iff_unique_mem.2 ⟨h0F, fun y hy => hcon y hy⟩
    have h1 : Nat.card F = 1 := by rw [hF]; exact Nat.card_unique
    obtain ⟨k, hk⟩ := dvd_pow (by norm_num : (2 : ℕ) ∣ 4) (by omega : n ≠ 0)
    rw [h4, hk, h1] at hcard
    unfold Nat.ModEq at hcard
    omega
  have hF_add : ∀ a b, a ∈ F → b ∈ F → a + b ∈ F := fun a b ha hb p => by
    rw [smul_add, ha p, hb p]
  have hF_smul : ∀ (c : K) a, a ∈ F → c • a ∈ F := fun c a ha p => by
    rw [smul_comm, ha p]
  have hF_sub : ∀ a b, a ∈ F → b ∈ F → a - b ∈ F := fun a b ha hb => by
    rw [sub_eq_add_neg, ← neg_one_smul K b]
    exact hF_add _ _ ha (hF_smul _ _ hb)
  have hF_tv : ∀ x : Fin n → K, x ≠ 0 → herm frob x x = 0 → ∀ a ∈ F,
      ((tvU x : SUid frob n) : GL (Fin n) K) • a ∈ F := by
    intro x hx0 hx a ha p
    set t := ((tvU x : SUid frob n) : GL (Fin n) K)
    have hp' := ha ⟨_, hnorm x hx0 hx p p.2⟩
    change (p : GL (Fin n) K) • t • a = t • a
    change (t⁻¹ * (p : GL (Fin n) K) * t) • a = a at hp'
    calc (p : GL (Fin n) K) • t • a = t • (t⁻¹ * (p : GL (Fin n) K) * t) • a := by
          rw [← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = t • a := by rw [hp']
  have hkey : ∀ y z : Fin n → K, herm frob y y = 0 → z ∈ F → herm frob y z ≠ 0 → y ∈ F := by
    intro y z hy hz hyz
    have hy0 : y ≠ 0 := by rintro rfl; exact hyz (herm_zero_left frob z)
    have h1 := hF_sub _ _ (hF_tv y hy0 hy z hz) hz
    have e : ((tvU y : SUid frob n) : GL (Fin n) K) • z - z = herm frob y z • y := by
      change tvU y • z - z = _
      rw [tvU_smul hy, add_sub_cancel_left]
    rw [e] at h1
    have := hF_smul (herm frob y z)⁻¹ _ h1
    rwa [smul_smul, inv_mul_cancel₀ hyz, one_smul] at this
  have hiso : ∀ y : Fin n → K, herm frob y y = 0 → y ∈ F := by
    intro y hy
    by_cases hy0 : y = 0
    · rw [hy0]; exact h0F
    obtain ⟨d, hd, hyd, hzd⟩ := exists_cno isUnitaryInvolution_frob hy0 hy hz0
    have hdF : d ∈ F := hkey d z hd hzF (by
      rw [herm_conj frob frob_frob z d]; exact frob_ne_zero hzd)
    exact hkey y d hy hdF hyd
  rw [eq_bot_iff]
  intro p hp
  rw [Subgroup.mem_bot]
  have hlin := linearMap_ext_isotropic hn
    (f := Matrix.mulVecLin ((p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (g := LinearMap.id)
    fun y hy => hiso y hy ⟨p, hp⟩
  exact Units.ext (Matrix.ext_of_mulVec_single fun j => by
    rw [Units.val_one, one_mulVec]
    exact LinearMap.congr_fun hlin _)

end CFSG.Fischer.Classification.Unitary
