module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Steinberg.Isogeny.Minuscule
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.TitsSimplicity.Core

public section

namespace CFSG.ClassicalInvolution.ModelFacts.A2Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.TitsSimplicity

section Generic

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

theorem exists_char_of_mem_iSup_torus {g : hV.minGroup k} (hg : g ∈ ⨆ i, hV.torus k i) :
    ∃ u : Fin τ.rank → kˣ, hV.endo k g =
      diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k) := by
  have hone : ∃ u : Fin τ.rank → kˣ, hV.endo k 1 =
      diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k) :=
    ⟨1, by
      rw [MinData.Valid.endo_one, ← diagOp_one]
      congr 1
      funext a
      simp [MinData.Valid.charHom_apply]⟩
  have hmul : ∀ x y : hV.minGroup k,
      (∃ u : Fin τ.rank → kˣ, hV.endo k x =
        diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k)) →
      (∃ u : Fin τ.rank → kˣ, hV.endo k y =
        diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k)) →
      ∃ u : Fin τ.rank → kˣ, hV.endo k (x * y) =
        diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k) := by
    rintro x y ⟨u, hux⟩ ⟨u', huy⟩
    refine ⟨u * u', ?_⟩
    rw [MinData.Valid.endo_mul, hux, huy, diagOp_mul]
    congr 1
    funext a
    simp [MinData.Valid.charHom_apply, mul_zpow, Finset.prod_mul_distrib]
  refine Subgroup.iSup_induction _ (C := fun x => ∃ u : Fin τ.rank → kˣ, hV.endo k x =
    diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k)) hg
    (fun j x hx => ?_) hone hmul
  obtain ⟨t, rfl⟩ := (hV.mem_torus k).1 hx
  refine ⟨Pi.mulSingle j t, ?_⟩
  rw [MinData.Valid.endo_hm, MinData.hDiag]
  congr 1
  funext a
  rw [MinData.Valid.charHom_apply, Finset.prod_eq_single j
    (fun l _ hl => by simp [Pi.mulSingle_eq_of_ne hl]) (by simp)]
  simp

end Generic

section Central

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

theorem charHom_toWeight_single_eq_zero {z : hV.minGroup k}
    (hz : z ∈ Subgroup.center (hV.minGroup k)) {u : Fin τ.rank → kˣ}
    (hu : hV.endo k z =
      diagOp fun a => ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k))
    (i : Fin τ.rank) :
    MinData.Valid.charHom k u (MinData.toWeight (Pi.single i 1)) = 0 := by
  obtain ⟨a, b, ε, hε, hab, hwt⟩ := hV.exists_rootOp_single_ne_zero k (isRoot_single τ i)
  have hc := congrArg (hV.endo k) ((Subgroup.mem_center_iff.1 hz) (hV.xm k (Pi.single i 1) 1))
  rw [MinData.Valid.endo_mul, MinData.Valid.endo_mul, hu, MinData.Valid.endo_xm] at hc
  have h1 := congrArg (fun f : Module.End k (Fin D.d →₀ k) => f (Finsupp.single a 1) b) hc
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, one_smul, hab,
    map_add, map_smul, diagOp_single, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul] at h1
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have h2 : ((Additive.toMul (MinData.Valid.charHom k u (D.wt a)) : kˣ) : k) =
      ((Additive.toMul (MinData.Valid.charHom k u (D.wt b)) : kˣ) : k) := by
    apply mul_left_cancel₀ hε0
    linear_combination h1
  have h4 : MinData.Valid.charHom k u (D.wt a) = MinData.Valid.charHom k u (D.wt b) :=
    Additive.toMul.injective (Units.ext h2)
  rw [hwt, map_add] at h4
  simpa using h4

theorem charHom_toWeight_eq_zero {u : Fin τ.rank → kˣ}
    (h : ∀ i, MinData.Valid.charHom k u (MinData.toWeight (Pi.single i 1)) = 0)
    (n : Fin τ.rank → ℤ) : MinData.Valid.charHom k u (MinData.toWeight n) = 0 := by
  have hn : n = ∑ i, n i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  let φ : (Fin τ.rank → ℤ) →+ Additive kˣ :=
    (MinData.Valid.charHom k u).comp (AddMonoidHom.mk' MinData.toWeight MinData.toWeight_add)
  have hφ : φ n = 0 := by
    rw [hn, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul]
    change n i • MinData.Valid.charHom k u (MinData.toWeight (Pi.single i 1)) = 0
    rw [h i, smul_zero]
  exact hφ

end Central

section Power

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

theorem diagOp_pow_nat {d : ℕ} (f : Fin d → k) (m : ℕ) : diagOp f ^ m = diagOp (f ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, diagOp_one]
  | succ m ih => rw [pow_succ, pow_succ, ih, diagOp_mul]

theorem endo_pow_nat (g : hV.minGroup k) (m : ℕ) : hV.endo k (g ^ m) = hV.endo k g ^ m := by
  induction m with
  | zero => exact MinData.Valid.endo_one hV k
  | succ m ih => rw [pow_succ, MinData.Valid.endo_mul, ih, pow_succ]

theorem pow_eq_one_of_central {N : ℕ}
    (hN : ∀ j : Fin τ.rank, ∃ n : Fin τ.rank → ℤ,
      MinData.toWeight n = (N : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ))
    {z : hV.minGroup k} (hz : z ∈ Subgroup.center (hV.minGroup k))
    (hzT : z ∈ ⨆ i, hV.torus k i) : z ^ N = 1 := by
  obtain ⟨u, hu⟩ := exists_char_of_mem_iSup_torus hV k hzT
  have hzero := charHom_toWeight_eq_zero k (charHom_toWeight_single_eq_zero hV k hz hu)
  have huN : ∀ j, u j ^ N = 1 := fun j => by
    obtain ⟨n, hn⟩ := hN j
    have h1 := hzero n
    rw [hn, map_zsmul] at h1
    have h2 := congrArg Additive.toMul h1
    rw [toMul_zsmul, MinData.Valid.charHom_single, zpow_natCast] at h2
    exact h2
  apply hV.endo_injective k
  rw [endo_pow_nat, hu, diagOp_pow_nat, MinData.Valid.endo_one, ← diagOp_one]
  congr 1
  funext a
  rw [Pi.pow_apply, Pi.one_apply, ← Units.val_pow_eq_pow_val, MinData.Valid.charHom_apply]
  have : (∏ j, u j ^ D.wt a j) ^ N = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, huN j, one_zpow]
  rw [this, Units.val_one]

end Power

section Tables

@[expose] def adjE7 : List (List ℤ) :=
  [[4, 4, 6, 8, 6, 4, 2], [4, 7, 8, 12, 9, 6, 3], [6, 8, 12, 16, 12, 8, 4],
    [8, 12, 16, 24, 18, 12, 6], [6, 9, 12, 18, 15, 10, 5], [4, 6, 8, 12, 10, 8, 4],
    [2, 3, 4, 6, 5, 4, 3]]

@[expose] def adjE6 : List (List ℤ) :=
  [[4, 3, 5, 6, 4, 2], [3, 6, 6, 9, 6, 3], [5, 6, 10, 12, 8, 4], [6, 9, 12, 18, 12, 6],
    [4, 6, 8, 12, 10, 5], [2, 3, 4, 6, 5, 4]]

theorem exists_toWeight_eq_two_E7 (j : Fin (Tag.rank .E7)) :
    ∃ n : Fin (Tag.rank .E7) → ℤ,
      MinData.toWeight n = ((2 : ℕ) : ℤ) • (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) := by
  refine ⟨fun i => (adjE7.getD i []).getD j 0, ?_⟩
  revert j
  decide +kernel

theorem exists_toWeight_eq_three_E6 (j : Fin (Tag.rank .E6)) :
    ∃ n : Fin (Tag.rank .E6) → ℤ,
      MinData.toWeight n = ((3 : ℕ) : ℤ) • (Pi.single j 1 : Fin (Tag.rank .E6) → ℤ) := by
  refine ⟨fun i => (adjE6.getD i []).getD j 0, ?_⟩
  revert j
  decide +kernel

end Tables

section Centre

variable (k : Type) [Field k]

theorem center_pow_two_e7 {z : ↥(e7Data_valid.minGroup k)}
    (hz : z ∈ Subgroup.center ↥(e7Data_valid.minGroup k)) : z ^ 2 = 1 := by
  have hct := e7Datum_isCTGroupDatum k
  have h1 := (center_eq_normalCore_borel hct (e7Datum_steinbergExtras k)
    (e7Datum_bruhatExtras k)) ▸ hz
  exact pow_eq_one_of_central e7Data_valid k exists_toWeight_eq_two_E7 hz
    (normalCore_borel_le_iSup hct (e7Datum_bruhatExtras k) h1)

theorem center_pow_three_e6 {z : ↥(e6Data_valid.minGroup k)}
    (hz : z ∈ Subgroup.center ↥(e6Data_valid.minGroup k)) : z ^ 3 = 1 := by
  have hct := e6Datum_isCTGroupDatum k
  have h1 := (center_eq_normalCore_borel hct (e6Datum_steinbergExtras k)
    (e6Datum_bruhatExtras k)) ▸ hz
  exact pow_eq_one_of_central e6Data_valid k exists_toWeight_eq_three_E6 hz
    (normalCore_borel_le_iSup hct (e6Datum_bruhatExtras k) h1)

end Centre

end CFSG.ClassicalInvolution.ModelFacts.A2Isogeny
