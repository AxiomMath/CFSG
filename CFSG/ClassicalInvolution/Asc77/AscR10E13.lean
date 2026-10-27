module

public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE6Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter

public section

set_option linter.unusedSectionVars false



namespace CFSG.ClassicalInvolution.ModelFacts.A2Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.TitsSimplicity

section Generic

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

theorem eq_one_of_central_of_roots {N : ℕ}
    (hN : ∀ j : Fin τ.rank, ∃ n : Fin τ.rank → ℤ,
      MinData.toWeight n = (N : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ))
    (hk : ∀ w : kˣ, w ^ N = 1 → w = 1)
    {z : hV.minGroup k} (hz : z ∈ Subgroup.center (hV.minGroup k))
    (hzT : z ∈ ⨆ i, hV.torus k i) : z = 1 := by
  obtain ⟨u, hu⟩ := exists_char_of_mem_iSup_torus hV k hzT
  have hzero := charHom_toWeight_eq_zero k (charHom_toWeight_single_eq_zero hV k hz hu)
  have huN : ∀ j, u j = 1 := fun j => by
    obtain ⟨n, hn⟩ := hN j
    have h1 := hzero n
    rw [hn, map_zsmul] at h1
    have h2 := congrArg Additive.toMul h1
    rw [toMul_zsmul, MinData.Valid.charHom_single, zpow_natCast] at h2
    exact hk _ h2
  apply hV.endo_injective k
  rw [hu, MinData.Valid.endo_one, ← diagOp_one]
  congr 1
  funext a
  rw [Pi.one_apply, MinData.Valid.charHom_apply]
  have : (∏ j, u j ^ D.wt a j) = 1 :=
    Finset.prod_eq_one fun j _ => by rw [huN j, one_zpow]
  rw [this, Units.val_one]

end Generic

section Centre

variable (k : Type) [Field k] [CharP k 3]

theorem center_eq_one_e6_of_char_three {z : ↥(e6Data_valid.minGroup k)}
    (hz : z ∈ Subgroup.center ↥(e6Data_valid.minGroup k)) : z = 1 := by
  have hct := e6Datum_isCTGroupDatum k
  have h1 := (center_eq_normalCore_borel hct (e6Datum_steinbergExtras k)
    (e6Datum_bruhatExtras k)) ▸ hz
  refine eq_one_of_central_of_roots e6Data_valid k exists_toWeight_eq_three_E6 (fun w hw => ?_)
    hz (normalCore_borel_le_iSup hct (e6Datum_bruhatExtras k) h1)
  have h3 : ((w : k) - 1) ^ 3 = 0 := by
    have hw' : (w : k) ^ 3 = 1 := by
      have := congrArg Units.val hw
      simpa using this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [sub_pow_char, hw']
    simp
  have h4 : (w : k) - 1 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h3
  exact Units.ext (sub_eq_zero.1 h4)

end Centre

end CFSG.ClassicalInvolution.ModelFacts.A2Isogeny

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

variable {p e : ℕ} [Fact p.Prime]

theorem e6Isogeny_ker_sq_three (h3 : p ^ e = 3) (x : E6sc p e)
    (hx : x ∈ (e6Isogeny (GaloisField p e)).ker) : x * x = 1 := by
  have hp : p = 3 := (CFSG.ClassicalInvolution.Asc77.T3CII.eq_three_of_pow_eq_three h3).1
  have : CharP (GaloisField p e) 3 := hp ▸ (inferInstance : CharP (GaloisField p e) p)
  have h1 := A2Isogeny.center_eq_one_e6_of_char_three (GaloisField p e)
    (ChevAut.e6Isogeny_ker_le_center (GaloisField p e) hx)
  rw [h1, mul_one]

end CFSG.ClassicalInvolution.ModelFacts.Levi
