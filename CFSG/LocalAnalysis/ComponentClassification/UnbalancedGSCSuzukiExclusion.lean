module

public import CFSG.LieType.Ree.SuzukiMatrixIdentities
public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG.Blueprint CFSG.LieType.Ree

namespace SuzukiExclusion

variable {K : Type} [Field K]

theorem isElementaryAbelian_top_multiplicative (h2 : (2 : K) = 0) :
    CFSG.IsElementaryAbelian 2 (⊤ : Subgroup (Multiplicative K)) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
  change (x : Multiplicative K) ^ 2 = 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul]

@[expose] noncomputable def suzukiCenterHom (a : ℕ) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Multiplicative K →* suzukiGroup a K where
  toFun v := suzukiSElt a K 0 (Multiplicative.toAdd v)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact (suzuki_unipotent_product a hK).2.2.2.2.1
  map_mul' v w := by
    apply Subtype.ext
    apply Units.ext
    change suzukiS a 0 (Multiplicative.toAdd (v * w)) =
      suzukiS a 0 (Multiplicative.toAdd v) * suzukiS a 0 (Multiplicative.toAdd w)
    rw [suzukiS_mul a hK, toAdd_mul]
    simp

theorem suzukiCenterHom_injective (a : ℕ) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (suzukiCenterHom a hK) := by
  intro v w h
  have h' := congrArg (fun g : suzukiGroup a K =>
    ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) h
  have := ((suzuki_unipotent_product a hK).2.2.2.2.2 0 _ 0 _).mp h'
  exact Multiplicative.toAdd.injective this.2

end SuzukiExclusion

open SuzukiExclusion

theorem dihedral_sylow_suzuki_model_exclusion {T : Type} [Group T] {p f : ℕ}
    (hT : SuzukiModel T p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hT
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hK
  have : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK').1
  have := isElementaryAbelian_top_multiplicative h2
  let φ : Multiplicative K →* T := e.symm.toMonoidHom.comp (suzukiCenterHom a hK')
  have hφ : Function.Injective φ := e.symm.injective.comp (suzukiCenterHom_injective a hK')
  have hE := CFSG.IsElementaryAbelian.map (A := (⊤ : Subgroup (Multiplicative K))) (p := 2) φ
  have hcard : Nat.card ((⊤ : Subgroup (Multiplicative K)).map φ) = 2 ^ f := by
    rw [Subgroup.card_map_of_injective hφ, Subgroup.card_top]
    exact hK
  have hle := RankOneCenter.le_pRank_of_subgroup hE hcard
  have hrank :=
    (SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩).1
  omega

end CFSG.ComponentClassification.UnbalancedGS
