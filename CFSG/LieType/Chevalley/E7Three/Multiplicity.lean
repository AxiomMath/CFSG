module

public import CFSG.LieType.Chevalley.E7Three.Images

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Multiplicity

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.PauliWords CFSG.LieType.Chevalley.E7Three.Product
  CFSG.LieType.Chevalley.E7Three.Images CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

@[expose] def multiplicityWord (ζ : Kˣ) : adjointGroup .E7 K :=
  ((List.finRange Tag.E7.rank).map fun i =>
    torusElement .E7 K i (ζ ^ multiplicityCochar i)).prod

theorem cartanChar_multiplicity (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    cartanChar (cubeChar ζ multiplicityCochar) = cubeChar ζ multiplicityExp := by
  funext j
  change cartanChar (fun i => ζ ^ multiplicityCochar i) j = ζ ^ multiplicityExp j
  rw [cartanChar_zpow]
  calc
    ζ ^ (∑ i, multiplicityCochar i * Tag.E7.cartan i j) =
        ζ ^ ((∑ i, multiplicityCochar i * Tag.E7.cartan i j) % 3) :=
      zpow_eq_zpow_emod' _ hζ
    _ = ζ ^ (multiplicityExp j % 3) := by
      congr 1
      fin_cases j <;> rfl
    _ = ζ ^ multiplicityExp j := (zpow_eq_zpow_emod' _ hζ).symm

theorem multiplicityWord_val (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (multiplicityWord ζ : ModGL .E7 K) = rootDiagUnit .E7 (cubeChar ζ multiplicityExp) := by
  rw [multiplicityWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange Tag.E7.rank).map fun i =>
    torusElt .E7 K i (ζ ^ multiplicityCochar i)).prod = _
  rw [list_prod_torusElt_eq_rootDiagUnit]
  change rootDiagUnit .E7 (cartanChar (cubeChar ζ multiplicityCochar)) = _
  rw [cartanChar_multiplicity ζ hζ]

theorem multiplicityWord_mem_torusGroup (ζ : Kˣ) :
    (multiplicityWord ζ : ModGL .E7 K) ∈ torusGroup .E7 K := by
  rw [multiplicityWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange Tag.E7.rank).map fun i =>
    torusElt .E7 K i (ζ ^ multiplicityCochar i)).prod ∈ _
  refine Subgroup.list_prod_mem _ ?_
  rintro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_torusGroup i _

theorem multiplicityWord_pow_three (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    multiplicityWord ζ ^ 3 = 1 := by
  apply Subtype.ext
  change (multiplicityWord ζ : ModGL .E7 K) ^ 3 = 1
  rw [multiplicityWord_val ζ hζ]
  change (rootDiagUnitHom .E7 K (cubeChar ζ multiplicityExp)) ^ 3 = 1
  rw [← map_pow, cubeChar_pow_three ζ hζ multiplicityExp, map_one]

theorem multiplicityWord_val_product (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (multiplicityWord ζ : ModGL .E7 K) =
      torusElt .E7 K (e7Index 1) ζ * torusElt .E7 K (e7Index 3) (ζ ^ 2) *
        torusElt .E7 K (e7Index 5) (ζ ^ 2) * torusElt .E7 K (e7Index 6) ζ := by
  have ht (i : Fin 7) : torusElt .E7 K i (1 : Kˣ) = 1 :=
    CFSG.Blueprint.Chevalley.torusElt_one (τ := .E7) (R := K) i
  rw [multiplicityWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange 7).map fun i : Fin 7 =>
    torusElt .E7 K i (ζ ^ multiplicityCochar i)).prod = _
  simp [List.finRange_succ, multiplicityCochar, ht, hζ, e7Index, mul_assoc]

theorem prodHom_multiplicity (w : NativeFrame K) (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    prodHom w ![centralWord ζ, centralWord (ζ ^ 2), 1] =
      (multiplicityWord ζ : ModGL .E7 K) := by
  have h4 : (ζ ^ 2) ^ 2 = ζ := by
    rw [← pow_mul]
    change ζ ^ 4 = ζ
    rw [pow_succ, hζ, one_mul]
  rw [prodHom_apply]
  change theta w 0 (centralWord ζ) * theta w 1 (centralWord (ζ ^ 2)) * theta w 2 1 = _
  rw [theta_central_zero, theta_central_one, map_one, h4,
    multiplicityWord_val_product ζ hζ]
  simp only [mul_one, mul_assoc]

theorem multiplicityWord_commute_adjProdHom (w : NativeFrame K) (ζ : Kˣ)
    (hζ : ζ ^ 3 = 1) (f : Fin 3 → SL(3, K)) :
    Commute (multiplicityWord ζ) (adjProdHom w f) := by
  have hζ2 : (ζ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hζ, one_pow]
  have hc : Commute ![centralWord ζ, centralWord (ζ ^ 2), (1 : SL(3, K))] f := by
    change ![centralWord ζ, centralWord (ζ ^ 2), (1 : SL(3, K))] * f =
      f * ![centralWord ζ, centralWord (ζ ^ 2), (1 : SL(3, K))]
    funext i
    fin_cases i
    · exact (centralWord_commute ζ hζ (f 0)).eq
    · exact (centralWord_commute (ζ ^ 2) hζ2 (f 1)).eq
    · simp
  change multiplicityWord ζ * adjProdHom w f = adjProdHom w f * multiplicityWord ζ
  apply Subtype.ext
  change (multiplicityWord ζ : ModGL .E7 K) * prodHom w f =
    prodHom w f * (multiplicityWord ζ : ModGL .E7 K)
  rw [← prodHom_multiplicity w ζ hζ]
  exact (hc.map (prodHom w)).eq

end CFSG.LieType.Chevalley.E7Three.Multiplicity
