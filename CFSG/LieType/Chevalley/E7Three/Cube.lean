module

public import CFSG.LieType.Chevalley.E7Three.Weyl

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Cube

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SectionRank
  CFSG.LieType.Chevalley.E7Three.Weyl
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [CharP K 2]

@[expose] def scalarWord (ζ : Kˣ) : adjointGroup .E7 K :=
  ((List.finRange Tag.E7.rank).map fun i => torusElement .E7 K i (ζ ^ scalarCochar i)).prod

@[expose] def pairedWord (ζ : Kˣ) : adjointGroup .E7 K :=
  ((List.finRange Tag.E7.rank).map fun i => torusElement .E7 K i (ζ ^ pairedCochar i)).prod

@[expose] def cyclic : adjointGroup .E7 K := CFSG.SectionRank.LargeRee.nrepHom .E7 K gamma

theorem cartanChar_scalar (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    cartanChar (cubeChar ζ scalarCochar) = cubeChar ζ scalarExp := by
  funext j
  change cartanChar (fun i => ζ ^ scalarCochar i) j = ζ ^ scalarExp j
  rw [cartanChar_zpow]
  calc
    ζ ^ (∑ i, scalarCochar i * Tag.E7.cartan i j) =
        ζ ^ ((∑ i, scalarCochar i * Tag.E7.cartan i j) % 3) := zpow_eq_zpow_emod' _ hζ
    _ = ζ ^ (scalarExp j % 3) := by
      congr 1
      fin_cases j <;> rfl
    _ = ζ ^ scalarExp j := (zpow_eq_zpow_emod' _ hζ).symm

theorem cartanChar_paired (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    cartanChar (cubeChar ζ pairedCochar) = cubeChar ζ pairedExp := by
  funext j
  change cartanChar (fun i => ζ ^ pairedCochar i) j = ζ ^ pairedExp j
  rw [cartanChar_zpow]
  calc
    ζ ^ (∑ i, pairedCochar i * Tag.E7.cartan i j) =
        ζ ^ ((∑ i, pairedCochar i * Tag.E7.cartan i j) % 3) := zpow_eq_zpow_emod' _ hζ
    _ = ζ ^ (pairedExp j % 3) := by
      congr 1
      fin_cases j <;> rfl
    _ = ζ ^ pairedExp j := (zpow_eq_zpow_emod' _ hζ).symm

theorem scalarWord_val (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (scalarWord ζ : ModGL .E7 K) = rootDiagUnit .E7 (cubeChar ζ scalarExp) := by
  rw [scalarWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange Tag.E7.rank).map fun i => torusElt .E7 K i (ζ ^ scalarCochar i)).prod = _
  rw [list_prod_torusElt_eq_rootDiagUnit]
  change rootDiagUnit .E7 (cartanChar (cubeChar ζ scalarCochar)) = _
  rw [cartanChar_scalar ζ hζ]

theorem pairedWord_val (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (pairedWord ζ : ModGL .E7 K) = rootDiagUnit .E7 (cubeChar ζ pairedExp) := by
  rw [pairedWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange Tag.E7.rank).map fun i => torusElt .E7 K i (ζ ^ pairedCochar i)).prod = _
  rw [list_prod_torusElt_eq_rootDiagUnit]
  change rootDiagUnit .E7 (cartanChar (cubeChar ζ pairedCochar)) = _
  rw [cartanChar_paired ζ hζ]

theorem scalarWord_mem_torusGroup (ζ : Kˣ) :
    (scalarWord ζ : ModGL .E7 K) ∈ torusGroup .E7 K := by
  rw [scalarWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange Tag.E7.rank).map fun i => torusElt .E7 K i (ζ ^ scalarCochar i)).prod ∈ _
  refine Subgroup.list_prod_mem _ ?_
  rintro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_torusGroup i _

theorem pairedWord_mem_torusGroup (ζ : Kˣ) :
    (pairedWord ζ : ModGL .E7 K) ∈ torusGroup .E7 K := by
  rw [pairedWord, Subgroup.val_list_prod, List.map_map]
  change ((List.finRange Tag.E7.rank).map fun i => torusElt .E7 K i (ζ ^ pairedCochar i)).prod ∈ _
  refine Subgroup.list_prod_mem _ ?_
  rintro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_torusGroup i _

theorem cyclic_pow_val (n : ℕ) :
    ((cyclic (K := K)) ^ n : ModGL .E7 K) =
      canonicalRep (coxeterSystem .E7) K (gamma ^ n) := by
  let N : WeylGroup .E7 →* ModGL .E7 K :=
    (adjointGroup .E7 K).subtype.comp (CFSG.SectionRank.LargeRee.nrepHom .E7 K)
  change (N gamma) ^ n = N (gamma ^ n)
  exact (N.map_pow gamma n).symm

theorem three_dvd_of_cyclic_pow_mem_torusGroup (n : ℕ)
    (hn : ((cyclic (K := K)) ^ n : ModGL .E7 K) ∈ torusGroup .E7 K) : 3 ∣ n := by
  rw [cyclic_pow_val] at hn
  have hpow : gamma ^ n = 1 :=
    (mapsRootLines_canonicalRep (gamma ^ n)).unique (mapsRootLines_of_mem_torusGroup hn)
  simpa only [orderOf_gamma] using orderOf_dvd_of_pow_eq_one hpow

theorem scalarWord_pow_three (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : scalarWord ζ ^ 3 = 1 := by
  apply Subtype.ext
  change (scalarWord ζ : ModGL .E7 K) ^ 3 = 1
  rw [scalarWord_val ζ hζ]
  change (rootDiagUnitHom .E7 K (cubeChar ζ scalarExp)) ^ 3 = 1
  rw [← map_pow, cubeChar_pow_three ζ hζ scalarExp, map_one]

theorem pairedWord_pow_three (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : pairedWord ζ ^ 3 = 1 := by
  apply Subtype.ext
  change (pairedWord ζ : ModGL .E7 K) ^ 3 = 1
  rw [pairedWord_val ζ hζ]
  change (rootDiagUnitHom .E7 K (cubeChar ζ pairedExp)) ^ 3 = 1
  rw [← map_pow, cubeChar_pow_three ζ hζ pairedExp, map_one]

theorem cyclic_pow_three : (cyclic (K := K)) ^ 3 = 1 := nrep_gamma_pow_three

theorem scalar_paired_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Commute (scalarWord ζ) (pairedWord ζ) := by
  change scalarWord ζ * pairedWord ζ = pairedWord ζ * scalarWord ζ
  apply Subtype.ext
  change (scalarWord ζ : ModGL .E7 K) * (pairedWord ζ : ModGL .E7 K) =
    (pairedWord ζ : ModGL .E7 K) * (scalarWord ζ : ModGL .E7 K)
  rw [scalarWord_val ζ hζ, pairedWord_val ζ hζ]
  change rootDiagUnitHom .E7 K (cubeChar ζ scalarExp) *
      rootDiagUnitHom .E7 K (cubeChar ζ pairedExp) =
    rootDiagUnitHom .E7 K (cubeChar ζ pairedExp) *
      rootDiagUnitHom .E7 K (cubeChar ζ scalarExp)
  rw [← map_mul, ← map_mul, mul_comm]

theorem cyclic_scalar_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Commute (cyclic (K := K)) (scalarWord ζ) := by
  change cyclic * scalarWord ζ = scalarWord ζ * cyclic
  apply Subtype.ext
  change (cyclic (K := K) : ModGL .E7 K) * (scalarWord ζ : ModGL .E7 K) =
    (scalarWord ζ : ModGL .E7 K) * (cyclic (K := K) : ModGL .E7 K)
  rw [scalarWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ scalarExp) =
    rootDiagUnit .E7 (cubeChar ζ scalarExp) * canonicalRep (coxeterSystem .E7) K gamma
  exact mul_inv_eq_iff_eq_mul.mp (gamma_conj_scalar ζ hζ)

theorem cyclic_paired_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Commute (cyclic (K := K)) (pairedWord ζ) := by
  change cyclic * pairedWord ζ = pairedWord ζ * cyclic
  apply Subtype.ext
  change (cyclic (K := K) : ModGL .E7 K) * (pairedWord ζ : ModGL .E7 K) =
    (pairedWord ζ : ModGL .E7 K) * (cyclic (K := K) : ModGL .E7 K)
  rw [pairedWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K gamma * rootDiagUnit .E7 (cubeChar ζ pairedExp) =
    rootDiagUnit .E7 (cubeChar ζ pairedExp) * canonicalRep (coxeterSystem .E7) K gamma
  exact mul_inv_eq_iff_eq_mul.mp (gamma_conj_paired ζ hζ)

@[expose] def generators (ζ : Kˣ) : Fin 3 → adjointGroup .E7 K :=
  ![scalarWord ζ, pairedWord ζ, cyclic (K := K)]

theorem generators_pow_three (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    ∀ i, generators ζ i ^ 3 = 1 := by
  intro i
  fin_cases i
  · exact scalarWord_pow_three ζ hζ
  · exact pairedWord_pow_three ζ hζ
  · exact cyclic_pow_three

theorem generators_commute (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    ∀ i j, Commute (generators ζ i) (generators ζ j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact scalar_paired_commute ζ hζ
  · exact (cyclic_scalar_commute ζ hζ).symm
  · exact (scalar_paired_commute ζ hζ).symm
  · exact Commute.refl _
  · exact (cyclic_paired_commute ζ hζ).symm
  · exact cyclic_scalar_commute ζ hζ
  · exact cyclic_paired_commute ζ hζ
  · exact Commute.refl _

@[expose] def cubeHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (Fin 3 → Multiplicative (ZMod 3)) →* adjointGroup .E7 K :=
  MonoidHom.noncommPiCoprod
    (fun i => zmodPowHom (generators ζ i) (generators_pow_three ζ hζ i))
    (fun i j _ x y => (generators_commute ζ hζ i j).pow_pow _ _)

theorem cubeHom_apply (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (f : Fin 3 → Multiplicative (ZMod 3)) :
    cubeHom ζ hζ f = scalarWord ζ ^ (Multiplicative.toAdd (f 0)).val *
      pairedWord ζ ^ (Multiplicative.toAdd (f 1)).val *
      (cyclic (K := K)) ^ (Multiplicative.toAdd (f 2)).val := by
  change Finset.noncommProd (Finset.univ : Finset (Fin 3))
    (fun i => generators ζ i ^ (Multiplicative.toAdd (f i)).val)
    (fun i _ j _ _ => (generators_commute ζ hζ i j).pow_pow _ _) = _
  refine (Finset.noncommProd_congr
    (f := fun i => generators ζ i ^ (Multiplicative.toAdd (f i)).val)
    (g := fun i => generators ζ i ^ (Multiplicative.toAdd (f i)).val)
    (show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from by decide +kernel)
    (fun _ _ => rfl)
    (fun i _ j _ _ => (generators_commute ζ hζ i j).pow_pow _ _)).trans ?_
  rw [Finset.noncommProd_insert_of_notMem ({1, 2} : Finset (Fin 3)) 0
      (fun i => generators ζ i ^ (Multiplicative.toAdd (f i)).val)
      (fun i _ j _ _ => (generators_commute ζ hζ i j).pow_pow _ _) (by decide +kernel),
    Finset.noncommProd_insert_of_notMem ({2} : Finset (Fin 3)) 1
      (fun i => generators ζ i ^ (Multiplicative.toAdd (f i)).val)
      (fun i _ j _ _ => (generators_commute ζ hζ i j).pow_pow _ _) (by decide +kernel),
    Finset.noncommProd_singleton (2 : Fin 3)
      (fun i => generators ζ i ^ (Multiplicative.toAdd (f i)).val)]
  exact (mul_assoc _ _ _).symm

theorem third_val_eq_zero_of_cubeHom_eq_one (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (f : Fin 3 → Multiplicative (ZMod 3)) (hf : cubeHom ζ hζ f = 1) :
    (Multiplicative.toAdd (f 2)).val = 0 := by
  let a := (Multiplicative.toAdd (f 0)).val
  let b := (Multiplicative.toAdd (f 1)).val
  let c := (Multiplicative.toAdd (f 2)).val
  have hp : scalarWord ζ ^ a * pairedWord ζ ^ b * (cyclic (K := K)) ^ c = 1 := by
    simpa only [cubeHom_apply] using hf
  have hi : (cyclic (K := K)) ^ c = (scalarWord ζ ^ a * pairedWord ζ ^ b)⁻¹ := by
    calc
      (cyclic (K := K)) ^ c = (scalarWord ζ ^ a * pairedWord ζ ^ b)⁻¹ *
          ((scalarWord ζ ^ a * pairedWord ζ ^ b) * (cyclic (K := K)) ^ c) := by group
      _ = (scalarWord ζ ^ a * pairedWord ζ ^ b)⁻¹ := by rw [hp, mul_one]
  let S := (adjointGroup .E7 K).subtype
  have hi' : (cyclic (K := K) : ModGL .E7 K) ^ c =
      ((scalarWord ζ : ModGL .E7 K) ^ a * (pairedWord ζ : ModGL .E7 K) ^ b)⁻¹ := by
    have e := congrArg S hi
    simpa only [S, map_pow, map_mul, map_inv, Subgroup.subtype_apply] using e
  have hc : ((cyclic (K := K)) ^ c : ModGL .E7 K) ∈ torusGroup .E7 K := by
    rw [hi']
    exact (torusGroup .E7 K).inv_mem ((torusGroup .E7 K).mul_mem
      ((torusGroup .E7 K).pow_mem (scalarWord_mem_torusGroup ζ) a)
      ((torusGroup .E7 K).pow_mem (pairedWord_mem_torusGroup ζ) b))
  have hd : 3 ∣ c := three_dvd_of_cyclic_pow_mem_torusGroup c hc
  have hlt : c < 3 := ZMod.val_lt _
  obtain ⟨t, ht⟩ := hd
  change c = 0
  omega

theorem first_two_vals_eq_zero_of_cubeHom_eq_one (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
    (f : Fin 3 → Multiplicative (ZMod 3)) (hf : cubeHom ζ hζ.pow_eq_one f = 1) :
    (Multiplicative.toAdd (f 0)).val = 0 ∧ (Multiplicative.toAdd (f 1)).val = 0 := by
  let a := (Multiplicative.toAdd (f 0)).val
  let b := (Multiplicative.toAdd (f 1)).val
  have hc0 := third_val_eq_zero_of_cubeHom_eq_one ζ hζ.pow_eq_one f hf
  have hp : scalarWord ζ ^ a * pairedWord ζ ^ b = 1 := by
    have e := hf
    rw [cubeHom_apply, hc0, pow_zero, mul_one] at e
    exact e
  have hcoords : cubeChar ζ scalarExp ^ a * cubeChar ζ pairedExp ^ b = 1 := by
    apply rootDiagUnit_injective
    change rootDiagUnitHom .E7 K (cubeChar ζ scalarExp ^ a * cubeChar ζ pairedExp ^ b) =
      rootDiagUnitHom .E7 K 1
    rw [map_mul, map_pow, map_pow, map_one]
    have e := congrArg (adjointGroup .E7 K).subtype hp
    simp only [map_mul, map_pow, map_one, Subgroup.subtype_apply] at e
    rw [scalarWord_val ζ hζ.pow_eq_one, pairedWord_val ζ hζ.pow_eq_one] at e
    exact e
  have hbpow : (ζ ^ 2) ^ b = 1 := by
    simpa [cubeChar, scalarExp, pairedExp] using congrFun hcoords (0 : Fin Tag.E7.rank)
  have hbd : 3 ∣ 2 * b := hζ.dvd_of_pow_eq_one (2 * b) (by
    simpa only [← pow_mul] using hbpow)
  have hb_lt : b < 3 := ZMod.val_lt _
  have hb0 : b = 0 := by
    obtain ⟨m, hm⟩ := hbd
    omega
  have hapow : ζ ^ a = 1 := by
    simpa [cubeChar, scalarExp, pairedExp, hb0] using congrFun hcoords (2 : Fin Tag.E7.rank)
  have had : 3 ∣ a := hζ.dvd_of_pow_eq_one a hapow
  have ha_lt : a < 3 := ZMod.val_lt _
  have ha0 : a = 0 := by
    obtain ⟨m, hm⟩ := had
    omega
  exact ⟨ha0, hb0⟩

theorem eq_one_of_cubeHom_eq_one (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3)
    (f : Fin 3 → Multiplicative (ZMod 3)) (hf : cubeHom ζ hζ.pow_eq_one f = 1) : f = 1 := by
  obtain ⟨h0, h1⟩ := first_two_vals_eq_zero_of_cubeHom_eq_one ζ hζ f hf
  have h2 := third_val_eq_zero_of_cubeHom_eq_one ζ hζ.pow_eq_one f hf
  funext i
  fin_cases i
  · apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (f 0) = 0
    exact (ZMod.val_eq_zero _).1 h0
  · apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (f 1) = 0
    exact (ZMod.val_eq_zero _).1 h1
  · apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (f 2) = 0
    exact (ZMod.val_eq_zero _).1 h2

theorem cubeHom_injective (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    Function.Injective (cubeHom ζ hζ.pow_eq_one) := by
  exact (injective_iff_map_eq_one (cubeHom ζ hζ.pow_eq_one)).2
    (eq_one_of_cubeHom_eq_one ζ hζ)

theorem card_range_cubeHom (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (cubeHom ζ hζ.pow_eq_one).range = 3 ^ 3 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (cubeHom_injective ζ hζ)).toEquiv,
    Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem generators_mem_range (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    ∀ i, generators ζ i ∈ (cubeHom ζ hζ).range := by
  have h1 : (1 : ZMod 3).val = 1 := by decide +kernel
  intro i
  fin_cases i
  · refine ⟨![Multiplicative.ofAdd (1 : ZMod 3), 1, 1], ?_⟩
    rw [cubeHom_apply]
    simp [generators, h1]
  · refine ⟨![1, Multiplicative.ofAdd (1 : ZMod 3), 1], ?_⟩
    rw [cubeHom_apply]
    simp [generators, h1]
  · refine ⟨![1, 1, Multiplicative.ofAdd (1 : ZMod 3)], ?_⟩
    rw [cubeHom_apply]
    simp [generators, h1]

theorem cubeChar_neg (ζ : Kˣ) (a : Fin Tag.E7.rank → ℤ) :
    cubeChar ζ (-a) = (cubeChar ζ a)⁻¹ := by
  funext i
  change ζ ^ (-a i) = (ζ ^ a i)⁻¹
  exact zpow_neg _ _

theorem cubeChar_add (ζ : Kˣ) (a b : Fin Tag.E7.rank → ℤ) :
    cubeChar ζ (fun i => a i + b i) = cubeChar ζ a * cubeChar ζ b := by
  funext i
  exact zpow_add _ _ _

theorem cubeChar_two (ζ : Kˣ) (a : Fin Tag.E7.rank → ℤ) :
    cubeChar ζ (fun i => 2 * a i) = cubeChar ζ a ^ 2 := by
  funext i
  change ζ ^ (2 * a i) = (ζ ^ a i) ^ 2
  rw [two_mul, zpow_add, pow_two]

@[expose] def a5CycleElement : adjointGroup .E7 K :=
  CFSG.SectionRank.LargeRee.nrepHom .E7 K a5Cycle

theorem a5CycleElement_conj_scalarWord (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    a5CycleElement * scalarWord ζ * a5CycleElement⁻¹ = scalarWord ζ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [scalarWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K a5Cycle * rootDiagUnit .E7 (cubeChar ζ scalarExp) *
    (canonicalRep (coxeterSystem .E7) K a5Cycle)⁻¹ = rootDiagUnit .E7 (cubeChar ζ scalarExp)
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_a5Cycle_scalar ζ hζ]

theorem a5CycleElement_conj_pairedWord (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    a5CycleElement * pairedWord ζ * a5CycleElement⁻¹ = pairedWord ζ * scalarWord ζ ^ 2 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  rw [pairedWord_val ζ hζ, scalarWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K a5Cycle * rootDiagUnit .E7 (cubeChar ζ pairedExp) *
    (canonicalRep (coxeterSystem .E7) K a5Cycle)⁻¹ =
      rootDiagUnit .E7 (cubeChar ζ pairedExp) * rootDiagUnit .E7 (cubeChar ζ scalarExp) ^ 2
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit, weylTuple_a5Cycle_paired ζ hζ,
    cubeChar_add, cubeChar_two]
  exact (rootDiagUnitHom .E7 K).map_mul _ _ |>.trans (by rw [map_pow]; rfl)

theorem a5CycleElement_conj_cyclic :
    a5CycleElement * cyclic (K := K) * a5CycleElement⁻¹ = cyclic := by
  have h := congrArg (CFSG.SectionRank.LargeRee.nrepHom .E7 K) a5Cycle_gamma_commute
  have hc : a5CycleElement (K := K) * cyclic = cyclic * a5CycleElement := by
    simpa only [a5CycleElement, cyclic, map_mul] using h
  rw [hc]
  group

theorem a5CycleElement_conj_mem_range (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    {y : adjointGroup .E7 K} (hy : y ∈ (cubeHom ζ hζ).range) :
    a5CycleElement * y * a5CycleElement⁻¹ ∈ (cubeHom ζ hζ).range := by
  obtain ⟨f, rfl⟩ := hy
  let E := (cubeHom ζ hζ).range
  let Q : adjointGroup .E7 K →* adjointGroup .E7 K :=
    (MulAut.conj (a5CycleElement (K := K))).toMonoidHom
  have h0 : Q (scalarWord ζ) = scalarWord ζ := a5CycleElement_conj_scalarWord ζ hζ
  have h1 : Q (pairedWord ζ) = pairedWord ζ * scalarWord ζ ^ 2 :=
    a5CycleElement_conj_pairedWord ζ hζ
  have h2 : Q (cyclic (K := K)) = cyclic := a5CycleElement_conj_cyclic
  change Q (cubeHom ζ hζ f) ∈ E
  rw [cubeHom_apply, Q.map_mul _ _, Q.map_mul _ _, Q.map_pow _ _, Q.map_pow _ _, Q.map_pow _ _,
    h0, h1, h2]
  exact E.mul_mem (E.mul_mem
    (E.pow_mem (generators_mem_range ζ hζ 0) _)
    (E.pow_mem (E.mul_mem (generators_mem_range ζ hζ 1)
      (E.pow_mem (generators_mem_range ζ hζ 0) 2)) _))
    (E.pow_mem (generators_mem_range ζ hζ 2) _)

theorem a5CycleElement_mem_normalizer (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    a5CycleElement (K := K) ∈
      Subgroup.normalizer ((cubeHom ζ hζ).range : Set (adjointGroup .E7 K)) := by
  classical
  letI : Fintype (cubeHom ζ hζ).range := MonoidHom.fintypeRange (cubeHom ζ hζ)
  exact Subgroup.mem_normalizer_fintype (fun y hy => a5CycleElement_conj_mem_range ζ hζ hy)

theorem rootDiagUnit_cubeChar_neg (ζ : Kˣ) (a : Fin Tag.E7.rank → ℤ) :
    rootDiagUnit .E7 (cubeChar ζ (-a)) = (rootDiagUnit .E7 (cubeChar ζ a))⁻¹ := by
  rw [cubeChar_neg]
  exact (rootDiagUnitHom .E7 K).map_inv (cubeChar ζ a)

@[expose] def moveElement : adjointGroup .E7 K :=
  CFSG.SectionRank.LargeRee.nrepHom .E7 K move

theorem moveElement_pow_two : (moveElement (K := K)) ^ 2 = 1 := nrep_move_pow_two

theorem moveElement_conj_scalarWord (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    moveElement * scalarWord ζ * moveElement⁻¹ = (pairedWord ζ)⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [scalarWord_val ζ hζ, pairedWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 (cubeChar ζ scalarExp) *
      (canonicalRep (coxeterSystem .E7) K move)⁻¹ = (rootDiagUnit .E7 (cubeChar ζ pairedExp))⁻¹
  rw [move_conj_scalar ζ hζ, rootDiagUnit_cubeChar_neg]

theorem moveElement_conj_pairedWord (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    moveElement * pairedWord ζ * moveElement⁻¹ = (scalarWord ζ)⁻¹ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [pairedWord_val ζ hζ, scalarWord_val ζ hζ]
  change canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 (cubeChar ζ pairedExp) *
      (canonicalRep (coxeterSystem .E7) K move)⁻¹ = (rootDiagUnit .E7 (cubeChar ζ scalarExp))⁻¹
  rw [move_conj_paired ζ hζ, rootDiagUnit_cubeChar_neg]

theorem moveElement_conj_cyclic :
    moveElement * cyclic (K := K) * moveElement⁻¹ = cyclic ^ 2 := nrep_move_gamma_conj

theorem moveElement_conj_mem_range (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    {y : adjointGroup .E7 K} (hy : y ∈ (cubeHom ζ hζ).range) :
    moveElement * y * moveElement⁻¹ ∈ (cubeHom ζ hζ).range := by
  obtain ⟨f, rfl⟩ := hy
  let E := (cubeHom ζ hζ).range
  let Q : adjointGroup .E7 K →* adjointGroup .E7 K :=
    (MulAut.conj (moveElement (K := K))).toMonoidHom
  have h0 : Q (scalarWord ζ) = (pairedWord ζ)⁻¹ := moveElement_conj_scalarWord ζ hζ
  have h1 : Q (pairedWord ζ) = (scalarWord ζ)⁻¹ := moveElement_conj_pairedWord ζ hζ
  have h2 : Q (cyclic (K := K)) = cyclic ^ 2 := moveElement_conj_cyclic
  change Q (cubeHom ζ hζ f) ∈ E
  rw [cubeHom_apply, Q.map_mul _ _, Q.map_mul _ _, Q.map_pow _ _, Q.map_pow _ _, Q.map_pow _ _,
    h0, h1, h2]
  exact E.mul_mem (E.mul_mem
    (E.pow_mem (E.inv_mem (generators_mem_range ζ hζ 1)) _)
    (E.pow_mem (E.inv_mem (generators_mem_range ζ hζ 0)) _))
    (E.pow_mem (E.pow_mem (generators_mem_range ζ hζ 2) 2) _)

theorem moveElement_mem_normalizer (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    moveElement (K := K) ∈ Subgroup.normalizer ((cubeHom ζ hζ).range : Set (adjointGroup .E7 K)) := by
  refine Subgroup.mem_normalizer_iff.2 ?_
  intro y
  constructor
  · exact moveElement_conj_mem_range ζ hζ
  · intro hy
    have h := moveElement_conj_mem_range ζ hζ hy
    have hsq : (moveElement (K := K)) * moveElement = 1 := by
      simpa only [pow_two] using (moveElement_pow_two (K := K))
    have hinv : (moveElement (K := K))⁻¹ = moveElement := by
      calc
        moveElement⁻¹ = moveElement⁻¹ * (moveElement * moveElement) := by rw [hsq, mul_one]
        _ = moveElement := by group
    have he : moveElement (K := K) * (moveElement * y * moveElement⁻¹) * moveElement⁻¹ = y := by
      rw [hinv]
      calc
        moveElement * (moveElement * y * moveElement) * moveElement =
            (moveElement * moveElement) * y * (moveElement * moveElement) := by group
        _ = y := by rw [hsq, one_mul, mul_one]
    rwa [he] at h

end CFSG.LieType.Chevalley.E7Three.Cube
