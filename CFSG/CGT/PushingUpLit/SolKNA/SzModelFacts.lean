module

public import CFSG.CGT.PushingUpLit.SolKNA.SzWeightDef
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix

private theorem coe_rootSz (a : ℕ) (α β : F a) :
    (((rootSz a α β : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      rootMat a α β := rfl

private theorem frob_add (a : ℕ) (x y : F a) :
    (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) :=
  add_pow_char_pow (R := F a) (p := 2) (n := a + 1) x y

theorem rootSz_zero_mul (a : ℕ) (b b' : F a) :
    rootSz a 0 b * rootSz a 0 b' = rootSz a 0 (b + b') := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, coe_rootSz, frob_add a b b'] <;> ring

theorem rootSz_zero_zero (a : ℕ) : rootSz a 0 0 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, coe_rootSz]

theorem rootSz_zero_injective (a : ℕ) : Function.Injective (rootSz a 0) := by
  intro b b' h
  have := congrArg (fun y : ↥(Sz a) =>
    ((y : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) 0 2) h
  simpa [rootMat, coe_rootSz] using this

private theorem rootSz_mul_zero (a : ℕ) (α β b : F a) :
    rootSz a α β * rootSz a 0 b = rootSz a α (β + b) := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, coe_rootSz, frob_add a β b] <;> ring

private theorem rootSz_zero_mul' (a : ℕ) (α β b : F a) :
    rootSz a 0 b * rootSz a α β = rootSz a α (b + β) := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, coe_rootSz, frob_add a b β] <;> ring

theorem rootSz_mul_zero_comm (a : ℕ) (α β b : F a) :
    rootSz a α β * rootSz a 0 b = rootSz a 0 b * rootSz a α β := by
  rw [rootSz_mul_zero, rootSz_zero_mul', add_comm β b]

private theorem coe_torusSz (a : ℕ) (x : (F a)ˣ) :
    (((torusSz a x : ↥(Sz a)) : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)) =
      torusMat a x := rfl

private theorem pow_theta_mul_theta (a : ℕ) (u : F a) :
    u ^ (2 ^ (a + 1) * 2 ^ (a + 1)) = u ^ 2 := by
  let _ : Fintype (F a) := Fintype.ofFinite _
  have hq : u ^ (2 ^ (2 * a + 1)) = u := by
    have h := FiniteField.pow_card u
    rwa [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * a + 1) (by omega)] at h
  calc u ^ (2 ^ (a + 1) * 2 ^ (a + 1)) = u ^ (2 * 2 ^ (2 * a + 1)) := by
        congr 1; ring
    _ = (u ^ (2 ^ (2 * a + 1))) ^ 2 := by rw [mul_comm 2 (2 ^ (2 * a + 1)), pow_mul]
    _ = u ^ 2 := by rw [hq]

private theorem torusMat_mul_rootMat_zero (a : ℕ) (x : (F a)ˣ) (b : F a) :
    torusMat a x * rootMat a 0 b =
      rootMat a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) * torusMat a x := by
  have hu : (x : F a) ≠ 0 := x.ne_zero
  have h1 : (x : F a) ^ (1 + 2 ^ (a + 1)) = (x : F a) ^ (1 + 2 ^ a) * (x : F a) ^ 2 ^ a := by
    rw [← pow_add]; congr 1; ring
  have h2 : (x : F a) ^ (1 + 2 ^ (a + 1)) = (x : F a) ^ 2 ^ a * (x : F a) ^ (1 + 2 ^ a) := by
    rw [h1, mul_comm]
  have h3 : ((x : F a) ^ (1 + 2 ^ a)) ^ 2 = (x : F a) ^ 2 ^ (a + 1) * (x : F a) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h4 : ((x : F a) ^ (1 + 2 ^ (a + 1))) ^ 2 ^ (a + 1) =
      (x : F a) ^ 2 ^ (a + 1) * (x : F a) ^ 2 := by
    rw [← pow_mul, show (1 + 2 ^ (a + 1)) * 2 ^ (a + 1) =
      2 ^ (a + 1) + 2 ^ (a + 1) * 2 ^ (a + 1) by ring, pow_add, pow_theta_mul_theta]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, rootMat, Matrix.mul_apply, Fin.sum_univ_four]
  · rw [h1]
    field_simp
  · rw [mul_pow, h4]
    field_simp
    linear_combination (b ^ 2 ^ (a + 1)) * h3
  · rw [h2]
    field_simp

theorem torus_conj_root_zero (a : ℕ) (x : (F a)ˣ) (b : F a) :
    torusSz a x * rootSz a 0 b * (torusSz a x)⁻¹ =
      rootSz a 0 ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  simpa [coe_rootSz, coe_torusSz] using torusMat_mul_rootMat_zero a x b

section Sylow

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

private theorem sz_eq_suzukiMatrixGroup (a : ℕ) : Sz a = SuzukiMatrixGroup a := by
  have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := CFSG.Models.benderSzModel_eq_sz a
  rw [← hmodel]
  exact CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a

private noncomputable def titsPi (a : ℕ) : F a ≃+* F a := iterateFrobeniusEquiv (F a) 2 (a + 1)

private theorem titsPi_apply (a : ℕ) (x : F a) : titsPi a x = x ^ 2 ^ (a + 1) :=
  iterateFrobeniusEquiv_def (F a) 2 (a + 1) x

private theorem titsPi_sq (a : ℕ) (x : F a) : titsPi a (titsPi a x) = x ^ 2 :=
  binaryGaloisField_tits_formula_sq a (titsPi a) (titsPi_apply a) x

private noncomputable def rootClosure (a : ℕ) : Subgroup (GL (Fin 4) (F a)) :=
  Subgroup.closure {A | ∃ α β : F a, A = SuzukiRootGL a α β}

private theorem rootClosure_le (a : ℕ) : rootClosure a ≤ Sz a := by
  rw [rootClosure, Subgroup.closure_le]
  rintro A ⟨α, β, rfl⟩
  exact rootGL_mem a α β

private theorem hb31 (a : ℕ) (ha : 1 ≤ a) :
    IsPGroup 2 (rootClosure a) ∧ Nat.card (rootClosure a) = (2 ^ (2 * a + 1)) ^ 2 ∧
    (∀ α β α' β' : F a, SuzukiRootGL a α β * SuzukiRootGL a α' β' =
      SuzukiRootGL a (α + α') (β + β' + α * α' ^ 2 ^ (a + 1))) := by
  rcases huppert_blackburn_XI_3_1 a ha (titsPi a) (titsPi_sq a) with
    ⟨_, _, hFp, _, _, _, hFcard, _, hroot_mul, _, _, _, _, _, _⟩
  refine ⟨hFp, hFcard, fun α β α' β' => ?_⟩
  rw [hroot_mul, titsPi_apply]

private theorem card_Sz (a : ℕ) (ha : 1 ≤ a) :
    Nat.card ↥(Sz a) =
      ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  rw [sz_eq_suzukiMatrixGroup]
  exact (huppert_blackburn_XI_3_3 a ha (titsPi a) (titsPi_apply a)).2.2.2.2.2.2.1

private theorem factorization_two_mul_odd {e c d : ℕ} (hc : Odd c) (hd : Odd d) :
    (c * 2 ^ e * d).factorization 2 = e := by
  have hc0 : c ≠ 0 := hc.pos.ne'
  have hd0 : d ≠ 0 := hd.pos.ne'
  have h2 : (2 : ℕ) ^ e ≠ 0 := by positivity
  rw [Nat.factorization_mul (mul_ne_zero hc0 h2) hd0, Nat.factorization_mul hc0 h2]
  have h1 : c.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero] using hc.not_two_dvd_nat)
  have h3 : d.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.two_dvd_ne_zero] using hd.not_two_dvd_nat)
  simp [h1, h3, Nat.Prime.factorization_pow Nat.prime_two]

private noncomputable def rootSub (a : ℕ) : Subgroup ↥(Sz a) := (rootClosure a).subgroupOf (Sz a)

private theorem card_rootSub (a : ℕ) (ha : 1 ≤ a) :
    Nat.card ↥(rootSub a) = 2 ^ (Nat.card ↥(Sz a)).factorization 2 := by
  have h1 : Nat.card ↥(rootSub a) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [rootSub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootClosure_le a)).toEquiv]
    exact (hb31 a ha).2.1
  have hqodd : Odd (((2 ^ (2 * a + 1)) ^ 2) + 1) := by
    have : Even ((2 ^ (2 * a + 1)) ^ 2) := (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩,
      by norm_num⟩)
    exact this.add_one
  have hq1odd : Odd (2 ^ (2 * a + 1) - 1) := by
    have hqe : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    have hqpos : 0 < 2 ^ (2 * a + 1) := by positivity
    exact Nat.Even.sub_odd hqpos hqe odd_one
  have hq : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ (2 * (2 * a + 1)) := by rw [← pow_mul, mul_comm]
  obtain ⟨c, hc⟩ : ∃ c, c = (2 ^ (2 * a + 1)) ^ 2 + 1 := ⟨_, rfl⟩
  have hcodd : Odd c := hc ▸ hqodd
  rw [h1, card_Sz a ha, ← hc, hq, factorization_two_mul_odd hcodd hq1odd]

private theorem exists_eq_rootSz_zero_of_sq {a : ℕ} (ha : 1 ≤ a) {y : ↥(Sz a)}
    (hy : y ∈ rootSub a) (hy2 : y * y = 1) : ∃ b : F a, y = rootSz a 0 b := by
  have hy' : (y : GL (Fin 4) (F a)) ∈ rootClosure a := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨α, β, hαβ⟩ :=
    (suzukiRootGL_mem_closure_iff a (titsPi a) (titsPi_sq a) (titsPi_apply a) _).mp hy'
  have hsq : SuzukiRootGL a α β * SuzukiRootGL a α β = 1 := by
    rw [← hαβ]
    exact congrArg Subtype.val hy2
  rw [(hb31 a ha).2.2 α β α β, CharTwo.add_self_eq_zero α, CharTwo.add_self_eq_zero β,
    zero_add] at hsq
  have h02 := congrArg (fun A : GL (Fin 4) (F a) =>
    (A : Matrix (Fin 4) (Fin 4) (F a)) 0 2) hsq
  have hα : α = 0 := by simpa [SuzukiRootGL, SuzukiRootMatrix] using h02
  subst hα
  exact ⟨β, Subtype.ext hαβ⟩

private theorem finite_Sz (a : ℕ) (ha : 1 ≤ a) : Finite ↥(Sz a) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_Sz a ha]
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) (by positivity)) (by omega)

private noncomputable def zMap (a : ℕ) : Multiplicative (F a) →* ↥(Sz a) where
  toFun b := rootSz a 0 (Multiplicative.toAdd b)
  map_one' := by simpa using rootSz_zero_zero a
  map_mul' _ _ := by simp [rootSz_zero_mul]

private theorem zMap_injective (a : ℕ) : Function.Injective (zMap a) := fun _ _ h =>
  Multiplicative.toAdd.injective (rootSz_zero_injective a h)

private theorem card_zMap_range (a : ℕ) : Nat.card ↥(zMap a).range = 2 ^ (2 * a + 1) := by
  rw [Nat.card_congr (MonoidHom.ofInjective (zMap_injective a)).toEquiv.symm,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (F a) ≃ F a)]
  exact GaloisField.card 2 (2 * a + 1) (by omega)

theorem exists_conj_eq_Z {a : ℕ} (ha : 1 ≤ a) (E : Subgroup ↥(Sz a))
    (_hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card ↥E = 2 ^ (2 * a + 1)) :
    ∃ g₀ : ↥(Sz a), ∀ y : ↥(Sz a), y ∈ E ↔ ∃ b : F a, y = g₀ * rootSz a 0 b * g₀⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(Sz a) := finite_Sz a ha
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card hcard
  obtain ⟨P, hEP⟩ := hE2.exists_le_sylow
  let P₀ : Sylow 2 ↥(Sz a) := Sylow.ofCard (rootSub a) (card_rootSub a ha)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Sz a) P₀ P
  have hmem : ∀ y ∈ E, g⁻¹ * y * g ∈ rootSub a := by
    intro y hy
    have hyP : y ∈ (P : Subgroup ↥(Sz a)) := hEP hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyP
    have h3 : g⁻¹ * y * g ∈ (P₀ : Subgroup ↥(Sz a)) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hyP
    exact h3
  have hZ : ∀ y ∈ E, ∃ b : F a, y = g * rootSz a 0 b * g⁻¹ := by
    intro y hy
    have h1 := hmem y hy
    have h2 : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
      calc (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
        _ = 1 := by rw [hsq y hy]; group
    obtain ⟨b, hb⟩ := exists_eq_rootSz_zero_of_sq ha h1 h2
    exact ⟨b, by rw [← hb]; group⟩
  let Z' : Subgroup ↥(Sz a) := (zMap a).range.map (MulAut.conj g).toMonoidHom
  have hmemZ' : ∀ b : F a, g * rootSz a 0 b * g⁻¹ ∈ Z' := fun b =>
    Subgroup.mem_map.mpr ⟨rootSz a 0 b, ⟨Multiplicative.ofAdd b, rfl⟩, by simp [MulAut.conj_apply]⟩
  have hEZ : E ≤ Z' := fun y hy => by
    obtain ⟨b, hb⟩ := hZ y hy
    rw [hb]
    exact hmemZ' b
  have hcardZ' : Nat.card ↥Z' = 2 ^ (2 * a + 1) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_zMap_range]
  have hEq : E = Z' := Subgroup.eq_of_le_of_card_ge hEZ (by rw [hcardZ', hcard])
  refine ⟨g, fun y => ⟨hZ y, ?_⟩⟩
  rintro ⟨b, rfl⟩
  rw [hEq]
  exact hmemZ' b

end Sylow

end CFSG.CGT.PushingUpLit.SolKNA
