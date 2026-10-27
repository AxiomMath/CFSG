module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder
public import CFSG.CharacterTheory.Semidihedral.CentralTransferSplitting
public import CFSG.Fischer.Classification.Basic.Heisenberg

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo

open CFSG.Fischer.Classification (CubeRel)
open scoped commutatorElement

section Lift

variable {E G : Type*} [Group E] [Group G] {π : E →* G}

theorem eq_one_of_sq_eq_one (h3 : IsPGroup 3 π.ker) {c : E} (hc : c ∈ π.ker) (h2 : c ^ 2 = 1) :
    c = 1 := by
  obtain ⟨k, hk⟩ := h3 ⟨c, hc⟩
  have hk' : c ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h := pow_gcd_eq_one.2 ⟨h2, hk'⟩
  rwa [(Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, pow_one] at h

theorem exists_lift_conj_eq_inv (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h3 : IsPGroup 3 π.ker) (t' : E) {x : G} (hx : π t' * x * (π t')⁻¹ = x⁻¹) :
    ∃ x' : E, π x' = x ∧ t' * x' * t'⁻¹ = x'⁻¹ := by
  obtain ⟨x₀, rfl⟩ := hπ x
  set c := t' * x₀ * t'⁻¹ * x₀ with hc_def
  have hc : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hx, inv_mul_cancel]
  obtain ⟨d, hd⟩ := (h3.powEquiv (n := 2) (by norm_num)).surjective ⟨c⁻¹, inv_mem hc⟩
  have hd' : (d : E) ^ 2 = c⁻¹ := by
    have := congrArg Subtype.val hd
    rwa [IsPGroup.powEquiv_apply, Subgroup.coe_pow] at this
  have hdc : ∀ g : E, g * d = d * g := fun g => Subgroup.mem_center_iff.1 (hcen d.2) g
  refine ⟨x₀ * d, by rw [map_mul, MonoidHom.mem_ker.1 d.2, mul_one], ?_⟩
  apply eq_inv_of_mul_eq_one_left
  calc t' * (x₀ * d) * t'⁻¹ * (x₀ * d) = t' * x₀ * (d * t'⁻¹) * x₀ * d := by group
    _ = t' * x₀ * t'⁻¹ * (d * x₀) * d := by rw [← hdc t'⁻¹]; group
    _ = c * (d : E) ^ 2 := by rw [← hdc x₀, hc_def, sq]; group
    _ = 1 := by rw [hd', mul_inv_cancel]

theorem pow_three_eq_one_of_conj_eq_inv (hcen : π.ker ≤ Subgroup.center E)
    (h3 : IsPGroup 3 π.ker) {t' u g : E} (hu : π u ^ 3 = 1)
    (ht : t' * u * t'⁻¹ = (g * u * g⁻¹)⁻¹) : u ^ 3 = 1 := by
  have hc : u ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hu]
  have hcen' : ∀ h : E, h * u ^ 3 = u ^ 3 * h := fun h => Subgroup.mem_center_iff.1 (hcen hc) h
  have h1 : t' * u ^ 3 * t'⁻¹ = u ^ 3 := by rw [hcen', mul_inv_cancel_right]
  have h2 : t' * u ^ 3 * t'⁻¹ = (u ^ 3)⁻¹ := by
    rw [← conj_pow, ht, inv_pow, conj_pow, hcen' g, mul_inv_cancel_right]
  refine eq_one_of_sq_eq_one h3 hc ?_
  rw [sq, mul_eq_one_iff_eq_inv]
  exact h1.symm.trans h2

theorem cubeRel_of_conj_eq_inv (hcen : π.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 π.ker)
    {t' x' y' : E} (hR : CubeRel (π x') (π y')) (hx : t' * x' * t'⁻¹ = x'⁻¹)
    (hy : t' * y' * t'⁻¹ = y'⁻¹) : CubeRel x' y' where
  cube_left := pow_three_eq_one_of_conj_eq_inv hcen h3 (g := 1) hR.cube_left (by rw [hx]; group)
  cube_right := pow_three_eq_one_of_conj_eq_inv hcen h3 (g := 1) hR.cube_right (by rw [hy]; group)
  cube_mul := pow_three_eq_one_of_conj_eq_inv hcen h3 (g := y')
    (by rw [map_mul]; exact hR.cube_mul) (by
      calc t' * (x' * y') * t'⁻¹ = t' * x' * t'⁻¹ * (t' * y' * t'⁻¹) := by group
        _ = (y' * (x' * y') * y'⁻¹)⁻¹ := by rw [hx, hy]; group)
  cube_mul_inv := pow_three_eq_one_of_conj_eq_inv hcen h3 (g := y'⁻¹)
    (by rw [map_mul, map_inv]; exact hR.cube_mul_inv) (by
      calc t' * (x' * y'⁻¹) * t'⁻¹ = t' * x' * t'⁻¹ * (t' * y' * t'⁻¹)⁻¹ := by group
        _ = (y'⁻¹ * (x' * y'⁻¹) * y'⁻¹⁻¹)⁻¹ := by rw [hx, hy]; group)

theorem card_closure_le_of_cubeRel {x y : G} (hR : CubeRel x y) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 27 := by
  set H := Subgroup.closure ({x, y} : Set G)
  have hx : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  have hy : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hc : ⁅x, y⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  let f : Fin 3 × Fin 3 × Fin 3 → H := fun ijk =>
    ⟨x ^ (ijk.1 : ℕ) * y ^ (ijk.2.1 : ℕ) * ⁅x, y⁆ ^ (ijk.2.2 : ℕ),
      H.mul_mem (H.mul_mem (H.pow_mem hx _) (H.pow_mem hy _)) (H.pow_mem hc _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := hR.exists_eq_of_mem_closure hg
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), rfl⟩
  have h := Nat.card_le_card_of_surjective f hf
  simpa using h

theorem card_closure_eq_of_cubeRel [Finite G] {x y : G} (hR : CubeRel x y)
    (hxy : x * y ≠ y * x) : Nat.card (Subgroup.closure ({x, y} : Set G)) = 27 := by
  set H := Subgroup.closure ({x, y} : Set G)
  have hx : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  have hy : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hp : IsPGroup 3 H := fun g =>
    ⟨1, Subtype.ext (by simpa using hR.pow_three_eq_one g.2)⟩
  have hnc : ¬ IsMulCommutative H := fun h =>
    hxy (congrArg Subtype.val ((isMulCommutative_iff.1 h) ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
  have hle := card_closure_le_of_cubeRel hR
  rw [hn] at hle ⊢
  have hn3 : n ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · have : IsCyclic H := isCyclic_of_card_dvd_prime (p := 3) (by rw [hn]; norm_num)
    exact (hnc inferInstance).elim
  · have : IsCyclic H := isCyclic_of_card_dvd_prime (p := 3) (by rw [hn]; norm_num)
    exact (hnc inferInstance).elim
  · exact absurd (IsPGroup.isMulCommutative_of_card_eq_prime_sq hn) hnc
  · rfl

theorem exists_section_of_cubeRel [Finite E] [Finite G] (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 π.ker) {x y t : G} (hR : CubeRel x y)
    (hxy : x * y ≠ y * x) (htx : t * x * t⁻¹ = x⁻¹) (hty : t * y * t⁻¹ = y⁻¹) {m : ℕ}
    (hG : Nat.card G = 27 * m) (hm : ¬ 3 ∣ m) :
    ∃ s : G →* E, ∀ g, π (s g) = g := by
  set H := Subgroup.closure ({x, y} : Set G)
  have hH : Nat.card H = 27 := card_closure_eq_of_cubeRel hR hxy
  have hidx : H.index = m := by
    have h := H.card_mul_index
    rw [hH, hG] at h
    omega
  obtain ⟨t', rfl⟩ := hπ t
  obtain ⟨x', rfl, hx'⟩ := exists_lift_conj_eq_inv hπ hcen h3 t' htx
  obtain ⟨y', rfl, hy'⟩ := exists_lift_conj_eq_inv hπ hcen h3 t' hty
  have hR' : CubeRel x' y' := cubeRel_of_conj_eq_inv hcen h3 hR hx' hy'
  set H' := Subgroup.closure ({x', y'} : Set E)
  have hmap : H'.map π = H := by rw [MonoidHom.map_closure, Set.image_pair]
  have hbij : Function.Bijective (π.subgroupMap H') := by
    refine (π.subgroupMap_surjective H').bijective_of_nat_card_le ?_
    rw [hmap, hH]
    exact card_closure_le_of_cubeRel hR'
  let e : H' ≃* H'.map π := MulEquiv.ofBijective _ hbij
  refine CFSG.Semidihedral.CentralTransferSplitting.exists_section_of_coprime_index 3 π hπ hcen h3
    (H'.map π) ?_ (H'.subtype.comp e.symm.toMonoidHom) fun k =>
      congrArg Subtype.val (e.apply_symm_apply k)
  rw [hmap, hidx]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm

end Lift

section Model

open Matrix CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem conjTr_fin_three (a b c d e f g h i : F) :
    conjTr σ !![a, b, c; d, e, f; g, h, i] = !![σ a, σ d, σ g; σ b, σ e, σ h; σ c, σ f, σ i] := by
  ext r s
  fin_cases r <;> fin_cases s <;> rfl

@[expose] def mkSUid (A : Matrix (Fin 3) (Fin 3) F) (hdet : A.det = 1) (hu : conjTr σ A * A = 1) :
    SUid σ 3 :=
  ⟨⟨A, conjTr σ A, mul_eq_one_comm.1 hu, hu⟩, hdet, hu⟩

theorem coe_mkSUid (A : Matrix (Fin 3) (Fin 3) F) (hdet : A.det = 1) (hu : conjTr σ A * A = 1) :
    (((mkSUid σ A hdet hu : SUid σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = A :=
  rfl

theorem coe_mkSUid_inv (A : Matrix (Fin 3) (Fin 3) F) (hdet : A.det = 1)
    (hu : conjTr σ A * A = 1) :
    ((((mkSUid σ A hdet hu)⁻¹ : SUid σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      conjTr σ A :=
  rfl

variable {σ} in
theorem ext_mat {g h : SUid σ 3}
    (hgh : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = ((h : GL (Fin 3) F) : Matrix _ _ F)) :
    g = h :=
  Subtype.ext (Units.ext hgh)

theorem exists_cubeRel_SUid_three {ζ : F} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    (hσζ : σ ζ = ζ⁻¹) :
    ∃ x y t : SUid σ 3, CubeRel x y ∧ x * y ≠ y * x ∧ t * x * t⁻¹ = x⁻¹ ∧ t * y * t⁻¹ = y⁻¹ := by
  have h3 : ζ * (ζ * ζ) = 1 := by rw [← hζ3]; ring
  have h3' : ζ⁻¹ * (ζ⁻¹ * ζ⁻¹) = 1 := by rw [← mul_inv, ← mul_inv, h3, inv_one]
  have hXd : (!![1, 0, 0; 0, ζ, 0; 0, 0, ζ⁻¹] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp [det_fin_three, hζ0]
  have hXu : conjTr σ !![1, 0, 0; 0, ζ, 0; 0, 0, ζ⁻¹] * !![1, 0, 0; 0, ζ, 0; 0, 0, ζ⁻¹] = 1 := by
    simp [conjTr_fin_three, hσζ, hζ0, one_fin_three]
  have hYd : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp [det_fin_three]
  have hYu : conjTr σ !![0, 0, 1; 1, 0, 0; 0, 1, 0] * !![0, 0, 1; 1, 0, 0; 0, 1, 0] = 1 := by
    simp [conjTr_fin_three, one_fin_three]
  have hTd : (!![-1, 0, 0; 0, 0, -1; 0, -1, 0] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp [det_fin_three]
  have hTu : conjTr σ !![-1, 0, 0; 0, 0, -1; 0, -1, 0] * !![-1, 0, 0; 0, 0, -1; 0, -1, 0] = 1 := by
    simp [conjTr_fin_three, one_fin_three]
  refine ⟨mkSUid σ _ hXd hXu, mkSUid σ _ hYd hYu, mkSUid σ _ hTd hTu, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · apply ext_mat
    simp only [pow_three, Subgroup.coe_mul, Units.val_mul, coe_mkSUid, Subgroup.coe_one,
      Units.val_one]
    simp [h3, h3', one_fin_three]
  · apply ext_mat
    simp only [pow_three, Subgroup.coe_mul, Units.val_mul, coe_mkSUid, Subgroup.coe_one,
      Units.val_one]
    simp [one_fin_three]
  · apply ext_mat
    simp only [pow_three, Subgroup.coe_mul, Units.val_mul, coe_mkSUid, Subgroup.coe_one,
      Units.val_one]
    simp [hζ0, one_fin_three]
  · apply ext_mat
    simp only [pow_three, Subgroup.coe_mul, Units.val_mul, coe_mkSUid, coe_mkSUid_inv,
      Subgroup.coe_one, Units.val_one]
    simp [conjTr_fin_three, hζ0, one_fin_three]
  · intro h
    have h' := congrArg (fun g : SUid σ 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0) h
    simp only [Subgroup.coe_mul, Units.val_mul, coe_mkSUid] at h'
    simp [mul_apply, Fin.sum_univ_three] at h'
    exact hζ1 h'
  · apply ext_mat
    simp only [Subgroup.coe_mul, Units.val_mul, coe_mkSUid, coe_mkSUid_inv]
    simp [conjTr_fin_three, hσζ]
  · apply ext_mat
    simp only [Subgroup.coe_mul, Units.val_mul, coe_mkSUid, coe_mkSUid_inv]
    simp [conjTr_fin_three]

end Model

section Main

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_section_SUid_three_two_of_three (hF : Nat.card F = (2 ^ 1) ^ 2)
    {E : Type*} [Group E] [Finite E] {π : E →* SUid (unitaryInvolution F 2 1) 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 π.ker) :
    ∃ s : SUid (unitaryInvolution F 2 1) 3 →* E, ∀ g, π (s g) = g := by
  obtain ⟨ω, hω, hω1⟩ := exists_norm_eq_one_ne_one hF
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω
  have hσω : unitaryInvolution F 2 1 ω = ω⁻¹ := eq_inv_of_mul_eq_one_left hω
  have hω3 : ω ^ 3 = 1 := by
    rw [unitaryInvolution_apply] at hω
    rw [← hω]
    ring
  obtain ⟨x, y, t, hR, hxy, htx, hty⟩ :=
    exists_cubeRel_SUid_three (unitaryInvolution F 2 1) hω0 hω1 hω3 hσω
  have hcard : Nat.card (SUid (unitaryInvolution F 2 1) 3) = 27 * 8 := by
    obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
    rw [← Nat.card_congr (conjEquiv P hP).toEquiv, card_SU_three hF]
    norm_num
  exact exists_section_of_cubeRel hπ hcen h3 hR hxy htx hty hcard (by norm_num)

theorem su_three_two_exists_section_of_three (hF : Nat.card F = (2 ^ 1) ^ 2)
    {E : Type*} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F 2 1) 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 π.ker) :
    ∃ s : SU (unitaryInvolution F 2 1) 3 →* E, ∀ g, π (s g) = g := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 3
  set e := conjEquiv P hP
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  obtain ⟨s, hs⟩ := exists_section_SUid_three_two_of_three hF (π := e.toMonoidHom.comp π)
    (e.surjective.comp hπ) (hker ▸ hcen) (hker ▸ h3)
  exact ⟨s.comp e.toMonoidHom, fun x => e.injective (hs (e x))⟩

end Main

end CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo
