module

public import CFSG.CharacterTheory.Semidihedral.DefiningCharacteristicDimension
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.Semidihedral.PrimeFieldDegreeTwoAction

open Matrix

universe u v w

section OriginalDescent

variable {J : Type w} [Group J] {F : Type u} [Field F]
variable {k : Type v} [Field k]

theorem range_ne_bot (ρ : J →* GeneralLinearGroup (Fin 2) k) (t : J)
    (hρ : ρ t ≠ 1) : ρ.range ≠ ⊥ := by
  intro hbot
  have ht : ρ t ∈ ρ.range := ⟨t, rfl⟩
  exact hρ (by simpa only [hbot, Subgroup.mem_bot] using ht)

theorem central_odd_kernel_le_action_kernel [Group.IsPerfect J]
    (β : J →* SpecialLinearGroup (Fin 2) F)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (ρ : J →* GeneralLinearGroup (Fin 2) k) (t : J) (hρ : ρ t ≠ 1) :
    β.ker ≤ ρ.ker := by
  let : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hrange := range_ne_bot ρ t hρ
  intro e he
  have hcenter : ρ.rangeRestrict e ∈ Subgroup.center ρ.range := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    obtain ⟨j, hj⟩ := a.property
    apply Subtype.ext
    change (a : GeneralLinearGroup (Fin 2) k) * ρ e =
      ρ e * (a : GeneralLinearGroup (Fin 2) k)
    rw [← hj, ← map_mul, ← map_mul]
    exact congrArg ρ (Subgroup.mem_center_iff.mp (hcentral he) j)
  rcases CFSG.SectionRank.Ccomm.perfect_center_eq_one_or_neg_one ρ.range hrange hcenter
      with hone | hminus
  · exact MonoidHom.mem_ker.mpr hone
  · change ρ e = -1 at hminus
    have hsquare : (ρ e) ^ 2 = 1 := by rw [hminus]; simp
    have hpow : e ^ Nat.card β.ker = 1 := by
      exact congrArg (fun x : β.ker => (x : J))
        (pow_card_eq_one' (x := (⟨e, he⟩ : β.ker)))
    have himagepow : (ρ e) ^ Nat.card β.ker = 1 := by rw [← map_pow, hpow, map_one]
    exact MonoidHom.mem_ker.mpr
      ((pow_eq_one_iff_of_coprime hodd.coprime_two_left).mp ⟨hsquare, himagepow⟩)

theorem central_action_eq_minusIdentity [Group.IsPerfect J]
    (ρ : J →* GeneralLinearGroup (Fin 2) k) (t : J)
    (ht : t ∈ Subgroup.center J) (hρ : ρ t ≠ 1) :
    ρ t = GeneralLinearGroup.scalar (Fin 2) (-1 : kˣ) := by
  let : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hcenter : ρ.rangeRestrict t ∈ Subgroup.center ρ.range := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    obtain ⟨j, hj⟩ := a.property
    apply Subtype.ext
    change (a : GeneralLinearGroup (Fin 2) k) * ρ t =
      ρ t * (a : GeneralLinearGroup (Fin 2) k)
    rw [← hj, ← map_mul, ← map_mul]
    exact congrArg ρ (Subgroup.mem_center_iff.mp ht j)
  have hminus : ρ t = -1 :=
    (CFSG.SectionRank.Ccomm.perfect_center_eq_one_or_neg_one ρ.range
      (range_ne_bot ρ t hρ) hcenter).resolve_left hρ
  rw [hminus]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

end OriginalDescent

section RepresentativeEquivalence

variable {J : Type u} {Q : Type v} {H : Type w} [Group J] [Group Q] [Group H]

@[expose] noncomputable def inducedRangeHom (β : J →* Q) (hβ : Function.Surjective β)
    (ρ : J →* H) (hker : ρ.ker = β.ker) : Q →* ρ.range :=
  β.liftOfSurjective hβ ⟨ρ.rangeRestrict, by rw [MonoidHom.ker_rangeRestrict, hker]⟩

theorem inducedRangeHom_apply (β : J →* Q) (hβ : Function.Surjective β)
    (ρ : J →* H) (hker : ρ.ker = β.ker) (j : J) :
    inducedRangeHom β hβ ρ hker (β j) = ρ.rangeRestrict j := by
  simp only [inducedRangeHom, MonoidHom.liftOfRightInverse_comp_apply]

theorem inducedRangeHom_bijective (β : J →* Q) (hβ : Function.Surjective β)
    (ρ : J →* H) (hker : ρ.ker = β.ker) :
    Function.Bijective (inducedRangeHom β hβ ρ hker) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro q hq
    obtain ⟨j, rfl⟩ := hβ q
    rw [inducedRangeHom_apply] at hq
    have hj : j ∈ ρ.ker := MonoidHom.mem_ker.mpr (congrArg Subtype.val hq)
    exact MonoidHom.mem_ker.mp (hker ▸ hj)
  · intro a
    obtain ⟨j, hj⟩ := a.property
    refine ⟨β j, ?_⟩
    rw [inducedRangeHom_apply]
    exact Subtype.ext hj

@[expose] noncomputable def inducedRangeEquiv (β : J →* Q) (hβ : Function.Surjective β)
    (ρ : J →* H) (hker : ρ.ker = β.ker) : Q ≃* ρ.range :=
  MulEquiv.ofBijective (inducedRangeHom β hβ ρ hker)
    (inducedRangeHom_bijective β hβ ρ hker)

theorem inducedRangeEquiv_apply (β : J →* Q) (hβ : Function.Surjective β)
    (ρ : J →* H) (hker : ρ.ker = β.ker) (j : J) :
    (inducedRangeEquiv β hβ ρ hker (β j) : H) = ρ j :=
  congrArg Subtype.val (inducedRangeHom_apply β hβ ρ hker j)

end RepresentativeEquivalence

section OriginalKernel

variable {J : Type w} [Group J] [Group.IsPerfect J]
variable {F : Type u} [Field F] [Finite F] {k : Type v} [Field k]

theorem original_action_kernel_eq (hF : 4 ≤ Nat.card F)
    (β : J →* SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (htβ : β t = ProjectiveSL2Cover.minusIdentity F)
    (ρ : J →* GeneralLinearGroup (Fin 2) k) (hρ : ρ t ≠ 1) : ρ.ker = β.ker := by
  have hle := central_odd_kernel_le_action_kernel β hcentral hodd ρ t hρ
  let δ : SpecialLinearGroup (Fin 2) F →* GeneralLinearGroup (Fin 2) k :=
    β.liftOfSurjective hβ ⟨ρ, hle⟩
  have hδ (j : J) : δ (β j) = ρ j :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hminus : δ (OddFieldSL2.minusIdentity F) ≠ 1 := by
    intro heq
    apply hρ
    rw [← hδ, htβ]
    simpa only [ProjectiveSL2Cover.minusIdentity_eq_neg_one, OddFieldSL2.minusIdentity]
      using heq
  have hinj := DefiningCharacteristicDimension.nativeSL2_action_injective hF δ hminus
  apply le_antisymm _ hle
  intro j hj
  apply MonoidHom.mem_ker.mpr
  apply hinj
  rw [hδ, map_one]
  exact MonoidHom.mem_ker.mp hj

theorem central_odd_cover_degree_two_kernel_descent (hF : 4 ≤ Nat.card F)
    (β : J →* SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J)
    (htβ : β t = ProjectiveSL2Cover.minusIdentity F)
    (ρ : J →* GeneralLinearGroup (Fin 2) k) (hρ : ρ t ≠ 1) :
    ρ.ker = β.ker ∧ ρ t = GeneralLinearGroup.scalar (Fin 2) (-1 : kˣ) ∧
      ∃ e : SpecialLinearGroup (Fin 2) F ≃* ρ.range,
        ∀ j : J, (e (β j) : GeneralLinearGroup (Fin 2) k) = ρ j := by
  have hker := original_action_kernel_eq hF β hβ hcentral hodd t htβ ρ hρ
  exact ⟨hker, central_action_eq_minusIdentity ρ t ht hρ,
    inducedRangeEquiv β hβ ρ hker, inducedRangeEquiv_apply β hβ ρ hker⟩

end OriginalKernel

section OrderArithmetic

theorem sl2_order_strictMonoOn :
    StrictMonoOn (fun q : ℕ => q * (q ^ 2 - 1)) (Set.Ici 1) := by
  intro a ha b _ hab
  have ha2 : 1 ≤ a ^ 2 := by nlinarith only [show 1 ≤ a from ha]
  exact Nat.mul_lt_mul_of_lt_of_lt hab
    (Nat.sub_lt_sub_right ha2 (Nat.pow_left_strictMono (by decide : 2 ≠ 0) hab))

theorem sl2_order_injective {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b :=
  sl2_order_strictMonoOn.injOn ha hb h

theorem prime_power_eq_prime_parameters {p ℓ f : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (h : p ^ f = ℓ) : p = ℓ ∧ f = 1 := by
  have hdvd : p ∣ ℓ := h ▸ dvd_pow_self p (by omega : f ≠ 0)
  have hpeq := (Nat.prime_dvd_prime_iff_eq hp hℓ).mp hdvd
  refine ⟨hpeq, ?_⟩
  apply Nat.pow_right_injective hp.two_le
  simpa only [pow_one, hpeq] using h

theorem parameter_exclusions {p ℓ f : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (h : p ^ f = 5 ∨ p ^ f = ℓ) :
    p ^ f ≠ 9 ∧ (5 < p ^ f → p = ℓ) ∧ f = 1 := by
  rcases h with h5 | hℓq
  · exact ⟨by omega, fun hlt => by omega,
      (prime_power_eq_prime_parameters hp Nat.prime_five hf h5).2⟩
  · have hparams := prime_power_eq_prime_parameters hp hℓ hf hℓq
    refine ⟨?_, fun _ => hparams.1, hparams.2⟩
    intro h9
    have hℓ9 : ℓ = 9 := hℓq.symm.trans h9
    rw [hℓ9] at hℓ
    norm_num at hℓ

end OrderArithmetic

section OriginalPrimeField

variable {k : Type u} {K : Type v} [Field k] [Field K]

@[expose] def coefficientGL (e : k ≃+* K) :
    GeneralLinearGroup (Fin 2) k ≃* GeneralLinearGroup (Fin 2) K :=
  Units.mapEquiv e.mapMatrix.toMulEquiv

theorem coefficientGL_apply (e : k ≃+* K) (g : GeneralLinearGroup (Fin 2) k) :
    coefficientGL e g = GeneralLinearGroup.map e.toRingHom g := by
  apply Units.ext
  rfl

theorem coefficientGL_map_specialLinear (e : k ≃+* K) :
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →*
      GeneralLinearGroup (Fin 2) k).range.map (coefficientGL e).toMonoidHom =
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →*
      GeneralLinearGroup (Fin 2) K).range := by
  ext g
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    refine ⟨SpecialLinearGroup.map e.toRingHom A, ?_⟩
    apply Units.ext
    rfl
  · rintro ⟨A, rfl⟩
    refine ⟨SpecialLinearGroup.toGL (SpecialLinearGroup.map e.symm.toRingHom A),
      ⟨SpecialLinearGroup.map e.symm.toRingHom A, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, coefficientGL_apply]
    apply Units.ext
    ext i j
    simp [GeneralLinearGroup.map_apply]

variable [Finite k]

theorem perfect_prime_field_defining_image
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (hk : Nat.card k = ℓ) (H : Subgroup (GeneralLinearGroup (Fin 2) k))
    [Group.IsPerfect H] (hH : H ≠ ⊥) (hdiv : ℓ ∣ Nat.card H) :
    H = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →*
      GeneralLinearGroup (Fin 2) k).range := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let : Fintype k := Fintype.ofFinite k
  let e : k ≃+* ZMod ℓ :=
    (ZMod.ringEquivOfPrime k hℓ (by simpa only [Nat.card_eq_fintype_card] using hk)).symm
  let g := coefficientGL e
  let H' := H.map g.toMonoidHom
  let : Group.IsPerfect H' := Group.IsPerfect.map g.toMonoidHom
  have hH' : H' ≠ ⊥ := by
    intro hbot
    exact hH ((Subgroup.map_eq_bot_iff_of_injective H g.injective).mp hbot)
  have hcard' : Nat.card H' = Nat.card H :=
    Subgroup.card_map_of_injective (K := H) (f := g.toMonoidHom) g.injective
  have hdiv' : ℓ ∣ Nat.card H' := hcard'.symm ▸ hdiv
  have hℓ2 : ℓ ≠ 2 := by intro h2; rw [h2] at hℓodd; norm_num at hℓodd
  have himage := (CFSG.SectionRank.Ccomm.prime_field_unipotent_generation hℓ2 H' hH' hdiv').2
  apply Subgroup.map_injective g.injective
  exact himage.trans (coefficientGL_map_specialLinear e).symm

end OriginalPrimeField

section TameImage

variable {k : Type u} [Field k]

@[expose] def projectiveImageHom (H : Subgroup (GeneralLinearGroup (Fin 2) k)) :
    H →* Matrix.ProjGenLinGroup (Fin 2) k :=
  Matrix.ProjGenLinGroup.mk.comp H.subtype

theorem projectiveImageHom_ker (H : Subgroup (GeneralLinearGroup (Fin 2) k))
    [Group.IsPerfect H] (hH : H ≠ ⊥) :
    (projectiveImageHom H).ker = Subgroup.center H := by
  ext g
  change Matrix.ProjGenLinGroup.mk (g : GeneralLinearGroup (Fin 2) k) = 1 ↔
    g ∈ Subgroup.center H
  rw [Matrix.ProjGenLinGroup.mk_eq_one]
  constructor
  · intro hg
    apply Subgroup.mem_center_iff.mpr
    intro a
    exact Subtype.ext (Subgroup.mem_center_iff.mp hg (a : GeneralLinearGroup (Fin 2) k))
  · intro hg
    obtain ⟨c, hc⟩ := (CFSG.SectionRank.Ccomm.perfect_mem_center_iff H hH g).mp hg
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply Units.ext
    change (a : Matrix (Fin 2) (Fin 2) k) * (g : GeneralLinearGroup (Fin 2) k).val =
      (g : GeneralLinearGroup (Fin 2) k).val * (a : Matrix (Fin 2) (Fin 2) k)
    rw [hc, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem projectiveImageHom_range_not_solvable
    (H : Subgroup (GeneralLinearGroup (Fin 2) k)) [Group.IsPerfect H] (hH : H ≠ ⊥) :
    ¬ Group.IsSolvable (projectiveImageHom H).range := by
  intro hsol
  let π := projectiveImageHom H
  let : Group.IsSolvable π.range := hsol
  let : IsMulCommutative π.ker := by rw [projectiveImageHom_ker H hH]; infer_instance
  let : Group.IsSolvable H := Group.isSolvable_of_ker_le_range π.ker.subtype π.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  exact Group.IsPerfect.not_isSolvable H inferInstance

variable [Finite k]

theorem projectiveImageHom_ker_card_two
    (H : Subgroup (GeneralLinearGroup (Fin 2) k)) [Group.IsPerfect H] (hH : H ≠ ⊥)
    (z : H) (hz : orderOf z = 2) (hπz : projectiveImageHom H z = 1) :
    Nat.card (projectiveImageHom H).ker = 2 := by
  let zker : (projectiveImageHom H).ker := ⟨z, hπz⟩
  have horder : orderOf zker = 2 := (Subgroup.orderOf_mk z hπz).trans hz
  have hdiv : 2 ∣ Nat.card (projectiveImageHom H).ker := by
    simpa only [horder] using orderOf_dvd_natCard zker
  have hle : Nat.card (projectiveImageHom H).ker ≤ 2 := by
    rw [projectiveImageHom_ker H hH]
    exact (CFSG.SectionRank.Ccomm.perfect_linear_two_basics H hH).2.2.2
  exact Nat.le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdiv)

theorem perfect_linear_two_tame_image_card
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP k ℓ]
    (H : Subgroup (GeneralLinearGroup (Fin 2) k)) [Group.IsPerfect H] (hH : H ≠ ⊥)
    (z : H) (hz : orderOf z = 2) (hπz : projectiveImageHom H z = 1)
    (hdiv : ¬ ℓ ∣ Nat.card H) : Nat.card H = 120 := by
  let π := projectiveImageHom H
  have hpimage : ¬ ℓ ∣ Nat.card π.range := fun h =>
    hdiv (h.trans (Subgroup.card_range_dvd π))
  have hcard := (CFSG.LinearGroups.tame_projective_linear_two_nonsolvable_order_sixty hℓ
    π.range hpimage (projectiveImageHom_range_not_solvable H hH)).1
  have hker := projectiveImageHom_ker_card_two H hH z hz hπz
  have h := Subgroup.card_ker_mul_card_range π
  rw [hcard, hker] at h
  exact h.symm

end TameImage

section ActualImageOrder

variable {k : Type u} [Field k] [Finite k]

theorem actual_specialLinear_subgroup_card :
    Nat.card (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →*
      GeneralLinearGroup (Fin 2) k).range = Nat.card k * (Nat.card k ^ 2 - 1) := by
  rw [SpecialLinearGroup.range_toGL_eq_ker_det,
    ← Nat.card_congr SpecialLinearGroup.toGLKerEquiv.toEquiv]
  exact CFSG.GorensteinWalter.sl2_card_formula k

end ActualImageOrder

section CanonicalAction

variable {F : Type u} [Field F] {k : Type v} [Field k]
variable {J : Type w} [Group J] [Finite J] [Group.IsPerfect J]

theorem prime_field_degree_two_central_cover_action
    {p ℓ f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hℓ : ℓ.Prime) (hℓodd : Odd ℓ)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hk : Nat.card k = ℓ) (hq : 5 ≤ p ^ f)
    (β : J →* SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = ProjectiveSL2Cover.minusIdentity F)
    (ρ : J →* GeneralLinearGroup (Fin 2) k) (hρ : ρ t ≠ 1) :
    ρ.ker = β.ker ∧
    ρ t = GeneralLinearGroup.scalar (Fin 2) (-1 : kˣ) ∧
    (∃ e : SpecialLinearGroup (Fin 2) F ≃* ρ.range,
      ∀ j : J, (e (β j) : GeneralLinearGroup (Fin 2) k) = ρ j) ∧
    (p ^ f = 5 ∨ p ^ f = ℓ) ∧
    (ℓ ∣ Nat.card ρ.range →
      ρ.range = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →*
        GeneralLinearGroup (Fin 2) k).range ∧ p ^ f = ℓ) ∧
    (¬ ℓ ∣ Nat.card ρ.range → p ^ f = 5 ∧ Nat.card ρ.range = 120) ∧
    p ^ f ≠ 9 ∧ (5 < p ^ f → p = ℓ) ∧ f = 1 := by
  classical
  have hFodd : Odd (Nat.card F) := by rw [hF]; exact hpodd.pow
  have hFne : Nat.card F ≠ 0 := by
    have hm := Nat.odd_iff.mp hFodd
    omega
  let : Finite F := Nat.finite_of_card_ne_zero hFne
  let : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hℓ.ne_zero)
  let : Fintype k := Fintype.ofFinite k
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let : CharP k ℓ := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  let : Finite ρ.range :=
    Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hH := range_ne_bot ρ t hρ
  obtain ⟨hker, hminus, e, he⟩ := central_odd_cover_degree_two_kernel_descent
    (by rw [hF]; omega) β hβ hcentral hodd t ht htβ ρ hρ
  have hcard : Nat.card ρ.range = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula, hF]
  have himagepos : 0 < Nat.card ρ.range := Nat.card_pos
  have hqpos : 1 ≤ p ^ f := by
    rw [hcard] at himagepos
    exact Nat.pos_of_mul_pos_right himagepos
  have hdef : ℓ ∣ Nat.card ρ.range →
      ρ.range = (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) k →*
        GeneralLinearGroup (Fin 2) k).range ∧ p ^ f = ℓ := by
    intro hdiv
    have hactual := perfect_prime_field_defining_image hℓ hℓodd hk ρ.range hH hdiv
    refine ⟨hactual, sl2_order_injective hqpos (Nat.le_trans (by decide : 1 ≤ 2) hℓ.two_le) ?_⟩
    rw [← hcard, hactual, actual_specialLinear_subgroup_card, hk]
  have htame : ¬ ℓ ∣ Nat.card ρ.range → p ^ f = 5 ∧ Nat.card ρ.range = 120 := by
    intro hdiv
    let z : ρ.range := ρ.rangeRestrict t
    have hzsquare : z ^ 2 = 1 := by
      change (ρ.rangeRestrict t) ^ 2 = 1
      rw [← map_pow, show t ^ 2 = 1 by simpa only [htorder] using pow_orderOf_eq_one t,
        map_one]
    have hzne : z ≠ 1 := fun h => hρ (congrArg Subtype.val h)
    have hz : orderOf z = 2 := (orderOf_eq_prime_iff (p := 2)).mpr ⟨hzsquare, hzne⟩
    have hπz : projectiveImageHom ρ.range z = 1 := by
      change Matrix.ProjGenLinGroup.mk (ρ t) = 1
      rw [hminus, Matrix.ProjGenLinGroup.mk_eq_one]
      apply Subgroup.mem_center_iff.mpr
      intro a
      exact (GeneralLinearGroup.scalar_commute (-1 : kˣ) a).symm
    have h120 := perfect_linear_two_tame_image_card hℓ ρ.range hH z hz hπz hdiv
    refine ⟨sl2_order_injective hqpos (by decide : 1 ≤ 5) ?_, h120⟩
    rw [← hcard, h120]
    norm_num
  have hcase : p ^ f = 5 ∨ p ^ f = ℓ := by
    by_cases hdiv : ℓ ∣ Nat.card ρ.range
    · exact Or.inr (hdef hdiv).2
    · exact Or.inl (htame hdiv).1
  exact ⟨hker, hminus, ⟨e, he⟩, hcase, hdef, htame,
    parameter_exclusions hp hℓ hf hcase⟩

end CanonicalAction

end CFSG.Semidihedral.PrimeFieldDegreeTwoAction
