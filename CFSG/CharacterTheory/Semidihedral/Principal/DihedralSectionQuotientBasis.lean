module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCharacterFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionInductionIsometry

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section DihedralStructure

variable {S : Type*} [Group S] {r s : S} {M : ℕ}

theorem dihedral_rotation_or_reflection [Finite S] (hM : 2 ≤ M) (hcard : Nat.card S = 2 * M)
    (hgen : Subgroup.closure {r, s} = ⊤) (hr : r ^ M = 1) (hs : s * s = 1)
    (hrel : s * r * s = r⁻¹) (y : S) :
    (∃ j : ℕ, y = r ^ j) ∨ (∃ j : ℕ, y = s * r ^ j) := by
  obtain ⟨e, he, -⟩ := exists_dihedral_mulEquiv hM hcard hgen hr hs hrel
  obtain ⟨d, rfl⟩ := e.surjective y
  cases d with
  | r j => exact Or.inl ⟨j.val, by rw [he]; rfl⟩
  | sr j => exact Or.inr ⟨j.val, by rw [he]; rfl⟩

theorem dihedral_reflection_not_mem_zpowers [Finite S] (hcard : Nat.card S = 2 * M)
    (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M) (hM : 0 < M) (j : ℤ) :
    s * r ^ j ∉ Subgroup.zpowers r := by
  intro h
  have hs : s ∈ Subgroup.zpowers r := by
    have := Subgroup.mul_mem _ h (Subgroup.zpow_mem _ (Subgroup.mem_zpowers r) (-j))
    simpa [mul_assoc, ← zpow_add] using this
  have htop : (⊤ : Subgroup S) ≤ Subgroup.zpowers r := by
    rw [← hgen, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_zpowers _
    · exact hs
  have hle := Subgroup.card_le_of_le htop
  rw [Subgroup.card_top, hcard, Nat.card_zpowers, hr] at hle
  omega

theorem dihedral_reflection_mul_self (hs : s * s = 1) (hrel : s * r * s = r⁻¹) (j : ℕ) :
    (s * r ^ j) * (s * r ^ j) = 1 := by
  have h := conj_pow_of_dihedral hs hrel j
  calc (s * r ^ j) * (s * r ^ j) = (s * r ^ j * s) * r ^ j := by group
    _ = 1 := by rw [h, inv_mul_cancel]

theorem eq_one_or_eq_half_of_mem_zpowers (hr : orderOf r = M) (hEven : Even M) {z : S}
    (hz : z ∈ Subgroup.zpowers r) (hzz : z * z = 1) : z = 1 ∨ z = r ^ (M / 2) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨m, hm⟩ := hEven
  have hhalf : M / 2 = m := by omega
  rw [hhalf]
  have h2 : r ^ (2 * k) = 1 := by
    rw [mul_comm, zpow_mul, zpow_two, hzz]
  have hdvd : (M : ℤ) ∣ 2 * k := by
    rw [← hr]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  have hmk : (m : ℤ) ∣ k := by
    rw [hm] at hdvd
    obtain ⟨q, hq⟩ := hdvd
    exact ⟨q, by push_cast at hq; linarith⟩
  obtain ⟨q, rfl⟩ := hmk
  have hrm : (r ^ (m : ℤ)) ^ (2 : ℤ) = 1 := by
    rw [← zpow_mul, show (m : ℤ) * 2 = (M : ℤ) by push_cast [hm]; ring, zpow_natCast, ← hr,
      pow_orderOf_eq_one]
  rw [zpow_mul]
  rcases Int.emod_two_eq_zero_or_one q with h0 | h1
  · left
    rw [zpow_eq_zpow_emod q hrm, h0, zpow_zero]
  · right
    rw [zpow_eq_zpow_emod q hrm, h1, zpow_one, zpow_natCast]

end DihedralStructure

section Retraction

variable {C S : Type*} [Group C] [Group S] (ι : S →* C) (R : Subgroup C) [R.Normal]

omit [R.Normal] in
theorem retraction_apply_mul {π : C →* S} (hker : π.ker = R) (hid : π.comp ι = MonoidHom.id S)
    {u : C} (hu : u ∈ R) (y : S) : π (u * ι y) = y := by
  have hu' : π u = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hu
  have hy : π (ι y) = y := DFunLike.congr_fun hid y
  rw [map_mul, hu', hy, one_mul]

theorem exists_unique_retraction (hι : Function.Injective ι) (hRS : R ⊓ ι.range = ⊥)
    (hprod : ∀ c : C, ∃ u ∈ R, ∃ y : S, c = u * ι y) :
    ∃! π : C →* S, π.ker = R ∧ π.comp ι = MonoidHom.id S := by
  let φ : S →* C ⧸ R := (QuotientGroup.mk' R).comp ι
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hmem : ι y ∈ R := (QuotientGroup.eq_one_iff _).mp hy
    have hbot : ι y ∈ R ⊓ ι.range := ⟨hmem, ⟨y, rfl⟩⟩
    rw [hRS, Subgroup.mem_bot] at hbot
    exact hι (hbot.trans (map_one ι).symm)
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, y, rfl⟩ := hprod c
    refine ⟨y, ?_⟩
    change ((ι y : C) : C ⧸ R) = ((u * ι y : C) : C ⧸ R)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff u).mpr hu, one_mul]
  let e : S ≃* C ⧸ R := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hker : (e.symm.toMonoidHom.comp (QuotientGroup.mk' R)).ker = R := by
    ext c
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
  have hid : (e.symm.toMonoidHom.comp (QuotientGroup.mk' R)).comp ι = MonoidHom.id S := by
    ext y
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      QuotientGroup.mk'_apply, MonoidHom.id_apply]
    rw [MulEquiv.symm_apply_eq]
    rfl
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' R), ⟨hker, hid⟩, ?_⟩
  rintro π' ⟨hker', hid'⟩
  ext c
  obtain ⟨u, hu, y, rfl⟩ := hprod c
  rw [retraction_apply_mul ι R hker' hid' hu, retraction_apply_mul ι R hker hid hu]

end Retraction

theorem blocksInnerProduct_comp_surjective {C S : Type} [Group C] [Group S] [Fintype C]
    [Fintype S] (π : C →* S) (hπ : Function.Surjective π) (F H : S → ℂ) :
    BlocksInnerProduct (F ∘ π) (H ∘ π) = BlocksInnerProduct F H := by
  unfold BlocksInnerProduct
  simp only [Function.comp_apply]
  rw [sum_comp_surjective_group_hom π hπ (fun y => F y * starRingEnd ℂ (H y)),
    card_surjective_group_hom π hπ]
  have hker : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp


theorem eq_one_of_mul_self_of_odd_card {C : Type*} [Group C] [Finite C] {R : Subgroup C}
    (hR : Odd (Nat.card R)) {v : C} (hv : v ∈ R) (hvv : v * v = 1) : v = 1 := by
  by_contra hne
  have horder : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hvv) hne
  have hdvd := orderOf_dvd_natCard (⟨v, hv⟩ : R)
  rw [Subgroup.orderOf_mk, horder] at hdvd
  exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr hdvd)

section SectionQuotient

variable {C S : Type*} [Group C] [Finite C] [Group S] [Finite S]
  {ι : S →* C} {R : Subgroup C} {π : C →* S} {r s : S} {n M : ℕ}

theorem mem_centralInvolutionSection_iff_retraction (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1))
    (hcard : Nat.card S = 2 * M) (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M)
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (hRodd : Odd (Nat.card R))
    (ht : ι (r ^ (M / 2)) ∈ Subgroup.center C) (hker : π.ker = R)
    (hid : π.comp ι = MonoidHom.id S) (x : C) :
    x ∈ centralInvolutionSection (ι (r ^ (M / 2))) ↔ π x ∈ Subgroup.zpowers r ∧ π x ≠ 1 := by
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEven : Even M := by
    rw [hM]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hrM : r ^ M = 1 := hr ▸ pow_orderOf_eq_one r
  have hss : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hπι : ∀ y, π (ι y) = y := fun y => DFunLike.congr_fun hid y
  have hhalf : M / 2 + M / 2 = M := by
    obtain ⟨m, hm⟩ := hEven
    omega
  have ht1 : r ^ (M / 2) ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hr]; omega)
  have htt : r ^ (M / 2) * r ^ (M / 2) = 1 := by rw [← pow_add, hhalf, hrM]
  have hS2 : ∀ y : S, ∃ k, orderOf y = 2 ^ k := by
    intro y
    have hdvd := orderOf_dvd_natCard y
    rw [hcard, hM, ← pow_succ', show n - 1 + 1 = n by omega] at hdvd
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd |>.imp fun k hk => hk.2
  constructor
  · rintro ⟨-, heven, hpow⟩
    have hπpow : π x ^ (orderOf x / 2) = r ^ (M / 2) := by
      rw [← map_pow, hpow, hπι]
    refine ⟨?_, ?_⟩
    · rcases dihedral_rotation_or_reflection hM2 hcard hgen hrM hss hrel (π x) with
        ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [hj]
        exact Subgroup.npow_mem_zpowers r j
      · exfalso
        have hrefl : π x ^ 2 = 1 := by
          rw [sq, hj]
          exact dihedral_reflection_mul_self hss hrel j
        rw [pow_eq_pow_mod _ hrefl] at hπpow
        rcases Nat.mod_two_eq_zero_or_one (orderOf x / 2) with h0 | h1
        · rw [h0, pow_zero] at hπpow
          exact ht1 hπpow.symm
        · rw [h1, pow_one, hj] at hπpow
          apply dihedral_reflection_not_mem_zpowers hcard hgen hr (by omega) (j : ℤ)
          rw [zpow_natCast, hπpow]
          exact Subgroup.npow_mem_zpowers r _
    · intro h1
      rw [h1, one_pow] at hπpow
      exact ht1 hπpow.symm
  · rintro ⟨hA, hne⟩
    have hxord : orderOf (π x) ∣ orderOf x := orderOf_map_dvd π x
    obtain ⟨k, hk⟩ := hS2 (π x)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by simpa using hk))
    have heven : Even (orderOf x) := by
      apply even_iff_two_dvd.mpr
      refine dvd_trans ?_ hxord
      rw [hk]
      exact dvd_pow_self 2 hk0
    have hhalfx : orderOf x / 2 + orderOf x / 2 = orderOf x := by
      obtain ⟨m, hm⟩ := heven
      omega
    have hxpos : 0 < orderOf x := orderOf_pos x
    set w := x ^ (orderOf x / 2) with hw
    have hww : w * w = 1 := by rw [hw, ← pow_add, hhalfx, pow_orderOf_eq_one]
    have hzA : π w ∈ Subgroup.zpowers r := by
      rw [hw, map_pow]
      exact Subgroup.pow_mem _ hA _
    have hzz : π w * π w = 1 := by rw [← map_mul, hww, map_one]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, heven, ?_⟩
    · rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_center_iff.mp ht x).symm
    rcases eq_one_or_eq_half_of_mem_zpowers hr hEven hzA hzz with hz | hz
    · exfalso
      have hwR : w ∈ R := by
        rw [← hker, MonoidHom.mem_ker]
        exact hz
      have hw1 : w = 1 := eq_one_of_mul_self_of_odd_card hRodd hwR hww
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega) hw1
    · have hcomm : Commute w (ι (r ^ (M / 2))) := Subgroup.mem_center_iff.mp ht w
      have hvR : w * (ι (r ^ (M / 2)))⁻¹ ∈ R := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hπι, hz, mul_inv_cancel]
      have hvv : (w * (ι (r ^ (M / 2)))⁻¹) * (w * (ι (r ^ (M / 2)))⁻¹) = 1 := by
        have htt' : ι (r ^ (M / 2)) * ι (r ^ (M / 2)) = 1 := by rw [← map_mul, htt, map_one]
        calc (w * (ι (r ^ (M / 2)))⁻¹) * (w * (ι (r ^ (M / 2)))⁻¹) =
            w * ((ι (r ^ (M / 2)))⁻¹ * w) * (ι (r ^ (M / 2)))⁻¹ := by group
          _ = w * (w * (ι (r ^ (M / 2)))⁻¹) * (ι (r ^ (M / 2)))⁻¹ := by
              rw [← hcomm.inv_right.eq]
          _ = (w * w) * (ι (r ^ (M / 2)) * ι (r ^ (M / 2)))⁻¹ := by group
          _ = 1 := by rw [hww, htt', inv_one, one_mul]
      have hv1 := eq_one_of_mul_self_of_odd_card hRodd hvR hvv
      exact mul_inv_eq_one.mp hv1

end SectionQuotient

section InnerProduct

variable {G : Type} [Group G] [Fintype G]

theorem blocksInnerProduct_left_add (f g h : G → ℂ) :
    BlocksInnerProduct (f + g) h = BlocksInnerProduct f h + BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.add_apply, add_mul]

theorem blocksInnerProduct_left_sub (f g h : G → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.sub_apply, sub_mul]

theorem blocksInnerProduct_left_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℂ) (f : ι → G → ℂ)
    (h : G → ℂ) :
    BlocksInnerProduct (∑ i, c i • f i) h = ∑ i, c i * BlocksInnerProduct (f i) h := by
  unfold BlocksInnerProduct
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Fintype G] in
theorem blocksIrr_isClassFunction {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    BlocksIsClassFunction χ := by
  obtain ⟨V, _, _, _, ρ, _, rfl⟩ := hχ
  intro g h
  exact Representation.char_conj ρ g h

end InnerProduct

@[expose] def sectionQuotientSpace {C S : Type*} [Group C] [Group S] (π : C →* S) (D : Set C) :
    Submodule ℂ (C → ℂ) where
  carrier := {h | BlocksIsClassFunction h ∧ (∀ x, x ∉ D → h x = 0) ∧
    ∃ F : S → ℂ, BlocksIsClassFunction F ∧ h = F ∘ π}
  add_mem' := by
    rintro h₁ h₂ ⟨hc₁, hv₁, F₁, hF₁, rfl⟩ ⟨hc₂, hv₂, F₂, hF₂, rfl⟩
    refine ⟨fun g k => ?_, fun x hx => ?_, F₁ + F₂, fun g k => ?_, rfl⟩
    · simp only [Pi.add_apply]
      rw [hc₁ g k, hc₂ g k]
    · simp only [Pi.add_apply]
      rw [hv₁ x hx, hv₂ x hx, add_zero]
    · simp only [Pi.add_apply]
      rw [hF₁ g k, hF₂ g k]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, 0, fun _ _ => rfl, rfl⟩
  smul_mem' := by
    rintro c h ⟨hc, hv, F, hF, rfl⟩
    refine ⟨fun g k => ?_, fun x hx => ?_, c • F, fun g k => ?_, rfl⟩
    · simp only [Pi.smul_apply]
      rw [hc g k]
    · simp only [Pi.smul_apply]
      rw [hv x hx, smul_zero]
    · simp only [Pi.smul_apply]
      rw [hF g k]

@[expose] noncomputable def dihedralSectionFamily {C S : Type*} [Group C] [Group S]
    (π : C →* S) (r s : S) (M : ℕ) : Option (dihedralIndexSet M) → C → ℂ
  | none => dihedralTheta r s M ∘ π
  | some k => dihedralEta r s M k ∘ π

theorem card_option_dihedralIndexSet {M : ℕ} (hM : 2 ≤ M) :
    Fintype.card (Option (dihedralIndexSet M)) = M / 2 := by
  rw [Fintype.card_option, Fintype.card_coe, dihedralIndexSet, Int.card_Icc]
  omega

section Basis

variable {C S : Type} [Group C] [Fintype C] [Group S] [Fintype S]
  {ι : S →* C} {R : Subgroup C} {π : C →* S} {r s : S} {n M : ℕ}

theorem dihedralSectionFamily_basis (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1))
    (hcard : Nat.card S = 2 * M) (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M)
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (hRodd : Odd (Nat.card R))
    (ht : ι (r ^ (M / 2)) ∈ Subgroup.center C) (hker : π.ker = R)
    (hid : π.comp ι = MonoidHom.id S) :
    LinearIndependent ℂ (dihedralSectionFamily π r s M) ∧
    Submodule.span ℂ (Set.range (dihedralSectionFamily π r s M)) =
      sectionQuotientSpace π (centralInvolutionSection (ι (r ^ (M / 2)))) ∧
    Module.finrank ℂ (sectionQuotientSpace π (centralInvolutionSection (ι (r ^ (M / 2))))) =
      M / 2 := by
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEven : Even M := by
    rw [hM]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hrM : r ^ M = 1 := hr ▸ pow_orderOf_eq_one r
  have hss : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hπι : ∀ y, π (ι y) = y := fun y => DFunLike.congr_fun hid y
  have hπsurj : Function.Surjective π := fun y => ⟨ι y, hπι y⟩
  have hD := mem_centralInvolutionSection_iff_retraction hn hM hcard hgen hr hs hrel hRodd ht
    hker hid
  obtain ⟨-, -, hφirr, hγirr, hφinj, hγinj, hφγ, -, -, -, -, -, hθ1, hθrefl, hη, -, -, -, -, -⟩ :=
    dihedral_explicit_character_family hM2 hEven hcard hgen hr hs hrel
  set U := sectionQuotientSpace π (centralInvolutionSection (ι (r ^ (M / 2))))
  have hφφ : ∀ i j : Fin 4, BlocksInnerProduct (dihedralLinearCharacter r s M i)
      (dihedralLinearCharacter r s M j) = if i = j then 1 else 0 := by
    intro i j
    rw [blocksInnerProduct_of_mem_blocksIrr (hφirr i) (hφirr j)]
    exact if_congr hφinj.eq_iff rfl rfl
  have hγφ : ∀ k ∈ dihedralIndexSet M, ∀ i : Fin 4, BlocksInnerProduct
      (dihedralRotationCharacter r s M k) (dihedralLinearCharacter r s M i) = 0 := by
    intro k hk i
    rw [blocksInnerProduct_of_mem_blocksIrr (hγirr k hk) (hφirr i)]
    exact ite_eq_right_iff.mpr fun h => absurd h.symm (hφγ i k hk)
  have hφγ' : ∀ k ∈ dihedralIndexSet M, ∀ i : Fin 4, BlocksInnerProduct
      (dihedralLinearCharacter r s M i) (dihedralRotationCharacter r s M k) = 0 := by
    intro k hk i
    rw [blocksInnerProduct_of_mem_blocksIrr (hφirr i) (hγirr k hk)]
    exact ite_eq_right_iff.mpr fun h => absurd h (hφγ i k hk)
  have hγγ : ∀ k ∈ dihedralIndexSet M, ∀ l ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralRotationCharacter r s M k) (dihedralRotationCharacter r s M l) =
        if k = l then 1 else 0 := by
    intro k hk l hl
    rw [blocksInnerProduct_of_mem_blocksIrr (hγirr k hk) (hγirr l hl)]
    exact if_congr ⟨fun h => hγinj hk hl h, fun h => h ▸ rfl⟩ rfl rfl
  have hθclass : BlocksIsClassFunction (dihedralTheta r s M) := by
    intro g k
    simp only [dihedralTheta, Pi.add_apply, Pi.sub_apply]
    rw [blocksIrr_isClassFunction (hφirr 0) g k, blocksIrr_isClassFunction (hφirr 1) g k,
      blocksIrr_isClassFunction (hφirr 2) g k, blocksIrr_isClassFunction (hφirr 3) g k]
  have hηclass : ∀ k ∈ dihedralIndexSet M, BlocksIsClassFunction (dihedralEta r s M k) := by
    intro k hk g h
    simp only [dihedralEta, Pi.add_apply, Pi.sub_apply]
    rw [blocksIrr_isClassFunction (hφirr 0) g h, blocksIrr_isClassFunction (hφirr 1) g h,
      blocksIrr_isClassFunction (hγirr k hk) g h]
  have hvanish : ∀ F : S → ℂ, F 1 = 0 → (∀ j : ℤ, F (s * r ^ j) = 0) →
      ∀ x, x ∉ centralInvolutionSection (ι (r ^ (M / 2))) → (F ∘ π) x = 0 := by
    intro F hF1 hFrefl x hx
    rw [hD] at hx
    simp only [Function.comp_apply]
    rcases dihedral_rotation_or_reflection hM2 hcard hgen hrM hss hrel (π x) with
      ⟨j, hj⟩ | ⟨j, hj⟩
    · have hx1 : π x = 1 := by
        by_contra hne
        exact hx ⟨hj ▸ Subgroup.npow_mem_zpowers r j, hne⟩
      rw [hx1, hF1]
    · rw [hj, ← zpow_natCast]
      exact hFrefl j
  have hmem : ∀ o, dihedralSectionFamily π r s M o ∈ U := by
    intro o
    cases o with
    | none =>
      refine ⟨fun g k => ?_, hvanish _ hθ1 hθrefl, dihedralTheta r s M, hθclass, rfl⟩
      simp only [dihedralSectionFamily, Function.comp_apply, map_mul, map_inv]
      exact hθclass _ _
    | some k =>
      refine ⟨fun g h => ?_, hvanish _ (hη k).1 (hη k).2, dihedralEta r s M k,
        hηclass k k.2, rfl⟩
      simp only [dihedralSectionFamily, Function.comp_apply, map_mul, map_inv]
      exact hηclass k k.2 _ _
  have hpair : ∀ o (H : S → ℂ), BlocksInnerProduct (dihedralSectionFamily π r s M o) (H ∘ π) =
      BlocksInnerProduct (o.elim (dihedralTheta r s M) (fun k => dihedralEta r s M k)) H := by
    intro o H
    cases o with
    | none => exact blocksInnerProduct_comp_surjective π hπsurj _ _
    | some k => exact blocksInnerProduct_comp_surjective π hπsurj _ _
  have hzero_left : ∀ H : C → ℂ, BlocksInnerProduct 0 H = 0 := by
    intro H
    simp [BlocksInnerProduct]
  have hlinind : LinearIndependent ℂ (dihedralSectionFamily π r s M) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have htest : ∀ H : S → ℂ, ∑ o, g o * BlocksInnerProduct
        (o.elim (dihedralTheta r s M) (fun k => dihedralEta r s M k)) H = 0 := by
      intro H
      have h := congrArg (fun f => BlocksInnerProduct f (H ∘ π)) hg
      simp only [blocksInnerProduct_left_sum_smul, hzero_left, hpair] at h
      exact h
    have hnone : g none = 0 := by
      have h := htest (dihedralLinearCharacter r s M 2)
      rw [Fintype.sum_option] at h
      simp only [Option.elim, dihedralTheta, dihedralEta, blocksInnerProduct_left_add,
        blocksInnerProduct_left_sub, hφφ] at h
      rw [Finset.sum_eq_zero fun k _ => by rw [hγφ k k.2 2]; norm_num] at h
      norm_num at h
      exact h
    intro o
    cases o with
    | none => exact hnone
    | some l =>
      have h := htest (dihedralRotationCharacter r s M l)
      rw [Fintype.sum_option, hnone, zero_mul, zero_add] at h
      have hterm : ∀ k : dihedralIndexSet M, g (some k) * BlocksInnerProduct
          (Option.elim (some k) (dihedralTheta r s M) fun k => dihedralEta r s M ↑k)
          (dihedralRotationCharacter r s M l) = if k = l then -g (some k) else 0 := by
        intro k
        simp only [Option.elim, dihedralEta, blocksInnerProduct_left_add,
          blocksInnerProduct_left_sub, hφγ' l l.2, hγγ k k.2 l l.2]
        by_cases hkl : k = l
        · simp [hkl]
        · have hkl' : (k : ℤ) ≠ l := fun h => hkl (Subtype.ext h)
          simp [hkl, hkl']
      rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_ite_eq'] at h
      simpa using h
  let ev : U →ₗ[ℂ] (Fin (M / 2) → ℂ) :=
    (LinearMap.pi fun j : Fin (M / 2) => LinearMap.proj (ι (r ^ (j.val + 1)))).comp U.subtype
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    obtain ⟨hc, hv, F, hF, hFeq⟩ := h.2
    have hzero : ∀ a : ℕ, 1 ≤ a → a ≤ M / 2 → (h : C → ℂ) (ι (r ^ a)) = 0 := by
      intro a ha1 ha2
      have h' := congrFun hh ⟨a - 1, by omega⟩
      simpa [ev, show a - 1 + 1 = a by omega] using h'
    apply Subtype.ext
    funext x
    change (h : C → ℂ) x = 0
    by_cases hxD : x ∈ centralInvolutionSection (ι (r ^ (M / 2)))
    · obtain ⟨hA, hne⟩ := (hD x).mp hxD
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hA
      have hMpos : (0 : ℤ) < M := by exact_mod_cast (by omega : 0 < M)
      have hknn : 0 ≤ k % (M : ℤ) := Int.emod_nonneg _ hMpos.ne'
      have hklt : k % (M : ℤ) < M := Int.emod_lt_of_pos _ hMpos
      set a := (k % (M : ℤ)).toNat with ha
      have haz : (a : ℤ) = k % (M : ℤ) := Int.toNat_of_nonneg hknn
      have hka : r ^ a = π x := by
        rw [← hk, ← zpow_natCast, haz, ← hr, zpow_mod_orderOf]
      have haM : a < M := by omega
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hka
        exact hne hka.symm
      have hxval : (h : C → ℂ) x = (h : C → ℂ) (ι (r ^ a)) := by
        rw [hFeq]
        simp only [Function.comp_apply, hπι, hka]
      rw [hxval]
      by_cases haM2 : a ≤ M / 2
      · exact hzero a (by omega) haM2
      · have hconj : ι s * ι (r ^ a) * (ι s)⁻¹ = ι (r ^ (M - a)) := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
          rw [hsinv, conj_pow_of_dihedral hss hrel a, inv_eq_iff_mul_eq_one, ← pow_add,
            show a + (M - a) = M by omega, hrM]
        rw [← hc (ι (r ^ a)) (ι s), hconj]
        exact hzero (M - a) (by omega) (by omega)
    · exact hv x hxD
  have hfinrank : Module.finrank ℂ U ≤ M / 2 := by
    have h := LinearMap.finrank_le_finrank_of_injective hev
    simpa using h
  have hspan_le : Submodule.span ℂ (Set.range (dihedralSectionFamily π r s M)) ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨o, rfl⟩
    exact hmem o
  have hspan_rank :
      Module.finrank ℂ (Submodule.span ℂ (Set.range (dihedralSectionFamily π r s M))) =
        M / 2 := by
    rw [finrank_span_eq_card hlinind, card_option_dihedralIndexSet hM2]
  have hspan : Submodule.span ℂ (Set.range (dihedralSectionFamily π r s M)) = U :=
    Submodule.eq_of_le_of_finrank_le hspan_le (by rw [hspan_rank]; exact hfinrank)
  refine ⟨hlinind, hspan, ?_⟩
  rw [← hspan, hspan_rank]

theorem dihedral_section_quotient_basis_of_embedding (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1))
    (hcard : Nat.card S = 2 * M) (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M)
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (hι : Function.Injective ι) [R.Normal]
    (hRodd : Odd (Nat.card R)) (hprod : ∀ c : C, ∃ u ∈ R, ∃ y : S, c = u * ι y)
    (hRS : R ⊓ ι.range = ⊥) (ht : ι (r ^ (M / 2)) ∈ Subgroup.center C) :
    (∃! π : C →* S, π.ker = R ∧ π.comp ι = MonoidHom.id S) ∧
    ∀ π : C →* S, π.ker = R → π.comp ι = MonoidHom.id S →
      centralInvolutionSection (ι (r ^ (M / 2))) =
        π ⁻¹' ((Subgroup.zpowers r : Set S) \ {1}) ∧
      LinearIndependent ℂ (dihedralSectionFamily π r s M) ∧
      Submodule.span ℂ (Set.range (dihedralSectionFamily π r s M)) =
        sectionQuotientSpace π (centralInvolutionSection (ι (r ^ (M / 2)))) ∧
      Module.finrank ℂ (sectionQuotientSpace π (centralInvolutionSection (ι (r ^ (M / 2))))) =
        M / 2 ∧
      ∀ F H : S → ℂ, BlocksInnerProduct (F ∘ π) (H ∘ π) = BlocksInnerProduct F H := by
  refine ⟨exists_unique_retraction ι R hι hRS hprod, fun π hker hid => ?_⟩
  obtain ⟨hlin, hspan, hrank⟩ :=
    dihedralSectionFamily_basis hn hM hcard hgen hr hs hrel hRodd ht hker hid
  have hπsurj : Function.Surjective π := fun y => ⟨ι y, DFunLike.congr_fun hid y⟩
  refine ⟨?_, hlin, hspan, hrank, blocksInnerProduct_comp_surjective π hπsurj⟩
  ext x
  rw [mem_centralInvolutionSection_iff_retraction hn hM hcard hgen hr hs hrel hRodd ht hker hid]
  simp

end Basis

theorem dihedral_central_involution_section_quotient_basis {C : Type} [Group C] [Fintype C]
    {n M : ℕ} (hn : 2 ≤ n) (hM : M = 2 ^ (n - 1)) (S : Subgroup C) (r s : S)
    (hcard : Nat.card S = 2 * M) (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M)
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) (R : Subgroup C) [R.Normal]
    (hRodd : Odd (Nat.card R)) (hRS : ∀ c : C, ∃ u ∈ R, ∃ y ∈ S, c = u * y)
    (hRS1 : R ⊓ S = ⊥) (ht : ((r ^ (M / 2) : S) : C) ∈ Subgroup.center C) :
    (∃! π : C →* S, π.ker = R ∧ ∀ y : S, π y = y) ∧
    ∀ π : C →* S, π.ker = R → (∀ y : S, π y = y) →
      centralInvolutionSection ((r ^ (M / 2) : S) : C) =
        π ⁻¹' ((Subgroup.zpowers r : Set S) \ {1}) ∧
      LinearIndependent ℂ (dihedralSectionFamily π r s M) ∧
      Submodule.span ℂ (Set.range (dihedralSectionFamily π r s M)) =
        sectionQuotientSpace π (centralInvolutionSection ((r ^ (M / 2) : S) : C)) ∧
      Module.finrank ℂ
          (sectionQuotientSpace π (centralInvolutionSection ((r ^ (M / 2) : S) : C))) =
        M / 2 ∧
      ∀ F H : S → ℂ, BlocksInnerProduct (F ∘ π) (H ∘ π) = BlocksInnerProduct F H := by
  have hcomp : ∀ π : C →* S, π.comp S.subtype = MonoidHom.id S ↔ ∀ y : S, π y = y := by
    intro π
    constructor
    · intro h y
      exact DFunLike.congr_fun h y
    · intro h
      ext y
      exact congrArg Subtype.val (h y)
  have hprod : ∀ c : C, ∃ u ∈ R, ∃ y : S, c = u * S.subtype y := by
    intro c
    obtain ⟨u, hu, y, hy, rfl⟩ := hRS c
    exact ⟨u, hu, ⟨y, hy⟩, rfl⟩
  have hRS' : R ⊓ S.subtype.range = ⊥ := by rwa [Subgroup.range_subtype]
  obtain ⟨huniq, hrest⟩ := dihedral_section_quotient_basis_of_embedding (ι := S.subtype) hn hM
    hcard hgen hr hs hrel Subtype.val_injective hRodd hprod hRS' ht
  refine ⟨?_, fun π hker hid => hrest π hker ((hcomp π).mpr hid)⟩
  obtain ⟨π, ⟨hker, hid⟩, huniq'⟩ := huniq
  exact ⟨π, ⟨hker, (hcomp π).mp hid⟩, fun π' ⟨hker', hid'⟩ =>
    huniq' π' ⟨hker', (hcomp π').mpr hid'⟩⟩

end CFSG.Semidihedral.Principal
