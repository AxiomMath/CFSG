module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Steinberg.Adjoint


theorem exists_conj_mem_of_odd_index {C : Type*} [Group C] [Finite C] (N : Subgroup C)
    (hN : Odd N.index) {x : C} (hx : x * x = 1) : ∃ u : C, u * x * u⁻¹ ∈ N := by
  classical
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hx
  have hpg : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (x ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ¬ 2 ∣ Nat.card (C ⧸ N) := by
    have hQI : Nat.card (C ⧸ N) = N.index := rfl
    rw [hQI]
    exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hN)
  obtain ⟨Q, hQ⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (C ⧸ N) hcard
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  have hfix := hQ ⟨x, Subgroup.mem_zpowers x⟩
  change ((x * z : C) : C ⧸ N) = (z : C ⧸ N) at hfix
  rw [QuotientGroup.eq] at hfix
  refine ⟨z⁻¹, ?_⟩
  have h2 : z⁻¹ * x * z ∈ N := by
    have := N.inv_mem hfix
    simpa [mul_assoc] using this
  simpa [mul_assoc] using h2



section S0

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def leviMonomial (τ : Tag) (K : Type) [Field K] (J : Set (Fin τ.rank)) :
    Subgroup (ModGL τ K) :=
  parabolicLevi τ K J ⊓ monomialSubgroup τ K

theorem leviMonomial_le_levi (J : Set (Fin τ.rank)) : leviMonomial τ K J ≤ parabolicLevi τ K J :=
  inf_le_left

theorem card_radical_mul_card_levi [Finite K] (J : Set (Fin τ.rank)) :
    Nat.card (parabolicRadical τ K J) * Nat.card (parabolicLevi τ K J) =
      Nat.card (parabolicSubgroup τ K J) := by
  classical
  obtain ⟨hQP, -, -, hMP, hQM, -, huniq, -⟩ := parabolic_root_radical_Levi_factors τ K J
  have hle : ∀ (a : parabolicRadical τ K J) (b : parabolicLevi τ K J),
      (a : ModGL τ K) * b ∈ parabolicSubgroup τ K J := fun a b =>
    mul_mem (hQP a.2) (hMP b.2)
  let f : parabolicRadical τ K J × parabolicLevi τ K J → parabolicSubgroup τ K J :=
    fun p => ⟨p.1 * p.2, hle p.1 p.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p p' h => ?_, fun g => ?_⟩
    · have h' : (p.1 : ModGL τ K) * p.2 = p'.1 * p'.2 := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_parabolic p.1.2 p'.1.2 p.2.2 p'.2.2 h'
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · obtain ⟨⟨q, m⟩, ⟨hq, hm, hg⟩, -⟩ := huniq g g.2
      exact ⟨(⟨q, hq⟩, ⟨m, hm⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf)




end S0

section S1

variable {τ : Tag} {K : Type} [Field K]

theorem weylQuotientHom_mem_parabolicWeylGroup {J : Set (Fin τ.rank)} {n : ModGL τ K}
    (hn : n ∈ monomialSubgroup τ K) (hL : n ∈ parabolicLevi τ K J) :
    weylQuotientHom τ K ⟨n, hn⟩ ∈ parabolicWeylGroup τ J := by
  obtain ⟨w₀, h, hh, he⟩ := monomialSubgroup_le_torusWeylCosets hn
  have hw₀ : weylQuotientHom τ K ⟨n, hn⟩ = w₀ := weylQuotientHom_eq (by
    change MapsRootLines n w₀
    rw [he]
    simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w₀))
  rw [hw₀]
  have hP : n ∈ parabolicSubgroup τ K J := parabolicLevi_le_parabolicSubgroup J hL
  have hcell : n ∈ parabolicCells τ K J := by
    rw [← parabolicSubgroup_eq_parabolicCells]; exact hP
  obtain ⟨w, hw, hnw⟩ := mem_parabolicCells.1 hcell
  have hn0 : n ∈ bruhatCell τ K w₀ := by
    rw [he]
    exact mem_bruhatCell.2 ⟨h, Subgroup.mem_sup_left hh, 1, one_mem _, by simp⟩
  by_cases hww : w = w₀
  · rwa [← hww]
  · exact absurd hn0 (Set.disjoint_left.1 (disjoint_bruhatCell (K := K) hww) hnw)




end S1

section S2

variable {τ : Tag} {K : Type} [Field K]

theorem torusGroup_le_leviMonomial (J : Set (Fin τ.rank)) :
    torusGroup τ K ≤ leviMonomial τ K J :=
  le_inf (torusGroup_le_parabolicLevi J) torusGroup_le_monomialSubgroup

@[expose] noncomputable def leviWeylHom (τ : Tag) (K : Type) [Field K] (J : Set (Fin τ.rank)) :
    leviMonomial τ K J →* WeylGroup τ :=
  (weylQuotientHom τ K).comp (Subgroup.inclusion inf_le_right)

theorem leviWeylHom_range (J : Set (Fin τ.rank)) :
    (leviWeylHom τ K J).range = parabolicWeylGroup τ J := by
  apply le_antisymm
  · rintro _ ⟨n, rfl⟩
    exact weylQuotientHom_mem_parabolicWeylGroup n.2.2 n.2.1
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨⟨weylElt τ K j 1, weylElt_mem_parabolicLevi hj, weylElt_mem_monomialSubgroup j⟩, ?_⟩
    exact weylQuotientHom_eq (mapsRootLines_weylElt j)

theorem leviWeylHom_ker (J : Set (Fin τ.rank)) :
    (leviWeylHom τ K J).ker = (torusGroup τ K).subgroupOf (leviMonomial τ K J) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hn
    obtain ⟨w₀, h, hh, he⟩ := monomialSubgroup_le_torusWeylCosets n.2.2
    have hw₀ : weylQuotientHom τ K ⟨n, n.2.2⟩ = w₀ := weylQuotientHom_eq (by
      change MapsRootLines (n : ModGL τ K) w₀
      rw [he]
      simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w₀))
    have h1 : weylQuotientHom τ K ⟨n, n.2.2⟩ = 1 := hn
    rw [hw₀] at h1
    rw [he, h1, canonicalRep_one, mul_one]
    exact hh
  · intro hn
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hn)

theorem card_leviMonomial [Finite K] (J : Set (Fin τ.rank)) :
    Nat.card (leviMonomial τ K J) =
      Nat.card (torusGroup τ K) * Nat.card (parabolicWeylGroup τ J) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (leviWeylHom τ K J).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (leviWeylHom τ K J)).toEquiv,
    leviWeylHom_range, leviWeylHom_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusGroup_le_leviMonomial J)).toEquiv,
    mul_comm] at h1
  exact h1




end S2

section S3

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem levi_odd_index (J : Set (Fin τ.rank)) (hq : Odd (Nat.card K)) {M : ℕ}
    (hqM : Nat.card K ≡ 1 [MOD 2 ^ M]) (hW : ¬ 2 ^ M ∣ Nat.card (parabolicWeylGroup τ J)) :
    Odd ((leviMonomial τ K J).relIndex (parabolicLevi τ K J)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL (τ := τ) (K := K)
  have : Fintype (parabolicWeylGroup τ J) := Fintype.ofFinite _
  set q := Nat.card K with hqdef
  set W := Nat.card (parabolicWeylGroup τ J) with hWdef
  set P := ∑ᶠ w : parabolicWeylGroup τ J, q ^ (coxeterSystem τ).length w with hP
  set I := (leviMonomial τ K J).relIndex (parabolicLevi τ K J) with hI
  have hH : 0 < Nat.card (torusGroup τ K) := Nat.card_pos
  have hNM : leviMonomial τ K J ≤ parabolicLevi τ K J := leviMonomial_le_levi J
  have hIdef : I = ((leviMonomial τ K J).subgroupOf (parabolicLevi τ K J)).index := rfl
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells τ K
  have hPJ := hcell J
  have hQ := card_parabolicRadical (τ := τ) (K := K) J
  have hQM := card_radical_mul_card_levi (τ := τ) (K := K) J
  have hMI : Nat.card (parabolicLevi τ K J) = Nat.card (leviMonomial τ K J) * I := by
    have h1 := Subgroup.card_mul_index ((leviMonomial τ K J).subgroupOf (parabolicLevi τ K J))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, ← hIdef] at h1
    exact h1.symm
  have hrel : q ^ (parabolicRadicalRoots τ J).ncard * (W * I) =
      q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard * P := by
    apply Nat.eq_of_mul_eq_mul_left hH
    calc Nat.card (torusGroup τ K) * (q ^ (parabolicRadicalRoots τ J).ncard * (W * I))
        = q ^ (parabolicRadicalRoots τ J).ncard *
            (Nat.card (torusGroup τ K) * W * I) := by ring
      _ = Nat.card (parabolicRadical τ K J) * Nat.card (parabolicLevi τ K J) := by
          rw [hQ, hMI, card_leviMonomial]
      _ = Nat.card (torusGroup τ K) * q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard *
            P := by rw [hQM, hPJ]
      _ = _ := by ring
  have hPW : P ≡ W [MOD 2 ^ M] := by
    rw [← ZMod.natCast_eq_natCast_iff, hP, finsum_eq_sum_of_fintype, Nat.cast_sum]
    have hq1 : (q : ZMod (2 ^ M)) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hqM
    simp only [Nat.cast_pow, hq1, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hWdef, Nat.card_eq_fintype_card]
  have hW0 : W ≠ 0 := Nat.card_pos.ne'
  set e := W.factorization 2 with he
  have he1 : ¬ 2 ^ (e + 1) ∣ W := Nat.pow_succ_factorization_not_dvd hW0 Nat.prime_two
  have heM : e + 1 ≤ M := by
    by_contra h
    exact hW ((Nat.pow_dvd_pow 2 (by omega)).trans (Nat.ordProj_dvd W 2))
  by_contra hIe
  rw [Nat.not_odd_iff_even] at hIe
  obtain ⟨m, hm⟩ := hIe
  have hdvd : 2 ^ (e + 1) ∣ q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard * P := by
    rw [← hrel, hm, pow_succ]
    refine Dvd.dvd.mul_left ?_ _
    exact mul_dvd_mul (Nat.ordProj_dvd W 2) (Dvd.intro m (by ring))
  have hcop : Nat.Coprime (2 ^ (e + 1))
      (q ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard) :=
    Nat.Coprime.pow _ _ (Nat.coprime_two_left.2 hq)
  have hP2 : 2 ^ (e + 1) ∣ P := hcop.dvd_of_dvd_mul_left hdvd
  exact he1 ((hPW.dvd_iff (Nat.pow_dvd_pow 2 heM)).1 hP2)

theorem exists_conj_leviMonomial (J : Set (Fin τ.rank)) (hq : Odd (Nat.card K)) {M : ℕ}
    (hqM : Nat.card K ≡ 1 [MOD 2 ^ M]) (hW : ¬ 2 ^ M ∣ Nat.card (parabolicWeylGroup τ J))
    {y : ModGL τ K} (hy : y ∈ parabolicLevi τ K J) (hy2 : y * y = 1) :
    ∃ u ∈ parabolicLevi τ K J, u * y * u⁻¹ ∈ leviMonomial τ K J := by
  have : Finite (ModGL τ K) := finite_modGL (τ := τ) (K := K)
  have hodd := levi_odd_index (τ := τ) (K := K) J hq hqM hW
  have hodd' : Odd ((leviMonomial τ K J).subgroupOf (parabolicLevi τ K J)).index := hodd
  obtain ⟨u, hu⟩ := exists_conj_mem_of_odd_index ((leviMonomial τ K J).subgroupOf
    (parabolicLevi τ K J)) hodd' (x := (⟨y, hy⟩ : parabolicLevi τ K J)) (Subtype.ext hy2)
  refine ⟨u, u.2, ?_⟩
  exact (Subgroup.mem_subgroupOf.1 hu)




end S3

section S4

variable {τ : Tag} {K : Type} [Field K]

theorem neg_mem_parabolicRoots' {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRoots τ J) : -α ∈ parabolicRoots τ J :=
  ⟨IsRoot.neg hα.1, fun i hi => by simp [hα.2 i hi]⟩

theorem rootSubgroup_le_parabolicLevi' {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRoots τ J) : rootSubgroup τ K α ≤ parabolicLevi τ K J := by
  rcases IsRoot.height_pos_or_neg hα.1 with hpos | hneg
  · exact (le_iSup₂_of_le α ⟨hα, hα.1, hpos⟩ le_rfl :
      rootSubgroup τ K α ≤ parabolicLeviUnipotent τ K J).trans
      (parabolicLeviUnipotent_le_parabolicLevi J)
  · have hmem : -α ∈ parabolicPosRoots τ J :=
      ⟨neg_mem_parabolicRoots' hα, IsRoot.neg hα.1, by rw [height_neg]; omega⟩
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-α) rfl hmem
    have hα' : α = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by
      rw [smul_neg, hwj, neg_neg]
    rw [hα', ← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ j)]
    rintro _ ⟨u, hu, rfl⟩
    have huQ : u ∈ parabolicLevi τ K J := by
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_parabolicLevi hj c
    have hn := canonicalRep_mem_parabolicLevi (K := K) hw
    exact mul_mem (mul_mem hn huQ) (inv_mem hn)

theorem rootRankOneGroup_le_parabolicLevi {J : Set (Fin τ.rank)} {β : Fin τ.rank → ℤ}
    (hβ : β ∈ parabolicRoots τ J) : rootRankOneGroup τ K β ≤ parabolicLevi τ K J := by
  have hβ' : -β ∈ parabolicRoots τ J := neg_mem_parabolicRoots' hβ
  rintro _ ⟨A, rfl⟩
  have hcl : (Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K))) = ⊤ :=
    sl2_closure_upper_lower
  have hle : (Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K))) ≤
      (parabolicLevi τ K J).comap (rootSL2 τ K β) := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : sl2Upper K c = uSL c := rfl
      rw [e, rootSL2_uSL_eq]
      exact rootSubgroup_le_parabolicLevi' hβ (Subgroup.subset_closure ⟨_, rfl⟩)
    · obtain ⟨ε, -, hε⟩ := exists_rootSL2_vSL_eq (K := K) hβ.1
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      have e : sl2Lower K c = vSL c := rfl
      rw [e, hε]
      exact rootSubgroup_le_parabolicLevi' hβ' (Subgroup.subset_closure ⟨_, rfl⟩)
  exact hle (hcl ▸ Subgroup.mem_top A)




end S4

section S5

variable {τ : Tag} {K : Type} [Field K]

theorem rootReflection_smul_of_iform_eq_zero {α v : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h : iform α v = 0) : rootReflection α • v = v := by
  rw [rootReflection_smul hα]
  have : corootPair α v = 0 := by simp [corootPair, h]
  rw [this, zero_smul, sub_zero]

theorem prod_rootReflection_smul_of_orth (βs : List (Fin τ.rank → ℤ))
    (hroots : ∀ β ∈ βs, IsRoot τ β) {v : Fin τ.rank → ℤ} (hv : ∀ β ∈ βs, iform β v = 0) :
    (βs.map rootReflection).prod • v = v := by
  induction βs with
  | nil => simp
  | cons a γs ih =>
    rw [List.map_cons, List.prod_cons, mul_smul,
      ih (fun β hβ => hroots β (List.mem_cons_of_mem _ hβ))
        (fun β hβ => hv β (List.mem_cons_of_mem _ hβ)),
      rootReflection_smul_of_iform_eq_zero (hroots a List.mem_cons_self)
        (hv a List.mem_cons_self)]

theorem prod_rootReflection_smul_mem (βs : List (Fin τ.rank → ℤ))
    (hroots : ∀ β ∈ βs, IsRoot τ β)
    (hpair : βs.Pairwise fun β γ => iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)) :
    ∀ β ∈ βs, (βs.map rootReflection).prod • β = -β := by
  induction βs with
  | nil => simp
  | cons a γs ih =>
    rw [List.pairwise_cons] at hpair
    intro β hβ
    rw [List.map_cons, List.prod_cons, mul_smul]
    rcases List.mem_cons.1 hβ with rfl | hβ'
    · rw [prod_rootReflection_smul_of_orth γs (fun β hβ => hroots β (List.mem_cons_of_mem _ hβ))
        (fun γ hγ => by rw [iform_comm]; exact (hpair.1 γ hγ).1),
        rootReflection_smul_self (hroots β List.mem_cons_self)]
    · rw [ih (fun β hβ => hroots β (List.mem_cons_of_mem _ hβ)) hpair.2 β hβ', smul_neg,
        rootReflection_smul_of_iform_eq_zero (hroots a List.mem_cons_self) (hpair.1 β hβ').1]

theorem exists_levi_conj_mem_torusGroup [IsAlgClosed K] (hK : ringChar K ≠ 2)
    {J : Set (Fin τ.rank)} {n : ModGL τ K} (hn : n ∈ monomialSubgroup τ K)
    (hnJ : n ∈ parabolicLevi τ K J) (hw : weylQuotientHom τ K ⟨n, hn⟩ ^ 2 = 1) :
    ∃ g ∈ parabolicLevi τ K J, g * n * g⁻¹ ∈ torusGroup τ K := by
  have hwJ := weylQuotientHom_mem_parabolicWeylGroup hn hnJ
  obtain ⟨βs, -, hroots, hprod, hpair⟩ :=
    exceptional_Lang_Weyl_involution_strongly_orthogonal_reflections τ _ hw
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_pairwise hK βs hroots hpair n hn hprod
  refine ⟨g, ?_, hgn⟩
  have hβJ : ∀ β ∈ βs, β ∈ parabolicRoots τ J := fun β hβ => ⟨hroots β hβ, fun i hi => by
    have h1 := prod_rootReflection_smul_mem βs hroots hpair β hβ
    rw [← hprod] at h1
    have h2 := smul_apply_of_mem_parabolicWeylGroup hwJ β hi
    rw [h1] at h2
    simp only [Pi.neg_apply] at h2
    omega⟩
  have hle : Subgroup.closure (⋃ β ∈ βs, (rootRankOneGroup τ K β : Set (ModGL τ K))) ≤
      parabolicLevi τ K J := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨β, hβ, hx⟩ := hx
    exact rootRankOneGroup_le_parabolicLevi (hβJ β hβ) hx
  exact hle hg


end S5


end CFSG.ClassicalInvolution.ModelFacts.Levi
