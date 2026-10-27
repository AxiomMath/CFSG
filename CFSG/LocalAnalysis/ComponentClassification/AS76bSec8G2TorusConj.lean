module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Centr
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveFixedPoints

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

section SL2

open Projectivization Matrix MulAction
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K]

theorem pairDet_mulVec (M : Matrix (Fin 2) (Fin 2) K) (v w : Fin 2 → K) :
    CFSG.LinearGroups.pairDet (M *ᵥ v) (M *ᵥ w) = M.det * CFSG.LinearGroups.pairDet v w := by
  simp only [CFSG.LinearGroups.pairDet, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

theorem exists_eigen_of_smul_eq {g : Matrix.SpecialLinearGroup (Fin 2) K} {P : ℙ K (Fin 2 → K)}
    (h : g • P = P) : ∃ c : K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ P.rep = c • P.rep := by
  have h' := h
  rw [← mk_rep P, smul_mk, mk_eq_mk_iff'] at h'
  obtain ⟨a, ha⟩ := h'
  exact ⟨a, ha.symm⟩

theorem eq_one_of_three_fixed [CharP K 2] {g : Matrix.SpecialLinearGroup (Fin 2) K}
    {P₁ P₂ P₃ : ℙ K (Fin 2 → K)} (h₁ : g • P₁ = P₁) (h₂ : g • P₂ = P₂) (h₃ : g • P₃ = P₃)
    (h12 : P₁ ≠ P₂) (h13 : P₁ ≠ P₃) (h23 : P₂ ≠ P₃) : g = 1 := by
  obtain ⟨c₁, hc₁⟩ := exists_eigen_of_smul_eq h₁
  obtain ⟨c₂, hc₂⟩ := exists_eigen_of_smul_eq h₂
  obtain ⟨c₃, hc₃⟩ := exists_eigen_of_smul_eq h₃
  have hd : ∀ {P P' : ℙ K (Fin 2 → K)}, P ≠ P' → CFSG.LinearGroups.pairDet P.rep P'.rep ≠ 0 := by
    intro P P' hPP'
    rw [← CFSG.LinearGroups.mk_ne_mk_iff_pairDet_ne_zero (rep_nonzero P) (rep_nonzero P'),
      mk_rep, mk_rep]
    exact hPP'
  have hprod : ∀ {P P' : ℙ K (Fin 2 → K)} {c c' : K}, P ≠ P' →
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ P.rep = c • P.rep →
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ P'.rep = c' • P'.rep → c * c' = 1 := by
    intro P P' c c' hPP' hc hc'
    have e := pairDet_mulVec (g : Matrix (Fin 2) (Fin 2) K) P.rep P'.rep
    rw [hc, hc', g.2, one_mul] at e
    have e' : CFSG.LinearGroups.pairDet (c • P.rep) (c' • P'.rep) =
        c * c' * CFSG.LinearGroups.pairDet P.rep P'.rep := by
      simp only [CFSG.LinearGroups.pairDet, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e'] at e
    have h0 := hd hPP'
    calc c * c' = c * c' * CFSG.LinearGroups.pairDet P.rep P'.rep /
        CFSG.LinearGroups.pairDet P.rep P'.rep := by field_simp
      _ = 1 := by rw [e, div_self h0]
  have e12 := hprod h12 hc₁ hc₂
  have e13 := hprod h13 hc₁ hc₃
  have e23 := hprod h23 hc₂ hc₃
  have hc0 : c₁ ≠ 0 := left_ne_zero_of_mul_eq_one e12
  have h23' : c₂ = c₃ := mul_left_cancel₀ hc0 (e12.trans e13.symm)
  have hsq : c₂ * c₂ = 1 := by
    nth_rewrite 2 [h23']
    exact e23
  have hc2 : c₂ = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h : (c₂ - 1) * (c₂ - 1) = 0 := by linear_combination hsq + (1 - c₂) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h)
  have hc1 : c₁ = 1 := by rw [hc2, mul_one] at e12; exact e12
  rw [hc1, one_smul] at hc₁
  rw [hc2, one_smul] at hc₂
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = 1 :=
    CFSG.LinearGroups.eq_of_mulVec_eq (hd h12) (by rw [hc₁, one_mulVec])
      (by rw [hc₂, one_mulVec])
  exact Subtype.ext (hg.trans Matrix.SpecialLinearGroup.coe_one.symm)

theorem ncard_fixedBy_le_two [Finite K] [CharP K 2] {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g ≠ 1) : (fixedBy (ℙ K (Fin 2 → K)) g).ncard ≤ 2 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h
  exact hg (eq_one_of_three_fixed ha hb hc hab hac hbc)

theorem false_of_orbit_sizes {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 3) {N : ℕ}
    (hN : Odd N) (d : ι → ℕ) (hd : ∀ i, d i ∣ N) (hd1 : ∀ i, d i ≠ 1)
    (hsum : ∑ i, d i = N + 2) : False := by
  classical
  have hN0 : 0 < N := hN.pos
  have hd3 : ∀ i, 3 ≤ d i := by
    intro i
    obtain ⟨k, hk⟩ := hd i
    have hodd : Odd (d i) := Nat.Odd.of_mul_left (hk ▸ hN)
    obtain ⟨j, hj⟩ := hodd
    have := hd1 i
    omega
  by_cases hex : ∃ i, d i = N
  · obtain ⟨i, hi⟩ := hex
    have hsplit := Finset.sum_erase_add (s := Finset.univ) (f := d) (Finset.mem_univ i)
    rw [hsum, hi] at hsplit
    have h2 : ∑ j ∈ Finset.univ.erase i, d j = 2 := by omega
    rcases (Finset.univ.erase i).eq_empty_or_nonempty with hne | ⟨j, hj⟩
    · rw [hne, Finset.sum_empty] at h2
      omega
    · have h3 := Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) hj
      have := hd3 j
      omega
  · have hle : ∀ i, 3 * d i ≤ N := by
      intro i
      obtain ⟨k, hk⟩ := hd i
      have hk1 : k ≠ 1 := fun h => hex ⟨i, by rw [hk, h, mul_one]⟩
      have hkodd : Odd k := Nat.Odd.of_mul_right (hk ▸ hN)
      obtain ⟨j, hj⟩ := hkodd
      have h3 : 3 ≤ k := by omega
      rw [hk]
      nlinarith [hd3 i]
    have h3 : 3 * ∑ i, d i ≤ 3 * N := by
      rw [Finset.mul_sum]
      calc ∑ i, 3 * d i ≤ ∑ _i : ι, N := Finset.sum_le_sum fun i _ => hle i
        _ = Fintype.card ι * N := by simp
        _ ≤ 3 * N := Nat.mul_le_mul_right _ hι
    omega

theorem exists_fixed_of_card [Finite K] [CharP K 2]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hT : Nat.card T = Nat.card K - 1) :
    ∃ P : ℙ K (Fin 2 → K), ∀ g ∈ T, g • P = P := by
  classical
  have := Fintype.ofFinite K
  have hX : Nat.card (ℙ K (Fin 2 → K)) = Nat.card K + 1 := card_of_finrank_two K _ (by simp)
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have h2q : 2 ∣ Nat.card K := by
    have h := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card] at h
    exact (CharP.cast_eq_zero_iff K 2 _).1 h
  have hodd : Odd (Nat.card K - 1) := by
    obtain ⟨k, hk⟩ := h2q
    exact ⟨k - 1, by omega⟩
  by_contra hno
  have hno' : ∀ P : ℙ K (Fin 2 → K), ∃ g ∈ T, g • P ≠ P := by
    intro P
    by_contra h
    exact hno ⟨P, fun g hg => by_contra fun h' => h ⟨g, hg, h'⟩⟩
  have := Fintype.ofFinite T
  have := Fintype.ofFinite (ℙ K (Fin 2 → K))
  have hsum : ∑ g : T, Nat.card (fixedBy (ℙ K (Fin 2 → K)) g) ≤ 3 * (Nat.card K - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : T))]
    have h1 : Nat.card (fixedBy (ℙ K (Fin 2 → K)) (1 : T)) = Nat.card K + 1 := by
      rw [show fixedBy (ℙ K (Fin 2 → K)) (1 : T) = Set.univ from
        Set.eq_univ_of_forall fun x => one_smul _ x, Nat.card_coe_set_eq, Set.ncard_univ, hX]
    have h2 : ∑ g ∈ Finset.univ.erase (1 : T), Nat.card (fixedBy (ℙ K (Fin 2 → K)) g) ≤
        ∑ _g ∈ Finset.univ.erase (1 : T), 2 := Finset.sum_le_sum fun g hg => by
      have hg1 : (g : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := fun h =>
        Finset.ne_of_mem_erase hg (Subtype.ext h)
      rw [Nat.card_coe_set_eq]
      exact ncard_fixedBy_le_two hg1
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hT, smul_eq_mul] at h2
    rw [h1]
    omega
  have hΩ : Nat.card (orbitRel.Quotient T (ℙ K (Fin 2 → K))) ≤ 3 := by
    have e := Nat.card_congr (sigmaFixedByEquivOrbitsProdGroup T (ℙ K (Fin 2 → K)))
    rw [Nat.card_sigma, Nat.card_prod, hT] at e
    have h3 : Nat.card (orbitRel.Quotient T (ℙ K (Fin 2 → K))) * (Nat.card K - 1) ≤
        3 * (Nat.card K - 1) := e ▸ hsum
    exact Nat.le_of_mul_le_mul_right h3 (by omega)
  have := Fintype.ofFinite (orbitRel.Quotient T (ℙ K (Fin 2 → K)))
  have hcardX := Nat.card_congr (selfEquivSigmaOrbits T (ℙ K (Fin 2 → K)))
  rw [Nat.card_sigma] at hcardX
  refine false_of_orbit_sizes (ι := orbitRel.Quotient T (ℙ K (Fin 2 → K)))
    (by rw [← Nat.card_eq_fintype_card]; exact hΩ) hodd
    (fun ω => Nat.card (orbit T ω.out)) (fun ω => ?_) (fun ω => ?_) ?_
  · rw [← hT, Nat.card_coe_set_eq, ← index_stabilizer]
    exact Subgroup.index_dvd_card _
  · intro h1
    rw [Nat.card_coe_set_eq, Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    obtain ⟨g, hg, hne⟩ := hno' ω.out
    have hx : ω.out ∈ orbit T ω.out := mem_orbit_self _
    have hgx : (⟨g, hg⟩ : T) • ω.out ∈ orbit T ω.out := mem_orbit _ _
    rw [ha] at hx hgx
    exact hne ((Set.mem_singleton_iff.1 hgx).trans (Set.mem_singleton_iff.1 hx).symm)
  · rw [← hcardX, hX]
    omega

theorem apply_one_zero_eq_zero_of_smul {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : g • mk K ![(1 : K), 0] (by simp) = mk K ![(1 : K), 0] (by simp)) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [smul_mk, mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrFun ha 1
  simp [Matrix.SpecialLinearGroup.smul_def, mulVec, dotProduct, Fin.sum_univ_two] at h1
  exact h1.symm

theorem smul_mk_e0_eq {g : Matrix.SpecialLinearGroup (Fin 2) K} {v : Fin 2 → K} (hv : v ≠ 0)
    (h : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = v) :
    g • mk K ![(1 : K), 0] (by simp) = mk K v hv := by
  rw [smul_mk]
  exact (mk_eq_mk_iff' K _ _ _ _).2 ⟨1, by rw [one_smul]; exact h.symm⟩

theorem exists_smul_mk_e0 (P : ℙ K (Fin 2 → K)) :
    ∃ g₀ : Matrix.SpecialLinearGroup (Fin 2) K, g₀ • mk K ![(1 : K), 0] (by simp) = P := by
  have hv0 : P.rep ≠ 0 := rep_nonzero P
  by_cases h0 : P.rep 0 = 0
  · have h1 : P.rep 1 ≠ 0 := fun h1 => hv0 (by funext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, -(P.rep 1)⁻¹; P.rep 1, 0], by simp [det_fin_two, h1]⟩, ?_⟩
    conv_rhs => rw [← mk_rep P]
    refine smul_mk_e0_eq hv0 ?_
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![P.rep 0, 0; P.rep 1, (P.rep 0)⁻¹], by simp [det_fin_two, h0]⟩, ?_⟩
    conv_rhs => rw [← mk_rep P]
    refine smul_mk_e0_eq hv0 ?_
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_conj_upper_of_card [Finite K] [CharP K 2]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hT : Nat.card T = Nat.card K - 1) :
    ∃ g₀ : Matrix.SpecialLinearGroup (Fin 2) K, ∀ g ∈ T,
      ((g₀⁻¹ * g * g₀ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  obtain ⟨P, hP⟩ := exists_fixed_of_card T hT
  obtain ⟨g₀, hg₀⟩ := exists_smul_mk_e0 P
  refine ⟨g₀, fun g hg => apply_one_zero_eq_zero_of_smul ?_⟩
  rw [mul_smul, mul_smul, hg₀, hP g hg, ← hg₀, inv_smul_smul]


end SL2

theorem card_sup_eq_mul_of_inf_eq_bot {G : Type*} [Group G] {N T : Subgroup G}
    (hT : T ≤ normalizer (N : Set G)) (hNT : N ⊓ T = ⊥) :
    Nat.card ↥(N ⊔ T) = Nat.card N * Nat.card T := by
  let f : N × T → ↥(N ⊔ T) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨n, t⟩ ⟨n', t'⟩ heq
      have e : (n : G) * t = n' * t' := congrArg Subtype.val heq
      have h1 : (n' : G)⁻¹ * n = t' * (t : G)⁻¹ := by
        calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * t) * (t : G)⁻¹ := by group
          _ = (n' : G)⁻¹ * (n' * t') * (t : G)⁻¹ := by rw [e]
          _ = t' * (t : G)⁻¹ := by group
      have hmem : (n' : G)⁻¹ * n ∈ N ⊓ T :=
        mem_inf.mpr ⟨mul_mem (inv_mem n'.2) n.2, h1 ▸ mul_mem t'.2 (inv_mem t.2)⟩
      rw [hNT, mem_bot, inv_mul_eq_one] at hmem
      have hn : n = n' := Subtype.ext hmem.symm
      subst hn
      have ht : t = t' := Subtype.ext (mul_left_cancel e)
      rw [ht]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ ((N ⊔ T : Subgroup G) : Set G) := hx
      rw [coe_mul_of_right_le_normalizer_left N T hT] at hx'
      obtain ⟨n, hn, t, ht, rfl⟩ := hx'
      exact ⟨(⟨n, hn⟩, ⟨t, ht⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

section TorusConj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem odd_card_sub_one [CharP K 2] : Odd (Nat.card K - 1) := by
  have := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have h2q : 2 ∣ Nat.card K := by
    have h := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card] at h
    exact (CharP.cast_eq_zero_iff K 2 _).1 h
  obtain ⟨k, hk⟩ := h2q
  exact ⟨k - 1, by omega⟩

omit [Finite K] [CharP K 2] in
theorem card_g2TorusR
    : Nat.card (g2TorusR K) = Nat.card K - 1 := by
  have hinj : Function.Injective (LieType.Chevalley.torusEltHom .G2 K g2ir) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h := torus_r_v (K := K) t 1
    have ht' : torusElt .G2 K g2ir t = 1 := ht
    rw [ht', one_mul, inv_one, mul_one, mul_one] at h
    exact Units.ext (pinnedX_injective .G2 K g2v h).symm
  show Nat.card (LieType.Chevalley.torusEltHom .G2 K g2ir).range = _
  rw [← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_range_of_injective hinj,
    Nat.card_units]

omit [Finite K] [CharP K 2] in
theorem card_posUnipotent_g2
    : Nat.card (posUnipotent .G2 K) = Nat.card K ^ 6 := by
  have hinj : Function.Injective (fun p : K × K × K × K × K × K =>
      g2N p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
    intro p p' h
    beta_reduce at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2N_injective h
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6))))
  have hrange : Set.range (fun p : K × K × K × K × K × K =>
      g2N p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) =
        (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      exact g2N_mem_posUnipotent _ _ _ _ _ _
    · intro hg
      obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hg
      exact ⟨(A, B, C, D, E, F), rfl⟩
  rw [← SetLike.coe_sort_coe, ← hrange, Nat.card_range_of_injective hinj]
  simp only [Nat.card_prod]
  ring

theorem g2LongCent_le_normalizer :
    g2LongCent K ≤ normalizer (g2LongRadical K : Set (ModGL .G2 K)) := by
  obtain ⟨-, -, -, -, -, hLN, -⟩ := even_G2_highest_long_root_centralizer K
  rw [g2LongCent_eq_sup]
  exact sup_le le_normalizer hLN

theorem exists_conj_g2TorusR
    {S : Subgroup (ModGL .G2 K)} (hSP : S ≤ g2LongCent K)
    (hS : Nat.card S = Nat.card (g2TorusR K)) :
    ∃ h ∈ g2LongCent K, S = (g2TorusR K).map (MulAut.conj h).toMonoidHom := by
  classical
  have := LieType.Chevalley.finite_modGL (τ := .G2) (K := K)
  rw [card_g2TorusR] at hS
  obtain ⟨-, -, hQ2, -, hset, hLN, hQL, -⟩ := even_G2_highest_long_root_centralizer K
  obtain ⟨ρ, -, -, -, -, hrange, hinj, hcell0, -⟩ := g2_rank_one (K := K) g2ir
  have hPN := g2LongCent_le_normalizer (K := K)
  have hQP : g2LongRadical K ≤ g2LongCent K := g2LongCent_eq_sup (K := K) ▸ le_sup_left
  have hLP : g2RankOne K g2ir ≤ g2LongCent K := g2LongCent_eq_sup (K := K) ▸ le_sup_right
  have hSQ : g2LongRadical K ⊓ S = ⊥ := by
    have := Fact.mk Nat.prime_two
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ2
    refine disjoint_iff.1 (disjoint_of_coprime_natCard ?_)
    rw [hS, hn]
    exact (Nat.Coprime.pow_right n (Nat.coprime_two_right.2 odd_card_sub_one)).symm
  set Sb := (S ⊔ g2LongRadical K) ⊓ g2RankOne K g2ir with hSb
  have hSbL : Sb ≤ g2RankOne K g2ir := inf_le_right
  have hSbN : Sb ≤ normalizer (g2LongRadical K : Set (ModGL .G2 K)) :=
    hSbL.trans (hLP.trans hPN)
  have hSle : S ≤ g2LongRadical K ⊔ Sb := by
    intro s hs
    have hs' : s ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hSP hs
    rw [hset] at hs'
    obtain ⟨q, hq, l, hl, hql⟩ := hs'
    beta_reduce at hql
    have hlS : l ∈ S ⊔ g2LongRadical K := by
      have e : l = q⁻¹ * s := by rw [← hql]; group
      rw [e]
      exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hs)
    rw [← hql]
    exact mul_mem (mem_sup_left hq) (mem_sup_right (mem_inf.2 ⟨hlS, hl⟩))
  have hSQeq : S ⊔ g2LongRadical K = g2LongRadical K ⊔ Sb :=
    le_antisymm (sup_le hSle le_sup_left) (sup_le le_sup_right inf_le_left)
  have hcardSb : Nat.card Sb = Nat.card K - 1 := by
    have h1 := card_sup_eq_mul_of_inf_eq_bot (hSP.trans hPN) hSQ
    have h2 := card_sup_eq_mul_of_inf_eq_bot hSbN (by
      rw [eq_bot_iff]
      exact (inf_le_inf_left _ hSbL).trans hQL.le)
    rw [sup_comm, hSQeq, h2] at h1
    rw [← hS]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  set T := Sb.comap ρ with hT
  have hcardT : Nat.card T = Nat.card K - 1 := by
    have hmap : T.map ρ = Sb := map_comap_eq_self (by rw [hrange]; exact hSbL)
    rw [← hcardSb, ← hmap]
    exact Nat.card_congr (equivMapOfInjective T ρ hinj).toEquiv
  obtain ⟨g₀, hg₀⟩ := exists_conj_upper_of_card T hcardT
  have hHU : g2TorusR K ≤ normalizer (posUnipotent .G2 K : Set (ModGL .G2 K)) := by
    rintro _ ⟨t, rfl⟩
    exact LieType.Chevalley.torusGroup_le_normalizer_posUnipotent
      (LieType.Chevalley.torusElt_mem_torusGroup _ _)
  have hUH : posUnipotent .G2 K ⊓ g2TorusR K = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, t, rfl⟩
    have h := LieType.Chevalley.torusGroup_inf_posUnipotent (τ := .G2) (R := K)
    rw [eq_bot_iff] at h
    exact h ⟨LieType.Chevalley.torusElt_mem_torusGroup _ _, hxU⟩
  have hQU : g2LongRadical K ≤ posUnipotent .G2 K := by
    rintro _ ⟨B, C, D, E, F, rfl⟩
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  have hUP : posUnipotent .G2 K ≤ g2LongCent K := by
    intro u hu
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2
      (commute_pinnedX_c_of_mem_posUnipotent 1 hu).eq.symm⟩
    obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
    simp only [g2N]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)
  have hHP : g2TorusR K ≤ g2LongCent K := by
    rintro _ ⟨t, rfl⟩
    exact hLP (torusElt_mem_g2RankOne g2ir t)
  set M := posUnipotent .G2 K ⊔ g2TorusR K with hM
  have hMP : M ≤ g2LongCent K := sup_le hUP hHP
  set n₀ := ρ g₀ with hn₀
  have hn₀L : n₀ ∈ g2RankOne K g2ir := by rw [← hrange]; exact ⟨g₀, rfl⟩
  set S' := S.map (MulAut.conj n₀⁻¹).toMonoidHom with hS'
  have hS'M : S' ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' := hSle hs
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hSbN] at hs'
    obtain ⟨q, hq, l, hl, rfl⟩ := hs'
    have hlR : l ∈ ρ.range := by rw [hrange]; exact hSbL hl
    obtain ⟨g, rfl⟩ := hlR
    have hgT : g ∈ T := hl
    show n₀⁻¹ * (q * ρ g) * n₀⁻¹⁻¹ ∈ M
    have e : n₀⁻¹ * (q * ρ g) * n₀⁻¹⁻¹ = n₀⁻¹ * q * n₀⁻¹⁻¹ * ρ (g₀⁻¹ * g * g₀) := by
      simp only [hn₀, map_mul, map_inv, inv_inv]
      group
    rw [e]
    refine mul_mem (mem_sup_left (hQU ((mem_normalizer_iff.1
      (inv_mem (hPN (hLP hn₀L))) q).1 hq))) ?_
    rw [hcell0 _ (hg₀ g hgT), xUnit_g2ir]
    refine mul_mem (mem_sup_right ⟨_, rfl⟩) (mem_sup_left ?_)
    rw [pinnedX_r_eq_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  have hcardS' : Nat.card S' = Nat.card K - 1 := by
    rw [← hS]
    exact (Nat.card_congr (equivMapOfInjective S _ (MulAut.conj n₀⁻¹).injective).toEquiv).symm
  have hU2 : IsPGroup 2 (posUnipotent .G2 K) := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    refine IsPGroup.of_card (n := n * 6) ?_
    rw [card_posUnipotent_g2, ← Fintype.card_eq_nat_card, hn, ← pow_mul]
  have hMsolv : Group.IsSolvable M := by
    have := Fact.mk Nat.prime_two
    set U' := (posUnipotent .G2 K).subgroupOf M
    have : U'.Normal := by
      rw [normal_subgroupOf_iff_le_normalizer le_sup_left]
      exact sup_le le_normalizer hHU
    have : Group.IsNilpotent U' :=
      (Group.isNilpotent_congr (subgroupOfEquivOfLe le_sup_left)).2 hU2.isNilpotent
    have hrep : ∀ x : M, ∃ t : Kˣ, (QuotientGroup.mk x : M ⧸ U') =
        QuotientGroup.mk (⟨LieType.Chevalley.torusEltHom .G2 K g2ir t,
          mem_sup_right ⟨t, rfl⟩⟩ : M) := by
      intro x
      have hx : (x : ModGL .G2 K) ∈ ((posUnipotent .G2 K ⊔ g2TorusR K :
          Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := x.2
      rw [coe_mul_of_right_le_normalizer_left _ _ hHU] at hx
      obtain ⟨u, hu, _, ⟨t, rfl⟩, hx'⟩ := hx
      refine ⟨t, ?_⟩
      rw [QuotientGroup.eq, mem_subgroupOf]
      show (x : ModGL .G2 K)⁻¹ * LieType.Chevalley.torusEltHom .G2 K g2ir t ∈ posUnipotent .G2 K
      rw [← hx']
      have e : (u * LieType.Chevalley.torusEltHom .G2 K g2ir t)⁻¹ *
          LieType.Chevalley.torusEltHom .G2 K g2ir t =
            (LieType.Chevalley.torusEltHom .G2 K g2ir t)⁻¹ * u⁻¹ *
              (LieType.Chevalley.torusEltHom .G2 K g2ir t)⁻¹⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem (hHU ⟨t, rfl⟩)) _).1 (inv_mem hu)
    have : Group.IsSolvable (M ⧸ U') := Group.isSolvable_of_comm fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨t, ht⟩ := hrep x
      obtain ⟨t', ht'⟩ := hrep y
      have e : (⟨LieType.Chevalley.torusEltHom .G2 K g2ir t, mem_sup_right ⟨t, rfl⟩⟩ : M) *
          ⟨LieType.Chevalley.torusEltHom .G2 K g2ir t', mem_sup_right ⟨t', rfl⟩⟩ =
            ⟨LieType.Chevalley.torusEltHom .G2 K g2ir t', mem_sup_right ⟨t', rfl⟩⟩ *
              ⟨LieType.Chevalley.torusEltHom .G2 K g2ir t, mem_sup_right ⟨t, rfl⟩⟩ := by
        refine Subtype.ext ?_
        show LieType.Chevalley.torusEltHom .G2 K g2ir t *
            LieType.Chevalley.torusEltHom .G2 K g2ir t' =
          LieType.Chevalley.torusEltHom .G2 K g2ir t' * LieType.Chevalley.torusEltHom .G2 K g2ir t
        rw [← map_mul, ← map_mul, mul_comm]
      rw [ht, ht', ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, e]
    exact Group.isSolvable_of_ker_le_range U'.subtype (QuotientGroup.mk' U')
      (by rw [QuotientGroup.ker_mk', range_subtype])
  have hcardM : Nat.card M = Nat.card K ^ 6 * (Nat.card K - 1) := by
    rw [hM, card_sup_eq_mul_of_inf_eq_bot hHU hUH, card_posUnipotent_g2, card_g2TorusR]
  have hq1 : 0 < Nat.card K - 1 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  let π : Set Nat.Primes := {p | p.val ∣ Nat.card K - 1}
  have hHall : ∀ X : Subgroup (ModGL .G2 K), X ≤ M → Nat.card X = Nat.card K - 1 →
      IsHallSubgroup π (X.subgroupOf M) := by
    intro X hXM hX
    have hcX : Nat.card (X.subgroupOf M) = Nat.card K - 1 := by
      rw [← hX]
      exact Nat.card_congr (subgroupOfEquivOfLe hXM).toEquiv
    refine ⟨fun p hp => ?_, fun p hp hpπ => ?_⟩
    · rw [hcX] at hp
      exact hp
    · have hidx : (X.subgroupOf M).index = Nat.card K ^ 6 := by
        have h := (X.subgroupOf M).card_mul_index
        rw [hcX, hcardM, mul_comm (Nat.card K ^ 6)] at h
        exact Nat.eq_of_mul_eq_mul_left hq1 h
      rw [hidx] at hp
      have hpq : p.val ∣ Nat.card K := p.2.dvd_of_dvd_pow hp
      have hpq1 : p.val ∣ Nat.card K - 1 := hpπ
      have h1 : p.val ∣ 1 := by
        have h := Nat.dvd_sub hpq hpq1
        rwa [Nat.sub_sub_self (by omega)] at h
      exact p.2.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨m, hm⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hMsolv
    (hHall (g2TorusR K) le_sup_right (card_g2TorusR)) (hHall S' hS'M hcardS')
  have hS'eq : S' = (g2TorusR K).map (MulAut.conj (m : ModGL .G2 K)).toMonoidHom := by
    have h : (S'.subgroupOf M).map M.subtype =
        (((g2TorusR K).subgroupOf M).map (MulAut.conj m).toMonoidHom).map M.subtype := by
      rw [hm]
    rw [subgroupOf_map_subtype, inf_of_le_left hS'M,
      map_subgroupOf_map_conj_eq le_sup_right m] at h
    exact h
  have hconj : ∀ (a b : ModGL .G2 K) (X : Subgroup (ModGL .G2 K)),
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        X.map (MulAut.conj (a * b)).toMonoidHom := by
    intro a b X
    rw [map_map]
    congr 1
  refine ⟨n₀ * m, mul_mem (hLP hn₀L) (hMP m.2), ?_⟩
  rw [← hconj, ← hS'eq, hS', hconj, mul_inv_cancel]
  ext x
  simp

theorem g2TorusConj
    : G2TorusConj := fun _ _ _ _ _ _ hSP hS =>
  exists_conj_g2TorusR hSP hS

end TorusConj

end CFSG.ComponentClassification.RankTwoExceptional
