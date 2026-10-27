module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SplitSylow
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SplitOrder

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree


variable {K : Type} [Field K] [Finite K]

theorem card_le_of_isPGroup_fixed_gammaP (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K)
    {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) {ζ : Kˣ}
    (hζ : orderOf ζ = 3 ^ (Nat.card K - 1).factorization 3) {R : Subgroup ↥(adjointGroup Tag.D4 K)}
    (hR : IsPGroup 3 R) (hRα : ∀ x ∈ R, gammaP K (HSL ω) x = x) :
    Nat.card R ≤ 3 * Nat.card (Subgroup.zpowers ζ) ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e := (Nat.card K - 1).factorization 3 with he
  set μ := Subgroup.zpowers ζ with hμ
  have hμsq : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hcardT : Nat.card (torusSub (K := K) μ) = (3 ^ e) ^ 4 := by
    rw [card_torusSub μ hμsq, hcardμ]
  have hcardS : Nat.card (S1 (K := K) hω3 μ) = 3 ^ (4 * e + 1) := by
    rw [card_S1 hω3 hω μ, hcardT, ← pow_mul, pow_succ, mul_comm e 4]
  have hSsyl : Nat.card (S1 (K := K) hω3 μ) =
      3 ^ (Nat.card ↥(adjointGroup Tag.D4 K)).factorization 3 := by
    rw [hcardS]
    congr 1
    refine le_antisymm ?_ ?_
    · have hdvd : 3 ^ (4 * e + 1) ∣ Nat.card ↥(adjointGroup Tag.D4 K) := by
        rw [← hcardS]
        exact Subgroup.card_subgroup_dvd_card _
      exact (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
    · exact factorization_card_D4_le hq
  have hTS : (torusSub (K := K) μ).relIndex (S1 hω3 μ) = 3 := by
    have h := Subgroup.relIndex_mul_card (H := torusSub (K := K) μ) (K := S1 hω3 μ)
    rw [inf_eq_left.2 (show torusSub (K := K) μ ≤ S1 hω3 μ from le_sup_left),
      card_S1 hω3 hω μ] at h
    have hT0 : Nat.card (torusSub (K := K) μ) ≠ 0 := Nat.card_pos.ne'
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hT0) (h.trans (mul_comm _ _))
  exact card_le_of_isPGroup_of_fixed conj_injective_adj
    (gammaP_pow_three (HSL_pow_three hω3)) (gammaP_HSL_not_inner hω (by omega)) hSsyl
    (fun x hx => gammaP_HSL_mem_S1 hω3 μ hx) hTS.le (by rw [hTS]; norm_num)
    (fun s hs j hj hj3 F hF hfix => card_fixed_le hω3 μ hs hj hj3 hF hfix) hR hRα

theorem exists_conj_mem_Q0 (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K) {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hω : orderOf ω = 3) {ζ : Kˣ}
    (hζ : orderOf ζ = 3 ^ (Nat.card K - 1).factorization 3) {x : ↥(adjointGroup Tag.D4 K)}
    (hx : gammaP K (HSL ω) x = x) (hx3 : x ^ 3 = 1) :
    ∃ c : ↥(adjointGroup Tag.D4 K), gammaP K (HSL ω) c = c ∧
      c⁻¹ * x * c ∈ Q0 hω3 (Subgroup.zpowers ζ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set μ := Subgroup.zpowers ζ with hμ
  set C := fixedSubgroup (gammaP K (HSL ω)) with hC
  set e := (Nat.card K - 1).factorization 3 with he
  have hμsq : ∀ u ∈ μ, ∃ b : Kˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hQge : 3 * Nat.card μ ^ 2 ≤ Nat.card (Q0 (K := K) hω3 μ) := by
    rw [card_Q0 hω3 hω μ, mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge μ hμsq)
  have hQp : IsPGroup 3 (Q0 (K := K) hω3 μ) := by
    have hdvdT : Nat.card (T3fix (ω := ω) (K := K) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : T3fix (ω := ω) (K := K) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [card_Q0 hω3 hω μ, pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  have hbound : ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R → R ≤ C →
      Nat.card R ≤ 3 * Nat.card μ ^ 2 := fun R hR hRC =>
    card_le_of_isPGroup_fixed_gammaP hq hK4 hω3 hω hζ hR (fun y hy => hRC hy)
  have hQC : Q0 (K := K) hω3 μ ≤ C := Q0_le_fixed hω3 μ
  have hQsyl : Nat.card ((Q0 (K := K) hω3 μ).subgroupOf C) = 3 ^ (Nat.card C).factorization 3 := by
    rw [card_subgroupOf_of_le hQC]
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 C))
    have hP := Sylow.card_eq_multiplicity P
    refine le_antisymm ?_ ?_
    · have hQp' : IsPGroup 3 ((Q0 (K := K) hω3 μ).subgroupOf C) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
        exact IsPGroup.of_card (n := n) (by rw [card_subgroupOf_of_le hQC, hn])
      obtain ⟨P', hP'⟩ := hQp'.exists_le_sylow
      have h1 := Subgroup.card_le_of_le hP'
      rw [card_subgroupOf_of_le hQC, Sylow.card_eq_multiplicity] at h1
      exact h1
    · have hR : IsPGroup 3 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map _
      have h2 := hbound _ hR (Subgroup.map_subtype_le _)
      rw [← hP]
      calc Nat.card (P : Subgroup C) = Nat.card ((P : Subgroup C).map C.subtype) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv)
        _ ≤ 3 * Nat.card μ ^ 2 := h2
        _ ≤ Nat.card (Q0 (K := K) hω3 μ) := hQge
  have hxC : x ∈ C := hx
  have hxp : IsPGroup 3 (Subgroup.zpowers (⟨x, hxC⟩ : C)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx3))
  obtain ⟨P, hP⟩ := hxp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (Sylow.ofCard _ hQsyl) P
  have hxP : (⟨x, hxC⟩ : C) ∈ (P : Subgroup C) := hP (Subgroup.mem_zpowers _)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hxP
  simp only [MulAut.smul_def, map_inv, MulAut.conj_inv_apply] at hxP
  refine ⟨c, c.2, ?_⟩
  simpa [mul_assoc] using hxP

theorem exists_pow_four_ne_one (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K) :
    ∃ l : Kˣ, l ^ 4 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨g, fun h4 => ?_⟩
  have hdvd := orderOf_dvd_of_pow_eq_one h4
  rw [hg, card_units_K] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card K - 1 <;> omega

theorem pairGenAt_gammaP_HSL (hq : Nat.card K % 3 = 1) (hK4 : 4 ≤ Nat.card K) {ω : Kˣ}
    (hω : orderOf ω = 3) : PairGenAt (gammaP K (HSL ω)) := by
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K)
  obtain ⟨l, hl⟩ := exists_pow_four_ne_one hq hK4
  intro x hx3 _ hαx
  obtain ⟨c, hcα, hcQ⟩ := exists_conj_mem_Q0 hq hK4 hω3 hω hζ hαx hx3
  have hcα' : gammaP K (HSL ω) c⁻¹ = c⁻¹ := by rw [map_inv, hcα]
  refine closure_eq_top_of_conj hcα' ?_
  rw [inv_inv, eq_top_iff, ← closure_fixedSubgroup_gammaP_HSL_torus hω3 hl]
  refine Subgroup.closure_mono ?_
  rintro y (hy | hy)
  · exact Or.inr hy
  · left
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := Q0_le_centralizer hω3 (Subgroup.zpowers ζ) l hcQ
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact h.symm

theorem conj_gammaP (P B : SL2 K) :
    MulAut.conj (sl2At K ⟨2, by decide⟩ P) * gammaP K B *
        (MulAut.conj (sl2At K ⟨2, by decide⟩ P))⁻¹ =
      gammaP K (P * B * P⁻¹) := by
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, gammaP, gammaP, MulAut.mul_apply, MulAut.mul_apply,
    MulAut.conj_inv_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
    map_mul, map_inv, d4Graph_one_sl2Two, map_mul, map_mul, map_inv]
  group

theorem d4GraphA2PairGenSplit_holds : D4GraphA2PairGenSplit := by
  intro K _ _ hq hK4 B hB3 hB1
  have h3 : 3 ∣ Nat.card K - 1 := by have := Nat.card_pos (α := K); omega
  obtain ⟨P, t, hP⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3 B
    ⟨1, by simpa using hB3⟩
  have ht3 : t ^ 3 = 1 := by
    have h : HSL t ^ 3 = 1 := by rw [← hP, conj_pow, hB3]; group
    apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective
    rw [map_pow, map_one]
    exact h
  have ht1 : t ≠ 1 := by
    intro h1
    apply hB1
    have h : HSL t = 1 := by
      rw [h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL]
    have := congrArg (fun A => P⁻¹ * A * P) (hP.trans h)
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  refine pairGenAt_of_conj_eq (MulAut.conj (sl2At K ⟨2, by decide⟩ P))
    (pairGenAt_gammaP_HSL hq hK4 ht) (Or.inl ?_)
  rw [conj_gammaP, hP]

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
