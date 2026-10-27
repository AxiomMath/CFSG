module

public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalKleinFourIndexThree
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

namespace AscEightFour

section Elements

theorem sl2_two (F : Type) [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) :
    ∃ t : Matrix.SpecialLinearGroup (Fin 2) F, t ^ 2 = 1 ∧ t ≠ 1 := by
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at h
    exact (pow_eq_zero_iff (by omega)).mp h
  have hdet : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two]
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨(!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F), hdet⟩
  refine ⟨t, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]
  · intro h
    have := congrArg
      (fun t : Matrix.SpecialLinearGroup (Fin 2) F => (t : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [t] at this

theorem alt_two {m : ℕ} (hm : 4 ≤ m) : ∃ t : alternatingGroup (Fin m), t ^ 2 = 1 ∧ t ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hdvd : 2 ∣ Nat.card (alternatingGroup (Fin m)) := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    apply Nat.dvd_div_of_mul_dvd
    exact (show 2 * 2 ∣ Nat.factorial 4 by decide).trans (Nat.factorial_dvd_factorial hm)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨t, ?_, ?_⟩
  · rw [← ht]
    exact pow_orderOf_eq_one t
  · rintro rfl
    simp at ht

end Elements

section A4

variable {G : Type} [Group G] [Finite G]

theorem mem_of_centralizes_aux {L U : Subgroup G} (hU4 : Nat.card U = 4)
    (hUab : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {c : G} (hc3 : orderOf c = 3)
    (hcN : c ∈ Subgroup.normalizer (U : Set G)) (hcfp : ∀ u ∈ U, u ≠ 1 → c * u * c⁻¹ ≠ u)
    (hLc : L = U ⊔ Subgroup.zpowers c) {l : G} (hl : l ∈ L) (hc : ∀ u ∈ U, l * u = u * l) :
    l ∈ U := by
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨u₀, hu₀U, hu₀1⟩ : ∃ u₀ ∈ U, u₀ ≠ 1 := by
    by_contra hcon
    have hle : U ≤ ⊥ := fun u hu => by
      rw [Subgroup.mem_bot]
      by_contra h'
      exact hcon ⟨u, hu, h'⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hU4, Subgroup.card_bot] at h1
    omega
  have hlmem : l ∈ ((Subgroup.zpowers c ⊔ U : Subgroup G) : Set G) := by
    have : l ∈ Subgroup.zpowers c ⊔ U := by rw [sup_comm, ← hLc]; exact hl
    exact this
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) U
    (Subgroup.zpowers_le.mpr hcN)] at hlmem
  obtain ⟨y, hy, u', hu', hyu0⟩ := hlmem
  have hyu : y * u' = l := hyu0
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hck : ∀ u ∈ U, c ^ k * u = u * c ^ k := by
    intro u hu
    have h1 := hc u hu
    have h2 : u'⁻¹ * u = u * u'⁻¹ := hUab u'⁻¹ (inv_mem hu') u hu
    calc c ^ k * u = (c ^ k * u') * (u'⁻¹ * u) := by group
      _ = l * (u * u'⁻¹) := by rw [hyu, h2]
      _ = (l * u) * u'⁻¹ := by group
      _ = (u * l) * u'⁻¹ := by rw [h1]
      _ = u * (c ^ k * u' * u'⁻¹) := by rw [← hyu]; group
      _ = u * c ^ k := by group
  have hk : c ^ k = c ^ (k % 3) := by
    have := zpow_mod_orderOf c k
    rw [hc3] at this
    simpa using this.symm
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h0 | h0
  · have : c ^ k = 1 := by rw [hk, h0, zpow_zero]
    rw [← hyu, this, one_mul]
    exact hu'
  · exfalso
    have hcc : c * u₀ = u₀ * c := by
      have := hck u₀ hu₀U
      rwa [hk, h0, zpow_one] at this
    apply hcfp u₀ hu₀U hu₀1
    calc c * u₀ * c⁻¹ = u₀ * c * c⁻¹ := by rw [hcc]
      _ = u₀ := by group
  · exfalso
    have hcc2 : c ^ 2 * u₀ = u₀ * c ^ 2 := by
      have := hck u₀ hu₀U
      rw [hk, h0] at this
      simpa [zpow_two, pow_two] using this
    have hc4 : c = c ^ 2 * c ^ 2 := by
      calc c = c * c ^ 3 := by rw [hc3', mul_one]
        _ = c ^ 2 * c ^ 2 := by group
    apply hcfp u₀ hu₀U hu₀1
    have hcc : c * u₀ = u₀ * c := by
      calc c * u₀ = (c ^ 2 * c ^ 2) * u₀ := by rw [← hc4]
        _ = c ^ 2 * (c ^ 2 * u₀) := by group
        _ = c ^ 2 * (u₀ * c ^ 2) := by rw [hcc2]
        _ = (c ^ 2 * u₀) * c ^ 2 := by group
        _ = (u₀ * c ^ 2) * c ^ 2 := by rw [hcc2]
        _ = u₀ * (c ^ 2 * c ^ 2) := by group
        _ = u₀ * c := by rw [← hc4]
    calc c * u₀ * c⁻¹ = u₀ * c * c⁻¹ := by rw [hcc]
      _ = u₀ := by group

theorem nonempty_mulEquiv_A4 {B : Subgroup G} (hs : IsShort2 B) (ha : IsAltType B 3) :
    Nonempty (↥B ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨-, hU4, hU2, hUab, hB12, -, c, -, hc3, hcN, hcfp, hBc⟩ := hs.alt3_structure ha
  set U := blockU B with hU
  have hUB : U ≤ B := by rw [hBc]; exact le_sup_left
  have hBN : B ≤ Subgroup.normalizer (U : Set G) := by
    rw [hBc]; exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hcN)
  have hcard : Nat.card ↥(U.subgroupOf B) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv]
    exact hU4
  have hnormal : (U.subgroupOf B).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hUB).mpr fun u k hu hk => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hBN hk) u).mp hu
  have hKlein : IsKleinFour ↥(U.subgroupOf B) := by
    have hnt : Nontrivial ↥(U.subgroupOf B) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    refine ⟨hcard, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    apply Subtype.ext
    apply Subtype.ext
    simpa using hU2 (((g : ↥B)) : G) g.2
  have hcentr : Subgroup.centralizer ((U.subgroupOf B : Subgroup ↥B) : Set ↥B) =
      U.subgroupOf B := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      refine Subgroup.mem_subgroupOf.mpr
        (mem_of_centralizes_aux hU4 hUab hc3 hcN hcfp hBc x.2 fun u hu => ?_)
      have := hx ⟨u, hUB hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      exact (congrArg Subtype.val this).symm
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext
        (hUab _ (Subgroup.mem_subgroupOf.mp hy) _ (Subgroup.mem_subgroupOf.mp hx))
  have hindex : (U.subgroupOf B).index = 3 := by
    have := (U.subgroupOf B).card_mul_index
    rw [hcard, hB12] at this
    omega
  exact CFSG.GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    _ hnormal hKlein hcentr hindex

end A4

end AscEightFour

open AscEightFour in
theorem asc81bEightFour_of_cgtBlock (hCGT : AschbacherLocalCGTBlock) : Asc81bEightFour := by
  intro G _ _ X S hK hyp
  by_cases hc : cgsIn (hGrp X S) S = hGrp X S
  · left
    exact oddBar_le_centralizer hyp (hc.symm.le.trans (cgsIn_hGrp_le hyp))
  · right
    obtain ⟨B, hBH, hBsn, ⟨hs, htype⟩, -⟩ := hCGT G (hGrp X S) S (isKGroup_mono hK hGrp_le)
      (charTwo_hGrp hyp) (isSylowTwoOf_hGrp hyp) hc
    have hBP := le_pGrp_of_short hyp hBH hs
    have h2 : ∀ b : ↥B, ∀ k : ℕ, (b : G) ^ 2 ^ k = 1 → (b : G) ∈ pCoreOf 2 B :=
      fun b k hk => mem_blockQ_of_pow hBP b.2 hk
    refine ⟨B, hBP.trans pGrp_le, ?_, ?_⟩
    · have h1 := isSubnormal_inf hBsn (pGrp X)
      rw [inf_eq_left.mpr hBP, inf_eq_right.mpr pGrp_le_hGrp] at h1
      exact isSubnormal_trans_normal h1 pGrp_le pGrp_normal
    · rcases htype with ⟨n, hn, hlin⟩ | ⟨n, hn, halt⟩
      · exfalso
        obtain ⟨F, _, _, hcard, α, hαs, hαk, -⟩ := hlin
        obtain ⟨t, ht2, ht1⟩ := sl2_two F hn hcard
        exact false_of_two_element α hαs hαk h2 ht2 ht1
      · rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
        · exact nonempty_mulEquiv_A4 hs halt
        · exfalso
          obtain ⟨α, hαs, hαk, -⟩ := halt
          obtain ⟨t, ht2, ht1⟩ := alt_two (m := 2 * n + 1) (by omega)
          exact false_of_two_element α hαs hαk h2 ht2 ht1

theorem asc81bEightFour_of_factorization
    (h : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization) : Asc81bEightFour :=
  asc81bEightFour_of_cgtBlock (aschbacherLocalCGTBlock_of_factorization h)


end CFSG.AGLEmbedding
