module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceAltSeven
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceCycle
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceGlue
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReducePSL
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTypes

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial LinearFlag

namespace ToralReduce

theorem mem_zpowers_of_card_le_three {X : Type*} [Group X] {P : Subgroup X} {u v : X}
    (hu : u ∈ P) (hv : v ∈ P) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hv3 : v ^ 3 = 1)
    (hc : v * u = u * v)
    (hP : ∀ Q : Subgroup X, Q ≤ P → IsPGroup 3 Q → Nat.card Q ≤ 3) :
    v ∈ Subgroup.zpowers u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hvu
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hE : BlockCyc.HasE9 ↥P := by
    refine BlockCyc.hasE9_of_two_elements (e₁ := ⟨u, hu⟩) (e₂ := ⟨v, hv⟩)
      (Subtype.ext hc.symm) (Subtype.ext hu3) (Subtype.ext hv3) fun i j hi hj h => ?_
    have h' : u ^ i * v ^ j = 1 := by simpa using congrArg Subtype.val h
    interval_cases j
    · rw [pow_zero, mul_one] at h'
      have := orderOf_dvd_of_pow_eq_one h'
      rw [hou] at this
      exact ⟨by interval_cases i <;> simp_all, rfl⟩
    · exfalso
      apply hvu
      rw [pow_one] at h'
      rw [eq_inv_of_mul_eq_one_right h']
      exact (Subgroup.zpowers u).inv_mem (Subgroup.npow_mem_zpowers u i)
    · exfalso
      apply hvu
      have hv2 : v ^ 2 = (u ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h'
      have hvv : v = (v ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hv3, one_mul]
      rw [hvv, hv2]
      exact (Subgroup.zpowers u).pow_mem ((Subgroup.zpowers u).inv_mem
        (Subgroup.npow_mem_zpowers u i)) 2
  obtain ⟨E, hEel, hEc⟩ := hE
  have h := hP (E.map P.subtype) (Subgroup.map_subtype_le _)
    (IsPGroup.of_card (n := 2) (by rw [Subgroup.card_map_of_injective P.subtype_injective, hEc]))
  rw [Subgroup.card_map_of_injective P.subtype_injective, hEc] at h
  norm_num at h

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_center {M L : Subgroup G}
    (hζ : ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      ζ ^ 3 = 1 → ζ = 1) : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hzC : ((z : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨k, hk⟩)
  have hz3 : ((z : ↥(barM M L)) : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg (fun w : Subgroup.center ↥(barM M L) => ((w : ↥(barM M L)) :
      ↥M ⧸ CFSG.pCore 2 ↥M)) this
  have h1 := hζ _ (z : ↥(barM M L)).2 hzC hz3
  have : z = 1 := Subtype.ext (Subtype.ext h1)
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem mem_zpowers_of_cyc_two (hC : KFactFixCensusThree) (hG : GlueVhyp) {M S L : Subgroup G}
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h2 : NineThreeTwo M S L) (hcyc : CycPerfect 3 (blockPL M S L))
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L))) {u : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hu : u ∈ barM M L) (hu3 : u ^ 3 = 1)
    (huC : u ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (barM M (S ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ u ∈ V)
    (hfix : ∀ l ∈ barM M L, u * l * u⁻¹ = l → l ∈ blockPL M S L)
    {v : ↥M ⧸ CFSG.pCore 2 ↥M} (hv : v ∈ barM M L) (hv3 : v ^ 3 = 1) (hvu : v * u = u * v) :
    v ∈ Subgroup.zpowers u := by
  obtain ⟨hCP, hjoin, e, -, ⟨φ⟩⟩ :=
    exists_census_of_nineThreeTwo hC hG hA hL hS h2 hcyc hu hu3 huC hV hfix
  by_cases hK3 : 3 ∣ Nat.card (GaloisField 2 e) - 1
  · obtain ⟨ω, hω1, hω3⟩ := exists_cube_root_of_dvd hK3
    exact (false_of_fix_of_cube_root hCP φ hω1 hω3 hZ3 hu hu3 huC hjoin hfix).elim
  · have h3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3
    have hu3' : (⟨u, hu⟩ : ↥(barM M L)) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    have hv3' : (⟨v, hv⟩ : ↥(barM M L)) ^ 3 = 1 := Subtype.ext (by simpa using hv3)
    have hx1 : censusHom φ ⟨u, hu⟩ ≠ 1 := by
      intro h1
      apply huC
      rw [censusHom_eq_one_iff] at h1
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨l, hl⟩)
    have hz := mem_zpowers_of_commute_of_not_dvd hK3 (x := censusHom φ ⟨u, hu⟩)
      (y := censusHom φ ⟨v, hv⟩) (by rw [← map_pow, hu3', map_one]) hx1
      (by rw [← map_pow, hv3', map_one])
      (by rw [← map_mul, ← map_mul]; congr 1; exact Subtype.ext hvu.symm)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← map_zpow] at hk
    have heq := eq_of_censusHom_eq_of_pow φ h3 (a := ⟨u, hu⟩ ^ k) (b := ⟨v, hv⟩)
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3', one_zpow])
      hv3' hk
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val heq
    simpa using this

end ToralReduce

open ToralReduce in
theorem citedBlockToralThreeCyc_of_census (hC : KFactFixCensusThree) (hG : GlueVhyp)
    (hTPLT : CitedBlockTransvectionPLType) (h86 : Asc81bEightSix) : CitedBlockToralThreeCyc := by
  intro G _ _ M S L hK hA hL h93 hX hS hcyc hζ u hu hu3 huC hV hfix v hv hv3 hvu
  have hTPL := citedBlockTransvectionPL_of_type hTPLT
  have hZ3 := not_three_dvd_card_center hζ
  have huP : u ∈ blockPL M S L := hfix u hu (by rw [mul_inv_cancel_right])
  have hvP : v ∈ blockPL M S L := hfix v hv (by rw [← hvu, mul_inv_cancel_right])
  have hu1 : u ≠ 1 := fun h => huC (h ▸ Subgroup.one_mem _)
  obtain ⟨V, hVp, hVL, hVSL, hVS, huV⟩ := hV
  have hrest : NineThreeThree M S L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L → v ∈ Subgroup.zpowers u := fun h =>
    mem_zpowers_of_card_le_three huP hvP hu3 hu1 hv3 hvu fun Q hQ hQ3 =>
      card_le_three_of_cyc_rest hTPL hK hA hL hX hS h hcyc hQ hQ3
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (hX h1).elim
  · exact mem_zpowers_of_cyc_two hC hG hA hL hS h2 hcyc hZ3 hu hu3 huC
      ⟨V, hVp, hVL, hVSL, huV⟩ hfix hv hv3 hvu
  · exact hrest (Or.inl h3)
  · exact (hZ3 (by rw [h4.2.1])).elim
  · exact (false_of_nineThreeFive h86 hK hA hL h5 hVp hVL hVS huC huV).elim
  · exact hrest (Or.inr (Or.inl h6))
  · exact hrest (Or.inr (Or.inr (Or.inl h7)))
  · exact hrest (Or.inr (Or.inr (Or.inr h8)))

end CFSG.AGLEmbedding
