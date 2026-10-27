module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269SGrp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6Comp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Polynomial CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6
open scoped commutatorElement

variable {K : Type} [Field K]

theorem i269s_X2K_ne_sub_one [Finite K] (hK : Nat.card K = 2) : (X2K : K[X]) ≠ X - 1 := by
  intro h
  have hdeg : (X2K : K[X]).natDegree = 2 := by unfold X2K; compute_degree!
  have h1 : (X - 1 : K[X]).natDegree = 1 := by compute_degree!
  have h2 := congrArg Polynomial.natDegree h
  rw [hdeg, h1] at h2
  omega

theorem i269s_singleton_mem [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K} (hx : x ^ 3 = 1)
    {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) :
    ({h} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
  ⟨h, hh, reciprocalOrbit_singleton hK x hx hh⟩

theorem i269s_rank_data [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K} (hx : x ^ 3 = 1)
    (hx1 : x ≠ 1) (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x)) :
    (X2K : K[X]) ∈ primaryFactors (spEnd x) ∧ ∃ s : ℕ, spFixedDim x = 2 * s ∧
      3 = s + primaryMultiplicity (spEnd x) (X2K : K[X]) := by
  classical
  obtain ⟨s, hs, -, hrank⟩ := blocks.rank
  have hdeg : (X2K : K[X]).natDegree = 2 := by unfold X2K; compute_degree!
  have hIRT : IsReciprocalTransversal (spEnd x) ∅ := by
    refine ⟨by simp, fun h hh hne => ?_, by simp⟩
    exact (hne (reciprocal_of_primaryFactor hK x hx hh).symm).elim
  have heq := hrank ∅ hIRT
  rw [Finset.sum_empty, add_zero] at heq
  have hfs : ((primaryFactors (spEnd x)).filter (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1))
      ⊆ {(X2K : K[X])} := by
    intro h hh
    rw [Finset.mem_filter] at hh
    rcases primaryFactor_cases hK x hx hh.1 with h1 | h1
    · exact absurd h1 hh.2.2
    · rw [Finset.mem_singleton]; exact h1
  by_cases hX2 : (X2K : K[X]) ∈ primaryFactors (spEnd x)
  · have hfilt : ((primaryFactors (spEnd x)).filter
        (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1)) = {(X2K : K[X])} := by
      apply Finset.Subset.antisymm hfs
      intro h hh
      rw [Finset.mem_singleton] at hh
      subst hh
      exact Finset.mem_filter.2 ⟨hX2, reciprocal_X2K, i269s_X2K_ne_sub_one hK⟩
    rw [hfilt, Finset.sum_singleton, hdeg] at heq
    exact ⟨hX2, s, hs, by simpa using heq⟩
  · exfalso
    have hempty : ((primaryFactors (spEnd x)).filter
        (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1)) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro h hh
      have h1 := hfs hh
      rw [Finset.mem_singleton] at h1
      subst h1
      exact hX2 (Finset.mem_filter.1 hh).1
    rw [hempty, Finset.sum_empty, add_zero] at heq
    have h6 : Module.finrank K (primaryComponent (spEnd x) (X - 1 : K[X])) = 6 := by
      omega
    exact hx1 (eq_one_of_fixed_finrank_six hK x h6)

theorem i269s_x_mem_H [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K} (hx : x ^ 3 = 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x)) :
    x ∈ spSupported x ({(X2K : K[X])} : Set K[X]) := by
  rw [mem_spSupported]
  refine ⟨rfl, fun k hk hkO v hv => ?_⟩
  rcases primaryFactor_cases hK x hx hk with h1 | h1
  · subst h1
    have hv' : v ∈ LinearMap.ker (spEnd x - 1) := by
      rw [← blocks.fixed_eq]
      exact hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv'
    exact hv'
  · exact absurd (by rw [h1]; exact Set.mem_singleton _) hkO

theorem i269s_card_H [Finite K] (hK : Nat.card K = 2) {x : StatedSp 3 K} (hx : x ^ 3 = 1)
    (blocks : SpPrimaryBlocks 2 1 3 x (proj 3 K x)) (hmem : (X2K : K[X]) ∈ primaryFactors (spEnd x))
    (hm1 : primaryMultiplicity (spEnd x) (X2K : K[X]) = 1) :
    Nat.card ↥(spSupported x ({(X2K : K[X])} : Set K[X])) = 3 := by
  haveI : Fact (Irreducible (X2K : K[X])) := ⟨X2K_irreducible hK⟩
  have hne : (X2K : K[X]) ≠ X - 1 := i269s_X2K_ne_sub_one hK
  obtain ⟨d, hd2, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
    (blocks.selfDual ⟨X2K, hmem⟩ hne reciprocal_X2K).exists_half
  have hd1 : d = 1 := by
    have : (X2K : K[X]).natDegree = 2 * d := hd2
    have hdeg : (X2K : K[X]).natDegree = 2 := by unfold X2K; compute_degree!
    omega
  subst hd1
  have hcardφ : Nat.card ↥(spSupported x ({(X2K : K[X])} : Set K[X])) =
      Nat.card ↥(sesqUnitaryGroup Hf) := Nat.card_congr φ.toEquiv
  have hc := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := primaryMultiplicity (spEnd x) (X2K : K[X])) rfl (by omega)).1
  rw [hm1] at hc
  rw [hcardφ]
  norm_num [Finset.Icc_self] at hc
  exact_mod_cast hc

theorem i269s_mem_sup_of_commute {G : Type} [Group G] {F H : Subgroup G}
    (hc : ∀ a ∈ F, ∀ b ∈ H, a * b = b * a) {g : G} (hg : g ∈ F ⊔ H) :
    ∃ a ∈ F, ∃ b ∈ H, g = a * b := by
  let S : Subgroup G :=
    { carrier := {g | ∃ a ∈ F, ∃ b ∈ H, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', F.mul_mem ha ha', b * b', H.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
          _ = a * (a' * b) * b' := by rw [hc a' ha' b hb]
          _ = a * a' * (b * b') := by simp only [mul_assoc]
      one_mem' := ⟨1, F.one_mem, 1, H.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, F.inv_mem ha, b⁻¹, H.inv_mem hb, ?_⟩
        rw [mul_inv_rev, hc a⁻¹ (F.inv_mem ha) b⁻¹ (H.inv_mem hb)] }
  have hle : F ⊔ H ≤ S := sup_le (fun a ha => ⟨a, ha, 1, H.one_mem, by simp⟩)
    (fun b hb => ⟨1, F.one_mem, b, hb, by simp⟩)
  obtain ⟨a, ha, b, hb, hgab⟩ := hle hg
  exact ⟨a, ha, b, hb, hgab⟩

theorem i269s_comm_fst {G : Type} [Group G] {F H : Subgroup G}
    (hc : ∀ a ∈ F, ∀ b ∈ H, a * b = b * a) (hdisj : F ⊓ H = ⊥)
    {a b c d : G} (ha : a ∈ F) (hb : b ∈ H) (hcF : c ∈ F) (hd : d ∈ H)
    (hcomm : (a * b) * (c * d) = (c * d) * (a * b)) : a * c = c * a := by
  have hbc : b * c = c * b := (hc c hcF b hb).symm
  have hda : d * a = a * d := (hc a ha d hd).symm
  have h1 : a * c * (b * d) = c * a * (d * b) := by
    calc a * c * (b * d) = a * (c * b) * d := by simp only [mul_assoc]
      _ = a * (b * c) * d := by rw [hbc]
      _ = (a * b) * (c * d) := by simp only [mul_assoc]
      _ = (c * d) * (a * b) := hcomm
      _ = c * (d * a) * b := by simp only [mul_assoc]
      _ = c * (a * d) * b := by rw [hda]
      _ = c * a * (d * b) := by simp only [mul_assoc]
  have hz : (c * a)⁻¹ * (a * c) = (d * b) * (b * d)⁻¹ := by
    calc (c * a)⁻¹ * (a * c) = (c * a)⁻¹ * (a * c * (b * d)) * (b * d)⁻¹ := by group
      _ = (c * a)⁻¹ * (c * a * (d * b)) * (b * d)⁻¹ := by rw [h1]
      _ = (d * b) * (b * d)⁻¹ := by group
  have hzF : (c * a)⁻¹ * (a * c) ∈ F :=
    F.mul_mem (F.inv_mem (F.mul_mem hcF ha)) (F.mul_mem ha hcF)
  have hzH : (c * a)⁻¹ * (a * c) ∈ H := by
    rw [hz]
    exact H.mul_mem (H.mul_mem hd hb) (H.inv_mem (H.mul_mem hb hd))
  have hz1 : (c * a)⁻¹ * (a * c) = 1 := by
    have hmem : (c * a)⁻¹ * (a * c) ∈ F ⊓ H := ⟨hzF, hzH⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact (inv_mul_eq_one.1 hz1).symm

theorem i269s_cube_fst {G : Type} [Group G] {F H : Subgroup G}
    (hc : ∀ a ∈ F, ∀ b ∈ H, a * b = b * a) (hdisj : F ⊓ H = ⊥)
    {c d : G} (hcF : c ∈ F) (hd : d ∈ H) (h3 : (c * d) ^ 3 = 1) : c ^ 3 = 1 := by
  have hcd : Commute c d := hc c hcF d hd
  have hpow : c ^ 3 * d ^ 3 = 1 := by rw [← hcd.mul_pow]; exact h3
  have hmemF : c ^ 3 ∈ F := F.pow_mem hcF 3
  have hmemH : c ^ 3 ∈ H := by
    have h4 : c ^ 3 = (d ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [h4]
    exact H.inv_mem (H.pow_mem hd 3)
  have hmem : c ^ 3 ∈ F ⊓ H := ⟨hmemF, hmemH⟩
  rw [hdisj] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem i269s_pair_solvable [Finite K] (hK : Nat.card K = 2) {x y : StatedSp 3 K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hxy : Commute x y)
    (hyx : y ∉ Subgroup.zpowers x) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (StatedSp 3 K)) ⊓
      Subgroup.centralizer ({y} : Set (StatedSp 3 K))) := by
  classical
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hordp : orderOf (proj 3 K x) = 3 := by
    rw [orderOf_injective (proj 3 K) (proj_injective_of_card_two hK) x, hord]
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks (r := 3) Nat.prime_two le_rfl hK'
    Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (proj 3 K x) hordp).2 x rfl hord
  obtain ⟨hX2, s, hs, hm⟩ := i269s_rank_data hK hx3 hx1 blocks
  have hsolvH : Group.IsSolvable ↥(spSupported x ({(X2K : K[X])} : Set K[X])) :=
    selfDual_solvable hK blocks hX2
  have hxH : x ∈ spSupported x ({(X2K : K[X])} : Set K[X]) := i269s_x_mem_H hK hx3 blocks
  have hyC : y ∈ Subgroup.centralizer ({x} : Set (StatedSp 3 K)) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hxy
  by_cases hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)
  · have hO1 : ({(X - 1 : K[X])} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
      i269s_singleton_mem hK hx3 hX1
    have hO2 : ({(X2K : K[X])} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
      i269s_singleton_mem hK hx3 hX2
    have hne : ({(X - 1 : K[X])} : Set K[X]) ≠ {(X2K : K[X])} := by
      intro h
      exact i269s_X2K_ne_sub_one hK (Set.singleton_injective h).symm
    have hcomm : ∀ a ∈ spSupported x ({(X - 1 : K[X])} : Set K[X]),
        ∀ b ∈ spSupported x ({(X2K : K[X])} : Set K[X]), a * b = b * a :=
      fun a ha b hb => blocks.directProduct.1 _ hO1 _ hO2 hne a ha b hb
    have hdisj : spSupported x ({(X - 1 : K[X])} : Set K[X]) ⊓
        spSupported x ({(X2K : K[X])} : Set K[X]) = ⊥ := by
      have hne' : (⟨_, hO1⟩ : ↥(reciprocalOrbits (spEnd x))) ≠ ⟨_, hO2⟩ :=
        fun h => hne (congrArg Subtype.val h)
      exact disjoint_iff.1 (blocks.directProduct.2.1.pairwiseDisjoint hne')
    have hcover : Subgroup.centralizer ({x} : Set (StatedSp 3 K)) ≤
        spSupported x ({(X - 1 : K[X])} : Set K[X]) ⊔ spSupported x ({(X2K : K[X])} : Set K[X]) := by
      rw [← blocks.directProduct.2.2]
      refine iSup_le fun O => ?_
      obtain ⟨h, hh, hcase, hO⟩ := reciprocalOrbit_cases hK hx3 O
      rcases hcase with rfl | rfl
      · rw [hO]
        exact le_sup_left
      · rw [hO]
        exact le_sup_right
    have hsplit : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSp 3 K)),
        ∃ a ∈ spSupported x ({(X - 1 : K[X])} : Set K[X]),
          ∃ b ∈ spSupported x ({(X2K : K[X])} : Set K[X]), g = a * b :=
      fun g hg => i269s_mem_sup_of_commute hcomm (hcover hg)
    by_cases hFs : Group.IsSolvable ↥(spSupported x ({(X - 1 : K[X])} : Set K[X]))
    · haveI := hFs
      haveI := hsolvH
      refine i269s_solvable_of_prod (spSupported x ({(X - 1 : K[X])} : Set K[X]))
        (spSupported x ({(X2K : K[X])} : Set K[X]))
        (Subgroup.centralizer ({x} : Set (StatedSp 3 K)) ⊓
          Subgroup.centralizer ({y} : Set (StatedSp 3 K))) hcomm (fun g hg => ?_)
      obtain ⟨a, ha, b, hb, hgab⟩ := hsplit g (Subgroup.mem_inf.1 hg).1
      exact ⟨a, ha, b, hb, hgab⟩
    · rcases orbit_tame hK hx3 hx1 blocks ⟨{(X - 1 : K[X])}, hO1⟩ with ⟨-, hd4, -⟩ | hsolF
      swap
      · exact absurd hsolF hFs
      have hm1 : primaryMultiplicity (spEnd x) (X2K : K[X]) = 1 := by omega
      have hHcard : Nat.card ↥(spSupported x ({(X2K : K[X])} : Set K[X])) = 3 :=
        i269s_card_H hK hx3 blocks hX2 hm1
      obtain ⟨-, hodd⟩ := spFixed_four_two hK blocks hd4
      obtain ⟨⟨eD⟩, hrel⟩ := spFixed_four_two_alt hK blocks hd4
      have hDF : ⁅spFixedFactor x, spFixedFactor x⁆ ≤ spFixedFactor x :=
        Subgroup.commutator_le.2 fun a ha b hb => by
          rw [commutatorElement_def]
          exact (spFixedFactor x).mul_mem
            ((spFixedFactor x).mul_mem ((spFixedFactor x).mul_mem ha hb)
              ((spFixedFactor x).inv_mem ha)) ((spFixedFactor x).inv_mem hb)
      have hcardF : Nat.card ↥(spFixedFactor x) = 720 := by
        have h1 := (⁅spFixedFactor x, spFixedFactor x⁆.subgroupOf (spFixedFactor x)).card_mul_index
        have h2 : Nat.card ↥(⁅spFixedFactor x, spFixedFactor x⁆.subgroupOf (spFixedFactor x)) =
            Nat.card ↥⁅spFixedFactor x, spFixedFactor x⁆ :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDF).toEquiv
        have h3 : (⁅spFixedFactor x, spFixedFactor x⁆.subgroupOf (spFixedFactor x)).index = 2 := hrel
        have h4 : Nat.card ↥⁅spFixedFactor x, spFixedFactor x⁆ = 360 := by
          rw [Nat.card_congr eD.toEquiv, card_alternating_six]
        rw [h2, h4, h3] at h1
        omega
      have hD : ∀ w ∈ spFixedFactor x, ∀ q : ℕ, q.Prime → q ≠ 2 → w ^ q = 1 →
          w ∈ ⁅spFixedFactor x, spFixedFactor x⁆ :=
        fun w hw q hq hq2 hwq => hodd hq hq2 w hw hwq
      obtain ⟨c, hcF, d, hdH, hycd⟩ := hsplit y hyC
      have hc3 : c ^ 3 = 1 := i269s_cube_fst hcomm hdisj hcF hdH (by rw [← hycd]; exact hy3)
      have hc1 : c ≠ 1 := by
        intro hc1
        rw [hc1, one_mul] at hycd
        have hzle : Subgroup.zpowers x ≤ spSupported x ({(X2K : K[X])} : Set K[X]) :=
          Subgroup.zpowers_le.2 hxH
        have hcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
        have heq := Subgroup.eq_of_le_of_card_ge hzle (by rw [hcard, hHcard])
        apply hyx
        rw [heq, hycd]
        exact hdH
      haveI hsolvP := i269s_fixed_sp4_solvable (spFixedFactor x) ⁅spFixedFactor x, spFixedFactor x⁆
        hcardF hDF eD hD c hcF hc3 hc1
      haveI := hsolvH
      refine i269s_solvable_of_prod (Subgroup.centralizer ({c} : Set (StatedSp 3 K)) ⊓
          spFixedFactor x)
        (spSupported x ({(X2K : K[X])} : Set K[X]))
        (Subgroup.centralizer ({x} : Set (StatedSp 3 K)) ⊓
          Subgroup.centralizer ({y} : Set (StatedSp 3 K)))
        (fun p hp q hq => hcomm p (Subgroup.mem_inf.1 hp).2 q hq) (fun g hg => ?_)
      obtain ⟨a, ha, b, hb, rfl⟩ := hsplit g (Subgroup.mem_inf.1 hg).1
      have hgy : a * b ∈ Subgroup.centralizer ({y} : Set (StatedSp 3 K)) :=
        (Subgroup.mem_inf.1 hg).2
      have hcomm_gy : (a * b) * (c * d) = (c * d) * (a * b) := by
        rw [← hycd]
        exact ((Subgroup.mem_centralizer_iff.1 hgy) y (Set.mem_singleton y)).symm
      have hac : a * c = c * a := i269s_comm_fst hcomm hdisj ha hb hcF hdH hcomm_gy
      have haC : a ∈ Subgroup.centralizer ({c} : Set (StatedSp 3 K)) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff.1 hh]
          exact hac.symm
      exact ⟨a, Subgroup.mem_inf.2 ⟨haC, ha⟩, b, hb, rfl⟩
  · have hle : Subgroup.centralizer ({x} : Set (StatedSp 3 K)) ≤
        spSupported x ({(X2K : K[X])} : Set K[X]) := by
      rw [← blocks.directProduct.2.2]
      refine iSup_le fun O => ?_
      obtain ⟨h, hh, hcase, hO⟩ := reciprocalOrbit_cases hK hx3 O
      rcases hcase with rfl | rfl
      · exact absurd hh hX1
      · rw [hO]
    haveI := hsolvH
    exact isSolvable_of_le_isSolvable (inf_le_left.trans hle)

end CFSG.LocalAnalysis.GLTheoremA

end
