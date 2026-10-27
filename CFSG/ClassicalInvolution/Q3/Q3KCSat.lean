module

public import CFSG.ClassicalInvolution.Q3.Q3KCBoot
public import CFSG.ClassicalInvolution.Balance.BootstrapUntouched
import CFSG.ClassicalInvolution.Q3.Q3NHVertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NG


section Defs

variable {G : Type} [Group G]

@[expose] def membersOver (Ω : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ ∃ z ∈ A, IsClassicalMember3 M z}

end Defs

section Abstract

variable {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}

theorem le_range_of_not_centralizes (D : LieSystemData3 ι X Φ) {k : ι} {M : Subgroup X}
    (hM : M ∈ Φ) {m : X} (hm : m ∈ M) (hnc : ¬ ∀ q ∈ (D.hom k).range, m * q = q * m) :
    M ≤ (D.hom k).range :=
  CFSG.ClassicalInvolution.Q3.Q3NH.le_range_of_not_centralizes' D hM hm hnc

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem exists_lift_centralizer_group {Y : Subgroup G} (hA : IsElemAbelian 2 A) (hAY : A ≤ Y)
    {q : ↥Y ⧸ classicalInvolutionOddCore ↥Y}
    (hq : ∀ (f : G) (hf : f ∈ A), QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
      ⟨f, hAY hf⟩ * q = q * QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨f, hAY hf⟩) :
    ∃ y : ↥Y, y ∈ Subgroup.centralizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y = q := by
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  set E : Subgroup ↥Y := A.subgroupOf Y with hE
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx =>
    Subtype.ext (Q3C.elem_sq hA (Subgroup.mem_subgroupOf.mp hx))
  have hnorm : E ≤ Subgroup.normalizer ((⊤ : Subgroup ↥Y) : Set ↥Y) := fun x _ =>
    (Subgroup.mem_normalizer_iff).mpr fun h => by simp
  have key := map_inf_centralizer_eq π (Q3Y2.odd_card_ker_mk Y) E ⊤
    (isPGroup_two_of_sq_eq_one hE2) hnorm
  have hqmem : q ∈ (⊤ : Subgroup ↥Y).map π ⊓ Subgroup.centralizer (E.map π : Set _) := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨y, trivial, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hq x (Subgroup.mem_subgroupOf.mp hx)
  rw [← key] at hqmem
  obtain ⟨y, ⟨-, hyE⟩, hyq⟩ := hqmem
  exact ⟨y, hyE, hyq⟩

theorem exists_involution_lift_group {Y : Subgroup G} (hA : IsElemAbelian 2 A) (hAY : A ≤ Y)
    {z : G} (hzY : z ∈ Y) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcomm : ∀ (f : G) (hf : f ∈ A), QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
        ⟨f, hAY hf⟩ * QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hzY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hzY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨f, hAY hf⟩) :
    ∃ (w : G) (hw : w ∈ Y), w ∈ Subgroup.centralizer (A : Set G) ∧ w * w = 1 ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hw⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hzY⟩ := by
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  obtain ⟨y, hyE, hyq⟩ := exists_lift_centralizer_group hA hAY (q := π ⟨z, hzY⟩) hcomm
  have hker : Odd (Nat.card π.ker) := Q3Y2.odd_card_ker_mk Y
  have hzb1 : π ⟨z, hzY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hzY hz2 hz1
  have hzb2 : π ⟨z, hzY⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hord : orderOf (π ⟨z, hzY⟩) = 2 := orderOf_eq_prime hzb2 hzb1
  have hy2 : y ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hyq]
    exact hzb2
  have hodd : Odd (orderOf (y ^ 2)) := hker.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy2)
  have hdvd : 2 ∣ orderOf y := by
    have := orderOf_map_dvd π y
    rw [hyq, hord] at this
    exact this
  obtain ⟨m, hm⟩ := hdvd
  have hgm : orderOf (y ^ 2) = m := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  rw [hgm] at hodd
  refine ⟨((y ^ m : ↥Y) : G), (y ^ m).2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hge : y ^ m ∈ Subgroup.centralizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) :=
      Subgroup.pow_mem _ hyE m
    have := Subgroup.mem_centralizer_iff.mp hge ⟨e, hAY he⟩ (Subgroup.mem_subgroupOf.mpr he)
    exact congrArg Subtype.val this
  · have : y ^ m * y ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← hm]
      exact pow_orderOf_eq_one y
    exact congrArg Subtype.val this
  · obtain ⟨k, hk⟩ := hodd
    show π (y ^ m) = π ⟨z, hzY⟩
    rw [map_pow, hyq, hk, pow_succ, pow_mul, hzb2, one_pow, one_mul]

end Lift

section Cover

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lieCovers3_of_saturated (hΩ : InClass3 Ω) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hsat : InvSaturated T.group) {a : G} (ha : a ∈ T.group) :
    LieCovers3 Ω (membersOver Ω T.group) a := by
  intro ι D i
  have hΩc := hΩ.conjInvariant
  have hA := T.isElemAbelian
  have hAY : T.group ≤ centralizingLayer Ω {a} :=
    group_le_centralizingLayer_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  have hbc : ∀ {M : Subgroup G}, M ≤ Subgroup.centralizer (T.group : Set G) →
      M ≤ Subgroup.centralizer ({a} : Set G) := fun hM =>
    hM.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  set Y := centralizingLayer Ω {a} with hY
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hΦ : ∀ {M : Subgroup G}, M ∈ centralizingMembers Ω {a} →
      modOddIn Y M ∈ localFamily Ω a :=
    fun {M} hM => ⟨M.subgroupOf Y, ⟨M, hM, le_centralizingLayer hM, rfl⟩, rfl⟩
  have hmove : ∀ {K : Subgroup G} {z : G}, K ∈ Ω → K ≤ Subgroup.centralizer ({a} : Set G) →
      IsClassicalMember3 K z → ∀ hzA : z ∈ T.group,
      (¬ ∀ q ∈ (D.hom i).range, π ⟨z, hAY hzA⟩ * q = q * π ⟨z, hAY hzA⟩) →
      ∃ K' ∈ membersOver Ω T.group, K' ≤ Subgroup.centralizer ({a} : Set G) ∧
        modOddIn Y K' ≤ (D.hom i).range := by
    intro K z hKΩ hKa hz hzA hnc
    refine ⟨K, ⟨hKΩ, z, hzA, hz⟩, hKa, ?_⟩
    exact le_range_of_not_centralizes D (hΦ ⟨hKΩ, hKa⟩) (m := π ⟨z, hAY hzA⟩)
      ⟨⟨z, hAY hzA⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩ hnc
  by_cases hc₁ : ∀ q ∈ (D.hom i).range, π ⟨z₁, hAY hz₁A⟩ * q = q * π ⟨z₁, hAY hz₁A⟩
  swap
  · exact hmove hΩ₁ (hbc T.le_centralizer₁) hz₁ hz₁A hc₁
  by_cases hc₂ : ∀ q ∈ (D.hom i).range, π ⟨z₂, hAY hz₂A⟩ * q = q * π ⟨z₂, hAY hz₂A⟩
  swap
  · exact hmove hΩ₂ (hbc T.le_centralizer₂) hz₂ hz₂A hc₂
  by_cases hc₃ : ∀ q ∈ (D.hom i).range, π ⟨z₃, hAY hz₃A⟩ * q = q * π ⟨z₃, hAY hz₃A⟩
  swap
  · exact hmove hΩ₃ (hbc T.le_centralizer₃) hz₃ hz₃A hc₃
  have hfix : ∀ (f : G) (hf : f ∈ T.group), ∀ q ∈ (D.hom i).range,
      π ⟨f, hAY hf⟩ * q = q * π ⟨f, hAY hf⟩ := by
    set Q : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) := (D.hom i).range with hQ
    let Cq : Subgroup G := ((Subgroup.centralizer (Q : Set _)).comap π).map Y.subtype
    have hCq : ∀ (f : G) (hf : f ∈ Y), (∀ q ∈ Q, π ⟨f, hf⟩ * q = q * π ⟨f, hf⟩) → f ∈ Cq :=
      fun f hf h => ⟨⟨f, hf⟩, Subgroup.mem_centralizer_iff.mpr fun q hq => (h q hq).symm, rfl⟩
    have hsub : T.group ≤ Cq := by
      refine (Subgroup.closure_le _).mpr ?_
      rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hCq z₁ (hAY hz₁A) hc₁, hCq z₂ (hAY hz₂A) hc₂, hCq z₃ (hAY hz₃A) hc₃⟩
    intro f hf q hq
    obtain ⟨c, hc, hcf⟩ := hsub hf
    have hcf' : c = ⟨f, hAY hf⟩ := Subtype.ext hcf
    subst hcf'
    exact (Subgroup.mem_centralizer_iff.mp hc q hq).symm
  obtain ⟨R, hR, hmeet⟩ := D.meets i
  obtain ⟨_, ⟨M, hMmem, hMY, rfl⟩, hS⟩ := hmeet
  have hMbar : modOddIn Y M ≤ (D.hom i).range := by
    have h1 : modOddIn Y M = R.map (D.hom i) := hS
    rw [h1]
    exact Subgroup.map_le_range _ _
  obtain ⟨z, hz⟩ := hΩ.classical M hMmem.1
  have hzY : z ∈ Y := hMY hz.mem
  have hz2 : z * z = 1 := hz.isCentralInvolution.sq
  have hzbar : π ⟨z, hzY⟩ ∈ (D.hom i).range :=
    hMbar ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
  obtain ⟨w, hwY, hwC, hw2, hwπ⟩ := exists_involution_lift_group hA hAY hzY hz2 hz.ne_one
    (fun f hf => hfix f hf _ hzbar)
  have hwA : w ∈ T.group := hsat w hw2 hwC
  obtain ⟨o, ho, hzo⟩ := Q3Y.exists_conj_of_mk_eq Y hwY hzY hw2 hz2 hwπ
  have hoY : o ∈ Y := oddCoreIn_le _ ho
  have hoC : o ∈ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a} hoY
  have hK' : IsClassicalMember3 (conjSub o⁻¹ M) w := by
    have h1 := hz.conj o⁻¹
    have e : o⁻¹ * z * (o⁻¹)⁻¹ = w := by rw [hzo]; group
    rwa [e] at h1
  have hKmem : conjSub o⁻¹ M ∈ centralizingMembers Ω {a} :=
    conjSub_mem_centralizingMembers hΩc (Subgroup.inv_mem _ hoC) hMmem
  refine ⟨conjSub o⁻¹ M, ⟨hKmem.1, w, hwA, hK'⟩, hKmem.2, ?_⟩
  refine le_trans ?_ hMbar
  rintro _ ⟨c, hc, rfl⟩
  have hc' : (c : G) ∈ conjSub o⁻¹ M := Subgroup.mem_subgroupOf.mp hc
  rw [mem_conjSub_iff] at hc'
  have hm : o * (c : G) * o⁻¹ ∈ M := by simpa using hc'
  have hmY : o * (c : G) * o⁻¹ ∈ Y := hMY hm
  have hπo : π ⟨o, hoY⟩ = 1 := by
    obtain ⟨x, hx, hxo⟩ := ho
    have hxo' : x = ⟨o, hoY⟩ := Subtype.ext hxo
    rw [hxo'] at hx
    exact (QuotientGroup.eq_one_iff _).mpr hx
  have hπo' : π ⟨o⁻¹, Y.inv_mem hoY⟩ = 1 := by
    have : (⟨o⁻¹, Y.inv_mem hoY⟩ : ↥Y) = (⟨o, hoY⟩ : ↥Y)⁻¹ := rfl
    rw [this, map_inv, hπo, inv_one]
  have hceq : c = ⟨o⁻¹, Y.inv_mem hoY⟩ * ⟨o * (c : G) * o⁻¹, hmY⟩ * ⟨o, hoY⟩ :=
    Subtype.ext (by
      show (c : G) = o⁻¹ * (o * (c : G) * o⁻¹) * o
      group)
  refine ⟨⟨o * (c : G) * o⁻¹, hmY⟩, Subgroup.mem_subgroupOf.mpr hm, ?_⟩
  calc π ⟨o * (c : G) * o⁻¹, hmY⟩
      = π ⟨o⁻¹, Y.inv_mem hoY⟩ * π ⟨o * (c : G) * o⁻¹, hmY⟩ * π ⟨o, hoY⟩ := by
        rw [hπo, hπo', one_mul, mul_one]
    _ = π c := by rw [← map_mul, ← map_mul, ← hceq]

end Cover

section Generation

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rankTwoSpan_eq_top_of_saturated (hΩ : InClass3 Ω) (hIH : LocalLieSystems3 Ω)
    (hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G) (hconn : OmegaConnected Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hz₂ : IsClassicalMember3 K₂ z₂)
    (hz₃ : IsClassicalMember3 K₃ z₃) (hsat : InvSaturated T.group) :
    (⨆ F ∈ signalizerFunctorEk 2 2 T.group, Subgroup.centralizer (F : Set G)) = ⊤ := by
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  refine rankTwoSpan_eq_top3 (A := T.group) (S := membersOver Ω T.group) hΩ
    { elem := T.isElemAbelian
      card := (T.card_eq_eight hind).ge
      subset := fun M hM => hM.1
      nonempty := ⟨K₁, hΩ₁, z₁, hz₁A, hz₁⟩
      involution := fun M hM => hM.2
      generation := fun a ha hfa => ?_
      link := fun a ha hfa => ?_ } hconn
  · obtain ⟨L, -, hLa⟩ := hfa
    exact centralizerGenerationModOTwo_of_exactTriple hIH T hind hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ ha
      hLa.ne_one (hnc a hLa.ne_one)
  · obtain ⟨L, -, hLa⟩ := hfa
    exact involutionLink_of_lieCovers3' hΩ hIH (hnc a hLa.ne_one) (fun M hM => hM.1)
      (fun M hM => hM.2) (lieCovers3_of_saturated hΩ T hΩ₁ hΩ₂ hΩ₃ hz₁ hz₂ hz₃ hsat ha)

theorem invSaturated_of_twoRank_le_three {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hr : CFSG.Open.twoRank G ≤ 3) : InvSaturated A := by
  intro w hw2 hwC
  by_contra hwA
  have hcomm : ∀ s ∈ (A : Set G) ∪ {w}, ∀ t ∈ (A : Set G) ∪ {w}, s * t = t * s := by
    intro s hs t ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact Q3C.elem_comm hA hs ht
    · rw [Set.mem_singleton_iff.mp ht]
      exact Subgroup.mem_centralizer_iff.mp hwC s hs
    · rw [Set.mem_singleton_iff.mp hs]
      exact (Subgroup.mem_centralizer_iff.mp hwC t ht).symm
    · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht]
  have hsq : ∀ s ∈ (A : Set G) ∪ {w}, s * s = 1 := by
    intro s hs
    rcases hs with hs | hs
    · exact Q3C.elem_sq hA hs
    · rw [Set.mem_singleton_iff.mp hs]
      exact hw2
  set B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {w}) with hB
  have hBe : IsElemAbelian 2 B := Balance.Theorem5.isElemAbelian_closure_of_commuting_involutions
    hsq hcomm
  have hAB : A ≤ B := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hwB : w ∈ B := Subgroup.subset_closure (Or.inr rfl)
  have hBp : IsPGroup 2 B := isPGroup_two_of_sq_eq_one fun x hx => by
    have := hBe.2 x hx
    rwa [pow_two] at this
  obtain ⟨n, hn⟩ := hBp.exists_card_eq
  have hdvd : 8 ∣ 2 ^ n := hn ▸ hcard ▸ Subgroup.card_dvd_of_le hAB
  have hn3 : 3 ≤ n := by
    have h8 : (2 : ℕ) ^ 3 ∣ 2 ^ n := by simpa using hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h8
  have hne : n ≠ 3 := by
    rintro rfl
    have hle : Nat.card B ≤ Nat.card A := by rw [hn, hcard]; norm_num
    exact hwA (Subgroup.eq_of_le_of_card_ge hAB hle ▸ hwB)
  have h4 : 4 ≤ n := by omega
  have := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G B hBe n hn
  omega

theorem rankTwoSpan_eq_top_of_twoRank_le_three {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (hS : BootTripleSetting3 K z) (hr : CFSG.Open.twoRank G ≤ 3)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃) :
    (⨆ F ∈ signalizerFunctorEk 2 2 T.exact.group, Subgroup.centralizer (F : Set G)) = ⊤ := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hS.member
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hS.below
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hS.nonabelian hb1 (Set.singleton_subset_iff.mpr hbc)
  exact rankTwoSpan_eq_top_of_saturated hΩ hIH hnc (omegaConnected_range_conjSub hS.delta)
    T.exact T.ind T.mem₁ T.mem₂ T.mem₃ T.cls₁ T.cls₂ T.cls₃
    (invSaturated_of_twoRank_le_three T.exact.isElemAbelian (T.exact.card_eq_eight T.ind) hr)

end Generation

@[expose] def LieCovers3AtUnsat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    BootTripleSetting3 K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G),
      ∀ T : ClassTriple3 K K₁ K₂ K₃ z₁ z₂ z₃, ¬ InvSaturated T.exact.group →
        ∀ a ∈ T.exact.group,
          IsFrameInvolution3 (frameFamily3 (conjClass3 K) T.exact.group) a →
            LieCovers3 (conjClass3 K) (frameFamily3 (conjClass3 K) T.exact.group) a

theorem lieCovers3AtUnsat_of_lieCovers3At (h : LieCovers3At) : LieCovers3AtUnsat :=
  fun G _ _ _ K z hS K₁ K₂ K₃ z₁ z₂ z₃ T _ a ha hfa => h G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T a ha hfa

theorem tripleGeneration3_of_unsat (hcov : LieCovers3AtUnsat) : TripleGeneration3 := by
  intro G _ _ _ K z hS K₁ K₂ K₃ z₁ z₂ z₃ T
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hS.member
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hS.below
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hS.nonabelian hb1 (Set.singleton_subset_iff.mpr hbc)
  have hconn := omegaConnected_range_conjSub hS.delta
  by_cases hsat : InvSaturated T.exact.group
  · exact rankTwoSpan_eq_top_of_saturated hΩ hIH hnc hconn T.exact T.ind T.mem₁ T.mem₂ T.mem₃
      T.cls₁ T.cls₂ T.cls₃ hsat
  · exact rankTwoSpan_eq_top_of_covers hΩ hIH hnc hconn T.exact T.ind T.mem₁ T.mem₂ T.mem₃
      T.cls₁ T.cls₂ T.cls₃
      (fun a ha hfa => hcov G K z hS K₁ K₂ K₃ z₁ z₂ z₃ T hsat a ha hfa)

theorem bootTriple3_of_unsat (hcov : LieCovers3AtUnsat) (hP1 : P1Cover3) : BootTriple3 :=
  Q3KB.bootTriple3_of_gen' (tripleGeneration3_of_unsat hcov) hP1

end CFSG.ClassicalInvolution.Q3.Q3KC
