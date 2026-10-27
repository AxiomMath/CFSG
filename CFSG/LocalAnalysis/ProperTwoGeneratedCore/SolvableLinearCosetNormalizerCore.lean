module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerTranslations
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerComplement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerSylow

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizer CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative Pointwise MatrixGroups

universe u

variable {G : Type u} [Group G] [Finite G]

theorem solvable_linear_coset_normalizer_core
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    (hPK : LinearSuzukiPointKernelRootProduct G) (hOC : LinearSuzukiHullOddCoreTrivial G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hut : Commute u t)
    (hdeg : Nat.card (elementFixedSet H u) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) + 1)
    (hn : Nat.card (pointRightCosetSpace H) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) ^ 2 + 1)
    (hsolv : Group.IsSolvable (cosetNormalizerPerm (rootCoset H z u)).range) :
    let M := Subgroup.centralizer ({u} : Set G)
    let D := pairPointStabilizer H beta
    let L := localInvolutionPointHull z u
    let q := Nat.card ({1} ∪ distinguishedRoots H z u : Set G)
    let Δ := rootCoset H z u
    let N := Subgroup.normalizer Δ
    let A := N ⊓ D
    (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) ∧ ¬ IsConj u z ∧
    ∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f ∧
    ∃ (U : Subgroup G) (_ : IsElementaryAbelian 2 U),
      (U : Set G) = {1} ∪ distinguishedRoots H z u ∧ (∀ x ∈ U, x ≠ 1 → IsConj z x) ∧
      ∃ j : Additive U ≃ Δ, (∀ v : U, (j (Additive.ofMul v) : G) = u * v) ∧
        (∀ g ∈ translationGroup (Additive U),
          j.permCongr g.toEquiv ∈ (cosetNormalizerPerm Δ).range) ∧
        (∀ n : N, (∃ g ∈ translationGroup (Additive U),
            cosetNormalizerPerm Δ n = j.permCongr g.toEquiv) ↔
          (n : G) ∈ Subgroup.centralizer (U : Set G)) ∧
        let Q := N ⊓ Subgroup.centralizer (U : Set G)
        let V := U ⊔ ⁅A, Q⁆
        U ≤ Q ∧ u ∈ Q ∧ Nat.card Q = 2 * q ^ 2 ∧ (∀ x ∈ Q, x * x ∈ U) ∧
        (∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ U) ∧ N ≤ Subgroup.normalizer (Q : Set G) ∧
        A = D ⊓ M ∧ N = Q ⊔ A ∧ Q ⊓ A = Subgroup.zpowers u ∧
        V ≤ Q ∧ N ≤ Subgroup.normalizer (V : Set G) ∧ u ∉ V ∧ Nat.card V = q ^ 2 ∧
        (∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U) ∧
        Subgroup.zpowers u ⊔ V = Q ∧
        Nat.card N = 2 ^ (2 * f) * Nat.card A ∧
        (∀ S : Sylow 2 N, ∃ S' : Sylow 2 G, (S' : Subgroup G) = (S : Subgroup N).map N.subtype) ∧
        (L.subgroupOf M).Normal ∧
        (∃ e : ℕ, 1 ≤ e ∧ Nat.card (BinaryGaloisField e) = 2 ^ e ∧
          Nonempty (L ≃* SL(2, BinaryGaloisField e))) ∧
        M ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers u ∧
        (∀ X : Subgroup G, X ≤ L ⊓ A → IsPGroup 2 X → X = ⊥) ∧
        (∀ x ∈ Q, IsConj u x → ∀ y ∈ U, IsConj u (x * y)) ∧
        (∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y → IsConj z (x * y)) := by
  intro M D L q Δ N A
  classical
  have htH : t ∉ H := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have hesc : ¬ M ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq.symm))
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  obtain ⟨⟨hsimple, hnonab⟩, hnconj, ⟨f, hf, hqf⟩, U, hUset, hUel, hqU, hUz, hΔu, hUL, huL, hLn,
      hXU, hSL, hBle, hKu, hconjH, hprod⟩ :=
    solvable_linear_root_data hPK hOC h hbeta ht hrank huD hu huz hut hdeg
  have hqf' : q = 2 ^ f := hqf
  have hqU' : Nat.card U = q := hqU
  obtain ⟨-, hindex, hglobal⟩ :=
    exact_two_power_point_index_root_coset hgen.pairGenerationTheorem h hbeta huD hu huz hesc
  have hindex' : D.relIndex N = q * (Nat.card (elementFixedSet H u) - 1) := hindex
  have hglobal' : Nat.card (pointRightCosetSpace H) - 1 =
      q * (Nat.card (elementFixedSet H u) - 1) → ∀ S : Sylow 2 N, ∃ S' : Sylow 2 G,
        (S' : Subgroup G) = (S : Subgroup N).map N.subtype := hglobal
  have hsolv' : Group.IsSolvable (cosetNormalizerPerm Δ).range := hsolv
  have hΔ : Δ = (fun v : G => u * v) '' (U : Set G) := by
    show rootCoset H z u = _
    rw [hUset]
    rfl
  clear hindex hglobal hsolv
  clear_value Δ
  subst hΔ
  have hcomm : ∀ x ∈ U, Commute u x := by
    intro x hx
    rw [← SetLike.mem_coe, hUset] at hx
    rcases hx with hx | ⟨-, hxM⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact Commute.one_right u
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hxM).symm
  have hUsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
    rwa [pow_two] at h1
  have huU : u ∉ U := fun h' => huL (hUL h')
  have hq4 : 4 ≤ q := by
    rw [hqf']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huD
  have hLM : L ≤ M := localInvolutionPointHull_le_centralizer z u
  obtain ⟨hNH, hLN, hLtr, j, hj, htr⟩ :=
    coset_normalizer_translation_data h hbeta hrank huD hu huz hesc U hUset hsolv'
  refine ⟨⟨hsimple, hnonab⟩, hnconj, f, hf, hqf', U, hUel, hUset, hUz, j, hj, htr,
    fun n => translation_iff_mem_centralizer hu2 hcomm j hj n, ?_⟩
  intro Q V
  have hθsurj := exists_displacement_eq_of_translations hu2 hcomm j hj htr
  obtain ⟨hEQ, hQE, -, hQcard, hsq, hQcomm⟩ :=
    translation_subgroup_structure hu2 hcomm hUsq huU hθsurj hBle
  have hUQ : U ≤ Q := le_sup_right.trans hEQ
  have huQ : u ∈ Q := hEQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hNU : N ≤ Subgroup.normalizer (U : Set G) :=
    involution_translate_normalizer_le_unit_normalizer U u hu2 hcomm
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) := fun n hn =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hn, le_normalizer_centralizer (hNU hn)⟩
  have hinter : (fun v : G => u * v) '' (U : Set G) ∩ (D : Set G) = {u} := by
    have h1 := translated_coset_inter_pair_eq_singleton h.local_datum beta hbeta huD
    have hcus : cosetUnitSet H z u = (U : Set G) := by
      rw [hUset, cosetUnitSet, one_union_distinguishedRoots_eq]
    rwa [translatedCosetUnitSet, hcus] at h1
  have hND := normalizer_inter_eq_centralizer_inter _ D u hinter
  have hAM : A ≤ M := fun x hx => by
    have h1 : x ∈ (N ⊓ M) ⊓ D := hND ▸ hx
    exact h1.1.2
  have hAeq : A = D ⊓ M := by
    apply le_antisymm (le_inf inf_le_right hAM)
    rintro x ⟨hxD, hxM⟩
    exact ⟨centralizer_inf_normalizer_le_normalizer_coset U u
      ⟨hxM, inf_le_normalizer_root hUset ⟨pairPointStabilizer_le_point H beta hxD, hxM⟩⟩, hxD⟩
  have hUD : ∀ b ∈ U, b ∈ D → b = 1 := by
    intro b hb hbD
    have h1 : u * b ∈ (fun v : G => u * v) '' (U : Set G) ∩ (D : Set G) :=
      ⟨⟨b, hb, rfl⟩, D.mul_mem huD hbD⟩
    rw [hinter] at h1
    exact mul_left_cancel (h1.trans (mul_one u).symm)
  have huA : u ∈ A := ⟨(inf_le_left : Q ≤ N) huQ, huD⟩
  have hQA : Q ⊓ A = Subgroup.zpowers u := by
    apply le_antisymm
    · rintro x ⟨hxQ, hxA⟩
      have hxE : x ∈ Subgroup.zpowers u ⊔ U := hQE ▸ ⟨hxQ, hAM hxA⟩
      rw [Subgroup.zpowers_eq_closure, mem_closure_singleton_sup_iff hu2 hcomm] at hxE
      rw [Subgroup.zpowers_eq_closure]
      rcases hxE with hxU | ⟨b, hb, rfl⟩
      · rw [hUD x hxU hxA.2]
        exact Subgroup.one_mem _
      · have hbD : b ∈ D := by
          have h1 : b = u⁻¹ * (u * b) := by group
          rw [h1]
          exact D.mul_mem (D.inv_mem huD) hxA.2
        show u * b ∈ _
        rw [hUD b hb hbD, mul_one]
        exact Subgroup.subset_closure (Set.mem_singleton u)
    · rw [Subgroup.zpowers_le]
      exact ⟨huQ, huA⟩
  have hk : Nat.card (elementFixedSet H u) - 1 = q := by
    rw [hdeg]
    rfl
  rw [hk] at hindex' hglobal'
  have hNcard : Nat.card N = 2 ^ (2 * f) * Nat.card A := by
    have h1 := Subgroup.card_mul_index (D.subgroupOf N)
    have h2 : Nat.card (D.subgroupOf N) = Nat.card A := by
      rw [← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ N ≤ N)).toEquiv,
        inf_comm]
    rw [h2] at h1
    change Nat.card A * D.relIndex N = Nat.card N at h1
    rw [hindex', hqf'] at h1
    rw [← h1]
    ring
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := fun a ha => hNQ ha.1
  have hNQA : N = Q ⊔ A := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hAQ
    rw [hQA, Nat.card_zpowers, hu, hQcard, hqU'] at h1
    have h3 : (2 : ℕ) ^ (2 * f) = q ^ 2 := by rw [hqf']; ring
    have h2 : Nat.card (A ⊔ Q : Subgroup G) = Nat.card N := by
      rw [hNcard, h3]
      linarith
    rw [sup_comm]
    exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) h2.symm.le).symm
  have hNset : (N : Set G) = (Q : Set G) * (A : Set G) := by
    rw [hNQA, Subgroup.coe_mul_of_right_le_normalizer_left Q A hAQ]
  have hMLn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hCA : L ⊓ D ≤ A := fun x hx => hAeq ▸ ⟨hx.2, hLM hx.1⟩
  have hAC : A ≤ Subgroup.normalizer ((L ⊓ D : Subgroup G) : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hMLn (hAM ha), Subgroup.le_normalizer ha.2⟩
  have hLDH : L ⊓ D ≤ L ⊓ H := inf_le_inf_left L (pairPointStabilizer_le_point H beta)
  have hCodd : Odd (Nat.card (L ⊓ D : Subgroup G)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hxp : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe]
      exact hx
    have hxle : Subgroup.zpowers (x : G) ≤ L ⊓ H :=
      Subgroup.zpowers_le.mpr (hLDH x.2)
    have hxU : (x : G) ∈ U := hXU _ hxle hxp (Subgroup.mem_zpowers _)
    have hx1 : (x : G) = 1 := hUD _ hxU x.2.2
    rw [← Subgroup.orderOf_coe, hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hCtr : ∀ b ∈ U, b ≠ 1 → ∀ b' ∈ U, b' ≠ 1 → ∃ c ∈ L ⊓ D, c * b * c⁻¹ = b' := by
    intro b hb hb1 b' hb' hb'1
    obtain ⟨m, ⟨hmL, hmU⟩, hmb⟩ := hLtr b hb hb1 b' hb' hb'1
    have hmN : m ∈ (N : Set G) := hLN ⟨hmL, hmU⟩
    rw [hNset] at hmN
    obtain ⟨x, hxQ, a, haA, hxa⟩ := hmN
    have hxM : x ∈ M := by
      have h1 : x = m * a⁻¹ := by rw [← hxa]; group
      rw [h1]
      exact M.mul_mem (hLM hmL) (M.inv_mem (hAM haA))
    have hxE : x ∈ Subgroup.zpowers u ⊔ U := hQE ▸ ⟨hxQ, hxM⟩
    rw [Subgroup.zpowers_eq_closure, mem_closure_singleton_sup_iff hu2 hcomm] at hxE
    have hconjb : ∀ y ∈ U, (y⁻¹ * m) * b * (y⁻¹ * m)⁻¹ = b' := by
      intro y hy
      calc (y⁻¹ * m) * b * (y⁻¹ * m)⁻¹ = y⁻¹ * (m * b * m⁻¹) * y := by group
        _ = y⁻¹ * b' * y := by rw [hmb]
        _ = b' := by
          rw [mul_comm_of_mul_self_eq_one hUsq (U.inv_mem hy) hb', mul_assoc, inv_mul_cancel,
            mul_one]
    rcases hxE with hxU | ⟨y, hyU, rfl⟩
    · refine ⟨x⁻¹ * m, ⟨L.mul_mem (L.inv_mem (hUL hxU)) hmL, ?_⟩, hconjb x hxU⟩
      have h1 : x⁻¹ * m = a := by rw [← hxa]; group
      rw [h1]
      exact haA.2
    · refine ⟨y⁻¹ * m, ⟨L.mul_mem (L.inv_mem (hUL hyU)) hmL, ?_⟩, hconjb y hyU⟩
      have h1 : y⁻¹ * m = u * a := by
        rw [← hxa]
        calc y⁻¹ * ((fun v : G => u * v) y * a) = y⁻¹ * (u * y) * a := by simp only [mul_assoc]
          _ = y⁻¹ * (y * u) * a := by rw [(hcomm y hyU).eq]
          _ = u * a := by group
      rw [h1]
      exact D.mul_mem huD haA.2
  have hE : ∀ x ∈ Q, x * u = u * x → x ∈ U ∨ u * x ∈ U := by
    intro x hx hxu
    have hxE : x ∈ Subgroup.zpowers u ⊔ U :=
      hQE ▸ ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxu⟩
    rw [Subgroup.zpowers_eq_closure, mem_closure_singleton_sup_iff hu2 hcomm] at hxE
    rcases hxE with h1 | ⟨v, hv, rfl⟩
    · exact Or.inl h1
    · right
      change u * (u * v) ∈ U
      rw [← mul_assoc, hu2, one_mul]
      exact hv
  obtain ⟨hVQ, hAV, hQV, huV, -, -, hVcard, htrans, hQeqV⟩ :=
    sup_commutator_complement hUQ inf_le_right hQcomm huQ huU hu2
      (fun x hx => involutionDisplacement_mem hu2 hx.1) hθsurj hE hAQ
      (fun a ha => hNU ha.1) hAM hCA hAC hCodd hCtr (by omega)
  have hNV : N ≤ Subgroup.normalizer (V : Set G) := by
    rw [hNQA]
    exact sup_le hQV hAV
  have hLA : ∀ X : Subgroup G, X ≤ L ⊓ A → IsPGroup 2 X → X = ⊥ := by
    intro X hX hXp
    have hXU := hXU X (fun x hx => ⟨(hX hx).1,
      pairPointStabilizer_le_point H beta (hX hx).2.2⟩) hXp
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (hUD x (hXU hx) (hX hx).2.2)
  have hsat : ∀ x ∈ Q, IsConj u x → ∀ y ∈ U, IsConj u (x * y) := fun x hx hxc y hy =>
    isConj_mul_of_mem_root hUset hΔu hconjH (hNH hx.1) hx.2 hxc hy
  refine ⟨hUQ, huQ, by rw [hQcard, hqU'], hsq, hQcomm, hNQ, hAeq, hNQA, hQA, hVQ, hNV, huV,
    by rw [hVcard, hqU'], htrans, hQeqV, hNcard, ?_, hLn, hSL, hKu, hLA, hsat, hprod⟩
  apply hglobal'
  show Nat.card (pointRightCosetSpace H) - 1 = q * q
  rw [hn]
  show q ^ 2 + 1 - 1 = q * q
  rw [Nat.add_sub_cancel, pow_two]

end CFSG.ProperTwoGeneratedCore.HighRankPair
