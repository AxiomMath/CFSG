module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Root
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Frame

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Abstract

variable {A : Type} [Group A] [Finite A]

theorem card_le_of_isElemAbelian (c : L34Cover A) (T : Sylow 2 A) {M : Subgroup A}
    (hMT : M ≤ T) (hM : IsElemAbelian 2 M) : Nat.card M ≤ 16 * Nat.card c.π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := standardComponentOddCore A
  have hN : Odd (Nat.card N) := RankTwoSporadic.odd_card_standardComponentOddCore
  set p := QuotientGroup.mk' N
  obtain ⟨π', hsurj', hker', hTb⟩ := exists_std_cover c T
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  obtain ⟨hH, -, -, -, -, -, -, hlevi⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  obtain ⟨⟨σ, -, -, hσ, -⟩, -⟩ := hlevi 0
  obtain ⟨⟨-, -, -, -, -, -, hEA, -, -, -, -⟩, -, -⟩ :=
    field_four_central_cover_exact_Sylow_geometry c.card_k π' hsurj' hCZ' helem' σ hσ
  have hpM : IsElemAbelian 2 (M.map p) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg p (congrArg Subtype.val (hM.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hM.2 x hx, map_one]
  have hpM' : CFSG.IsElementaryAbelian 2 ↥(M.map p) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).mpr hpM
  have hpMT : M.map p ≤ (projUnip c.k).comap π' := hTb ▸ map_mono hMT
  have hcard : Nat.card M = Nat.card (M.map p) := (card_map_mk'_of_le T.2 hN hMT).symm
  rcases hEA _ hpMT hpM' with h | h
  · rw [hcard, ← hker', ← (hH 0).2]
    exact card_le_of_le h
  · rw [hcard, ← hker', ← (hH 1).2]
    exact card_le_of_le h


end Abstract

section Transfer

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem mem_sup_centralizer_of_commute (c : L34Cover ↥A)
    (hNZ : standardComponentOddCore ↥A ≤ center ↥A) {S : Subgroup G} (hS : IsSylowOf 2 S A)
    {z : G} (hz : z ∈ centerIn S) (hzZ : z ∉ centralizer (A : Set G)) {y : G} (hyA : y ∈ A)
    (hyz : y * z = z * y) : y ∈ S ⊔ centralizer (A : Set G) := by
  obtain ⟨T, rfl⟩ := hS
  obtain ⟨z₀, hz₀, rfl⟩ := centerIn_map_subtype_le (T : Subgroup ↥A) hz
  have hz₀Z : z₀ ∉ center ↥A := fun h => hzZ (mem_centralizer_iff.mpr fun b hb =>
    congrArg Subtype.val (mem_center_iff.mp h ⟨b, hb⟩))
  have hy : (⟨y, hyA⟩ : ↥A) ∈ (T : Subgroup ↥A) ⊔ center ↥A := by
    apply centralizer_le_sup_center c hNZ T hz₀ hz₀Z
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext hyz
  have h1 : y ∈ ((T : Subgroup ↥A) ⊔ center ↥A).map A.subtype := ⟨_, hy, rfl⟩
  rw [Subgroup.map_sup] at h1
  have hle : (center ↥A).map A.subtype ≤ centralizer (A : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_centralizer_iff.mpr fun b hb => congrArg Subtype.val (mem_center_iff.mp hw ⟨b, hb⟩)
  exact sup_le_sup_left hle _ h1

theorem le_of_le_sup_centralizer {S S' : Subgroup G} (hS : IsSylowOf 2 S A) (hS'A : S' ≤ A)
    (hS' : IsPGroup 2 S') (hle : S' ≤ S ⊔ centralizer (A : Set G)) : S' ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : S ⊔ centralizer (A : Set G) ≤ normalizer (S : Set G) :=
    sup_le le_normalizer ((Subgroup.centralizer_le hS.le).trans
      (Subgroup.centralizer_le_normalizer _))
  have hsup := hS.eq_of_le le_sup_left (sup_le hS.le hS'A)
    (hS.isPGroup.to_sup_of_normal_left' hS' (hle.trans hN))
  rw [← hsup]
  exact le_sup_right

theorem card_le_of_isSylowOf (c : L34Cover ↥A) {S M : Subgroup G} (hS : IsSylowOf 2 S A)
    (hMS : M ≤ S) (hM : IsElemAbelian 2 M) : Nat.card M ≤ 16 * Nat.card c.π.ker := by
  obtain ⟨T, rfl⟩ := hS
  have hMA : M ≤ A := hMS.trans (map_subtype_le _)
  have hMT : M.subgroupOf A ≤ T := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := hMS (mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcard : Nat.card (M.subgroupOf A) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMA).toEquiv
  rw [← hcard]
  exact card_le_of_isElemAbelian c T hMT (isElemAbelian_subgroupOf hM A)

theorem exists_isSylowOf_mem_centerIn (c : L34Cover ↥A) {h : G} (hhA : h ∈ A) (hh2 : h ^ 2 = 1)
    (hh1 : h ≠ 1) : ∃ S : Subgroup G, IsSylowOf 2 S A ∧ h ∈ centerIn S := by
  obtain ⟨T, hT, hTC⟩ := exists_sylow_le_centralizer c (a := ⟨h, hhA⟩)
    (Subtype.ext (by simpa using hh2)) (fun h' => hh1 (congrArg Subtype.val h'))
  refine ⟨(T : Subgroup ↥A).map A.subtype, ⟨T, rfl⟩, ⟨_, hT, rfl⟩, mem_centralizer_iff.mpr ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hTC ht))

theorem isElemAbelian_centerIn (c : L34Cover ↥A) {S : Subgroup G} (hS : IsSylowOf 2 S A) :
    IsElemAbelian 2 (centerIn S) := by
  obtain ⟨T, rfl⟩ := hS
  obtain ⟨H₁, H₂, -, -, hH₁, -, -, -, -, hZ, -, -⟩ := sylow_structure c T
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact (mem_centralizer_iff.mp a.2.2 b b.2.1).symm
  · obtain ⟨x₀, hx₀, rfl⟩ := centerIn_map_subtype_le (T : Subgroup ↥A) hx
    rw [← hZ] at hx₀
    have := hH₁.2 x₀ hx₀.1
    simpa using congrArg Subtype.val this

theorem card_ker_eq_card_inf (c : L34Cover ↥A) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) : Nat.card c.π.ker = Nat.card ↥(R ⊓ A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 ↥A))
  rw [card_ker_eq c T]
  have heq : ((T : Subgroup ↥A) ⊓ center ↥A).map A.subtype = R ⊓ A := by
    apply le_antisymm
    · rintro _ ⟨z, ⟨hzT, hzZ⟩, rfl⟩
      refine ⟨mem_of_mem_centralizer_of_isPGroup hR z.2 ?_ ?_, z.2⟩
      · exact mem_centralizer_iff.mpr fun b hb =>
          congrArg Subtype.val (mem_center_iff.mp hzZ ⟨b, hb⟩)
      · have h2 : IsPGroup 2 (zpowers z) := T.isPGroup'.to_le (zpowers_le.mpr hzT)
        have := h2.map A.subtype
        rwa [MonoidHom.map_zpowers] at this
    · intro x hx
      have hS : IsSylowOf 2 ((T : Subgroup ↥A).map A.subtype) A := ⟨T, rfl⟩
      obtain ⟨t, ht, rfl⟩ := le_of_le_sup_centralizer hS inf_le_right
        (hR.isPGroup.to_le inf_le_left) (inf_le_left.trans (hR.le.trans le_sup_right)) hx
      refine ⟨t, ⟨ht, mem_center_iff.mpr fun b => ?_⟩, rfl⟩
      exact Subtype.ext (mem_centralizer_iff.mp (hR.le hx.1) b b.2)
  rw [← heq, Subgroup.card_map_of_injective A.subtype_injective]

end Transfer

section Lines

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G}

omit [Finite G] in
theorem centerIn_eq_sup {D : Subgroup G} (hRA : R ≤ centralizer (A : Set G))
    (hRc : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r) (hRD : R ≤ D) (hDAR : D ≤ A ⊔ R) :
    centerIn D = centerIn (D ⊓ A) ⊔ R := by
  refine le_antisymm (centerIn_le_sup_of_le_sup hRA hRD hDAR) (sup_le ?_ ?_)
  · rintro x ⟨hxDA, hxC⟩
    refine ⟨hxDA.1, mem_centralizer_iff.mpr fun d hd => ?_⟩
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRD hDAR hd
    have h1 : a * x = x * a := mem_centralizer_iff.mp hxC a ha
    have h2 : r * x = x * r := (mem_centralizer_iff.mp (hRA hr) x hxDA.2).symm
    calc a * r * x = a * (r * x) := by group
      _ = a * (x * r) := by rw [h2]
      _ = a * x * r := by group
      _ = x * a * r := by rw [h1]
      _ = x * (a * r) := by group
  · intro r hr
    refine ⟨hRD hr, mem_centralizer_iff.mpr fun d hd => ?_⟩
    obtain ⟨a, ha, r', hr', rfl⟩ := exists_eq_mul_of_le_sup hRA hRD hDAR hd
    have h1 : a * r = r * a := mem_centralizer_iff.mp (hRA hr) a ha.2
    have h2 : r' * r = r * r' := hRc r' hr' r hr
    calc a * r' * r = a * (r' * r) := by group
      _ = a * (r * r') := by rw [h2]
      _ = a * r * r' := by group
      _ = r * a * r' := by rw [h1]
      _ = r * (a * r') := by group

theorem inf_le_of_ne (c : L34Cover ↥A) (hNZ : standardComponentOddCore ↥A ≤ center ↥A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) {S S' : Subgroup G} (hS : IsSylowOf 2 S A)
    (hS' : IsSylowOf 2 S' A) (hne : S ≠ S') : (centerIn S ⊔ R) ⊓ (centerIn S' ⊔ R) ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdec : ∀ {S₀ : Subgroup G}, S₀ ≤ A → ∀ x ∈ centerIn S₀ ⊔ R,
      ∃ z ∈ centerIn S₀, ∃ r ∈ R, x = z * r := by
    intro S₀ hS₀ x hx
    have hN : centerIn S₀ ≤ normalizer (R : Set G) := fun z hz =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
        (mem_centralizer_iff.mp (hR.le hr) z (hS₀ hz.1)).symm)
    have hx' : x ∈ ((centerIn S₀ ⊔ R : Subgroup G) : Set G) := hx
    rw [coe_mul_of_left_le_normalizer_right _ _ hN, Set.mem_mul] at hx'
    obtain ⟨z, hz, r, hr, rfl⟩ := hx'
    exact ⟨z, hz, r, hr, rfl⟩
  rintro x ⟨hx, hx'⟩
  obtain ⟨z, hz, r, hr, rfl⟩ := hdec hS.le _ hx
  obtain ⟨z', hz', r', hr', he⟩ := hdec hS'.le _ hx'
  by_cases hzA : z ∈ centralizer (A : Set G)
  · have hz2 : IsPGroup 2 (zpowers z) := hS.isPGroup.to_le (zpowers_le.mpr hz.1)
    exact mul_mem (mem_of_mem_centralizer_of_isPGroup hR (hS.le hz.1) hzA hz2) hr
  · exfalso
    apply hne
    have hS'C : S' ≤ S ⊔ centralizer (A : Set G) := by
      intro s hs
      refine mem_sup_centralizer_of_commute c hNZ hS hz hzA (hS'.le hs) ?_
      have hzeq : z = z' * (r' * r⁻¹) := by
        calc z = z * r * r⁻¹ := by group
          _ = z' * r' * r⁻¹ := by rw [he]
          _ = z' * (r' * r⁻¹) := by group
      have h1 : s * z' = z' * s := mem_centralizer_iff.mp hz'.2 s hs
      have hrr : r' * r⁻¹ ∈ R := mul_mem hr' (inv_mem hr)
      have h2 : s * (r' * r⁻¹) = r' * r⁻¹ * s :=
        mem_centralizer_iff.mp (hR.le hrr) s (hS'.le hs)
      rw [hzeq]
      calc s * (z' * (r' * r⁻¹)) = s * z' * (r' * r⁻¹) := by group
        _ = z' * (s * (r' * r⁻¹)) := by rw [h1]; group
        _ = z' * (r' * r⁻¹ * s) := by rw [h2]
        _ = z' * (r' * r⁻¹) * s := by group
    exact hS'.eq_of_le (le_of_le_sup_centralizer hS hS'.le hS'.isPGroup hS'C) hS.le hS.isPGroup

theorem exists_isSylowOf_of_mem (c : L34Cover ↥A)
    (hNZ : standardComponentOddCore ↥A ≤ center ↥A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    {E : Subgroup G} (hE : IsElemAbelian 2 E) (hRE : R ≤ E) (hEAR : E ≤ A ⊔ R)
    (hE64 : Nat.card E = 64) (hR4 : Nat.card R = 4) {e : G} (he : e ∈ E) (heR : e ∉ R) :
    ∃ S : Subgroup G, IsSylowOf 2 S A ∧ centerIn S ≤ E ∧ e ∈ centerIn S ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : IsPGroup 2 E := isPGroup_two_of_isElemAbelian hE
  obtain ⟨h, hh, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRE hEAR he
  have hhK : h ∉ centralizer (A : Set G) := by
    intro hK
    have h2 : IsPGroup 2 (zpowers h) := hE2.to_le (zpowers_le.mpr hh.1)
    exact heR (mul_mem (mem_of_mem_centralizer_of_isPGroup hR hh.2 hK h2) hr)
  have hh1 : h ≠ 1 := fun h1 => hhK (h1 ▸ one_mem _)
  obtain ⟨S, hS, hhS⟩ := exists_isSylowOf_mem_centerIn c hh.2 (hE.2 h hh.1) hh1
  have hEAS : E ⊓ A ≤ S :=
    le_of_le_sup_centralizer hS inf_le_right (hE2.to_le inf_le_left) fun y hy =>
      mem_sup_centralizer_of_commute c hNZ hS hhS hhK hy.2 (hcomm y hy.1 h hh.1)
  have hcardEA : Nat.card ↥(E ⊓ A) = 16 * Nat.card c.π.ker := by
    have hN : R ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := fun r hr =>
      Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx =>
        mem_centralizer_iff.mp (hRA hr) x hx.2)
    have h1 := card_sup_mul_card_inf hN
    have h2 : E ⊓ A ⊓ R = R ⊓ A :=
      le_antisymm (fun x hx => ⟨hx.2, hx.1.2⟩) (fun x hx => ⟨⟨hRE hx.1, hx.2⟩, hx.1⟩)
    rw [← eq_inf_sup_of_le_sup hRA hRE hEAR, hE64, hR4, h2] at h1
    rw [card_ker_eq_card_inf c hR]
    omega
  have hEA : IsElemAbelian 2 (E ⊓ A) :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2.1 b b.2.1)⟩⟩, fun x hx => hE.2 x hx.1⟩
  have hM : IsElemAbelian 2 (centerIn S ⊔ (E ⊓ A)) :=
    isElemAbelian_sup_of_le_centralizer (isElemAbelian_centerIn c hS) hEA fun z hz =>
      mem_centralizer_iff.mpr fun y hy => mem_centralizer_iff.mp hz.2 y (hEAS hy)
  have hMle := card_le_of_isSylowOf c hS (sup_le inf_le_left hEAS) hM
  have heq : E ⊓ A = centerIn S ⊔ (E ⊓ A) :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardEA]; exact hMle)
  have hZE : centerIn S ≤ E := le_sup_left.trans (heq.ge.trans inf_le_left)
  exact ⟨S, hS, hZE, mul_mem (mem_sup_left hhS) (mem_sup_right hr)⟩

theorem isSylowOf_rightConjugate_of_mem {T K : Subgroup G} (hT : IsSylowOf 2 T K) {a : G}
    (ha : a ∈ K) : IsSylowOf 2 (rightConjugate T a) K := by
  have := AschbacherTheorem3.isSylowOf_rightConjugate hT a
  rwa [AschbacherTheorem3.rightConjugate_eq_of_mem ha] at this

omit [Finite G] in
theorem rightConjugate_centerIn (H : Subgroup G) (a : G) :
    rightConjugate (centerIn H) a = centerIn (rightConjugate H a) := by
  unfold centerIn
  rw [AschbacherTheorem3.rightConjugate_inf, AschbacherTheorem3.rightConjugate_centralizer]

omit [Finite G] in
theorem card_pointsIn_rightConjugate (R V : Subgroup G) (a : G) :
    Nat.card (pointsIn R (rightConjugate V a)) = Nat.card (pointsIn R V) := by
  refine Nat.card_congr
    { toFun := fun Q => ⟨rightConjugate Q.1 a⁻¹, ?_⟩
      invFun := fun Q => ⟨rightConjugate Q.1 a, ?_⟩
      left_inv := fun Q => ?_
      right_inv := fun Q => ?_ }
  · obtain ⟨hQV, x, hx⟩ := Q.2
    refine ⟨?_, x * a⁻¹, by rw [hx, rightConjugate_mul]⟩
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hQV a⁻¹
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
  · obtain ⟨hQV, x, hx⟩ := Q.2
    exact ⟨AschbacherTheorem3.rightConjugate_le_rightConjugate hQV a, x * a,
      by rw [hx, rightConjugate_mul]⟩
  · exact Subtype.ext (show rightConjugate (rightConjugate Q.1 a⁻¹) a = Q.1 by
      rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one])
  · exact Subtype.ext (show rightConjugate (rightConjugate Q.1 a) a⁻¹ = Q.1 by
      rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one])

end Lines

section Partition

theorem ncard_eq_ncard_mul_of_partition {α β : Type*} [Finite α] [Finite β] {X : Set α}
    {I : Set β} {B : β → Set α} {m : ℕ} (hBX : ∀ i ∈ I, B i ⊆ X)
    (hcov : ∀ x ∈ X, ∃ i ∈ I, x ∈ B i)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (hcard : ∀ i ∈ I, (B i).ncard = m) : X.ncard = I.ncard * m := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  have hX : X.toFinset = I.toFinset.biUnion fun i => (B i).toFinset := by
    ext x
    simp only [Set.mem_toFinset, Finset.mem_biUnion]
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := hcov x hx
      exact ⟨i, hi, hxi⟩
    · rintro ⟨i, hi, hxi⟩
      exact hBX i hi hxi
  have hpair : (I.toFinset : Set β).PairwiseDisjoint fun i => (B i).toFinset := by
    intro i hi j hj hij
    rw [Function.onFun, Set.disjoint_toFinset]
    exact hdisj i (by simpa using hi) j (by simpa using hj) hij
  have hsum : ∑ i ∈ I.toFinset, (B i).toFinset.card = ∑ i ∈ I.toFinset, m :=
    Finset.sum_congr rfl fun i hi => by
      rw [← Set.ncard_eq_toFinset_card']
      exact hcard i (Set.mem_toFinset.mp hi)
  rw [Set.ncard_eq_toFinset_card', hX, Finset.card_biUnion hpair, hsum, Finset.sum_const,
    smul_eq_mul, Set.ncard_eq_toFinset_card']

end Partition

section Count

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem isSylowOf_inf_and_inf_eq (hF : Frame G A A R g E F) :
    IsSylowOf 2 ((E ⊔ F) ⊓ A) A ∧ E ⊓ F = centerIn ((E ⊔ F) ⊓ A) ⊔ R := by
  have hRc : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := fun a ha b hb =>
    congrArg Subtype.val (hF.elemR.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hREF, hT, -⟩ := sylow_sup_structure hF.sylowR.le hF.sylowR.isPGroup hF.sylow
  refine ⟨hT, ?_⟩
  rw [hF.inf_eq_center]
  exact centerIn_eq_sup hF.sylowR.le hRc hREF hF.sylow.le

theorem rightConjugate_inf_eq (hF : Frame G A A R g E F) {a : G} (ha : a ∈ A) :
    rightConjugate (E ⊓ F) a = centerIn (rightConjugate ((E ⊔ F) ⊓ A) a) ⊔ R := by
  have hRa : rightConjugate R a = R :=
    (rightConjugate_eq_self_iff R a).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hF.sylowR.le hr) a ha).symm))
  have hsup : rightConjugate (centerIn ((E ⊔ F) ⊓ A) ⊔ R) a =
      rightConjugate (centerIn ((E ⊔ F) ⊓ A)) a ⊔ rightConjugate R a := Subgroup.map_sup _ _ _
  rw [(isSylowOf_inf_and_inf_eq hF).2, hsup, hRa, rightConjugate_centerIn]

theorem inf_rightConjugate_le (h11 : Step11) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) {a₁ a₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hne : rightConjugate (E ⊓ F) a₁ ≠ rightConjugate (E ⊓ F) a₂) :
    rightConjugate (E ⊓ F) a₁ ⊓ rightConjugate (E ⊓ F) a₂ ≤ R := by
  have hstd := hF.base.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hF.base hL
  have hT := (isSylowOf_inf_and_inf_eq hF).1
  rw [rightConjugate_inf_eq hF ha₁, rightConjugate_inf_eq hF ha₂]
  refine inf_le_of_ne c (oddCore_le_center hstd.1.1 hstd.1.2) hF.sylowR
    (isSylowOf_rightConjugate_of_mem hT ha₁) (isSylowOf_rightConjugate_of_mem hT ha₂)
    fun h => hne ?_
  rw [rightConjugate_inf_eq hF ha₁, rightConjugate_inf_eq hF ha₂, h]

theorem exists_line_of_mem (h11 : Step11) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) {e : G} (he : e ∈ E) (heR : e ∉ R) :
    ∃ a ∈ A, rightConjugate (E ⊓ F) a ≤ E ∧ e ∈ rightConjugate (E ⊓ F) a := by
  have hstd := hF.base.hyp.standard
  obtain ⟨c⟩ := l34Cover_of_base h11 hF.base hL
  obtain ⟨S, hS, hZE, heS⟩ := exists_isSylowOf_of_mem c (oddCore_le_center hstd.1.1 hstd.1.2)
    hF.sylowR hF.elemE hF.R_le_E hF.E_le hF.cardE hF.cardR he heR
  obtain ⟨a, ha, hTa⟩ :=
    AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hS (isSylowOf_inf_and_inf_eq hF).1
  have hW : rightConjugate (E ⊓ F) a = centerIn S ⊔ R := by rw [rightConjugate_inf_eq hF ha, hTa]
  exact ⟨a, ha, hW ▸ sup_le hZE hF.R_le_E, hW ▸ heS⟩

theorem exists_line_of_mem_pointsIn {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) {Q : Subgroup G}
    (hQ : Q ∈ pointsIn R E) (hQR : Q ≠ R) : ∃ a ∈ A, rightConjugate (E ⊓ F) a = R ⊔ Q := by
  obtain ⟨hQE, x, rfl⟩ := hQ
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hRc : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := fun a ha b hb =>
    congrArg Subtype.val (hF.elemR.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hx : x ∉ normalizer (A : Set G) := fun hx =>
    hQR (rightConjugate_eq_of_mem_normalizer hF hQE hx)
  have hgc : rightConjugate R x ≤ centralizer (R : Set G) := fun y hy =>
    mem_centralizer_iff.mpr fun r hr => hcommE r (hF.R_le_E hr) y (hQE hy)
  obtain ⟨-, D, hD, -, -, hZD⟩ := exists_sylow_centerIn_eq h11 hE16 hF.base hL hF.sylowR hx hgc
  obtain ⟨hRD, hDA, -⟩ := sylow_sup_structure hF.sylowR.le hF.sylowR.isPGroup hD
  obtain ⟨a, ha, hTa⟩ :=
    AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hDA (isSylowOf_inf_and_inf_eq hF).1
  refine ⟨a, ha, ?_⟩
  rw [rightConjugate_inf_eq hF ha, hTa, ← centerIn_eq_sup hF.sylowR.le hRc hRD hD.le, hZD]

theorem card_pointsIn_eq {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) :
    Nat.card (pointsIn R E) = 1 + 5 * (Nat.card (pointsIn R (E ⊓ F)) - 1) := by
  classical
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  set V := E ⊓ F with hVdef
  set n := Nat.card (pointsIn R V) with hn
  have hRa : ∀ a ∈ A, rightConjugate R a = R := fun a ha =>
    (rightConjugate_eq_self_iff R a).mpr (Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) a ha).symm))
  have hRV : R ≤ V := le_inf hF.R_le_E hF.R_le_F
  set Lines : Set (Subgroup G) := {W | W ≤ E ∧ ∃ a ∈ A, W = rightConjugate V a} with hLines
  have hRW : ∀ W ∈ Lines, R ≤ W := by
    rintro W ⟨-, a, ha, rfl⟩
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hRV a
    rwa [hRa a ha] at h1
  have hWcard : ∀ W ∈ Lines, Nat.card W = 16 := by
    rintro W ⟨-, a, -, rfl⟩
    rw [rightConjugate_card]
    exact card_inf_of_frame hF
  have hWpts : ∀ W ∈ Lines, Nat.card (pointsIn R W) = n := by
    rintro W ⟨-, a, -, rfl⟩
    exact card_pointsIn_rightConjugate R V a
  have hinf : ∀ W₁ ∈ Lines, ∀ W₂ ∈ Lines, W₁ ≠ W₂ → W₁ ⊓ W₂ ≤ R := by
    rintro W₁ ⟨-, a₁, ha₁, rfl⟩ W₂ ⟨-, a₂, ha₂, rfl⟩ hne
    exact inf_rightConjugate_le h11 hF hL ha₁ ha₂ hne
  have hcov : ∀ e ∈ E, e ∉ R → ∃ W ∈ Lines, e ∈ W := by
    intro e he heR
    obtain ⟨a, ha, hWE, heW⟩ := exists_line_of_mem h11 hF hL he heR
    exact ⟨_, ⟨hWE, a, ha, rfl⟩, heW⟩
  have hpts : ∀ Q ∈ pointsIn R E, Q ≠ R → ∃ W ∈ Lines, Q ≤ W := by
    intro Q hQ hQR
    obtain ⟨a, ha, hW⟩ := exists_line_of_mem_pointsIn hE16 h11 hF hL hQ hQR
    exact ⟨_, ⟨hW ▸ sup_le hF.R_le_E hQ.1, a, ha, rfl⟩, hW ▸ le_sup_right⟩
  have hlines : Lines.ncard = 5 := by
    have h := ncard_eq_ncard_mul_of_partition (X := (E : Set G) \ R) (I := Lines)
      (B := fun W => (W : Set G) \ R) (m := 12)
      (fun W hW => Set.sdiff_subset_sdiff_left hW.1)
      (fun e he => by
        obtain ⟨W, hW, heW⟩ := hcov e he.1 he.2
        exact ⟨W, hW, heW, he.2⟩)
      (fun W₁ hW₁ W₂ hW₂ hne => Set.disjoint_left.mpr fun x hx₁ hx₂ =>
        hx₁.2 (hinf W₁ hW₁ W₂ hW₂ hne ⟨hx₁.1, hx₂.1⟩))
      (fun W hW => by
        rw [Set.ncard_sdiff (show (R : Set G) ⊆ W from hRW W hW), ← Nat.card_coe_set_eq,
          ← Nat.card_coe_set_eq]
        change Nat.card W - Nat.card R = 12
        rw [hWcard W hW, hF.cardR])
    rw [Set.ncard_sdiff (show (R : Set G) ⊆ E from hF.R_le_E), ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq] at h
    change Nat.card E - Nat.card R = _ at h
    rw [hF.cardE, hF.cardR] at h
    omega
  have hR : R ∈ pointsIn R E := self_mem_pointsIn hF.R_le_E
  have h := ncard_eq_ncard_mul_of_partition (X := pointsIn R E \ {R}) (I := Lines)
    (B := fun W => pointsIn R W \ {R}) (m := n - 1)
    (fun W hW Q hQ => ⟨⟨hQ.1.1.trans hW.1, hQ.1.2⟩, hQ.2⟩)
    (fun Q hQ => by
      obtain ⟨W, hW, hQW⟩ := hpts Q hQ.1 hQ.2
      exact ⟨W, hW, ⟨hQW, hQ.1.2⟩, hQ.2⟩)
    (fun W₁ hW₁ W₂ hW₂ hne => Set.disjoint_left.mpr fun Q hQ₁ hQ₂ => by
      obtain ⟨⟨hQW₁, x, hx⟩, hQR⟩ := hQ₁
      have hQ : Q ≤ R := (le_inf hQW₁ hQ₂.1.1).trans (hinf W₁ hW₁ W₂ hW₂ hne)
      refine hQR (Subgroup.eq_of_le_of_card_ge hQ ?_)
      rw [hx, rightConjugate_card])
    (fun W hW => by
      rw [Set.ncard_sdiff_singleton_of_mem (self_mem_pointsIn (hRW W hW)), ← Nat.card_coe_set_eq,
        hWpts W hW])
  rw [Set.ncard_sdiff_singleton_of_mem hR, ← Nat.card_coe_set_eq, hlines] at h
  have h1 : 1 ≤ Nat.card (pointsIn R E) := by
    have : Nonempty (pointsIn R E) := ⟨⟨R, hR⟩⟩
    exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  omega

theorem card_pointsIn_eq_six {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) : Nat.card (pointsIn R E) = 6 := by
  rw [card_pointsIn_eq hE16 h11 hF hL, h2]

theorem inf_sup_eq_bot_of_card_two {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (h2 : Nat.card (pointsIn R (E ⊓ F)) = 2) {P Q : Subgroup G} (hP : P ∈ pointsIn R E)
    (hQ : Q ∈ pointsIn R E) (hPR : P ≠ R) (hQR : Q ≠ R) (hPQ : P ≠ Q) : P ⊓ (R ⊔ Q) = ⊥ := by
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨a, ha, haP⟩ := exists_line_of_mem_pointsIn hE16 h11 hF hL hP hPR
  obtain ⟨b, hb, hbQ⟩ := exists_line_of_mem_pointsIn hE16 h11 hF hL hQ hQR
  by_cases hab : rightConjugate (E ⊓ F) a = rightConjugate (E ⊓ F) b
  ·
    exfalso
    set W := rightConjugate (E ⊓ F) a
    have hW : Nat.card (pointsIn R W) = 2 := by rw [card_pointsIn_rightConjugate, h2]
    have hsub : ({R, P, Q} : Set (Subgroup G)) ⊆ pointsIn R W := by
      rintro X (rfl | rfl | rfl)
      · exact ⟨haP ▸ le_sup_left, 1, (rightConjugate_one _).symm⟩
      · exact ⟨haP ▸ le_sup_right, hP.2⟩
      · exact ⟨hab ▸ hbQ ▸ le_sup_right, hQ.2⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_insert_of_notMem (by simp [hPR.symm, hQR.symm]), Set.ncard_pair hPQ,
      ← Nat.card_coe_set_eq, hW] at h1
    omega
  · have hle := inf_rightConjugate_le h11 hF hL ha hb hab
    rw [haP, hbQ] at hle
    have h1 : P ⊓ (R ⊔ Q) ≤ R ⊓ P := fun x hx =>
      ⟨hle ⟨mem_sup_right hx.1, hx.2⟩, hx.1⟩
    rw [inf_eq_bot_of_mem_pointsIn hKte hF.sylowR hcommE (self_mem_pointsIn hF.R_le_E) hP
      hPR.symm] at h1
    exact le_bot_iff.mp h1

end Count

end CFSG.ComponentClassification.AS81
