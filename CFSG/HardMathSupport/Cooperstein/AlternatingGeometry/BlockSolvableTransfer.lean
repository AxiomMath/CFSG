module

public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Subgroup Pointwise CFSG.Open CFSG.QuasithinUnique
open CFSG.AGLEmbedding (Asc81bHyp)

variable {G : Type} [Group G]


theorem exists_mul_of_mem_sup {B S : Subgroup G} (hSB : S ≤ normalizer (B : Set G)) {y : G}
    (hy : y ∈ B ⊔ S) : ∃ s ∈ S, ∃ b ∈ B, y = s * b := by
  have h : y ∈ ((S ⊔ B : Subgroup G) : Set G) := by rw [sup_comm]; exact hy
  rw [coe_mul_of_left_le_normalizer_right S B hSB] at h
  obtain ⟨s, hs, b, hb, rfl⟩ := h
  exact ⟨s, hs, b, hb, rfl⟩

theorem solvable_sup_of_normalizes [Finite G] {B S : Subgroup G} (hSB : S ≤ normalizer (B : Set G))
    (hB : Group.IsSolvable ↥B) (hS : IsPGroup 2 S) : Group.IsSolvable ↥(B ⊔ S) := by
  set Y := B ⊔ S with hY
  have hBY : B ≤ Y := le_sup_left
  have hSY : S ≤ Y := le_sup_right
  have hYN : Y ≤ normalizer (B : Set G) := sup_le le_normalizer hSB
  have hN : (B.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hBY).2 hYN
  have hq : IsPGroup 2 (↥Y ⧸ B.subgroupOf Y) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨s, hs, b, hb, hsb⟩ := exists_mul_of_mem_sup hSB y.2
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hmk : (QuotientGroup.mk y : ↥Y ⧸ B.subgroupOf Y) = QuotientGroup.mk ⟨s, hSY hs⟩ := by
      rw [QuotientGroup.eq]
      refine (mem_subgroupOf).2 ?_
      simp only [InvMemClass.coe_inv, Subgroup.coe_mul, hsb]
      simpa [mul_assoc] using B.inv_mem hb
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨s, hSY hs⟩ : ↥Y) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this]; rfl
  have : Finite ↥Y := inferInstance
  have : Group.IsNilpotent (↥Y ⧸ B.subgroupOf Y) := hq.isNilpotent
  have : Group.IsSolvable (↥Y ⧸ B.subgroupOf Y) := inferInstance
  have : Group.IsSolvable ↥(B.subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hBY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBY).injective
  exact Group.isSolvable_of_ker_le_range (B.subgroupOf Y).subtype (QuotientGroup.mk' (B.subgroupOf Y))
    (by simp)

theorem index_sup_eq [Finite G] {B S : Subgroup G} (hSB : S ≤ normalizer (B : Set G)) :
    (S.subgroupOf (B ⊔ S)).index = ((S ⊓ B).subgroupOf B).index := by
  set Y := B ⊔ S with hY
  have hBY : B ≤ Y := le_sup_left
  let f : ↥B ⧸ ((S ⊓ B).subgroupOf B) → ↥Y ⧸ S.subgroupOf Y :=
    Quotient.map' (fun b : ↥B => (⟨b.1, hBY b.2⟩ : ↥Y)) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      have h1 : ((a⁻¹ * b : ↥B) : G) ∈ S ⊓ B := hab
      exact (mem_subgroupOf).2 h1.1)
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have h := QuotientGroup.eq.1 hxy
    have h1 : ((a : G))⁻¹ * (b : G) ∈ S := (mem_subgroupOf).1 h
    refine QuotientGroup.eq.2 ((mem_subgroupOf).2 ⟨h1, ?_⟩)
    exact B.mul_mem (B.inv_mem a.2) b.2
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hy : (y : G)⁻¹ ∈ B ⊔ S := Y.inv_mem y.2
    obtain ⟨s, hs, b, hb, hsb⟩ := exists_mul_of_mem_sup hSB hy
    refine ⟨QuotientGroup.mk ⟨b⁻¹, B.inv_mem hb⟩, ?_⟩
    show (QuotientGroup.mk (⟨b⁻¹, hBY (B.inv_mem hb)⟩ : ↥Y) : ↥Y ⧸ S.subgroupOf Y) = _
    rw [QuotientGroup.eq]
    refine (mem_subgroupOf).2 ?_
    have hy' : (y : G) = b⁻¹ * s⁻¹ := by
      rw [← inv_inv (y : G), hsb]; group
    simp only [InvMemClass.coe_inv, Subgroup.coe_mul]
    rw [hy']
    simpa [mul_assoc] using S.inv_mem hs
  rw [Subgroup.index, Subgroup.index]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem isSylowTwoOf_sup [Finite G] {B S : Subgroup G} (hSB : S ≤ normalizer (B : Set G))
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ ((S ⊓ B).subgroupOf B).index) :
    IsPGroup 2 S ∧ ¬ 2 ∣ (S.subgroupOf (B ⊔ S)).index := by
  rw [index_sup_eq hSB]; exact ⟨hS, hodd⟩


theorem mem_mul_of_three_pow [Finite G] {Q B S R : Subgroup G}
    (hSB : S ≤ normalizer (B : Set G)) (hS : IsPGroup 2 S) {k : ℕ}
    (hpow : ∀ r ∈ R, r ^ (3 ^ k) ∈ Q) (hRY : R ≤ B ⊔ S) {r : G} (hr : r ∈ R) :
    ∃ q ∈ Q, ∃ b ∈ B, r = q * b := by
  set Y := B ⊔ S with hY
  have hBY : B ≤ Y := le_sup_left
  have hSY : S ≤ Y := le_sup_right
  have hYN : Y ≤ normalizer (B : Set G) := sup_le le_normalizer hSB
  have hN : (B.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hBY).2 hYN
  obtain ⟨s, hs, b, hb, hsb⟩ := exists_mul_of_mem_sup hSB (hRY hr)
  obtain ⟨a, ha⟩ := hS ⟨s, hs⟩
  set y : ↥Y := ⟨r, hRY hr⟩ with hy
  have hmk : (QuotientGroup.mk y : ↥Y ⧸ B.subgroupOf Y) = QuotientGroup.mk ⟨s, hSY hs⟩ := by
    rw [QuotientGroup.eq]
    refine (mem_subgroupOf).2 ?_
    simp only [hy, InvMemClass.coe_inv, Subgroup.coe_mul, hsb]
    simpa [mul_assoc] using B.inv_mem hb
  have h2 : (QuotientGroup.mk y : ↥Y ⧸ B.subgroupOf Y) ^ (2 ^ a) = 1 := by
    rw [hmk, ← QuotientGroup.mk_pow]
    have : (⟨s, hSY hs⟩ : ↥Y) ^ (2 ^ a) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val ha
      simpa using this
    rw [this]; rfl
  set q : G := r ^ (3 ^ k) with hq
  have hqQ : q ∈ Q := hpow r hr
  have hqY : q ∈ Y := Y.pow_mem (hRY hr) _
  have h3 : (QuotientGroup.mk y : ↥Y ⧸ B.subgroupOf Y) ^ (3 ^ k) = QuotientGroup.mk ⟨q, hqY⟩ := by
    rw [← QuotientGroup.mk_pow]
    rfl
  have hcop : IsCoprime ((3 ^ k : ℕ) : ℤ) ((2 ^ a : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow _ _ (by norm_num))
  obtain ⟨u, v, huv⟩ := hcop
  have hz : (QuotientGroup.mk y : ↥Y ⧸ B.subgroupOf Y) =
      (QuotientGroup.mk ⟨q, hqY⟩ : ↥Y ⧸ B.subgroupOf Y) ^ u := by
    calc (QuotientGroup.mk y : ↥Y ⧸ B.subgroupOf Y)
        = (QuotientGroup.mk y) ^ (((3 ^ k : ℕ) : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v) := by
          rw [show ((3 ^ k : ℕ) : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v = 1 by linarith, zpow_one]
      _ = ((QuotientGroup.mk y) ^ (3 ^ k)) ^ u * ((QuotientGroup.mk y) ^ (2 ^ a)) ^ v := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = _ := by rw [h3, h2, one_zpow, mul_one]
  have hq' : ((⟨q, hqY⟩ : ↥Y) ^ u : ↥Y) = ⟨q ^ u, Y.zpow_mem hqY u⟩ := by
    apply Subtype.ext; simp
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, hq'] at hz
  have hb' := (mem_subgroupOf).1 hz
  refine ⟨q ^ u, Q.zpow_mem hqQ u, (q ^ u)⁻¹ * r, ?_, by group⟩
  have hb'' := B.inv_mem hb'
  simpa [hy] using hb''


theorem eq_of_normal_three [Finite G] {Q B S R : Subgroup G}
    (hSB : S ≤ normalizer (B : Set G)) (hS : IsPGroup 2 S)
    (hQN : B ⊔ S ≤ normalizer (Q : Set G)) (hQR : Q ≤ R) (hRY : R ≤ B ⊔ S)
    (hRn : ∀ y ∈ B ⊔ S, ∀ r ∈ R, y * r * y⁻¹ ∈ R) (hk : ∃ k : ℕ, Q.relIndex R = 3 ^ k)
    (hB3 : ∀ R' : Subgroup G, R' ≤ B → (∀ b ∈ B, ∀ r ∈ R', b * r * b⁻¹ ∈ R') →
      (∀ r ∈ R', ∃ m : ℕ, r ^ (3 ^ m) ∈ Q) → R' ≤ Q) : R = Q := by
  obtain ⟨k, hk⟩ := hk
  have hQnR : (Q.subgroupOf R).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQR).2 fun r hr => hQN (hRY hr)
  have hpow : ∀ r ∈ R, r ^ (3 ^ k) ∈ Q := by
    intro r hr
    have h1 : (QuotientGroup.mk (⟨r, hr⟩ : ↥R) : ↥R ⧸ Q.subgroupOf R) ^ (3 ^ k) = 1 := by
      rw [← hk]
      exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact (mem_subgroupOf).1 h1
  have hR' : (R ⊓ B) ≤ Q := by
    refine hB3 (R ⊓ B) inf_le_right (fun b hb r hr => ⟨?_, ?_⟩) (fun r hr => ⟨k, hpow r hr.1⟩)
    · exact hRn b (Subgroup.mem_sup_left hb) r hr.1
    · exact B.mul_mem (B.mul_mem hb hr.2) (B.inv_mem hb)
  refine le_antisymm (fun r hr => ?_) hQR
  obtain ⟨q, hq, b, hb, rfl⟩ := mem_mul_of_three_pow hSB hS hpow hRY hr
  have hbR : b ∈ R := by
    have := R.mul_mem (R.inv_mem (hQR hq)) hr
    simpa using this
  exact Q.mul_mem hq (hR' ⟨hbR, hb⟩)

@[expose] def SolvableSylowNormalizer (X S : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, pCoreOf 2 X ≤ Y → Y ≤ X → Group.IsSolvable ↥Y → IsSylowTwoOf S Y →
    (∀ R : Subgroup G, pCoreOf 2 X ≤ R → R ≤ Y → (∀ y ∈ Y, ∀ r ∈ R, y * r * y⁻¹ ∈ R) →
      (∃ k : ℕ, (pCoreOf 2 X).relIndex R = 3 ^ k) → R = pCoreOf 2 X) →
    Y ≤ Subgroup.normalizer (S : Set G)

theorem blockTransfer [Finite G] {X S B : Subgroup G} (hA : Asc81bHyp X S) (hBX : B ≤ X)
    (hSB : S ≤ normalizer (B : Set G)) (hsolv : Group.IsSolvable ↥B)
    (hSyl : IsSylowTwoOf (S ⊓ B) B)
    (hB3 : ∀ R' : Subgroup G, R' ≤ B → (∀ b ∈ B, ∀ r ∈ R', b * r * b⁻¹ ∈ R') →
      (∀ r ∈ R', ∃ m : ℕ, r ^ (3 ^ m) ∈ pCoreOf 2 X) → R' ≤ pCoreOf 2 X)
    (hLB : SolvableSylowNormalizer X S) : B ≤ Subgroup.normalizer (S : Set G) := by
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hSX : S ≤ X := hA.twoRadical.1
  have hQS : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hQY : pCoreOf 2 X ≤ B ⊔ S := hQS.trans le_sup_right
  have hYX : B ⊔ S ≤ X := sup_le hBX hSX
  have hQN : B ⊔ S ≤ normalizer (pCoreOf 2 X : Set G) := fun y hy =>
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X (hYX hy)
  have hSyl' := isSylowTwoOf_sup hSB hS2 hSyl.2.2
  have hY := hLB (B ⊔ S) hQY hYX (solvable_sup_of_normalizes hSB hsolv hS2)
    ⟨le_sup_right, hSyl'.1, hSyl'.2⟩ (fun R hQR hRY hRn hk =>
      eq_of_normal_three hSB hS2 hQN hQR hRY hRn hk hB3)
  exact le_sup_left.trans hY


end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
