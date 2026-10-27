module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_inf_centralizer_mul_of_coprime {M N S : Subgroup G} (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set G)) (hSM : S ≤ normalizer (M : Set G))
    (hSN : S ≤ normalizer (N : Set G)) (hsolv : Group.IsSolvable M)
    (hcop : (Nat.card S).Coprime (Nat.card M)) {m : G} (hm : m ∈ M)
    (hfix : ∀ s ∈ S, m⁻¹ * (s * m * s⁻¹) ∈ N) :
    ∃ c ∈ M ⊓ centralizer (S : Set G), ∃ n ∈ N, m = c * n := by
  let : MulDistribMulAction S M := Subgroup.conjMulDistribMulActionOfLeNormalizer S M hSM
  set H : Subgroup M := N.subgroupOf M with hH
  have : H.Normal := (normal_subgroupOf_iff_le_normalizer hNM).2 hMN
  have hinv : IsInvariant S M H := ⟨fun a g => by
    rw [hH, mem_subgroupOf, mem_subgroupOf]
    change (g : G) ∈ N ↔ (a : G) * g * (a : G)⁻¹ ∈ N
    exact mem_normalizer_iff.1 (hSN a.2) g⟩
  have key := CFSG.fixedPointSubgroup_quotient_eq_map_of_solvable_coprime (G := M) (A := S)
    hsolv hcop H hinv
  let : MulDistribMulAction S (M ⧸ H) := CFSG.quotientMulDistribMulAction H hinv
  let : MulAction.QuotientAction S H := CFSG.quotientAction_of_isInvariant H hinv
  have hmem : (QuotientGroup.mk' H ⟨m, hm⟩ : M ⧸ H) ∈ CFSG.fixedPointSubgroup S (M ⧸ H) := by
    intro a
    change a • ((⟨m, hm⟩ : M) : M ⧸ H) = ((⟨m, hm⟩ : M) : M ⧸ H)
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, mem_subgroupOf]
    change ((a : G) * m * (a : G)⁻¹)⁻¹ * m ∈ N
    have := inv_mem (hfix a a.2)
    rwa [mul_inv_rev, inv_inv] at this
  rw [key] at hmem
  obtain ⟨c, hc, hce⟩ := hmem
  have hcS : ∀ a : S, (a : G) * (c : G) * (a : G)⁻¹ = c := fun a =>
    congrArg Subtype.val (hc a)
  have hcn : (c : G)⁻¹ * m ∈ N := by
    have := QuotientGroup.eq.1 hce
    rwa [mem_subgroupOf] at this
  refine ⟨c, mem_inf.2 ⟨c.2, mem_centralizer_iff.2 fun s hs => ?_⟩, _, hcn, by group⟩
  have e := hcS ⟨s, hs⟩
  calc s * (c : G) = s * (c : G) * s⁻¹ * s := by group
    _ = (c : G) * s := by rw [e]

theorem exists_mem_forall_conj_mem_of_isPGroup {p : ℕ} [Fact p.Prime] {R H N : Subgroup G}
    (hR : IsPGroup p R) (hH : IsPGroup p H) (hNH : N ≤ H) (hne : ¬ H ≤ N)
    (hRH : R ≤ normalizer (H : Set G)) (hRN : R ≤ normalizer (N : Set G))
    (hHN : H ≤ normalizer (N : Set G)) :
    ∃ x ∈ H, x ∉ N ∧ ∀ r ∈ R, x⁻¹ * (r * x * r⁻¹) ∈ N := by
  set X : Subgroup G := R ⊔ H with hX
  have hX2 : IsPGroup p X := IsPGroup.to_sup_of_normal_right' hR hH hRH
  have hNX : N ≤ X := hNH.trans le_sup_right
  have hHX : H ≤ X := le_sup_right
  set N' : Subgroup X := N.subgroupOf X with hN'
  have : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNX).2 (sup_le hRN hHN)
  have hHn : (H.subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hHX).2 (sup_le hRH le_normalizer)
  set π := QuotientGroup.mk' N' with hπ
  set H' : Subgroup (X ⧸ N') := (H.subgroupOf X).map π with hH'
  have : H'.Normal := hHn.map π (QuotientGroup.mk'_surjective N')
  have hQ2 : IsPGroup p (X ⧸ N') := hX2.to_quotient N'
  have : Group.IsNilpotent (X ⧸ N') := hQ2.isNilpotent
  have hH'ne : H' ≠ ⊥ := by
    intro hbot
    apply hne
    intro x hx
    have : π ⟨x, hHX hx⟩ ∈ H' := ⟨⟨x, hHX hx⟩, mem_subgroupOf.2 hx, rfl⟩
    rw [hbot, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      at this
    exact this
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH'ne)
  obtain ⟨hyH, hyZ⟩ := mem_inf.1 hy
  obtain ⟨x, hxH, hxy⟩ := hyH
  refine ⟨x, mem_subgroupOf.1 hxH, fun hxN => hy1 ?_, fun r hr => ?_⟩
  · have hy1' : y = 1 := by
      rw [← hxy, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hxN
    exact Subtype.ext hy1'
  · set r' : X := ⟨r, le_sup_left (a := R) hr⟩
    have hc := mem_center_iff.1 hyZ (π r')
    rw [← hxy] at hc
    have e : π (r' * x * r'⁻¹) = π x := by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf] at e
    have e' : ((x : X)⁻¹ * (r' * x * r'⁻¹) : X) = (x : G)⁻¹ * (r * x * r⁻¹) := by
      simp [r']
    rw [← e']
    have := inv_mem e
    simpa [mul_assoc] using this

theorem mem_of_mem_commutator_sup_of_fixed {A Y Z : Subgroup G} (hZY : Z ≤ Y)
    (hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' * y⁻¹ * y'⁻¹ ∈ Z)
    (hAY : A ≤ normalizer (Y : Set G)) (hAZ : A ≤ normalizer (Z : Set G))
    (hcop : (Nat.card A).Coprime (Nat.card Y)) {x : G} (hx : x ∈ ⁅A, Y⁆ ⊔ Z)
    (hfix : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Z) : x ∈ Z := by
  let : MulDistribMulAction A Y := Subgroup.conjMulDistribMulActionOfLeNormalizer A Y hAY
  set H : Subgroup Y := Z.subgroupOf Y with hH
  have hYZ : Y ≤ normalizer (Z : Set G) := by
    intro y hy
    refine mem_normalizer_fintype fun z hz => ?_
    have := hcomm y hy z (hZY hz)
    have e : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
    rw [e]
    exact mul_mem this hz
  have : H.Normal := (normal_subgroupOf_iff_le_normalizer hZY).2 hYZ
  have hinv : IsInvariant A Y H := ⟨fun a g => by
    rw [hH, mem_subgroupOf, mem_subgroupOf]
    change (g : G) ∈ Z ↔ (a : G) * g * (a : G)⁻¹ ∈ Z
    exact mem_normalizer_iff.1 (hAZ a.2) g⟩
  let : MulDistribMulAction A (Y ⧸ H) := CFSG.quotientMulDistribMulAction H hinv
  let : MulAction.QuotientAction A H := CFSG.quotientAction_of_isInvariant H hinv
  have hcommQ : IsMulCommutative (Y ⧸ H) := ⟨⟨fun u v => by
    induction u using QuotientGroup.induction_on with | H y => ?_
    induction v using QuotientGroup.induction_on with | H y' => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have := hcomm y'⁻¹ (inv_mem y'.2) y⁻¹ (inv_mem y.2)
    simpa [mul_assoc] using this⟩⟩
  have hsolv : Group.IsSolvable (Y ⧸ H) := by
    have := hcommQ
    infer_instance
  have hcopQ : (Nat.card A).Coprime (Nat.card (Y ⧸ H)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card H) hcop
  have hcompl :=
    CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := Y ⧸ H) (A := A) hsolv hcopQ hcommQ
  have hxY : x ∈ Y := sup_le (commutator_le.2 fun a ha y hy => by
    rw [commutatorElement_def]
    exact mul_mem ((mem_normalizer_iff.1 (hAY ha) y).1 hy) (inv_mem hy)) hZY hx
  set xb : Y ⧸ H := ((⟨x, hxY⟩ : Y) : Y ⧸ H)
  have hfixb : xb ∈ CFSG.fixedPointSubgroup A (Y ⧸ H) := by
    intro a
    change a • ((⟨x, hxY⟩ : Y) : Y ⧸ H) = ((⟨x, hxY⟩ : Y) : Y ⧸ H)
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, mem_subgroupOf]
    change ((a : G) * x * (a : G)⁻¹)⁻¹ * x ∈ Z
    have h1 := (mem_normalizer_iff.1 (inv_mem (hYZ hxY)) _).1 (inv_mem (hfix a a.2))
    have e : ((a : G) * x * (a : G)⁻¹)⁻¹ * x =
        x⁻¹ * ((a : G) * x * (a : G)⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact h1
  set W : Subgroup G :=
    ((CFSG.commutatorAction A (Y ⧸ H)).comap (QuotientGroup.mk' H)).map Y.subtype with hW
  have hle : ⁅A, Y⁆ ⊔ Z ≤ W := by
    refine sup_le (commutator_le.2 fun a ha y hy => ?_) fun z hz => ?_
    · have hyc : (a : G) * y * (a : G)⁻¹ ∈ Y := (mem_normalizer_iff.1 (hAY ha) y).1 hy
      have hmem : (a : G) * y * (a : G)⁻¹ * y⁻¹ ∈ Y := mul_mem hyc (inv_mem hy)
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      have hgen : (((⟨y, hy⟩ : Y) : Y ⧸ H))⁻¹ * ((⟨a, ha⟩ : A) • ((⟨y, hy⟩ : Y) : Y ⧸ H)) ∈
          CFSG.commutatorAction A (Y ⧸ H) :=
        Subgroup.subset_closure ⟨⟨a, ha⟩, _, mem_top _, rfl⟩
      have e : QuotientGroup.mk' H ⟨_, hmem⟩ =
          (((⟨y, hy⟩ : Y) : Y ⧸ H))⁻¹ * ((⟨a, ha⟩ : A) • ((⟨y, hy⟩ : Y) : Y ⧸ H)) := by
        rw [MulAction.Quotient.smul_coe, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq, mem_subgroupOf]
        change ((a : G) * y * (a : G)⁻¹ * y⁻¹)⁻¹ * (y⁻¹ * ((a : G) * y * (a : G)⁻¹)) ∈ Z
        have e : ((a : G) * y * (a : G)⁻¹ * y⁻¹)⁻¹ * (y⁻¹ * ((a : G) * y * (a : G)⁻¹)) =
            y * ((a : G) * y * (a : G)⁻¹)⁻¹ * y⁻¹ * ((a : G) * y * (a : G)⁻¹)⁻¹⁻¹ := by group
        rw [e]
        exact hcomm y hy _ (inv_mem hyc)
      rw [e]
      exact hgen
    · refine ⟨⟨z, hZY hz⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      have : QuotientGroup.mk' H ⟨z, hZY hz⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact hz
      rw [this]
      exact one_mem _
  obtain ⟨y, hyc, hyx⟩ := hle hx
  have hxbc : xb ∈ CFSG.commutatorAction A (Y ⧸ H) := by
    have e : y = ⟨x, hxY⟩ := Subtype.ext hyx
    rw [SetLike.mem_coe, mem_comap, e] at hyc
    exact hyc
  have hbot := (hcompl.disjoint.le_bot) (mem_inf.2 ⟨hfixb, hxbc⟩)
  rw [mem_bot] at hbot
  have := QuotientGroup.eq_one_iff (N := H) (⟨x, hxY⟩ : Y) |>.1 hbot
  exact mem_subgroupOf.1 this

omit [Finite G] in
theorem card_sup_mul_card_inf_eq {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have hnorm : ∀ (X : Subgroup N) (Y : Subgroup N) [Y.Normal],
      Nat.card (X ⊔ Y : Subgroup N) * Nat.card (X ⊓ Y : Subgroup N) = Nat.card X * Nat.card Y := by
    intro X Y _
    have h1 := Subgroup.relIndex_mul_card (H := Y) (K := X ⊔ Y)
    have h2 := Subgroup.relIndex_mul_card (H := Y) (K := X)
    rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : Y ≤ X ⊔ Y)] at h1
    rw [inf_comm] at h2
    rw [← h1, ← h2]
    ring
  have h := hnorm (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ Y : Subgroup G, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

end CFSG.LocalAnalysis.EvenBN.Common
