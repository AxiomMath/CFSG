module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofA7M22
public import CFSG.RankThree.PartTwo.Sec10.Item1012Res2ProofTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaSimple

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open Res417Three
open scoped Pointwise

theorem nine_twentyseven_of_dvd {k m : ℕ} (hm : m ∣ 27) (hkm : k ∣ m) (h9 : 9 ∣ k)
    (hne : k ≠ m) : k = 9 ∧ m = 27 := by
  have hm27 : m ≤ 27 := Nat.le_of_dvd (by norm_num) hm
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hm)
  have hkm' : k ≤ m := Nat.le_of_dvd hm0 hkm
  obtain ⟨j, rfl⟩ := h9
  have hj : j ≤ 3 := by omega
  interval_cases m <;> interval_cases j <;> omega

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {c : G}

theorem isHeisCentral_and_autIn (hLp : Group.IsPerfect L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) (hc3 : orderOf c = 3)
    (hcL : c ∈ L) (hcZ : (⟨c, hcL⟩ : L) ∈ Subgroup.center L)
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹)
    (hS27 : ¬ 27 ∣ Nat.card (L ⧸ Subgroup.center L))
    (hinv : ∀ P : Subgroup (L ⧸ Subgroup.center L), Nat.card P = 9 →
      ∃ g : L ⧸ Subgroup.center L, ∀ x ∈ P, g * x * g⁻¹ = x⁻¹)
    (hcent : ∀ P : Subgroup (L ⧸ Subgroup.center L), Nat.card P = 9 →
      Subgroup.centralizer (P : Set (L ⧸ Subgroup.center L)) ≤ P) :
    IsHeisCentral ↥(A ⊔ L) ↥L ∧ CFSG.Assembly.IsElemAbelian 3 (autIn L A) ∧
      Nat.card (autIn L A) = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect L := hLp
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hAc]; exact Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcAC.1
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := hcAC.2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLC : L ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hcL, hcC⟩) ?_
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective L.subtype_injective, hZ, Nat.card_zpowers, hc3]
  obtain ⟨v, hv1, hv2⟩ : ∃ v : A → L, (∀ a : A, ∀ x ∈ L,
      (a : G) * x * (a : G)⁻¹ = (v a : G) * x * (v a : G)⁻¹) ∧
      ∀ a, innerHom hinner a = (v a : L ⧸ Subgroup.center L) :=
    ⟨innerRep hinner, innerRep_spec hinner, innerHom_apply hinner⟩
  have hR9 : Nat.card (innerHom hinner).range = 9 := by
    have h1 := card_range_innerHom_mul hinner
    rw [hAc, Nat.card_zpowers, hc3, hA27] at h1
    omega
  set ρ := innerHom hinner with hρ
  have hv3Z : ∀ a : A, v a ^ 3 ∈ Subgroup.center L := by
    intro a
    have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hAel.2 a a.2)
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hv2, ← map_pow, ha3, map_one]
  obtain ⟨g₀, hg₀⟩ := hinv ρ.range hR9
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g₀
  have hv3 : ∀ a : A, v a ^ 3 = 1 := by
    intro a
    refine pow_three_eq_one_of_inv hZ (hv3Z a) (g := g) ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      ← hv2]
    exact hg₀ _ ⟨a, rfl⟩
  have hdec : ∀ a ∈ A, ∃ w : L, (w : G) ^ 3 = 1 ∧ a * w = w * a ∧
      a * (w : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    refine ⟨v ⟨a, ha⟩, by simpa using congrArg Subtype.val (hv3 ⟨a, ha⟩), ?_, ?_⟩
    · have h1 := hv1 ⟨a, ha⟩ _ (v ⟨a, ha⟩).2
      have h2 : a * (v ⟨a, ha⟩ : G) * a⁻¹ = v ⟨a, ha⟩ := by
        rw [h1, mul_inv_cancel_right]
      calc a * (v ⟨a, ha⟩ : G) = a * (v ⟨a, ha⟩ : G) * a⁻¹ * a := by group
        _ = (v ⟨a, ha⟩ : G) * a := by rw [h2]
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (v ⟨a, ha⟩ : G)⁻¹ * x * v ⟨a, ha⟩ ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem (v ⟨a, ha⟩).2) hx) (v ⟨a, ha⟩).2
      have h1 := hv1 ⟨a, ha⟩ _ hx'
      have h2 : a * ((v ⟨a, ha⟩ : G)⁻¹ * x * v ⟨a, ha⟩) * a⁻¹ = x := by
        rw [h1]; group
      calc x * (a * (v ⟨a, ha⟩ : G)⁻¹) =
          a * ((v ⟨a, ha⟩ : G)⁻¹ * x * v ⟨a, ha⟩) * a⁻¹ * (a * (v ⟨a, ha⟩ : G)⁻¹) := by
            rw [h2]
        _ = a * (v ⟨a, ha⟩ : G)⁻¹ * x := by group
  have hnc : ∃ a b : A, (v a : G) * v b ≠ v b * v a := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    set f := QuotientGroup.mk' (Subgroup.center L) with hf
    set Pt := ρ.range.comap f with hPt
    have hR3 : IsPGroup 3 ρ.range := IsPGroup.of_card (n := 2) (by rw [hR9]; norm_num)
    have hK3 : IsPGroup 3 f.ker := by
      rw [hf, QuotientGroup.ker_mk']
      exact IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
    obtain ⟨P, hP⟩ := (hR3.comap_of_ker_isPGroup f hK3).exists_le_sylow
    have hle1 : ρ.range ≤ (P : Subgroup L).map f := by
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) ρ.range]
      exact Subgroup.map_mono hP
    have hcardle : Nat.card ((P : Subgroup L).map f) ≤ Nat.card ρ.range := by
      obtain ⟨k, hk⟩ := (P.isPGroup'.map f).exists_card_eq
      have hdvd := Subgroup.card_subgroup_dvd_card ((P : Subgroup L).map f)
      rw [hk] at hdvd ⊢
      rw [hR9]
      by_contra hlt
      have hk3 : 3 ≤ k := by
        by_contra hk3
        have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact hS27 ((Nat.pow_dvd_pow 3 hk3).trans hdvd)
    have heq := Subgroup.eq_of_le_of_card_ge hle1 hcardle
    have hPle : (P : Subgroup L) ≤ Pt := by
      rw [hPt, heq]
      exact Subgroup.le_comap_map f _
    have hrep : ∀ x ∈ (P : Subgroup L), ∃ a : A, ∃ z ∈ Subgroup.center L, x = v a * z := by
      intro x hx
      obtain ⟨a, ha⟩ := hPle hx
      refine ⟨a, (v a)⁻¹ * x, ?_, by group⟩
      rw [← QuotientGroup.eq]
      rw [hv2] at ha
      exact ha
    have hPc : ∀ x ∈ (P : Subgroup L), ∀ y ∈ (P : Subgroup L), x * y = y * x := by
      intro x hx y hy
      obtain ⟨a, z, hz, rfl⟩ := hrep x hx
      obtain ⟨b, z', hz', rfl⟩ := hrep y hy
      have hab : v a * v b = v b * v a := Subtype.ext (hall a b)
      have hz1 := Subgroup.mem_center_iff.mp hz
      have hz2 := Subgroup.mem_center_iff.mp hz'
      calc v a * z * (v b * z') = v a * (z * v b) * z' := by group
        _ = v a * (v b * z) * z' := by rw [hz1]
        _ = v a * v b * (z * z') := by group
        _ = v b * v a * (z' * z) := by rw [hab, hz1 z']
        _ = v b * (v a * z') * z := by group
        _ = v b * (z' * v a) * z := by rw [hz2]
        _ = v b * z' * (v a * z) := by group
    have hcP : (⟨c, hcL⟩ : L) ∈ (P : Subgroup L) := hP (by
      rw [Subgroup.mem_comap, hf, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr hcZ]
      exact one_mem _)
    have hmem := CFSG.ShultStronglyClosedTI.central_element_mem_sylow_derived P
      ⟨⟨c, hcL⟩, hcP⟩ hcZ
    have hbot : commutator (P : Subgroup L) = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subtype.ext (hPc y y.2 x x.2)
    rw [hbot, Subgroup.mem_bot] at hmem
    have hc1 : c = 1 := congrArg Subtype.val (congrArg Subtype.val hmem)
    rw [hc1, orderOf_one] at hc3
    omega
  set U : Subgroup G := (A ⊔ L) ⊓ Subgroup.centralizer (L : Set G) with hU
  have hUL : U ⊔ L = A ⊔ L := by
    apply le_antisymm (sup_le inf_le_left le_sup_right)
    refine sup_le (fun a ha => ?_) le_sup_right
    obtain ⟨w, -, -, hwC⟩ := hdec a ha
    have haw : a * (w : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (inv_mem w.2)), hwC⟩
    have : a = a * (w : G)⁻¹ * w := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left haw) (Subgroup.mem_sup_right w.2)
  have hUinf : U ⊓ L = Subgroup.zpowers c := by
    rw [← hLC]
    ext x
    simp only [Subgroup.mem_inf, hU]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨⟨Subgroup.mem_sup_right h2, h1⟩, h2⟩
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨huAL, huC⟩ := Subgroup.mem_inf.mp hu
    have hmul : u ∈ (A : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A L hAN]
      exact huAL
    obtain ⟨a, ha, l, hl, hu'⟩ := hmul
    have hu'' : u = a * l := hu'.symm
    subst hu''
    obtain ⟨w, hw3, hwa, hwC⟩ := hdec a ha
    have hwl : (w : G) * l ∈ Subgroup.zpowers c := by
      rw [← hLC]
      refine Subgroup.mem_inf.mpr ⟨mul_mem w.2 hl, ?_⟩
      have : (w : G) * l = (a * (w : G)⁻¹)⁻¹ * (a * l) := by group
      rw [this]
      exact mul_mem (inv_mem hwC) huC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwl
    have hal : a * l = (a * (w : G)⁻¹) * c ^ k := by rw [hk]; group
    rw [hal]
    have hca : Commute c a := hAcomm c hcA a ha
    have hcw : Commute c (w : G) := (Subgroup.mem_centralizer_iff.mp hcC w w.2).symm
    have hc1 : Commute (a * (w : G)⁻¹) (c ^ k) :=
      ((hca.mul_right hcw.inv_right).symm).zpow_right k
    have hc2 : Commute a (w : G)⁻¹ := Commute.inv_right hwa
    rw [hc1.mul_pow, hc2.mul_pow, hAel.2 a ha, inv_pow, hw3, inv_one, one_mul, one_mul,
      ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc3',
      _root_.one_zpow]
  have hUnc : ¬ ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
    intro hUc
    obtain ⟨a₁, a₂, hv12⟩ := hnc
    have hC : ∀ a : A, (a : G) * (v a : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      intro a
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : (v a : G)⁻¹ * x * v a ∈ L :=
        L.mul_mem (L.mul_mem (L.inv_mem (v a).2) hx) (v a).2
      have h1 := hv1 a _ hx'
      have h2 : (a : G) * ((v a : G)⁻¹ * x * v a) * (a : G)⁻¹ = x := by rw [h1]; group
      calc x * ((a : G) * (v a : G)⁻¹) =
          (a : G) * ((v a : G)⁻¹ * x * v a) * (a : G)⁻¹ * ((a : G) * (v a : G)⁻¹) := by
            rw [h2]
        _ = (a : G) * (v a : G)⁻¹ * x := by group
    have hu₁ : (a₁ : G) * (v a₁ : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left a₁.2) (Subgroup.mem_sup_right (inv_mem (v a₁).2)), hC a₁⟩
    have hu₂ : (a₂ : G) * (v a₂ : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left a₂.2) (Subgroup.mem_sup_right (inv_mem (v a₂).2)), hC a₂⟩
    have hcu := hUc _ hu₁ _ hu₂
    obtain ⟨u₁, hu₁d⟩ : ∃ u, u = (a₁ : G) * (v a₁ : G)⁻¹ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂d⟩ : ∃ u, u = (a₂ : G) * (v a₂ : G)⁻¹ := ⟨_, rfl⟩
    rw [← hu₁d, ← hu₂d] at hcu
    have hu₂v₁ : u₂ * v a₁ = v a₁ * u₂ := by
      rw [hu₂d]
      exact (Subgroup.mem_centralizer_iff.mp (hC a₂) _ (v a₁).2).symm
    have hu₁v₂ : u₁ * v a₂ = v a₂ * u₁ := by
      rw [hu₁d]
      exact (Subgroup.mem_centralizer_iff.mp (hC a₁) _ (v a₂).2).symm
    have ha₁ : (a₁ : G) = u₁ * v a₁ := by rw [hu₁d]; group
    have ha₂ : (a₂ : G) = u₂ * v a₂ := by rw [hu₂d]; group
    apply hv12
    have h1 := hAcomm a₁ a₁.2 a₂ a₂.2
    rw [ha₁, ha₂] at h1
    have h' : u₁ * u₂ * ((v a₁ : G) * v a₂) = u₁ * u₂ * ((v a₂ : G) * v a₁) :=
      calc u₁ * u₂ * ((v a₁ : G) * v a₂) = u₁ * (u₂ * v a₁) * v a₂ := by group
        _ = u₁ * (v a₁ * u₂) * v a₂ := by rw [hu₂v₁]
        _ = u₁ * v a₁ * (u₂ * v a₂) := by group
        _ = u₂ * v a₂ * (u₁ * v a₁) := h1
        _ = u₂ * (v a₂ * u₁) * v a₁ := by group
        _ = u₂ * (u₁ * v a₂) * v a₁ := by rw [hu₁v₂]
        _ = u₂ * u₁ * ((v a₂ : G) * v a₁) := by group
        _ = u₁ * u₂ * ((v a₂ : G) * v a₁) := by rw [hcu]
    exact mul_left_cancel h'
  have hcommUL : ∀ x ∈ U, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hcardUL := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U L hcommUL).1
  rw [hUL, hUinf, Nat.card_zpowers, hc3] at hcardUL
  have hcardAL : Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card A * Nat.card L := by
    have : ((L.subgroupOf (A ⊔ L))).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
    have h1 := card_sup_mul_card_inf_of_normal (A.subgroupOf (A ⊔ L)) (L.subgroupOf (A ⊔ L))
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self,
      Subgroup.card_top, ← inf_subgroupOf,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_left)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ L)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : L ≤ A ⊔ L)).toEquiv] at h1
    exact h1
  rw [hA27] at hcardAL
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have h81 : Nat.card U * Nat.card (A ⊓ L : Subgroup G) = 81 := by
    have h1 : Nat.card U * Nat.card (A ⊓ L : Subgroup G) * Nat.card L = 81 * Nat.card L := by
      calc Nat.card U * Nat.card (A ⊓ L : Subgroup G) * Nat.card L =
          Nat.card U * Nat.card L * Nat.card (A ⊓ L : Subgroup G) := by ring
        _ = Nat.card (A ⊔ L : Subgroup G) * 3 * Nat.card (A ⊓ L : Subgroup G) := by
            rw [hcardUL]
        _ = 3 * (Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G)) := by ring
        _ = 81 * Nat.card L := by rw [hcardAL]; ring
    exact Nat.eq_of_mul_eq_mul_right hLpos h1
  have hAL3 : 3 ∣ Nat.card (A ⊓ L : Subgroup G) := by
    have h1 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩ :
      Subgroup.zpowers c ≤ A ⊓ L)
    rwa [Nat.card_zpowers, hc3] at h1
  have hU27 : Nat.card U = 27 := by
    have hdvd : Nat.card U ∣ 3 ^ 4 := ⟨_, h81.symm⟩
    obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk3 : k ≤ 3 := by
      by_contra hk3
      have hk4' : k = 4 := by omega
      subst hk4'
      rw [hk] at h81
      have := Nat.le_of_dvd (by omega) hAL3
      omega
    have hcomm : k ≤ 2 → ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
      intro hk2 u hu u' hu'
      have hU : IsMulCommutative U := by
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
        · rw [pow_zero] at hk
          have : Subsingleton U := (Nat.card_eq_one_iff_unique.mp hk).1
          exact ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
        · rw [pow_one] at hk
          have := isCyclic_of_prime_card hk
          infer_instance
        · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
      exact congrArg Subtype.val (hU.is_comm.comm ⟨u, hu⟩ ⟨u', hu'⟩)
    rcases (show k ≤ 2 ∨ k = 3 by omega) with hk2 | rfl
    · exact absurd (hcomm hk2) hUnc
    · rw [hk]; norm_num

  have hC : ∀ a : A, (a : G) * (v a : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : (v a : G)⁻¹ * x * v a ∈ L :=
      L.mul_mem (L.mul_mem (L.inv_mem (v a).2) hx) (v a).2
    have h1 := hv1 a _ hx'
    have h2 : (a : G) * ((v a : G)⁻¹ * x * v a) * (a : G)⁻¹ = x := by rw [h1]; group
    calc x * ((a : G) * (v a : G)⁻¹) =
        (a : G) * ((v a : G)⁻¹ * x * v a) * (a : G)⁻¹ * ((a : G) * (v a : G)⁻¹) := by
          rw [h2]
      _ = (a : G) * (v a : G)⁻¹ * x := by group
  have hZmem : ∀ x : L, (x : G) ∈ Subgroup.zpowers c → x ∈ Subgroup.center L := by
    intro x hx
    rw [← hLC, CFSG.GroupTheory.inf_centralizer_eq_map_center] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hZmem' : ∀ x : L, x ∈ Subgroup.center L → (x : G) ∈ Subgroup.zpowers c := by
    intro x hx
    rw [← hLC, CFSG.GroupTheory.inf_centralizer_eq_map_center]
    exact ⟨x, hx, rfl⟩
  have hAL : A ⊓ L = Subgroup.zpowers c := by
    have h3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
      rw [hU27] at h81
      omega
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hcA, hcL⟩) ?_
    rw [h3, Nat.card_zpowers, hc3]
  have hcomm_id : ∀ l ∈ L, ∀ a : A,
      l * a * l⁻¹ * (a : G)⁻¹ = l * v a * l⁻¹ * (v a : G)⁻¹ := by
    intro l hl a
    set u : G := (a : G) * (v a : G)⁻¹ with hu
    have huL : ∀ y ∈ L, u * y = y * u := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hC a) y hy).symm
    have hk : l * v a * l⁻¹ * (v a : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hl (v a).2) (L.inv_mem hl)) (L.inv_mem (v a).2)
    have ha : (a : G) = u * v a := by rw [hu]; group
    calc l * a * l⁻¹ * (a : G)⁻¹ = l * (u * v a) * l⁻¹ * (u * v a)⁻¹ := by rw [← ha]
      _ = (l * u) * v a * l⁻¹ * (v a : G)⁻¹ * u⁻¹ := by group
      _ = (u * l) * v a * l⁻¹ * (v a : G)⁻¹ * u⁻¹ := by rw [huL l hl]
      _ = u * (l * v a * l⁻¹ * (v a : G)⁻¹) * u⁻¹ := by group
      _ = (l * v a * l⁻¹ * (v a : G)⁻¹) * u * u⁻¹ := by rw [huL _ hk]
      _ = l * v a * l⁻¹ * (v a : G)⁻¹ := by group
  set Pt : Subgroup L := ρ.range.comap (QuotientGroup.mk' (Subgroup.center L)) with hPt
  have hPt27 : Nat.card Pt = 27 := by
    rw [hPt, CFSG.ABGLocalTools.card_comap_mk', hZ, hR9]
  have hPtmem : ∀ b : A, v b ∈ Pt := fun b => ⟨b, hv2 b⟩
  have hPtrep : ∀ x : L, x ∈ Pt → ∃ b : A, ∃ z ∈ Subgroup.center L, x = v b * z := by
    intro x hx
    obtain ⟨b, hb⟩ := hx
    refine ⟨b, (v b)⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq]
    rw [hv2] at hb
    exact hb
  have hRcomm : ∀ p q : L ⧸ Subgroup.center L, p ∈ ρ.range → q ∈ ρ.range → p * q = q * p := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext (hAcomm a a.2 b b.2)]
  have hcommZ : ∀ x : L, x ∈ Pt → ∀ a : A, x * v a * x⁻¹ * (v a)⁻¹ ∈ Subgroup.center L := by
    intro x hx a
    rw [← QuotientGroup.eq_one_iff]
    have hx' : (x : L ⧸ Subgroup.center L) ∈ ρ.range := hx
    have h1 : ((v a : L) : L ⧸ Subgroup.center L) ∈ ρ.range := ⟨a, hv2 a⟩
    have h2 := hRcomm _ _ hx' h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [h2]
    group
  have hND : L ⊓ Subgroup.normalizer (A : Set G) = Pt.map L.subtype := by
    ext g
    constructor
    · rintro ⟨hgL, hgN⟩
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      have hcen : ((⟨g, hgL⟩ : L) : L ⧸ Subgroup.center L) ∈
          Subgroup.centralizer (ρ.range : Set (L ⧸ Subgroup.center L)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨a, rfl⟩
        have hga : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgN a).mp a.2
        have hcomA : g * a * g⁻¹ * (a : G)⁻¹ ∈ A := A.mul_mem hga (A.inv_mem a.2)
        have hcomL : g * a * g⁻¹ * (a : G)⁻¹ ∈ L := by
          have h1 : (a : G) * g⁻¹ * (a : G)⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (hAN a.2) _).mp (L.inv_mem hgL)
          have e : g * a * g⁻¹ * (a : G)⁻¹ = g * ((a : G) * g⁻¹ * (a : G)⁻¹) := by group
          rw [e]
          exact L.mul_mem hgL h1
        have hz : g * a * g⁻¹ * (a : G)⁻¹ ∈ Subgroup.zpowers c := hAL ▸ ⟨hcomA, hcomL⟩
        rw [hcomm_id g hgL a] at hz
        have hzL := hZmem ((⟨g, hgL⟩ : L) * v a * (⟨g, hgL⟩ : L)⁻¹ * (v a)⁻¹) (by simpa using hz)
        rw [← QuotientGroup.eq_one_iff] at hzL
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hzL
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hzL
        rw [hv2 a]
        exact hzL.symm
      exact hcent _ hR9 hcen
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      apply Subgroup.mem_normalizer_fintype
      intro a ha
      show (x : G) * a * (x : G)⁻¹ ∈ A
      have h1 := hcommZ x hx ⟨a, ha⟩
      have h2 : (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ A := by
        have h3 := hcomm_id x x.2 ⟨a, ha⟩
        simp only at h3
        rw [h3]
        have := hZmem' _ h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
        exact (Subgroup.zpowers_le.mpr hcA) this
      have e : (x : G) * a * (x : G)⁻¹ = ((x : G) * a * (x : G)⁻¹ * a⁻¹) * a := by group
      rw [e]
      exact A.mul_mem h2 ha
  set K : Subgroup G := L ⊓ Subgroup.centralizer (A : Set G) with hK
  have hcK : Subgroup.zpowers c ≤ K := Subgroup.zpowers_le.mpr
    ⟨hcL, Subgroup.mem_centralizer_iff.mpr fun a ha => hAcomm a ha c hcA⟩
  have hKD : K ≤ Pt.map L.subtype := by
    rw [← hND]
    exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hKc : ∀ k ∈ K, ∀ x : L, x ∈ Pt → k * x = x * k := by
    intro k hk x hx
    obtain ⟨b, z, hz, rfl⟩ := hPtrep x hx
    have hkL := hk.1
    have hkA : ∀ a ∈ A, a * k = k * a := Subgroup.mem_centralizer_iff.mp hk.2
    have h1 : k * b * k⁻¹ * (b : G)⁻¹ = 1 := by
      rw [← hkA b b.2]
      group
    rw [hcomm_id k hkL b] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    have hkz : k * z = z * k := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hkL⟩)
      simpa using this
    simp only [Subgroup.coe_mul]
    rw [← mul_assoc, h1, mul_assoc, hkz, ← mul_assoc]
  have hK3 : Nat.card K = 3 := by
    obtain ⟨a₁, a₂, h12⟩ := hnc
    have hv1K : (v a₁ : G) ∉ K := fun h => h12 (hKc _ h (v a₂) (hPtmem a₂))
    have hKdvd : Nat.card K ∣ 27 := by
      have := Subgroup.card_dvd_of_le hKD
      rwa [Subgroup.card_map_of_injective L.subtype_injective, hPt27] at this
    have h3K : 3 ∣ Nat.card K := by
      have := Subgroup.card_dvd_of_le hcK
      rwa [Nat.card_zpowers, hc3] at this
    by_contra hne
    have h9 : 9 ∣ Nat.card K := by
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card K ∣ 3 ^ 3 by norm_num; exact hKdvd)
      interval_cases j
      · rw [hj', pow_zero] at h3K
        norm_num at h3K
      · exact absurd (by rw [hj', pow_one]) hne
      · rw [hj']
        norm_num
      · rw [hj']
        norm_num
    set M : Subgroup G := K ⊔ Subgroup.zpowers (v a₁ : G) with hM
    have hMD : M ≤ Pt.map L.subtype :=
      sup_le hKD (Subgroup.zpowers_le.mpr ⟨v a₁, hPtmem a₁, rfl⟩)
    have hMdvd : Nat.card M ∣ 27 := by
      have := Subgroup.card_dvd_of_le hMD
      rwa [Subgroup.card_map_of_injective L.subtype_injective, hPt27] at this
    have hKM : Nat.card K ∣ Nat.card M := Subgroup.card_dvd_of_le le_sup_left
    have hKMne : Nat.card K ≠ Nat.card M := by
      intro h
      have hEq : K = M := Subgroup.eq_of_le_of_card_ge le_sup_left h.symm.le
      exact hv1K (hEq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    obtain ⟨-, hM27⟩ := nine_twentyseven_of_dvd hMdvd hKM h9 hKMne
    have hMeq : M = Pt.map L.subtype := Subgroup.eq_of_le_of_card_ge hMD (by
      rw [hM27, Subgroup.card_map_of_injective L.subtype_injective, hPt27])
    have hv2M : (v a₂ : G) ∈ M := hMeq ▸ ⟨v a₂, hPtmem a₂, rfl⟩
    rw [hM, sup_comm] at hv2M
    obtain ⟨i, k, hk, hik⟩ := exists_zpow_mul_of_mem_sup
      (fun k hk => hKc k hk (v a₁) (hPtmem a₁)) hv2M
    apply h12
    rw [hik]
    have hkv := hKc k hk (v a₁) (hPtmem a₁)
    calc (v a₁ : G) * ((v a₁ : G) ^ i * k) = (v a₁ : G) ^ i * (v a₁ : G) * k := by
          rw [← mul_assoc, ← zpow_one_add, ← zpow_add_one, add_comm]
      _ = (v a₁ : G) ^ i * (k * v a₁) := by rw [mul_assoc, hkv]
      _ = (v a₁ : G) ^ i * k * v a₁ := by rw [mul_assoc]
  have hautcard : Nat.card (autIn L A) = 9 := by
    have h := Sec10.Item1012Res2Proof.card_autIn_mul_card_inf_centralizer L A
    rw [← hK, hK3, hND, Subgroup.card_map_of_injective L.subtype_injective, hPt27] at h
    omega
  have hautEl : CFSG.Assembly.IsElemAbelian 3 (autIn L A) := by
    have hcomm : IsMulCommutative (autIn L A) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hautcard]; norm_num)
    refine ⟨hcomm, fun σ hσ => ?_⟩
    obtain ⟨g, hgN, hgL, rfl⟩ := mem_autIn_iff.mp hσ
    have hgD : g ∈ Pt.map L.subtype := hND ▸ ⟨hgL, hgN⟩
    obtain ⟨x, hx, hxg⟩ := hgD
    have hxg' : (x : G) = g := hxg
    have hx3 : x ^ 3 ∈ Subgroup.center L := by
      obtain ⟨b, hb⟩ := hx
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      have hxb : ((x : L) : L ⧸ Subgroup.center L) = ρ b := hb.symm
      rw [hxb, ← map_pow, show b ^ 3 = 1 from Subtype.ext (by simpa using hAel.2 b b.2), map_one]
    have hx3A : g ^ 3 ∈ A := by
      have := hZmem' _ hx3
      rw [Subgroup.coe_pow, hxg'] at this
      exact (Subgroup.zpowers_le.mpr hcA) this
    have hpow : (⟨g, hgN⟩ : Subgroup.normalizer (A : Set G)) ^ 3 =
        ⟨g ^ 3, pow_mem hgN 3⟩ := Subtype.ext (by simp)
    rw [← map_pow, hpow]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [normalizerMonoidHom_apply_coe]
    simp only [MulAut.one_apply]
    rw [hAcomm _ hx3A _ a.2, mul_inv_cancel_right]
  refine ⟨?_, hautEl, hautcard⟩
  refine ⟨U.subgroupOf (A ⊔ L), L.subgroupOf (A ⊔ L), ?_, ?_, ?_,
    ⟨Subgroup.subgroupOfEquivOfLe le_sup_right⟩, ?_⟩
  · rw [← Subgroup.subgroupOf_sup inf_le_left le_sup_right, hUL, Subgroup.subgroupOf_self]
  · intro u hu w hw
    rw [Subgroup.mem_subgroupOf] at hu hw
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hu.2 _ hw).symm)
  · apply isHeisThree_of
    · rw [← hU27]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      have := hU3 _ (Subgroup.mem_subgroupOf.mp x.2)
      simpa using this
    · intro hcomm
      apply hUnc
      intro u hu u' hu'
      have h1 := hcomm.is_comm.comm ⟨⟨u, hu.1⟩, Subgroup.mem_subgroupOf.mpr hu⟩
        ⟨⟨u', hu'.1⟩, Subgroup.mem_subgroupOf.mpr hu'⟩
      exact congrArg (fun x : ↥(U.subgroupOf (A ⊔ L)) => ((x : ↥(A ⊔ L)) : G)) h1
  · rw [← inf_subgroupOf, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_right : U ⊓ L ≤ L).trans le_sup_right)).toEquiv.symm, hUinf, Nat.card_zpowers,
      hc3]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover
