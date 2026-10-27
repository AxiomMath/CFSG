module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedA7

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem IsElemTwo.isPGroup {F : Subgroup G} (hF : IsElemTwo F) : IsPGroup 2 F := fun y =>
  ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hF.2 y y.2)⟩

theorem IsElemTwo.three_le_pRank [Finite G] {F : Subgroup G} (hF : IsElemTwo F)
    (h8 : 8 ≤ Nat.card F) : 3 ≤ pRank 2 ↥F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2) (G := ↥F)).mp hF.isPGroup
  have hr3 : 3 ≤ r := by
    by_contra h
    push Not at h
    have : 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hEA : IsElementaryAbelian 2 ↥(⊤ : Subgroup ↥F) :=
    { is_comm := ⟨fun x y => Subtype.ext (Subtype.ext (hF.1 _ x.1.2 _ y.1.2))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y =>
        Subtype.ext (Subtype.ext (by
          show ((y : F) : G) ^ 2 = 1
          rw [pow_two]
          exact hF.2 _ y.1.2)) }
  have hmem : r ∈ {r : ℕ | ∃ A : Subgroup ↥F, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} :=
    ⟨⊤, hEA, by rw [card_top, hr]⟩
  have hbdd : BddAbove
      {r : ℕ | ∃ A : Subgroup ↥F, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card F, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card F := by rw [← Nat.card_congr (Equiv.refl _)]; exact card_le_card_group B
  exact hr3.trans (le_csSup hbdd hmem)

theorem IsElemTwo.isAbelianTwoOfRank [Finite G] {F : Subgroup G} (hF : IsElemTwo F)
    (h8 : 8 ≤ Nat.card F) : IsAbelianTwoOfRank 3 F :=
  ⟨hF.isPGroup, hF.1, hF.three_le_pRank h8⟩

theorem IsElemTwo.mono {F F' : Subgroup G} (hF : IsElemTwo F) (h : F' ≤ F) : IsElemTwo F' :=
  ⟨fun x hx y hy => hF.1 x (h hx) y (h hy), fun x hx => hF.2 x (h hx)⟩

theorem IsElemTwo.sup {F F' : Subgroup G} (hF : IsElemTwo F) (hF' : IsElemTwo F')
    (hc : ∀ x ∈ F, ∀ y ∈ F', x * y = y * x) : IsElemTwo (F ⊔ F') := by
  have hC : F ⊔ F' ≤ centralizer (F : Set G) ⊓ centralizer (F' : Set G) := by
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact hF.1 y hy x hx
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact (hc x hx y hy).symm
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact hc y hy x hx
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact hF'.1 y hy x hx
  have hcomm : ∀ x ∈ F ⊔ F', ∀ y ∈ F ⊔ F', x * y = y * x := by
    intro x hx y hy
    have hxc := hC hx
    rw [mem_inf, mem_centralizer_iff, mem_centralizer_iff] at hxc
    have hle : F ⊔ F' ≤ centralizer ({x} : Set G) := sup_le
      (fun z hz => mem_centralizer_singleton_iff.mpr (hxc.1 z hz))
      (fun z hz => mem_centralizer_singleton_iff.mpr (hxc.2 z hz))
    exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
  refine ⟨hcomm, fun x hx => ?_⟩
  rw [sup_eq_closure] at hx
  induction hx using closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hF.2 y hy
    · exact hF'.2 y hy
  | one => exact mul_one 1
  | mul y z hy hz ihy ihz =>
    rw [← sup_eq_closure] at hy hz
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [hcomm z hz y hy]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [ihy, ihz, one_mul]
  | inv y hy ihy =>
    rw [← mul_inv_rev, ihy, inv_one]

theorem isElemTwo_zpowers {x : G} (hx : x * x = 1) : IsElemTwo (zpowers x) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [← zpow_add, ← two_mul, zpow_mul, hx2, one_zpow]

theorem card_zpowers_sup_le {x : G} (hx : x * x = 1) {H : Subgroup G}
    (hxH : x ∈ normalizer (H : Set G)) [Finite G] :
    Nat.card ↥(zpowers x ⊔ H) ≤ 2 * Nat.card H := by
  have hle : zpowers x ≤ normalizer (H : Set G) := zpowers_le.mpr hxH
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers x) H hle
  have h1 : Nat.card ↥(zpowers x ⊔ H) =
      Nat.card ↥((zpowers x : Set G) * (H : Set G)) := by
    rw [← hset]
    rfl
  have hz : Nat.card ↥(zpowers x) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hx)
  rw [h1]
  calc Nat.card ↥((zpowers x : Set G) * (H : Set G)) ≤
        Nat.card ↥(zpowers x : Set G) * Nat.card ↥(H : Set G) := Set.natCard_mul_le
    _ ≤ 2 * Nat.card H := Nat.mul_le_mul_right _ hz

theorem card_le_card_inf_centralizer_sq [Finite G] {E : Subgroup G} {a : G} (hE : IsElemTwo E)
    (haE : a ∈ normalizer (E : Set G)) (ha2 : a * a = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({a} : Set G)) ^ 2 := by
  have hconj : ∀ e ∈ E, a * e * a⁻¹ ∈ E := fun e he => (mem_normalizer_iff.mp haE e).mp he
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  let f : E →* E :=
    { toFun := fun e => ⟨(e : G)⁻¹ * (a * e * a⁻¹), mul_mem (inv_mem e.2) (hconj e e.2)⟩
      map_one' := by ext; simp
      map_mul' := fun e₁ e₂ => by
        apply Subtype.ext
        show ((e₁ : G) * e₂)⁻¹ * (a * (e₁ * e₂) * a⁻¹) =
          ((e₁ : G)⁻¹ * (a * e₁ * a⁻¹)) * ((e₂ : G)⁻¹ * (a * e₂ * a⁻¹))
        have h1 := hE.1 _ (hconj _ e₁.2) _ (inv_mem e₂.2)
        calc ((e₁ : G) * e₂)⁻¹ * (a * (e₁ * e₂) * a⁻¹) =
              (e₂ : G)⁻¹ * (e₁ : G)⁻¹ * ((a * e₁ * a⁻¹) * (a * e₂ * a⁻¹)) := by group
          _ = (e₁ : G)⁻¹ * (e₂ : G)⁻¹ * ((a * e₁ * a⁻¹) * (a * e₂ * a⁻¹)) := by
              rw [hE.1 _ (inv_mem e₂.2) _ (inv_mem e₁.2)]
          _ = (e₁ : G)⁻¹ * ((e₂ : G)⁻¹ * (a * e₁ * a⁻¹)) * (a * e₂ * a⁻¹) := by group
          _ = (e₁ : G)⁻¹ * ((a * e₁ * a⁻¹) * (e₂ : G)⁻¹) * (a * e₂ * a⁻¹) := by rw [h1]
          _ = ((e₁ : G)⁻¹ * (a * e₁ * a⁻¹)) * ((e₂ : G)⁻¹ * (a * e₂ * a⁻¹)) := by group }
  have hker : Nat.card f.ker = Nat.card ↥(E ⊓ centralizer ({a} : Set G)) := by
    refine Nat.card_congr ⟨fun e => ⟨((e : E) : G), mem_inf.mpr ⟨(e : E).2, ?_⟩⟩,
      fun c => ⟨⟨c, (mem_inf.mp c.2).1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · have h := MonoidHom.mem_ker.mp e.2
      have h' : ((e : E) : G)⁻¹ * (a * ((e : E) : G) * a⁻¹) = 1 := congrArg Subtype.val h
      rw [mem_centralizer_singleton_iff]
      have h'' : ((e : E) : G) = a * ((e : E) : G) * a⁻¹ := inv_mul_eq_one.mp h'
      calc ((e : E) : G) * a = a * ((e : E) : G) * a⁻¹ * a := by rw [← h'']
        _ = a * (e : E) := by group
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (c : G)⁻¹ * (a * c * a⁻¹) = 1
      have hc := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
      rw [← hc]
      group
  have hrange : Nat.card f.range ≤ Nat.card ↥(E ⊓ centralizer ({a} : Set G)) := by
    have hle : (f.range).map E.subtype ≤ E ⊓ centralizer ({a} : Set G) := by
      rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
      refine mem_inf.mpr ⟨(f e).2, ?_⟩
      rw [mem_centralizer_singleton_iff]
      show ((e : G)⁻¹ * (a * e * a⁻¹)) * a = a * ((e : G)⁻¹ * (a * e * a⁻¹))
      set c : G := (e : G)⁻¹ * (a * e * a⁻¹) with hcdef
      have h1 : a * c * a⁻¹ = (a * e * a⁻¹)⁻¹ * ((a * a) * e * (a * a)⁻¹) := by
        rw [hcdef]
        group
      rw [ha2, inv_one, one_mul, mul_one] at h1
      have h2 : (a * e * a⁻¹)⁻¹ * (e : G) = c := by
        have hinv1 : (a * e * a⁻¹)⁻¹ = a * e * a⁻¹ := by
          rw [inv_eq_iff_mul_eq_one]; exact hE.2 _ (hconj e e.2)
        have hinv2 : (e : G)⁻¹ = e := by rw [inv_eq_iff_mul_eq_one]; exact hE.2 e e.2
        rw [hcdef, hinv1, hinv2, hE.1 _ (hconj e e.2) _ e.2]
      have h3 := h1.trans h2
      calc c * a = a * c * a⁻¹ * a := by rw [h3]
        _ = a * c := by group
    calc Nat.card f.range = Nat.card ↥((f.range).map E.subtype) :=
          (Subgroup.card_map_of_injective E.subtype_injective).symm
      _ ≤ Nat.card ↥(E ⊓ centralizer ({a} : Set G)) := Subgroup.card_le_of_le hle
  have hcard : Nat.card E = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard, hker, pow_two]
  exact Nat.mul_le_mul_left _ hrange

theorem le_card_of_le_card_sq [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H) :
    (8 ≤ Nat.card H ^ 2 → 4 ≤ Nat.card H) ∧ (32 ≤ Nat.card H ^ 2 → 8 ≤ Nat.card H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2) (G := ↥H)).mp hH
  rw [hr]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hlt
    push Not at hlt
    have : r ≤ 1 := by
      by_contra h'
      push Not at h'
      have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h'
      omega
    interval_cases r <;> norm_num at h
  · by_contra hlt
    push Not at hlt
    have : r ≤ 2 := by
      by_contra h'
      push Not at h'
      have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h'
      omega
    interval_cases r <;> norm_num at h

theorem exists_isElemTwo_of_isAbelianTwoOfRank [Finite G] {A : Subgroup G}
    (hA : IsAbelianTwoOfRank 3 A) : ∃ F : Subgroup G, F ≤ A ∧ IsElemTwo F ∧ 8 ≤ Nat.card F := by
  set s := {r : ℕ | ∃ B : Subgroup ↥A, IsElementaryAbelian 2 ↥B ∧ Nat.card B = 2 ^ r} with hs
  have h3 : 3 ≤ sSup s := hA.2.2
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, csSup_empty] at h3
    exact absurd h3 (by decide)
  have hbdd : BddAbove s := by
    refine ⟨Nat.card A, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card A := card_le_card_group B
  obtain ⟨B, hBe, hBc⟩ := Nat.sSup_mem hne hbdd
  refine ⟨B.map A.subtype, map_subtype_le _, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h := hBe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : B) ⟨y, hy⟩
    exact congrArg (fun w : B => ((w : ↥A) : G)) h
  · rintro _ ⟨x, hx, rfl⟩
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x hx
    have h2' := congrArg Subtype.val h2
    rw [← pow_two]
    exact h2'
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hBc]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ sSup s := Nat.pow_le_pow_right (by norm_num) h3

theorem commute_iff_le_centralizer {B K : Subgroup G} :
    (∀ x ∈ B, ∀ y ∈ K, x * y = y * x) ↔ B ≤ centralizer (K : Set G) := by
  constructor
  · intro h x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact (h x hx y hy).symm
  · intro h x hx y hy
    exact ((mem_centralizer_iff.mp (h hx)) y hy).symm

theorem commute_sup_left {H H' K : Subgroup G} (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (h' : ∀ x ∈ H', ∀ y ∈ K, x * y = y * x) : ∀ x ∈ H ⊔ H', ∀ y ∈ K, x * y = y * x :=
  commute_iff_le_centralizer.mpr (sup_le (commute_iff_le_centralizer.mp h)
    (commute_iff_le_centralizer.mp h'))

theorem commute_symm {H K : Subgroup G} (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    ∀ x ∈ K, ∀ y ∈ H, x * y = y * x := fun x hx y hy => (h y hy x hx).symm

theorem commute_zpowers_left {a : G} {K : Subgroup G} (h : ∀ y ∈ K, a * y = y * a) :
    ∀ x ∈ zpowers a, ∀ y ∈ K, x * y = y * x := by
  apply commute_iff_le_centralizer.mpr
  rw [zpowers_le, mem_centralizer_iff]
  intro y hy
  exact (h y hy).symm

theorem commute_sup_right {H K K' : Subgroup G} (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x)
    (h' : ∀ x ∈ H, ∀ y ∈ K', x * y = y * x) : ∀ x ∈ H, ∀ y ∈ K ⊔ K', x * y = y * x :=
  commute_symm (commute_sup_left (commute_symm h) (commute_symm h'))

theorem commute_of_elemTwo {F H K : Subgroup G} (hF : IsElemTwo F) (hH : H ≤ F) (hK : K ≤ F) :
    ∀ x ∈ H, ∀ y ∈ K, x * y = y * x := fun x hx y hy => hF.1 x (hH hx) y (hK hy)


theorem abelianConnectedIn_of_normal_elementary [Finite G] {S E A : Subgroup G}
    (hS : IsPGroup 2 S) (hES : E ≤ S) (hEn : S ≤ normalizer (E : Set G)) (hE : IsElemTwo E)
    (hE32 : 32 ≤ Nat.card E) (hAS : A ≤ S) (hA : IsAbelianTwoOfRank 3 A) :
    AbelianConnectedIn S 3 A E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have step : ∀ {A' B' : Subgroup G}, B' ≤ S → IsElemTwo B' → 8 ≤ Nat.card B' →
      (∀ x ∈ A', ∀ y ∈ B', x * y = y * x) →
      (fun A' B' : Subgroup G => B' ≤ S ∧ IsAbelianTwoOfRank 3 B' ∧
        ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) A' B' :=
    fun hB hBe hB8 hc => ⟨hB, hBe.isAbelianTwoOfRank hB8, hc⟩
  have hE8 : 8 ≤ Nat.card E := by omega
  obtain ⟨F, hFA, hFe, hF8⟩ := exists_isElemTwo_of_isAbelianTwoOfRank hA
  have hFS : F ≤ S := hFA.trans hAS
  have hAF := step (A' := A) hFS hFe hF8 (fun x hx y hy => hA.2.1 x hx y (hFA hy))
  refine ⟨hAS, hA, Relation.ReflTransGen.head hAF ?_⟩
  set C : Subgroup G := E ⊓ centralizer (A : Set G) with hCdef
  have hCe : IsElemTwo C := hE.mono inf_le_left
  have hCS : C ≤ S := (inf_le_left : C ≤ E).trans hES
  have hCF : ∀ x ∈ F, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp (mem_inf.mp hy).2) x (hFA hx)
  have hEE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := hE.1
  by_cases hC8 : 8 ≤ Nat.card C
  · have hCE : ∀ x ∈ C, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      hE.1 x (mem_inf.mp hx).1 y hy
    exact Relation.ReflTransGen.head (step hCS hCe hC8 hCF)
      (Relation.ReflTransGen.single (step hES hE hE8 hCE))
  push Not at hC8
  have hC1 : 2 ≤ Nat.card C := by
    have hnil : Group.IsNilpotent ↥S := IsPGroup.isNilpotent hS
    have hEn' : (E.subgroupOf S).Normal := ⟨fun e he s => by
      rw [mem_subgroupOf] at he ⊢
      exact (mem_normalizer_iff.mp (hEn s.2) e).mp he⟩
    have hEne : E.subgroupOf S ≠ ⊥ := by
      intro h
      have h1 : Nat.card (E.subgroupOf S) = 1 := by rw [h, card_bot]
      rw [Nat.card_congr (subgroupOfEquivOfLe hES).toEquiv] at h1
      omega
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hEne)
    rw [mem_inf, mem_subgroupOf] at hw
    have hwC : ((w : ↥S) : G) ∈ C := by
      refine mem_inf.mpr ⟨hw.1, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h := (mem_center_iff.mp hw.2) ⟨y, hAS hy⟩
      exact congrArg Subtype.val h
    have hw1' : ((w : ↥S) : G) ≠ 1 := by
      intro h
      apply hw1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    by_contra hlt
    push Not at hlt
    have hC1' : Nat.card C = 1 := by
      have := Nat.card_pos (α := C)
      omega
    have hbot := (card_eq_one.mp hC1')
    rw [hbot] at hwC
    exact hw1' hwC
  have hFE : F ⊓ E ≤ C := fun y hy => mem_inf.mpr ⟨(mem_inf.mp hy).2,
    mem_centralizer_iff.mpr fun z hz => hA.2.1 z hz y (hFA (mem_inf.mp hy).1)⟩
  obtain ⟨a₀, ha₀F, ha₀E⟩ : ∃ a₀ ∈ F, a₀ ∉ E := by
    by_contra h
    push Not at h
    have hle : F ≤ C := fun y hy => hFE (mem_inf.mpr ⟨hy, h y hy⟩)
    have := Subgroup.card_le_of_le hle
    omega
  have ha₀2 : a₀ * a₀ = 1 := hFe.2 a₀ ha₀F
  have ha₀N : a₀ ∈ normalizer (E : Set G) := hEn (hFS ha₀F)
  set E₀ : Subgroup G := E ⊓ centralizer ({a₀} : Set G) with hE₀def
  have hE₀e : IsElemTwo E₀ := hE.mono inf_le_left
  have hE₀S : E₀ ≤ S := (inf_le_left : E₀ ≤ E).trans hES
  have hE₀8 : 8 ≤ Nat.card E₀ :=
    (le_card_of_le_card_sq hE₀e.isPGroup).2
      (hE32.trans (card_le_card_inf_centralizer_sq hE ha₀N ha₀2))
  have hE₀E : ∀ x ∈ E₀, ∀ y ∈ E, x * y = y * x := fun x hx y hy => hE.1 x (mem_inf.mp hx).1 y hy
  have ha₀E₀ : ∀ y ∈ E₀, a₀ * y = y * a₀ := fun y hy =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2).symm
  have ha₀C : ∀ y ∈ C, a₀ * y = y * a₀ := fun y hy => hCF a₀ ha₀F y hy
  have ha₀notC : a₀ ∉ C := fun h => ha₀E (mem_inf.mp h).1
  have htail : Relation.ReflTransGen (fun A' B' : Subgroup G => B' ≤ S ∧
      IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) E₀ E :=
    Relation.ReflTransGen.single (step hES hE hE8 hE₀E)
  have hD : 2 * Nat.card C ≤ Nat.card ↥(zpowers a₀ ⊔ C) :=
    two_mul_card_le_of_not_mem le_sup_right (mem_sup_left (mem_zpowers a₀)) ha₀notC
  have hDe : IsElemTwo (zpowers a₀ ⊔ C) :=
    (isElemTwo_zpowers ha₀2).sup hCe (commute_zpowers_left ha₀C)
  have hDS : zpowers a₀ ⊔ C ≤ S := sup_le (zpowers_le.mpr (hFS ha₀F)) hCS
  have hFD : ∀ x ∈ F, ∀ y ∈ zpowers a₀ ⊔ C, x * y = y * x := by
    apply commute_symm
    apply commute_sup_left (commute_zpowers_left fun y hy => hFe.1 a₀ ha₀F y hy)
    exact commute_symm hCF
  have hCE₀ : ∀ x ∈ C, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    hE.1 x (mem_inf.mp hx).1 y (mem_inf.mp hy).1
  have hDE₀ : ∀ x ∈ zpowers a₀ ⊔ C, ∀ y ∈ E₀, x * y = y * x :=
    commute_sup_left (commute_zpowers_left ha₀E₀) hCE₀
  by_cases hC4 : 4 ≤ Nat.card C
  ·
    have hD8 : 8 ≤ Nat.card ↥(zpowers a₀ ⊔ C) := by omega
    exact Relation.ReflTransGen.head (step hDS hDe hD8 hFD)
      (Relation.ReflTransGen.head (step hE₀S hE₀e hE₀8 hDE₀) htail)
  push Not at hC4
  have hC2 : Nat.card C = 2 := by
    obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2) (G := ↥C)).mp hCe.isPGroup
    rw [hr] at hC1 hC4 ⊢
    have hr1 : 1 ≤ r := by
      by_contra h
      push Not at h
      interval_cases r
      norm_num at hC1
    have hr2 : r ≤ 1 := by
      by_contra h
      push Not at h
      have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
      omega
    have : r = 1 := by omega
    rw [this, pow_one]
  have ha₀NC : a₀ ∈ normalizer (C : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [ha₀C y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := ha₀C _ hy
      have h2 : y = a₀ * y * a₀⁻¹ := by
        have hinv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀2
        calc y = a₀⁻¹ * (a₀ * y * a₀⁻¹) * a₀ := by group
          _ = a₀⁻¹ * (a₀ * (a₀ * y * a₀⁻¹)) := by rw [mul_assoc, ← h1]
          _ = a₀ * y * a₀⁻¹ := by group
      rw [h2]
      exact hy
  have hDle : Nat.card ↥(zpowers a₀ ⊔ C) ≤ 4 := by
    have := card_zpowers_sup_le ha₀2 ha₀NC
    omega
  obtain ⟨a₁, ha₁F, ha₁D⟩ : ∃ a₁ ∈ F, a₁ ∉ zpowers a₀ ⊔ C := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (fun y hy => h y hy : F ≤ zpowers a₀ ⊔ C)
    omega
  have ha₁2 : a₁ * a₁ = 1 := hFe.2 a₁ ha₁F
  have ha₀a₁ : a₀ * a₁ = a₁ * a₀ := hFe.1 a₀ ha₀F a₁ ha₁F
  have hB₁e : IsElemTwo (zpowers a₀ ⊔ C ⊔ zpowers a₁) :=
    hDe.sup (isElemTwo_zpowers ha₁2) (commute_symm (commute_zpowers_left fun y hy =>
      (hFD a₁ ha₁F y hy)))
  have hB₁8 : 8 ≤ Nat.card ↥(zpowers a₀ ⊔ C ⊔ zpowers a₁) := by
    have := two_mul_card_le_of_not_mem (le_sup_left : zpowers a₀ ⊔ C ≤ _)
      (mem_sup_right (mem_zpowers a₁)) ha₁D
    omega
  have hB₁S : zpowers a₀ ⊔ C ⊔ zpowers a₁ ≤ S := sup_le hDS (zpowers_le.mpr (hFS ha₁F))
  have hFB₁ : ∀ x ∈ F, ∀ y ∈ zpowers a₀ ⊔ C ⊔ zpowers a₁, x * y = y * x := by
    apply commute_symm
    apply commute_sup_left (commute_symm hFD)
    exact commute_zpowers_left fun y hy => hFe.1 a₁ ha₁F y hy
  set E₁ : Subgroup G := E₀ ⊓ centralizer ({a₁} : Set G) with hE₁def
  have hE₁e : IsElemTwo E₁ := hE₀e.mono inf_le_left
  have ha₁N : a₁ ∈ normalizer (E₀ : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have hEa := mem_normalizer_iff.mp (hEn (hFS ha₁F)) y
    have hcomm : (a₁ * y * a₁⁻¹) * a₀ = a₀ * (a₁ * y * a₁⁻¹) ↔ y * a₀ = a₀ * y := by
      constructor
      · intro h
        have h' : a₁⁻¹ * ((a₁ * y * a₁⁻¹) * a₀) * a₁ = a₁⁻¹ * (a₀ * (a₁ * y * a₁⁻¹)) * a₁ := by
          rw [h]
        have e1 : a₁⁻¹ * ((a₁ * y * a₁⁻¹) * a₀) * a₁ = y * (a₁⁻¹ * a₀ * a₁) := by group
        have e2 : a₁⁻¹ * (a₀ * (a₁ * y * a₁⁻¹)) * a₁ = (a₁⁻¹ * a₀ * a₁) * y := by group
        have e3 : a₁⁻¹ * a₀ * a₁ = a₀ := by rw [mul_assoc, ha₀a₁, ← mul_assoc, inv_mul_cancel,
          one_mul]
        rw [e1, e2, e3] at h'
        exact h'
      · intro h
        have e3 : a₁ * a₀ * a₁⁻¹ = a₀ := by rw [← ha₀a₁, mul_inv_cancel_right]
        have hc : a₀ * a₁⁻¹ = a₁⁻¹ * a₀ := (Commute.inv_right (show Commute a₀ a₁ from ha₀a₁)).eq
        calc (a₁ * y * a₁⁻¹) * a₀ = a₁ * y * (a₁⁻¹ * a₀) := by group
          _ = a₁ * y * (a₀ * a₁⁻¹) := by rw [hc]
          _ = a₁ * (y * a₀) * a₁⁻¹ := by group
          _ = a₁ * (a₀ * y) * a₁⁻¹ := by rw [h]
          _ = (a₁ * a₀ * a₁⁻¹) * (a₁ * y * a₁⁻¹) := by group
          _ = a₀ * (a₁ * y * a₁⁻¹) := by rw [e3]
    simp only [hE₀def, mem_inf, mem_centralizer_singleton_iff]
    rw [hEa, hcomm]
  have hE₁4 : 4 ≤ Nat.card E₁ :=
    (le_card_of_le_card_sq hE₁e.isPGroup).1
      (hE₀8.trans (card_le_card_inf_centralizer_sq hE₀e ha₁N ha₁2))
  have ha₀E₁ : ∀ y ∈ E₁, a₀ * y = y * a₀ := fun y hy => ha₀E₀ y (mem_inf.mp hy).1
  have hB₂e : IsElemTwo (zpowers a₀ ⊔ E₁) :=
    (isElemTwo_zpowers ha₀2).sup hE₁e (commute_zpowers_left ha₀E₁)
  have ha₀E₁' : a₀ ∉ E₁ := fun h => ha₀E (mem_inf.mp (mem_inf.mp h).1).1
  have hB₂8 : 8 ≤ Nat.card ↥(zpowers a₀ ⊔ E₁) := by
    have := two_mul_card_le_of_not_mem le_sup_right (mem_sup_left (mem_zpowers a₀)) ha₀E₁'
    omega
  have hB₂S : zpowers a₀ ⊔ E₁ ≤ S :=
    sup_le (zpowers_le.mpr (hFS ha₀F)) ((inf_le_left : E₁ ≤ E₀).trans hE₀S)
  have hzF₀ : zpowers a₀ ≤ F := zpowers_le.mpr ha₀F
  have hzF₁ : zpowers a₁ ≤ F := zpowers_le.mpr ha₁F
  have hE₁E : E₁ ≤ E := (inf_le_left : E₁ ≤ E₀).trans inf_le_left
  have hB₁B₂ : ∀ x ∈ zpowers a₀ ⊔ C ⊔ zpowers a₁, ∀ y ∈ zpowers a₀ ⊔ E₁, x * y = y * x := by
    refine commute_sup_left (commute_sup_left (commute_sup_right ?_ ?_)
      (commute_sup_right ?_ ?_)) (commute_sup_right ?_ ?_)
    · exact commute_of_elemTwo hFe hzF₀ hzF₀
    · exact commute_zpowers_left ha₀E₁
    · exact commute_symm (commute_zpowers_left ha₀C)
    · exact commute_of_elemTwo hE inf_le_left hE₁E
    · exact commute_of_elemTwo hFe hzF₁ hzF₀
    · exact commute_zpowers_left fun y hy =>
        (mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2).symm
  have hB₂E₀ : ∀ x ∈ zpowers a₀ ⊔ E₁, ∀ y ∈ E₀, x * y = y * x :=
    commute_sup_left (commute_zpowers_left ha₀E₀) (commute_of_elemTwo hE₀e inf_le_left le_rfl)
  exact Relation.ReflTransGen.head (step hB₁S hB₁e hB₁8 hFB₁)
    (Relation.ReflTransGen.head (step hB₂S hB₂e hB₂8 hB₁B₂)
      (Relation.ReflTransGen.head (step hE₀S hE₀e hE₀8 hB₂E₀) htail))


theorem AbelianConnectedIn.symm [Finite G] {S A B : Subgroup G} (h : AbelianConnectedIn S 3 A B) :
    AbelianConnectedIn S 3 B A := by
  obtain ⟨hAS, hA, hR⟩ := h
  have key : ∀ C, Relation.ReflTransGen (fun A' B' : Subgroup G => B' ≤ S ∧
      IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) A C →
      (C ≤ S ∧ IsAbelianTwoOfRank 3 C) ∧ Relation.ReflTransGen (fun A' B' : Subgroup G =>
        B' ≤ S ∧ IsAbelianTwoOfRank 3 B' ∧ ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) C A := by
    intro C hC
    induction hC with
    | refl => exact ⟨⟨hAS, hA⟩, Relation.ReflTransGen.refl⟩
    | tail _ hst ih =>
      obtain ⟨hD, hDr, hc⟩ := hst
      exact ⟨⟨hD, hDr⟩, Relation.ReflTransGen.head ⟨ih.1.1, ih.1.2, commute_symm hc⟩ ih.2⟩
  obtain ⟨⟨hBS, hB⟩, hR'⟩ := key B hR
  exact ⟨hBS, hB, hR'⟩

theorem AbelianConnectedIn.trans {S A B C : Subgroup G} [Finite G]
    (h₁ : AbelianConnectedIn S 3 A B) (h₂ : AbelianConnectedIn S 3 B C) :
    AbelianConnectedIn S 3 A C :=
  ⟨h₁.1, h₁.2.1, h₁.2.2.trans h₂.2.2⟩

theorem isThreeConnected_of_normal [Finite G] {S E : Subgroup G} (hS : IsPGroup 2 S)
    (hES : E ≤ S) (hEn : S ≤ normalizer (E : Set G)) (hE : IsElemTwo E) (hE32 : 32 ≤ Nat.card E) :
    IsThreeConnected S := fun _ _ hA hB hAr hBr =>
  (abelianConnectedIn_of_normal_elementary hS hES hEn hE hE32 hA hAr).trans
    (abelianConnectedIn_of_normal_elementary hS hES hEn hE hE32 hB hBr).symm

end CFSG.ComponentClassification.GrSLit
