module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCensus
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open
open scoped commutatorElement

variable {W : Type*} [Group W]

theorem commutator_self_of_commutator_eq_top {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator ↥H = ⊤) : ⁅H, H⁆ = H := by
  rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commute_of_mem_zpowers {G : Type*} [Group G] {a g z : G} (h : g * a = a * g)
    (hz : z ∈ zpowers a) : z * g = g * z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  exact ((Commute.zpow_left (Commute.eq h).symm k)).eq

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {x w : G} (hx : x ^ 2 = 1)
    (hw : w ∈ zpowers x) : w = 1 ∨ w = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have hx2 : x ^ (2 : ℤ) = 1 := by exact_mod_cast hx
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.mul_ediv_add_emod k 2, h, add_zero, zpow_mul, hx2, one_zpow]
  · right
    rw [← Int.mul_ediv_add_emod k 2, h, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]

theorem zpow_mul_comm_of_mul_comm {G : Type*} [Group G] {a m : G} (h : a * m = m * a)
    (k : ℤ) : a ^ k * m = m * a ^ k :=
  ((Commute.zpow_left h k)).eq

theorem exists_zpow_mul_of_mem_sup {G : Type*} [Group G] {a : G} {M : Subgroup G}
    (ha : ∀ m ∈ M, a * m = m * a) {g : G} (hg : g ∈ zpowers a ⊔ M) :
    ∃ k : ℤ, ∃ m ∈ M, g = a ^ k * m := by
  have hc : ∀ k : ℤ, ∀ m ∈ M, a ^ k * m = m * a ^ k := fun k m hm =>
    ((Commute.zpow_left (ha m hm) k)).eq
  let S : Subgroup G :=
    { carrier := {g | ∃ k : ℤ, ∃ m ∈ M, g = a ^ k * m}
      mul_mem' := by
        rintro _ _ ⟨k₁, m₁, hm₁, rfl⟩ ⟨k₂, m₂, hm₂, rfl⟩
        refine ⟨k₁ + k₂, m₁ * m₂, M.mul_mem hm₁ hm₂, ?_⟩
        rw [zpow_add, mul_assoc, ← mul_assoc m₁, ← hc k₂ m₁ hm₁]
        group
      one_mem' := ⟨0, 1, M.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, m, hm, rfl⟩
        refine ⟨-k, m⁻¹, M.inv_mem hm, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, hc (-k) m⁻¹ (M.inv_mem hm)] }
  have hle : zpowers a ⊔ M ≤ S := sup_le
    (fun x hx => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact ⟨k, 1, M.one_mem, by simp⟩)
    (fun m hm => ⟨0, m, hm, by simp⟩)
  exact hle hg

theorem exists_mem_eq_or_eq_mul_of_mem_sup {G : Type*} [Group G] {a : G} {M : Subgroup G}
    (ha : ∀ m ∈ M, a * m = m * a) (ha2 : a * a = 1) {g : G} (hg : g ∈ zpowers a ⊔ M) :
    ∃ m ∈ M, g = m ∨ g = a * m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_zpow_mul_of_mem_sup ha hg
  refine ⟨m, hm, ?_⟩
  rcases eq_one_or_eq_of_mem_zpowers (by rw [sq]; exact ha2) (zpow_mem_zpowers a k) with h | h
  · left
    rw [h, one_mul]
  · right
    rw [h]

theorem commutator_le_of_relIndex_two {G : Type*} [Group G] {M N : Subgroup G}
    (h : (N.subgroupOf M).index = 2) : ⁅M, M⁆ ≤ N := by
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have k := Subgroup.mul_mem_iff_of_index_two h (a := (⟨g₁ * g₂, M.mul_mem hg₁ hg₂⟩ : ↥M))
    (b := ⟨g₁⁻¹ * g₂⁻¹, M.mul_mem (M.inv_mem hg₁) (M.inv_mem hg₂)⟩)
  have k1 := Subgroup.mul_mem_iff_of_index_two h (a := (⟨g₁, hg₁⟩ : ↥M)) (b := ⟨g₂, hg₂⟩)
  have k2 := Subgroup.mul_mem_iff_of_index_two h (a := (⟨g₁⁻¹, M.inv_mem hg₁⟩ : ↥M))
    (b := ⟨g₂⁻¹, M.inv_mem hg₂⟩)
  have i1 : (⟨g₁⁻¹, M.inv_mem hg₁⟩ : ↥M) ∈ N.subgroupOf M ↔ (⟨g₁, hg₁⟩ : ↥M) ∈ N.subgroupOf M :=
    inv_mem_iff (x := (⟨g₁, hg₁⟩ : ↥M))
  have i2 : (⟨g₂⁻¹, M.inv_mem hg₂⟩ : ↥M) ∈ N.subgroupOf M ↔ (⟨g₂, hg₂⟩ : ↥M) ∈ N.subgroupOf M :=
    inv_mem_iff (x := (⟨g₂, hg₂⟩ : ↥M))
  have hmem : (⟨g₁ * g₂, M.mul_mem hg₁ hg₂⟩ * ⟨g₁⁻¹ * g₂⁻¹, M.mul_mem (M.inv_mem hg₁)
      (M.inv_mem hg₂)⟩ : ↥M) ∈ N.subgroupOf M := by
    rw [k]
    change (⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ : ↥M) ∈ N.subgroupOf M ↔
      (⟨g₁⁻¹, M.inv_mem hg₁⟩ * ⟨g₂⁻¹, M.inv_mem hg₂⟩ : ↥M) ∈ N.subgroupOf M
    rw [k1, k2, i1, i2]
  have he : ⁅g₁, g₂⁆ = g₁ * g₂ * (g₁⁻¹ * g₂⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact mem_subgroupOf.mp hmem

theorem centDer_le {G : Type*} [Group G] (X : Subgroup G) (t : G) :
    centDer X t ≤ X ⊓ centralizer {t} :=
  Subgroup.commutator_le_self _

theorem autModel_top {T : Type*} [Group T] (hc : center T = ⊥)
    (hinn : ∀ α : MulAut T, ∃ g : T, α = MulAut.conj g) :
    AutModel T T ⊤ := by
  refine ⟨inferInstance, ?_, ⟨Subgroup.topEquiv⟩, fun α => ?_⟩
  · rw [coe_top, centralizer_univ, hc]
  · obtain ⟨g, hg⟩ := hinn ((Subgroup.topEquiv.symm.trans α).trans Subgroup.topEquiv)
    refine ⟨g, fun x => ?_⟩
    have h := congrArg (fun β : MulAut T => β (x : T)) hg
    have hx : Subgroup.topEquiv.symm (x : T) = x := Subtype.ext rfl
    simpa [hx] using h

section MulAut

variable {G : Type*} [Group G]

theorem mulAut_mul_conj_mul_inv (β : MulAut G) (g : G) :
    β * MulAut.conj g * β⁻¹ = MulAut.conj (β g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem conj_injective_of_center_eq_bot (hc : center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have hmem : y⁻¹ * x ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut G => φ g) hxy
    simp only [MulAut.conj_apply] at h
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * y * y⁻¹ * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * y * y⁻¹ * x := by rw [h]
      _ = y⁻¹ * x * g := by group
  rw [hc, mem_bot] at hmem
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [hmem, mul_one]

theorem autModel_mulAut_of_center {X₀ : Type*} [Group X₀] (e : G ≃* X₀) (hc : center G = ⊥) :
    AutModel X₀ (MulAut G) (OuterAutomorphisms.inner G) := by
  have hinj := conj_injective_of_center_eq_bot hc
  set φ : G ≃* OuterAutomorphisms.inner G := MonoidHom.ofInjective hinj with hφ
  have hφv : ∀ g : G, ((φ g : OuterAutomorphisms.inner G) : MulAut G) = MulAut.conj g :=
    fun g => rfl
  refine ⟨OuterAutomorphisms.inner_normal G, ?_, ⟨φ.symm.trans e⟩, fun α => ?_⟩
  · rw [eq_bot_iff]
    intro β hβ
    rw [mem_bot]
    ext g
    have hc' := mem_centralizer_iff.mp hβ (MulAut.conj g) ⟨g, rfl⟩
    have h1 : β * MulAut.conj g * β⁻¹ = MulAut.conj g := by
      rw [← hc']
      group
    rw [mulAut_mul_conj_mul_inv] at h1
    exact hinj h1
  · refine ⟨(φ.trans α).trans φ.symm, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := φ.surjective x
    have hβg : φ (((φ.trans α).trans φ.symm) g) = α (φ g) := by
      simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [← hβg, hφv, hφv, mulAut_mul_conj_mul_inv]

end MulAut

theorem commutator_le_nE {X E : Subgroup W} {t b : W} (ht : t ∈ E) (ht1 : t ≠ 1)
    (hb : b ∈ E) {P : Subgroup W} (hP : P ≤ centDer X t) :
    ⁅zpowers b, P⁆ ≤ nE X E :=
  commutator_mono (zpowers_le.mpr hb)
    (hP.trans (le_iSup₂_of_le t ht (le_iSup_of_le ht1 le_rfl)))

theorem commutator_le_of_mem_normalizer {b : W} {P : Subgroup W}
    (hb : b ∈ normalizer (P : Set W)) : ⁅zpowers b, P⁆ ≤ P := by
  rw [commutator_le]
  intro x hx p hp
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  have h1 : b ^ n * p * (b ^ n)⁻¹ ∈ P :=
    (mem_normalizer_iff.mp (zpow_mem hb n) p).mp hp
  rw [commutatorElement_def]
  exact P.mul_mem h1 (P.inv_mem hp)

theorem conj_mem_commutator_of_mem_right {H K : Subgroup W} {y p : W} (hy : y ∈ ⁅H, K⁆)
    (hp : p ∈ K) : p * y * p⁻¹ ∈ ⁅H, K⁆ := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, q, hq, rfl⟩ := hx
    have h : p * ⁅c, q⁆ * p⁻¹ = ⁅c, p⁆⁻¹ * ⁅c, p * q⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h]
    exact mul_mem (inv_mem (commutator_mem_commutator hc hp))
      (commutator_mem_commutator hc (K.mul_mem hp hq))
  | one => simp
  | mul x y _ _ hx hy =>
    have h : p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by group
    rw [h]
    exact mul_mem hx hy
  | inv x _ hx =>
    have h : p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ := by group
    rw [h]
    exact inv_mem hx

theorem conj_mem_commutator {b : W} {P : Subgroup W} {y p : W} (hy : y ∈ ⁅zpowers b, P⁆)
    (hp : p ∈ P) : p * y * p⁻¹ ∈ ⁅zpowers b, P⁆ :=
  conj_mem_commutator_of_mem_right hy hp

theorem exists_not_commute_of_perfect {b : W} {P : Subgroup W} (hperf : ⁅P, P⁆ = P)
    (hb : b ∈ normalizer (P : Set W)) (hbc : b ∉ centralizer (P : Set W)) :
    ∃ y ∈ ⁅zpowers b, P⁆, ∃ p ∈ P, y * p ≠ p * y := by
  by_contra hcon
  push Not at hcon
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
  let f : ↥P →* ↥P :=
    { toFun := fun x => ⟨b * x * b⁻¹, (mem_normalizer_iff.mp hb x).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [coe_mul]; group) }
  have hdisp : ∀ x : ↥P, x⁻¹ * f x ∈ center ↥P := by
    intro x
    rw [mem_center_iff]
    intro p
    have hmem : ((x : W)⁻¹ * (b * x * b⁻¹)) ∈ ⁅zpowers b, P⁆ := by
      have h := commutator_mem_commutator (mem_zpowers b) (P.inv_mem x.2)
      have he : ⁅b, (x : W)⁻¹⁆⁻¹ = (x : W)⁻¹ * (b * x * b⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [← he]
      exact inv_mem h
    apply Subtype.ext
    simp only [coe_mul]
    exact (hcon _ hmem p p.2).symm
  have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement f hdisp
  apply hbc
  rw [mem_centralizer_iff]
  intro x hx
  have h := congrArg (fun g : ↥P →* ↥P => ((g ⟨x, hx⟩ : ↥P) : W)) hid
  change b * x * b⁻¹ = x at h
  calc x * b = b * x * b⁻¹ * b := by rw [h]
    _ = b * x := by group

@[expose] def FourProp (P : Subgroup W) : Prop :=
  ∀ N : Subgroup W, N ≤ P → (∀ p ∈ P, ∀ y ∈ N, p * y * p⁻¹ ∈ N) →
    (∃ y ∈ N, ∃ p ∈ P, y * p ≠ p * y) → ∃ y ∈ N, 4 ∣ orderOf y

theorem exists_four_of_perfect {b : W} {P : Subgroup W} (hperf : ⁅P, P⁆ = P) (h4 : FourProp P)
    (hb : b ∈ normalizer (P : Set W)) (hbc : b ∉ centralizer (P : Set W)) :
    ∃ y ∈ ⁅zpowers b, P⁆, 4 ∣ orderOf y :=
  h4 _ (commutator_le_of_mem_normalizer hb) (fun _ hp _ hy => conj_mem_commutator hy hp)
    (exists_not_commute_of_perfect hperf hb hbc)

theorem yWitness_of_perfect {X E : Subgroup W} {t b : W} (ht : t ∈ E) (ht1 : t ≠ 1)
    (hb : b ∈ E) {P : Subgroup W} (hP : P ≤ centDer X t) (hperf : ⁅P, P⁆ = P)
    (h4 : FourProp P) (hbn : b ∈ normalizer (P : Set W)) (hbc : b ∉ centralizer (P : Set W)) :
    YWitness X E := by
  obtain ⟨y, hy, h⟩ := exists_four_of_perfect hperf h4 hbn hbc
  exact Or.inl ⟨y, commutator_le_nE ht ht1 hb hP hy, h⟩

theorem fourProp_of_quasisimple {P : Subgroup W} (hq : CFSG.Open.IsQuasisimple ↥P)
    (h4 : ∃ y ∈ P, 4 ∣ orderOf y) : FourProp P := by
  intro N hNP hNn ⟨y, hyN, p, hpP, hyp⟩
  have : (N.subgroupOf P).Normal :=
    ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      simpa using hNn g g.2 x hx⟩
  rcases Quasisimple.normal_le_center_or_eq_top hq (N.subgroupOf P) with h | h
  · exfalso
    have hc := mem_center_iff.mp (h (show (⟨y, hNP hyN⟩ : ↥P) ∈ N.subgroupOf P from hyN))
      ⟨p, hpP⟩
    exact hyp (congrArg Subtype.val hc).symm
  · obtain ⟨z, hzP, hz⟩ := h4
    have : (⟨z, hzP⟩ : ↥P) ∈ N.subgroupOf P := h ▸ mem_top _
    exact ⟨z, this, hz⟩

theorem fourProp_of_constrained {P Q Z : Subgroup W} (hQP : Q ≤ P)
    (hQn : ∀ p ∈ P, ∀ q ∈ Q, p * q * p⁻¹ ∈ Q) (hZ : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z)
    (hirr : ∀ M : Subgroup W, M ≤ Q → (∀ p ∈ P, ∀ y ∈ M, p * y * p⁻¹ ∈ M) → M ≤ Z ∨ M = Q)
    (hfaith : ∀ x ∈ P, (∀ q ∈ Q, ⁅x, q⁆ ∈ Z) → x ∈ Q) (h4 : ∃ y ∈ Q, 4 ∣ orderOf y) :
    FourProp P := by
  intro N hNP hNn ⟨y, hyN, p, hpP, hyp⟩
  obtain ⟨w, hwQ, hw⟩ := h4
  suffices hQN : Q ≤ N from ⟨w, hQN hwQ, hw⟩
  have hMn : ∀ p ∈ P, ∀ y ∈ N ⊓ Q, p * y * p⁻¹ ∈ N ⊓ Q := fun p hp y hy =>
    ⟨hNn p hp y hy.1, hQn p hp y hy.2⟩
  by_cases hNQ : N ≤ Q
  · rcases hirr N hNQ hNn with h | h
    · exact absurd (hZ y (h hyN) p hpP) hyp
    · exact h.ge
  · obtain ⟨n, hnN, hnQ⟩ := Set.not_subset.mp hNQ
    obtain ⟨q, hqQ, hnq⟩ : ∃ q ∈ Q, ⁅n, q⁆ ∉ Z := by
      by_contra hcon
      push Not at hcon
      exact hnQ (hfaith n (hNP hnN) hcon)
    have hmem : ⁅n, q⁆ ∈ N ⊓ Q := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine N.mul_mem hnN ?_
        have := hNn q (hQP hqQ) n⁻¹ (N.inv_mem hnN)
        simpa [mul_assoc] using this
      · rw [commutatorElement_def]
        exact Q.mul_mem (hQn n (hNP hnN) q hqQ) (Q.inv_mem hqQ)
    rcases hirr (N ⊓ Q) inf_le_right hMn with h | h
    · exact absurd (h hmem) hnq
    · rw [← h]
      exact inf_le_left

theorem fourProp_map_iff {U : Type*} [Group U] (ι : W →* U) (hι : Function.Injective ι)
    (P : Subgroup W) : FourProp (P.map ι) ↔ FourProp P := by
  constructor
  · intro h N hNP hNn ⟨y, hyN, p, hpP, hyp⟩
    obtain ⟨_, ⟨w, hwN, rfl⟩, hw⟩ := h (N.map ι) (map_mono hNP)
      (by
        rintro _ ⟨p', hp', rfl⟩ _ ⟨y', hy', rfl⟩
        exact ⟨p' * y' * p'⁻¹, hNn p' hp' y' hy', by simp⟩)
      ⟨ι y, ⟨y, hyN, rfl⟩, ι p, ⟨p, hpP, rfl⟩, fun he => hyp (hι (by simpa using he))⟩
    exact ⟨w, hwN, by rwa [orderOf_injective ι hι] at hw⟩
  · intro h N hNP hNn ⟨y, hyN, p, hpP, hyp⟩
    have hcomap : N.comap ι ≤ P := by
      intro n hn
      obtain ⟨p₀, hp₀, he⟩ := hNP hn
      rw [← hι he]
      exact hp₀
    obtain ⟨p₀, hp₀, rfl⟩ := hpP
    obtain ⟨y₀, -, rfl⟩ := hNP hyN
    obtain ⟨w, hw, h4⟩ := h (N.comap ι) hcomap
      (fun p' hp' n hn => by
        show ι (p' * n * p'⁻¹) ∈ N
        rw [map_mul, map_mul, map_inv]
        exact hNn _ ⟨p', hp', rfl⟩ _ hn)
      ⟨y₀, hyN, p₀, hp₀, fun he => hyp (by rw [← map_mul, he, map_mul])⟩
    exact ⟨ι w, hw, by rwa [orderOf_injective ι hι]⟩

theorem yWitness_of_isConj_mem {X : Subgroup W} (hX : X.Normal) {t₀ : W}
    (h : ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → t₀ ∈ E → YWitness X E)
    {E : Subgroup W} (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) {t : W} (ht : t ∈ E)
    (hc : IsConj t₀ t) : YWitness X E := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  set σ := MulAut.conj g⁻¹
  have hmem : t₀ ∈ E.map σ.toMonoidHom :=
    ⟨g * t₀ * g⁻¹, ht, by simp [σ, mul_assoc]⟩
  have hw := h _ (isElemAbelian_map hE _) (by rwa [card_map_of_injective σ.injective]) hmem
  rwa [← map_conj_eq_of_normal hX g⁻¹, yWitness_map_iff σ.toMonoidHom σ.injective] at hw

theorem exists_mem_inf_ne_one_of_index_dvd_two {X : Subgroup W} (hX : X.Normal)
    (hidx : X.index ∣ 2) {E : Subgroup W} (hE4 : 4 ≤ Nat.card E) :
    ∃ e ∈ E, e ∈ X ∧ e ≠ 1 := by
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : X.relIndex E ∣ 2 := (relIndex_dvd_index_of_normal X E).trans hidx
  have hmul := (X.subgroupOf E).card_mul_index
  rw [show (X.subgroupOf E).index = X.relIndex E from rfl] at hmul
  have hle : X.relIndex E ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hcard : 1 < Nat.card (X.subgroupOf E) := by
    by_contra hcon
    push Not at hcon
    have : Nat.card E ≤ 2 := by
      calc Nat.card E = Nat.card (X.subgroupOf E) * X.relIndex E := hmul.symm
        _ ≤ 1 * 2 := Nat.mul_le_mul hcon hle
        _ = 2 := by norm_num
    omega
  obtain ⟨x, hx⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp hcard)
  exact ⟨x.1.1, x.1.2, (mem_subgroupOf).mp x.2, fun h => hx (Subtype.ext (Subtype.ext h))⟩

theorem mem_normalizer_centDer {X : Subgroup W} {t b : W} (hbX : b ∈ normalizer (X : Set W))
    (hbt : b * t = t * b) : b ∈ normalizer (centDer X t : Set W) := by
  have ht1 : b * t * b⁻¹ = t := by rw [hbt, mul_inv_cancel_right]
  have ht2 : b⁻¹ * t * b = t := by rw [mul_assoc, ← hbt, ← mul_assoc, inv_mul_cancel, one_mul]
  have hH : ∀ g : W, g ∈ X ⊓ centralizer {t} ↔ b * g * b⁻¹ ∈ X ⊓ centralizer {t} := by
    intro g
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr ((mem_normalizer_iff.mp hbX) g) ⟨fun h => ?_, fun h => ?_⟩
    · calc b * g * b⁻¹ * t = b * g * b⁻¹ * (b * t * b⁻¹) := by rw [ht1]
        _ = b * (g * t) * b⁻¹ := by group
        _ = b * (t * g) * b⁻¹ := by rw [h]
        _ = (b * t * b⁻¹) * (b * g * b⁻¹) := by group
        _ = t * (b * g * b⁻¹) := by rw [ht1]
    · calc g * t = b⁻¹ * (b * g * b⁻¹) * b * (b⁻¹ * t * b) := by rw [ht2]; group
        _ = b⁻¹ * ((b * g * b⁻¹) * t) * b := by group
        _ = b⁻¹ * (t * (b * g * b⁻¹)) * b := by rw [h]
        _ = (b⁻¹ * t * b) * g := by group
        _ = t * g := by rw [ht2]
  have hmap : (X ⊓ centralizer {t}).map (MulAut.conj b).toMonoidHom = X ⊓ centralizer {t} := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hH g).mp hg
    · intro hy
      refine ⟨b⁻¹ * y * b, (hH _).mpr (by simpa [mul_assoc] using hy), ?_⟩
      simp [mul_assoc]
  have hP : (centDer X t).map (MulAut.conj b).toMonoidHom = centDer X t := by
    rw [centDer, map_commutator, hmap]
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [← hP]
    exact ⟨n, hn, rfl⟩
  · intro hn
    rw [← hP] at hn
    obtain ⟨m, hm, he⟩ := hn
    have : m = n := by
      have he' : b * m * b⁻¹ = b * n * b⁻¹ := he
      simpa using he'
    rwa [← this]

theorem yCensus_of_classes {X : Subgroup W} (hX : X.Normal) (P : W → Prop)
    (hE : ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E →
      ∃ t ∈ E, ∃ t₀, P t₀ ∧ IsConj t₀ t)
    (hrep : ∀ t₀, P t₀ → ∀ E : Subgroup W, IsElemAbelian 2 E → 4 ≤ Nat.card E → t₀ ∈ E →
      YWitness X E) :
    YCensus X (fun _ => False) := by
  intro E hE2 hE4 _
  obtain ⟨t, htE, t₀, ht₀, hconj⟩ := hE E hE2 hE4
  exact yWitness_of_isConj_mem hX (hrep t₀ ht₀) hE2 hE4 htE hconj

theorem mul_comm_of_isElemAbelian {E : Subgroup W} (hE : IsElemAbelian 2 E) {a b : W}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem exists_orderOf_eq_two_of_isElemAbelian {E : Subgroup W} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) : ∃ t ∈ E, orderOf t = 2 := by
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨t, htE⟩, ht1⟩ := exists_ne (1 : ↥E)
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  exact ⟨t, htE, orderOf_eq_prime (hE.2 t htE) ht1'⟩

theorem exists_not_mem_zpowers_of_isElemAbelian {E : Subgroup W} (hE4 : 4 ≤ Nat.card E)
    {t : W} (ht : t ^ 2 = 1) : ∃ b ∈ E, b ∉ zpowers t := by
  by_contra hcon
  push Not at hcon
  have : Finite ↥(zpowers t) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, ht⟩)
  have hcard := card_le_of_le (show E ≤ zpowers t from hcon)
  have hz : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) ht
  omega

theorem yCensus_inner_of_derived {T : Type*} [Group T] [Finite T] {z : T} {C L : Subgroup T}
    (hc : center T = ⊥) (hout : Nat.card (OuterAutomorphisms.Outer T) ∣ 2) (hz : orderOf z = 2)
    (hfus : ∀ t : T, orderOf t = 2 → ∃ x : T, x * z * x⁻¹ = t)
    (hC : C = centralizer {z}) (hL : L = ⁅C, C⁆) (hperf : ⁅L, L⁆ = L) (h4 : FourProp L)
    (hfix : ∀ α : MulAut T, α * α = 1 → (∀ l ∈ L, α l = l) → α = 1 ∨ α = MulAut.conj z) :
    YCensus (OuterAutomorphisms.inner T) (fun _ => False) := by
  have hinj := conj_injective_of_center_eq_bot hc
  set X := OuterAutomorphisms.inner T with hX
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hι2 : MulAut.conj z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hι1 : MulAut.conj z ≠ 1 := fun h => by
    have hz1 : z = 1 := hinj (by rw [h, map_one])
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  refine yCensus_of_classes (OuterAutomorphisms.inner_normal T) (fun t₀ => t₀ = MulAut.conj z)
    (fun E hE hE4 => ?_) ?_
  ·
    obtain ⟨e, heE, heX, he1⟩ :=
      exists_mem_inf_ne_one_of_index_dvd_two (OuterAutomorphisms.inner_normal T) hout hE4
    obtain ⟨j, rfl⟩ := (MonoidHom.mem_range).mp (show e ∈ (MulAut.conj (G := T)).range from heX)
    have hj1 : j ≠ 1 := fun h => he1 (by rw [h, map_one])
    have hj2 : orderOf j = 2 := by
      have h2 : (MulAut.conj j) ^ 2 = 1 := hE.2 _ heE
      rw [← map_pow] at h2
      exact orderOf_eq_prime (hinj (by rw [h2, map_one])) hj1
    obtain ⟨x, hx⟩ := hfus j hj2
    refine ⟨MulAut.conj j, heE, MulAut.conj z, rfl, isConj_iff.mpr ⟨MulAut.conj x, ?_⟩⟩
    rw [← hx, map_mul, map_mul, map_inv]
  · rintro t₀ rfl E hE hE4 hιE
    obtain ⟨β, hβE, hβz⟩ := exists_not_mem_zpowers_of_isElemAbelian hE4 hι2
    have hcomm : β * MulAut.conj z = MulAut.conj z * β :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨β, hβE⟩ ⟨MulAut.conj z, hιE⟩)
    have hβfix : β z = z := by
      apply hinj
      rw [← mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
    have hβC : ∀ c, c ∈ C ↔ β c ∈ C := by
      intro c
      rw [hC, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · intro h
        rw [← hβfix, ← map_mul, ← map_mul, h]
      · intro h
        apply β.injective
        rw [map_mul, map_mul, hβfix, h]
    have hCmap : C.map β.toMonoidHom = C := by
      ext y
      constructor
      · rintro ⟨c, hc', rfl⟩
        exact (hβC c).mp hc'
      · intro hy
        exact ⟨β.symm y, (hβC _).mpr (by simpa using hy), by simp⟩
    have hLmap : L.map β.toMonoidHom = L := by rw [hL, map_commutator, hCmap]
    have hβL : ∀ l, l ∈ L ↔ β l ∈ L := by
      intro l
      constructor
      · intro hl
        rw [← hLmap]
        exact ⟨l, hl, rfl⟩
      · intro hl
        rw [← hLmap] at hl
        obtain ⟨l', hl', he⟩ := hl
        rwa [← β.injective he]
    set P := L.map (MulAut.conj : T →* MulAut T) with hPdef
    have hP : P ≤ centDer X (MulAut.conj z) := by
      have hCX : C.map (MulAut.conj : T →* MulAut T) ≤ X ⊓ centralizer {MulAut.conj z} := by
        rintro _ ⟨c, hc', rfl⟩
        refine ⟨⟨c, rfl⟩, ?_⟩
        have hc'' : c * z = z * c := by
          rw [SetLike.mem_coe, hC, mem_centralizer_singleton_iff] at hc'
          exact hc'
        show MulAut.conj c ∈ centralizer {MulAut.conj z}
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc'']
      rw [hPdef, hL, map_commutator]
      exact commutator_mono hCX hCX
    have hPperf : ⁅P, P⁆ = P := by rw [hPdef, ← map_commutator, hperf]
    have hP4 : FourProp P := (fourProp_map_iff _ hinj L).mpr h4
    have hβn : β ∈ normalizer (P : Set (MulAut T)) := by
      rw [mem_normalizer_iff]
      intro n
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨β l, (hβL l).mp hl, (mulAut_mul_conj_mul_inv β l).symm⟩
      · rintro ⟨l, hl, he⟩
        refine ⟨β⁻¹ l, (hβL _).mpr (by simpa using hl), ?_⟩
        have h1 : MulAut.conj (β⁻¹ l) = β⁻¹ * MulAut.conj l * β := by
          simpa using (mulAut_mul_conj_mul_inv β⁻¹ l).symm
        change MulAut.conj (β⁻¹ l) = n
        rw [h1]
        change MulAut.conj l = β * n * β⁻¹ at he
        rw [he]
        group
    have hβc : β ∉ centralizer (P : Set (MulAut T)) := by
      intro hc'
      have hfixL : ∀ l ∈ L, β l = l := by
        intro l hl
        apply hinj
        have h := mem_centralizer_iff.mp hc' (MulAut.conj l) ⟨l, hl, rfl⟩
        rw [← mulAut_mul_conj_mul_inv, ← h, mul_inv_cancel_right]
      have hβ2 : β * β = 1 := by rw [← sq]; exact hE.2 β hβE
      rcases hfix β hβ2 hfixL with h | h
      · exact hβz (h ▸ one_mem _)
      · exact hβz (h ▸ mem_zpowers _)
    exact yWitness_of_perfect hιE hι1 hβE hP hPperf hP4 hβn hβc

theorem sporadicCaseOdd_of_yCensus_of_simple (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {s : TauCeti.SporadicName} {X₀ W : Type*} [Group X₀] [Group W] [Finite W] {X : Subgroup W}
    (hW : AutModel X₀ W X) (hc : YCensus X (fun _ => False))
    (hiso : ∀ (Q : Type) [Group Q], IsSimpleGroup Q →
      (Q ≃* Blueprint.NativeSporadic.Carrier s) → Nonempty (Q ≃* X₀)) :
    SporadicCaseOdd s := by
  intro G _ _ A hH hodd ⟨e⟩
  obtain ⟨e'⟩ := hiso _ hH.standard.1.2 e
  have hcII : YCensus X (· ≤ X) := fun E h1 h2 _ => hc E h1 h2 id
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus hW hcII hH.standard.1.1 e', hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, -, g, -, T, -, -, hExc⟩ := exc_of_yCensus h32 h33 hyp hW e'
  exact hExc _ hc

end CFSG.ComponentClassification.RankTwoSporadic
