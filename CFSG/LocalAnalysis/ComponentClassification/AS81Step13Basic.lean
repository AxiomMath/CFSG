module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf [Finite G] {H R : Subgroup G} (hR : R ≤ normalizer (H : Set G)) :
    Nat.card (H ⊔ R : Subgroup G) * Nat.card (H ⊓ R : Subgroup G) =
      Nat.card H * Nat.card R := by
  have h1 := Subgroup.relIndex_mul_card H (H ⊔ R)
  rw [inf_eq_left.mpr le_sup_left, AschbacherTheorem3.relIndex_sup_of_le_normalizer hR] at h1
  have h2 := Subgroup.relIndex_mul_card H R
  rw [← h1, ← h2]
  ring

theorem isPGroup_two_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    IsPGroup 2 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem isElemAbelian_sup_of_le_centralizer {H R : Subgroup G} (hH : IsElemAbelian 2 H)
    (hR : IsElemAbelian 2 R) (hHR : H ≤ centralizer (R : Set G)) :
    IsElemAbelian 2 (H ⊔ R) := by
  have hcH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hH.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hHR' : ∀ h ∈ H, ∀ r ∈ R, h * r = r * h := fun h hh r hr =>
    (mem_centralizer_iff.mp (hHR hh) r hr).symm
  have hmem : ∀ x ∈ H ⊔ R, ∃ h ∈ H, ∃ r ∈ R, h * r = x := by
    intro x hx
    have hx' : x ∈ ((H ⊔ R : Subgroup G) : Set G) := hx
    rw [coe_mul_of_left_le_normalizer_right H R
      (hHR.trans (Subgroup.centralizer_le_normalizer _)), Set.mem_mul] at hx'
    exact hx'
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨h, hh, r, hr, ha⟩ := hmem a a.2
    obtain ⟨h', hh', r', hr', hb⟩ := hmem b b.2
    simp only [coe_mul]
    rw [← ha, ← hb]
    calc h * r * (h' * r') = h * (r * h') * r' := by group
      _ = h * (h' * r) * r' := by rw [← hHR' h' hh' r hr]
      _ = h * h' * (r * r') := by group
      _ = h' * h * (r' * r) := by rw [hcH h hh h' hh', hcR r hr r' hr']
      _ = h' * (h * r') * r := by group
      _ = h' * (r' * h) * r := by rw [hHR' h hh r' hr']
      _ = h' * r' * (h * r) := by group
  · obtain ⟨h, hh, r, hr, rfl⟩ := hmem x hx
    have h2 : (h * r) ^ 2 = h ^ 2 * r ^ 2 := by
      rw [sq, sq, sq]
      calc h * r * (h * r) = h * (r * h) * r := by group
        _ = h * (h * r) * r := by rw [← hHR' h hh r hr]
        _ = h * h * (r * r) := by group
    rw [h2, hH.2 h hh, hR.2 r hr, one_mul]

theorem isElemAbelian_subgroupOf {E : Subgroup G} (hE : IsElemAbelian 2 E) (N : Subgroup G) :
    IsElemAbelian 2 (E.subgroupOf N) := CFSG.Open.IsElemAbelian.subgroupOf hE N

theorem sup_le_normalizer_left {A R : Subgroup G} (hRA : R ≤ centralizer (A : Set G)) :
    A ⊔ R ≤ normalizer (A : Set G) :=
  sup_le le_normalizer (hRA.trans (Subgroup.centralizer_le_normalizer _))

theorem sup_le_normalizer_right {A R : Subgroup G} (hRA : R ≤ centralizer (A : Set G)) :
    A ⊔ R ≤ normalizer (R : Set G) :=
  sup_le ((le_centralizer_iff.mp hRA).trans (Subgroup.centralizer_le_normalizer _))
    le_normalizer

theorem le_of_isSylowOf_of_le_normalizer [Finite G] {P L Q : Subgroup G}
    (hP : IsSylowOf 2 P L) (hQ : IsPGroup 2 Q) (hQL : Q ≤ L)
    (hLQ : L ≤ normalizer (Q : Set G)) : Q ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (P ⊔ Q : Subgroup G) :=
    hP.isPGroup.to_sup_of_normal_right' hQ (hP.le.trans hLQ)
  have := hP.eq_of_le le_sup_left (sup_le hP.le hQL) h2
  rw [← this]
  exact le_sup_right

theorem exists_eq_mul_of_le_sup {A R D : Subgroup G} (hRA : R ≤ centralizer (A : Set G))
    (hRD : R ≤ D) (hDAR : D ≤ A ⊔ R) {d : G} (hd : d ∈ D) :
    ∃ a ∈ D ⊓ A, ∃ r ∈ R, d = a * r := by
  have hd' : d ∈ ((R ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hDAR hd
  rw [coe_mul_of_left_le_normalizer_right R A (hRA.trans (Subgroup.centralizer_le_normalizer _)),
    Set.mem_mul] at hd'
  obtain ⟨r, hr, a, ha, rfl⟩ := hd'
  have haD : a ∈ D := by
    have := D.mul_mem (D.inv_mem (hRD hr)) hd
    simpa using this
  exact ⟨a, ⟨haD, ha⟩, r, hr, (mem_centralizer_iff.mp (hRA hr) a ha).symm⟩

theorem centerIn_le_sup_of_le_sup {A R D : Subgroup G} (hRA : R ≤ centralizer (A : Set G))
    (hRD : R ≤ D) (hDAR : D ≤ A ⊔ R) : centerIn D ≤ centerIn (D ⊓ A) ⊔ R := by
  intro d hd
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRD hDAR hd.1
  refine mul_mem (mem_sup_left ⟨ha, ?_⟩) (mem_sup_right hr)
  show a ∈ centralizer ((D ⊓ A : Subgroup G) : Set G)
  rw [mem_centralizer_iff]
  intro s hs
  have hs' : s ∈ D ⊓ A := hs
  have hd2 : a * r ∈ centralizer (D : Set G) := hd.2
  have h1 : s * (a * r) = a * r * s := mem_centralizer_iff.mp hd2 s hs'.1
  have h2 : s * r = r * s := mem_centralizer_iff.mp (hRA hr) s hs'.2
  have h3 : s * a * r = a * s * r := by
    calc s * a * r = s * (a * r) := by group
      _ = a * r * s := h1
      _ = a * (r * s) := by group
      _ = a * (s * r) := by rw [← h2]
      _ = a * s * r := by group
  exact mul_right_cancel h3

theorem sylow_sup_structure [Finite G] {A R D : Subgroup G}
    (hRA : R ≤ centralizer (A : Set G)) (hR : IsPGroup 2 R) (hD : IsSylowOf 2 D (A ⊔ R)) :
    R ≤ D ∧ IsSylowOf 2 (D ⊓ A) A ∧ D = (D ⊓ A) ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRD : R ≤ D :=
    le_of_isSylowOf_of_le_normalizer hD hR le_sup_right (sup_le_normalizer_right hRA)
  refine ⟨hRD, hD.inf_of_le_normalizer le_sup_left (sup_le_normalizer_left hRA),
    le_antisymm (fun d hd => ?_) (sup_le inf_le_left hRD)⟩
  obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hRD hD.le hd
  exact mul_mem (mem_sup_left ha) (mem_sup_right hr)

theorem exists_isSylowOf_sup_le_centralizer [Finite G] {A R : Subgroup G}
    (hRA : R ≤ centralizer (A : Set G)) (hR : IsElemAbelian 2 R)
    (hcent : ∀ a ∈ A, a ^ 2 = 1 → ∃ T : Subgroup G, IsSylowOf 2 T A ∧
      T ≤ centralizer ({a} : Set G))
    {x : G} (hx : x ∈ A ⊔ R) (hx2 : x ^ 2 = 1) :
    ∃ D : Subgroup G, IsSylowOf 2 D (A ⊔ R) ∧ D ≤ centralizer ({x} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ r ∈ R, ∀ a ∈ A, r * a = a * r := fun r hr a ha =>
    (mem_centralizer_iff.mp (hRA hr) a ha).symm
  have hcR : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hx' : x ∈ ((R ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right R A (hRA.trans (Subgroup.centralizer_le_normalizer _)),
    Set.mem_mul] at hx'
  obtain ⟨r, hr, a, ha, rfl⟩ := hx'
  have ha2 : a ^ 2 = 1 := by
    rw [Commute.mul_pow (hcomm r hr a ha) 2, hR.2 r hr, one_mul] at hx2
    exact hx2
  obtain ⟨T, hT, hTa⟩ := hcent a ha ha2
  obtain ⟨D, hD, hTD⟩ :=
    AschbacherTheorem3.exists_isSylowOf_le hT.isPGroup (hT.le.trans le_sup_left)
  obtain ⟨hRD, -, -⟩ := sylow_sup_structure hRA (isPGroup_two_of_isElemAbelian hR) hD
  have hDA : D ⊓ A = T :=
    hT.eq_of_le (le_inf hTD hT.le) inf_le_right (hD.isPGroup.to_le inf_le_left)
  refine ⟨D, hD, fun d hd => ?_⟩
  obtain ⟨a', ha', r', hr', rfl⟩ := exists_eq_mul_of_le_sup hRA hRD hD.le hd
  rw [hDA] at ha'
  have haa' : a' * a = a * a' := mem_centralizer_singleton_iff.mp (hTa ha')
  rw [mem_centralizer_singleton_iff]
  calc a' * r' * (r * a) = a' * (r' * r) * a := by group
    _ = a' * (r * r') * a := by rw [hcR r' hr' r hr]
    _ = a' * r * (r' * a) := by group
    _ = r * a' * (a * r') := by rw [← hcomm r hr a' (hT.le ha'), hcomm r' hr' a ha]
    _ = r * (a' * a) * r' := by group
    _ = r * (a * a') * r' := by rw [haa']
    _ = r * a * (a' * r') := by group

theorem exists_isSylowOf_le_centralizer_of_le [Finite G] {M D₁ U : Subgroup G} {x : G}
    (hD₁ : IsSylowOf 2 D₁ M) (hD₁x : D₁ ≤ centralizer ({x} : Set G)) (hU : IsPGroup 2 U)
    (hUM : U ≤ M) (hUx : U ≤ centralizer ({x} : Set G)) :
    ∃ D : Subgroup G, IsSylowOf 2 D M ∧ U ≤ D ∧ D ≤ centralizer ({x} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD, hUD⟩ := AschbacherTheorem3.exists_isSylowOf_le hU (le_inf hUM hUx)
  have h1 : Nat.card D₁ ≤ Nat.card D :=
    AschbacherTheorem3.card_le_of_isSylowOf hD hD₁.isPGroup (le_inf hD₁.le hD₁x)
  have h2 : Nat.card D ≤ Nat.card D₁ :=
    AschbacherTheorem3.card_le_of_isSylowOf hD₁ hD.isPGroup (hD.le.trans inf_le_left)
  refine ⟨D, isSylowOf_of_card (hD.le.trans inf_le_left) ?_, hUD, hD.le.trans inf_le_right⟩
  rw [← hD₁.card_eq]
  omega

theorem le_sup_of_le_sup_normalizer [Finite G] {A R T : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hT : IsPGroup 2 T)
    (hTN : T ≤ normalizer (R : Set G)) (hTAK : T ≤ A ⊔ centralizer (A : Set G)) :
    T ≤ A ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKA : centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _
  intro x hx
  have hxKA : x ∈ ((centralizer (A : Set G) ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hTAK hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hKA, Set.mem_mul] at hxKA
  obtain ⟨k, hk, a, ha, rfl⟩ := hxKA
  have hka : Commute k a := (mem_centralizer_iff.mp hk a ha).symm
  have haC : a ∈ centralizer (R : Set G) :=
    mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hR.le hr) a ha).symm
  have hkN : k ∈ normalizer (R : Set G) := by
    have h1 := (normalizer (R : Set G)).mul_mem (hTN hx)
      ((normalizer (R : Set G)).inv_mem (Subgroup.centralizer_le_normalizer _ haC))
    simpa using h1
  obtain ⟨n, hn⟩ := hT ⟨k * a, hx⟩
  have hn' : (k * a) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hkA : k ^ (2 ^ n) ∈ A := by
    have h1 : k ^ (2 ^ n) * a ^ (2 ^ n) = 1 := by rw [← hka.mul_pow]; exact hn'
    rw [eq_inv_of_mul_eq_one_left h1]
    exact A.inv_mem (A.pow_mem ha _)
  obtain ⟨y, hy, hy2, w, hw, hwo, hkyw⟩ := exists_two_mul_odd k
  have hwA : w ∈ A := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
    have hcop : Nat.Coprime (2 ^ n) (orderOf (k ^ j)) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hwo)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have h1 : (k ^ j) ^ (2 ^ n) ∈ A := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact A.zpow_mem hkA j
    rw [← hm]
    exact A.pow_mem h1 m
  have hyK : y ∈ centralizer (A : Set G) := (zpowers_le.mpr hk) hy
  have hyN : y ∈ normalizer (R : Set G) := (zpowers_le.mpr hkN) hy
  have hsup : R ⊔ zpowers y = R :=
    hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hyK))
      (hR.isPGroup.to_sup_of_normal_left' hy2 (zpowers_le.mpr hyN))
  have hyR : y ∈ R := hsup ▸ mem_sup_right (mem_zpowers y)
  rw [hkyw, mul_assoc]
  exact mul_mem (mem_sup_right hyR) (mem_sup_left (A.mul_mem hwA ha))

theorem commutator_le_of_le_sup {B U D : Subgroup G} (hU : U ≤ centralizer (B : Set G))
    (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hD : D ≤ B ⊔ U) : ⁅D, D⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  have hdec : ∀ d ∈ D, ∃ b ∈ B, ∃ u ∈ U, d = b * u := by
    intro d hd
    have hd' : d ∈ ((B ⊔ U : Subgroup G) : Set G) := hD hd
    rw [coe_mul_of_left_le_normalizer_right B U
      ((le_centralizer_iff.mp hU).trans (Subgroup.centralizer_le_normalizer _)), Set.mem_mul] at hd'
    obtain ⟨b, hb, u, hu, rfl⟩ := hd'
    exact ⟨b, hb, u, hu, rfl⟩
  intro d₁ hd₁ d₂ hd₂
  obtain ⟨b₁, hb₁, u₁, hu₁, rfl⟩ := hdec d₁ hd₁
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := hdec d₂ hd₂
  have h1 : u₁ * b₂ = b₂ * u₁ := (mem_centralizer_iff.mp (hU hu₁) b₂ hb₂).symm
  have h2 : Commute u₂ b₁⁻¹ :=
    Commute.inv_right (mem_centralizer_iff.mp (hU hu₂) b₁ hb₁).symm
  have h3 : u₁ * u₂ = u₂ * u₁ := hUc u₁ hu₁ u₂ hu₂
  have key : ⁅b₁ * u₁, b₂ * u₂⁆ = ⁅b₁, b₂⁆ := by
    simp only [commutatorElement_def]
    calc b₁ * u₁ * (b₂ * u₂) * (b₁ * u₁)⁻¹ * (b₂ * u₂)⁻¹
        = b₁ * (u₁ * b₂) * u₂ * u₁⁻¹ * b₁⁻¹ * u₂⁻¹ * b₂⁻¹ := by group
      _ = b₁ * (b₂ * u₁) * u₂ * u₁⁻¹ * b₁⁻¹ * u₂⁻¹ * b₂⁻¹ := by rw [h1]
      _ = b₁ * b₂ * (u₁ * u₂ * u₁⁻¹) * b₁⁻¹ * u₂⁻¹ * b₂⁻¹ := by group
      _ = b₁ * b₂ * u₂ * b₁⁻¹ * u₂⁻¹ * b₂⁻¹ := by rw [h3, mul_inv_cancel_right]
      _ = b₁ * b₂ * (u₂ * b₁⁻¹) * u₂⁻¹ * b₂⁻¹ := by group
      _ = b₁ * b₂ * (b₁⁻¹ * u₂) * u₂⁻¹ * b₂⁻¹ := by rw [h2.eq]
      _ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := by group
  rw [key, commutatorElement_def]
  exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂) (B.inv_mem hb₁)) (B.inv_mem hb₂)

end Basic

end CFSG.ComponentClassification.AS81
