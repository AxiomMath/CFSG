module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductPerfect
import CFSG.LocalAnalysis.EvenBN.U5.ModelThree
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem s38d_quasisimple_normal {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center Q))) with
    h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅center Q, center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem s38d_exists_perfect_sup [Finite G] {Y N N₀ : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ normalizer (N : Set G)) (hY : ⁅Y, Y⁆ ⊔ N = Y) (hN₀Y : N₀ ≤ Y)
    (hN₀ : ⁅N₀, N₀⁆ = N₀) :
    ∃ X ≤ Y, N₀ ≤ X ∧ ⁅X, X⁆ = X ∧ X ⊔ N = Y := by
  classical
  let S : Set (Subgroup G) := {X | N₀ ≤ X ∧ X ≤ Y ∧ X ⊔ N = Y}
  have hS : S.Nonempty := ⟨Y, hN₀Y, le_rfl, sup_eq_left.2 hNY⟩
  obtain ⟨X, hXS, hmin⟩ := wellFounded_lt.has_min S hS
  obtain ⟨hN₀X, hXY, hXN⟩ := hXS
  have hXn : X ≤ normalizer (N : Set G) := hXY.trans hYN
  have hprod : (↑(X ⊔ N) : Set G) = (X : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X N hXn
  have hconj : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (mem_normalizer_iff.1 (hYN hy) n).1 hn
  have hXXle : ⁅X, X⁆ ≤ X := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hcomm : ⁅Y, Y⁆ ≤ ⁅X, X⁆ ⊔ N := by
    rw [commutator_le]
    intro a ha b hb
    rw [← hXN] at ha hb
    have ha' : a ∈ (X : Set G) * (N : Set G) := by rw [← hprod]; exact ha
    have hb' : b ∈ (X : Set G) * (N : Set G) := by rw [← hprod]; exact hb
    obtain ⟨x₁, hx₁, n₁, hn₁, rfl⟩ := ha'
    obtain ⟨x₂, hx₂, n₂, hn₂, rfl⟩ := hb'
    have hx₁Y : x₁ ∈ Y := hXY hx₁
    have hx₂Y : x₂ ∈ Y := hXY hx₂
    have hn₁Y : n₁ ∈ Y := hNY hn₁
    have hn₂Y : n₂ ∈ Y := hNY hn₂
    set b := x₂ * n₂ with hb
    have hbY : b ∈ Y := mul_mem hx₂Y hn₂Y
    have e : ⁅x₁ * n₁, x₂ * n₂⁆ = (x₁ * (n₁ * (b * n₁⁻¹ * b⁻¹)) * x₁⁻¹) * ⁅x₁, x₂⁆ *
        (x₂ * (x₁ * n₂ * x₁⁻¹ * n₂⁻¹) * x₂⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def, hb]
      group
    rw [e]
    have h1 : x₁ * (n₁ * (b * n₁⁻¹ * b⁻¹)) * x₁⁻¹ ∈ N :=
      hconj _ hx₁Y _ (mul_mem hn₁ (hconj _ hbY _ (inv_mem hn₁)))
    have h3 : x₂ * (x₁ * n₂ * x₁⁻¹ * n₂⁻¹) * x₂⁻¹ ∈ N :=
      hconj _ hx₂Y _ (mul_mem (hconj _ hx₁Y _ hn₂) (inv_mem hn₂))
    exact mul_mem (mul_mem (Subgroup.mem_sup_right h1)
      (Subgroup.mem_sup_left (commutator_mem_commutator hx₁ hx₂))) (Subgroup.mem_sup_right h3)
  have hsup : ⁅X, X⁆ ⊔ N = Y := by
    refine le_antisymm (sup_le (hXXle.trans hXY) hNY) ?_
    calc Y = ⁅Y, Y⁆ ⊔ N := hY.symm
      _ ≤ ⁅X, X⁆ ⊔ N := sup_le hcomm le_sup_right
  have hN₀le : N₀ ≤ ⁅X, X⁆ := by
    rw [← hN₀]
    exact commutator_mono hN₀X hN₀X
  have hEq : ⁅X, X⁆ = X := by
    by_contra hne
    exact hmin ⁅X, X⁆ ⟨hN₀le, hXXle.trans hXY, hsup⟩ (lt_of_le_of_ne hXXle hne)
  exact ⟨X, hXY, hN₀X, hEq, hXN⟩

theorem s38d_map_conj_eq {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 hx
  · intro x hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply]; group⟩
    have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    simpa using this

theorem s38d_conj_mem_commutator {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G))
    {c : G} (hc : c ∈ ⁅H, H⁆) : g * c * g⁻¹ ∈ ⁅H, H⁆ := by
  have h2 : (⁅H, H⁆).map (MulAut.conj g).toMonoidHom = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, s38d_map_conj_eq hg]
  have : g * c * g⁻¹ ∈ (⁅H, H⁆).map (MulAut.conj g).toMonoidHom := ⟨c, hc, rfl⟩
  rwa [h2] at this

theorem s38d_commutator_le_self (X : Subgroup G) : ⁅X, X⁆ ≤ X := by
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem s38d_perfect_subgroupOf {X H : Subgroup G} (hXH : X ≤ H) (hX : ⁅X, X⁆ = X) :
    ⁅X.subgroupOf H, X.subgroupOf H⁆ = X.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXH, hX]

theorem s38d_commutator_mul_central {x₁ x₂ w₁ w₂ : G}
    (h12 : w₁ * x₂ = x₂ * w₁) (h21 : w₂ * x₁ = x₁ * w₂) (hww : w₁ * w₂ = w₂ * w₁) :
    ⁅x₁ * w₁, x₂ * w₂⁆ = ⁅x₁, x₂⁆ := by
  have c12 : Commute w₁ x₂ := h12
  have c21 : Commute w₂ x₁ := h21
  have cww : Commute w₁ w₂ := hww
  have c22 : Commute w₂ x₁⁻¹ := c21.inv_right
  have c12' : Commute w₂ w₁⁻¹ := cww.symm.inv_right
  simp only [commutatorElement_def, mul_inv_rev]
  calc x₁ * w₁ * (x₂ * w₂) * (w₁⁻¹ * x₁⁻¹) * (w₂⁻¹ * x₂⁻¹)
      = x₁ * (w₁ * x₂) * (w₂ * w₁⁻¹) * x₁⁻¹ * (w₂⁻¹ * x₂⁻¹) := by group
    _ = x₁ * (x₂ * w₁) * (w₁⁻¹ * w₂) * x₁⁻¹ * (w₂⁻¹ * x₂⁻¹) := by rw [h12, c12'.eq]
    _ = x₁ * x₂ * w₂ * x₁⁻¹ * (w₂⁻¹ * x₂⁻¹) := by group
    _ = x₁ * x₂ * (w₂ * x₁⁻¹) * (w₂⁻¹ * x₂⁻¹) := by group
    _ = x₁ * x₂ * (x₁⁻¹ * w₂) * (w₂⁻¹ * x₂⁻¹) := by rw [c22.eq]
    _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by group

theorem s38d_normalClosure_perfect {Q : Type*} [Group Q] {N : Subgroup Q} (hN : ⁅N, N⁆ = N) :
    ⁅normalClosure (N : Set Q), normalClosure (N : Set Q)⁆ = normalClosure (N : Set Q) := by
  apply le_antisymm (s38d_commutator_le_self _)
  haveI : (normalClosure (N : Set Q)).Normal := Subgroup.normalClosure_normal
  haveI : ⁅normalClosure (N : Set Q), normalClosure (N : Set Q)⁆.Normal := inferInstance
  refine normalClosure_le_normal fun x hx => ?_
  have : x ∈ ⁅N, N⁆ := by rw [hN]; exact hx
  exact commutator_mono subset_normalClosure subset_normalClosure this

theorem s38d_commutator_sup_le {X N : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) :
    ⁅X ⊔ N, X ⊔ N⁆ ≤ ⁅X, X⁆ ⊔ N := by
  have hprod : (↑(X ⊔ N) : Set G) = (X : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X N hXN
  have hconj : ∀ y ∈ X ⊔ N, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn => by
    have hy' : y ∈ (X : Set G) * (N : Set G) := by rw [← hprod]; exact hy
    obtain ⟨x, hx, m, hm, rfl⟩ := hy'
    have : x * m * n * (x * m)⁻¹ = x * (m * n * m⁻¹) * x⁻¹ := by group
    rw [show x * m * n * (x * m)⁻¹ = x * (m * n * m⁻¹) * x⁻¹ by group]
    exact (mem_normalizer_iff.1 (hXN hx) _).1 (mul_mem (mul_mem hm hn) (inv_mem hm))
  rw [commutator_le]
  intro a ha b hb
  have ha' : a ∈ (X : Set G) * (N : Set G) := by rw [← hprod]; exact ha
  have hb' : b ∈ (X : Set G) * (N : Set G) := by rw [← hprod]; exact hb
  obtain ⟨x₁, hx₁, n₁, hn₁, rfl⟩ := ha'
  obtain ⟨x₂, hx₂, n₂, hn₂, rfl⟩ := hb'
  have hx₁Y : x₁ ∈ X ⊔ N := Subgroup.mem_sup_left hx₁
  have hx₂Y : x₂ ∈ X ⊔ N := Subgroup.mem_sup_left hx₂
  have hbY : x₂ * n₂ ∈ X ⊔ N := mul_mem hx₂Y (Subgroup.mem_sup_right hn₂)
  have e : ⁅x₁ * n₁, x₂ * n₂⁆ = (x₁ * (n₁ * ((x₂ * n₂) * n₁⁻¹ * (x₂ * n₂)⁻¹)) * x₁⁻¹) *
      ⁅x₁, x₂⁆ * (x₂ * (x₁ * n₂ * x₁⁻¹ * n₂⁻¹) * x₂⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [e]
  have h1 : x₁ * (n₁ * ((x₂ * n₂) * n₁⁻¹ * (x₂ * n₂)⁻¹)) * x₁⁻¹ ∈ N :=
    hconj _ hx₁Y _ (mul_mem hn₁ (hconj _ hbY _ (inv_mem hn₁)))
  have h3 : x₂ * (x₁ * n₂ * x₁⁻¹ * n₂⁻¹) * x₂⁻¹ ∈ N :=
    hconj _ hx₂Y _ (mul_mem (hconj _ hx₁Y _ hn₂) (inv_mem hn₂))
  exact mul_mem (mul_mem (Subgroup.mem_sup_right h1)
    (Subgroup.mem_sup_left (commutator_mem_commutator hx₁ hx₂))) (Subgroup.mem_sup_right h3)

theorem s38d_goursat {J : Type*} [Group J] [IsSimpleGroup J] {S : Subgroup (J × J)}
    (hS : ∀ j : J, (j, j) ∈ S) : (∀ p ∈ S, p.1 = p.2) ∨ S = ⊤ := by
  let T : Subgroup J :=
    { carrier := {y | ((1 : J), y) ∈ S}
      mul_mem' := fun {a b} ha hb => by
        have := S.mul_mem ha hb
        simpa using this
      one_mem' := S.one_mem
      inv_mem' := fun {a} ha => by
        have := S.inv_mem ha
        simpa using this }
  have hTn : T.Normal := ⟨fun y hy g => by
    have h1 := S.mul_mem (S.mul_mem (hS g) hy) (S.inv_mem (hS g))
    show ((1 : J), g * y * g⁻¹) ∈ S
    simpa using h1⟩
  rcases (haveI := hTn; IsSimpleGroup.eq_bot_or_eq_top_of_normal T) with hT | hT
  · left
    rintro ⟨a, b⟩ hp
    have h1 := S.mul_mem hp (S.inv_mem (hS a))
    have h2 : b * a⁻¹ ∈ T := by
      show ((1 : J), b * a⁻¹) ∈ S
      simpa using h1
    rw [hT, Subgroup.mem_bot] at h2
    exact (mul_inv_eq_one.1 h2).symm
  · right
    rw [eq_top_iff]
    rintro ⟨a, b⟩ _
    have h2 : a⁻¹ * b ∈ T := by rw [hT]; exact Subgroup.mem_top _
    have h3 : ((1 : J), a⁻¹ * b) ∈ S := h2
    have h4 := S.mul_mem (hS a) h3
    simpa using h4

structure ProdLayer {H : Type*} [Group H] (J : Subgroup H) (a : H) : Prop where
  centr : centralizer (normalClosure (J : Set H) : Set H) = ⊥
  psi : ∃ ψ : (normalClosure (J : Set H)) ≃* J × J,
    (∀ (j : H) (hjJ : j ∈ J) (hjD : j ∈ normalClosure (J : Set H)),
      ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) ∧
    ∀ (d : H) (hd : d ∈ normalClosure (J : Set H))
      (hda : a⁻¹ * d * a ∈ normalClosure (J : Set H)),
      ψ ⟨a⁻¹ * d * a, hda⟩ = (ψ ⟨d, hd⟩).swap

theorem s38d_prodLayer {H : Type*} [Group H] {J : Subgroup H} {a : H}
    (hc : CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayerConclusion J a)
    (hns : ¬ IsSimpleGroup (CFSG.layer H)) : ProdLayer J a := by
  obtain ⟨-, -, -, hnc, hcen, halt, -⟩ := hc
  refine ⟨hcen, ?_⟩
  rw [← hnc] at hns
  rcases halt with ⟨hP, -⟩ | ⟨hQ, -⟩
  · exact absurd hP.1 hns
  · obtain ⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -, -, ψ, hψ1, hψ2⟩ := hQ
    exact ⟨ψ, hψ1, hψ2⟩

theorem ProdLayer.center_eq_bot {H : Type*} [Group H] {J : Subgroup H} {a : H}
    (hP : ProdLayer J a) (z : J) (hz : ∀ y : J, z * y = y * z) : z = 1 := by
  obtain ⟨ψ, hψ1, -⟩ := hP.psi
  have hzD : (z : H) ∈ normalClosure (J : Set H) := subset_normalClosure z.2
  set d : ↥(normalClosure (J : Set H)) := ψ.symm (z, 1) with hd
  have hdc : (d : H) ∈ centralizer (normalClosure (J : Set H) : Set H) := by
    rw [mem_centralizer_iff]
    intro e he
    have h1 : ψ (⟨e, he⟩ * d) = ψ (d * ⟨e, he⟩) := by
      obtain ⟨y, y', hy⟩ : ∃ y y' : J, ψ ⟨e, he⟩ = (y, y') := ⟨_, _, rfl⟩
      rw [map_mul, map_mul, hd, MulEquiv.apply_symm_apply, hy]
      simp [Prod.ext_iff, hz y]
    exact congrArg Subtype.val (ψ.injective h1)
  rw [hP.centr, Subgroup.mem_bot] at hdc
  have h2 : d = 1 := Subtype.ext hdc
  have h3 : ψ d = (1, 1) := by rw [h2, map_one]; rfl
  rw [hd, MulEquiv.apply_symm_apply] at h3
  exact (Prod.mk.inj h3).1

theorem s38d_quot_equiv_image {F F' : Type*} [Group F] [Group F'] [Finite F] (θ : F →* F')
    (hθ : Odd (Nat.card θ.ker)) {K : Subgroup F} (hK : CFSG.Open.IsQuasisimple K)
    (hKev : ¬ Odd (Nat.card K))
    (hZ : ∀ z : K.map θ, (∀ y : K.map θ, z * y = y * z) → z = 1) :
    Nonempty (K ⧸ center K ≃* K.map θ) := by
  classical
  let φ : K →* K.map θ := (θ.comp K.subtype).codRestrict (K.map θ) (fun k => ⟨k, k.2, rfl⟩)
  have hφ : ∀ k : K, ((φ k : K.map θ) : F') = θ k := fun _ => rfl
  have hφs : Function.Surjective φ := by
    rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩
  have hker : φ.ker = center K := by
    apply le_antisymm
    · rcases s38d_quasisimple_normal hK (MonoidHom.normal_ker φ) with h | h
      · exfalso
        have hKle : K ≤ θ.ker := fun k hk => by
          have : φ ⟨k, hk⟩ = 1 := by
            have := (h ▸ Subgroup.mem_top (⟨k, hk⟩ : K) : (⟨k, hk⟩ : K) ∈ φ.ker)
            exact this
          have h2 := congrArg Subtype.val this
          rw [hφ] at h2
          exact h2
        exact hKev (Odd.of_dvd_nat hθ (Subgroup.card_dvd_of_le hKle))
      · exact h
    · intro z hz
      rw [MonoidHom.mem_ker]
      refine hZ (φ z) fun y => ?_
      obtain ⟨y', rfl⟩ := hφs y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y').symm]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem s38d_simple_image {F F' : Type*} [Group F] [Group F'] [Finite F] (θ : F →* F')
    (hθ : Odd (Nat.card θ.ker)) {K : Subgroup F} (hK : CFSG.Open.IsQuasisimple K)
    (hKev : ¬ Odd (Nat.card K))
    (hZ : ∀ z : K.map θ, (∀ y : K.map θ, z * y = y * z) → z = 1) :
    IsSimpleGroup (K.map θ) := by
  obtain ⟨e⟩ := s38d_quot_equiv_image θ hθ hK hKev hZ
  haveI := hK.2
  exact e.symm.isSimpleGroup

theorem s38d_quasi_image {F F' : Type*} [Group F] [Group F'] [Finite F] (θ : F →* F')
    (hθ : Odd (Nat.card θ.ker)) {K : Subgroup F} (hK : CFSG.Open.IsQuasisimple K)
    (hKev : ¬ Odd (Nat.card K))
    (hZ : ∀ z : K.map θ, (∀ y : K.map θ, z * y = y * z) → z = 1) :
    CFSG.Open.IsQuasisimple (K.map θ) := by
  obtain ⟨e⟩ := s38d_quot_equiv_image θ hθ hK hKev hZ
  haveI : IsSimpleGroup (K.map θ) := s38d_simple_image θ hθ hK hKev hZ
  refine ⟨?_, ?_⟩
  · haveI : Group.IsPerfect K := Group.isPerfect_def.2 hK.1
    haveI : Group.IsPerfect (K ⧸ center K) := inferInstance
    haveI : Group.IsPerfect (K.map θ) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Group.isPerfect_def.1 this
  · have hc : center (K.map θ) = ⊥ := by
      refine eq_bot_iff.2 fun z hz => ?_
      rw [Subgroup.mem_bot]
      exact hZ z fun y => (Subgroup.mem_center_iff.1 hz y).symm
    exact ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup

theorem s38d_two_element_mul_centralizer [Finite G] {E L I : Subgroup G}
    (hLE : L ≤ normalizer (E : Set G)) (hEL : E ≤ L) (hIE : I ≤ normalizer (E : Set G))
    (hE2 : IsPGroup 2 E) (hIodd : Odd (Nat.card I))
    (hcomm : ∀ x ∈ L, ∀ i ∈ I, x⁻¹ * (i * x * i⁻¹) ∈ E)
    {y : G} (hy : y ∈ L) {k : ℕ} (hyk : y ^ 2 ^ k = 1) :
    ∃ c ∈ L ⊓ centralizer (I : Set G), ∃ e ∈ E, y = c * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := E ⊔ zpowers y with hM
  have hyE : zpowers y ≤ normalizer (E : Set G) := zpowers_le.2 (hLE hy)
  have hyP : IsPGroup 2 (zpowers y) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyk, one_zpow]
  have hMP : IsPGroup 2 M := hE2.to_sup_of_normal_left' hyP hyE
  have hMsolv : Group.IsSolvable M := by
    haveI := hMP.isNilpotent
    infer_instance
  obtain ⟨n, hn⟩ := (isPGroup_iff_card_dvd_pow.1 hMP)
  have hcop : (Nat.card I).Coprime (Nat.card M) :=
    Nat.Coprime.coprime_dvd_right hn
      (Nat.Coprime.pow_right n (Nat.coprime_two_left.2 hIodd).symm)
  have hMN : M ≤ normalizer (E : Set G) := sup_le Subgroup.le_normalizer hyE
  have hSM : I ≤ normalizer (M : Set G) := by
    intro i hi
    refine mem_normalizer_fintype fun m hm => ?_
    have hle : M.map (MulAut.conj i).toMonoidHom ≤ M := by
      rw [hM, Subgroup.map_sup, MonoidHom.map_zpowers]
      refine sup_le ?_ ?_
      · rintro _ ⟨e, he, rfl⟩
        exact Subgroup.mem_sup_left ((mem_normalizer_iff.1 (hIE hi) e).1 he)
      · rw [zpowers_le]
        have h1 : i * y * i⁻¹ = y * (y⁻¹ * (i * y * i⁻¹)) := by group
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [h1]
        exact mul_mem (Subgroup.mem_sup_right (mem_zpowers y))
          (Subgroup.mem_sup_left (hcomm y hy i hi))
    exact hle ⟨m, hm, rfl⟩
  have hyM : y ∈ M := Subgroup.mem_sup_right (mem_zpowers y)
  obtain ⟨c, hc, e, he, hce⟩ :=
    CFSG.LocalAnalysis.EvenBN.Common.exists_mem_inf_centralizer_mul_of_coprime
      (le_sup_left : E ≤ M) hMN hSM hIE hMsolv hcop hyM fun s hs => hcomm y hy s hs
  have hML : M ≤ L := sup_le hEL (zpowers_le.2 hy)
  exact ⟨c, Subgroup.mem_inf.2 ⟨hML (Subgroup.mem_inf.1 hc).1, (Subgroup.mem_inf.1 hc).2⟩, e, he,
    hce⟩

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem s38d_perfect_le_normalClosure {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q} {a : Q}
    (hP : ProdLayer J a) (hJq : CFSG.Open.IsQuasisimple J)
    (hOut : Group.IsSolvable (Outer J)) {M : Subgroup Q} (hM : ⁅M, M⁆ = M) :
    M ≤ normalClosure (J : Set Q) := by
  obtain ⟨ψ, -, -⟩ := hP.psi
  set D := normalClosure (J : Set Q) with hD
  let ι₁ : J →* Q := D.subtype.comp (ψ.symm.toMonoidHom.comp (MonoidHom.inl J J))
  let ι₂ : J →* Q := D.subtype.comp (ψ.symm.toMonoidHom.comp (MonoidHom.inr J J))
  have hι₁ : Function.Injective ι₁ := fun x y hxy => by
    have h1 := Subtype.ext hxy
    have h2 := ψ.symm.injective h1
    exact (Prod.mk.inj h2).1
  have hι₂ : Function.Injective ι₂ := fun x y hxy => by
    have h1 := Subtype.ext hxy
    have h2 := ψ.symm.injective h1
    exact (Prod.mk.inj h2).2
  let e₁ : J ≃* ι₁.range := MonoidHom.ofInjective hι₁
  let e₂ : J ≃* ι₂.range := MonoidHom.ofInjective hι₂
  have hq₁ : CFSG.Open.IsQuasisimple ι₁.range := hJq.of_mulEquiv e₁.symm
  have hq₂ : CFSG.Open.IsQuasisimple ι₂.range := hJq.of_mulEquiv e₂.symm
  have hOut₁ : Group.IsSolvable (Outer ι₁.range) :=
    haveI := hOut
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e₁
  have hOut₂ : Group.IsSolvable (Outer ι₂.range) :=
    haveI := hOut
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e₂
  have h12 : ι₂.range ≤ centralizer (ι₁.range : Set Q) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have : ψ.symm (x, 1) * ψ.symm (1, y) = ψ.symm (1, y) * ψ.symm (x, 1) := by
      rw [← map_mul, ← map_mul]
      simp
    exact congrArg Subtype.val this
  have hsup : ι₁.range ⊔ ι₂.range = D := by
    apply le_antisymm
    · exact sup_le (fun _ ⟨x, hx⟩ => hx ▸ (ψ.symm (x, 1)).2) (fun _ ⟨x, hx⟩ => hx ▸ (ψ.symm (1, x)).2)
    · intro d hd
      obtain ⟨x, y, hxy⟩ : ∃ x y : J, ψ ⟨d, hd⟩ = (x, y) := ⟨_, _, rfl⟩
      have hd' : (⟨d, hd⟩ : D) = ψ.symm (x, 1) * ψ.symm (1, y) := by
        rw [← map_mul]
        have : ((x, 1) * (1, y) : J × J) = (x, y) := by simp
        rw [this, ← hxy, MulEquiv.symm_apply_apply]
      have hdd : d = ι₁ x * ι₂ y := congrArg Subtype.val hd'
      rw [hdd]
      exact mul_mem (Subgroup.mem_sup_left ⟨x, rfl⟩) (Subgroup.mem_sup_right ⟨y, rfl⟩)
  haveI : D.Normal := Subgroup.normalClosure_normal
  have hC : Odd (Nat.card (centralizer ((ι₁.range ⊔ ι₂.range : Subgroup Q) : Set Q))) := by
    rw [hsup, hP.centr]
    simp
  have hMN : M ≤ normalizer ((ι₁.range ⊔ ι₂.range : Subgroup Q) : Set Q) := by
    rw [hsup]
    exact Subgroup.le_normalizer_of_normal
  have := CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct.perfect_le_of_le_normalizer_sup
    hq₁ hq₂ h12 hOut₁ hOut₂ hC hM hMN
  rwa [hsup] at this

theorem s38d_normal_closure_of_conj {Q : Type*} [Group Q] (S : Set Q)
    (h : ∀ g : Q, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : (Subgroup.closure S).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (h g x hx)
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem s38d_closure_two_elements {K : Type*} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (hx : ∃ x : K, x ∉ center K ∧ ∃ k, x ^ 2 ^ k = 1) :
    Subgroup.closure {x : K | ∃ k, x ^ 2 ^ k = 1} = ⊤ := by
  set S : Set K := {x | ∃ k, x ^ 2 ^ k = 1} with hS
  have hSc : ∀ g : K, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    rintro g s ⟨k, hk⟩
    exact ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  haveI := s38d_normal_closure_of_conj S hSc
  rcases s38d_quasisimple_normal hK (inferInstance : (Subgroup.closure S).Normal) with h | h
  · exact h
  · exfalso
    obtain ⟨x, hxc, k, hk⟩ := hx
    exact hxc (h (Subgroup.subset_closure ⟨k, hk⟩))

end Generic

namespace Data

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s38d_E_le_centralizerSection (d : Data G h) : d.E ≤ centralizerSection d.L₂ d.E := by
  intro e he
  refine ⟨le_normalizer (d.E_le_L₂ he), le_normalizer he, fun x hx => ?_⟩
  have hxN : x⁻¹ ∈ normalizer (d.E : Set G) := inv_mem (d.L₂_le_normalizer_E hx)
  have h1 := (mem_normalizer_iff.1 hxN e).1 he
  rw [inv_inv] at h1
  have : x⁻¹ * (e * x * e⁻¹) = (x⁻¹ * e * x) * e⁻¹ := by group
  rw [this]
  exact mul_mem h1 (inv_mem he)

theorem s38d_centralizerSection_le (d : Data G h) :
    centralizerSection d.L₂ d.E ≤ normalizer (d.E : Set G) := fun _ hg => hg.2.1

theorem s38d_relIndex_eq (d : Data G h) :
    d.E.relIndex (centralizerSection d.L₂ d.E) =
      Nat.card (bar d.E (centralizerSection d.L₂ d.E)) := by
  have hEX := s38d_E_le_centralizerSection d
  have h1 := Subgroup.relIndex_mul_card (H := d.E) (K := centralizerSection d.L₂ d.E)
  have h2 := card_bar_mul hEX (s38d_centralizerSection_le d)
  rw [inf_of_le_left hEX] at h1
  have hpos : 0 < Nat.card d.E := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem s38d_bar_L₂_normal (d : Data G h) : (bar d.E d.L₂).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨n₀, rfl⟩ := proj_surjective n
  obtain ⟨g₀, rfl⟩ := proj_surjective g
  have hn₀ : (n₀ : G) ∈ d.L₂ := (mem_bar_iff d.E_le_L₂ n₀).1 hn
  rw [← map_inv, ← map_mul, ← map_mul, mem_bar_iff d.E_le_L₂]
  simp only [coe_mul, coe_inv]
  exact (mem_normalizer_iff.1 (d.normalizer_E_le_normalizer_L₂ g₀.2) _).1 hn₀

theorem s38d_bar_le (ho : d.Sec38Outcome) :
    bar d.E (centralizerSection d.L₂ d.E) ≤ OE d := by
  obtain ⟨ht, hout⟩ := ho
  have hcen := hout.1.2.2.2.2.1
  set π : Bar d.E →* Bar d.E ⧸ OE d := QuotientGroup.mk' (OE d) with hπ
  set S : Subgroup (Bar d.E ⧸ OE d) := (bar d.E d.L₂).map π with hS
  have hSn : S.Normal := (s38d_bar_L₂_normal d).map π (QuotientGroup.mk'_surjective _)
  have hAS : ((bar d.E d.N₂).map π : Subgroup (Bar d.E ⧸ OE d)) ≤ S :=
    map_mono (bar_mono d.N₂_le_L₂)
  have hnc : normalClosure (((bar d.E d.N₂).map π : Subgroup (Bar d.E ⧸ OE d)) :
      Set (Bar d.E ⧸ OE d)) ≤ S := normalClosure_le_normal hAS
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (x : G) ∈ centralizerSection d.L₂ d.E := hx
  have hycen : π (proj d.E x) ∈ centralizer (normalClosure (((bar d.E d.N₂).map π :
      Subgroup (Bar d.E ⧸ OE d)) : Set (Bar d.E ⧸ OE d)) : Set (Bar d.E ⧸ OE d)) := by
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨z₁, hz₁, rfl⟩ := hnc hz
    obtain ⟨z₀, rfl⟩ := proj_surjective z₁
    have hz₀L : (z₀ : G) ∈ d.L₂ := (mem_bar_iff d.E_le_L₂ z₀).1 hz₁
    have h1 : proj d.E z₀ = proj d.E (x * z₀ * x⁻¹) := by
      rw [proj_eq_proj_iff]
      simpa using hx'.2.2 _ hz₀L
    have h2 : proj d.E x * proj d.E z₀ = proj d.E z₀ * proj d.E x := by
      have h3 : proj d.E (x * z₀ * x⁻¹) = proj d.E z₀ := h1.symm
      rw [map_mul, map_mul, map_inv] at h3
      exact mul_inv_eq_iff_eq_mul.1 h3
    rw [← map_mul π, ← map_mul π, h2]
  rw [hcen, mem_bot] at hycen
  exact (QuotientGroup.eq_one_iff _).1 hycen

theorem s38d_odd (ho : d.Sec38Outcome) :
    Odd (d.E.relIndex (centralizerSection d.L₂ d.E)) := by
  rw [s38d_relIndex_eq]
  exact Odd.of_dvd_nat (GMSK.odd_card_standardComponentOddCore (Bar d.E))
    (Subgroup.card_dvd_of_le (s38d_bar_le ho))

theorem s38d_N₂_le_centralizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.N₂ ≤ centralizer (d.V : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, ψ, -, hker, hψ, hequiv⟩ := hd.sec3_3_one hGMS
  have hperf : Group.IsPerfect d.N₂ :=
    Group.isPerfect_def.2 (hd.quasisimple_lieModel_N₂ (X := d.N₂) ⟨MulEquiv.refl _⟩).1.1
  have hN : ∀ c ∈ d.N₂, c ∈ normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun c hc => ⟨Subgroup.centralizer_le_normalizer _ (hd.N₂_le_K₀ hc).1.2, (hd.N₂_le_K₀ hc).2⟩
  have hcZ : ∀ c ∈ d.N₂, ∀ z ∈ d.Zp, z * c = c * z := fun c hc z hz =>
    mem_centralizer_iff.1 (hd.N₂_le_K₀ hc).1.2 z hz
  have h1 : ⁅d.N₂, d.V⁆ ≤ d.Zp := by
    rw [commutator_le]
    intro c hc v hv
    obtain ⟨hv', he⟩ := hequiv c (hN c hc) ⟨v, hv⟩
    have e1 : ψ ⟨c * v * c⁻¹, hv'⟩ = ψ ⟨v, hv⟩ := by
      apply Subtype.ext
      rw [he]
      have := hcZ c hc _ (ψ ⟨v, hv⟩).2
      rw [← this]
      group
    have e2 : ψ (⟨c * v * c⁻¹, hv'⟩ * ⟨v, hv⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, e1, mul_inv_cancel]
    have e3 : (⟨c * v * c⁻¹, hv'⟩ * ⟨v, hv⟩⁻¹ : d.V) ∈ ψ.ker := e2
    rw [hker, mem_subgroupOf] at e3
    simpa [commutatorElement_def] using e3
  have h2 : ⁅⁅d.N₂, d.V⁆, d.N₂⁆ = ⊥ := by
    rw [eq_bot_iff]
    refine (commutator_mono h1 le_rfl).trans ?_
    rw [commutator_comm, ← eq_bot_iff, commutator_eq_bot_iff_le_centralizer]
    intro c hc z hz
    exact hcZ c hc z hz
  have h3 := CFSG.LocalCores.perfect_double_commutator hperf h2
  rw [commutator_eq_bot_iff_le_centralizer] at h3
  exact h3

theorem s38d_L₂_le_centralizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.L₂ ≤ centralizer (d.V : Set G) := by
  obtain ⟨-, -, -, -, -, hZ, -, -⟩ := hd.sec3_6 hGMS
  refine sup_le (hd.E_le_centralizer_V hGMS) ((closure_le _).2 ?_)
  rintro _ ⟨g, hg, n, hn, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro v hv
  have hgV : g ∈ normalizer (d.V : Set G) := by
    rw [← hZ]
    exact normalizer_le_normalizer_centerIn d.E hg
  have hv' : g⁻¹ * v * g ∈ d.V := by
    have := (mem_normalizer_iff.1 (inv_mem hgV) v).1 hv
    simpa using this
  have hcomm := mem_centralizer_iff.1 (s38d_N₂_le_centralizer_V hGMS hd hn) _ hv'
  calc v * (g * n * g⁻¹) = g * ((g⁻¹ * v * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
    _ = g * n * g⁻¹ * v := by group

theorem s38d_V_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V ≤ CFSG.centerIn d.L₂ := by
  intro v hv
  refine Subgroup.mem_inf.2 ⟨d.E_le_L₂ (d.V_le_E hv), ?_⟩
  rw [mem_centralizer_iff]
  intro x hx
  exact (mem_centralizer_iff.1 (s38d_L₂_le_centralizer_V hGMS hd hx) v hv).symm

theorem s38d_exists_involution_N₂ (hd : d.Hyp) : ∃ x ∈ d.N₂, x ≠ 1 ∧ x * x = 1 := by
  obtain ⟨hinf, -⟩ := d.isSylowOf_N₂_inf_P
  by_contra hcon
  push_neg at hcon
  have hcl := d.closure_involutions_CPI₂.1
  have hsub : {x | x ∈ d.CPI₂ ∧ x * x = 1} ⊆ {1} := by
    rintro x ⟨hx, hx2⟩
    have hxN : x ∈ d.N₂ := (hinf ▸ hx : x ∈ d.N₂ ⊓ d.P).1
    by_contra hne
    exact hcon x hxN hne hx2
  have hbot : d.CPI₆ = ⊥ := by
    rw [← hcl, eq_bot_iff, closure_le]
    intro x hx
    have := hsub hx
    rw [Set.mem_singleton_iff] at this
    simp [this]
  have hcard := d.card_CPI₆
  rw [hbot, Subgroup.card_bot] at hcard
  have h2 := hd.setting.two_le
  have : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  omega

theorem s38d_odd_I₂ (d : Data G h) : Odd (Nat.card d.I₂) :=
  Odd.of_dvd_nat d.odd_card_I (Subgroup.card_dvd_of_le d.I₂_le_I)

theorem s38d_N₂_two_gen (hd : d.Hyp) :
    d.N₂ ≤ closure {x | x ∈ d.N₂ ∧ ∃ k, x ^ 2 ^ k = 1} := by
  have hq := (hd.quasisimple_lieModel_N₂ (X := d.N₂) ⟨MulEquiv.refl _⟩).1
  obtain ⟨x, hxN, hx1, hx2⟩ := s38d_exists_involution_N₂ hd
  have hxc : (⟨x, hxN⟩ : d.N₂) ∉ center d.N₂ := by
    intro hc
    have hcomm : ∀ n ∈ d.N₂, x * n = n * x := fun n hn =>
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨n, hn⟩).symm
    have hxI : x ∈ d.I₂ := d.mem_I₂_of_comm_N₂ hxN hcomm
    have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [sq]) hx1
    have h2 := Subgroup.orderOf_dvd_natCard d.I₂ hxI
    rw [hord] at h2
    exact (Nat.not_even_iff_odd.2 (s38d_odd_I₂ d)) (even_iff_two_dvd.2 h2)
  have hgen := s38d_closure_two_elements hq
    ⟨⟨x, hxN⟩, hxc, 1, by apply Subtype.ext; simpa [pow_one, sq] using hx2⟩
  intro z hz
  have hz' : (⟨z, hz⟩ : d.N₂) ∈ Subgroup.closure {x : d.N₂ | ∃ k, x ^ 2 ^ k = 1} := by
    rw [hgen]; exact Subgroup.mem_top _
  have hmem : z ∈ (Subgroup.closure {x : d.N₂ | ∃ k, x ^ 2 ^ k = 1}).map d.N₂.subtype :=
    ⟨⟨z, hz⟩, hz', rfl⟩
  rw [MonoidHom.map_closure] at hmem
  refine closure_mono ?_ hmem
  rintro _ ⟨⟨y, hy⟩, ⟨k, hk⟩, rfl⟩
  exact ⟨hy, k, by simpa using congrArg Subtype.val hk⟩

theorem s38d_I₂_le_normalizer_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.I₂ ≤ normalizer (d.E : Set G) :=
  d.I₂_le_I.trans (hd.I_le_normalizer_B₄.trans (hd.normalizer_B₄_le_normalizer_E hGMS))

theorem s38d_isPGroup_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    IsPGroup 2 d.E :=
  IsPGroup.of_card (n := f * 14) (by rw [hd.card_E hGMS, ← pow_mul])

theorem s38d_L₂_le_sup_centralizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hI : ∀ x ∈ d.L₂, ∀ i ∈ d.I₂, x⁻¹ * (i * x * i⁻¹) ∈ d.E) :
    d.L₂ ≤ d.E ⊔ (d.L₂ ⊓ centralizer (d.I₂ : Set G)) := by
  set Z := d.E ⊔ (d.L₂ ⊓ centralizer (d.I₂ : Set G)) with hZ
  have hgen := s38d_N₂_two_gen hd
  refine sup_le le_sup_left ((closure_le _).2 ?_)
  rintro _ ⟨g, hg, n, hn, rfl⟩
  set N' : Subgroup G := d.N₂ ⊓ Z.comap (MulAut.conj g).toMonoidHom with hN'
  have hN'le : d.N₂ ≤ N' := by
    refine hgen.trans ((closure_le _).2 ?_)
    rintro y ⟨hyN, k, hk⟩
    refine Subgroup.mem_inf.2 ⟨hyN, ?_⟩
    have hyL : g * y * g⁻¹ ∈ d.L₂ :=
      Subgroup.mem_sup_right (subset_closure ⟨g, hg, y, hyN, rfl⟩)
    have hgyk : (g * y * g⁻¹) ^ 2 ^ k = 1 := by
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
    obtain ⟨c, hc, e, he, hce⟩ := s38d_two_element_mul_centralizer d.L₂_le_normalizer_E
      d.E_le_L₂ (s38d_I₂_le_normalizer_E hGMS hd) (s38d_isPGroup_E hGMS hd) (s38d_odd_I₂ d)
      hI hyL hgyk
    show g * y * g⁻¹ ∈ Z
    rw [hce]
    exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left he)
  exact (Subgroup.mem_inf.1 (hN'le hn)).2

abbrev s38dH (d : Data G h) : Subgroup G := centralizer (d.I₂ : Set G)

abbrev s38dO (d : Data G h) : Subgroup ↥d.s38dH := standardComponentOddCore ↥d.s38dH

abbrev s38dθ (d : Data G h) : ↥d.s38dH →* ↥d.s38dH ⧸ d.s38dO := QuotientGroup.mk' d.s38dO

abbrev s38dJ (d : Data G h) : Subgroup (↥d.s38dH ⧸ d.s38dO) :=
  (d.N₂.subgroupOf d.s38dH).map d.s38dθ

open CFSG.ComponentClassification.OuterAutomorphisms (Outer) in
theorem s38d_H₂_facts (hp : d.ProductCaseHyp) :
    ProdLayer d.s38dJ (d.s38dθ ⟨d.t, hp.hyp.t_mem_centralizer_I₂⟩) ∧
    (d.M₂.subgroupOf d.s38dH).map d.s38dθ = normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)) ∧
    CFSG.Open.IsQuasisimple d.s38dJ ∧ Group.IsSolvable (Outer d.s38dJ) ∧
      IsSimpleGroup ↥d.s38dJ := by
  obtain ⟨hout, hM⟩ := hp.hyp.sec3_3_two hp.gms
  have hP : ProdLayer d.s38dJ (d.s38dθ ⟨d.t, hp.hyp.t_mem_centralizer_I₂⟩) :=
    s38d_prodLayer hout.1 (fun hs => hp.caseB hs)
  have hM' : (d.M₂.subgroupOf d.s38dH).map d.s38dθ = normalClosure (d.s38dJ : Set _) :=
    hM.trans hout.1.2.2.2.1.symm
  have hKm := hp.hyp.quasisimple_lieModel_N₂ (X := d.N₂.subgroupOf d.s38dH)
    ⟨Subgroup.subgroupOfEquivOfLe d.N₂_le_centralizer_I₂⟩
  obtain ⟨x, hxN, hx1, hx2⟩ := s38d_exists_involution_N₂ hp.hyp
  have hxH : x ∈ d.s38dH := d.N₂_le_centralizer_I₂ hxN
  have hKev : ¬ Odd (Nat.card (d.N₂.subgroupOf d.s38dH)) := by
    have hordG : orderOf x = 2 := orderOf_eq_prime (by rwa [sq]) hx1
    have hmem : (⟨x, hxH⟩ : d.s38dH) ∈ d.N₂.subgroupOf d.s38dH := hxN
    have h2 := Subgroup.orderOf_dvd_natCard (d.N₂.subgroupOf d.s38dH) hmem
    rw [Subgroup.orderOf_mk, hordG] at h2
    exact fun hodd => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hθ : Odd (Nat.card d.s38dθ.ker) := by
    rw [QuotientGroup.ker_mk']
    exact GMSK.odd_card_standardComponentOddCore _
  have hZ : ∀ z : (d.N₂.subgroupOf d.s38dH).map d.s38dθ,
      (∀ y, z * y = y * z) → z = 1 := hP.center_eq_bot
  refine ⟨hP, hM', s38d_quasi_image d.s38dθ hθ hKm.1 hKev hZ, ?_,
    s38d_simple_image d.s38dθ hθ hKm.1 hKev hZ⟩
  obtain ⟨e⟩ := s38d_quot_equiv_image d.s38dθ hθ hKm.1 hKev hZ
  have hLM := CFSG.Blueprint.LieModel.of_mulEquiv e hKm.2
  exact CFSG.SeitzReduction.UnitaryPilot.isSolvable_outer_of_lieModel hLM

theorem s38d_L₂_le_commutator_sup (hd : d.Hyp) : d.L₂ ≤ ⁅d.L₂, d.L₂⁆ ⊔ d.E := by
  have hq := (hd.quasisimple_lieModel_N₂ (X := d.N₂) ⟨MulEquiv.refl _⟩).1
  have hP : Group.IsPerfect ↥d.N₂ := (Group.isPerfect_def (G := ↥d.N₂)).2 hq.1
  have hperf : ⁅d.N₂, d.N₂⁆ = d.N₂ := (Subgroup.isPerfect_iff (H := d.N₂)).1 hP
  refine sup_le le_sup_right ((closure_le _).2 ?_)
  rintro _ ⟨g, hg, n, hn, rfl⟩
  have hnc : n ∈ ⁅d.L₂, d.L₂⁆ := by
    have : n ∈ ⁅d.N₂, d.N₂⁆ := by rw [hperf]; exact hn
    exact commutator_mono d.N₂_le_L₂ d.N₂_le_L₂ this
  exact Subgroup.mem_sup_left
    (s38d_conj_mem_commutator (d.normalizer_E_le_normalizer_L₂ hg) hnc)

theorem s38d_exists_X (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hI : ∀ x ∈ d.L₂, ∀ i ∈ d.I₂, x⁻¹ * (i * x * i⁻¹) ∈ d.E) :
    ∃ X : Subgroup G, X ≤ d.L₂ ⊓ centralizer (d.I₂ : Set G) ∧ d.N₂ ≤ X ∧ ⁅X, X⁆ = X ∧
      d.E ⊔ X = d.L₂ := by
  set Y := d.L₂ ⊓ centralizer (d.I₂ : Set G) with hY
  set N := Y ⊓ d.E with hN
  have hNY : N ≤ Y := inf_le_left
  have hYL : Y ≤ d.L₂ := inf_le_left
  have hYE : Y ≤ normalizer (d.E : Set G) := hYL.trans d.L₂_le_normalizer_E
  have hYN : Y ≤ normalizer (N : Set G) := by
    intro y hy
    refine mem_normalizer_fintype fun n hn => ?_
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hy (Subgroup.mem_inf.1 hn).1) (inv_mem hy),
      (mem_normalizer_iff.1 (hYE hy) n).1 (Subgroup.mem_inf.1 hn).2⟩
  have hL₂ : d.L₂ ≤ d.E ⊔ Y := s38d_L₂_le_sup_centralizer hGMS hd hI
  have hL₂' : d.L₂ ≤ Y ⊔ d.E := by rw [sup_comm]; exact hL₂
  have h1 : d.L₂ ≤ ⁅Y, Y⁆ ⊔ d.E := by
    calc d.L₂ ≤ ⁅d.L₂, d.L₂⁆ ⊔ d.E := s38d_L₂_le_commutator_sup hd
      _ ≤ ⁅Y ⊔ d.E, Y ⊔ d.E⁆ ⊔ d.E := sup_le_sup_right (commutator_mono hL₂' hL₂') _
      _ ≤ (⁅Y, Y⁆ ⊔ d.E) ⊔ d.E := sup_le_sup_right (s38d_commutator_sup_le hYE) _
      _ = ⁅Y, Y⁆ ⊔ d.E := by rw [sup_assoc, sup_idem]
  have hYY : ⁅Y, Y⁆ ⊔ N = Y := by
    apply le_antisymm
    · exact sup_le (s38d_commutator_le_self Y) hNY
    · intro y hy
      have hy1 : y ∈ ⁅Y, Y⁆ ⊔ d.E := h1 (hYL hy)
      have hprod := Subgroup.coe_mul_of_left_le_normalizer_right ⁅Y, Y⁆ d.E
        ((s38d_commutator_le_self Y).trans hYE)
      have hy2 : y ∈ ((⁅Y, Y⁆ : Subgroup G) : Set G) * (d.E : Set G) := by
        rw [← hprod]; exact hy1
      obtain ⟨c, hc, e, he, rfl⟩ := hy2
      have hcY : c ∈ Y := s38d_commutator_le_self Y hc
      have heY : e ∈ Y := by
        have := mul_mem (inv_mem hcY) hy
        simpa using this
      exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨heY, he⟩))
  have hN₂Y : d.N₂ ≤ Y := le_inf d.N₂_le_L₂ d.N₂_le_centralizer_I₂
  have hP : Group.IsPerfect d.N₂ := (Group.isPerfect_def (G := ↥d.N₂)).2
    (hd.quasisimple_lieModel_N₂ (X := d.N₂) ⟨MulEquiv.refl _⟩).1.1
  have hperf : ⁅d.N₂, d.N₂⁆ = d.N₂ := (Subgroup.isPerfect_iff (H := d.N₂)).1 hP
  obtain ⟨X, hXY, hN₂X, hXperf, hXN⟩ := s38d_exists_perfect_sup hNY hYN hYY hN₂Y hperf
  refine ⟨X, hXY, hN₂X, hXperf, le_antisymm (sup_le d.E_le_L₂ (hXY.trans hYL)) ?_⟩
  calc d.L₂ ≤ d.E ⊔ Y := hL₂
    _ = d.E ⊔ (X ⊔ N) := by rw [hXN]
    _ ≤ d.E ⊔ X := sup_le le_sup_left (sup_le le_sup_right (inf_le_right.trans le_sup_left))

theorem s38d_M₂_subgroupOf (d : Data G h) :
    d.M₂.subgroupOf d.s38dH = normalClosure ((d.N₂.subgroupOf d.s38dH : Subgroup ↥d.s38dH) :
      Set ↥d.s38dH) :=
  Subgroup.comap_map_eq_self_of_injective d.s38dH.subtype_injective _

theorem s38d_M₂_le_H (d : Data G h) : d.M₂ ≤ d.s38dH := fun _ ⟨_, _, e⟩ => e ▸ Subtype.property _

theorem s38d_M₂_normal (d : Data G h) : (d.M₂.subgroupOf d.s38dH).Normal := by
  rw [s38d_M₂_subgroupOf]
  infer_instance

theorem s38d_theta_X_le (hp : d.ProductCaseHyp) {X : Subgroup G} (hXH : X ≤ d.s38dH)
    (hX : ⁅X, X⁆ = X) :
    (X.subgroupOf d.s38dH).map d.s38dθ ≤ normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)) := by
  obtain ⟨hP, hM', hq, hOut, -⟩ := s38d_H₂_facts hp
  have hX'p : ⁅X.subgroupOf d.s38dH, X.subgroupOf d.s38dH⁆ = X.subgroupOf d.s38dH :=
    s38d_perfect_subgroupOf hXH hX
  have hXθp : ⁅(X.subgroupOf d.s38dH).map d.s38dθ, (X.subgroupOf d.s38dH).map d.s38dθ⁆ =
      (X.subgroupOf d.s38dH).map d.s38dθ := by
    rw [← Subgroup.map_commutator, hX'p]
  exact s38d_perfect_le_normalClosure hP hq hOut hXθp

theorem s38d_X_le_M₂ (hp : d.ProductCaseHyp) {X : Subgroup G} (hXH : X ≤ d.s38dH)
    (hX : ⁅X, X⁆ = X) : X ≤ d.M₂ := by
  obtain ⟨hP, hM', hq, hOut, -⟩ := s38d_H₂_facts hp
  set X' : Subgroup ↥d.s38dH := X.subgroupOf d.s38dH with hX'
  have hX'p : ⁅X', X'⁆ = X' := s38d_perfect_subgroupOf hXH hX
  have hle := s38d_theta_X_le hp hXH hX
  have hMC : ∀ m ∈ X', ∃ n ∈ d.M₂.subgroupOf d.s38dH, n⁻¹ * m ∈ d.s38dO := by
    intro m hm
    have h1 : d.s38dθ m ∈ (d.M₂.subgroupOf d.s38dH).map d.s38dθ := by
      rw [hM']; exact hle ⟨m, hm, rfl⟩
    obtain ⟨n, hn, hnm⟩ := h1
    refine ⟨n, hn, ?_⟩
    have : d.s38dθ (n⁻¹ * m) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  haveI := s38d_M₂_normal d
  haveI : Group.IsSolvable d.s38dO :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (GMSK.odd_card_standardComponentOddCore _)
  have hres : X' ≤ d.M₂.subgroupOf d.s38dH :=
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct.perfect_le_of_forall_inv_mul_mem
      Subgroup.le_normalizer_of_normal hX'p Subgroup.le_normalizer_of_normal hMC
  intro x hx
  exact hres (show (⟨x, hXH hx⟩ : d.s38dH) ∈ X' from hx)

theorem s38d_theta_X_dichotomy (hp : d.ProductCaseHyp) {X : Subgroup G} (hXH : X ≤ d.s38dH)
    (hN₂X : d.N₂ ≤ X) (hX : ⁅X, X⁆ = X) :
    (X.subgroupOf d.s38dH).map d.s38dθ = normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)) ∨
      (X.subgroupOf d.s38dH).map d.s38dθ = d.s38dJ := by
  obtain ⟨hP, hM', hq, hOut, hJs⟩ := s38d_H₂_facts hp
  have hle := s38d_theta_X_le hp hXH hX
  have hJX : d.s38dJ ≤ (X.subgroupOf d.s38dH).map d.s38dθ :=
    Subgroup.map_mono (fun x hx => show (x : G) ∈ X from hN₂X hx)
  obtain ⟨ψ, hψ1, -⟩ := hP.psi
  let S' : Subgroup (↥d.s38dJ × ↥d.s38dJ) :=
    (((X.subgroupOf d.s38dH).map d.s38dθ).subgroupOf
      (normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)))).map ψ.toMonoidHom
  have hdiag : ∀ j : ↥d.s38dJ, (j, j) ∈ S' := fun j => by
    have hjD : (j : ↥d.s38dH ⧸ d.s38dO) ∈ normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)) :=
      subset_normalClosure j.2
    refine ⟨⟨j, hjD⟩, hJX j.2, ?_⟩
    have h0 := hψ1 j j.2 hjD
    simp only [Subtype.coe_eta] at h0
    exact h0
  rcases s38d_goursat hdiag with h | h
  · right
    refine le_antisymm (fun x hx => ?_) hJX
    have hxD := hle hx
    obtain ⟨a, b, hab⟩ : ∃ a b : ↥d.s38dJ, ψ ⟨x, hxD⟩ = (a, b) := ⟨_, _, rfl⟩
    have hmem : ψ ⟨x, hxD⟩ ∈ S' := ⟨⟨x, hxD⟩, hx, rfl⟩
    rw [hab] at hmem
    have hab' : a = b := h _ hmem
    have haD : (a : ↥d.s38dH ⧸ d.s38dO) ∈
        normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)) := subset_normalClosure a.2
    have h2 := hψ1 a a.2 haD
    have h3 : ψ ⟨x, hxD⟩ = ψ ⟨a, haD⟩ := by
      rw [hab, h2]
      subst hab'
      rfl
    have h4 : (⟨x, hxD⟩ : ↥(normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO)))) = ⟨a, haD⟩ :=
      ψ.injective h3
    have hxa : x = a := congrArg Subtype.val h4
    rw [hxa]
    exact a.2
  · left
    refine le_antisymm hle (fun z hz => ?_)
    have : ψ ⟨z, hz⟩ ∈ S' := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyz⟩ := this
    have h5 : y = ⟨z, hz⟩ := ψ.injective hyz
    rw [h5] at hy
    exact hy

theorem s38d_N₂_perfect (hd : d.Hyp) : ⁅d.N₂, d.N₂⁆ = d.N₂ := by
  have hP : Group.IsPerfect ↥d.N₂ := (Group.isPerfect_def (G := ↥d.N₂)).2
    (hd.quasisimple_lieModel_N₂ (X := d.N₂) ⟨MulEquiv.refl _⟩).1.1
  exact (Subgroup.isPerfect_iff (H := d.N₂)).1 hP

theorem s38d_M₂_le_X (hp : d.ProductCaseHyp)
    (hO : ∀ o : ↥d.s38dH, o ∈ d.s38dO → ∀ n ∈ d.N₂, (o : G) * n = n * (o : G))
    {X : Subgroup G} (hXH : X ≤ d.s38dH) (hX : ⁅X, X⁆ = X)
    (hθ : (X.subgroupOf d.s38dH).map d.s38dθ =
      normalClosure (d.s38dJ : Set (↥d.s38dH ⧸ d.s38dO))) : d.M₂ ≤ X := by
  obtain ⟨hP, hM', hq, hOut, -⟩ := s38d_H₂_facts hp
  have hXM : X ≤ d.M₂ := s38d_X_le_M₂ hp hXH hX
  set X' : Subgroup ↥d.s38dH := X.subgroupOf d.s38dH with hX'
  set M' : Subgroup ↥d.s38dH := d.M₂.subgroupOf d.s38dH with hM'def
  have hX'M' : X' ≤ M' := fun x hx => hXM hx
  have hN'perf : ⁅d.N₂.subgroupOf d.s38dH, d.N₂.subgroupOf d.s38dH⁆ = d.N₂.subgroupOf d.s38dH :=
    s38d_perfect_subgroupOf d.N₂_le_centralizer_I₂ (s38d_N₂_perfect hp.hyp)
  have hCent : ∀ m ∈ M', ∀ o ∈ d.s38dO, o * m = m * o := by
    haveI : (centralizer (d.s38dO : Set ↥d.s38dH)).Normal := Subgroup.normal_centralizer
    have hN' : (d.N₂.subgroupOf d.s38dH : Set ↥d.s38dH) ⊆
        (centralizer (d.s38dO : Set ↥d.s38dH) : Set ↥d.s38dH) := by
      intro n hn
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro o ho
      exact Subtype.ext (hO o ho n hn)
    have hM'C : M' ≤ centralizer (d.s38dO : Set ↥d.s38dH) := by
      rw [hM'def, s38d_M₂_subgroupOf]
      exact normalClosure_le_normal hN'
    intro m hm o ho
    exact mem_centralizer_iff.1 (hM'C hm) o ho
  have hM'perf : ⁅M', M'⁆ = M' := by
    rw [hM'def, s38d_M₂_subgroupOf]
    exact s38d_normalClosure_perfect hN'perf
  have hMC : ∀ m ∈ M', ∃ x ∈ X', x⁻¹ * m ∈ d.s38dO := by
    intro m hm
    have h1 : d.s38dθ m ∈ X'.map d.s38dθ := by
      rw [hθ, ← hM']; exact ⟨m, hm, rfl⟩
    obtain ⟨x, hx, hxm⟩ := h1
    refine ⟨x, hx, ?_⟩
    have : d.s38dθ (x⁻¹ * m) = 1 := by rw [map_mul, map_inv, hxm, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hMX : M' ≤ X' := by
    rw [← hM'perf, commutator_le]
    intro a ha b hb
    obtain ⟨x₁, hx₁, hw₁⟩ := hMC a ha
    obtain ⟨x₂, hx₂, hw₂⟩ := hMC b hb
    have ha' : a = x₁ * (x₁⁻¹ * a) := by group
    have hb' : b = x₂ * (x₂⁻¹ * b) := by group
    have hw₁M : x₁⁻¹ * a ∈ M' := mul_mem (inv_mem (hX'M' hx₁)) ha
    have hw₂M : x₂⁻¹ * b ∈ M' := mul_mem (inv_mem (hX'M' hx₂)) hb
    have h12 : (x₁⁻¹ * a) * x₂ = x₂ * (x₁⁻¹ * a) := hCent x₂ (hX'M' hx₂) _ hw₁
    have h21 : (x₂⁻¹ * b) * x₁ = x₁ * (x₂⁻¹ * b) := hCent x₁ (hX'M' hx₁) _ hw₂
    have hww : (x₁⁻¹ * a) * (x₂⁻¹ * b) = (x₂⁻¹ * b) * (x₁⁻¹ * a) := hCent _ hw₂M _ hw₁
    rw [ha', hb', s38d_commutator_mul_central h12 h21 hww]
    exact s38d_commutator_le_self X' (commutator_mem_commutator hx₁ hx₂)
  intro x hx
  exact hMX (show (⟨x, s38d_M₂_le_H d hx⟩ : ↥d.s38dH) ∈ M' from hx)

theorem s38d_X_le_N₂ (hO : ∀ o : ↥d.s38dH, o ∈ d.s38dO → ∀ n ∈ d.N₂, (o : G) * n = n * (o : G))
    {X : Subgroup G} (hXH : X ≤ d.s38dH) (hX : ⁅X, X⁆ = X)
    (hθ : (X.subgroupOf d.s38dH).map d.s38dθ = d.s38dJ) : X ≤ d.N₂ := by
  set X' : Subgroup ↥d.s38dH := X.subgroupOf d.s38dH with hX'
  set N' : Subgroup ↥d.s38dH := d.N₂.subgroupOf d.s38dH with hN'
  have hX'p : ⁅X', X'⁆ = X' := s38d_perfect_subgroupOf hXH hX
  have hOc : ∀ o ∈ d.s38dO, ∀ n ∈ N', o * n = n * o := fun o ho n hn =>
    Subtype.ext (hO o ho n hn)
  have hMC : ∀ m ∈ X', ∃ n ∈ N', n⁻¹ * m ∈ d.s38dO := by
    intro m hm
    have h1 : d.s38dθ m ∈ N'.map d.s38dθ := by
      have : d.s38dθ m ∈ X'.map d.s38dθ := ⟨m, hm, rfl⟩
      rwa [hθ] at this
    obtain ⟨n, hn, hnm⟩ := h1
    refine ⟨n, hn, ?_⟩
    have : d.s38dθ (n⁻¹ * m) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  haveI : Group.IsSolvable d.s38dO :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (GMSK.odd_card_standardComponentOddCore _)
  have hCN : d.s38dO ≤ normalizer (N' : Set ↥d.s38dH) := by
    intro o ho
    refine mem_normalizer_fintype fun c hc => ?_
    rw [hOc o ho c hc, mul_inv_cancel_right]
    exact hc
  have hMN : X' ≤ normalizer (N' : Set ↥d.s38dH) := by
    intro m hm
    obtain ⟨n, hn, hw⟩ := hMC m hm
    refine mem_normalizer_fintype fun c hc => ?_
    have hm' : m = n * (n⁻¹ * m) := by group
    have hwc := hOc _ hw c hc
    have : m * c * m⁻¹ = n * c * n⁻¹ := by
      rw [hm']
      calc n * (n⁻¹ * m) * c * (n * (n⁻¹ * m))⁻¹
          = n * ((n⁻¹ * m) * c) * (n⁻¹ * m)⁻¹ * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * m)) * (n⁻¹ * m)⁻¹ * n⁻¹ := by rw [hwc]
        _ = n * c * n⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hn hc) (inv_mem hn)
  have hres : X' ≤ N' :=
    CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProduct.perfect_le_of_forall_inv_mul_mem
      hCN hX'p hMN hMC
  intro x hx
  exact hres (show (⟨x, hXH hx⟩ : ↥d.s38dH) ∈ X' from hx)

theorem s38d_normalClosure_le (d : Data G h) :
    normalClosure (((bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) :
      Subgroup (Bar d.E ⧸ OE d)) : Set (Bar d.E ⧸ OE d)) ≤
      (bar d.E d.L₂).map (QuotientGroup.mk' (OE d)) := by
  haveI := (s38d_bar_L₂_normal d).map (QuotientGroup.mk' (OE d)) (QuotientGroup.mk'_surjective _)
  exact normalClosure_le_normal (map_mono (bar_mono d.N₂_le_L₂))

theorem s38d_bar_sup_le (d : Data G h) : bar d.E (d.E ⊔ d.N₂) ≤ bar d.E d.N₂ := by
  rintro _ ⟨y, hy, rfl⟩
  have hprod := Subgroup.coe_mul_of_right_le_normalizer_left d.E d.N₂ d.N₂_le_normalizer_E
  have hy' : (y : G) ∈ (d.E : Set G) * (d.N₂ : Set G) := by
    rw [← hprod]; exact hy
  obtain ⟨e, he, n, hn, hyen⟩ := hy'
  have hnN : n ∈ normalizer (d.E : Set G) := d.N₂_le_normalizer_E hn
  have h1 : proj d.E y = proj d.E ⟨n, hnN⟩ := by
    rw [proj_eq_proj_iff]
    have : (y : G)⁻¹ * n = n⁻¹ * e⁻¹ * n := by rw [← hyen]; group
    show (y : G)⁻¹ * n ∈ d.E
    rw [this]
    have := (mem_normalizer_iff.1 (inv_mem hnN) e⁻¹).1 (inv_mem he)
    simpa using this
  rw [h1]
  exact proj_mem_bar hn

theorem s38d_not_L₂_le (ho : d.Sec38Outcome) : ¬ d.L₂ ≤ d.E ⊔ d.N₂ := by
  intro hL
  obtain ⟨ht, hout⟩ := ho
  have hDJ : normalClosure (((bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) :
      Subgroup (Bar d.E ⧸ OE d)) : Set (Bar d.E ⧸ OE d)) ≤
      (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) :=
    (s38d_normalClosure_le d).trans
      (map_mono ((bar_mono hL).trans (s38d_bar_sup_le d)))
  rcases hout.1.2.2.2.2.2.1 with ⟨hP, -⟩ | ⟨hQ, -⟩
  · exact absurd (lt_of_lt_of_le hP.2.2.1 hDJ) (lt_irrefl _)
  · obtain ⟨D₁, D₂, -, -, -, -, h5, -, -, h8, -, -, -, -, ψ, -, -⟩ := hQ
    set J : Subgroup (Bar d.E ⧸ OE d) := (bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) with hJ
    have hDJeq : normalClosure (J : Set (Bar d.E ⧸ OE d)) = J :=
      le_antisymm hDJ subset_normalClosure
    have hcard : Nat.card ↥(normalClosure (J : Set (Bar d.E ⧸ OE d))) =
        Nat.card ↥J * Nat.card ↥J := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_prod]
    rw [hDJeq] at hcard
    have hpos : 0 < Nat.card ↥J := Nat.card_pos
    have h1 : Nat.card ↥J = 1 := by
      have : Nat.card ↥J * 1 = Nat.card ↥J * Nat.card ↥J := by rw [mul_one]; exact hcard
      exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
    have hbot : J = ⊥ := Subgroup.card_eq_one.1 h1
    have hD1 : D₁ ≤ ⊥ := by
      have : D₁ ≤ normalClosure (J : Set (Bar d.E ⧸ OE d)) := h8 ▸ le_sup_left
      rwa [hDJeq, hbot] at this
    obtain ⟨x, y, hxy⟩ := h5
    have hx : (x : Bar d.E ⧸ OE d) = 1 := Subgroup.mem_bot.1 (hD1 x.2)
    exact hxy (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, one_mul, mul_one]))

theorem s38d_L₂_eq (hp : d.ProductCaseHyp) (ho : d.Sec38Outcome) (hodd : d.Sec38Odd) :
    d.L₂ = d.E ⊔ d.M₂ := by
  have hI : ∀ x ∈ d.L₂, ∀ i ∈ d.I₂, x⁻¹ * (i * x * i⁻¹) ∈ d.E := fun x hx i hi => by
    have h1 := hodd.comm_le (commutator_mem_commutator (inv_mem hx) hi)
    have e : x⁻¹ * (i * x * i⁻¹) = ⁅x⁻¹, i⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact h1
  have hO : ∀ o : ↥d.s38dH, o ∈ d.s38dO → ∀ n ∈ d.N₂, (o : G) * n = n * (o : G) :=
    fun o ho n hn => by
      have h1 : (o : G) ∈ d.s38dO.map d.s38dH.subtype := ⟨o, ho, rfl⟩
      exact (mem_centralizer_iff.1 (hodd.oddCore_le h1) n hn).symm
  obtain ⟨X, hXYL, hN₂X, hXp, hEX⟩ := s38d_exists_X hp.gms hp.hyp hI
  have hXH : X ≤ d.s38dH := hXYL.trans inf_le_right
  have hXM : X ≤ d.M₂ := s38d_X_le_M₂ hp hXH hXp
  rcases s38d_theta_X_dichotomy hp hXH hN₂X hXp with hθ | hθ
  · have hMX := s38d_M₂_le_X hp hO hXH hXp hθ
    apply le_antisymm
    · rw [← hEX]
      exact sup_le_sup_left hXM _
    · exact sup_le d.E_le_L₂ (hMX.trans (hXYL.trans inf_le_left))
  · exfalso
    have hXN := s38d_X_le_N₂ hO hXH hXp hθ
    refine s38d_not_L₂_le ho ?_
    rw [← hEX]
    exact sup_le_sup_left hXN _

theorem sec38_layer (hp : d.ProductCaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input)
    (hnn : d.Sec38NotNormal) (ho : d.Sec38Outcome) (hodd : d.Sec38Odd) : d.Sec38Layer :=
  ⟨s38d_L₂_eq hp ho hodd, s38d_V_le hp.gms hp.hyp, s38d_odd ho⟩

end Data

namespace CaseBParts

theorem sec38Layer : Sec38LayerStatement :=
  fun _ _ _ _ _ _ _ _ hp ha hi hnn ho hodd => Data.sec38_layer hp ha hi hnn ho hodd

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
