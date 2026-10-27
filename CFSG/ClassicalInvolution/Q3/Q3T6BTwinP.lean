module

public import CFSG.ClassicalInvolution.Q3.Q3T6BAct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

@[expose] def ExAt (a : F) : Prop := Balance.oddCoreIn (Subgroup.centralizer ({a} : Set F)) = ⊥

theorem Mem3.oddCoreOf_eq_bot {K : Subgroup F} {z : F} (hK : Mem3 K z) (h : ExAt z) :
    oddCoreOf K = ⊥ :=
  (Uniform.oddCoreIn_eq_of_intrinsic hK.member (hK.intrinsic solvableType_three)).trans h

theorem Mem3.commute_of_twin_exact {K₁ K₂ : Subgroup F} {z : F} (h₁ : Mem3 K₁ z)
    (h₂ : Mem3 K₂ z) (hex : ExAt z) (hne : K₁ ≠ K₂) {a b : F} (ha : a ∈ K₁) (hb : b ∈ K₂) :
    a * b = b * a := by
  obtain ⟨-, -, hc⟩ := h₁.twin_facts h₂ hne
  have h1 : ⁅a, b⁆ ∈ oddCoreOf K₁ ⊓ oddCoreOf K₂ :=
    hc (Subgroup.commutator_mem_commutator ha hb)
  have h2 : ⁅a, b⁆ ∈ oddCoreOf K₁ := h1.1
  rw [Mem3.oddCoreOf_eq_bot h₁ hex, Subgroup.mem_bot] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

@[expose] def twinClass (K J : Subgroup F) : Set (Subgroup F) := {L | ∃ k ∈ K, L = conjSub k J}

@[expose] def twinProd (K J : Subgroup F) : Subgroup F := ⨆ L ∈ twinClass K J, L

theorem le_twinProd {K J L : Subgroup F} (hL : L ∈ twinClass K J) : L ≤ twinProd K J :=
  le_iSup₂_of_le L hL le_rfl

section Twins

variable {K J : Subgroup F} {t : F}

theorem mem3_of_mem_twinClass (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k) {L : Subgroup F}
    (hL : L ∈ twinClass K J) : Mem3 L t := by
  obtain ⟨k, hk, rfl⟩ := hL
  exact hJ.conj_of_commute (htK k hk)

theorem le_normalizer_of_mem_twinClass (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k)
    {L L' : Subgroup F} (hL : L ∈ twinClass K J) (hL' : L' ∈ twinClass K J) :
    L' ≤ Subgroup.normalizer (L : Set F) := by
  by_cases hne : L = L'
  · rw [← hne]
    exact Subgroup.le_normalizer
  · exact ((mem3_of_mem_twinClass hJ htK hL).twin_facts (mem3_of_mem_twinClass hJ htK hL')
      hne).1

theorem twinProd_le_normalizer (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k) {L : Subgroup F}
    (hL : L ∈ twinClass K J) : twinProd K J ≤ Subgroup.normalizer (L : Set F) :=
  iSup₂_le fun _ hL' => le_normalizer_of_mem_twinClass hJ htK hL hL'

theorem commute_of_mem_twinClass (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k) (hex : ExAt t)
    {L L' : Subgroup F} (hL : L ∈ twinClass K J) (hL' : L' ∈ twinClass K J) (hne : L ≠ L')
    {a b : F} (ha : a ∈ L) (hb : b ∈ L') : a * b = b * a :=
  Mem3.commute_of_twin_exact (mem3_of_mem_twinClass hJ htK hL) (mem3_of_mem_twinClass hJ htK hL')
    hex hne ha hb

theorem conjSub_mem_twinClass {k : F} (hk : k ∈ K) {L : Subgroup F} (hL : L ∈ twinClass K J) :
    conjSub k L ∈ twinClass K J := by
  obtain ⟨k', hk', rfl⟩ := hL
  exact ⟨k * k', K.mul_mem hk hk', (conjSub_mul k k' J).symm⟩

theorem conj_mem_twinProd {k : F} (hk : k ∈ K) {p : F} (hp : p ∈ twinProd K J) :
    k * p * k⁻¹ ∈ twinProd K J := by
  have hle : twinProd K J ≤ (twinProd K J).comap (MulAut.conj k).toMonoidHom := by
    refine iSup₂_le fun L hL => ?_
    intro l hl
    show k * l * k⁻¹ ∈ twinProd K J
    exact le_twinProd (conjSub_mem_twinClass hk hL) (conj_mem_conjSub hl)
  exact hle hp

theorem K_le_normalizer_twinProd :
    K ≤ Subgroup.normalizer ((twinProd K J : Subgroup F) : Set F) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨fun hp => conj_mem_twinProd hk hp, fun hp => ?_⟩
  have := conj_mem_twinProd (K.inv_mem hk) hp
  simpa [mul_assoc] using this

theorem isSubnormal_twinProd (hJsub : IsSubnormal J (Subgroup.centralizer ({t} : Set F)))
    (htK : ∀ k ∈ K, k * t = t * k) :
    IsSubnormal (twinProd K J) (Subgroup.centralizer ({t} : Set F)) := by
  classical
  set C : Subgroup F := Subgroup.centralizer ({t} : Set F) with hC
  have hsubL : ∀ L ∈ twinClass K J, IsSubnormal L C := by
    rintro L ⟨k, hk, rfl⟩
    have h1 := isSubnormal_map_conj_centralizer hJsub k
    have h2 : k * t * k⁻¹ = t := by rw [htK k hk]; group
    rw [h2] at h1
    exact h1
  have hLC : ∀ L ∈ twinClass K J, L ≤ C := fun L hL => isSubnormal_le (hsubL L hL)
  let 𝒮 : Set (Subgroup ↥C) := (fun L : Subgroup F => L.subgroupOf C) '' twinClass K J
  have h𝒮 : ∀ A ∈ 𝒮, A.IsSubnormal := by
    rintro _ ⟨L, hL, rfl⟩
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      (Uniform.isSubnormal_subgroupOf_top (hsubL L hL)) Subgroup.IsSubnormal.top
  have hjoin := (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 h𝒮).1
  have h3 := CFSG.ComponentClassification.Components.chain_map C.subtype
    (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hjoin)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h3
  have heq : (Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥C))).map C.subtype = twinProd K J := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨A, ⟨L, hL, rfl⟩, hxA⟩ := hx
      exact le_twinProd hL (Subgroup.mem_subgroupOf.mp hxA)
    · refine iSup₂_le fun L hL l hl => ?_
      refine ⟨⟨l, hLC L hL hl⟩, Subgroup.subset_closure ?_, rfl⟩
      simp only [Set.mem_iUnion]
      exact ⟨L.subgroupOf C, ⟨L, hL, rfl⟩, Subgroup.mem_subgroupOf.mpr hl⟩
  rw [heq] at h3
  exact h3

theorem oddCoreIn_twinProd_eq_bot (hJsub : IsSubnormal J (Subgroup.centralizer ({t} : Set F)))
    (htK : ∀ k ∈ K, k * t = t * k) (hex : ExAt t) : Balance.oddCoreIn (twinProd K J) = ⊥ :=
  le_bot_iff.mp (hex ▸ Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_twinProd hJsub htK))

end Twins

section OddFixed

variable {K J : Subgroup F} {t z : F}

theorem isPGroup_two_of_odd_eq_one (H : Subgroup F)
    (h : ∀ x ∈ H, Odd (orderOf x) → x = 1) : IsPGroup 2 H := by
  intro g
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : F)).ne'
  refine ⟨a, ?_⟩
  have hy : (g : F) ^ 2 ^ a ∈ H := H.pow_mem g.2 _
  have hord : orderOf ((g : F) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (by positivity) ⟨m, hn⟩, hn]
    simp [Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  have := h _ hy (hord ▸ hm)
  exact Subtype.ext (by simpa using this)

theorem mem_normalizer_of_mem_twinClass (hzJ : z ∈ Subgroup.normalizer (J : Set F))
    (hzK : ∀ k ∈ K, k * z = z * k) {L : Subgroup F} (hL : L ∈ twinClass K J) :
    z ∈ Subgroup.normalizer (L : Set F) := by
  obtain ⟨k, hk, rfl⟩ := hL
  apply AscHypOmega.mem_normalizer_of_conjSub_eq
  calc conjSub z (conjSub k J) = conjSub (z * k) J := (conjSub_mul z k J).symm
    _ = conjSub (k * z) J := by rw [← hzK k hk]
    _ = conjSub k (conjSub z J) := conjSub_mul k z J
    _ = conjSub k J := by rw [conjSub_eq_of_mem_normalizer hzJ]

theorem exists_noncomm_of_mem_twinClass (hzK : ∀ k ∈ K, k * z = z * k)
    (hnt : ∃ j ∈ J, z * j ≠ j * z) {L : Subgroup F} (hL : L ∈ twinClass K J) :
    ∃ l ∈ L, z * l ≠ l * z := by
  obtain ⟨k, hk, rfl⟩ := hL
  obtain ⟨j, hj, hne⟩ := hnt
  refine ⟨k * j * k⁻¹, conj_mem_conjSub hj, fun h => hne ?_⟩
  have hc : Commute z k := (hzK k hk).symm
  have hl : Commute z (k * j * k⁻¹) := h
  have hj' : Commute z (k⁻¹ * (k * j * k⁻¹) * k) := (hc.inv_right.mul_right hl).mul_right hc
  have hjj : k⁻¹ * (k * j * k⁻¹) * k = j := by group
  rw [hjj] at hj'
  exact hj'

theorem odd_eq_one_of_twinProd (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k) (hex : ExAt t)
    (hz2 : z * z = 1) (hzJ : z ∈ Subgroup.normalizer (J : Set F)) (hzK : ∀ k ∈ K, k * z = z * k)
    (hnt : ∃ j ∈ J, z * j ≠ j * z) {x : F} (hx : x ∈ twinProd K J) (hxz : x * z = z * x)
    (hodd : Odd (orderOf x)) : x = 1 := by
  have hxC : ∀ L ∈ twinClass K J, ∀ l ∈ L, x * l = l * x := by
    intro L hL l hl
    have hLm : Mem3 L t := mem3_of_mem_twinClass hJ htK hL
    have hOL : oddCoreOf L = ⊥ := Mem3.oddCoreOf_eq_bot hLm hex
    have hzL : z ∈ Subgroup.normalizer (L : Set F) := mem_normalizer_of_mem_twinClass hzJ hzK hL
    have hxN : x ∈ Subgroup.normalizer (L : Set F) := twinProd_le_normalizer hJ htK hL hx
    obtain ⟨ρ, hρ⟩ := exists_action hLm
    have hρz : ρ ⟨z, hzL⟩ ≠ 1 := by
      intro h1
      obtain ⟨l', hl', hne⟩ := exists_noncomm_of_mem_twinClass hzK hnt hL
      have h2 := (hρ ⟨z, hzL⟩).mp h1 l' hl'
      rw [hOL, Subgroup.mem_bot] at h2
      exact hne (commutatorElement_eq_one_iff_mul_comm.mp h2)
    have h3 := act_trivial_of_odd ρ hzL hz2 hρz hxN hxz hodd
    have h4 := (hρ ⟨x, hxN⟩).mp h3 l hl
    rw [hOL, Subgroup.mem_bot] at h4
    exact commutatorElement_eq_one_iff_mul_comm.mp h4
  have hPC : twinProd K J ≤ Subgroup.centralizer ({x} : Set F) := by
    refine iSup₂_le fun L hL l hl => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hxC L hL l hl).symm
  have hnorm : twinProd K J ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup F) : Set F) := by
    intro p hp
    have hpx : p * x = x * p := Subgroup.mem_centralizer_singleton_iff.mp (hPC hp)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hcomm : ∀ n : ℤ, Commute p (x ^ n) := fun n =>
      Commute.zpow_right (show Commute p x from hpx) n
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [(hcomm n).mul_inv_cancel]
      exact Subgroup.zpow_mem_zpowers x n
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : y = p⁻¹ * x ^ n * p := by rw [hn]; group
      rw [this, (hcomm n).inv_mul_cancel]
      exact Subgroup.zpow_mem_zpowers x n
  have hcard : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have hle := Balance.le_oddCoreIn_of_normalizes (Subgroup.zpowers_le.mpr hx) hnorm hcard
  have hJsub : IsSubnormal J (Subgroup.centralizer ({t} : Set F)) := hJ.subnormal
  rw [oddCoreIn_twinProd_eq_bot hJsub htK hex] at hle
  have hx1 : x ∈ (⊥ : Subgroup F) := hle (Subgroup.mem_zpowers x)
  exact Subgroup.mem_bot.mp hx1

theorem isPGroup_twinProd_centralizer (hJ : Mem3 J t) (htK : ∀ k ∈ K, k * t = t * k)
    (hex : ExAt t) (hz2 : z * z = 1) (hzJ : z ∈ Subgroup.normalizer (J : Set F))
    (hzK : ∀ k ∈ K, k * z = z * k) (hnt : ∃ j ∈ J, z * j ≠ j * z) :
    IsPGroup 2 (twinProd K J ⊓ Subgroup.centralizer ({z} : Set F) : Subgroup F) :=
  isPGroup_two_of_odd_eq_one _ fun _ hx hodd =>
    odd_eq_one_of_twinProd hJ htK hex hz2 hzJ hzK hnt hx.1
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2) hodd

end OddFixed

end CFSG.ClassicalInvolution.Q3.Q3T6B
