module

public import CFSG.Walter.J1Props.Janko

public section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG Subgroup CFSG.Walter CFSG.Walter.J1 CFSG.Walter.J1Props

@[expose] def LocalA5 (C : Type) [Group C] : Prop :=
  ∀ t : C, orderOf t = 2 → ∃ F : Subgroup C, F ≤ centralizer ({t} : Set C) ∧ t ∉ F ∧
    centralizer ({t} : Set C) = zpowers t ⊔ F ∧ Nonempty (F ≃* alternatingGroup (Fin 5))

@[expose] def a5Three : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

@[expose] def a5Two : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide⟩

theorem orderOf_a5Three : orderOf a5Three = 3 := by
  apply orderOf_eq_prime
  · exact Subtype.ext (by decide)
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide

theorem orderOf_a5Two : orderOf a5Two = 2 := by
  apply orderOf_eq_prime
  · exact Subtype.ext (by decide)
  · intro h
    have := congrArg Subtype.val h
    revert this
    decide

theorem a5_not_comm : a5Three * a5Two ≠ a5Two * a5Three := by
  intro h
  have := congrArg Subtype.val h
  revert this
  decide

variable {C : Type} [Group C]

section Decomp

variable {t : C} (ht : orderOf t = 2) {F : Subgroup C} (hF : F ≤ centralizer ({t} : Set C))
include ht hF

omit hF in
theorem t_mul_t : t * t = 1 := by
  rw [← sq, ← ht, pow_orderOf_eq_one]

omit ht in
theorem zpowers_le_normalizer_of_le : zpowers t ≤ normalizer (F : Set C) := by
  rw [zpowers_le, mem_normalizer_iff]
  intro x
  have hc : x ∈ F → t * x * t⁻¹ = x := fun hx => by
    rw [(mem_centralizer_singleton_iff.mp (hF hx)).symm, mul_inv_cancel_right]
  constructor
  · intro hx
    rw [hc hx]
    exact hx
  · intro hx
    have hx' : t * x * t⁻¹ ∈ F := hx
    have hcy := mem_centralizer_singleton_iff.mp (hF hx')
    have hxx : x = t * x * t⁻¹ := by
      have h1 : t * x = t * (t * x * t⁻¹) := by
        rw [← hcy, inv_mul_cancel_right]
      exact mul_left_cancel h1
    rw [hxx]
    exact hx'

theorem mem_or_mul_mem {x : C} (hx : x ∈ zpowers t ⊔ F) : x ∈ F ∨ t * x ∈ F := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (ONOut.zpowers_le_normalizer_of_le hF), Set.mem_mul] at hx
  obtain ⟨a, ha, f, hf, rfl⟩ := hx
  rcases (mem_zpowers_of_orderOf_eq_two ht).mp ha with rfl | rfl
  · left
    rwa [one_mul]
  · right
    rwa [← mul_assoc, t_mul_t ht, one_mul]

theorem sq_eq_one_of_two_pow (e : F ≃* alternatingGroup (Fin 5)) {x : C} (hx : x ∈ zpowers t ⊔ F)
    (hxt : x * t = t * x) {n : ℕ} (hn : x ^ 2 ^ n = 1) : x ^ 2 = 1 := by
  rcases mem_or_mul_mem ht hF hx with hxF | hxF
  · exact A5Sub.sq_eq_one_of_pow e hxF hn
  · have hc : Commute t x := hxt.symm
    rcases n with _ | n
    · rw [pow_zero, pow_one] at hn
      rw [hn, one_pow]
    · have ht2 : t ^ 2 = 1 := by rw [sq, t_mul_t ht]
      have h1 : (t * x) ^ 2 ^ (n + 1) = 1 := by
        rw [hc.mul_pow, hn, mul_one, pow_succ, pow_mul', ht2, one_pow]
      have h2 := A5Sub.sq_eq_one_of_pow e hxF h1
      rwa [hc.mul_pow, ht2, one_mul] at h2

end Decomp

variable [Finite C]

theorem hasAbelianSylowTwo (hloc : LocalA5 C) : HasAbelianSylowTwo C := by
  intro S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hS : Nontrivial (S : Subgroup C)
  · have hp : IsPGroup 2 (S : Subgroup C) := S.isPGroup'
    have hZ : Nontrivial (center (S : Subgroup C)) := hp.center_nontrivial
    have h2 : 2 ∣ Nat.card (center (S : Subgroup C)) := by
      obtain ⟨k, hk⟩ := (hp.to_subgroup (center (S : Subgroup C))).exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
      rw [hk]
      exact dvd_pow_self 2 hk0
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    set t : C := ((c : (S : Subgroup C)) : C) with htdef
    have ht : orderOf t = 2 := by
      rw [htdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
    obtain ⟨F, hFC, -, hCt, ⟨e⟩⟩ := hloc t ht
    have hcomm : ∀ s ∈ (S : Subgroup C), s * t = t * s := fun s hs => by
      have := mem_center_iff.mp c.2 ⟨s, hs⟩
      exact congrArg Subtype.val this
    have hsq : ∀ s ∈ (S : Subgroup C), s ^ 2 = 1 := by
      intro s hs
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
      have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hsC : s ∈ centralizer ({t} : Set C) := mem_centralizer_singleton_iff.mpr (hcomm s hs)
      rw [hCt] at hsC
      exact sq_eq_one_of_two_pow ht hFC e hsC (hcomm s hs) hk'
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have ha := hsq a a.2
    have hb := hsq b b.2
    have hab := hsq _ ((S : Subgroup C).mul_mem a.2 b.2)
    have ha' : (a : C)⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha)
    have hb' : (b : C)⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb)
    have hab' : ((a : C) * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hab)
    change (a : C) * b = b * a
    rw [← hab', mul_inv_rev, ha', hb']
  · rw [not_nontrivial_iff_subsingleton] at hS
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩

omit [Finite C] in
theorem le_of_index_two {H : Subgroup C} (hH : H.index = 2) {F : Subgroup C}
    (e : F ≃* alternatingGroup (Fin 5)) : F ≤ H := by
  have : IsSimpleGroup F := A5Sub.isSimpleGroup e
  have := (normal_of_index_eq_two hH).subgroupOf F
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf F) with h0 | h0
  · exfalso
    set y : C := ((e.symm a5Three : F) : C) with hy
    have hy3 : orderOf y = 3 := by
      rw [hy, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a5Three]
    have hyF : y ^ 2 ∈ F := F.pow_mem (e.symm a5Three).2 2
    have hyH : (⟨y ^ 2, hyF⟩ : F) ∈ H.subgroupOf F := mem_subgroupOf.mpr (sq_mem_of_index_two hH y)
    rw [h0, mem_bot] at hyH
    have h2 : y ^ 2 = 1 := congrArg Subtype.val hyH
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy3] at this
    exact absurd this (by decide)
  · exact (subgroupOf_eq_top.mp h0)

theorem index_ne_two (hloc : LocalA5 C) {z : C} (hz : orderOf z = 2) (H : Subgroup C) :
    H.index ≠ 2 := by
  intro hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Fz, hFzC, -, hCz, ⟨ez⟩⟩ := hloc z hz
  have hFzH := le_of_index_two hH ez
  set t : C := ((ez.symm a5Two : Fz) : C) with htdef
  have ht : orderOf t = 2 := by
    rw [htdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a5Two]
  have htFz : t ∈ Fz := (ez.symm a5Two).2
  obtain ⟨Ft, hFtC, -, hCt, ⟨et⟩⟩ := hloc t ht
  have hFtH := le_of_index_two hH et
  have hzt : z ∈ centralizer ({t} : Set C) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hFzC htFz)).symm
  rw [hCt] at hzt
  have hzH : z ∈ H := by
    rcases mem_or_mul_mem ht hFtC hzt with h1 | h1
    · exact hFtH h1
    · have : z = t⁻¹ * (t * z) := by group
      rw [this]
      exact H.mul_mem (H.inv_mem (hFzH htFz)) (hFtH h1)
  have hz2 : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨S, hS⟩ := hz2.exists_le_sylow
  have hzS : z ∈ (S : Subgroup C) := hS (mem_zpowers z)
  have hab := hasAbelianSylowTwo hloc S
  have hSC : (S : Subgroup C) ≤ centralizer ({z} : Set C) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨z, hzS⟩))
  have hSH : (S : Subgroup C) ≤ H := by
    refine hSC.trans ?_
    rw [hCz]
    exact sup_le (zpowers_le.mpr hzH) hFzH
  have h1 : H.index ∣ (S : Subgroup C).index := index_dvd_of_le hSH
  rw [hH] at h1
  exact S.not_dvd_index h1

theorem nonempty_jankoHyp₀ (hloc : LocalA5 C) {z : C} (hz : orderOf z = 2) :
    Nonempty (JankoHyp₀ C) := by
  obtain ⟨F, hFC, hzF, hCz, ⟨e⟩⟩ := hloc z hz
  exact ⟨{ index_ne_two := index_ne_two hloc hz
           abelian_sylow := hasAbelianSylowTwo hloc
           t := z
           orderOf_t := hz
           F := F
           le_centralizer := hFC
           t_not_mem := hzF
           centralizer_eq := hCz
           iso := e }⟩

end CFSG.ComponentClassification.SolMax.ONOut
