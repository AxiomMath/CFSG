module

public import CFSG.GH74.Generic.S45.LAltCore
public import CFSG.GH74.Uniqueness.SU.KI1r4LyPairData

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.LyPerm

open Equiv Equiv.Perm Subgroup CFSG.GH74.Generic.S45.LAlt
open scoped commutatorElement

@[expose] def fixAlt (S : Finset (Fin 11)) : Subgroup (Perm (Fin 11)) :=
  (alternatingGroup {x : Fin 11 // x ∉ S}).map
    (Equiv.Perm.ofSubtype : Perm {x : Fin 11 // x ∉ S} →* Perm (Fin 11))

theorem fixAlt_fixes {S : Finset (Fin 11)} {f : Perm (Fin 11)} (hf : f ∈ fixAlt S) {x : Fin 11}
    (hx : x ∈ S) : f x = x := by
  obtain ⟨h, -, rfl⟩ := hf
  exact Equiv.Perm.ofSubtype_apply_of_not_mem h (by simpa using hx)

theorem fixAlt_le_alt (S : Finset (Fin 11)) : fixAlt S ≤ alternatingGroup (Fin 11) := by
  rintro _ ⟨h, hh, rfl⟩
  rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
  exact Perm.mem_alternatingGroup.1 hh

theorem fixAlt_perfect {S : Finset (Fin 11)} (hS : S.card = 4) : ⁅fixAlt S, fixAlt S⁆ = fixAlt S := by
  have h7 : 5 ≤ Nat.card {x : Fin 11 // x ∉ S} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hS]
    norm_num
  rw [fixAlt, ← Subgroup.map_commutator, commutator_alternatingGroup_eq_self h7]

theorem swap_mul_swap_mem_fixAlt {S : Finset (Fin 11)} {a b c d : Fin 11} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : a ∉ S) (hb : b ∉ S) (hc : c ∉ S) (hd : d ∉ S) : swap a b * swap c d ∈ fixAlt S := by
  have hab' : (⟨a, ha⟩ : {x : Fin 11 // x ∉ S}) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
  have hcd' : (⟨c, hc⟩ : {x : Fin 11 // x ∉ S}) ≠ ⟨d, hd⟩ := fun h => hcd (congrArg Subtype.val h)
  refine ⟨swap ⟨a, ha⟩ ⟨b, hb⟩ * swap ⟨c, hc⟩ ⟨d, hd⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab', Perm.sign_swap hcd']
    norm_num
  · rw [map_mul, Equiv.Perm.ofSubtype_swap_eq, Equiv.Perm.ofSubtype_swap_eq]

theorem fixAlt_commute {S : Finset (Fin 11)} {f : Perm (Fin 11)} (hf : f ∈ fixAlt S) {a b c d : Fin 11}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) :
    f * (swap a b * swap c d) * f⁻¹ = swap a b * swap c d := by
  have h1 := swap_apply_apply f a b
  have h2 := swap_apply_apply f c d
  rw [fixAlt_fixes hf ha, fixAlt_fixes hf hb] at h1
  rw [fixAlt_fixes hf hc, fixAlt_fixes hf hd] at h2
  calc f * (swap a b * swap c d) * f⁻¹ = (f * swap a b * f⁻¹) * (f * swap c d * f⁻¹) := by group
    _ = swap a b * swap c d := by rw [← h1, ← h2]

theorem eq_of_ne_one_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![1, a, b] : Fin 3 → G) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

variable {K : Type} [Group K]

theorem exists_fixed_involution_lift [Finite K] [Group.IsPerfect K]
    (π : K →* alternatingGroup (Fin 11)) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) (hK2 : IsPGroup 2 π.ker) (hne : π.ker ≠ ⊥)
    (y : MulAut K) (σ : Perm (Fin 11)) (hσ : σ * σ = 1)
    (hy : ∀ k : K, ((π (y k) : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
      σ * (π k : Perm (Fin 11)) * σ⁻¹) :
    ∃ u : K, π u ≠ 1 ∧ u * u = 1 ∧ y u = u := by
  classical
  obtain ⟨p, q, r, s, p', q', r', s', g, hnd, h1, h2, hg, hgσ, hconj⟩ := exists_pair_data σ hσ
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨hpq, hpr, hps, hpp', hpq', hpr', hps'⟩, ⟨hqr, hqs, hqp', hqq', hqr', hqs'⟩,
    ⟨hrs, hrp', hrq', hrr', hrs'⟩, ⟨hsp', hsq', hsr', hss'⟩, ⟨hp'q', hp'r', hp's'⟩, ⟨hq'r', hq's'⟩,
    hr's', -, -⟩ := hnd
  have hcard : Nat.card π.ker ≤ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      (by norm_num) π hπ hker hK2
  have hcent : ∀ w ∈ π.ker, ∀ x : K, x * w = w * x := fun w hw x =>
    Subgroup.mem_center_iff.1 (hker hw) x
  have hsq : ∀ w ∈ π.ker, w * w = 1 := fun w hw => by
    have := sq_eq_one_of_card_le_two hcard (⟨w, hw⟩ : π.ker)
    have h2 := congrArg Subtype.val this
    simpa [sq] using h2
  have huniq : ∀ w₁ ∈ π.ker, ∀ w₂ ∈ π.ker, w₁ ≠ 1 → w₂ ≠ 1 → w₁ = w₂ := fun w₁ h₁ w₂ h₂ n₁ n₂ =>
    congrArg Subtype.val (eq_of_ne_one_of_card_le_two hcard (a := (⟨w₁, h₁⟩ : π.ker))
      (b := ⟨w₂, h₂⟩) (fun h => n₁ (congrArg Subtype.val h)) (fun h => n₂ (congrArg Subtype.val h)))
  have hykerfix : ∀ w ∈ π.ker, y w = w := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, map_one]
    · have hyw : y w ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have h0 : ((π w : alternatingGroup (Fin 11)) : Perm (Fin 11)) = 1 := by
          rw [MonoidHom.mem_ker.1 hw]
          rfl
        rw [hy, h0]
        simp
      exact huniq _ hyw w hw (fun h => hw1 (y.injective (h.trans (map_one y).symm))) hw1
  have hsw_even : ∀ a b c d : Fin 11, a ≠ b → c ≠ d →
      swap a b * swap c d ∈ alternatingGroup (Fin 11) := fun a b c d hab hcd => by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    norm_num
  let a₁ : alternatingGroup (Fin 11) := ⟨swap p q * swap r s, hsw_even _ _ _ _ hpq hrs⟩
  let a₂ : alternatingGroup (Fin 11) := ⟨swap p' q' * swap r' s', hsw_even _ _ _ _ hp'q' hr's'⟩
  let gA : alternatingGroup (Fin 11) := ⟨g, hg⟩
  obtain ⟨k₁, hk₁⟩ := hπ a₁
  obtain ⟨kg, hkg⟩ := hπ gA
  set S : Finset (Fin 11) := {p, q, r, s} with hSdef
  have hS : S.card = 4 := by
    rw [hSdef, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hrs
    · simp [hqr, hqs]
    · simp [hpq, hpr, hps]
  let X : Subgroup (alternatingGroup (Fin 11)) := (fixAlt S).subgroupOf (alternatingGroup (Fin 11))
  have hXmap : X.map (alternatingGroup (Fin 11)).subtype = fixAlt S :=
    Subgroup.map_subgroupOf_eq_of_le (fixAlt_le_alt S)
  have hXperf : ⁅X, X⁆ = X := by
    apply Subgroup.map_injective (alternatingGroup (Fin 11)).subtype_injective
    rw [Subgroup.map_commutator, hXmap, fixAlt_perfect hS]
  have hXr : X ≤ π.range := by
    rw [MonoidHom.range_eq_top.2 hπ]
    exact le_top
  have hpS : p ∈ S := by simp [hSdef]
  have hqS : q ∈ S := by simp [hSdef]
  have hrS : r ∈ S := by simp [hSdef]
  have hsS : s ∈ S := by simp [hSdef]
  have hy' : ∀ k : K, π k ∈ X → π ((MulAut.conj k₁) k) = π k := by
    intro k hk
    have hf : ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) ∈ fixAlt S := hk
    have hc := fixAlt_commute hf hpS hqS hrS hsS
    apply Subtype.ext
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hk₁]
    show (swap p q * swap r s) * ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) *
      (swap p q * swap r s)⁻¹ = ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11))
    have hc' : ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) * (swap p q * swap r s) =
        (swap p q * swap r s) * ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by
      calc ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) * (swap p q * swap r s) =
          (((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) * (swap p q * swap r s) *
            ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11))⁻¹) *
              ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by group
        _ = (swap p q * swap r s) * ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by rw [hc]
    calc (swap p q * swap r s) * ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) *
        (swap p q * swap r s)⁻¹ = ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) *
          (swap p q * swap r s) * (swap p q * swap r s)⁻¹ := by rw [hc']
      _ = ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by group
  obtain ⟨D, -, hDsurj, hDfix⟩ := exists_fixed_perfect_lift (MulAut.conj k₁) π hker X hXr hXperf hy'
  have ha₂X : a₂ ∈ X := by
    show swap p' q' * swap r' s' ∈ fixAlt S
    refine swap_mul_swap_mem_fixAlt hp'q' hr's' ?_ ?_ ?_ ?_ <;> simp [eq_comm, *]
  obtain ⟨k₂, hk₂D, hk₂⟩ := hDsurj a₂ ha₂X
  have hcomm12 : k₂ * k₁ = k₁ * k₂ := by
    have h := hDfix k₂ hk₂D
    rw [MulAut.conj_apply] at h
    calc k₂ * k₁ = k₁ * k₂ * k₁⁻¹ * k₁ := by rw [h]
      _ = k₁ * k₂ := by group
  have hnd4 : [p, q, r, s].Nodup := by simp [hpq, hpr, hps, hqr, hqs, hrs]
  have hnd4' : [p', q', r', s'].Nodup := by simp [hp'q', hp'r', hp's', hq'r', hq's', hr's']
  have hsw1 : (swap p q * swap r s) * (swap p q * swap r s) = 1 := by
    have hc := (Equiv.Perm.disjoint_swap_swap hnd4).commute
    rw [← pow_two, hc.mul_pow, pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  have hsw2 : (swap p' q' * swap r' s') * (swap p' q' * swap r' s') = 1 := by
    have hc := (Equiv.Perm.disjoint_swap_swap hnd4').commute
    rw [← pow_two, hc.mul_pow, pow_two, pow_two, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  have hk₁sq : k₁ ^ 2 ≠ 1 :=
    sq_ne_one_of_lift_swap_mul_swap (by norm_num) π hπ hker hK2 hne hpq hpr hps hqr hqs hrs
      (by rw [hk₁])
  have hk₂sq : k₂ ^ 2 ≠ 1 :=
    sq_ne_one_of_lift_swap_mul_swap (by norm_num) π hπ hker hK2 hne hp'q' hp'r' hp's' hq'r' hq's'
      hr's' (by rw [hk₂])
  have hk₁ker : k₁ ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk₁]
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, hsw1]
    rfl
  have hk₂ker : k₂ ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk₂]
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_two, hsw2]
    rfl
  have hk12 : k₁ ^ 2 = k₂ ^ 2 := huniq _ hk₁ker _ hk₂ker hk₁sq hk₂sq
  have hu2 : (k₁ * k₂) * (k₁ * k₂) = 1 := by
    calc (k₁ * k₂) * (k₁ * k₂) = k₁ * (k₂ * k₁) * k₂ := by group
      _ = k₁ * (k₁ * k₂) * k₂ := by rw [hcomm12]
      _ = k₁ ^ 2 * k₂ ^ 2 := by simp only [pow_two, mul_assoc]
      _ = k₁ ^ 2 * k₁ ^ 2 := by rw [hk12]
      _ = 1 := hsq _ hk₁ker
  have hπu : π (k₁ * k₂) ≠ 1 := by
    intro h
    rw [map_mul, hk₁, hk₂] at h
    have h' := congrArg (fun z : alternatingGroup (Fin 11) => (z : Perm (Fin 11)) p) h
    have hfix : (swap p' q' * swap r' s') p = p := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpr' hps', swap_apply_of_ne_of_ne hpp' hpq']
    have h'' : (swap p q * swap r s) ((swap p' q' * swap r' s') p) = p := h'
    rw [hfix, Perm.mul_apply, swap_apply_of_ne_of_ne hpr hps, swap_apply_left] at h''
    exact hpq h''.symm
  let H : Subgroup K :=
    { carrier := {k | Commute ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ}
      mul_mem' := fun {a b} ha hb => by
        show Commute ((π (a * b) : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ
        rw [map_mul]
        exact Commute.mul_left ha hb
      one_mem' := by
        show Commute ((π 1 : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ
        rw [map_one]
        exact Commute.one_left σ
      inv_mem' := fun {a} ha => by
        show Commute ((π a⁻¹ : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ
        rw [map_inv]
        exact Commute.inv_left ha }
  have hε : ∀ k : K, Commute ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ →
      k⁻¹ * y k ∈ π.ker := by
    intro k hc
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy, Subgroup.coe_one]
    have : σ * ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) * σ⁻¹ =
        ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by
      calc σ * ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) * σ⁻¹ =
          (((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) * σ) * σ⁻¹ := by rw [hc.eq]
        _ = ((π k : alternatingGroup (Fin 11)) : Perm (Fin 11)) := by group
    rw [this, inv_mul_cancel]
  let ε : ↥H →* ↥π.ker :=
    { toFun := fun k => ⟨(k : K)⁻¹ * y k, hε k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ((a : K) * b)⁻¹ * y ((a : K) * b) = ((a : K)⁻¹ * y a) * ((b : K)⁻¹ * y b)
        have hcomm := hcent _ (hε a a.2) (b : K)⁻¹
        calc ((a : K) * b)⁻¹ * y ((a : K) * b) = (b : K)⁻¹ * ((a : K)⁻¹ * y a) * y b := by
              rw [map_mul]; group
          _ = ((a : K)⁻¹ * y a) * (b : K)⁻¹ * y b := by rw [hcomm]
          _ = ((a : K)⁻¹ * y a) * ((b : K)⁻¹ * y b) := mul_assoc _ _ _) }
  have hεval : ∀ k : ↥H, ((ε k : π.ker) : K) = (k : K)⁻¹ * y k := fun k => rfl
  have hkercomm : ∀ a b : π.ker, a * b = b * a := fun a b =>
    Subtype.ext (hcent _ a.2 b).symm
  have hk₁H : k₁ ∈ H := by
    show Commute ((π k₁ : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ
    rw [hk₁]
    exact h1
  have hkgH : kg ∈ H := by
    show Commute ((π kg : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ
    rw [hkg]
    exact hgσ
  have hk₂H : k₂ ∈ H := by
    show Commute ((π k₂ : alternatingGroup (Fin 11)) : Perm (Fin 11)) σ
    rw [hk₂]
    exact h2
  have hε2 : ε ⟨k₂, hk₂H⟩ = ε ⟨k₁, hk₁H⟩ := by
    have hk₂'H : kg * k₁ * kg⁻¹ ∈ H := H.mul_mem (H.mul_mem hkgH hk₁H) (H.inv_mem hkgH)
    have hπk₂' : π (kg * k₁ * kg⁻¹) = a₂ := by
      rw [map_mul, map_mul, map_inv, hk₁, hkg]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hconj.symm
    have hw : (kg * k₁ * kg⁻¹)⁻¹ * k₂ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπk₂', hk₂, inv_mul_cancel]
    have hwH : (kg * k₁ * kg⁻¹)⁻¹ * k₂ ∈ H := by
      refine H.mul_mem (H.inv_mem hk₂'H) hk₂H
    have hk₂eq : (⟨k₂, hk₂H⟩ : ↥H) =
        ⟨kg * k₁ * kg⁻¹, hk₂'H⟩ * ⟨(kg * k₁ * kg⁻¹)⁻¹ * k₂, hwH⟩ := by
      apply Subtype.ext
      show k₂ = (kg * k₁ * kg⁻¹) * ((kg * k₁ * kg⁻¹)⁻¹ * k₂)
      group
    have hεw : ε ⟨(kg * k₁ * kg⁻¹)⁻¹ * k₂, hwH⟩ = 1 := by
      apply Subtype.ext
      rw [hεval]
      show ((kg * k₁ * kg⁻¹)⁻¹ * k₂)⁻¹ * y ((kg * k₁ * kg⁻¹)⁻¹ * k₂) = 1
      rw [hykerfix _ hw, inv_mul_cancel]
    have hεconj : ε ⟨kg * k₁ * kg⁻¹, hk₂'H⟩ = ε ⟨k₁, hk₁H⟩ := by
      have : (⟨kg * k₁ * kg⁻¹, hk₂'H⟩ : ↥H) = ⟨kg, hkgH⟩ * ⟨k₁, hk₁H⟩ * ⟨kg, hkgH⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hkercomm (ε ⟨kg, hkgH⟩) (ε ⟨k₁, hk₁H⟩), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [hk₂eq, map_mul, hεw, mul_one, hεconj]
  refine ⟨k₁ * k₂, hπu, hu2, ?_⟩
  have hεu : ε (⟨k₁, hk₁H⟩ * ⟨k₂, hk₂H⟩) = 1 := by
    rw [map_mul, hε2]
    apply Subtype.ext
    have h := hsq _ (ε ⟨k₁, hk₁H⟩).2
    exact h
  have hεu' := congrArg Subtype.val hεu
  rw [hεval] at hεu'
  have h3 : (k₁ * k₂)⁻¹ * y (k₁ * k₂) = 1 := hεu'
  exact (inv_mul_eq_one.1 h3).symm

end CFSG.GH74.Uniqueness.SU.K.R4.LyPerm
