module

public import CFSG.GH74.GLS.C3.Layer1.BkL114Epw

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2

section Support

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem support_subset_of_numMoved {y v : Perm α} (hy2 : y * y = 1) (hv : numMoved v = 8)
    (hy : numMoved y = 4) (hyv : numMoved (y * v) = 4) : y.support ⊆ v.support := by
  have hv' : v = y * (y * v) := by rw [← mul_assoc, hy2, one_mul]
  have hsub : v.support ⊆ y.support ∪ (y * v).support := by
    conv_lhs => rw [hv']
    exact Equiv.Perm.support_mul_le y (y * v)
  have hcard : (y.support ∪ (y * v).support).card ≤ v.support.card := by
    calc (y.support ∪ (y * v).support).card ≤ y.support.card + (y * v).support.card :=
          Finset.card_union_le _ _
      _ = v.support.card := by
          rw [← numMoved_eq_card_support, ← numMoved_eq_card_support, ← numMoved_eq_card_support,
            hy, hyv, hv]
  have heq : v.support = y.support ∪ (y * v).support := Finset.eq_of_subset_of_card_le hsub hcard
  intro x hx
  rw [heq]
  exact Finset.mem_union_left _ hx

theorem exists_even_perm_fix (v : Perm α) {z w : α} (hz : v z = z) (hw : v w = w)
    (h3 : numMoved v + 3 ≤ Fintype.card α) :
    ∃ d : Perm α, sign d = 1 ∧ d w = z ∧ ∀ p, v p ≠ p → d p = p := by
  by_cases hwz : w = z
  · exact ⟨1, by simp, by simp [hwz], fun p _ => rfl⟩
  · have hcard : ({z, w} : Finset α).card < (v.supportᶜ).card := by
      have h1 : (v.supportᶜ).card = Fintype.card α - v.support.card := by
        rw [Finset.card_compl]
      have h2 : ({z, w} : Finset α).card ≤ 2 := Finset.card_le_two
      rw [h1, ← numMoved_eq_card_support]
      omega
    obtain ⟨u, hu, huzw⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have huv : v u = u := by
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hu
      exact hu
    have huz : u ≠ z := fun h => huzw (by simp [h])
    have huw : u ≠ w := fun h => huzw (by simp [h])
    refine ⟨swap w z * swap z u, ?_, ?_, ?_⟩
    · rw [map_mul, Equiv.Perm.sign_swap hwz, Equiv.Perm.sign_swap huz.symm]
      decide
    · have h1 : swap z u w = w := Equiv.swap_apply_of_ne_of_ne hwz huw.symm
      rw [Perm.mul_apply, h1, Equiv.swap_apply_left]
    · intro p hp
      have hpz : p ≠ z := fun h => hp (by rw [h]; exact hz)
      have hpw : p ≠ w := fun h => hp (by rw [h]; exact hw)
      have hpu : p ≠ u := fun h => hp (by rw [h]; exact huv)
      rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpz hpu,
        Equiv.swap_apply_of_ne_of_ne hpw hpz]

end Support

section Extension

@[expose] def extendLastPerm (n : ℕ) : Perm (Fin n) →* Perm (Fin (n + 1)) :=
  Equiv.Perm.extendDomainHom (finSuccAboveEquiv (Fin.last n))

variable {n : ℕ}

theorem extendLastPerm_last (g : Perm (Fin n)) :
    extendLastPerm n g (Fin.last n) = Fin.last n :=
  Equiv.Perm.extendDomain_apply_not_subtype g (finSuccAboveEquiv (Fin.last n)) (by simp)

theorem extendLastPerm_injective : Function.Injective (extendLastPerm n) :=
  Equiv.Perm.extendDomainHom_injective _

theorem sign_extendLastPerm (g : Perm (Fin n)) : sign (extendLastPerm n g) = sign g :=
  Equiv.Perm.sign_extendDomain g _

theorem card_support_extendLastPerm (g : Perm (Fin n)) :
    (extendLastPerm n g).support.card = g.support.card :=
  Equiv.Perm.card_support_extend_domain _

theorem exists_extendLastPerm_eq (g : Perm (Fin (n + 1))) (hg : g (Fin.last n) = Fin.last n) :
    ∃ k : Perm (Fin n), extendLastPerm n k = g := by
  let f := finSuccAboveEquiv (Fin.last n)
  have hp : ∀ x : Fin (n + 1), (g x ≠ Fin.last n) ↔ (x ≠ Fin.last n) := by
    intro x
    constructor
    · intro h hx
      exact h (hx ▸ hg)
    · intro h hgx
      apply h
      apply g.injective
      rw [hgx, hg]
  refine ⟨f.symm.permCongr (g.subtypePerm hp), ?_⟩
  refine Equiv.ext fun x => ?_
  by_cases hx : x = Fin.last n
  · subst hx
    rw [extendLastPerm_last, hg]
  · obtain ⟨a, ha⟩ := f.surjective ⟨x, hx⟩
    have hxa : x = (f a : Fin (n + 1)) := by rw [ha]
    rw [hxa]
    have h1 := Equiv.Perm.extendDomain_apply_image (f.symm.permCongr (g.subtypePerm hp)) f a
    simp only [extendLastPerm, Equiv.Perm.extendDomainHom_apply]
    rw [h1]
    simp [Equiv.permCongr_apply]

@[expose] def extendLastAlt (n : ℕ) :
    alternatingGroup (Fin n) →* alternatingGroup (Fin (n + 1)) :=
  ((extendLastPerm n).comp (alternatingGroup (Fin n)).subtype).codRestrict
    (alternatingGroup (Fin (n + 1))) fun g => by
      rw [mem_alternatingGroup]
      show sign (extendLastPerm n (g : Perm (Fin n))) = 1
      rw [sign_extendLastPerm]
      exact mem_alternatingGroup.1 g.2

theorem extendLastAlt_injective : Function.Injective (extendLastAlt n) := fun _ _ hab =>
  Subtype.ext (extendLastPerm_injective (congrArg Subtype.val hab))

theorem extendLastAlt_last (g : alternatingGroup (Fin n)) :
    ((extendLastAlt n g : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) (Fin.last n) =
      Fin.last n :=
  extendLastPerm_last _

theorem exists_extendLastAlt_eq (g : alternatingGroup (Fin (n + 1)))
    (hg : (g : Perm (Fin (n + 1))) (Fin.last n) = Fin.last n) : ∃ k, extendLastAlt n k = g := by
  obtain ⟨k, hk⟩ := exists_extendLastPerm_eq (g : Perm (Fin (n + 1))) hg
  refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
  rw [mem_alternatingGroup]
  have h1 := mem_alternatingGroup.1 g.2
  rw [← hk, sign_extendLastPerm] at h1
  exact h1

theorem numMoved_extendLastAlt (g : alternatingGroup (Fin n)) :
    numMoved ((extendLastAlt n g : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) =
      numMoved (g : Perm (Fin n)) :=
  card_support_extendLastPerm _

end Extension

section Sylow

theorem card_alternatingGroup_eleven :
    Nat.card (alternatingGroup (Fin 11)) = 11 * Nat.card (alternatingGroup (Fin 10)) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_alternatingGroup,
    card_alternatingGroup, Fintype.card_fin, Fintype.card_fin]
  decide

theorem factorization_two_card_alternatingGroup :
    (Nat.card (alternatingGroup (Fin 11))).factorization 2 =
      (Nat.card (alternatingGroup (Fin 10))).factorization 2 := by
  rw [card_alternatingGroup_eleven,
    Nat.factorization_mul (by norm_num) (Nat.card_pos (α := alternatingGroup (Fin 10))).ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 11), zero_add]

theorem isSylowOf_map_extendLastAlt {S : Subgroup (alternatingGroup (Fin 10))}
    (hS : IsSylowOf 2 S ⊤) : IsSylowOf 2 (S.map (extendLastAlt 10)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card le_top ?_
  rw [Subgroup.card_map_of_injective extendLastAlt_injective, hS.card_eq, Subgroup.card_top,
    Subgroup.card_top]
  exact congrArg (2 ^ ·) factorization_two_card_alternatingGroup.symm

end Sylow

section Descent

theorem exists_even_commuting (n : ℕ) (v y c : alternatingGroup (Fin (n + 1)))
    (hvz : (v : Perm (Fin (n + 1))) (Fin.last n) = Fin.last n) (hcv : c * v = v * c)
    (h3 : numMoved (v : Perm (Fin (n + 1))) + 3 ≤ n + 1)
    (hy : ∀ x, (y : Perm (Fin (n + 1))) x ≠ x → (v : Perm (Fin (n + 1))) x ≠ x) :
    ∃ d : alternatingGroup (Fin (n + 1)),
      (d : Perm (Fin (n + 1))) ((c : Perm (Fin (n + 1))) (Fin.last n)) = Fin.last n ∧
        d * v = v * d ∧ d * y = y * d := by
  have hvw : (v : Perm (Fin (n + 1))) ((c : Perm (Fin (n + 1))) (Fin.last n)) =
      (c : Perm (Fin (n + 1))) (Fin.last n) := by
    have h1 := congrArg (fun a : alternatingGroup (Fin (n + 1)) =>
      (a : Perm (Fin (n + 1))) (Fin.last n)) hcv
    simp only [Subgroup.coe_mul, Perm.mul_apply, hvz] at h1
    exact h1.symm
  obtain ⟨d, hds, hdw, hdp⟩ := exists_even_perm_fix (v : Perm (Fin (n + 1))) hvz hvw
    (by rw [Fintype.card_fin]; exact h3)
  refine ⟨⟨d, mem_alternatingGroup.2 hds⟩, hdw, ?_, ?_⟩
  · refine Subtype.ext (Equiv.Perm.Disjoint.commute fun x => ?_)
    by_cases hx : (v : Perm (Fin (n + 1))) x = x
    · exact Or.inr hx
    · exact Or.inl (hdp x hx)
  · refine Subtype.ext (Equiv.Perm.Disjoint.commute fun x => ?_)
    by_cases hx : (y : Perm (Fin (n + 1))) x = x
    · exact Or.inr hx
    · exact Or.inl (hdp x (hy x hx))

theorem exists_conj_of_extendLastAlt {n : ℕ} {v y₁ y₂ : alternatingGroup (Fin n)}
    {c' : alternatingGroup (Fin (n + 1))} (h3 : numMoved (v : Perm (Fin n)) + 3 ≤ n + 1)
    (hy : ∀ x, ((extendLastAlt n y₂ : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) x ≠ x →
      ((extendLastAlt n v : alternatingGroup (Fin (n + 1))) : Perm (Fin (n + 1))) x ≠ x)
    (hcv : c' * extendLastAlt n v = extendLastAlt n v * c')
    (hcy : c' * extendLastAlt n y₁ * c'⁻¹ = extendLastAlt n y₂) :
    ∃ c : alternatingGroup (Fin n), c * v = v * c ∧ c * y₁ * c⁻¹ = y₂ := by
  obtain ⟨d, hdz, hdv, hdy⟩ := exists_even_commuting n (extendLastAlt n v) (extendLastAlt n y₂) c'
    (extendLastAlt_last v) hcv (by rwa [numMoved_extendLastAlt]) hy
  obtain ⟨c, hc⟩ := exists_extendLastAlt_eq (n := n) (d * c') hdz
  refine ⟨c, extendLastAlt_injective ?_, extendLastAlt_injective ?_⟩
  · rw [map_mul, map_mul, hc, mul_assoc, hcv, ← mul_assoc, hdv, mul_assoc]
  · rw [map_mul, map_mul, map_inv, hc]
    calc d * c' * extendLastAlt n y₁ * (d * c')⁻¹
        = d * (c' * extendLastAlt n y₁ * c'⁻¹) * d⁻¹ := by group
      _ = d * extendLastAlt n y₂ * d⁻¹ := by rw [hcy]
      _ = extendLastAlt n y₂ := by rw [hdy]; group

end Descent

section Main

theorem amodel_ten_of_eleven (h : AModel 11) : AModel 10 := by
  intro S v hS hvS hvc hvord hv8
  have hSyl : IsSylowOf 2 (S.map (extendLastAlt 10)) ⊤ := isSylowOf_map_extendLastAlt hS
  have hcent : ∀ s ∈ S.map (extendLastAlt 10), s * extendLastAlt 10 v = extendLastAlt 10 v * s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    rw [← map_mul, ← map_mul, hvc t ht]
  have hord : orderOf (extendLastAlt 10 v) = 2 := by
    rw [orderOf_injective (extendLastAlt 10) extendLastAlt_injective v]
    exact hvord
  have hnum : numMoved (((extendLastAlt 10 v : alternatingGroup (Fin 11)) : Perm (Fin 11))) = 8 := by
    rw [numMoved_extendLastAlt]
    exact hv8
  obtain ⟨E', hES, hvE, hcard, hcomm, hsq, hnorm, hchar, hnum', htrans, hZ, hout⟩ :=
    h (S.map (extendLastAlt 10)) (extendLastAlt 10 v) hSyl (Subgroup.mem_map_of_mem _ hvS) hcent hord
      hnum
  have hinj : Function.Injective (extendLastAlt 10) := extendLastAlt_injective
  have hne1 : ∀ y : alternatingGroup (Fin 10), y ≠ 1 → extendLastAlt 10 y ≠ 1 := fun y hy h1 =>
    hy (hinj (by rw [h1, map_one]))
  have hnev : ∀ y : alternatingGroup (Fin 10), y ≠ v → extendLastAlt 10 y ≠ extendLastAlt 10 v :=
    fun y hy h1 => hy (hinj h1)
  have hrange : E' ≤ (extendLastAlt 10).range := fun x hx => by
    obtain ⟨s, -, hsx⟩ := Subgroup.mem_map.1 (hES hx)
    exact ⟨s, hsx⟩
  refine ⟨E'.comap (extendLastAlt 10), ?_, hvE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (Subgroup.mem_map_iff_mem hinj).1 (hES hx)
  · have h1 : Nat.card ((E'.comap (extendLastAlt 10)).map (extendLastAlt 10)) = 8 := by
      rw [Subgroup.map_comap_eq_self hrange]
      exact hcard
    rwa [Subgroup.card_map_of_injective hinj] at h1
  · intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ ha _ hb
  · intro a ha
    apply hinj
    rw [map_mul, map_one]
    exact hsq _ ha
  · intro c hc e he
    show extendLastAlt 10 (c * e * c⁻¹) ∈ E'
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (by rw [← map_mul, ← map_mul, hc]) _ he
  · intro y hy2 hy1 hyv hy4 hyv4
    show extendLastAlt 10 y ∈ E'
    refine hchar _ ?_ (hne1 y hy1) ?_ ?_ ?_
    · rw [← map_mul, hy2, map_one]
    · rw [← map_mul, ← map_mul, hyv]
    · rw [numMoved_extendLastAlt]
      exact hy4
    · rw [← map_mul, numMoved_extendLastAlt]
      exact hyv4
  · intro y hy hy1 hyv
    have h1 := hnum' (extendLastAlt 10 y) hy (hne1 y hy1) (hnev y hyv)
    rw [← map_mul, numMoved_extendLastAlt, numMoved_extendLastAlt] at h1
    exact h1
  · intro y₁ hy₁ y₂ hy₂ hy₁1 hy₁v hy₂1 hy₂v
    obtain ⟨c', hc'v, hc'y⟩ := htrans _ hy₁ _ hy₂ (hne1 y₁ hy₁1) (hnev y₁ hy₁v) (hne1 y₂ hy₂1)
      (hnev y₂ hy₂v)
    obtain ⟨h4, hv4⟩ := hnum' _ hy₂ (hne1 y₂ hy₂1) (hnev y₂ hy₂v)
    have hsq₂ : ((extendLastAlt 10 y₂ : alternatingGroup (Fin 11)) : Perm (Fin 11)) *
        ((extendLastAlt 10 y₂ : alternatingGroup (Fin 11)) : Perm (Fin 11)) = 1 :=
      congrArg Subtype.val (hsq _ hy₂)
    have hsupp := support_subset_of_numMoved hsq₂ hnum h4 hv4
    exact exists_conj_of_extendLastAlt (by omega)
      (fun x hx => Equiv.Perm.mem_support.1 (hsupp (Equiv.Perm.mem_support.2 hx))) hc'v hc'y
  · intro s hs hsc hss hs1
    apply hinj
    refine hZ _ (Subgroup.mem_map_of_mem _ hs) ?_ ?_ (hne1 s hs1)
    · intro t' ht'
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ht'
      rw [← map_mul, ← map_mul, hsc t ht]
    · rw [← map_mul, hss, map_one]
  · obtain ⟨s', hs'S, hs'sq, hs'E⟩ := hout
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hs'S
    refine ⟨s, hs, hinj ?_, hs'E⟩
    rw [map_mul, map_one]
    exact hs'sq

end Main

end CFSG.GH74.GLS.C3.Layer1.Bk
