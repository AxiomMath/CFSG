module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Basic
public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap

theorem two_ne_zero_of_odd_card {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  intro h2
  have hc : ringChar F = 2 := by
    have h : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
    have hd := (ringChar.spec F 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  have h0 := (FiniteField.even_card_iff_char_two (F := F)).mp hc
  rw [Nat.card_eq_fintype_card] at hodd
  have h1 := Nat.odd_iff.mp hodd
  omega

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure SplitInv (Q : QuadraticForm F V) (S T : Submodule F V) (a : V ≃ₗ[F] V) : Prop where
  ndS : PolarNondegOn Q S
  ndT : PolarNondegOn Q T
  orth : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0
  top : S ⊔ T = ⊤
  negS : ∀ x ∈ S, a x = -x
  fixT : ∀ x ∈ T, a x = x

namespace SplitInv

variable {S T : Submodule F V} {a : V ≃ₗ[F] V}

theorem exists_decomp (h : SplitInv Q S T a) (x : V) : ∃ s ∈ S, ∃ t ∈ T, x = s + t := by
  have hx : x ∈ S ⊔ T := by rw [h.top]; trivial
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨s, hs, t, ht, rfl⟩

theorem mem_S_iff (h : SplitInv Q S T a) (h2 : (2 : F) ≠ 0) {x : V} : x ∈ S ↔ a x = -x := by
  refine ⟨h.negS x, fun hx => ?_⟩
  obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
  rw [map_add, h.negS s hs, h.fixT t ht, neg_add] at hx
  have h1 : t = -t := add_left_cancel hx
  have h3 : t + t = 0 := by
    nth_rewrite 1 [h1]
    exact neg_add_cancel t
  have h4 : (2 : F) • t = 0 := by rw [two_smul]; exact h3
  rw [(smul_eq_zero.mp h4).resolve_left h2, add_zero]
  exact hs

theorem mem_T_iff (h : SplitInv Q S T a) (h2 : (2 : F) ≠ 0) {x : V} : x ∈ T ↔ a x = x := by
  refine ⟨h.fixT x, fun hx => ?_⟩
  obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
  rw [map_add, h.negS s hs, h.fixT t ht] at hx
  have h1 : -s = s := add_right_cancel hx
  have h3 : s + s = 0 := by
    nth_rewrite 1 [← h1]
    exact neg_add_cancel s
  have h4 : (2 : F) • s = 0 := by rw [two_smul]; exact h3
  rw [(smul_eq_zero.mp h4).resolve_left h2, zero_add]
  exact ht

theorem aa (h : SplitInv Q S T a) (x : V) : a (a x) = x := by
  obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
  rw [map_add, h.negS s hs, h.fixT t ht, map_add, map_neg, h.negS s hs, h.fixT t ht, neg_neg]

theorem mem_T_iff_perp (h : SplitInv Q S T a) {x : V} :
    x ∈ T ↔ ∀ y ∈ S, polar Q x y = 0 := by
  constructor
  · intro hx y hy
    rw [polar_comm]
    exact h.orth y hy x hx
  · intro hx
    obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
    have hs0 : s = 0 := by
      refine h.ndS s hs fun y hy => ?_
      have h1 := hx y hy
      rw [polar_add_left, polar_comm Q t y, h.orth y hy t ht, add_zero] at h1
      exact h1
    rw [hs0, zero_add]
    exact ht

theorem mem_S_iff_perp (h : SplitInv Q S T a) {x : V} :
    x ∈ S ↔ ∀ y ∈ T, polar Q x y = 0 := by
  constructor
  · intro hx y hy
    exact h.orth x hx y hy
  · intro hx
    obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
    have ht0 : t = 0 := by
      refine h.ndT t ht fun y hy => ?_
      have h1 := hx y hy
      rw [polar_add_left, h.orth s hs y hy, zero_add] at h1
      exact h1
    rw [ht0, add_zero]
    exact hs

theorem preserves_of_comm (h : SplitInv Q S T a) (h2 : (2 : F) ≠ 0) {g : V ≃ₗ[F] V}
    (hg : ∀ x, g (a x) = a (g x)) :
    (∀ x, x ∈ S ↔ g x ∈ S) ∧ ∀ x, x ∈ T ↔ g x ∈ T := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [h.mem_S_iff h2, h.mem_S_iff h2, ← hg x, ← map_neg]
    exact g.injective.eq_iff.symm
  · rw [h.mem_T_iff h2, h.mem_T_iff h2, ← hg x]
    exact g.injective.eq_iff.symm

theorem swaps_of_anticomm (h : SplitInv Q S T a) (h2 : (2 : F) ≠ 0) {g : V ≃ₗ[F] V}
    (hg : ∀ x, g (a x) = -a (g x)) :
    (∀ x, x ∈ S ↔ g x ∈ T) ∧ ∀ x, x ∈ T ↔ g x ∈ S := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [h.mem_S_iff h2, h.mem_T_iff h2]
    constructor
    · intro hx
      have e := hg x
      rw [hx, map_neg] at e
      exact (neg_inj.mp e).symm
    · intro hx
      have e := hg x
      rw [hx, ← map_neg] at e
      exact g.injective e
  · rw [h.mem_T_iff h2, h.mem_S_iff h2]
    constructor
    · intro hx
      have e := hg x
      rw [hx] at e
      exact neg_eq_iff_eq_neg.mp e.symm
    · intro hx
      have e := hg x
      rw [hx, neg_neg] at e
      exact g.injective e

theorem sign_of_rel (h : SplitInv Q S T a) [Nontrivial V] {g : V ≃ₗ[F] V} {c : F}
    (hg : ∀ x, g (a x) = c • a (g x)) : c = 1 ∨ c = -1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h3 : a (g (a x)) = c • g x := by rw [hg x, map_smul, h.aa]
  have h1 : g x = c • a (g (a x)) := by
    have := hg (a x)
    rw [h.aa x] at this
    exact this
  have h4 : ((c * c) - 1) • g x = 0 := by
    rw [sub_smul, mul_smul, one_smul, ← h3, ← h1, sub_self]
  have hgx : g x ≠ 0 := fun h0 => hx (g.injective (by rw [h0, map_zero]))
  have h5 : c * c - 1 = 0 := (smul_eq_zero.mp h4).resolve_right hgx
  exact mul_self_eq_one_iff.mp (sub_eq_zero.mp h5)

end SplitInv

theorem conj_mem_elemOn_of_le {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {S S' : Submodule F V} (hgS : ∀ x ∈ S, g x ∈ S') {h : V ≃ₗ[F] V} (hh : h ∈ elemOn Q S) :
    g * h * g⁻¹ ∈ elemOn Q S' := by
  have hle : elemOn Q S ≤ (elemOn Q S').comap (MulAut.conj g).toMonoidHom := by
    rw [elemOn, Subgroup.closure_le]
    rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      eichler_conj hg]
    exact eichler_mem_elemOn (hgS u hu) (hgS w hw)
  exact hle hh

namespace SplitInv

variable {S T : Submodule F V} {a : V ≃ₗ[F] V}

theorem conj_mem_join (h : SplitInv Q S T a) (h2 : (2 : F) ≠ 0) [Nontrivial V]
    {g : V ≃ₗ[F] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {c : F}
    (hgc : ∀ x, g (a x) = c • a (g x)) {y : V ≃ₗ[F] V} (hy : y ∈ elemOn Q S ⊔ elemOn Q T) :
    g * y * g⁻¹ ∈ elemOn Q S ⊔ elemOn Q T := by
  have hle : elemOn Q S ⊔ elemOn Q T ≤
      (elemOn Q S ⊔ elemOn Q T).comap (MulAut.conj g).toMonoidHom := by
    rcases h.sign_of_rel hgc with rfl | rfl
    · have hc : ∀ x, g (a x) = a (g x) := fun x => by rw [hgc x, one_smul]
      obtain ⟨hS, hT⟩ := h.preserves_of_comm h2 hc
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (conj_mem_elemOn_of_le hg (fun x hx => (hS x).mp hx) hy)
      · exact Subgroup.mem_sup_right (conj_mem_elemOn_of_le hg (fun x hx => (hT x).mp hx) hy)
    · have hc : ∀ x, g (a x) = -a (g x) := fun x => by rw [hgc x, neg_one_smul]
      obtain ⟨hS, hT⟩ := h.swaps_of_anticomm h2 hc
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_right (conj_mem_elemOn_of_le hg (fun x hx => (hS x).mp hx) hy)
      · exact Subgroup.mem_sup_left (conj_mem_elemOn_of_le hg (fun x hx => (hT x).mp hx) hy)
  have := hle hy
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem commute_of_mem_elemOn_right (h : SplitInv Q S T a) {y : V ≃ₗ[F] V}
    (hy : y ∈ elemOn Q T) : a * y = y * a := by
  obtain ⟨hyT, hyfix⟩ := support_of_mem_elemOn hy
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
  have hys : y s = s := hyfix s fun x hx => h.orth s hs x hx
  have hyt : y t ∈ T := (hyT t).mp ht
  simp only [LinearEquiv.mul_apply, map_add, map_neg, hys, h.negS s hs, h.fixT t ht,
    h.fixT _ hyt]

theorem commute_of_mem_elemOn_left (h : SplitInv Q S T a) {y : V ≃ₗ[F] V}
    (hy : y ∈ elemOn Q S) : a * y = y * a := by
  obtain ⟨hyS, hyfix⟩ := support_of_mem_elemOn hy
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := h.exists_decomp x
  have hyt : y t = t := hyfix t fun x hx => by
    rw [polar_comm]
    exact h.orth x hx t ht
  have hys : y s ∈ S := (hyS s).mp hs
  simp only [LinearEquiv.mul_apply, map_add, map_neg, hyt, h.negS s hs, h.fixT t ht,
    h.negS _ hys]

end SplitInv

theorem commute_elemOn_elemOn {S T : Submodule F V}
    (horth : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0) {g h : V ≃ₗ[F] V} (hg : g ∈ elemOn Q S)
    (hh : h ∈ elemOn Q T) : g * h = h * g := by
  have hgen : ∀ u w, u ∈ S → w ∈ S → Q u = 0 → polar Q u w = 0 →
      elemOn Q T ≤ Subgroup.centralizer ({eichler Q u w} : Set (V ≃ₗ[F] V)) := by
    intro u w hu hw hQu huw
    have hE : eichler Q u w ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      elementaryGroup_le_orthogonalGroup Q (eichler_mem_elementaryGroup Q u w)
    rw [elemOn, Subgroup.closure_le]
    rintro _ ⟨u', w', hu', hw', -, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 := eichler_conj hE u' w'
    have hu'' : eichler Q u w u' = u' :=
      eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact horth u hu u' hu')
        (by rw [polar_comm]; exact horth w hw u' hu')
    have hw'' : eichler Q u w w' = w' :=
      eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact horth u hu w' hw')
        (by rw [polar_comm]; exact horth w hw w' hw')
    rw [hu'', hw''] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  have hcg : ∀ g' ∈ elemOn Q S, h ∈ elemOn Q T → g' * h = h * g' := by
    intro g' hg' hh'
    have hle : elemOn Q S ≤ Subgroup.centralizer ({h} : Set (V ≃ₗ[F] V)) := by
      rw [elemOn, Subgroup.closure_le]
      rintro _ ⟨u, w, hu, hw, hQu, huw, rfl⟩
      have := hgen u w hu hw hQu huw hh'
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have := (Subgroup.mem_centralizer_iff.mp (hgen u w hu hw hQu huw hh')) (eichler Q u w)
        rfl
      exact this.symm
    have := (Subgroup.mem_centralizer_iff.mp (hle hg')) h rfl
    exact this.symm
  exact hcg g hg hh

section Schur

variable [Finite F] [FiniteDimensional F V]

theorem exists_smul_of_commute_elemOn (hodd : Odd (Nat.card F)) {S : Submodule F V}
    (hS : PolarNondegOn Q S) (h3 : 3 ≤ Module.finrank F S) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgS : ∀ x, x ∈ S ↔ g x ∈ S)
    (hcomm : ∀ h ∈ elemOn Q S, g * h = h * g) : ∃ c : F, ∀ x ∈ S, g x = c • x := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hQ' : (polarBilin (Q.restrict S)).Nondegenerate := nondegenerate_polarBilin_restrict hS
  have hA : HasAnisoPerp (Q.restrict S) := hasAnisoPerp_of_three_le_finrank hQ' h3
  obtain ⟨P, he, hf⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hS h3
  let ν : S ≃ₗ[F] S := resAux g hgS
  have hν : ν ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict S) := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    exact map_of_mem hg (x : V)
  have hcomm' : ∀ u w, (Q.restrict S) u = 0 → polar (Q.restrict S) u w = 0 →
      ν * eichler (Q.restrict S) u w = eichler (Q.restrict S) u w * ν := by
    intro u w hu hw
    have hE : eichler Q (u : V) (w : V) ∈ elemOn Q S := eichler_mem_elemOn u.2 w.2
    have hc := hcomm _ hE
    have hEs := (support_of_mem_elemOn hE).1
    have e1 : resAux (eichler Q (u : V) (w : V)) hEs = eichler (Q.restrict S) u w :=
      resAux_eichler u.2 w.2
    have hgE : ∀ x, x ∈ S ↔ (g * eichler Q (u : V) (w : V)) x ∈ S := fun x =>
      (hEs x).trans (hgS _)
    have hEg : ∀ x, x ∈ S ↔ (eichler Q (u : V) (w : V) * g) x ∈ S := fun x =>
      (hgS x).trans (hEs _)
    have key : resAux (g * eichler Q (u : V) (w : V)) hgE =
        resAux (eichler Q (u : V) (w : V) * g) hEg :=
      LinearEquiv.ext fun r => Subtype.ext (by
        simp only [coe_resAux]
        exact LinearEquiv.congr_fun hc (r : V))
    have m1 : resAux (g * eichler Q (u : V) (w : V)) hgE =
        resAux g hgS * resAux (eichler Q (u : V) (w : V)) hEs :=
      LinearEquiv.ext fun r => Subtype.ext rfl
    have m2 : resAux (eichler Q (u : V) (w : V) * g) hEg =
        resAux (eichler Q (u : V) (w : V)) hEs * resAux g hgS :=
      LinearEquiv.ext fun r => Subtype.ext rfl
    rw [← e1]
    exact m1.symm.trans (key.trans m2)
  obtain ⟨c, hc⟩ := mem_scalars.mp (mem_scalars_of_commute_eichler h2 hQ' hA
    (P.restrict he hf) hν hcomm')
  exact ⟨c, fun x hx => congrArg Subtype.val (hc ⟨x, hx⟩)⟩

end Schur

end CFSG.ClassicalInvolution.ModelFacts.Orth15
