module

public import CFSG.CGT.PushingUpLit.CGT6.EmbNatBase
public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin

variable {V : Type} [CommGroup V] {k : ℕ} {K : Subgroup (MulAut V)}

private theorem nrec_card_coreMod (hk : 1 ≤ k) : Nat.card (G6.coreMod k) = 2 ^ (k - 1) := by
  let s : G6.PermMod k →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)
      map_one' := by simp
      map_mul' := fun x y => by simp [Finset.sum_add_distrib] }
  have hker : s.ker = G6.coreMod k := by
    ext x
    rw [MonoidHom.mem_ker, G6.mem_coreMod]
    exact ofAdd_eq_one
  have hsurj : Function.Surjective s := by
    intro z
    refine ⟨Multiplicative.ofAdd (Pi.single ⟨0, hk⟩ (Multiplicative.toAdd z)), ?_⟩
    show Multiplicative.ofAdd (∑ i, Pi.single (⟨0, hk⟩ : Fin k) (Multiplicative.toAdd z) i) = z
    rw [Finset.sum_pi_single']
    simp
  have h1 : Nat.card s.ker * s.ker.index = Nat.card (G6.PermMod k) := Subgroup.card_mul_index _
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker] at h1
  have h2 : Nat.card (G6.PermMod k) = 2 ^ k := by
    rw [Nat.card_congr (Multiplicative.toAdd : G6.PermMod k ≃ (Fin k → ZMod 2)), Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
  rw [h2, h3] at h1
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ] at h1
  simpa using Nat.eq_of_mul_eq_mul_right (by norm_num) h1

private theorem nrec_exists_alt (hk3 : 3 ≤ k) (i j : Fin k) :
    ∃ σ : alternatingGroup (Fin k), (σ : Equiv.Perm (Fin k)) i = j := by
  have : MulAction.IsPretransitive (alternatingGroup (Fin k)) (Fin k) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin k) (by simpa using hk3)
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin k)) i j
  exact ⟨σ, hσ⟩

private theorem nrec_coboundary (hk : Odd k) (hk3 : 3 ≤ k)
    (c : alternatingGroup (Fin k) → G6.PermMod k)
    (hc : ∀ a b : alternatingGroup (Fin k),
      c (a * b) = c a * G6.permAct k (a : Equiv.Perm (Fin k)) (c b)) :
    ∃ e ∈ G6.coreMod k, ∀ a : alternatingGroup (Fin k),
      c a = G6.permAct k (a : Equiv.Perm (Fin k)) e * e⁻¹ := by
  classical
  let p : Fin k := ⟨0, by omega⟩
  let ev : alternatingGroup (Fin k) → ZMod 2 := fun a => Multiplicative.toAdd (c a) p
  have hev_mul : ∀ a b : alternatingGroup (Fin k), (a : Equiv.Perm (Fin k)) p = p →
      ev (a * b) = ev a + ev b := by
    intro a b ha
    have h1 : (a : Equiv.Perm (Fin k))⁻¹ p = p := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact ha.symm
    simp only [ev, hc, toAdd_mul, Pi.add_apply, G6.permAct_apply, h1]
  have hev_one : ev 1 = 0 := by
    have h := hev_mul 1 1 (by simp)
    rw [mul_one] at h
    linear_combination -h
  have hev_stab : ∀ a : alternatingGroup (Fin k), (a : Equiv.Perm (Fin k)) p = p → ev a = 0 := by
    intro a ha
    have hmem : a ∈ (alternatingGroup.ofSubtype ({p}ᶜ : Finset (Fin k))).range := by
      rw [alternatingGroup.mem_range_ofSubtype_iff]
      intro x hx
      rw [Finset.mem_compl, Finset.mem_singleton]
      rintro rfl
      exact (Equiv.Perm.mem_support.mp hx) ha
    obtain ⟨x, rfl⟩ := hmem
    have hfix : ∀ x : alternatingGroup ↥({p}ᶜ : Finset (Fin k)),
        (alternatingGroup.ofSubtype ({p}ᶜ : Finset (Fin k)) x : Equiv.Perm (Fin k)) p = p := by
      intro x
      rw [alternatingGroup.coe_ofSubtype]
      exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp)
    let φ : alternatingGroup ↥({p}ᶜ : Finset (Fin k)) →* Multiplicative (ZMod 2) :=
      { toFun := fun x => Multiplicative.ofAdd
          (ev (alternatingGroup.ofSubtype ({p}ᶜ : Finset (Fin k)) x))
        map_one' := by simp [hev_one]
        map_mul' := fun x y => by
          simp only [map_mul, hev_mul _ _ (hfix x), ofAdd_add] }
    have hle : Subgroup.closure {g : alternatingGroup ↥({p}ᶜ : Finset (Fin k)) |
        (g : Equiv.Perm ↥({p}ᶜ : Finset (Fin k))).IsThreeCycle} ≤ φ.ker := by
      rw [Subgroup.closure_le]
      intro g hg
      have h3 : g ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← Equiv.Perm.IsThreeCycle.orderOf hg]
        exact pow_orderOf_eq_one _
      have h2 : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      calc φ g = φ g ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h2, one_mul]
        _ = φ (g ^ 3) := (map_pow φ g 3).symm
        _ = 1 := by rw [h3, map_one]
    rw [alternatingGroup.closure_isThreeCycles_eq_top] at hle
    have h := hle (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at h
    exact ofAdd_eq_one.mp h
  obtain ⟨g, hg⟩ : ∃ g : Fin k → alternatingGroup (Fin k),
      ∀ r, (g r : Equiv.Perm (Fin k)) p = r := by
    choose g hg using fun r => nrec_exists_alt hk3 p r
    exact ⟨g, hg⟩
  let f : Fin k → ZMod 2 := fun r => ev (g r)⁻¹
  have hf : ∀ (h : alternatingGroup (Fin k)) (r : Fin k), (h : Equiv.Perm (Fin k)) p = r →
      f r = ev h⁻¹ := by
    intro h r hh
    have h1 : (((g r)⁻¹ * h : alternatingGroup (Fin k)) : Equiv.Perm (Fin k)) p = p := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hh]
      exact Equiv.Perm.inv_eq_iff_eq.mpr (hg r).symm
    show ev (g r)⁻¹ = _
    calc ev (g r)⁻¹ = ev ((g r)⁻¹ * h * h⁻¹) := by rw [mul_inv_cancel_right]
      _ = ev ((g r)⁻¹ * h) + ev h⁻¹ := hev_mul _ _ h1
      _ = ev h⁻¹ := by rw [hev_stab _ h1, zero_add]
  have hkey : ∀ (y : alternatingGroup (Fin k)) (r : Fin k),
      Multiplicative.toAdd (c y) r = f ((y : Equiv.Perm (Fin k))⁻¹ r) + f r := by
    intro y r
    have h1 : ev ((g r)⁻¹ * y) = ev (g r)⁻¹ + Multiplicative.toAdd (c y) r := by
      have h3 : (((g r)⁻¹ : alternatingGroup (Fin k)) : Equiv.Perm (Fin k))⁻¹ p = r := by
        rw [Subgroup.coe_inv, inv_inv]
        exact hg r
      simp only [ev, hc, toAdd_mul, Pi.add_apply, G6.permAct_apply, h3]
    have h2 : f ((y : Equiv.Perm (Fin k))⁻¹ r) = ev ((g r)⁻¹ * y) := by
      rw [hf (y⁻¹ * g r) _ ?_]
      · rw [mul_inv_rev, inv_inv]
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hg r]
    rw [h2, h1]
    show _ = ev (g r)⁻¹ + _ + ev (g r)⁻¹
    generalize ev (g r)⁻¹ = x
    generalize Multiplicative.toAdd (c y) r = t
    revert x t
    decide
  let w : ZMod 2 := ∑ j, f j
  refine ⟨Multiplicative.ofAdd (fun i => f i + w), ?_, fun a => ?_⟩
  · rw [G6.mem_coreMod]
    simp only [toAdd_ofAdd]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.2 hk, one_mul]
    exact CharTwo.add_self_eq_zero _
  · apply Multiplicative.toAdd.injective
    funext r
    simp only [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply, toAdd_ofAdd]
    rw [hkey]
    generalize f ((a : Equiv.Perm (Fin k))⁻¹ r) = x
    generalize f r = y
    generalize w = z
    revert x y z
    decide

private theorem nrec_beta (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) :
    ∃ β : ↥(commV K) →* ↥(G6.coreMod k), Function.Bijective β ∧
      ∀ (y : K) (e : ↥(commV K)),
        ((β ⟨(y : MulAut V) (e : V), commV_invariant y.2 e.2⟩ : G6.coreMod k) : G6.PermMod k) =
          G6.permAct k ((θ y : alternatingGroup (Fin k)) : Equiv.Perm (Fin k))
            (β e : G6.PermMod k) := by
  obtain ⟨-, β, hsurj, hker, hβ⟩ := h
  refine ⟨β, ⟨?_, hsurj⟩, fun y e => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  · exact congrArg Subtype.val (hβ y e (commV_invariant y.2 e.2))

theorem card_commV_of_natural (hk : 1 ≤ k) (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) : Nat.card ↥(commV K) = 2 ^ (k - 1) := by
  obtain ⟨β, hβ, -⟩ := nrec_beta θ h
  rw [Nat.card_congr (Equiv.ofBijective β hβ)]
  exact nrec_card_coreMod hk

theorem commV_inf_fixV_of_natural (hk : Odd k) (hk3 : 3 ≤ k) (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) : commV K ⊓ fixV K = ⊥ := by
  obtain ⟨β, hβ, hequiv⟩ := nrec_beta θ h
  refine eq_bot_iff.mpr fun v hv => ?_
  obtain ⟨hvc, hvf⟩ := hv
  rw [Subgroup.mem_bot]
  have hfix : ∀ a : alternatingGroup (Fin k),
      G6.permAct k (a : Equiv.Perm (Fin k)) (β ⟨v, hvc⟩ : G6.PermMod k) = β ⟨v, hvc⟩ := by
    intro a
    obtain ⟨y, rfl⟩ := θ.surjective a
    have h2 : β ⟨(y : MulAut V) v, commV_invariant y.2 hvc⟩ = β ⟨v, hvc⟩ := by
      congr 1
      exact Subtype.ext (mem_fixV.mp hvf y y.2)
    exact ((congrArg Subtype.val h2).symm.trans (hequiv y ⟨v, hvc⟩)).symm
  have hconst : ∀ i j : Fin k, Multiplicative.toAdd (β ⟨v, hvc⟩ : G6.PermMod k) i =
      Multiplicative.toAdd (β ⟨v, hvc⟩ : G6.PermMod k) j := by
    intro i j
    obtain ⟨σ, hσ⟩ := nrec_exists_alt hk3 j i
    have h1 := congrArg (fun x : G6.PermMod k => Multiplicative.toAdd x i) (hfix σ)
    have hj : (σ : Equiv.Perm (Fin k))⁻¹ i = j := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hσ.symm
    simp only [G6.permAct_apply, hj] at h1
    exact h1.symm
  have hsum : ∑ i, Multiplicative.toAdd (β ⟨v, hvc⟩ : G6.PermMod k) i = 0 :=
    (β ⟨v, hvc⟩).2
  have hzero : ∀ i, Multiplicative.toAdd (β ⟨v, hvc⟩ : G6.PermMod k) i = 0 := by
    intro i
    rw [Finset.sum_congr rfl fun j _ => hconst j i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.2 hk, one_mul] at hsum
    exact hsum
  have h1 : β ⟨v, hvc⟩ = β 1 := by
    rw [map_one]
    exact Subtype.ext (Multiplicative.toAdd.injective (funext fun i => hzero i))
  exact congrArg Subtype.val (hβ.1 h1)

private def nrecComm (K : Subgroup (MulAut V)) (v : V) (y : K) : ↥(commV K) :=
  ⟨(y : MulAut V) v * v⁻¹, Subgroup.subset_closure ⟨y, y.2, v, rfl⟩⟩

private theorem nrecComm_mul (K : Subgroup (MulAut V)) (v : V) (y z : K) :
    nrecComm K v (y * z) = ⟨(y : MulAut V) (nrecComm K v z : V),
      commV_invariant y.2 (nrecComm K v z).2⟩ * nrecComm K v y := by
  apply Subtype.ext
  simp only [nrecComm, Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
  group

theorem commV_sup_fixV_of_natural (hk : Odd k) (hk5 : 5 ≤ k) (θ : K ≃* alternatingGroup (Fin k))
    (h : IsNatSectionWith (altAct k) θ (commV K) ⊥) : commV K ⊔ fixV K = ⊤ := by
  obtain ⟨β, hβ, hequiv⟩ := nrec_beta θ h
  refine eq_top_iff.mpr fun v _ => ?_
  let c : alternatingGroup (Fin k) → G6.PermMod k := fun a =>
    (β (nrecComm K v (θ.symm a)) : G6.PermMod k)
  have hc : ∀ a b : alternatingGroup (Fin k),
      c (a * b) = c a * G6.permAct k (a : Equiv.Perm (Fin k)) (c b) := by
    intro a b
    simp only [c]
    rw [map_mul θ.symm, nrecComm_mul, map_mul β, Subgroup.coe_mul, hequiv,
      θ.apply_symm_apply, mul_comm]
  obtain ⟨e, he, hce⟩ := nrec_coboundary hk (by omega) c hc
  obtain ⟨u, hu⟩ := hβ.2 ⟨e, he⟩
  have hyu : ∀ y : K, (y : MulAut V) (u : V) * (u : V)⁻¹ = (y : MulAut V) v * v⁻¹ := by
    intro y
    have h1 : β (⟨(y : MulAut V) (u : V), commV_invariant y.2 u.2⟩ * u⁻¹) =
        β (nrecComm K v y) := by
      apply Subtype.ext
      have h2 := hce (θ y)
      simp only [c, θ.symm_apply_apply] at h2
      rw [h2, map_mul, map_inv, Subgroup.coe_mul, hequiv, hu]
      rfl
    exact congrArg Subtype.val (hβ.1 h1)
  have hw : v * (u : V)⁻¹ ∈ fixV K := by
    intro y hy
    have h1 := hyu ⟨y, hy⟩
    rw [map_mul, map_inv]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_div_eq_div]
    simpa [div_eq_mul_inv] using h1.symm
  have hv : (u : V) * (v * (u : V)⁻¹) = v := by rw [mul_comm v, mul_inv_cancel_left]
  rw [← hv]
  exact Subgroup.mul_mem_sup u.2 hw

end CFSG.CGT.PushingUpLit.CGT6
