module

public import CFSG.CGT.PushingUpLit.BHS.AltCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section Alt

variable {V : Type} [CommGroup V]

structure SymDat (E : Subgroup (MulAut V)) (m : ℕ) where
  θ : ↥E ≃* Equiv.Perm (Fin m)
  β : ↥(commV E) →* coreMod m
  odd : Odd m
  three_le : 3 ≤ m
  inv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E
  surj : Function.Surjective β
  ker : β.ker = ⊥
  equiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
    β ⟨(x : MulAut V) p, hp⟩ = coreAct m (θ x) (β p)
  top : commV E ⊔ fixV E = ⊤

variable {E : Subgroup (MulAut V)} {m : ℕ}

@[expose] def altOf (θ : ↥E ≃* Equiv.Perm (Fin m)) : Subgroup (MulAut V) :=
  ((alternatingGroup (Fin m)).comap θ.toMonoidHom).map E.subtype

theorem mem_altOf (θ : ↥E ≃* Equiv.Perm (Fin m)) {x : MulAut V} :
    x ∈ altOf θ ↔ ∃ h : x ∈ E, θ ⟨x, h⟩ ∈ alternatingGroup (Fin m) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem altOf_le (θ : ↥E ≃* Equiv.Perm (Fin m)) : altOf θ ≤ E := by
  intro x hx
  obtain ⟨h, -⟩ := (mem_altOf θ).1 hx
  exact h

@[expose] def altHom (θ : ↥E ≃* Equiv.Perm (Fin m)) : ↥(altOf θ) →* alternatingGroup (Fin m) where
  toFun x := ⟨θ ⟨x, altOf_le θ x.2⟩, ((mem_altOf θ).1 x.2).2⟩
  map_one' := Subtype.ext (map_one θ)
  map_mul' x y := Subtype.ext (map_mul θ ⟨x, altOf_le θ x.2⟩ ⟨y, altOf_le θ y.2⟩)

theorem altHom_bijective (θ : ↥E ≃* Equiv.Perm (Fin m)) : Function.Bijective (altHom θ) := by
  refine ⟨fun x y h => ?_, fun σ => ?_⟩
  · have h1 := congrArg Subtype.val h
    have h2 : θ ⟨x, altOf_le θ x.2⟩ = θ ⟨y, altOf_le θ y.2⟩ := h1
    have h3 := θ.injective h2
    exact Subtype.ext (congrArg (fun z : ↥E => (z : MulAut V)) h3)
  · refine ⟨⟨(θ.symm σ : MulAut V), (mem_altOf θ).2 ⟨(θ.symm σ).2, ?_⟩⟩, ?_⟩
    · simp
    · refine Subtype.ext ?_
      show θ ⟨(θ.symm σ : MulAut V), _⟩ = σ
      simp

@[expose] noncomputable def altEquiv (θ : ↥E ≃* Equiv.Perm (Fin m)) :
    ↥(altOf θ) ≃* alternatingGroup (Fin m) :=
  MulEquiv.ofBijective (altHom θ) (altHom_bijective θ)

theorem altOf_normal (θ : ↥E ≃* Equiv.Perm (Fin m)) : ((altOf θ).subgroupOf E).Normal := by
  have h : (altOf θ).subgroupOf E = (alternatingGroup (Fin m)).comap θ.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective _
  rw [h]
  exact Subgroup.Normal.comap inferInstance _

theorem isSubnormal_altOf {P : Subgroup (MulAut V)} (θ : ↥E ≃* Equiv.Perm (Fin m))
    (h : CFSG.Open.IsSubnormal E P) : CFSG.Open.IsSubnormal (altOf θ) P :=
  CFSG.Open.IsSubnormal.step (altOf_le θ) (altOf_normal θ) h

end Alt

section Delta

variable {m : ℕ}

theorem vsum_pairVec_eq_self (o : Fin m) (v : ↥(coreMod m)) :
    vsum (fun i => pairVec o i) v = v := by
  refine vcoord_ext fun q => ?_
  refine (vcoord_map_vsum (MonoidHom.id ↥(coreMod m)) (fun i => pairVec o i) v q).trans ?_
  show ∑ i, vcoord v i * vcoord (pairVec o i) q = vcoord v q
  simp only [vcoord_pairVec, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_vcoord, zero_mul, zero_add]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem mem_closure_pairVec (hm : 0 < m) (v : ↥(coreMod m)) :
    v ∈ Subgroup.closure {x : ↥(coreMod m) | ∃ a b : Fin m, x = pairVec a b} := by
  rw [← vsum_pairVec_eq_self ⟨0, hm⟩ v, vsum]
  refine Subgroup.prod_mem _ fun i _ => Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _
  exact ⟨⟨0, hm⟩, i, rfl⟩

end Delta

section Dat

variable {V : Type} [CommGroup V] {E : Subgroup (MulAut V)} {m : ℕ} (D : SymDat E m)

include D in
theorem SymDat.exists_lift_pairVec {a b : Fin m} (hab : a ≠ b) :
    ∃ q : ↥(commV E), (q : V) ∈ commV (altOf D.θ) ∧ D.β q = pairVec a b := by
  obtain ⟨k, hka, hkb⟩ := exists_ne_ne D.three_le a b
  obtain ⟨w, hw⟩ := D.surj (pairVec a k)
  set x : ↥E := D.θ.symm (cyc a b k) with hx
  have hx3 : (cyc a b k).IsThreeCycle := cyc_isThreeCycle hab (Ne.symm hka) (Ne.symm hkb)
  have hθx : D.θ x = cyc a b k := MulEquiv.apply_symm_apply _ _
  have hxalt : (x : MulAut V) ∈ altOf D.θ :=
    (mem_altOf D.θ).2 ⟨x.2, by
      rw [Equiv.Perm.mem_alternatingGroup]
      show Equiv.Perm.sign (D.θ x) = 1
      rw [hθx]
      exact hx3.sign⟩
  have hxw : (x : MulAut V) w ∈ commV E := D.inv _ x.2 _ w.2
  refine ⟨⟨_, hxw⟩ * w⁻¹, mem_commV_of_mem hxalt (w : V), ?_⟩
  rw [map_mul, map_inv, D.equiv x w hxw, hθx, hw]
  exact coreAct_cyc_pairVec (Ne.symm hka) (Ne.symm hkb)

include D in
theorem SymDat.commV_altOf : commV (altOf D.θ) = commV E := by
  refine le_antisymm (G6.commV_mono (altOf_le D.θ)) fun p hp => ?_
  set S : Subgroup (coreMod m) := ((commV (altOf D.θ)).subgroupOf (commV E)).map D.β with hS
  have hpair : ∀ a b : Fin m, pairVec a b ∈ S := by
    intro a b
    by_cases hab : a = b
    · rw [hab, pairVec_self]
      exact S.one_mem
    · obtain ⟨q, hq, hβ⟩ := D.exists_lift_pairVec hab
      exact ⟨q, hq, hβ⟩
  have hS' : ∀ v : ↥(coreMod m), v ∈ S := fun v =>
    (Subgroup.closure_le S).2 (by rintro _ ⟨a, b, rfl⟩; exact hpair a b)
      (mem_closure_pairVec (by have := D.three_le; omega) v)
  obtain ⟨q, hq, hβq⟩ := hS' (D.β ⟨p, hp⟩)
  have hinj : Function.Injective D.β := (MonoidHom.ker_eq_bot_iff _).1 D.ker
  have hqp : q = ⟨p, hp⟩ := hinj hβq
  have h1 : (q : V) ∈ commV (altOf D.θ) := hq
  rw [hqp] at h1
  exact h1

include D in
theorem SymDat.injective_β : Function.Injective D.β := (MonoidHom.ker_eq_bot_iff _).1 D.ker

include D in
theorem SymDat.commV_inf_fixV_altOf : commV (altOf D.θ) ⊓ fixV (altOf D.θ) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvc, hvf⟩
  have hvE : v ∈ commV E := D.commV_altOf ▸ hvc
  have hone : ∀ b ∈ alternatingGroup (Fin m), ∀ i, vcoord (D.β ⟨v, hvE⟩) (b⁻¹ i) =
      vcoord (D.β ⟨v, hvE⟩) i := by
    intro b hb i
    have hx : ((D.θ.symm b : ↥E) : MulAut V) ∈ altOf D.θ :=
      (mem_altOf D.θ).2 ⟨(D.θ.symm b).2, by simpa using hb⟩
    have hxv : ((D.θ.symm b : ↥E) : MulAut V) v = v := hvf _ hx
    have h1 := D.equiv (D.θ.symm b) ⟨v, hvE⟩ (by rw [hxv]; exact hvE)
    have h2 : (⟨((D.θ.symm b : ↥E) : MulAut V) v, by rw [hxv]; exact hvE⟩ : ↥(commV E)) =
        ⟨v, hvE⟩ := Subtype.ext hxv
    rw [h2, MulEquiv.apply_symm_apply] at h1
    have h3 := congrArg (fun u => vcoord u i) h1
    simp only [vcoord_coreAct] at h3
    exact h3.symm
  have hfix : D.β ⟨v, hvE⟩ ∈ fixV ((alternatingGroup (Fin m)).map (coreAct m)) := by
    rw [mem_fixV_map_iff]
    intro a ha i
    have := hone a⁻¹ (Subgroup.inv_mem _ ha) i
    simpa using this
  rw [fixV_alt_map D.odd D.three_le, Subgroup.mem_bot] at hfix
  have h4 : (⟨v, hvE⟩ : ↥(commV E)) = 1 := D.injective_β (hfix.trans (map_one D.β).symm)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h4)

@[expose] def SymDat.βalt : ↥(commV (altOf D.θ)) →* coreMod m :=
  D.β.comp (Subgroup.inclusion D.commV_altOf.le)

include D in
theorem SymDat.βalt_surjective : Function.Surjective D.βalt := by
  intro u
  obtain ⟨q, hq⟩ := D.surj u
  exact ⟨⟨q, D.commV_altOf.ge q.2⟩, hq⟩

include D in
theorem SymDat.βalt_injective : Function.Injective D.βalt :=
  D.injective_β.comp (Subgroup.inclusion_injective _)

include D in
theorem SymDat.βalt_ker :
    D.βalt.ker = (commV (altOf D.θ) ⊓ fixV (altOf D.θ)).subgroupOf (commV (altOf D.θ)) := by
  rw [D.commV_inf_fixV_altOf, Subgroup.bot_subgroupOf]
  exact (MonoidHom.ker_eq_bot_iff _).2 D.βalt_injective

include D in
theorem SymDat.βalt_equiv (x : ↥(altOf D.θ)) (p : ↥(commV (altOf D.θ)))
    (hp : (x : MulAut V) p ∈ commV (altOf D.θ)) :
    D.βalt ⟨(x : MulAut V) p, hp⟩ =
      coreAct m ((altEquiv D.θ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) (D.βalt p) :=
  D.equiv ⟨x, altOf_le D.θ x.2⟩ ⟨p, D.commV_altOf.le p.2⟩ _

include D in
theorem SymDat.isAltNatSection_altOf :
    IsAltNatSection (altOf D.θ) (commV (altOf D.θ)) (commV (altOf D.θ) ⊓ fixV (altOf D.θ)) m :=
  ⟨fun x hx p hp => by
    rw [D.commV_altOf] at hp ⊢
    exact D.inv x (altOf_le D.θ hx) p hp,
   altEquiv D.θ, D.βalt, D.βalt_surjective, D.βalt_ker, D.βalt_equiv⟩

include D in
theorem SymDat.commutator_altOf_ne_bot {X : Subgroup (MulAut V)} {b₀ : MulAut V} (hb₀X : b₀ ∈ X)
    (hb₀E : b₀ ∈ E) {i j : Fin m} (hij : i ≠ j) (hθ : D.θ ⟨b₀, hb₀E⟩ = Equiv.swap i j) :
    ⁅altOf D.θ, X⁆ ≠ ⊥ := by
  intro hbot
  obtain ⟨k, hki, hkj⟩ := exists_ne_ne D.three_le i j
  set x : ↥E := D.θ.symm (cyc i j k) with hx
  have hx3 : (cyc i j k).IsThreeCycle := cyc_isThreeCycle hij (Ne.symm hki) (Ne.symm hkj)
  have hθx : D.θ x = cyc i j k := MulEquiv.apply_symm_apply _ _
  have hxalt : (x : MulAut V) ∈ altOf D.θ :=
    (mem_altOf D.θ).2 ⟨x.2, by
      rw [Equiv.Perm.mem_alternatingGroup]
      show Equiv.Perm.sign (D.θ x) = 1
      rw [hθx]
      exact hx3.sign⟩
  have hc : ⁅(x : MulAut V), b₀⁆ ∈ ⁅altOf D.θ, X⁆ :=
    Subgroup.commutator_mem_commutator hxalt hb₀X
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  have h1 : D.θ ⟨(x : MulAut V) * b₀, E.mul_mem x.2 hb₀E⟩ =
      D.θ ⟨b₀ * (x : MulAut V), E.mul_mem hb₀E x.2⟩ :=
    congrArg D.θ (Subtype.ext hc)
  rw [show (⟨(x : MulAut V) * b₀, E.mul_mem x.2 hb₀E⟩ : ↥E) = x * ⟨b₀, hb₀E⟩ from rfl,
    show (⟨b₀ * (x : MulAut V), E.mul_mem hb₀E x.2⟩ : ↥E) = ⟨b₀, hb₀E⟩ * x from rfl, map_mul,
    map_mul, hθx, hθ] at h1
  have h2 := congrArg (fun σ : Equiv.Perm (Fin m) => σ i) h1
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h2
  rw [cyc_apply_second hij (Ne.symm hkj), cyc_apply_first (Ne.symm hki) (Ne.symm hkj),
    Equiv.swap_apply_of_ne_of_ne hki hkj] at h2
  exact hki h2.symm

end Dat

section Pt

variable {m : ℕ}

@[expose] def ptVec (hm : Odd m) (i : Fin m) : ↥(coreMod m) :=
  mkEven (fun k => if k = i then 0 else 1) (by
    have h1 : ∀ k : Fin m, (if k = i then (0 : ZMod 2) else 1) = 1 + if k = i then 1 else 0 := by
      intro k
      split_ifs <;> decide
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [nsmul_eq_mul, hm.natCast_zmod_two]
    decide)

theorem vcoord_ptVec (hm : Odd m) (i k : Fin m) :
    vcoord (ptVec hm i) k = if k = i then 0 else 1 := rfl

theorem coreAct_ptVec (hm : Odd m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    coreAct m σ (ptVec hm i) = ptVec hm (σ i) := by
  refine vcoord_ext fun k => ?_
  rw [vcoord_coreAct, vcoord_ptVec, vcoord_ptVec]
  simp only [Equiv.Perm.inv_eq_iff_eq]

theorem ptVec_injective (hm : Odd m) {i j : Fin m} (h : ptVec hm i = ptVec hm j) : i = j := by
  by_contra hne
  have := congrArg (fun v => vcoord v i) h
  simp [vcoord_ptVec, hne] at this

theorem apply_mem_pair_of_commute_swap {σ : Equiv.Perm (Fin m)} {i j : Fin m} (hij : i ≠ j)
    (h : σ * Equiv.swap i j = Equiv.swap i j * σ) : σ i = i ∨ σ i = j := by
  by_contra hcon
  push Not at hcon
  have h1 := congrArg (fun τ : Equiv.Perm (Fin m) => τ i) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h1
  rw [Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2] at h1
  exact hij (σ.injective h1).symm

end Pt

end CFSG.CGT.PushingUpLit.BHS5
