module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDPi

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC (card_evenWeight)
open scoped IsMulCommutative

section Abelian

variable {A : Type*} [CommGroup A]

@[expose] def Fv (a : Fin 5 → A) (w : Fin 5 → ZMod 2) : A := ∏ i, if w i = 0 then 1 else a i

theorem zmod2_cases (p : ZMod 2) : p = 0 ∨ p = 1 := by revert p; decide

theorem ite_add {x : A} (hx : x * x = 1) (p q : ZMod 2) :
    (if p + q = 0 then (1 : A) else x) = (if p = 0 then 1 else x) * (if q = 0 then 1 else x) := by
  rcases zmod2_cases p with rfl | rfl <;> rcases zmod2_cases q with rfl | rfl
  · simp
  · simp
  · simp
  · have h : (1 + 1 : ZMod 2) = 0 := by decide
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    simp [h, h1, hx]

theorem Fv_add {a : Fin 5 → A} (ha : ∀ i, a i * a i = 1) (w w' : Fin 5 → ZMod 2) :
    Fv a (w + w') = Fv a w * Fv a w' := by
  simp only [Fv, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => ite_add (ha i) _ _

theorem Fv_zero (a : Fin 5 → A) : Fv a 0 = 1 := by simp [Fv]

theorem Fv_pact {a : Fin 5 → A} (σ : Perm (Fin 5)) (w : Fin 5 → ZMod 2) :
    Fv a (pact σ w) = Fv (fun i => a (σ i)) w := by
  simp only [Fv, pact]
  rw [← Equiv.prod_comp σ]
  simp

theorem Fv_single {a : Fin 5 → A} (i : Fin 5) : Fv a (Pi.single i 1) = a i := by
  simp only [Fv]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem Fv_update_four {a : Fin 5 → A} (h4 : a 4 = 1) (w : Fin 5 → ZMod 2) (c : ZMod 2) :
    Fv a (Function.update w 4 c) = Fv a w := by
  simp only [Fv]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = 4
  · subst hi; simp [h4]
  · simp [Function.update_of_ne hi]

theorem Fv_map {B : Type*} [CommGroup B] (f : A →* B) (a : Fin 5 → A) (w : Fin 5 → ZMod 2) :
    f (Fv a w) = Fv (fun i => f (a i)) w := by
  simp only [Fv, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Abelian

section Group

variable {G : Type} [Group G]

@[expose] def conjHomU {U : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (U : Set G)) :
    ↥U →* ↥U where
  toFun u := ⟨y * u * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy u).1 u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

noncomputable def labAct (lab : Fin 5 → G) (y : G) (i : Fin 5) : Fin 5 :=
  Classical.epsilon fun j => y * lab i * y⁻¹ = lab j

theorem labAct_spec {lab : Fin 5 → G} {y : G} {i : Fin 5} (h : ∃ j, y * lab i * y⁻¹ = lab j) :
    y * lab i * y⁻¹ = lab (labAct lab y i) := Classical.epsilon_spec h

variable {S : Subgroup G} {lab : Fin 5 → G}

theorem labAct_mul (hinj : Function.Injective lab)
    (hstab : ∀ y ∈ S, ∀ i, ∃ j, y * lab i * y⁻¹ = lab j) {y z : G} (hy : y ∈ S) (hz : z ∈ S)
    (i : Fin 5) : labAct lab (y * z) i = labAct lab y (labAct lab z i) := by
  apply hinj
  rw [← labAct_spec (hstab _ (mul_mem hy hz) i), ← labAct_spec (hstab y hy _),
    ← labAct_spec (hstab z hz i)]
  group

theorem labAct_one (hinj : Function.Injective lab) (i : Fin 5) : labAct lab 1 i = i := by
  apply hinj
  rw [← labAct_spec (⟨i, by simp⟩ : ∃ j, (1 : G) * lab i * (1 : G)⁻¹ = lab j)]
  simp

@[expose] noncomputable def labHom (hinj : Function.Injective lab)
    (hstab : ∀ y ∈ S, ∀ i, ∃ j, y * lab i * y⁻¹ = lab j) : ↥S →* Perm (Fin 5) where
  toFun y :=
    { toFun := labAct lab (y : G)
      invFun := labAct lab (y : G)⁻¹
      left_inv := fun i => by
        rw [← labAct_mul hinj hstab (inv_mem y.2) y.2, inv_mul_cancel, labAct_one hinj]
      right_inv := fun i => by
        rw [← labAct_mul hinj hstab y.2 (inv_mem y.2), mul_inv_cancel, labAct_one hinj] }
  map_one' := by
    refine Equiv.ext fun i => ?_
    exact labAct_one hinj i
  map_mul' y z := by
    refine Equiv.ext fun i => ?_
    exact labAct_mul hinj hstab y.2 z.2 i

theorem labHom_spec (hinj : Function.Injective lab)
    (hstab : ∀ y ∈ S, ∀ i, ∃ j, y * lab i * y⁻¹ = lab j) (y : ↥S) (i : Fin 5) :
    (y : G) * lab i * (y : G)⁻¹ = lab (labHom hinj hstab y i) :=
  labAct_spec (hstab y y.2 i)

end Group

section Main

variable {G : Type} [Group G]

theorem pact_add_self (w : Fin 5 → ZMod 2) : w + w = 0 := by
  funext i
  show w i + w i = 0
  generalize w i = a
  revert a
  decide

theorem exists_PiS {S U : Subgroup G} (hSU : S ≤ Subgroup.normalizer (U : Set G))
    (hUe : IsElemAbelian 2 U) (hcard : Nat.card U = 16)
    (lab : Fin 5 → G) (hmem : ∀ i, lab i ∈ U) (h4 : lab 4 = 1) (hinj : Function.Injective lab)
    (hgen : U ≤ Subgroup.closure (Set.range lab))
    (hstab : ∀ y ∈ S, ∀ i, ∃ j, y * lab i * y⁻¹ = lab j) :
    ∃ P : PiS S U, ∀ (y : ↥S) (i : Fin 5), (y : G) * lab i * (y : G)⁻¹ = lab (P.π y i) := by
  classical
  have : IsMulCommutative U := hUe.1
  obtain ⟨-, hsq2⟩ := C5.isElemAbelian_two_iff.1 hUe
  set lab' : Fin 5 → ↥U := fun i => ⟨lab i, hmem i⟩ with hlab'
  have hsq : ∀ i, lab' i * lab' i = 1 := fun i =>
    Subtype.ext (by simpa [pow_two] using hsq2 (lab i) (hmem i))
  have h4' : lab' 4 = 1 := Subtype.ext h4
  set fU : Multiplicative (evenWeight 5) →* ↥U :=
    { toFun := fun w => Fv lab' (Multiplicative.toAdd w).1
      map_one' := by simpa using Fv_zero lab'
      map_mul' := fun a b => by
        simpa using Fv_add hsq (Multiplicative.toAdd a).1 (Multiplicative.toAdd b).1 } with hfU
  have key : ∀ g ∈ Subgroup.closure (Set.range lab),
      ∃ hg : g ∈ U, ∃ w : Fin 5 → ZMod 2, Fv lab' w = ⟨g, hg⟩ := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ∃ hg : g ∈ U, ∃ w : Fin 5 → ZMod 2,
      Fv lab' w = ⟨g, hg⟩) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨i, rfl⟩
      exact ⟨hmem i, Pi.single i 1, Fv_single i⟩
    · exact ⟨U.one_mem, 0, Fv_zero _⟩
    · rintro a b _ _ ⟨ha, wa, hwa⟩ ⟨hb, wb, hwb⟩
      refine ⟨U.mul_mem ha hb, wa + wb, ?_⟩
      rw [Fv_add hsq, hwa, hwb]
      rfl
    · rintro a _ ⟨ha, wa, hwa⟩
      refine ⟨U.inv_mem ha, wa, ?_⟩
      have h1 : Fv lab' wa * Fv lab' wa = 1 := by
        rw [← Fv_add hsq, pact_add_self, Fv_zero]
      rw [hwa] at h1 ⊢
      have : (⟨a, ha⟩ : ↥U)⁻¹ = ⟨a, ha⟩ := inv_eq_of_mul_eq_one_right h1
      exact this.symm
  have hsurj : Function.Surjective fU := by
    intro u
    obtain ⟨hu, w, hw⟩ := key (u : G) (hgen u.2)
    set w' : Fin 5 → ZMod 2 := Function.update w 4 (w 0 + w 1 + w 2 + w 3) with hw'
    have hw'even : w' ∈ evenWeight 5 := by
      rw [mem_evenWeight_iff]
      show ∑ i, w' i = 0
      rw [Fin.sum_univ_five]
      simp only [hw', Function.update_apply]
      simp
      generalize w 0 = a
      generalize w 1 = b
      generalize w 2 = c
      generalize w 3 = d
      revert a b c d
      decide
    refine ⟨Multiplicative.ofAdd ⟨w', hw'even⟩, ?_⟩
    show Fv lab' w' = u
    rw [hw', Fv_update_four h4', hw]
  have hcardα : Nat.card (Multiplicative (evenWeight 5)) = 16 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
    exact card_evenWeight
  have hbij : Function.Bijective fU :=
    hsurj.bijective_of_nat_card_le (by rw [hcardα, hcard])
  set β : ↥U ≃* Multiplicative (evenWeight 5) := (MulEquiv.ofBijective fU hbij).symm with hβ
  have hβf : ∀ w : Multiplicative (evenWeight 5), β (fU w) = w := fun w =>
    (MulEquiv.ofBijective fU hbij).symm_apply_apply w
  have hfβ : ∀ u : ↥U, fU (β u) = u := fun u =>
    (MulEquiv.ofBijective fU hbij).apply_symm_apply u
  set π : ↥S →* Perm (Fin 5) := labHom hinj hstab with hπ
  have hspec : ∀ (y : ↥S) (i : Fin 5), (y : G) * lab i * (y : G)⁻¹ = lab (π y i) :=
    labHom_spec hinj hstab
  have hyN : ∀ y : ↥S, (y : G) ∈ Subgroup.normalizer (U : Set G) := fun y => hSU y.2
  have master : ∀ (y : ↥S) (w : Fin 5 → ZMod 2),
      conjHomU (hyN y) (Fv lab' w) = Fv lab' (pact (π y) w) := by
    intro y w
    rw [Fv_map, Fv_pact]
    congr 1
    funext i
    exact Subtype.ext (hspec y i)
  refine ⟨⟨β, π, hSU, ?_, ?_⟩, hspec⟩
  · intro y u u' hu'
    set w := Multiplicative.toAdd (β u) with hw
    have hu : u = fU (Multiplicative.ofAdd w) := by
      rw [hw, ofAdd_toAdd, hfβ]
    have hu'eq : u' = conjHomU (hyN y) u := Subtype.ext hu'
    have : u' = fU (Multiplicative.ofAdd (vact (π y) w)) := by
      rw [hu'eq, hu]
      exact master y w.1
    rw [this, hβf]
    rfl
  · intro y
    constructor
    · intro h1 u hu
      obtain ⟨hg, w, hw⟩ := key u (hgen hu)
      have := master y w
      rw [h1, pact_one, hw] at this
      exact congrArg Subtype.val this
    · intro h1
      refine Equiv.ext fun i => hinj ?_
      rw [← hspec y i]
      exact h1 (lab i) (hmem i)
end Main

end CFSG.QuasithinUnique.AppD
