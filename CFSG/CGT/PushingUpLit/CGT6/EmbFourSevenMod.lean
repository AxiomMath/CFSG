module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NormMap
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.YuBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin

section Generic

variable {V : Type} [CommGroup V] [Finite V] {Y : Subgroup (MulAut V)} [Group.IsPerfect ↥Y]

@[expose] def psiC (hV : ∀ v : V, v ^ 2 = 1) {M : Type*} [Group M]
    (ψ : ↥(shortU ↥(yuHol Y)) →* M) : ↥(commV Y) →* M :=
  ψ.comp ((yuInc Y).codRestrict (shortU ↥(yuHol Y)) fun u => yuInc_mem_shortU Y hV u)

theorem psiC_apply (hV : ∀ v : V, v ^ 2 = 1) {M : Type*} [Group M]
    (ψ : ↥(shortU ↥(yuHol Y)) →* M) (u : ↥(commV Y)) :
    psiC hV ψ u = ψ ⟨yuInc Y u, yuInc_mem_shortU Y hV u⟩ := rfl

theorem fix_of_psiC_eq_one (hV : ∀ v : V, v ^ 2 = 1) {M : Type*} [Group M]
    (ψ : ↥(shortU ↥(yuHol Y)) →* M)
    (hker : ψ.ker = (shortC ↥(yuHol Y)).subgroupOf (shortU ↥(yuHol Y))) {u : ↥(commV Y)}
    (h : psiC hV ψ u = 1) : ∀ g ∈ Y, (g : MulAut V) (u : V) = u := by
  intro g hg
  have h1 : (⟨yuInc Y u, yuInc_mem_shortU Y hV u⟩ : ↥(shortU ↥(yuHol Y))) ∈ ψ.ker := h
  rw [hker, Subgroup.mem_subgroupOf] at h1
  exact apply_eq_of_yuInc_mem_center Y (g := ⟨g, hg⟩) h1.2

theorem psiC_apply_smul (hV : ∀ v : V, v ^ 2 = 1) {M : Type*} [Group M]
    (ψ : ↥(shortU ↥(yuHol Y)) →* M) (g : ↥Y) (u : ↥(commV Y))
    (hu' : yuSec Y g * yuInc Y u * (yuSec Y g)⁻¹ ∈ shortU ↥(yuHol Y)) :
    psiC hV ψ ⟨(g : MulAut V) (u : V), apply_mem_commV_self Y g.2 u.2⟩ =
      ψ ⟨yuSec Y g * yuInc Y u * (yuSec Y g)⁻¹, hu'⟩ := by
  rw [psiC_apply]
  congr 1
  exact Subtype.ext (conj_yuInc Y (yuSec Y g) u).symm

end Generic

section Bound

variable {V : Type} [CommGroup V]

theorem commV_le_ker_normK (K : Subgroup (MulAut V)) [Fintype ↥K] : commV K ≤ (normK K).ker := by
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, v, rfl⟩
  show normK K (k v * v⁻¹) = 1
  rw [map_mul, map_inv, normK_apply_mem K hk, mul_inv_cancel]

theorem commV_zpowers_le {Y : Subgroup (MulAut V)} {x : MulAut V} (hxY : x ∈ Y) :
    commV (Subgroup.zpowers x) ≤ commV Y := by
  unfold commV
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, v, rfl⟩
  exact Subgroup.subset_closure ⟨k, (Subgroup.zpowers_le.mpr hxY) hk, v, rfl⟩

theorem odd_card_zpowers {x : MulAut V} (hx5 : x ^ 5 = 1) [Fintype ↥(Subgroup.zpowers x)] :
    Odd (Fintype.card ↥(Subgroup.zpowers x)) := by
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx5)

variable [Finite V] {Y : Subgroup (MulAut V)} [Group.IsPerfect ↥Y]

omit [Group.IsPerfect ↥Y] in
theorem trivial_of_invariant {x : MulAut V} (hxY : x ∈ Y) (hx5 : x ^ 5 = 1) {N : Type*}
    [CommGroup N] (hN : ∀ n : N, n ^ 2 = 1) (f : ↥(commV Y) →* N)
    (hf : ∀ u : ↥(commV Y), f ⟨x u, apply_mem_commV_self Y hxY u.2⟩ = f u) {u : V}
    (huC : u ∈ commV (Subgroup.zpowers x)) (huY : u ∈ commV Y) : f ⟨u, huY⟩ = 1 := by
  classical
  let F : V → N := fun v => if h : v ∈ commV Y then f ⟨v, h⟩ else 1
  have hF : ∀ (v : V) (h : v ∈ commV Y), F v = f ⟨v, h⟩ := fun v h => by simp [F, h]
  have hFx : ∀ v ∈ commV Y, F (x v) = F v := fun v hv => by
    rw [hF v hv, hF (x v) (apply_mem_commV_self Y hxY hv)]
    exact hf ⟨v, hv⟩
  let I : Subgroup (MulAut V) :=
    { carrier := {k | k ∈ Y ∧ ∀ v ∈ commV Y, F (k v) = F v}
      one_mem' := ⟨one_mem _, fun v _ => rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun v hv => by
        show F (a (b v)) = F v
        rw [ha.2 (b v) (apply_mem_commV_self Y hb.1 hv), hb.2 v hv]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun v hv => by
        have h1 := ha.2 (a⁻¹ v) (apply_mem_commV_self Y (inv_mem ha.1) hv)
        rw [MulAut.apply_inv_self] at h1
        exact h1.symm⟩ }
  have hxI : x ∈ I := ⟨hxY, hFx⟩
  have hKI : Subgroup.zpowers x ≤ I := Subgroup.zpowers_le.mpr hxI
  have : Fintype ↥(Subgroup.zpowers x) := Fintype.ofFinite _
  have hker : normK (Subgroup.zpowers x) u = 1 := commV_le_ker_normK _ huC
  have hKY : ∀ k : ↥(Subgroup.zpowers x), (k : MulAut V) ∈ Y := fun k =>
    (Subgroup.zpowers_le.mpr hxY) k.2
  let w : ↥(Subgroup.zpowers x) → ↥(commV Y) := fun k =>
    ⟨(k : MulAut V) u, apply_mem_commV_self Y (hKY k) huY⟩
  have h1 : (∏ k : ↥(Subgroup.zpowers x), w k) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_finsetProd]
    exact hker
  have h2 : f (∏ k : ↥(Subgroup.zpowers x), w k) = ∏ k : ↥(Subgroup.zpowers x), f (w k) :=
    map_prod f _ _
  have h3 : ∀ k : ↥(Subgroup.zpowers x), f (w k) = f ⟨u, huY⟩ := fun k => by
    rw [← hF _ (apply_mem_commV_self Y (hKY k) huY), ← hF u huY]
    exact (hKI k.2).2 u huY
  rw [h1, map_one, Finset.prod_congr rfl (fun k _ => h3 k), Finset.prod_const,
    Finset.card_univ] at h2
  obtain ⟨m, hm⟩ := odd_card_zpowers hx5
  rw [hm, pow_succ, pow_mul, hN, one_pow, one_mul] at h2
  exact h2.symm

theorem card_commV_le_of_psiC (hV : ∀ v : V, v ^ 2 = 1) {M : Type*} [Group M]
    (ψ : ↥(shortU ↥(yuHol Y)) →* M)
    (hker : ψ.ker = (shortC ↥(yuHol Y)).subgroupOf (shortU ↥(yuHol Y)))
    {x : MulAut V} (hxY : x ∈ Y) (hx5 : x ^ 5 = 1) (T : Subgroup M) [Finite T]
    (hT : ∀ u : ↥(commV Y), (u : V) ∈ commV (Subgroup.zpowers x) → psiC hV ψ u ∈ T) :
    Nat.card (commV (Subgroup.zpowers x)) ≤ Nat.card T := by
  classical
  have : Fintype ↥(Subgroup.zpowers x) := Fintype.ofFinite _
  have hCY := commV_zpowers_le hxY
  let g : ↥(commV (Subgroup.zpowers x)) → ↥T := fun u =>
    ⟨psiC hV ψ ⟨u, hCY u.2⟩, hT ⟨u, hCY u.2⟩ u.2⟩
  refine Nat.card_le_card_of_injective g fun u u' h => ?_
  have h1 : psiC hV ψ ⟨u, hCY u.2⟩ = psiC hV ψ ⟨u', hCY u'.2⟩ := congrArg Subtype.val h
  have h2 : psiC hV ψ ⟨(u : V) * (u' : V)⁻¹, mul_mem (hCY u.2) (inv_mem (hCY u'.2))⟩ = 1 := by
    have : (⟨(u : V) * (u' : V)⁻¹, mul_mem (hCY u.2) (inv_mem (hCY u'.2))⟩ : ↥(commV Y)) =
        ⟨u, hCY u.2⟩ * ⟨u', hCY u'.2⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, h1, mul_inv_cancel]
  have hfix := fix_of_psiC_eq_one hV ψ hker h2
  have hmem : (u : V) * (u' : V)⁻¹ ∈ (normK (Subgroup.zpowers x)).ker ⊓
      fixV (Subgroup.zpowers x) := by
    refine ⟨commV_le_ker_normK _ (mul_mem u.2 (inv_mem u'.2)), fun k hk => ?_⟩
    exact hfix k ((Subgroup.zpowers_le.mpr hxY) hk)
  rw [normK_ker_inf_fixV _ (odd_card_zpowers hx5) hV, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact Subtype.ext hmem

end Bound

section Alt

variable {V : Type} [CommGroup V] [Finite V] {Y : Subgroup (MulAut V)} [Group.IsPerfect ↥Y]

@[expose] def movedSumZero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Subgroup (Multiplicative (Fin n → ZMod 2)) where
  carrier := {w | (∀ j, σ j = j → Multiplicative.toAdd w j = 0) ∧
    ∑ j, Multiplicative.toAdd w j = 0}
  one_mem' := ⟨fun j _ => rfl, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨fun j hj => by simp [ha.1 j hj, hb.1 j hj],
    by simp [Finset.sum_add_distrib, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨fun j hj => by simp [ha.1 j hj], by simp [ha.2]⟩

theorem card_movedSumZero_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (h5 : σ.support.card = 5) :
    Nat.card (movedSumZero σ) ≤ 16 := by
  classical
  obtain ⟨i₀, hi₀⟩ : σ.support.Nonempty := Finset.card_pos.mp (by omega)
  let g : ↥(movedSumZero σ) → (↥(σ.support.erase i₀) → ZMod 2) := fun w j =>
    Multiplicative.toAdd (w : Multiplicative (Fin n → ZMod 2)) j.1
  have hinj : Function.Injective g := by
    intro w w' h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext j
    have hne : ∀ j, j ≠ i₀ → Multiplicative.toAdd (w : Multiplicative (Fin n → ZMod 2)) j =
        Multiplicative.toAdd (w' : Multiplicative (Fin n → ZMod 2)) j := by
      intro j hj
      by_cases hjs : j ∈ σ.support
      · exact congrFun h ⟨j, Finset.mem_erase.mpr ⟨hj, hjs⟩⟩
      · have := Equiv.Perm.notMem_support.mp hjs
        rw [w.2.1 j this, w'.2.1 j this]
    by_cases hj : j = i₀
    · subst hj
      have h1 := w.2.2
      have h2 := w'.2.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h1 h2
      have h3 : ∑ k ∈ Finset.univ.erase j,
            Multiplicative.toAdd (w : Multiplicative (Fin n → ZMod 2)) k =
          ∑ k ∈ Finset.univ.erase j,
            Multiplicative.toAdd (w' : Multiplicative (Fin n → ZMod 2)) k :=
        Finset.sum_congr rfl fun k hk => hne k (Finset.ne_of_mem_erase hk)
      rw [h3] at h1
      exact add_right_cancel (h1.trans h2.symm)
    · exact hne j hj
  have h1 := Nat.card_le_card_of_injective g hinj
  have h2 : Nat.card (↥(σ.support.erase i₀) → ZMod 2) = 16 := by
    have h4 : Nat.card ↥(σ.support.erase i₀) = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_erase_of_mem hi₀, h5]
    rw [Nat.card_fun, h4, Nat.card_zmod]
    norm_num
  omega

theorem card_commV_le_alt (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ}
    (φ : (↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) ≃* alternatingGroup (Fin n))
    (ψ : ↥(shortU ↥(yuHol Y)) →* Multiplicative (Fin n → ZMod 2))
    (hsum : ∀ u, ∑ i, Multiplicative.toAdd (ψ u) i = 0)
    (hker : ψ.ker = (shortC ↥(yuHol Y)).subgroupOf (shortU ↥(yuHol Y)))
    (heq : ∀ (l u : ↥(yuHol Y)) (hu : u ∈ shortU ↥(yuHol Y))
      (hu' : l * u * l⁻¹ ∈ shortU ↥(yuHol Y)),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd (permActionTwo
        ((φ (l : ↥(yuHol Y) ⧸ pCore 2 ↥(yuHol Y)) : alternatingGroup (Fin n)) : Equiv.Perm _)
        (Multiplicative.toAdd (ψ ⟨u, hu⟩))))
    {x : MulAut V} (hxY : x ∈ Y) (hx5 : x ^ 5 = 1)
    (hsupp : ((yuTheta Y φ ⟨x, hxY⟩ : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n)).support.card = 5) :
    Nat.card (commV (Subgroup.zpowers x)) ≤ 16 := by
  set σ : Equiv.Perm (Fin n) :=
    ((yuTheta Y φ ⟨x, hxY⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) with hσ
  have hT : ∀ u : ↥(commV Y), (u : V) ∈ commV (Subgroup.zpowers x) →
      psiC hV ψ u ∈ movedSumZero σ := by
    intro u huC
    refine ⟨fun j hj => ?_, hsum ⟨yuInc Y u, yuInc_mem_shortU Y hV u⟩⟩
    let π : Multiplicative (Fin n → ZMod 2) →* Multiplicative (ZMod 2) :=
      AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin n => ZMod 2) j)
    have hf : ∀ u' : ↥(commV Y), (π.comp (psiC hV ψ))
        ⟨x u', apply_mem_commV_self Y hxY u'.2⟩ = (π.comp (psiC hV ψ)) u' := by
      intro u'
      have hu1 : yuInc Y u' ∈ shortU ↥(yuHol Y) := yuInc_mem_shortU Y hV u'
      have hu2 : yuSec Y ⟨x, hxY⟩ * yuInc Y u' * (yuSec Y ⟨x, hxY⟩)⁻¹ ∈
          shortU ↥(yuHol Y) := by
        rw [conj_yuInc]
        exact yuInc_mem_shortU Y hV _
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
        psiC_apply_smul hV ψ ⟨x, hxY⟩ u' hu2, heq _ _ hu1 hu2]
      show Multiplicative.ofAdd ((permActionTwo σ (Multiplicative.toAdd (ψ ⟨yuInc Y u', hu1⟩))) j) =
        Multiplicative.ofAdd (Multiplicative.toAdd (ψ ⟨yuInc Y u', hu1⟩) j)
      have : σ⁻¹ j = j := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hj.symm
      simp only [permActionTwo, this]
    have hN : ∀ n : Multiplicative (ZMod 2), n ^ 2 = 1 := fun n =>
      Multiplicative.toAdd.injective (by
        rw [toAdd_pow, toAdd_one]
        have : ∀ a : ZMod 2, 2 • a = 0 := by decide
        exact this _)
    have h := trivial_of_invariant hxY hx5 hN (π.comp (psiC hV ψ)) hf huC u.2
    exact congrArg Multiplicative.toAdd h
  exact (card_commV_le_of_psiC hV ψ hker hxY hx5 (movedSumZero σ) hT).trans
    (card_movedSumZero_le σ hsupp)

end Alt

end CFSG.CGT.PushingUpLit.CGT6
