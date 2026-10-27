module

public import CFSG.CGT.PushingUpLit.BHS.FourSymA
public import CFSG.CGT.PushingUpLit.BHSSym.Delta
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHSSym CFSG.Permutation

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

namespace ModId

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_two_val_one : (1 : ZMod 2).val = 1 := rfl

theorem pow_mod_two_of_sq {G : Type*} [Group G] {g : G} (hg : g ^ 2 = 1) (m : ℕ) :
    g ^ (m % 2) = g ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, hg, one_pow, one_mul]

@[expose] def cartanHom (k : ℕ) : (Fin k → ZMod 2) →+ (Fin k → ZMod 2) where
  toFun c i := ∑ j : Fin k, if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then c j else 0
  map_zero' := by
    funext i
    simp
  map_add' c c' := by
    funext i
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp

theorem cartanHom_single (k : ℕ) (i j : Fin k) :
    cartanHom k (Pi.single j 1) i = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 := by
  show (∑ j' : Fin k, if (i : ℕ) + 1 = j' ∨ (j' : ℕ) + 1 = i then
    (Pi.single j 1 : Fin k → ZMod 2) j' else 0) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

theorem cartanHom_bijective {k : ℕ} (hk : Even k) : Function.Bijective (cartanHom k) := by
  have hinj : Function.Injective (cartanHom k) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact cartan_inj hk c fun i => congrFun hc i
  exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩

theorem map_eq_prod_single {k : ℕ} {G : Type*} [CommGroup G]
    (f : Multiplicative (Fin k → ZMod 2) →* G) (c : Multiplicative (Fin k → ZMod 2)) :
    f c = ∏ j : Fin k,
      f (Multiplicative.ofAdd (Pi.single j 1)) ^ (Multiplicative.toAdd c j).val := by
  have hc : c = ∏ j : Fin k, (Multiplicative.ofAdd (Pi.single j 1 : Fin k → ZMod 2)) ^
      (Multiplicative.toAdd c j).val := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext m
    simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
      smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Nat.smul_one_eq_cast,
      ZMod.natCast_zmod_val]
  conv_lhs => rw [hc]
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [map_pow]

theorem hom_ext_single {k : ℕ} {G : Type*} [CommGroup G]
    {f g : Multiplicative (Fin k → ZMod 2) →* G}
    (h : ∀ j : Fin k, f (Multiplicative.ofAdd (Pi.single j 1)) =
      g (Multiplicative.ofAdd (Pi.single j 1))) : f = g := by
  refine MonoidHom.ext fun c => ?_
  rw [map_eq_prod_single f c, map_eq_prod_single g c]
  exact Finset.prod_congr rfl fun j _ => by rw [h j]

@[expose] def chainHom {V : Type} [CommGroup V] {k : ℕ} (u : Fin k → V) (hu : ∀ j, u j ^ 2 = 1) :
    Multiplicative (Fin k → ZMod 2) →* V where
  toFun c := ∏ j, u j ^ (Multiplicative.toAdd c j).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, pow_mod_two_of_sq (hu j), pow_add]

section Chain

variable {V : Type} [CommGroup V] {k : ℕ} (u : Fin k → V) (hu : ∀ j, u j ^ 2 = 1)

theorem chainHom_single (j : Fin k) :
    chainHom u hu (Multiplicative.ofAdd (Pi.single j 1)) = u j := by
  show ∏ j', u j' ^
    (Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single j 1 : Fin k → ZMod 2)) j').val = u j
  rw [Finset.prod_eq_single j]
  · simp [zmod_two_val_one]
  · intro j' _ hj'
    simp [hj']
  · simp

theorem chainHom_smul_single (i : Fin k) (a : ZMod 2) :
    chainHom u hu (Multiplicative.ofAdd (a • (Pi.single i 1 : Fin k → ZMod 2))) = u i ^ a.val := by
  rcases zmod_two_cases a with rfl | rfl
  · simp
  · rw [one_smul, chainHom_single, zmod_two_val_one, pow_one]

@[expose] def reflHom (k : ℕ) (i : Fin k) :
    Multiplicative (Fin k → ZMod 2) →* Multiplicative (Fin k → ZMod 2) where
  toFun c := c * Multiplicative.ofAdd
    (cartanHom k (Multiplicative.toAdd c) i • (Pi.single i 1 : Fin k → ZMod 2))
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, map_add, Pi.add_apply, add_smul, ofAdd_add]
    exact mul_mul_mul_comm _ _ _ _

theorem reflHom_apply (k : ℕ) (i : Fin k) (c : Multiplicative (Fin k → ZMod 2)) :
    reflHom k i c = c * Multiplicative.ofAdd
      (cartanHom k (Multiplicative.toAdd c) i • (Pi.single i 1 : Fin k → ZMod 2)) := rfl

theorem reflHom_single (k : ℕ) (i j : Fin k) :
    reflHom k i (Multiplicative.ofAdd (Pi.single j 1 : Fin k → ZMod 2)) =
      Multiplicative.ofAdd (Pi.single j 1 : Fin k → ZMod 2) *
      Multiplicative.ofAdd ((if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 : ZMod 2) •
        (Pi.single i 1 : Fin k → ZMod 2)) := by
  rw [reflHom_apply, toAdd_ofAdd, cartanHom_single]

theorem chainHom_reflHom (i : Fin k) (c : Multiplicative (Fin k → ZMod 2)) :
    chainHom u hu (reflHom k i c) =
      chainHom u hu c * u i ^ (cartanHom k (Multiplicative.toAdd c) i).val := by
  rw [reflHom_apply, map_mul, chainHom_smul_single]

end Chain

section Action

variable {V : Type} [CommGroup V] {k : ℕ}

theorem chain_apply_centre (x : ℕ → MulAut V) (u : ℕ → V)
    (hadj : ∀ i, i + 1 < k →
      x i (u (i + 1)) = u (i + 1) * u i ∧ x (i + 1) (u i) = u i * u (i + 1))
    (hfar : ∀ i j, i < k → j < k → j ≠ i + 1 → i ≠ j + 1 → x i (u j) = u j) (i j : Fin k) :
    x i (u j) = u j * (if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then u i else 1) := by
  by_cases h1 : (i : ℕ) + 1 = j
  · rw [ite_eq_left (Or.inl h1), ← h1]
    exact (hadj i (by omega)).1
  · by_cases h2 : (j : ℕ) + 1 = i
    · rw [ite_eq_left (Or.inr h2)]
      have e := (hadj j (by omega)).2
      rw [h2] at e
      exact e
    · rw [ite_eq_right (by tauto), mul_one]
      exact hfar i j i.2 j.2 (fun h => h1 h.symm) (fun h => h2 h.symm)

theorem chain_action (x : ℕ → MulAut V) (u : ℕ → V) (hu' : ∀ j : Fin k, u j ^ 2 = 1)
    (hadj : ∀ i, i + 1 < k →
      x i (u (i + 1)) = u (i + 1) * u i ∧ x (i + 1) (u i) = u i * u (i + 1))
    (hfar : ∀ i j, i < k → j < k → j ≠ i + 1 → i ≠ j + 1 → x i (u j) = u j) (i : Fin k)
    (c : Multiplicative (Fin k → ZMod 2)) :
    x i (chainHom (fun j : Fin k => u j) hu' c) =
      chainHom (fun j : Fin k => u j) hu' (reflHom k i c) := by
  have h : ((x i).toMonoidHom.comp (chainHom (fun j : Fin k => u j) hu')) =
      (chainHom (fun j : Fin k => u j) hu').comp (reflHom k i) := by
    refine hom_ext_single fun j => ?_
    change x i (chainHom (fun j : Fin k => u j) hu' (Multiplicative.ofAdd (Pi.single j 1))) =
      chainHom (fun j : Fin k => u j) hu' (reflHom k i (Multiplicative.ofAdd (Pi.single j 1)))
    rw [chainHom_single, reflHom_single, map_mul, chainHom_single, chainHom_smul_single,
      chain_apply_centre x u hadj hfar]
    split_ifs <;> simp [zmod_two_val_one]
  exact DFunLike.congr_fun h c

end Action

theorem rootBasis_reflHom (k : ℕ) (i : Fin k) (c : Multiplicative (Fin k → ZMod 2)) :
    rootBasis k (reflHom k i c) =
      coreAct (k + 1) (SymmetricCoxeter.adjSwap k i) (rootBasis k c) := by
  have hσ : SymmetricCoxeter.adjSwap k i = Equiv.swap i.castSucc i.succ :=
    SymmetricCoxeter.adjSwap_of_lt i.2
  have h : ((rootBasis k).toMonoidHom.comp (reflHom k i)) =
      ((coreAct (k + 1) (SymmetricCoxeter.adjSwap k i)).toMonoidHom.comp
        (rootBasis k).toMonoidHom) := by
    refine hom_ext_single fun j => ?_
    change rootBasis k (reflHom k i (Multiplicative.ofAdd (Pi.single j 1))) =
      coreAct (k + 1) (SymmetricCoxeter.adjSwap k i) (rootBasis k (Multiplicative.ofAdd
        (Pi.single j 1)))
    rw [reflHom_single, map_mul, rootBasis_single, coreAct_rootVec, hσ]
    by_cases h1 : (i : ℕ) + 1 = j
    · rw [ite_eq_left (Or.inl h1), one_smul, rootBasis_single]
      have e1 : j.castSucc = i.succ := Fin.ext (by simp; omega)
      have e2 : Equiv.swap i.castSucc i.succ j.succ = j.succ :=
        Equiv.swap_apply_of_ne_of_ne
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
      rw [e1, Equiv.swap_apply_right, e2, mul_comm, rootVec_mul]
    · by_cases h2 : (j : ℕ) + 1 = i
      · rw [ite_eq_left (Or.inr h2), one_smul, rootBasis_single]
        have e1 : j.succ = i.castSucc := Fin.ext (by simp; omega)
        have e2 : Equiv.swap i.castSucc i.succ j.castSucc = j.castSucc :=
          Equiv.swap_apply_of_ne_of_ne
            (fun h => by have := congrArg Fin.val h; simp at this; omega)
            (fun h => by have := congrArg Fin.val h; simp at this; omega)
        rw [e1, Equiv.swap_apply_left, e2, rootVec_mul]
      · rw [ite_eq_right (by tauto), zero_smul, ofAdd_zero, map_one, mul_one]
        by_cases h3 : j = i
        · subst h3
          rw [Equiv.swap_apply_left, Equiv.swap_apply_right, rootVec_comm]
        · rw [Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_of_ne_of_ne]
          · exact fun h => by have := congrArg Fin.val h; simp at this; omega
          · exact fun h => by have := congrArg Fin.val h; simp at this; omega
          · exact fun h => by have := congrArg Fin.val h; simp at this; omega
          · exact fun h => by have := congrArg Fin.val h; simp at this; omega
  exact DFunLike.congr_fun h c

theorem mem_fixV_closure_of_forall {V : Type*} [CommGroup V] {S : Set (MulAut V)} {v : V}
    (h : ∀ s ∈ S, s v = v) : v ∈ fixV (Subgroup.closure S) := by
  rw [mem_fixV]
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => rfl
  | mul a b _ _ iha ihb =>
    show a (b v) = v
    rw [ihb, iha]
  | inv a _ iha =>
    calc a⁻¹ v = a⁻¹ (a v) := by rw [iha]
      _ = v := by simp

end ModId

open ModId

theorem exists_module_identification {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) (x : ℕ → MulAut V) (u : ℕ → V)
    (hx : ∀ i < k, IsTransv (x i) (u i))
    (hadj : ∀ i, i + 1 < k → x i (u (i + 1)) = u (i + 1) * u i ∧ x (i + 1) (u i) = u i * u (i + 1))
    (hfar : ∀ i j, i < k → j < k → j ≠ i + 1 → i ≠ j + 1 → x i (u j) = u j)
    {E : Subgroup (MulAut V)} (hE : Subgroup.closure (x '' Set.Iio k) = E) :
    ∃ β : ↥(commV E) →* coreMod (k + 1),
      (∀ g ∈ E, ∀ p ∈ commV E, g p ∈ commV E) ∧ Function.Surjective β ∧ β.ker = ⊥ ∧
      (∀ (i : ℕ) (_hi : i < k) (p : ↥(commV E)) (hp : x i p ∈ commV E),
        β ⟨x i p, hp⟩ = coreAct (k + 1) (SymmetricCoxeter.adjSwap k i) (β p)) ∧
      commV E ⊔ fixV E = ⊤ := by
  have _ := hk2
  classical
  have hu2 : ∀ j : Fin k, u j ^ 2 = 1 := fun j => hV _
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Multiplicative (Fin k → ZMod 2) →* V,
      Θ = chainHom (fun j : Fin k => u j) hu2 := ⟨_, rfl⟩
  have hsingle : ∀ j : Fin k, Θ (Multiplicative.ofAdd (Pi.single j 1)) = u j := by
    subst hΘ
    exact fun j => chainHom_single _ hu2 j
  have hrefl : ∀ (i : Fin k) (c : Multiplicative (Fin k → ZMod 2)),
      Θ (reflHom k i c) = Θ c * u i ^ (cartanHom k (Multiplicative.toAdd c) i).val := by
    subst hΘ
    exact fun i c => chainHom_reflHom _ hu2 i c
  have hact : ∀ (i : Fin k) (c : Multiplicative (Fin k → ZMod 2)),
      x i (Θ c) = Θ (reflHom k i c) := by
    subst hΘ
    exact fun i c => chain_action x u hu2 hadj hfar i c
  have hprod : ∀ c : Multiplicative (Fin k → ZMod 2),
      Θ c = ∏ j : Fin k, u j ^ (Multiplicative.toAdd c j).val := by
    subst hΘ
    exact fun c => rfl
  have hxE : ∀ i : Fin k, x i ∈ E := fun i => by
    rw [← hE]
    exact Subgroup.subset_closure ⟨i, i.2, rfl⟩
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hN : ∀ i : Fin k, cartanHom k (Multiplicative.toAdd c) i = 0 := by
      intro i
      have h1 : Θ (reflHom k i c) = 1 := by rw [← hact, hc, map_one]
      rw [hrefl, hc, one_mul] at h1
      rcases zmod_two_cases (cartanHom k (Multiplicative.toAdd c) i) with h | h
      · exact h
      · exfalso
        rw [h, zmod_two_val_one, pow_one] at h1
        exact (hx i i.2).ne h1
    have hc0 : Multiplicative.toAdd c = 0 :=
      (cartanHom_bijective hk).1 (by rw [map_zero]; exact funext hN)
    rw [← ofAdd_toAdd c, hc0, ofAdd_zero]
  have hmemU : ∀ j : Fin k, u j ∈ commV E := by
    intro j
    obtain ⟨v, hv⟩ := (hx j j.2).exists_move
    have h1 := G6.mem_commV_of_mem (hxE j) v
    rw [hv, mul_comm v, mul_inv_cancel_right] at h1
    exact h1
  have hcomm : ∀ g ∈ E, ∀ v : V, g v * v⁻¹ ∈ Θ.range := by
    intro g hg
    rw [← hE] at hg
    induction hg using Subgroup.closure_induction with
    | mem g' hg' =>
      obtain ⟨i, hi, rfl⟩ := hg'
      intro v
      rcases (hx i hi).step_div v with h | h
      · rw [h]
        exact Θ.range.one_mem
      · rw [h]
        exact ⟨Multiplicative.ofAdd (Pi.single ⟨i, hi⟩ 1), hsingle ⟨i, hi⟩⟩
    | one =>
      intro v
      simp
    | mul a b _ _ iha ihb =>
      intro v
      have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
        show a (b v) * v⁻¹ = _
        comm_group
      rw [e]
      exact Θ.range.mul_mem (iha _) (ihb _)
    | inv a _ iha =>
      intro v
      have e : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
        have : a (a⁻¹ v) = v := by simp
        rw [this]
        comm_group
      rw [e]
      exact Θ.range.inv_mem (iha _)
  have hrange : commV E = Θ.range := by
    apply le_antisymm
    · rw [G6.commV_le_iff]
      exact hcomm
    · rintro _ ⟨c, rfl⟩
      rw [hprod]
      exact Subgroup.prod_mem _ fun j _ => Subgroup.pow_mem _ (hmemU j) _
  let θe : Multiplicative (Fin k → ZMod 2) ≃* ↥(commV E) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  refine ⟨(rootBasis k).toMonoidHom.comp θe.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg p hp
    have h1 : g p * p⁻¹ ∈ commV E := G6.mem_commV_of_mem hg p
    have h2 : g p = (g p * p⁻¹) * p := by rw [inv_mul_cancel_right]
    rw [h2]
    exact (commV E).mul_mem h1 hp
  · exact (rootBasis k).surjective.comp θe.symm.surjective
  · exact (MonoidHom.ker_eq_bot_iff _).2 ((rootBasis k).injective.comp θe.symm.injective)
  · intro i hi p hp
    obtain ⟨c, rfl⟩ := θe.surjective p
    have e1 : (⟨x i ((θe c : ↥(commV E)) : V), hp⟩ : ↥(commV E)) = θe (reflHom k ⟨i, hi⟩ c) :=
      Subtype.ext (hact ⟨i, hi⟩ c)
    change rootBasis k (θe.symm ⟨x i ((θe c : ↥(commV E)) : V), hp⟩) =
      coreAct (k + 1) (SymmetricCoxeter.adjSwap k i) (rootBasis k (θe.symm (θe c)))
    rw [e1, θe.symm_apply_apply, θe.symm_apply_apply]
    exact rootBasis_reflHom k ⟨i, hi⟩ c
  ·
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨c₀, hc₀⟩ := (cartanHom_bijective hk).2
      (fun i : Fin k => if x i v = v then (0 : ZMod 2) else 1)
    have hxv : ∀ i : Fin k, x i v = v * u i ^ (cartanHom k c₀ i).val := by
      intro i
      have hci : cartanHom k c₀ i = if x i v = v then 0 else 1 := congrFun hc₀ i
      rw [hci]
      by_cases h : x i v = v
      · simp [h]
      · rw [ite_eq_right h, zmod_two_val_one, pow_one]
        exact ((hx i i.2).step v).resolve_left h
    have hgen : ∀ i : Fin k, x i (v * (Θ (Multiplicative.ofAdd c₀))⁻¹) =
        v * (Θ (Multiplicative.ofAdd c₀))⁻¹ := by
      intro i
      have h1 : x i (Θ (Multiplicative.ofAdd c₀)) =
          Θ (Multiplicative.ofAdd c₀) * u i ^ (cartanHom k c₀ i).val := by
        rw [hact, hrefl, toAdd_ofAdd]
      rw [map_mul, map_inv, h1, hxv i]
      comm_group
    have hfix : v * (Θ (Multiplicative.ofAdd c₀))⁻¹ ∈ fixV E := by
      rw [← hE]
      exact mem_fixV_closure_of_forall fun s ⟨i, hi, hs⟩ => hs ▸ hgen ⟨i, hi⟩
    refine Subgroup.mem_sup.2 ⟨Θ (Multiplicative.ofAdd c₀), ?_, _, hfix, ?_⟩
    · rw [hrange]
      exact ⟨_, rfl⟩
    · comm_group

end CFSG.CGT.PushingUpLit.BHS
