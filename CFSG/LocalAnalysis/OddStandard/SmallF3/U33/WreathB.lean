module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathModel

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Open

variable {G : Type*} [Group G] {x₁ x₂ lam : G}

private abbrev wmodDecEq : DecidableEq WMod := WMod.equivProd.decidableEq

attribute [local instance 2000] wmodDecEq

private instance : Fintype WMod :=
  Fintype.ofEquiv (Fin 4 × Fin 4 × Fin 2) WMod.equivProd.symm

private abbrev wy : WMod := WMod.wx₁ ^ 2

private abbrev wz : WMod := (WMod.wx₁ * WMod.wx₂) ^ 2

private def projI : WMod →* Multiplicative (Fin 2) where
  toFun m := Multiplicative.ofAdd m.i
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma mem_projI_ker (m : WMod) : m ∈ projI.ker ↔ m.i = 0 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h; exact Multiplicative.ofAdd.injective h
  · intro h; show Multiplicative.ofAdd m.i = 1; rw [h]; rfl

private lemma model_baseGrp_eq : baseGrp WMod.wx₁ WMod.wx₂ = projI.ker := by
  apply le_antisymm
  · rw [baseGrp, Subgroup.closure_le]
    rintro x (hx : x ∈ ({WMod.wx₁, WMod.wx₂} : Set WMod))
    change x ∈ projI.ker
    rw [mem_projI_ker]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> decide
  · rintro ⟨a, b, i⟩ hx
    rw [mem_projI_ker] at hx
    have hi : i = 0 := hx
    subst hi
    rw [WMod.eq_pow_mul (⟨a, b, 0⟩ : WMod),
      show (⟨a, b, 0⟩ : WMod).i.val = 0 from rfl, pow_zero, mul_one]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

private lemma mem_baseGrp_iff (m : WMod) :
    m ∈ baseGrp WMod.wx₁ WMod.wx₂ ↔ m.i = 0 := by
  rw [model_baseGrp_eq]
  exact mem_projI_ker m

private lemma wy_mem_base : wy ∈ baseGrp WMod.wx₁ WMod.wx₂ :=
  pow_mem (Subgroup.subset_closure (by simp)) 2

private lemma wz_mem_base : wz ∈ baseGrp WMod.wx₁ WMod.wx₂ :=
  pow_mem (mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) 2

private lemma wy_sq : wy ^ 2 = 1 := by decide +kernel

private lemma wz_sq : wz ^ 2 = 1 := by decide +kernel

private lemma wy_mul_wz_sq : (wy * wz) ^ 2 = 1 := by decide +kernel

private lemma model_sq_one_even : ∀ (a b : Fin 4),
    (⟨a, b, 0⟩ : WMod) ^ 2 = 1 → a.val % 2 = 0 ∧ b.val % 2 = 0 := by
  decide +kernel

private lemma model_repr_even : ∀ (a b : Fin 4), a.val % 2 = 0 → b.val % 2 = 0 →
    (⟨a, b, 0⟩ : WMod) = 1 ∨ (⟨a, b, 0⟩ : WMod) = wy ∨ (⟨a, b, 0⟩ : WMod) = wz ∨
      (⟨a, b, 0⟩ : WMod) = wy * wz := by
  decide +kernel

private lemma model_sq_eq : ∀ (p q : Fin 4),
    (⟨p, q, 0⟩ : WMod) ^ 2 = (⟨p + p, q + q, 0⟩ : WMod) := by decide +kernel

private lemma model_add_self_even : ∀ p : Fin 4, (p + p).val % 2 = 0 := by decide +kernel

private lemma model_repr_even_mem : ∀ (a b : Fin 4), a.val % 2 = 0 → b.val % 2 = 0 →
    (⟨a, b, 0⟩ : WMod) ∈ fourGrp WMod.wx₁ WMod.wx₂ := by
  intro a b ha hb
  rcases model_repr_even a b ha hb with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact Subgroup.subset_closure (by simp [wy])
  · rw [h]; exact Subgroup.subset_closure (by simp [wz])
  · rw [h]; exact mul_mem (Subgroup.subset_closure (by simp [wy]))
      (Subgroup.subset_closure (by simp [wz]))

private lemma model_fourGrp_eq_omega :
    fourGrp WMod.wx₁ WMod.wx₂ =
      closure {m : WMod | m ∈ baseGrp WMod.wx₁ WMod.wx₂ ∧ m ^ 2 = 1} := by
  apply le_antisymm
  · rw [fourGrp, Subgroup.closure_le]
    rintro g (hg : g ∈ ({wy, wz} : Set WMod))
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure ⟨wy_mem_base, wy_sq⟩
    · exact Subgroup.subset_closure ⟨wz_mem_base, wz_sq⟩
  · rw [Subgroup.closure_le]
    rintro m ⟨hmb, hm2⟩
    obtain ⟨a, b, i⟩ := m
    have hi : i = 0 := (mem_baseGrp_iff ⟨a, b, i⟩).mp hmb
    subst hi
    exact model_repr_even_mem a b (model_sq_one_even a b hm2).1
      (model_sq_one_even a b hm2).2

private lemma model_sq_memF : ∀ p q : Fin 4,
    (⟨p, q, 0⟩ : WMod) ^ 2 ∈ fourGrp WMod.wx₁ WMod.wx₂ := by
  intro p q
  rw [model_sq_eq p q]
  exact model_repr_even_mem (p + p) (q + q) (model_add_self_even p) (model_add_self_even q)

private lemma model_fourGrp_eq_mho :
    fourGrp WMod.wx₁ WMod.wx₂ =
      closure {m : WMod | ∃ a ∈ baseGrp WMod.wx₁ WMod.wx₂, m = a ^ 2} := by
  apply le_antisymm
  · rw [fourGrp, Subgroup.closure_le]
    rintro g (hg : g ∈ ({wy, wz} : Set WMod))
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure ⟨WMod.wx₁, Subgroup.subset_closure (by simp), rfl⟩
    · exact Subgroup.subset_closure ⟨WMod.wx₁ * WMod.wx₂,
        mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)), rfl⟩
  · rw [Subgroup.closure_le]
    rintro m ⟨a, ha, rfl⟩
    obtain ⟨p, q, i⟩ := a
    have hi : i = 0 := (mem_baseGrp_iff ⟨p, q, i⟩).mp ha
    subst hi
    exact model_sq_memF p q

private abbrev Q (m : WMod) : Prop := m.i = 0 ∧ m.a.val % 2 = 0 ∧ m.b.val % 2 = 0

private lemma Q_mul : ∀ (a b : Fin 4) (i : Fin 2) (c d : Fin 4) (k : Fin 2),
    Q ⟨a, b, i⟩ → Q ⟨c, d, k⟩ → Q (⟨a, b, i⟩ * ⟨c, d, k⟩) := by
  decide +kernel

private lemma Q_inv : ∀ (a b : Fin 4) (i : Fin 2),
    Q ⟨a, b, i⟩ → Q (⟨a, b, i⟩ : WMod)⁻¹ := by
  decide +kernel

private abbrev fourSub : Subgroup WMod where
  carrier := {m | Q m}
  one_mem' := by decide +kernel
  mul_mem' := by
    rintro x y hx hy
    obtain ⟨a, b, i⟩ := x
    obtain ⟨c, d, k⟩ := y
    exact Q_mul a b i c d k hx hy
  inv_mem' := by
    rintro x hx
    obtain ⟨a, b, i⟩ := x
    exact Q_inv a b i hx

private instance : DecidablePred (· ∈ fourSub) := fun m => inferInstanceAs (Decidable (Q m))

private lemma model_omega_eq :
    {m : WMod | m ∈ baseGrp WMod.wx₁ WMod.wx₂ ∧ m ^ 2 = 1} = (fourSub : Set WMod) := by
  ext m
  constructor
  · rintro ⟨hmb, hm2⟩
    obtain ⟨a, b, i⟩ := m
    have hi : i = 0 := (mem_baseGrp_iff ⟨a, b, i⟩).mp hmb
    have hpar : a.val % 2 = 0 ∧ b.val % 2 = 0 := by
      rw [hi] at hm2
      exact model_sq_one_even a b hm2
    exact ⟨hi, hpar.1, hpar.2⟩
  · rintro hm
    obtain ⟨a, b, i⟩ := m
    obtain ⟨hi, ha, hb⟩ := hm
    subst hi
    refine ⟨(mem_baseGrp_iff _).mpr rfl, ?_⟩
    rcases model_repr_even a b ha hb with h | h | h | h
    · rw [h]; rfl
    · rw [h]; exact wy_sq
    · rw [h]; exact wz_sq
    · rw [h]; exact wy_mul_wz_sq

private lemma model_card_fourSub : Nat.card fourSub = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private lemma model_omega_ncard :
    {m : WMod | m ∈ baseGrp WMod.wx₁ WMod.wx₂ ∧ m ^ 2 = 1}.ncard = 4 := by
  rw [model_omega_eq, ← Nat.card_coe_set_eq]
  exact model_card_fourSub

private lemma model_fourGrp_eq_fourSub :
    fourGrp WMod.wx₁ WMod.wx₂ = fourSub := by
  rw [model_fourGrp_eq_omega, model_omega_eq]
  exact le_antisymm ((Subgroup.closure_le fourSub).mpr (le_refl _))
    Subgroup.subset_closure

private lemma model_card_fourGrp : Nat.card (fourGrp WMod.wx₁ WMod.wx₂) = 4 := by
  rw [model_fourGrp_eq_fourSub]
  exact model_card_fourSub

private lemma four_comm :
    ∀ x ∈ fourGrp WMod.wx₁ WMod.wx₂, ∀ y ∈ fourGrp WMod.wx₁ WMod.wx₂, Commute x y := by
  intro x hx y hy
  change x ∈ closure ({WMod.wx₁ ^ 2, (WMod.wx₁ * WMod.wx₂) ^ 2} : Set WMod) at hx
  change y ∈ closure ({WMod.wx₁ ^ 2, (WMod.wx₁ * WMod.wx₂) ^ 2} : Set WMod) at hy
  refine Subgroup.closure_induction₂
    (k := ({WMod.wx₁ ^ 2, (WMod.wx₁ * WMod.wx₂) ^ 2} : Set WMod))
    (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · show wy * wz = wz * wy; decide +kernel
    · show wz * wy = wy * wz; decide +kernel
    · exact Commute.refl _
  · intro x _; exact Commute.one_left x
  · intro x _; exact Commute.one_right x
  · intro x y z _ _ _ h1 h2; exact h1.mul_left h2
  · intro y z x _ _ _ h1 h2; exact h1.mul_right h2
  · intro x y _ _ h; exact Commute.inv_left_iff.mpr h
  · intro x y _ _ h; exact Commute.inv_right_iff.mpr h

private lemma four_sq_one :
    ∀ x ∈ fourGrp WMod.wx₁ WMod.wx₂, x ^ 2 = 1 := by
  intro x hx
  change x ∈ closure ({WMod.wx₁ ^ 2, (WMod.wx₁ * WMod.wx₂) ^ 2} : Set WMod) at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> decide +kernel
  | one => decide +kernel
  | mul x y hx hy ihx ihy => rw [(four_comm x hx y hy).mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

private lemma model_isElemAbelian : IsElemAbelian 2 (fourGrp WMod.wx₁ WMod.wx₂) :=
  ⟨IsMulCommutative.of_setLike_mul_comm (fun a ha b hb => four_comm a ha b hb),
    four_sq_one⟩

private lemma model_centralizer_count :
    ∀ a b : Fin 4,
      (Finset.univ.filter (fun m : WMod =>
        m ^ 2 = 1 ∧ m * (⟨a, b, 1⟩ : WMod) = (⟨a, b, 1⟩ : WMod) * m)).card ≤ 4 := by
  decide +kernel

private lemma model_centralizer_involutions_ncard (a b : Fin 4) :
    {m : WMod | m ^ 2 = 1 ∧ Commute m (⟨a, b, 1⟩ : WMod)}.ncard ≤ 4 := by
  have h : {m : WMod | m ^ 2 = 1 ∧ Commute m (⟨a, b, 1⟩ : WMod)} =
      {m : WMod | m ^ 2 = 1 ∧ m * (⟨a, b, 1⟩ : WMod) = (⟨a, b, 1⟩ : WMod) * m} := rfl
  rw [h, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact model_centralizer_count a b

private lemma model_centralizer_involutions_ncard' (m₀ : WMod) (hi : m₀.i = 1) :
    {m : WMod | m ^ 2 = 1 ∧ Commute m m₀}.ncard ≤ 4 := by
  obtain ⟨a, b, i⟩ := m₀
  have hi' : i = 1 := hi
  subst hi'
  exact model_centralizer_involutions_ncard a b

private lemma image_baseGrp (φ : WMod →* G) (h1 : φ WMod.wx₁ = x₁) (h2 : φ WMod.wx₂ = x₂) :
    (baseGrp WMod.wx₁ WMod.wx₂).map φ = baseGrp x₁ x₂ := by
  rw [baseGrp, baseGrp, MonoidHom.map_closure, Set.image_pair, h1, h2]

private lemma map_wy (φ : WMod →* G) (h1 : φ WMod.wx₁ = x₁) : φ wy = x₁ ^ 2 := by
  rw [wy, map_pow, h1]

private lemma map_wz (φ : WMod →* G) (h1 : φ WMod.wx₁ = x₁) (h2 : φ WMod.wx₂ = x₂) :
    φ wz = (x₁ * x₂) ^ 2 := by
  rw [wz, map_pow, map_mul, h1, h2]

private lemma image_fourGrp (φ : WMod →* G) (h1 : φ WMod.wx₁ = x₁) (h2 : φ WMod.wx₂ = x₂) :
    (fourGrp WMod.wx₁ WMod.wx₂).map φ = fourGrp x₁ x₂ := by
  rw [fourGrp, fourGrp, MonoidHom.map_closure, Set.image_pair, map_wy φ h1, map_wz φ h1 h2]

private lemma isElemAbelian_map {H : Subgroup WMod} (hH : IsElemAbelian 2 H)
    (φ : WMod →* G) : IsElemAbelian 2 (H.map φ) := by
  haveI : IsMulCommutative H := hH.1
  refine ⟨inferInstance, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  rw [← map_pow, hH.2 y hy, map_one]

private lemma isElemAbelian_comap {H : Subgroup G} (hH : IsElemAbelian 2 H)
    (φ : WMod →* G) (hinj : Function.Injective φ) : IsElemAbelian 2 (H.comap φ) := by
  haveI : IsMulCommutative H := hH.1
  refine ⟨Subgroup.comap_injective_isMulCommutative H hinj, ?_⟩
  intro x hx
  apply hinj
  rw [map_pow, map_one]
  exact hH.2 (φ x) hx

theorem WreathRel.x₂_sq (h : WreathRel x₁ x₂ lam) : x₂ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  have h4 : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [h.ord_x₁] at this
  have hc : Commute x₁ x₂ := h.comm
  rw [hc.mul_pow, ← mul_assoc, ← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h4, one_mul]

theorem WreathRel.fourGrp_eq_omega (h : WreathRel x₁ x₂ lam) :
    fourGrp x₁ x₂ = closure {a : G | a ∈ baseGrp x₁ x₂ ∧ a ^ 2 = 1} ∧
      IsElemAbelian 2 (fourGrp x₁ x₂) ∧ Nat.card (fourGrp x₁ x₂) = 4 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3⟩ := h.exists_embedding
  have hmap := image_fourGrp φ h1 h2
  have hbmap := image_baseGrp φ h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmap, model_fourGrp_eq_omega, MonoidHom.map_closure]
    congr 1
    ext a
    constructor
    · rintro ⟨m, ⟨hmb, hm2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hbmap]; exact ⟨m, hmb, rfl⟩
      · rw [← map_pow, hm2, map_one]
    · rintro ⟨ha, ha2⟩
      rw [← hbmap] at ha
      obtain ⟨m, hmb, rfl⟩ := ha
      refine ⟨m, ⟨hmb, ?_⟩, rfl⟩
      apply hinj
      rw [map_pow, ha2, map_one]
  · rw [← hmap]
    exact isElemAbelian_map model_isElemAbelian φ
  · rw [← hmap, Subgroup.card_map_of_injective hinj, model_card_fourGrp]

theorem WreathRel.fourGrp_eq_mho (h : WreathRel x₁ x₂ lam) :
    fourGrp x₁ x₂ = closure {g : G | ∃ a ∈ baseGrp x₁ x₂, g = a ^ 2} := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3⟩ := h.exists_embedding
  have hbmap := image_baseGrp φ h1 h2
  rw [← image_fourGrp φ h1 h2, model_fourGrp_eq_mho, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨m, ⟨a, ha, hm⟩, rfl⟩
    refine ⟨φ a, ?_, ?_⟩
    · rw [← hbmap]; exact ⟨a, ha, rfl⟩
    · rw [hm, map_pow]
  · rintro ⟨b, hb, rfl⟩
    rw [← hbmap] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨a ^ 2, ⟨a, ha, rfl⟩, map_pow φ a 2⟩

theorem WreathRel.pRank_eq_two [Finite G] (h : WreathRel x₁ x₂ lam) :
    CFSG.Open.pRank 2 (wreathGrp x₁ x₂ lam) = 2 := by
  obtain ⟨φ, hinj, hrange, h1, h2, h3⟩ := h.exists_embedding
  show sSup {k | ∃ E : Subgroup G, E ≤ wreathGrp x₁ x₂ lam ∧ IsElemAbelian 2 E ∧
    Nat.card E = 2 ^ k} = 2
  refine IsGreatest.csSup_eq ⟨?_, ?_⟩
  · refine ⟨fourGrp x₁ x₂, ?_, (WreathRel.fourGrp_eq_omega h).2.1, ?_⟩
    · rw [fourGrp, Subgroup.closure_le]
      rintro g (hg : g ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
      rcases hg with rfl | rfl
      · rw [wreathGrp]
        exact pow_mem (Subgroup.subset_closure (by simp)) 2
      · rw [wreathGrp]
        exact pow_mem (mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))) 2
    · rw [(WreathRel.fourGrp_eq_omega h).2.2]; norm_num
  · rintro k ⟨E, hE_T, hE_ab, hE_card⟩
    set E' : Subgroup WMod := E.comap φ with hE'def
    have hE'_map : E'.map φ = E := by
      rw [hE'def]
      exact Subgroup.map_comap_eq_self (by rw [hrange]; exact hE_T)
    have hE'_card : Nat.card E' = Nat.card E := by
      have h := Subgroup.card_map_of_injective (K := E') hinj
      rw [hE'_map] at h
      exact h.symm
    have hE'_ab : IsElemAbelian 2 E' := by
      rw [hE'def]
      exact isElemAbelian_comap hE_ab φ hinj
    haveI : IsMulCommutative E' := hE'_ab.1
    have h4 : Nat.card E' ≤ 4 := by
      by_cases hcase : E' ≤ baseGrp WMod.wx₁ WMod.wx₂
      · have hsub : (E' : Set WMod) ⊆
            {m : WMod | m ∈ baseGrp WMod.wx₁ WMod.wx₂ ∧ m ^ 2 = 1} :=
          fun m hm => ⟨hcase hm, hE'_ab.2 m hm⟩
        calc Nat.card E' = (E' : Set WMod).ncard := Nat.card_coe_set_eq (E' : Set WMod)
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = 4 := model_omega_ncard
      · have hcase' : ¬ (E' : Set WMod) ⊆ (baseGrp WMod.wx₁ WMod.wx₂ : Set WMod) := hcase
        obtain ⟨m₀, hm₀E', hm₀not⟩ := Set.not_subset.mp hcase'
        obtain ⟨a, b, i⟩ := m₀
        have hi : (⟨a, b, i⟩ : WMod).i = 1 := by
          have hne : (⟨a, b, i⟩ : WMod).i ≠ 0 := fun h0 =>
            hm₀not ((mem_baseGrp_iff ⟨a, b, i⟩).mpr h0)
          fin_cases i <;> simp_all
        have hsub : (E' : Set WMod) ⊆
            {m : WMod | m ^ 2 = 1 ∧ Commute m (⟨a, b, i⟩ : WMod)} :=
          fun m hm => ⟨hE'_ab.2 m hm, setLike_mul_comm hm hm₀E'⟩
        calc Nat.card E' = (E' : Set WMod).ncard := Nat.card_coe_set_eq (E' : Set WMod)
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ ≤ 4 := model_centralizer_involutions_ncard' ⟨a, b, i⟩ hi
    have hk : 2 ^ k ≤ 2 ^ 2 := by
      rw [← hE_card, ← hE'_card]
      simpa using h4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hk

end CFSG.OddStandard.SmallF3.HarrisU33
