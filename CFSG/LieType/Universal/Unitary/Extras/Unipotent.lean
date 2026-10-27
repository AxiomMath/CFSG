module

public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LieType.Steinberg.Extras
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

section Level

variable (s : Fin n → ℤ)

@[expose] def IdBelow (h : ℤ) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, s b - s a < h → M a b = (1 : Matrix (Fin n) (Fin n) F) a b

theorem idBelow_one (h : ℤ) : IdBelow s h (1 : Matrix (Fin n) (Fin n) F) :=
  fun _ _ _ => rfl

theorem mul_apply_of_idBelow {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n) (Fin n) F}
    (hM : IdBelow s h M) (hN : IdBelow s h N) {a b : Fin n} (hab : a ≠ b)
    (hlev : s b - s a ≤ h) : (M * N) a b = M a b + N a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM a a (by simpa using hh), hN b b (by simpa using hh)]
    simp [add_comm]
  · intro c _ ⟨hca, hcb⟩
    by_cases hc : s c - s a < h
    · rw [hM a c hc, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · rw [hN c b (by omega), Matrix.one_apply_ne hcb, mul_zero]
  · simp
  · simp

theorem idBelow_mul {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n) (Fin n) F}
    (hM : IdBelow s h M) (hN : IdBelow s h N) : IdBelow s h (M * N) := by
  intro a b hab
  by_cases hab' : a = b
  · subst hab'
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hM a a (by simpa using hh), hN a a (by simpa using hh)]
      simp
    · intro c _ hca
      by_cases hc : s c - s a < h
      · rw [hM a c hc, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
      · rw [hN c a (by omega), Matrix.one_apply_ne hca, mul_zero]
    · simp
  · rw [mul_apply_of_idBelow s hh hM hN hab' hab.le, hM a b hab, hN a b hab,
      Matrix.one_apply_ne hab', add_zero]

theorem IdBelow.mono {h h' : ℤ} {M : Matrix (Fin n) (Fin n) F} (hM : IdBelow s h M)
    (hh : h' ≤ h) : IdBelow s h' M := fun a b hab => hM a b (by omega)

end Level

abbrev lvl (sg : ℤ) (a : Fin n) : ℤ := sg * (a.val : ℤ)

variable (hσ : ∀ c, σ (σ c) = c)

theorem idBelow_of_mem_rootGroup {sg h : ℤ} {δ : Fin (n / 2) → ℤ} (hδh : h ≤ sg * ht δ)
    (hh : 0 < h) {x : SU σ n} (hx : x ∈ rootGroup σ hσ n δ) :
    IdBelow (lvl sg) h (mat σ n x) := by
  intro a b hab
  simp only [lvl] at hab
  apply mat_apply_of_mem_rootGroup hσ hx
  · intro hw
    have h1 := ht_eq_of_weight_sub hw
    have h2 : sg * (b.val : ℤ) - sg * a.val = sg * ht δ := by rw [h1]; ring
    linarith
  · intro hw
    have h1 := two_mul_ht_eq_of_weight_sub hw
    have h2 : sg * (b.val : ℤ) - sg * a.val = 2 * (sg * ht δ) := by rw [← mul_sub, ← h1]; ring
    linarith

@[expose] def QV (sg h : ℤ) (e : Fin (n / 2) → ℤ) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  IdBelow (lvl sg) h M ∧
    ∀ a b, (weight n a - weight n b = e ∨ weight n a - weight n b = 2 • e) → M a b = 0

section QV

variable {sg h : ℤ} {e : Fin (n / 2) → ℤ}

theorem mul_apply_of_qv (hsg : sg ≠ 0) (hh : 0 < h) (he : e ≠ 0)
    (hlev1 : ∀ a b : Fin n, weight n a - weight n b = e → lvl sg b - lvl sg a = h)
    (hlev2 : ∀ a b : Fin n, weight n a - weight n b = 2 • e → lvl sg b - lvl sg a = 2 * h)
    {X R : Matrix (Fin n) (Fin n) F} (hX : IdBelow (lvl sg) h X) (hR : QV sg h e R) (a b : Fin n)
    (hab : weight n a - weight n b = e ∨ weight n a - weight n b = 2 • e) :
    (X * R) a b = X a b := by
  rcases hab with hab | hab
  · have hne : a ≠ b := by
      rintro rfl
      exact he (by rw [← hab, sub_self])
    rw [mul_apply_of_idBelow (lvl sg) hh hX hR.1 hne (hlev1 a b hab).le, hR.2 a b (Or.inl hab),
      add_zero]
  · obtain ⟨rfl, hwa⟩ := eq_rev_of_weight_sub_eq_two_smul hab he
    have hlev := hlev2 a (Fin.rev a) hab
    have hne : a ≠ Fin.rev a := by
      intro h'
      rw [← h'] at hlev
      omega
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
    · rw [hR.1 _ _ (by simpa using hh), Matrix.one_apply_eq, mul_one]
    · intro c _ hc
      by_cases hca : c = a
      · rw [hca, hR.2 a (Fin.rev a) (Or.inr hab), mul_zero]
      by_cases hmid : Fin.rev c = c
      · have hw : weight n c - weight n (Fin.rev a) = e := by
          rw [weight_eq_zero_of_rev_eq hmid, weight_rev', hwa]
          abel
        rw [hR.2 c (Fin.rev a) (Or.inl hw), mul_zero]
      ·
        have hlv : lvl sg c - lvl sg a ≠ lvl sg (Fin.rev a) - lvl sg c := by
          intro h'
          apply hmid
          apply Fin.ext
          simp only [lvl, Fin.val_rev] at h'
          have h'' : sg * (2 * (c.val : ℤ) - (n - 1)) = 0 := by
            have := a.isLt
            have hc' : ((n - (a.val + 1) : ℕ) : ℤ) = (n : ℤ) - 1 - a.val := by omega
            rw [hc'] at h'
            linarith
          rcases mul_eq_zero.mp h'' with h3 | h3
          · exact absurd h3 hsg
          · simp only [Fin.val_rev]
            have := c.isLt
            omega
        by_cases h1 : lvl sg c - lvl sg a < h
        · rw [hX a c h1, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
        · have h2 : lvl sg (Fin.rev a) - lvl sg c < h := by omega
          rw [hR.1 c (Fin.rev a) h2, Matrix.one_apply_ne hc, mul_zero]
    · simp

theorem qv_one (he : e ≠ 0) : QV sg h e (1 : Matrix (Fin n) (Fin n) F) := by
  refine ⟨idBelow_one _ _, fun a b hab => Matrix.one_apply_ne ?_⟩
  rintro rfl
  rw [sub_self] at hab
  rcases hab with hab | hab
  · exact he hab.symm
  · exact he (by
      funext c
      have := congrFun hab c
      simp only [Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this ⊢
      omega)

theorem QV.mul (hsg : sg ≠ 0) (hh : 0 < h) (he : e ≠ 0)
    (hlev1 : ∀ a b : Fin n, weight n a - weight n b = e → lvl sg b - lvl sg a = h)
    (hlev2 : ∀ a b : Fin n, weight n a - weight n b = 2 • e → lvl sg b - lvl sg a = 2 * h)
    {M N : Matrix (Fin n) (Fin n) F} (hM : QV sg h e M) (hN : QV sg h e N) : QV sg h e (M * N) :=
  ⟨idBelow_mul _ hh hM.1 hN.1, fun a b hab => by
    rw [mul_apply_of_qv hsg hh he hlev1 hlev2 hM.1 hN a b hab, hM.2 a b hab]⟩

theorem qv_list_prod (hsg : sg ≠ 0) (hh : 0 < h) (he : e ≠ 0)
    (hlev1 : ∀ a b : Fin n, weight n a - weight n b = e → lvl sg b - lvl sg a = h)
    (hlev2 : ∀ a b : Fin n, weight n a - weight n b = 2 • e → lvl sg b - lvl sg a = 2 * h)
    (l : List (Matrix (Fin n) (Fin n) F)) (hl : ∀ M ∈ l, QV sg h e M) : QV sg h e l.prod := by
  induction l with
  | nil => exact qv_one he
  | cons M l ih =>
    rw [List.prod_cons]
    exact (hl M List.mem_cons_self).mul hsg hh he hlev1 hlev2
      (ih fun M' hM' => hl M' (List.mem_cons_of_mem _ hM'))

end QV

theorem qv_of_mem_rootGroup {sg h : ℤ} {γ δ : Fin (n / 2) → ℤ} (hh : 0 < h)
    (hδh : h ≤ sg * ht δ) (he : toStd n γ ≠ 0)
    (h1 : toStd n δ ≠ toStd n γ) (h2 : toStd n δ ≠ 2 • toStd n γ)
    (h3 : 2 • toStd n δ ≠ toStd n γ) (h4 : 2 • toStd n δ ≠ 2 • toStd n γ) {x : SU σ n}
    (hx : x ∈ rootGroup σ hσ n δ) : QV sg h (toStd n γ) (mat σ n x) := by
  refine ⟨idBelow_of_mem_rootGroup hσ hδh hh hx, fun a b hab => ?_⟩
  have hab' : a ≠ b := by
    rintro rfl
    rw [sub_self] at hab
    rcases hab with hab | hab
    · exact he hab.symm
    · exact he (by
        funext c
        have := congrFun hab c
        simp only [Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this ⊢
        omega)
  rw [mat_apply_of_mem_rootGroup hσ hx, Matrix.one_apply_ne hab']
  · rcases hab with hab | hab <;> rw [hab]
    · exact Ne.symm h1
    · exact Ne.symm h2
  · rcases hab with hab | hab <;> rw [hab]
    · exact Ne.symm h3
    · exact Ne.symm h4

theorem toStd_nsmul_two (v : Fin (n / 2) → ℤ) : toStd n (2 • v) = 2 • toStd n v :=
  toStd_nsmul n 2 v

theorem toStd_inj' : Function.Injective (toStd n) := toStd_injective n

theorem two_nsmul_injective' {v w : Fin (n / 2) → ℤ} (h : 2 • v = 2 • w) : v = w := by
  funext c
  have := congrFun h c
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  omega

theorem toStd_ne_zero_of_mem_roots {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) : toStd n γ ≠ 0 := by
  intro h
  have h0 : toStd n (0 : Fin (n / 2) → ℤ) = 0 := by
    have := toStd_nsmul n 0 0
    rwa [zero_smul, zero_smul] at this
  exact ne_zero_of_mem_roots _ _ hγ (toStd_injective n (h.trans h0.symm))

theorem eq_of_list_prod_eq (sg : ℤ) (hsg : sg ≠ 0) (L : List (Fin (n / 2) → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hindiv : ∀ γ ∈ L, ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), γ ≠ 2 • δ)
    (hlev : ∀ γ ∈ L, 1 ≤ sg * ht γ)
    (hsort : L.Pairwise fun γ δ => sg * ht γ ≤ sg * ht δ)
    (f g : (Fin (n / 2) → ℤ) → SU σ n) (hf : ∀ γ ∈ L, f γ ∈ rootGroup σ hσ n γ)
    (hg : ∀ γ ∈ L, g γ ∈ rootGroup σ hσ n γ) (hfg : (L.map f).prod = (L.map g).prod) :
    ∀ γ ∈ L, f γ = g γ := by
  induction L with
  | nil => simp
  | cons γ T ih =>
    rw [List.nodup_cons] at hL
    rw [List.pairwise_cons] at hsort
    simp only [List.map_cons, List.prod_cons] at hfg
    have hγ := hroots γ List.mem_cons_self
    have he := toStd_ne_zero_of_mem_roots hγ
    have hh : 0 < sg * ht γ := by have := hlev γ List.mem_cons_self; omega
    have hlev1 : ∀ a b : Fin n, weight n a - weight n b = toStd n γ →
        lvl sg b - lvl sg a = sg * ht γ := by
      intro a b hab
      rw [ht_eq_of_weight_sub hab]
      simp only [lvl]
      ring
    have hlev2 : ∀ a b : Fin n, weight n a - weight n b = 2 • toStd n γ →
        lvl sg b - lvl sg a = 2 * (sg * ht γ) := by
      intro a b hab
      have := two_mul_ht_eq_of_weight_sub hab
      simp only [lvl]
      linear_combination -sg * this
    have htail : ∀ k : (Fin (n / 2) → ℤ) → SU σ n, (∀ δ ∈ T, k δ ∈ rootGroup σ hσ n δ) →
        QV sg (sg * ht γ) (toStd n γ) (mat σ n (T.map k).prod) := by
      intro k hk
      rw [map_list_prod, List.map_map]
      have hall : ∀ δ ∈ T, QV sg (sg * ht γ) (toStd n γ) (mat σ n (k δ)) := by
        intro δ hδ
        have hδr := hroots δ (List.mem_cons_of_mem γ hδ)
        have hne : δ ≠ γ := fun h' => hL.1 (h' ▸ hδ)
        refine qv_of_mem_rootGroup hσ hh (hsort.1 δ hδ) he ?_ ?_ ?_ ?_ (hk δ hδ)
        · exact fun h' => hne (toStd_injective n h')
        · intro h'
          rw [← toStd_nsmul_two] at h'
          exact hindiv δ (List.mem_cons_of_mem γ hδ) γ hγ (toStd_injective n h')
        · intro h'
          rw [← toStd_nsmul_two] at h'
          exact hindiv γ List.mem_cons_self δ hδr (toStd_injective n h').symm
        · exact fun h' => hne (toStd_injective n (two_nsmul_injective' h'))
      refine qv_list_prod hsg hh he hlev1 hlev2 _ fun M hM => ?_
      obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hM
      exact hall δ hδ
    have hfγ := hf γ List.mem_cons_self
    have hgγ := hg γ List.mem_cons_self
    have hXf := idBelow_of_mem_rootGroup hσ le_rfl hh hfγ
    have hXg := idBelow_of_mem_rootGroup hσ le_rfl hh hgγ
    have hRf := htail f fun δ hδ => hf δ (List.mem_cons_of_mem γ hδ)
    have hRg := htail g fun δ hδ => hg δ (List.mem_cons_of_mem γ hδ)
    have hfg' : f γ = g γ := by
      refine eq_of_mem_rootGroup hσ hfγ hgγ fun a b hab => ?_
      rw [← mul_apply_of_qv hsg hh he hlev1 hlev2 hXf hRf a b hab,
        ← mul_apply_of_qv hsg hh he hlev1 hlev2 hXg hRg a b hab, ← map_mul, ← map_mul, hfg]
    intro δ hδ
    rcases List.mem_cons.mp hδ with rfl | hδ
    · exact hfg'
    · rw [hfg'] at hfg
      exact ih hL.2 (fun γ' hγ' => hroots γ' (List.mem_cons_of_mem _ hγ'))
        (fun γ' hγ' => hindiv γ' (List.mem_cons_of_mem _ hγ'))
        (fun γ' hγ' => hlev γ' (List.mem_cons_of_mem _ hγ')) hsort.2
        (fun γ' hγ' => hf γ' (List.mem_cons_of_mem _ hγ'))
        (fun γ' hγ' => hg γ' (List.mem_cons_of_mem _ hγ')) (mul_left_cancel hfg) δ hδ

theorem prodInjective_of (sg : ℤ) (hsg : sg ≠ 0) (L : List (Fin (n / 2) → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (hindiv : ∀ γ ∈ L, ∀ δ ∈ roots (isFiniteType_cartan n) (divisible n), γ ≠ 2 • δ)
    (hlev : ∀ γ ∈ L, 1 ≤ sg * ht γ)
    (hsort : L.Pairwise fun γ δ => sg * ht γ ≤ sg * ht δ) :
    ProdInjectiveFor (rootGroup σ hσ n) L :=
  fun f g hf hg hfg => eq_of_list_prod_eq hσ sg hsg L hL hroots hindiv hlev hsort f g hf hg hfg

theorem idBelow_of_mem_iSup (sg : ℤ) (P : Set (Fin (n / 2) → ℤ))
    (hP : ∀ γ ∈ P, 1 ≤ sg * ht γ) {x : SU σ n} (hx : x ∈ ⨆ γ ∈ P, rootGroup σ hσ n γ) :
    IdBelow (lvl sg) 1 (mat σ n x) := by
  rw [iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx (C := fun x : SU σ n => IdBelow (lvl sg) 1 (mat σ n x))
    (fun γ y hy => idBelow_of_mem_rootGroup hσ (hP γ.1 γ.2) one_pos hy) ?_ fun y z hy hz => ?_
  · rw [map_one]
    exact idBelow_one _ _
  · rw [map_mul]
    exact idBelow_mul _ one_pos hy hz

theorem eq_one_of_idBelow {x : SU σ n} (hpos : IdBelow (lvl 1) 1 (mat σ n x))
    (hneg : IdBelow (lvl (-1)) 1 (mat σ n x)) : x = 1 := by
  apply mat_injective
  rw [map_one]
  ext a b
  rcases le_or_gt b.val a.val with h | h
  · exact hpos a b (by simp only [lvl]; omega)
  · exact hneg a b (by simp only [lvl]; omega)

theorem posPart_inf_negPart :
    (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartan n) (divisible n) ∧ 0 < ht γ},
        rootGroup σ hσ n γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ roots (isFiniteType_cartan n) (divisible n) ∧ ht γ < 0},
        rootGroup σ hσ n γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxp, hxn⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_idBelow
    (idBelow_of_mem_iSup hσ 1 _ (fun γ hγ => by have := hγ.2; omega) hxp)
    (idBelow_of_mem_iSup hσ (-1) _ (fun γ hγ => by have := hγ.2; omega) hxn)

end CFSG.LieType.Universal.Unitary.SUExtras
