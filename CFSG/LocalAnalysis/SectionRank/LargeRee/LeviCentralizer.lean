module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity

section Check

variable {τ : Tag}

variable (τ) in
@[expose] def inversionCheck (ω : List (Fin τ.rank)) (P : (Fin τ.rank → ℤ) → Bool) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    decide (height (τ.rootCertificate.root k) < 0) ||
      decide (0 < height (τ.rootCertificate.root (walkPos τ ω k))) ||
        P (τ.rootCertificate.root k)

theorem of_inversionCheck
    {ω : List (Fin τ.rank)} {P : (Fin τ.rank → ℤ) → Bool}
    (h : inversionCheck τ ω P = true) {α : Root τ} (hα : 0 < height α.1)
    (hneg : height ((coxeterSystem τ).wordProd ω • α).1 < 0) : P α.1 = true := by
  obtain ⟨k, hk, hkα⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check α.2
  simp only [inversionCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rw [coe_smul_root] at hneg
  rcases h k hk with (h' | h') | h'
  · rw [hkα] at h'
    omega
  · rw [(walkPos_spec ω hk).2, hkα] at h'
    omega
  · rwa [hkα] at h'

end Check

section Centralizer

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem eq_one_of_mem_Uminus_of_forall_commute_inversions
    {A : Set (adjointGroup τ K)}
    (hA : ∀ h ∈ A, h ∈ (nativeData τ K).H) {S : Root τ → Prop}
    (hchar : ∀ β : Root τ, 0 < height β.1 → S β → ∀ y ∈ (nativeRootSubgroups τ K).X β,
      (∀ h ∈ A, h * y * h⁻¹ = y) → y = 1) :
    ∀ ω : List (Fin τ.rank), (coxeterSystem τ).IsReduced ω →
      (∀ β : Root τ, 0 < height β.1 → height ((coxeterSystem τ).wordProd ω • β).1 < 0 → S β) →
      ∀ u ∈ Uminus τ K ((coxeterSystem τ).wordProd ω), (∀ h ∈ A, h * u * h⁻¹ = u) → u = 1
  | [], _, _, u, hu, _ => by
    rwa [CoxeterSystem.wordProd_nil, Uminus_one, Subgroup.mem_bot] at hu
  | i :: ω, hred, hS, u, hu, hc => by
    have hred' : (coxeterSystem τ).IsReduced ([i] ++ ω) := hred
    obtain ⟨-, hω⟩ := isReduced_left_right_of_append hred'
    have hlen := length_mul_of_isReduced_append hred'
    rw [CoxeterSystem.wordProd_singleton] at hlen
    rw [CoxeterSystem.wordProd_cons] at hu hS
    obtain ⟨⟨z, y⟩, ⟨hz, hy, hzy⟩, huniq⟩ := existsUnique_Uminus_mul hlen hu
    simp only at hz hy hzy
    set v' := (coxeterSystem τ).wordProd ω
    set m : monomialGroup τ K := ⟨nrep τ K v', nrep_mem_monomialGroup τ K v'⟩
    have hfix : ∀ h ∈ A, h * z * h⁻¹ = z ∧ h * y * h⁻¹ = y := by
      intro h hhA
      have hh := hA h hhA
      have hh' : nrep τ K v' * h * (nrep τ K v')⁻¹ ∈ (nativeData τ K).H :=
        RootGroupData.conj_mem_H (D := nativeData τ K) m hh
      have hp := huniq (h * z * h⁻¹, h * y * h⁻¹) ⟨conj_mem_Uminus_of_mem_H hh hz, by
          have e : nrep τ K v' * (h * y * h⁻¹) * (nrep τ K v')⁻¹ =
              (nrep τ K v' * h * (nrep τ K v')⁻¹) * (nrep τ K v' * y * (nrep τ K v')⁻¹) *
                (nrep τ K v' * h * (nrep τ K v')⁻¹)⁻¹ := by group
          rw [e]
          exact conj_mem_Uminus_of_mem_H hh' hy, by
          have := hc h hhA
          rw [hzy] at this ⊢
          calc z * y = h * (z * y) * h⁻¹ := this.symm
            _ = h * z * h⁻¹ * (h * y * h⁻¹) := by group⟩
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    have hyX : y ∈ (nativeRootSubgroups τ K).X (v'⁻¹ • simpleRoot τ i) := by
      have hx := Uminus_simple_le i hy
      have h1 := RootGroupData.inv_conj_mem (D := nativeData τ K) m hx
      change (nrep τ K v')⁻¹ * (nrep τ K v' * y * (nrep τ K v')⁻¹) * nrep τ K v' ∈
        (nativeRootSubgroups τ K).X ((weylHom τ K m)⁻¹ • simpleRoot τ i) at h1
      rw [weylHom_nrep] at h1
      simpa [mul_assoc] using h1
    have hβ : 0 < height (v'⁻¹ • simpleRoot τ i).1 := by
      have hl : (coxeterSystem τ).length (simple τ i * v') =
          (coxeterSystem τ).length v' + 1 := by
        rw [hlen, (coxeterSystem τ).length_simple, add_comm]
      exact (length_simple_mul_eq_add_one_iff v' i).1 hl
    have hs : simple τ i • simpleRoot τ i = -simpleRoot τ i :=
      (rootCombinatorics τ).refl_simple i
    have hSβ : S (v'⁻¹ • simpleRoot τ i) := hS _ hβ (by
      rw [mul_smul, smul_inv_smul, hs, coe_neg_root, height_neg]
      exact neg_neg_of_pos (height_simpleRoot_pos i))
    have hy1 : y = 1 := hchar _ hβ hSβ y hyX fun h hh => (hfix h hh).2
    rw [hzy, hy1, mul_one]
    exact eq_one_of_mem_Uminus_of_forall_commute_inversions hA hchar ω hω
      (fun β hβ hneg => hS β hβ (height_mul_smul_neg hlen hβ hneg)) z hz fun h hh => (hfix h hh).1

omit [Finite K] in
theorem weylElement_eq_xElement_mul
    (i : Fin τ.rank) :
    weylElement τ K i = xElement i 1 * yElement i (-1) * xElement i 1 := by
  apply Subtype.ext
  change weylElt τ K i 1 = xUnit τ K i 1 * yUnit τ K i (-1) * xUnit τ K i 1
  rw [weylElt_eq_xUnit_mul]
  simp

theorem commute_weylElement_of_simpleChar_eq_one
    {h : adjointGroup τ K}
    (hh : h ∈ (nativeData τ K).H) {i : Fin τ.rank} (h1 : simpleChar h i = 1) :
    Commute h (weylElement τ K i) := by
  have e : h * weylElement τ K i * h⁻¹ = weylElement τ K i := by
    rw [weylElement_eq_xElement_mul]
    have e' : ∀ x y z : adjointGroup τ K,
        h * (x * y * z) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) * (h * z * h⁻¹) := fun _ _ _ => by
      group
    rw [e', conj_xElement_of_mem_H hh, conj_yElement_of_mem_H hh, h1, inv_one, one_mul, one_mul]
  exact mul_inv_eq_iff_eq_mul.1 e

end Centralizer

section F4

variable {K : Type} [Field K]

@[expose] noncomputable def torusProd4
    (m₀ m₁ m₂ m₃ : ℤ) (t : Kˣ) :
    adjointGroup ReeTag.F4.tag K :=
  torusElement ReeTag.F4.tag K (fi 0) (t ^ m₀) * torusElement ReeTag.F4.tag K (fi 1) (t ^ m₁) *
    torusElement ReeTag.F4.tag K (fi 2) (t ^ m₂) * torusElement ReeTag.F4.tag K (fi 3) (t ^ m₃)

theorem torusProd4_mem_H
    [Finite K] (m₀ m₁ m₂ m₃ : ℤ) (t : Kˣ) :
    torusProd4 m₀ m₁ m₂ m₃ t ∈ (nativeData ReeTag.F4.tag K).H :=
  mul_mem (mul_mem (mul_mem (torusElement_mem_H _ _ _) (torusElement_mem_H _ _ _))
    (torusElement_mem_H _ _ _)) (torusElement_mem_H _ _ _)

theorem torusProd4_conj
    (m₀ m₁ m₂ m₃ : ℤ) (t : Kˣ) (β : Root ReeTag.F4.tag) (c : K) :
    torusProd4 m₀ m₁ m₂ m₃ t * (rootOperatorFamily ReeTag.F4.tag).eltElement β c *
        (torusProd4 m₀ m₁ m₂ m₃ t)⁻¹ =
      (rootOperatorFamily ReeTag.F4.tag).eltElement β
        (((t ^ (m₀ * ∑ j, ReeTag.F4.tag.cartan (fi 0) j * β.1 j +
          m₁ * ∑ j, ReeTag.F4.tag.cartan (fi 1) j * β.1 j +
          m₂ * ∑ j, ReeTag.F4.tag.cartan (fi 2) j * β.1 j +
          m₃ * ∑ j, ReeTag.F4.tag.cartan (fi 3) j * β.1 j) : Kˣ) : K) * c) := by
  have e : ∀ a b c d x : adjointGroup ReeTag.F4.tag K, a * b * c * d * x * (a * b * c * d)⁻¹ =
      a * (b * (c * (d * x * d⁻¹) * c⁻¹) * b⁻¹) * a⁻¹ := fun _ _ _ _ _ => by group
  rw [torusProd4, e, RootOperatorFamily.torusElement_mul_eltElement_mul_inv,
    RootOperatorFamily.torusElement_mul_eltElement_mul_inv,
    RootOperatorFamily.torusElement_mul_eltElement_mul_inv,
    RootOperatorFamily.torusElement_mul_eltElement_mul_inv]
  congr 1
  simp only [← mul_assoc, ← Units.val_mul, ← zpow_mul, ← zpow_add, add_assoc]

theorem sum_cartan_F4 (i : Fin ReeTag.F4.tag.rank) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    ∑ j, ReeTag.F4.tag.cartan i j * v j =
      ReeTag.F4.tag.cartan i (fi 0) * v (fi 0) + ReeTag.F4.tag.cartan i (fi 1) * v (fi 1) +
        ReeTag.F4.tag.cartan i (fi 2) * v (fi 2) + ReeTag.F4.tag.cartan i (fi 3) * v (fi 3) :=
  Fin.sum_univ_four _

theorem cartan_F4_entries :
    (ReeTag.F4.tag.cartan (fi 0) (fi 0) = 2 ∧ ReeTag.F4.tag.cartan (fi 0) (fi 1) = -1 ∧
      ReeTag.F4.tag.cartan (fi 0) (fi 2) = 0 ∧ ReeTag.F4.tag.cartan (fi 0) (fi 3) = 0) ∧
    (ReeTag.F4.tag.cartan (fi 1) (fi 0) = -1 ∧ ReeTag.F4.tag.cartan (fi 1) (fi 1) = 2 ∧
      ReeTag.F4.tag.cartan (fi 1) (fi 2) = -1 ∧ ReeTag.F4.tag.cartan (fi 1) (fi 3) = 0) ∧
    (ReeTag.F4.tag.cartan (fi 2) (fi 0) = 0 ∧ ReeTag.F4.tag.cartan (fi 2) (fi 1) = -2 ∧
      ReeTag.F4.tag.cartan (fi 2) (fi 2) = 2 ∧ ReeTag.F4.tag.cartan (fi 2) (fi 3) = -1) ∧
    (ReeTag.F4.tag.cartan (fi 3) (fi 0) = 0 ∧ ReeTag.F4.tag.cartan (fi 3) (fi 1) = 0 ∧
      ReeTag.F4.tag.cartan (fi 3) (fi 2) = -1 ∧ ReeTag.F4.tag.cartan (fi 3) (fi 3) = 2) := by
  decide

theorem coweight_exponents (v : Fin ReeTag.F4.tag.rank → ℤ) :
    (2 * ∑ j, ReeTag.F4.tag.cartan (fi 0) j * v j + 3 * ∑ j, ReeTag.F4.tag.cartan (fi 1) j * v j +
      2 * ∑ j, ReeTag.F4.tag.cartan (fi 2) j * v j + 1 * ∑ j, ReeTag.F4.tag.cartan (fi 3) j * v j =
        v (fi 0)) ∧
    (2 * ∑ j, ReeTag.F4.tag.cartan (fi 0) j * v j + 4 * ∑ j, ReeTag.F4.tag.cartan (fi 1) j * v j +
      3 * ∑ j, ReeTag.F4.tag.cartan (fi 2) j * v j + 2 * ∑ j, ReeTag.F4.tag.cartan (fi 3) j * v j =
        v (fi 3)) := by
  obtain ⟨⟨a00, a01, a02, a03⟩, ⟨a10, a11, a12, a13⟩, ⟨a20, a21, a22, a23⟩,
    ⟨a30, a31, a32, a33⟩⟩ := cartan_F4_entries
  simp only [sum_cartan_F4, a00, a01, a02, a03, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31,
    a32, a33]
  constructor <;> ring

theorem torusProd4_conj_zero
    (t : Kˣ) (β : Root ReeTag.F4.tag) (c : K) :
    torusProd4 2 3 2 1 t * (rootOperatorFamily ReeTag.F4.tag).eltElement β c *
        (torusProd4 2 3 2 1 t)⁻¹ =
      (rootOperatorFamily ReeTag.F4.tag).eltElement β (((t ^ β.1 (fi 0) : Kˣ) : K) * c) := by
  rw [torusProd4_conj, (coweight_exponents β.1).1]

theorem torusProd4_conj_three
    (t : Kˣ) (β : Root ReeTag.F4.tag) (c : K) :
    torusProd4 2 4 3 2 t * (rootOperatorFamily ReeTag.F4.tag).eltElement β c *
        (torusProd4 2 4 3 2 t)⁻¹ =
      (rootOperatorFamily ReeTag.F4.tag).eltElement β (((t ^ β.1 (fi 3) : Kˣ) : K) * c) := by
  rw [torusProd4_conj, (coweight_exponents β.1).2]

variable [Finite K]

theorem simpleChar_torusProd4_zero
    (t : Kˣ) {k : Fin ReeTag.F4.tag.rank} (hk : k ≠ fi 0) :
    simpleChar (torusProd4 2 3 2 1 t) k = 1 := by
  refine simpleChar_eq_of_conj (torusProd4_mem_H 2 3 2 1 t) ?_
  rw [← eltElement_simpleRoot, torusProd4_conj_zero, mul_one]
  congr 1
  simp [simpleRoot, Ne.symm hk]

theorem simpleChar_torusProd4_three
    (t : Kˣ) {k : Fin ReeTag.F4.tag.rank} (hk : k ≠ fi 3) :
    simpleChar (torusProd4 2 4 3 2 t) k = 1 := by
  refine simpleChar_eq_of_conj (torusProd4_mem_H 2 4 3 2 t) ?_
  rw [← eltElement_simpleRoot, torusProd4_conj_three, mul_one]
  congr 1
  simp [simpleRoot, Ne.symm hk]

@[expose] def leviWord : List (Fin ReeTag.F4.tag.rank) :=
  ([0, 3, 1, 2, 1, 2, 0, 3, 1, 2, 1, 2, 0, 3, 1, 2, 1, 2, 0, 3] : List (Fin 4))

@[expose] def outerCoeff (v : Fin ReeTag.F4.tag.rank → ℤ) : Bool :=
  decide (v (fi 0) = 1) || decide (v (fi 0) = 2) || decide (v (fi 3) = 1) ||
    decide (v (fi 3) = 2)

theorem leviWord_spec :
    reducedCheck ReeTag.F4.tag (leviWord ++ ReeTag.F4.reeOrbitWord (fi 1)) = true ∧
      negCheck ReeTag.F4.tag (leviWord ++ ReeTag.F4.reeOrbitWord (fi 1)) = true ∧
        inversionCheck ReeTag.F4.tag leviWord outerCoeff = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem mem_Uminus_blockElt_one_of_forall_commute
    (ht : ∃ t : Kˣ, t ≠ 1 ∧ t ^ 2 ≠ 1)
    {u : adjointGroup ReeTag.F4.tag K} (hu : u ∈ (nativeData ReeTag.F4.tag K).U)
    (hc : ∀ h ∈ (nativeData ReeTag.F4.tag K).H, simpleChar h (fi 1) = 1 →
      simpleChar h (fi 2) = 1 → h * u * h⁻¹ = u) :
    u ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) := by
  obtain ⟨t, ht1, ht2⟩ := ht
  obtain ⟨hred, hneg, hinv⟩ := leviWord_spec
  have hred' := isReduced_of_reducedCheck hred
  set A : Set (adjointGroup ReeTag.F4.tag K) := {torusProd4 2 3 2 1 t, torusProd4 2 4 3 2 t}
    with hAdef
  have hAH : ∀ h ∈ A, h ∈ (nativeData ReeTag.F4.tag K).H := by
    rintro h (rfl | rfl)
    · exact torusProd4_mem_H _ _ _ _ _
    · exact torusProd4_mem_H _ _ _ _ _
  have hA12 : ∀ h ∈ A, simpleChar h (fi 1) = 1 ∧ simpleChar h (fi 2) = 1 := by
    rintro h (rfl | rfl)
    · exact ⟨simpleChar_torusProd4_zero t (by decide), simpleChar_torusProd4_zero t (by decide)⟩
    · exact ⟨simpleChar_torusProd4_three t (by decide), simpleChar_torusProd4_three t (by decide)⟩
  have hAn : ∀ h ∈ A, Commute h (nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1))) := by
    intro h hh
    rw [ReeTag.blockElt, nrep_eq_prod _ K (isReduced_reeOrbitWord ReeTag.F4 (fi 1))]
    refine Commute.list_prod_right _ _ fun x hx => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    rcases mem_of_mem_reeOrbitWord ReeTag.F4 (fi 1) j hj with rfl | rfl
    · exact commute_weylElement_of_simpleChar_eq_one (hAH h hh) (hA12 h hh).1
    · rw [perm_fi_one]
      exact commute_weylElement_of_simpleChar_eq_one (hAH h hh) (hA12 h hh).2
  have hlen := length_mul_of_isReduced_append hred'
  have huw : u ∈ Uminus ReeTag.F4.tag K
      ((coxeterSystem ReeTag.F4.tag).wordProd leviWord * ReeTag.F4.blockElt (fi 1)) := by
    rw [ReeTag.blockElt, ← CoxeterSystem.wordProd_append, Uminus_eq_U_of_negCheck hneg]
    exact hu
  obtain ⟨⟨z, y⟩, ⟨hz, hy, hzy⟩, huniq⟩ := existsUnique_Uminus_mul hlen huw
  simp only at hz hy hzy
  set n := nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (fi 1)) with hn
  have hfix : ∀ h ∈ A, h * y * h⁻¹ = y := by
    intro h hhA
    have hh := hAH h hhA
    have hp := huniq (h * z * h⁻¹, h * y * h⁻¹) ⟨conj_mem_Uminus_of_mem_H hh hz, by
        have e : n * (h * y * h⁻¹) * n⁻¹ = h * (n * y * n⁻¹) * h⁻¹ := by
          rw [show n * (h * y * h⁻¹) * n⁻¹ = (n * h) * y * (h⁻¹ * n⁻¹) by group,
            ← (hAn h hhA).eq, ← mul_inv_rev, ← (hAn h hhA).eq]
          group
        rw [e]
        exact conj_mem_Uminus_of_mem_H hh hy, by
        have := hc h hh (hA12 h hhA).1 (hA12 h hhA).2
        rw [hzy] at this ⊢
        calc z * y = h * (z * y) * h⁻¹ := this.symm
          _ = h * z * h⁻¹ * (h * y * h⁻¹) := by group⟩
    exact congrArg Prod.snd hp
  have hy' : ∀ h ∈ A, h * (n * y * n⁻¹) * h⁻¹ = n * y * n⁻¹ := by
    intro h hhA
    calc h * (n * y * n⁻¹) * h⁻¹ = n * (h * y * h⁻¹) * n⁻¹ := by
          rw [show h * (n * y * n⁻¹) * h⁻¹ = (h * n) * y * (n⁻¹ * h⁻¹) by group,
            (hAn h hhA).eq, ← mul_inv_rev, (hAn h hhA).eq]
          group
      _ = n * y * n⁻¹ := by rw [hfix h hhA]
  have hne : ∀ m : ℤ, (m = 1 ∨ m = 2) → ((t ^ m : Kˣ) : K) ≠ 1 := by
    rintro m (rfl | rfl)
    · rw [zpow_one, Ne, Units.val_eq_one]
      exact ht1
    · rw [zpow_two, ← sq, Ne, Units.val_eq_one]
      exact ht2
  have hchar : ∀ β : Root ReeTag.F4.tag, 0 < height β.1 → outerCoeff β.1 = true →
      ∀ y ∈ (nativeRootSubgroups ReeTag.F4.tag K).X β, (∀ h ∈ A, h * y * h⁻¹ = y) → y = 1 := by
    intro β _ hβ x hx hxc
    simp only [outerCoeff, Bool.or_eq_true, decide_eq_true_eq] at hβ
    rcases hβ with ((h0 | h0) | h3) | h3
    · exact eq_one_of_conj_eltElement (hne _ (.inl h0)) (torusProd4_conj_zero t β) hx
        (hxc _ (Set.mem_insert _ _))
    · exact eq_one_of_conj_eltElement (hne _ (.inr h0)) (torusProd4_conj_zero t β) hx
        (hxc _ (Set.mem_insert _ _))
    · exact eq_one_of_conj_eltElement (hne _ (.inl h3)) (torusProd4_conj_three t β) hx
        (hxc _ (Set.mem_insert_of_mem _ rfl))
    · exact eq_one_of_conj_eltElement (hne _ (.inr h3)) (torusProd4_conj_three t β) hx
        (hxc _ (Set.mem_insert_of_mem _ rfl))
  have hy1 : n * y * n⁻¹ = 1 :=
    eq_one_of_mem_Uminus_of_forall_commute_inversions hAH hchar leviWord
      (isReduced_left_right_of_append hred').1 (fun β hβ hneg => of_inversionCheck hinv hβ hneg)
      _ hy hy'
  rw [conj_eq_one_iff] at hy1
  rw [hzy, hy1, mul_one]
  exact hz

end F4

end CFSG.SectionRank.LargeRee
