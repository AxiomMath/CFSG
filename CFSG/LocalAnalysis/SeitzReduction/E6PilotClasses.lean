module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE6

public section

namespace CFSG.SeitzReduction.E6Pilot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def e6RepFrame : Fin 3 → List (Fin Tag.E6.rank → ℤ) :=
  ![[Pi.single (0 : Fin 6) 1], [Pi.single (0 : Fin 6) 1, Pi.single (3 : Fin 6) 1],
    [Pi.single (0 : Fin 6) 1, Pi.single (3 : Fin 6) 1, Pi.single (5 : Fin 6) 1]]

@[expose] def e6ASFrame : Fin 3 → List (Fin Tag.E6.rank → ℤ) :=
  ![[highRoot .E6], oddDerivE6YFrame, oddDerivE6ZFrame]

@[expose] def e6RepPos : Fin 3 → List ℕ :=
  ![[0], [0, 3], [0, 3, 5]]

@[expose] def e6ASPos : Fin 3 → List ℕ :=
  ![[70], [61, 62], [58, 56, 55]]

@[expose] def e6RepWord : Fin 3 → List ℕ :=
  ![[1, 3, 2, 4, 3, 1, 5, 4, 3, 2], [0, 2, 3, 1, 4, 3, 5, 4, 3, 1, 2],
    [3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2]]

@[expose] def e6RepPreHigh : Fin 3 → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 0], ![0, 1, 0, 0, 0, 0]]

@[expose] def e6RepPreHighPos : Fin 3 → ℕ :=
  ![40, 43, 1]

@[expose] noncomputable def e6RepWeyl (κ : Fin 3) : WeylGroup .E6 :=
  weylOfWord .E6 (e6RepWord κ)

theorem e6RepPos_map (κ : Fin 3) :
    (e6RepPos κ).map Tag.E6.rootCertificate.root = e6RepFrame κ := by
  apply List.map_injective_iff.2 List.ofFn_injective
  revert κ
  decide +kernel

theorem e6ASPos_map (κ : Fin 3) :
    (e6ASPos κ).map Tag.E6.rootCertificate.root = e6ASFrame κ := by
  apply List.map_injective_iff.2 List.ofFn_injective
  revert κ
  decide +kernel

theorem e6RepPreHighPos_root (κ : Fin 3) :
    Tag.E6.rootCertificate.root (e6RepPreHighPos κ) = e6RepPreHigh κ ∧
      Tag.E6.rootCertificate.root 70 = highRoot .E6 := by
  refine ⟨List.ofFn_injective ?_, List.ofFn_injective (by decide +kernel)⟩
  revert κ
  decide +kernel

theorem e6ASPos_lt (κ : Fin 3) :
    (∀ k ∈ e6ASPos κ, k < Tag.E6.rootCertificate.roots.length) ∧
      e6RepPreHighPos κ < Tag.E6.rootCertificate.roots.length := by
  revert κ
  decide +kernel

theorem e6RepWord_wordPos (κ : Fin 3) :
    (e6ASPos κ).map (wordPos Tag.E6.rootCertificate (e6RepWord κ)) = e6RepPos κ ∧
      wordPos Tag.E6.rootCertificate (e6RepWord κ) (e6RepPreHighPos κ) = 70 := by
  revert κ
  decide +kernel

theorem e6RepFrame_perp (κ : Fin 3) : ∀ β ∈ e6RepFrame κ,
    IsRoot .E6 β ∧ β (highNode .E6) = 0 ∧ iform β (highRoot .E6) = 0 := by
  have h0 : ∀ i : Fin 6, i ∈ [0, 3, 5] → IsRoot .E6 (Pi.single i 1) ∧
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (highNode .E6) = 0 ∧
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (highRoot .E6) = 0 := by
    intro i hi
    refine ⟨isRoot_single .E6 i, ?_⟩
    revert i
    decide +kernel
  intro β hβ
  fin_cases κ <;>
    simp only [e6RepFrame, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      List.mem_cons, List.not_mem_nil, or_false] at hβ <;>
    rcases hβ with rfl | rfl | rfl <;> exact h0 _ (by decide)

theorem e6RepFrame_pairwise (κ : Fin 3) :
    (e6RepFrame κ).Pairwise fun σ σ' => iform σ σ' = 0 := by
  revert κ
  decide +kernel

theorem e6RepFrame_ne_nil (κ : Fin 3) : e6RepFrame κ ≠ [] := by
  revert κ
  decide

theorem e6RepFrame_nodup_pos (κ : Fin 3) :
    (e6RepFrame κ).Nodup ∧ ∀ β ∈ e6RepFrame κ, 0 < height β := by
  revert κ
  decide +kernel

theorem e6ASFrame_isRoot (κ : Fin 3) :
    ∀ σ ∈ e6ASFrame κ, IsRoot .E6 σ := by
  intro σ hσ
  rw [← e6ASPos_map] at hσ
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hσ
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E6) k ((e6ASPos_lt κ).1 k hk)

section Weyl


theorem e6RepWeyl_smul_e6ASFrame (κ : Fin 3) :
    (e6ASFrame κ).map (e6RepWeyl κ • ·) = e6RepFrame κ := by
  rw [← e6ASPos_map, ← e6RepPos_map, ← (e6RepWord_wordPos κ).1, List.map_map, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  exact (wordPos_spec (Tag.rootCertificate_check .E6) (e6RepWord κ)
    ((e6ASPos_lt κ).1 k hk)).2.symm

theorem e6RepWeyl_smul_e6RepPreHigh (κ : Fin 3) :
    e6RepWeyl κ • e6RepPreHigh κ = highRoot .E6 := by
  obtain ⟨h1, h2⟩ := e6RepPreHighPos_root κ
  have h := (wordPos_spec (Tag.rootCertificate_check .E6) (e6RepWord κ) (e6ASPos_lt κ).2).2
  rw [(e6RepWord_wordPos κ).2, h2, h1] at h
  exact h.symm

end Weyl

section Transport


variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem canonicalRep_mul_pinnedX_mul_inv_of_charTwo (w : WeylGroup τ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (c : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K α c * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • α) c := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hα
  rw [h, frameWalk_eq_one_of_mul_self hε, one_mul]

theorem canonicalRep_mul_list_prod_mul_inv_of_charTwo (w : WeylGroup τ)
    {F : List (Fin τ.rank → ℤ)} (hF : ∀ α ∈ F, IsRoot τ α) (c : (Fin τ.rank → ℤ) → K) :
    canonicalRep (coxeterSystem τ) K w * (F.map fun α => pinnedX τ K α (c α)).prod *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      (F.map fun α => pinnedX τ K (w • α) (c α)).prod := by
  induction F with
  | nil => simp
  | cons α F ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      ← canonicalRep_mul_pinnedX_mul_inv_of_charTwo w (hF α List.mem_cons_self) (c α),
      ← ih fun β hβ => hF β (List.mem_cons_of_mem _ hβ)]
    group

end Transport

variable {K : Type} [Field K]

section Reps


variable (K) in
@[expose] noncomputable def e6Rep (κ : Fin 3) : adjointGroup .E6 K :=
  ⟨((e6RepFrame κ).map fun σ => pinnedX .E6 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup _⟩

variable (K) in
@[expose] noncomputable def e6ASRep (κ : Fin 3) : adjointGroup .E6 K :=
  ⟨((e6ASFrame κ).map fun σ => pinnedX .E6 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup _⟩

variable (K) in
@[expose] noncomputable def e6RepConj (κ : Fin 3) : adjointGroup .E6 K :=
  ⟨canonicalRep (coxeterSystem .E6) K (e6RepWeyl κ), canonicalRep_mem_adjointGroup _ K _⟩

theorem coe_e6Rep (κ : Fin 3) :
    (e6Rep K κ : ModGL .E6 K) = ((e6RepFrame κ).map fun σ => pinnedX .E6 K σ 1).prod :=
  rfl

theorem coe_e6Rep_zero :
    (e6Rep K 0 : ModGL .E6 K) = pinnedX .E6 K (Pi.single (0 : Fin 6) 1) 1 := by
  simp [e6Rep, e6RepFrame]

theorem coe_e6Rep_one :
    (e6Rep K 1 : ModGL .E6 K) =
      pinnedX .E6 K (Pi.single (0 : Fin 6) 1) 1 * pinnedX .E6 K (Pi.single (3 : Fin 6) 1) 1 := by
  simp [e6Rep, e6RepFrame]

theorem coe_e6Rep_two :
    (e6Rep K 2 : ModGL .E6 K) =
      pinnedX .E6 K (Pi.single (0 : Fin 6) 1) 1 * pinnedX .E6 K (Pi.single (3 : Fin 6) 1) 1 *
        pinnedX .E6 K (Pi.single (5 : Fin 6) 1) 1 := by
  simp [e6Rep, e6RepFrame, mul_assoc]

theorem coe_e6RepConj (κ : Fin 3) :
    (e6RepConj K κ : ModGL .E6 K) = canonicalRep (coxeterSystem .E6) K (e6RepWeyl κ) :=
  rfl

theorem mem_innerRepsE6_iff {t : adjointGroup .E6 K} :
    t ∈ innerRepsE6 K ↔ ∃ κ : Fin 3, t = e6ASRep K κ := by
  have e0 : e6ASRep K 0 = ⟨pinnedX .E6 K (highRoot .E6) 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (by simp [e6ASRep, e6ASFrame])
  simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, h.trans e0.symm⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨κ, rfl⟩
    fin_cases κ
    · exact Or.inl e0
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem coe_e6Rep_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)} {κ : Fin 3}
    (hS : ∀ β ∈ e6RepFrame κ, β ∈ S) : (e6Rep K κ : ModGL .E6 K) ∈ rootSpan .E6 K S :=
  list_prod_mem fun x hx => by
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_rootSpan (hS σ hσ) 1

theorem coe_e6Rep_mem_rootSpan_perp (κ : Fin 3) :
    (e6Rep K κ : ModGL .E6 K) ∈
      rootSpan .E6 K {γ | IsRoot .E6 γ ∧ γ (highNode .E6) = 0} :=
  coe_e6Rep_mem_rootSpan fun β hβ =>
    ⟨(e6RepFrame_perp κ β hβ).1, (e6RepFrame_perp κ β hβ).2.1⟩

theorem coe_e6Rep_mem_rootSpan_iform (κ : Fin 3) :
    (e6Rep K κ : ModGL .E6 K) ∈
      rootSpan .E6 K {γ | IsRoot .E6 γ ∧ iform γ (highRoot .E6) = 0} :=
  coe_e6Rep_mem_rootSpan fun β hβ =>
    ⟨(e6RepFrame_perp κ β hβ).1, (e6RepFrame_perp κ β hβ).2.2⟩

end Reps

section Conj


theorem e6RepConj_mul_e6ASRep_mul_inv [CharP K 2] (κ : Fin 3) :
    e6RepConj K κ * e6ASRep K κ * (e6RepConj K κ)⁻¹ = e6Rep K κ := by
  apply Subtype.ext
  change canonicalRep (coxeterSystem .E6) K (e6RepWeyl κ) *
      ((e6ASFrame κ).map fun σ => pinnedX .E6 K σ ((fun _ => (1 : K)) σ)).prod *
        (canonicalRep (coxeterSystem .E6) K (e6RepWeyl κ))⁻¹ =
      ((e6RepFrame κ).map fun σ => pinnedX .E6 K σ 1).prod
  rw [canonicalRep_mul_list_prod_mul_inv_of_charTwo (e6RepWeyl κ) (e6ASFrame_isRoot κ),
    ← e6RepWeyl_smul_e6ASFrame κ, List.map_map]
  rfl

theorem map_conj_e6RepConj_rootSubgroup (κ : Fin 3) {ρ : Fin Tag.E6.rank → ℤ}
    (hρ : IsRoot .E6 ρ) :
    (rootSubgroup .E6 K ρ).map (MulAut.conj (e6RepConj K κ : ModGL .E6 K)).toMonoidHom =
      rootSubgroup .E6 K (e6RepWeyl κ • ρ) :=
  (canonical_weyl_root_transport .E6 K).2.1 _ ρ hρ

theorem map_conj_e6RepConj_rootSpan (κ : Fin 3) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ ρ ∈ S, IsRoot .E6 ρ) :
    (rootSpan .E6 K S).map (MulAut.conj (e6RepConj K κ : ModGL .E6 K)).toMonoidHom =
      rootSpan .E6 K ((e6RepWeyl κ • ·) '' S) :=
  (canonical_weyl_root_transport .E6 K).1 _ S hS

theorem coe_e6RepConj_mem_normalizer_torusGroup (κ : Fin 3) :
    (e6RepConj K κ : ModGL .E6 K) ∈
      Subgroup.normalizer (torusGroup .E6 K : Set (ModGL .E6 K)) :=
  (canonical_weyl_root_transport .E6 K).2.2 _

theorem exists_conj_e6ASRep_eq_e6Rep [CharP K 2] (κ : Fin 3) :
    ∃ c : adjointGroup .E6 K, c * e6ASRep K κ * c⁻¹ = e6Rep K κ :=
  ⟨e6RepConj K κ, e6RepConj_mul_e6ASRep_mul_inv κ⟩

theorem frameProdConj_e6ASFrame_e6RepFrame [CharP K 2] (κ : Fin 3) :
    FrameProdConj .E6 K (e6ASFrame κ) (e6RepFrame κ) :=
  ⟨e6RepConj K κ, (e6RepConj K κ).2, congrArg Subtype.val (e6RepConj_mul_e6ASRep_mul_inv κ)⟩

end Conj

section ClassList


theorem exists_conj_eq_e6Rep_of_sq [Finite K] [CharP K 2] {y : adjointGroup .E6 K}
    (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    ∃ (κ : Fin 3) (c : adjointGroup .E6 K), c * y * c⁻¹ = e6Rep K κ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_innerRepsE6 hy2 hy1
  obtain ⟨κ, hκ⟩ := mem_innerRepsE6_iff.1 hg
  refine ⟨κ, e6RepConj K κ * g, ?_⟩
  rw [← e6RepConj_mul_e6ASRep_mul_inv κ, ← hκ]
  group

theorem exists_conj_eq_e6Rep [Finite K] [CharP K 2] {y : adjointGroup .E6 K}
    (hy : orderOf y = 2) :
    ∃ (κ : Fin 3) (c : adjointGroup .E6 K), c * y * c⁻¹ = e6Rep K κ := by
  refine exists_conj_eq_e6Rep_of_sq (hy ▸ pow_orderOf_eq_one y) fun h => ?_
  rw [h, orderOf_one] at hy
  exact absurd hy (by decide)

theorem exists_conj_eq_symm_e6Rep [Finite K] [CharP K 2] {L : Type*} [Group L]
    (e : L ≃* adjointGroup .E6 K) {y : L} (hy : orderOf y = 2) :
    ∃ (κ : Fin 3) (l : L), l * y * l⁻¹ = e.symm (e6Rep K κ) := by
  obtain ⟨κ, c, hc⟩ := exists_conj_eq_e6Rep (K := K) (y := e y) (by rw [MulEquiv.orderOf_eq, hy])
  refine ⟨κ, e.symm c, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

end ClassList

section Involution


theorem e6Rep_ne_one (κ : Fin 3) : e6Rep K κ ≠ 1 := by
  intro h
  obtain ⟨hnd, hpos⟩ := e6RepFrame_nodup_pos κ
  have h1 : ((e6RepFrame κ).map fun σ => pinnedX .E6 K σ ((fun _ => (1 : K)) σ)).prod =
      ((e6RepFrame κ).map fun σ => pinnedX .E6 K σ ((fun _ => (0 : K)) σ)).prod := by
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
    exact congrArg Subtype.val h
  obtain ⟨β, hβ⟩ := List.exists_mem_of_ne_nil _ (e6RepFrame_ne_nil κ)
  exact one_ne_zero (pinnedX_list_prod_injective (e6RepFrame κ) hnd
    (fun α hα => ⟨(e6RepFrame_perp κ α hα).1, hpos α hα⟩) _ _ h1 β hβ)

theorem e6Rep_sq [CharP K 2] (κ : Fin 3) : e6Rep K κ ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτ : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inr (Or.inl rfl)
  have sq : ∀ β : Fin Tag.E6.rank → ℤ, pinnedX .E6 K β 1 ^ 2 = 1 := fun β => by
    rw [pow_two]
    exact classD4_pinnedX_mul_self h2 β
  have key : ∀ F : List (Fin Tag.E6.rank → ℤ), (∀ β ∈ F, IsRoot .E6 β) →
      F.Pairwise (fun σ σ' => iform σ σ' = 0) →
      ((F.map fun σ => pinnedX .E6 K σ 1).prod) ^ 2 = 1 := by
    intro F
    induction F with
    | nil => intro _ _; simp
    | cons β F ih =>
      intro hF hpw
      rw [List.pairwise_cons] at hpw
      have hc : Commute (pinnedX .E6 K β 1) (F.map fun σ => pinnedX .E6 K σ 1).prod :=
        Commute.list_prod_right _ _ fun x hx => by
          obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
          exact classD4_commute_pinnedX hτ (hF β List.mem_cons_self)
            (hF σ (List.mem_cons_of_mem _ hσ)) (hpw.1 σ hσ).ge 1 1
      rw [List.map_cons, List.prod_cons, hc.mul_pow, sq,
        ih (fun σ hσ => hF σ (List.mem_cons_of_mem _ hσ)) hpw.2, one_mul]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact key _ (fun β hβ => (e6RepFrame_perp κ β hβ).1) (e6RepFrame_pairwise κ)

theorem orderOf_e6Rep [CharP K 2] (κ : Fin 3) : orderOf (e6Rep K κ) = 2 :=
  orderOf_eq_prime (e6Rep_sq κ) (e6Rep_ne_one κ)

end Involution

end CFSG.SeitzReduction.E6Pilot
