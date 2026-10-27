module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.HeisChevalley
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisSystemRoot
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SqRange

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SignalizerFunctorTheorem.NonLocalExc CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

section Pinned

@[expose] noncomputable def pinnedA (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) (c : K) :
    ↥(adjointGroup τ K) :=
  ⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩

theorem pinnedA_ext {x y : ↥(adjointGroup τ K)}
    (h : (x : ModGL τ K) = (y : ModGL τ K)) : x = y := Subtype.ext h

theorem pinnedA_add (α : Fin τ.rank → ℤ) (c d : K) :
    pinnedA τ K α (c + d) = pinnedA τ K α c * pinnedA τ K α d :=
  pinnedA_ext (pinnedX_add τ K α c d)

theorem pinnedA_neg (α : Fin τ.rank → ℤ) (c : K) : (pinnedA τ K α c)⁻¹ = pinnedA τ K α (-c) :=
  pinnedA_ext (pinnedX_neg τ K α c)

theorem pinnedA_comm (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hposα : 0 < height α) (hposβ : 0 < height β)
    (h : ¬ IsRoot τ (α + β)) (c d : K) :
    pinnedA τ K α c * pinnedA τ K β d = pinnedA τ K β d * pinnedA τ K α c :=
  pinnedA_ext (pinned_comm_of_not_isRoot hτ hα hβ hposα hposβ h c d)

theorem exists_comm_ss_K (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (β : Fin τ.rank → ℤ) (hβ : β ∈ heisS τ) :
    ∃ ε : K, ε ≠ 0 ∧ ∀ c d : K,
      ⁅(pinnedA τ K (heisα0 τ - β) c)⁻¹, pinnedA τ K β d⁆ = pinnedA τ K (heisα0 τ) (ε * c * d) := by
  have hβpos := hF.pos_of_mem β hβ
  have hlt := hF.two_height_lt β hβ
  have hγpos : 0 < height (heisα0 τ - β) := by
    rw [height_sub']
    omega
  have hne : heisα0 τ - β ≠ β := fun h => hF.sub_not_mem β hβ (by rw [h]; exact hβ)
  have hsum : heisα0 τ - β + β = heisα0 τ := sub_add_cancel _ _
  obtain ⟨ε', hε', hf⟩ := exists_pinned_comm_of_isRoot hτ (hF.isRoot_sub β hβ)
    (hF.isRoot_of_mem β hβ) hγpos hβpos hne (by rw [hsum]; exact hF.isRoot_α0)
  refine ⟨-(ε' : K), ?_, fun c d => ?_⟩
  · rcases hε' with rfl | rfl <;> simp
  · rw [pinnedA_neg]
    refine pinnedA_ext ?_
    have := hf K (-c) d
    simp only [hsum] at this
    show ⁅pinnedX τ K (heisα0 τ - β) (-c), pinnedX τ K β d⁆ = _
    rw [this]
    congr 1
    push_cast
    ring

end Pinned

section System

@[expose] noncomputable def heisSystemK (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (hα0 : 0 < height (heisα0 τ)) : HeisSystem ↥(adjointGroup τ K) K ↥(heisS τ) where
  xa s c := pinnedA τ K s.1 c
  xb s c := pinnedA τ K (heisα0 τ - s.1) c
  z c := pinnedA τ K (heisα0 τ) c
  ε s := Classical.choose (exists_comm_ss_K (K := K) hτ hF s.1 s.2)
  xa_add s c d := pinnedA_add s.1 c d
  xb_add s c d := pinnedA_add _ c d
  z_add c d := pinnedA_add _ c d
  z_injective := fun c d h => pinnedX_injective τ K _ (congrArg (fun x : ↥(adjointGroup τ K) =>
    (x : ModGL τ K)) h)
  ε_ne s := (Classical.choose_spec (exists_comm_ss_K (K := K) hτ hF s.1 s.2)).1
  xa_comm s t c d := pinnedA_comm hτ (hF.isRoot_of_mem _ s.2) (hF.isRoot_of_mem _ t.2)
    (hF.pos_of_mem _ s.2) (hF.pos_of_mem _ t.2) (hF.not_isRoot_SS _ s.2 _ t.2) c d
  xb_comm s t c d := pinnedA_comm hτ (hF.isRoot_sub _ s.2) (hF.isRoot_sub _ t.2)
    (heis_gamma_pos (hF := hF) s.2) (heis_gamma_pos (hF := hF) t.2)
    (hF.not_isRoot_TT _ s.2 _ t.2) c d
  z_comm_a c s d := pinnedA_comm hτ hF.isRoot_α0 (hF.isRoot_of_mem _ s.2) hα0
    (hF.pos_of_mem _ s.2) (hF.not_isRoot_α0_S _ s.2) c d
  z_comm_b c s d := pinnedA_comm hτ hF.isRoot_α0 (hF.isRoot_sub _ s.2) hα0
    (heis_gamma_pos (hF := hF) s.2) (hF.not_isRoot_α0_T _ s.2) c d
  xab_comm s t hst c d := pinnedA_comm hτ (hF.isRoot_sub _ s.2) (hF.isRoot_of_mem _ t.2)
    (heis_gamma_pos (hF := hF) s.2) (hF.pos_of_mem _ t.2)
    (by
      rw [add_comm]
      exact hF.not_isRoot_ST _ t.2 _ s.2 (fun h => hst (Subtype.ext h.symm))) c d
  comm_ss s c d := (Classical.choose_spec (exists_comm_ss_K (K := K) hτ hF s.1 s.2)).2 c d

end System

section Center

theorem heisS_nonempty (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : (heisS τ).Nonempty := by
  rw [← Finset.card_pos]
  rcases hτ with rfl | rfl | rfl
  · rw [card_heisS_E6]; decide
  · rw [card_heisS_E7]; decide
  · rw [card_heisS_E8]; decide

theorem eq_zero_of_pinnedA_mem_center (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (hS : (heisS τ).Nonempty) (c : K)
    (hc : pinnedA τ K (heisα0 τ) c ∈ Subgroup.center ↥(adjointGroup τ K)) : c = 0 := by
  obtain ⟨β, hβ⟩ := hS
  have hroot := hF.isRoot_of_mem β hβ
  have hβpos := hF.pos_of_mem β hβ
  have hlt := hF.two_height_lt β hβ
  have hne : heisα0 τ ≠ -β := fun h => by
    have := congrArg height h
    rw [height_neg'] at this
    omega
  have hne' : heisα0 τ ≠ -(-β) := fun h => by
    rw [neg_neg] at h
    have := congrArg height h
    omega
  have hsub : IsRoot τ (heisα0 τ + -β) := by
    rw [← sub_eq_add_neg]
    exact hF.isRoot_sub β hβ
  obtain ⟨hC, hf⟩ := (simply_laced_root_commutator_unit τ (simplyLaced_of hτ) hF.isRoot_α0
    (IsRoot.neg hroot) hne hne').1 hsub
  have hcomm := Subgroup.mem_center_iff.1 hc (pinnedA τ K (-β) 1)
  have h1 : ⁅pinnedX τ K (heisα0 τ) c, pinnedX τ K (-β) 1⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg (fun x : ↥(adjointGroup τ K) => (x : ModGL τ K)) hcomm).symm
  rw [hf K c 1] at h1
  have h2 := pinnedX_injective τ K _ (h1.trans (pinnedX_zero τ K _).symm)
  rcases hC with h | h
  · rw [h] at h2
    simpa using h2
  · rw [h] at h2
    simpa using h2

end Center

section Torus

theorem HSL_one_eq {F : Type} [Field F] : HSL (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL]

theorem HSL_mul_eq {F : Type} [Field F] (a b : Fˣ) : HSL (a * b) = HSL a * HSL b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] noncomputable def torusA (τ : Tag) (K : Type) [Field K] (β : Fin τ.rank → ℤ) :
    Kˣ →* ↥(adjointGroup τ K) :=
  MonoidHom.codRestrict
    { toFun := fun c => rootSL2 τ K β (HSL c)
      map_one' := by rw [HSL_one_eq, map_one]
      map_mul' := fun a b => by rw [HSL_mul_eq, map_mul] }
    (adjointGroup τ K)
    (fun c => ((exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.1 (HSL c)))

theorem iform_root_self (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : iform α α = 2 := by
  rw [← dotProduct_mulVec_eq_iform]
  exact rootForm_self (simplyLaced_of hτ) hα

theorem iform_α0_eq_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ heisS τ) : iform (heisα0 τ) β = 1 := by
  have h1 := iform_root_self hτ hF.isRoot_α0
  have h2 := iform_root_self hτ (hF.isRoot_of_mem β hβ)
  have h3 := iform_root_self hτ (hF.isRoot_sub β hβ)
  rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm β (heisα0 τ), h1, h2] at h3
  omega

theorem torusA_conj_z (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ) (c : Kˣ) (e : K) :
    torusA τ K (heisα0 τ) c * pinnedA τ K (heisα0 τ) e * (torusA τ K (heisα0 τ) c)⁻¹ =
      pinnedA τ K (heisα0 τ) (((c ^ 2 : Kˣ) : K) * e) := by
  refine pinnedA_ext ?_
  have h := rootTorusSL2_conj_pinnedX_of_isRoot (K := K) hF.isRoot_α0 hF.isRoot_α0 c e
  rw [iform_root_self hτ hF.isRoot_α0] at h
  have hexp : c ^ (2 * (2 : ℤ) / 2) = c ^ 2 := by norm_num
  rw [hexp] at h
  exact h

theorem torusA_conj_xa (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ) (c : Kˣ)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ heisS τ) (d : K) :
    torusA τ K (heisα0 τ) c * pinnedA τ K β d * (torusA τ K (heisα0 τ) c)⁻¹ =
      pinnedA τ K β ((c : K) * d) := by
  refine pinnedA_ext ?_
  have h := rootTorusSL2_conj_pinnedX_of_isRoot (K := K) hF.isRoot_α0 (hF.isRoot_of_mem β hβ) c d
  rw [iform_α0_eq_one hτ hF hβ, iform_root_self hτ hF.isRoot_α0] at h
  have hexp : c ^ (2 * (1 : ℤ) / 2) = c := by norm_num
  rw [hexp] at h
  exact h

theorem torusA_conj_xaProd (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hF : HeisFacts τ)
    (hα0 : 0 < height (heisα0 τ)) (c : Kˣ) (u : ↥(heisS τ) → K) [Fintype ↥(heisS τ)]
    [DecidableEq ↥(heisS τ)] :
    ∃ u' : ↥(heisS τ) → K,
      torusA τ K (heisα0 τ) c * heisXaProd (heisSystemK hτ hF hα0) (Multiplicative.ofAdd u) *
        (torusA τ K (heisα0 τ) c)⁻¹ =
      heisXaProd (heisSystemK hτ hF hα0) (Multiplicative.ofAdd u') := by
  have hw : u = ∑ s, Pi.single s (u s) := (Finset.univ_sum_single u).symm
  rw [hw]
  refine Finset.sum_induction _ (fun x : ↥(heisS τ) → K => ∃ u' : ↥(heisS τ) → K,
    torusA τ K (heisα0 τ) c * heisXaProd (heisSystemK hτ hF hα0) (Multiplicative.ofAdd x) *
      (torusA τ K (heisα0 τ) c)⁻¹ =
    heisXaProd (heisSystemK hτ hF hα0) (Multiplicative.ofAdd u')) ?_ ?_ ?_
  · rintro x y ⟨x', hx⟩ ⟨y', hy⟩
    refine ⟨x' + y', ?_⟩
    rw [ofAdd_add, map_mul, ofAdd_add, map_mul, ← hx, ← hy]
    group
  · exact ⟨0, by simp⟩
  · intro s _
    refine ⟨Pi.single s ((c : K) * u s), ?_⟩
    rw [heisXaProd_single, heisXaProd_single]
    exact torusA_conj_xa hτ hF c s.2 (u s)

end Torus

section Main

theorem two_pow_le_card_of_adjointE (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} (π : ↥L →* AdjointQuotient τ K)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) *
      ((Nat.card K - 1) / 2 * Nat.card K ^ (heisS τ).card / (p - 1))) ≤ Nat.card W := by
  classical
  have hF : HeisFacts τ := by
    rcases hτ with rfl | rfl | rfl
    · exact heisFacts_E6
    · exact heisFacts_E7
    · exact heisFacts_E8
  have hS := heisS_nonempty hτ
  have hα0 : 0 < height (heisα0 τ) := by
    obtain ⟨β, hβ⟩ := hS
    have h1 := hF.two_height_lt β hβ
    have h2 := hF.pos_of_mem β hβ
    omega
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K p 2).1 h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have key := two_pow_le_card_of_heisSystem hW hp2 π hπ hker hZ
    (heisSystemK (K := K) hτ hF hα0) (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K)))
    (by rw [QuotientGroup.ker_mk'])
    (fun c hc => eq_zero_of_pinnedA_mem_center hτ hF hS c hc)
    ((QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K))).comp (torusA τ K (heisα0 τ)))
    (powMonoidHom 2)
    (fun s c => by
      show QuotientGroup.mk' _ (torusA τ K (heisα0 τ) s) * QuotientGroup.mk' _
        (pinnedA τ K (heisα0 τ) c) * (QuotientGroup.mk' _ (torusA τ K (heisα0 τ) s))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg _ (torusA_conj_z hτ hF s c))
    (fun s u => by
      obtain ⟨u', hu'⟩ := torusA_conj_xaProd hτ hF hα0 s u
      refine ⟨u', ?_⟩
      show QuotientGroup.mk' _ (torusA τ K (heisα0 τ) s) * QuotientGroup.mk' _ _ *
        (QuotientGroup.mk' _ (torusA τ K (heisα0 τ) s))⁻¹ = _
      rw [← map_inv, ← map_mul, ← map_mul, hu'])
  rwa [card_range_powMonoidHom_two h2, Nat.card_fun, Nat.card_eq_fintype_card (α := ↥(heisS τ)),
    Fintype.card_coe] at key

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
