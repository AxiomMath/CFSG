module

public import CFSG.LieType.Simplicity.TitsSimple
public import CFSG.LieType.Simplicity.TitsElements
public import CFSG.LieType.Simplicity.ReeLargeModel

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree ReeTag
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem weylElement_conj_xElement_mem_U
    {τ : Tag} {i j : Fin τ.rank}
    (hpos : 0 < height ((simple τ i) • simpleRoot τ j).1) (c : K) :
    weylElement τ K i * xElement j c * (weylElement τ K i)⁻¹ ∈ (nativeData τ K).U := by
  have hx : xElement j c ∈ (nativeData τ K).X (simpleRoot τ j) :=
    ((nativeRootSubgroups τ K).mem_simple j _).2 ⟨c, rfl⟩
  have h := RootGroupData.conj_mem (D := nativeData τ K) ((nativeData τ K).n i) hx
  rw [(nativeData τ K).φ_n] at h
  exact (nativeData τ K).X_le_U hpos h

theorem xElement_mem_U
    {τ : Tag} (j : Fin τ.rank) (c : K) :
    xElement j c ∈ (nativeData τ K).U :=
  (nativeData τ K).X_le_U (by simp [simpleRoot, height])
    (((nativeRootSubgroups τ K).mem_simple j _).2 ⟨c, rfl⟩)

theorem titsG1_mem_U :
    titsG1 K ∈ (nativeData ReeTag.F4.tag K).U := by
  refine mul_mem (mul_mem (xElement_mem_U _ _) (xElement_mem_U _ _)) ?_
  exact weylElement_conj_xElement_mem_U (by decide) 1

variable [CharP K ReeTag.F4.prime]

theorem titsZ1_mem_reeFixed :
    titsZ1 K ∈ reeFixed ReeTag.F4 K 0 :=
  nrep_mem_reeFixed ReeTag.F4 K 0 (reeOrbitWord_mem ReeTag.F4 (0 : Fin 4))

theorem titsZ2_mem_reeFixed :
    titsZ2 K ∈ reeFixed ReeTag.F4 K 0 :=
  nrep_mem_reeFixed ReeTag.F4 K 0 (reeOrbitWord_mem ReeTag.F4 (1 : Fin 4))

theorem mem_commutator_of_conj_mem
    {x y : reeFixed ReeTag.F4 K 0}
    (h : x * y * x⁻¹ ∈ commutator (reeFixed ReeTag.F4 K 0)) :
    y ∈ commutator (reeFixed ReeTag.F4 K 0) := by
  have hN : (commutator (reeFixed ReeTag.F4 K 0)).Normal := Subgroup.commutator_normal ⊤ ⊤
  have := hN.conj_mem _ h x⁻¹
  simpa [mul_assoc] using this

variable (K) in
noncomputable def titsData
    (hK : Nat.card K = 2) : TitsData K where
  g₀ := ⟨titsG0 K, titsG0_mem_reeFixed⟩
  g₁ := ⟨titsG1 K, titsG1_mem_reeFixed⟩
  fixed₀ := fun _ hy hF => eq_one_or_eq_titsG0 hK hy hF
  fixed₁ := fun _ hy hF => mem_zpowers_titsG1 hK hy hF
  g₀_mul_self := Subtype.ext titsG0_mul_self
  g₀_ne_one := fun h => titsG0_ne_one (congrArg Subtype.val h)
  g₁_mem_U := titsG1_mem_U
  g₀_mem := by
    set z₁ : reeFixed ReeTag.F4 K 0 := ⟨titsZ1 K, titsZ1_mem_reeFixed⟩
    set z₂ : reeFixed ReeTag.F4 K 0 := ⟨titsZ2 K, titsZ2_mem_reeFixed⟩
    set g₁ : reeFixed ReeTag.F4 K 0 := ⟨titsG1 K, titsG1_mem_reeFixed⟩
    refine mem_commutator_of_conj_mem (x := z₁) ?_
    have h : z₁ * ⟨titsG0 K, titsG0_mem_reeFixed⟩ * z₁⁻¹ = ⁅(z₁ * z₂) * g₁ * (z₁ * z₂)⁻¹, g₁⁆ :=
      Subtype.ext tits_R2.symm
    rw [h]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  g₁_sq_mem := by
    set z₁ : reeFixed ReeTag.F4 K 0 := ⟨titsZ1 K, titsZ1_mem_reeFixed⟩
    set z₂ : reeFixed ReeTag.F4 K 0 := ⟨titsZ2 K, titsZ2_mem_reeFixed⟩
    set g₀ : reeFixed ReeTag.F4 K 0 := ⟨titsG0 K, titsG0_mem_reeFixed⟩
    set g₁ : reeFixed ReeTag.F4 K 0 := ⟨titsG1 K, titsG1_mem_reeFixed⟩
    refine mem_commutator_of_conj_mem (x := z₂) ?_
    have h : z₂ * g₁ ^ 2 * z₂⁻¹ = ⁅z₁ * g₁ * z₁⁻¹, (z₂ * z₁) * g₀ * (z₂ * z₁)⁻¹⁆ :=
      Subtype.ext tits_R1.symm
    rw [h]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  nonabelian := by
    set z₁ : reeFixed ReeTag.F4 K 0 := ⟨titsZ1 K, titsZ1_mem_reeFixed⟩
    set g₀ : reeFixed ReeTag.F4 K 0 := ⟨titsG0 K, titsG0_mem_reeFixed⟩
    have hg₀ : g₀ ∈ commutator (reeFixed ReeTag.F4 K 0) := by
      set z₂ : reeFixed ReeTag.F4 K 0 := ⟨titsZ2 K, titsZ2_mem_reeFixed⟩
      set g₁ : reeFixed ReeTag.F4 K 0 := ⟨titsG1 K, titsG1_mem_reeFixed⟩
      refine mem_commutator_of_conj_mem (x := z₁) ?_
      have h : z₁ * g₀ * z₁⁻¹ = ⁅(z₁ * z₂) * g₁ * (z₁ * z₂)⁻¹, g₁⁆ := Subtype.ext tits_R2.symm
      rw [h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    refine ⟨⁅g₀, z₁⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _), g₀, hg₀, fun h => tits_W (congrArg Subtype.val h)⟩

theorem fam_tits_simplicity
    (G : Type) [Group G] (p f : ℕ)
    (h : CFSG.Blueprint.ReeTitsModel G .Tits p f) : Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have ha : a = 0 := by omega
  subst ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card K = 2 := by rw [hK, hf1, pow_one]
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K ReeTag.F4.prime := hc
  have hQ := (titsData K hK2).isQuasisimple hK2
  have e' := e.trans (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 K 0)).trans
      ((reeFixed ReeTag.F4 K 0).equivMapOfInjective _ Subtype.val_injective).symm))
  have := hQ.2.1
  have : Nontrivial G := e'.toEquiv.nontrivial
  exact ⟨inferInstance, IsSimpleGroup.isSimpleGroup_of_surjective e'.symm.toMonoidHom
    e'.symm.surjective⟩

theorem fam_ree_tits_simplicity
    (G : Type) [Group G] (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (p f : ℕ) (h : CFSG.Blueprint.ReeTitsModel G t p f) : Nontrivial G ∧ IsSimpleGroup G := by
  cases t with
  | twistedG2 => exact fam_2g2_simplicity G p f h
  | twistedF4 => exact fam_2f4_simplicity G p f h
  | Tits => exact fam_tits_simplicity G p f h
  | _ =>
    obtain ⟨-, a, -, h'⟩ := h
    exact h'.elim

end CFSG.LieType.Simplicity
