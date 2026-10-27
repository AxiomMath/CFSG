module

public import CFSG.ClassicalGroups.Alternating.RT1SpFaithful
public import CFSG.ClassicalGroups.Orthogonal.SiegelI4CoplPoint

public section

namespace CFSG.ClassicalGroups.Alternating

open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}

omit [FiniteDimensional K N] in
private theorem isotropic_span_range_of_pairwise {ι : Type*} [Fintype ι] {v : ι → N}
    (hv : ∀ i j, BN (v i) (v j) = 0) :
    ∀ x ∈ Submodule.span K (Set.range v), ∀ y ∈ Submodule.span K (Set.range v), BN x y = 0 := by
  intro x hx y hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  simp [map_sum, hv]

theorem exists_isCompl_isPlane (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (h6 : finrank K N = 6) :
    ∃ π₀ π₀' : Submodule K N, IsCompl π₀ π₀' ∧ IsPlane BN π₀ ∧ IsPlane BN π₀' := by
  obtain ⟨n, b, hn, hb⟩ :=
    CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hBN hBNnd
  obtain rfl : n = 3 := by omega
  have hli₁ : LinearIndependent K (fun i : Fin 3 => b (Sum.inl i)) :=
    b.linearIndependent.comp Sum.inl Sum.inl_injective
  have hli₂ : LinearIndependent K (fun i : Fin 3 => b (Sum.inr i)) :=
    b.linearIndependent.comp Sum.inr Sum.inr_injective
  have hfr₁ := finrank_span_eq_card hli₁
  have hfr₂ := finrank_span_eq_card hli₂
  rw [Fintype.card_fin] at hfr₁ hfr₂
  have hcod : Submodule.span K (Set.range (fun i : Fin 3 => b (Sum.inl i))) ⊔
      Submodule.span K (Set.range (fun i : Fin 3 => b (Sum.inr i))) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases i with i | i
    · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_range_self i))
    · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range_self i))
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K (Set.range (fun i : Fin 3 => b (Sum.inl i))))
    (Submodule.span K (Set.range (fun i : Fin 3 => b (Sum.inr i))))
  rw [hcod, finrank_top, h6, hfr₁, hfr₂] at hfin
  have hbot : Submodule.span K (Set.range (fun i : Fin 3 => b (Sum.inl i))) ⊓
      Submodule.span K (Set.range (fun i : Fin 3 => b (Sum.inr i))) = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  exact ⟨_, _, ⟨disjoint_iff.mpr hbot, codisjoint_iff.mpr hcod⟩,
    ⟨isotropic_span_range_of_pairwise hb.1, hfr₁⟩,
    ⟨isotropic_span_range_of_pairwise hb.2.1, hfr₂⟩⟩

end CFSG.ClassicalGroups.Alternating

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {K : Type} [Field K] [Finite K]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
private lemma map_subtype_comap_of_le {A X : Submodule K V} (h : X ≤ A) :
    Submodule.map A.subtype (Submodule.comap A.subtype X) = X := by
  rw [Submodule.map_comap_subtype, inf_eq_right.2 h]

omit [FiniteDimensional K V] in
theorem exists_eq_of_injective_points {A : Submodule K V} (hA : finrank K A = 2)
    {S : Type*} (hS : Nat.card S = Nat.card K + 1) (f : S → Submodule K V)
    (hf1 : ∀ s, finrank K (f s) = 1) (hfA : ∀ s, f s ≤ A) (hinj : Function.Injective f)
    {P : Submodule K V} (hP1 : finrank K P = 1) (hPA : P ≤ A) : ∃ s, f s = P := by
  have hT : Nat.card {H : Submodule K ↥A // finrank K H = 1} = Nat.card K + 1 :=
    (Nat.card_congr (Projectivization.equivSubmodule K ↥A)).symm.trans
      (Projectivization.card_of_finrank_two K ↥A hA)
  have hTfin : Finite {H : Submodule K ↥A // finrank K H = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hT]; omega)
  let g : S → {H : Submodule K ↥A // finrank K H = 1} := fun s =>
    ⟨(f s).comap A.subtype, (Submodule.comapSubtypeEquivOfLe (hfA s)).finrank_eq.trans (hf1 s)⟩
  have hg : Function.Injective g := by
    intro s t hst
    have h1 : (f s).comap A.subtype = (f t).comap A.subtype := congrArg Subtype.val hst
    apply hinj
    rw [← map_subtype_comap_of_le (hfA s), h1, map_subtype_comap_of_le (hfA t)]
  have hbij : Function.Bijective g := hg.bijective_of_nat_card_le (hT.trans hS.symm).le
  let Q : {H : Submodule K ↥A // finrank K H = 1} :=
    ⟨P.comap A.subtype, (Submodule.comapSubtypeEquivOfLe hPA).finrank_eq.trans hP1⟩
  obtain ⟨s, hs⟩ := hbij.2 Q
  refine ⟨s, ?_⟩
  have h1 : (f s).comap A.subtype = P.comap A.subtype := congrArg Subtype.val hs
  rw [← map_subtype_comap_of_le (hfA s), h1, map_subtype_comap_of_le hPA]

@[expose] def trivMod (ρ : Gsp BN →* (V ≃ₗ[K] V)) (Y : Submodule K V) : Subgroup (Gsp BN) where
  carrier := {g | ∀ v, ρ g v - v ∈ Y}
  one_mem' := fun v => by simp
  mul_mem' := fun {g h} hg hh v => by
    have := Y.add_mem (hg (ρ h v)) (hh v)
    simpa [map_mul] using this
  inv_mem' := fun {g} hg v => by
    have := Y.neg_mem (hg (ρ g⁻¹ v))
    simpa [map_inv] using this

@[expose] def stabSub (ρ : Gsp BN →* (V ≃ₗ[K] V)) (P : Submodule K V) : Subgroup (Gsp BN) where
  carrier := {g | P.map (ρ g : V →ₗ[K] V) = P}
  one_mem' := by
    show P.map ((ρ 1 : V ≃ₗ[K] V) : V →ₗ[K] V) = P
    rw [map_one]
    exact Submodule.map_id P
  mul_mem' := fun {g h} hg hh => by
    have e : ((ρ (g * h) : V ≃ₗ[K] V) : V →ₗ[K] V) =
        (ρ g : V →ₗ[K] V) ∘ₗ (ρ h : V →ₗ[K] V) := by
      ext x
      simp
    show P.map ((ρ (g * h) : V ≃ₗ[K] V) : V →ₗ[K] V) = P
    rw [e, Submodule.map_comp]
    have hh' : P.map (ρ h : V →ₗ[K] V) = P := hh
    have hg' : P.map (ρ g : V →ₗ[K] V) = P := hg
    rw [hh', hg']
  inv_mem' := fun {g} hg => by
    have e : (ρ g⁻¹ : V →ₗ[K] V) ∘ₗ (ρ g : V →ₗ[K] V) = LinearMap.id := by
      ext x
      simp [← LinearEquiv.mul_apply]
    have hg' : P.map (ρ g : V →ₗ[K] V) = P := hg
    show P.map ((ρ g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) = P
    have := congrArg (Submodule.map (ρ g⁻¹ : V →ₗ[K] V)) hg'
    rw [← Submodule.map_comp, e, Submodule.map_id] at this
    exact this.symm

omit [Finite K] [FiniteDimensional K N] [FiniteDimensional K V] in
theorem mem_stabSub {ρ : Gsp BN →* (V ≃ₗ[K] V)} {P : Submodule K V} {g : Gsp BN} :
    g ∈ stabSub ρ P ↔ P.map (ρ g : V →ₗ[K] V) = P := Iff.rfl

section Basic

variable [CharP K 2] {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}
  (hs : I4Setting hBN Qf ρ)

include hs

theorem eq_top_of_forall_lineElt_mem (T : Subgroup (Gsp BN))
    (hT : ∀ a c : N, BN a c = 0 → LinearIndependent K ![a, c] → lineElt hBN a c ∈ T) :
    T = ⊤ := by
  have hNpos : 0 < finrank K N := by have := hs.dimN; omega
  have : Nontrivial N := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨a₁, ha₁⟩ := exists_ne (0 : N)
  obtain ⟨ℓ, hℓ, -⟩ := exists_isLine_of_ne_zero hBN hs.nondegN hs.dimN ha₁
  obtain ⟨a₀, c₀, hac₀, hind₀, -⟩ := hℓ.exists_pair
  have : IsSimpleGroup (Gsp BN) :=
    isSimpleGroup_Gsp hs.card hBN hs.nondegN (by have := hs.dimN; omega)
  have hx1 : lineElt hBN a₀ c₀ ≠ 1 := lineElt_ne_one hBN hs.nondegN hac₀ hind₀
  have htop : Subgroup.normalClosure {lineElt hBN a₀ c₀} = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.normalClosure {lineElt hBN a₀ c₀}) with
      h | h
    · exfalso
      apply hx1
      have : lineElt hBN a₀ c₀ ∈ Subgroup.normalClosure {lineElt hBN a₀ c₀} :=
        Subgroup.subset_normalClosure rfl
      rw [h] at this
      exact (Subgroup.mem_bot.mp this)
    · exact h
  have hle : Subgroup.normalClosure {lineElt hBN a₀ c₀} ≤ T := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨x', hx', hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    rw [Set.mem_singleton_iff.mp hx'] at hc
    rw [← hc, SetLike.mem_coe, conj_lineElt hBN c a₀ c₀]
    refine hT _ _ (by rw [Gsp.form_app]; exact hac₀) ?_
    have h := hind₀.map' c.lin (LinearMap.ker_eq_bot.mpr (Gsp.lin_injective c))
    convert h using 1
    ext i
    fin_cases i <;> rfl
  exact top_le_iff.mp (htop ▸ hle)

theorem iSup_famSpace_isLine :
    (⨆ (ℓ : Submodule K N) (_ : IsLine BN ℓ), famSpace hBN ρ ℓ) = ⊤ := by
  set U : Submodule K V := ⨆ (ℓ : Submodule K N) (_ : IsLine BN ℓ), famSpace hBN ρ ℓ with hU
  have hMline : ∀ a c : N, BN a c = 0 → LinearIndependent K ![a, c] →
      lineElt hBN a c ∈ trivMod ρ U := by
    intro a c hac hind v
    have hℓ := isLine_span_pair hBN hac hind
    have hg : lineElt hBN a c ∈ planeGroup hBN (Submodule.span K {a, c}) :=
      lineElt_mem_planeGroup hBN (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    exact (le_iSup₂ (f := fun (ℓ : Submodule K N) (_ : IsLine BN ℓ) => famSpace hBN ρ ℓ) _ hℓ)
      (movedSpace_le_famSpace hBN ρ hg (sub_mem_movedSpace _ v))
  have hMtop : ∀ g : Gsp BN, g ∈ trivMod ρ U := fun g =>
    (eq_top_of_forall_lineElt_mem hs _ hMline) ▸ Subgroup.mem_top g
  have hcomm : commutatorSpace ρ.range ≤ U := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, ⟨g, rfl⟩, v, rfl⟩
    exact hMtop g v
  rw [hs.gen] at hcomm
  exact top_le_iff.mp hcomm

end Basic

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
