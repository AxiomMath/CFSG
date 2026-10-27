module

public import CFSG.HardMathSupport.Lang.D4Three.CharThreeData
public import CFSG.HardMathSupport.Lang.D4Three.StableSylow
public import CFSG.Quasithin.H13.NQCatLieCartanG2
public import CFSG.HardMathSupport.Lang.D4Three.BorelLayers
public import CFSG.HardMathSupport.Lang.D4Three.DiagSquare

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K]

theorem permLattice_injective' {τ : Tag} (π : Equiv.Perm (Fin τ.rank)) :
    Function.Injective (permLattice π : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) := by
  intro v w h
  funext i
  have := congrFun h (π i)
  simpa [permLattice] using this

@[expose] def d4LayerAct {β : MulAut ↥(adjointGroup Tag.D4 K)} {g : ModGL Tag.D4 K} (hg : BorelScalar g)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (hβ : ∀ x : ↥(adjointGroup Tag.D4 K),
      ((β x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = g * d4F K a σ ε (x : ModGL Tag.D4 K) * g⁻¹) :
    LayerAct Tag.D4 β σ :=
  layerAct_of_borel_monomial hg (d4F K a σ ε) (permLattice (d4Rho ^ ε))
    (exists_d4F_pinnedX a σ ε).choose σ
    (fun γ hγ => isRoot_permLattice_d4Rho_pow hγ ε)
    (fun γ => height_permLattice _ _) (fun γ γ' _ _ h => permLattice_injective' _ h)
    (exists_d4F_pinnedX a σ ε).choose_spec hβ
    (fun k δ => ⟨permLattice (d4Rho ^ (2 * ε)) δ.1,
      isRoot_permLattice_d4Rho_pow δ.2.1 _, by rw [height_permLattice]; exact δ.2.2⟩)
    (fun k δ => by
      change permLattice (d4Rho ^ ε) (permLattice (d4Rho ^ (2 * ε)) δ.1) = δ.1
      rw [← permLattice_mul', ← pow_add, show ε + 2 * ε = 3 * ε by ring, pow_mul, d4Rho_pow_three,
        one_pow, permLattice_one'])

theorem d4F_one_apply (a : Fin Tag.D4.rank → Kˣ) (x : ModGL Tag.D4 K) :
    d4F K a (1 : K ≃+* K) 0 x = rootDiagUnit Tag.D4 a * x * (rootDiagUnit Tag.D4 a)⁻¹ := by
  have e : d4F K a (1 : K ≃+* K) 0 x =
      exactNormalAutGL Tag.D4 K a 1 0 (d4P K ^ 0 * x * (d4P K ^ 0)⁻¹) := rfl
  rw [e, exactNormalAutGL_apply]
  have hQ : exactQ Tag.D4 K 0 = 1 := rfl
  rw [hQ]
  have hid : Units.map (entrywiseHom ((1 : K ≃+* K).toRingHom)) x = x := by
    refine Units.ext ?_
    exact entrywise_id _
  simp only [pow_zero, one_mul, inv_one, mul_one]
  rw [hid]

theorem mem_inner_of_normal_form_one {g : ↥(adjointGroup Tag.D4 K)} {a : Fin Tag.D4.rank → Kˣ}
    {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 0))
    (hα3 : α ^ 3 = 1) : α ∈ inner ↥(adjointGroup Tag.D4 K) := by
  set w : ModGL Tag.D4 K := (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a with hw
  have hαx : ∀ x : ↥(adjointGroup Tag.D4 K), ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      w * (x : ModGL Tag.D4 K) * w⁻¹ := by
    intro x
    rw [hα]
    change (g : ModGL Tag.D4 K) * d4F K a 1 0 (x : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K)⁻¹ = _
    rw [d4F_one_apply, hw]
    group
  have hwΓ : w ∈ inndiagGroup Tag.D4 K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  have hw2 : w ^ 2 ∈ adjointGroup Tag.D4 K := sq_mem_adjointGroup_of_mem_inndiagGroup hwΓ
  have hw3 : ∀ x : ↥(adjointGroup Tag.D4 K), w ^ 3 * (x : ModGL Tag.D4 K) * (w ^ 3)⁻¹ = x := by
    intro x
    have h3 := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => ((φ x : ↥(adjointGroup Tag.D4 K)) :
      ModGL Tag.D4 K)) hα3
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h3
    rw [hαx, hαx, hαx] at h3
    calc w ^ 3 * (x : ModGL Tag.D4 K) * (w ^ 3)⁻¹
        = w * (w * (w * (x : ModGL Tag.D4 K) * w⁻¹) * w⁻¹) * w⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      _ = x := h3
  refine ⟨⟨(w ^ 2)⁻¹, inv_mem hw2⟩, ?_⟩
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.conj_apply, hαx]
  change (w ^ 2)⁻¹ * (x : ModGL Tag.D4 K) * ((w ^ 2)⁻¹)⁻¹ = _
  have h := hw3 x
  calc (w ^ 2)⁻¹ * (x : ModGL Tag.D4 K) * ((w ^ 2)⁻¹)⁻¹
      = (w ^ 2)⁻¹ * (w ^ 3 * (x : ModGL Tag.D4 K) * (w ^ 3)⁻¹) * ((w ^ 2)⁻¹)⁻¹ := by rw [h]
    _ = w * (x : ModGL Tag.D4 K) * w⁻¹ := by group

@[expose] def goodRoot : ℕ → (Fin Tag.D4.rank → ℤ)
  | 0 => ![1, 0, 0, 0]
  | 1 => ![1, 0, 1, 0]
  | _ => ![1, 1, 1, 0]

theorem goodRoot_mem_rootFinset : ∀ k : Fin 3, goodRoot k ∈ rootFinset Tag.D4 := by
  decide +kernel

theorem goodRoot_height : ∀ k : Fin 3, height (goodRoot k) = (((k : ℕ) + 1 : ℕ) : ℤ) := by
  decide +kernel

theorem goodRoot_spec (k : Fin 3) : IsRoot Tag.D4 (goodRoot k) ∧
    height (goodRoot k) = (((k : ℕ) + 1 : ℕ) : ℤ) :=
  ⟨mem_rootFinset.1 (goodRoot_mem_rootFinset k), goodRoot_height k⟩

theorem goodRoot_moved : ∀ (k : Fin 3) (ε : Fin 3), ε ≠ 0 →
    permLattice (d4Rho ^ (2 * (ε : ℕ))) (goodRoot k) ≠ goodRoot k ∧
    permLattice (d4Rho ^ (2 * (ε : ℕ))) (permLattice (d4Rho ^ (2 * (ε : ℕ))) (goodRoot k)) ≠
      goodRoot k := by
  decide +kernel

theorem two_lt_maxHeight : 2 < (maxHeight Tag.D4).toNat := by
  have hr : IsRoot Tag.D4 (goodRoot 2) := (goodRoot_spec 2).1
  have hh : height (goodRoot 2) = 3 := by simpa using (goodRoot_spec 2).2
  have := height_le_maxHeight (τ := Tag.D4) hr (by rw [hh]; norm_num)
  rw [hh] at this
  omega

theorem unitN_zero_eq_subgroupOf :
    unitN Tag.D4 K 0 = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) := by
  ext x
  rw [mem_unitN, Subgroup.mem_subgroupOf]
  have : (((0 + 1 : ℕ) : ℤ)) = 1 := by norm_num
  rw [this, heightSeries_one]

variable [CharP K 3]

theorem twentySeven_dvd_fixedSubgroup_D4_char3_stable
    (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner ↥(adjointGroup Tag.D4 K))
    (H : Subgroup ↥(adjointGroup Tag.D4 K))
    (hH : H = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hU : H.map α.toMonoidHom = H) (hSyl : IsPGroup 3 H) :
    27 ∣ Nat.card ↥(fixedSubgroup α) := by
  classical
  have hmemH : ∀ y : ↥(adjointGroup Tag.D4 K), y ∈ H ↔ (y : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K :=
    fun y => by rw [hH, Subgroup.mem_subgroupOf]
  obtain ⟨g, a, σ, ε, hε3, hαeq⟩ := exists_cube_normal_form α hα3
  have hνA : (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∈ unipotentPairAut Tag.D4 K :=
    mul_mem (exactNormalAut_mem a σ 0) (d4Graph_mem ε)
  have hνH : H.map (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε).toMonoidHom = H := by
    rw [hH]; exact hνA.1
  have hgeq : MulAut.conj g = α * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)⁻¹ := by
    rw [hαeq]; group
  have hgH : H.map (MulAut.conj g).toMonoidHom = H := by
    rw [hgeq, map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq hνH, hU]
  have hgH' : H.map (MulAut.conj g)⁻¹.toMonoidHom = H := map_inv_toMonoidHom_of_map_eq hgH
  have hnorm : (g : ModGL Tag.D4 K) ∈
      Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxG : x ∈ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup hx
      have hmem : (⟨x, hxG⟩ : ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj g) ⟨x, hxG⟩ ∈ H.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH] at h1
      exact (hmemH _).1 h1
    · intro hx
      have hxG' : (g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹ ∈ adjointGroup Tag.D4 K :=
        posUnipotent_le_adjointGroup hx
      have hxG : x ∈ adjointGroup Tag.D4 K := by
        have := mul_mem (mul_mem (inv_mem g.2) hxG') g.2
        simpa [mul_assoc] using this
      have hmem : (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) ∈ H := (hmemH _).2 hx
      have h1 : (MulAut.conj g)⁻¹ ⟨_, hxG'⟩ ∈ H.map (MulAut.conj g)⁻¹.toMonoidHom :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hgH'] at h1
      have e : (MulAut.conj g)⁻¹ (⟨(g : ModGL Tag.D4 K) * x * (g : ModGL Tag.D4 K)⁻¹, hxG'⟩ :
          ↥(adjointGroup Tag.D4 K)) = ⟨x, hxG⟩ := by
        apply Subtype.ext
        simp [MulAut.conj_apply, mul_assoc]
      rw [e] at h1
      exact (hmemH _).1 h1
  have hgB : (g : ModGL Tag.D4 K) ∈ borelGroup Tag.D4 K := by
    rw [← CFSG.Quasithin.H13.NQCat.LieCartan.G2.normalizer_posUnipotent_inf_eq
      (K := K) (τ := Tag.D4)]
    exact ⟨hnorm, g.2⟩
  have hg := borelScalar_of_mem_borelGroup hgB
  have hβ : ∀ x : ↥(adjointGroup Tag.D4 K), ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      (g : ModGL Tag.D4 K) * d4F K a σ ε (x : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K)⁻¹ := by
    intro x
    rw [hαeq]
    rfl
  let la := d4LayerAct hg a σ ε hβ
  have hS : ∀ k ∈ ({0, 1, 2} : Finset ℕ), k < (maxHeight Tag.D4).toNat ∧
      ∃ j₀ : UnitRoots Tag.D4 k, ∃ b, monoN (la.r k) (la.f k) σ b j₀ ≠ 0 := by
    intro k hk
    have hk3 : k < 3 := by simp at hk; omega
    refine ⟨by have := two_lt_maxHeight; omega, ?_⟩
    let j₀ : UnitRoots Tag.D4 k :=
      ⟨goodRoot k, (goodRoot_spec ⟨k, hk3⟩).1, (goodRoot_spec ⟨k, hk3⟩).2⟩
    refine ⟨j₀, ?_⟩
    by_cases hε0 : ε = 0
    · subst hε0
      by_cases hσ : σ = 1
      · subst hσ
        exact absurd (mem_inner_of_normal_form_one hαeq hα3) hαin
      · refine monoN_coord_ne_zero_of_fixed (la.r k) (la.f k) σ ?_ hσ
        refine Subtype.ext ?_
        change permLattice (d4Rho ^ (2 * 0)) (goodRoot k) = goodRoot k
        simp [permLattice_one']
    · have hε' : (⟨ε, hε3⟩ : Fin 3) ≠ 0 := by
        intro h
        exact hε0 (by simpa using congrArg Fin.val h)
      obtain ⟨h1, h2⟩ := goodRoot_moved ⟨k, hk3⟩ ⟨ε, hε3⟩ hε'
      refine monoN_coord_ne_zero_of_cycle (la.r k) (la.f k) σ ?_ ?_
      · intro h
        exact h1 (congrArg Subtype.val h)
      · intro h
        exact h2 (congrArg Subtype.val h)
  have hge := card_fixed_unitN_zero_ge la hα3 {0, 1, 2} hS
  set S' : Subgroup ↥(adjointGroup Tag.D4 K) := unitN Tag.D4 K 0 ⊓ fixedSubgroup α with hS'
  have hS'c : Nat.card S' =
      Nat.card {x : ↥(adjointGroup Tag.D4 K) // x ∈ unitN Tag.D4 K 0 ∧ α x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Subgroup.mem_inf)
  have hS'p : IsPGroup 3 S' := by
    refine hSyl.to_le ?_
    rw [hH, ← unitN_zero_eq_subgroupOf]
    exact inf_le_left
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card.1 hS'p)
  have h27 : 27 ≤ 3 ^ j := by
    rw [← hj, hS'c]
    simpa using hge
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have : 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le (inf_le_right : S' ≤ fixedSubgroup α))
  rw [hj]
  exact (pow_dvd_pow 3 hj3 : 3 ^ 3 ∣ 3 ^ j)

omit
  [Field K] [Finite K] [CharP K 3] in
theorem card_fixedSubgroup_conj' {G : Type*} [Group G] (h : G) (α : MulAut G) :
    Nat.card (fixedSubgroup (MulAut.conj h⁻¹ * α * MulAut.conj h)) =
      Nat.card (fixedSubgroup α) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨h * x.1 * h⁻¹, ?_⟩
      invFun := fun y => ⟨h⁻¹ * y.1 * h, ?_⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  · have hx : (MulAut.conj h⁻¹ * α * MulAut.conj h) x.1 = x.1 := x.2
    simp only [MulAut.mul_apply, MulAut.conj_apply] at hx
    change α (h * x.1 * h⁻¹) = h * x.1 * h⁻¹
    have := congrArg (fun z => h * z * h⁻¹) hx
    simpa [mul_assoc] using this
  · have hy : α y.1 = y.1 := y.2
    change (MulAut.conj h⁻¹ * α * MulAut.conj h) (h⁻¹ * y.1 * h) = h⁻¹ * y.1 * h
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    have e : h * (h⁻¹ * y.1 * h) * h⁻¹ = y.1 := by group
    rw [e, hy]
    group

theorem twentySeven_dvd_fixedSubgroup_D4_char3
    (α : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner ↥(adjointGroup Tag.D4 K)) :
    27 ∣ Nat.card ↥(fixedSubgroup α) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := exists_stable_sylow_of_order_three α hα3
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition Tag.D4 K 3 w₀ hw₀
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (adjointGroup Tag.D4 K) P S
  have hSeq : (S : Subgroup ↥(adjointGroup Tag.D4 K)) =
      (P : Subgroup ↥(adjointGroup Tag.D4 K)).map (MulAut.conj h).toMonoidHom := by
    rw [← hh, Sylow.coe_subgroup_smul]
    rfl
  set H : Subgroup ↥(adjointGroup Tag.D4 K) := (P : Subgroup ↥(adjointGroup Tag.D4 K)) with hHdef
  set c : MulAut ↥(adjointGroup Tag.D4 K) := MulAut.conj h with hc
  have hcinv : MulAut.conj h⁻¹ = c⁻¹ := map_inv MulAut.conj h
  have hα'eq : MulAut.conj h⁻¹ * α * MulAut.conj h = c⁻¹ * α * c := by rw [hcinv]
  have hα'3 : (MulAut.conj h⁻¹ * α * MulAut.conj h) ^ 3 = 1 := by
    rw [hα'eq]
    have : (c⁻¹ * α * c⁻¹⁻¹) ^ 3 = c⁻¹ * α ^ 3 * c⁻¹⁻¹ := conj_pow
    rw [inv_inv] at this
    rw [this, hα3]
    simp
  have hα'in : (MulAut.conj h⁻¹ * α * MulAut.conj h) ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(adjointGroup Tag.D4 K) := by
    rintro ⟨y, hy⟩
    apply hαin
    refine ⟨h * y * h⁻¹, ?_⟩
    have e : MulAut.conj (h * y * h⁻¹) = c * MulAut.conj y * c⁻¹ := by
      rw [map_mul, map_mul, hcinv]
    rw [e, hy, hα'eq]
    group
  have hU : H.map (MulAut.conj h⁻¹ * α * MulAut.conj h).toMonoidHom = H := by
    rw [hα'eq, map_toMonoidHom_mul_mulAut, map_toMonoidHom_mul_mulAut]
    have h1 : H.map c.toMonoidHom = (S : Subgroup _) := hSeq.symm
    rw [h1, hS]
    exact map_inv_toMonoidHom_of_map_eq h1
  have key := twentySeven_dvd_fixedSubgroup_D4_char3_stable
    (MulAut.conj h⁻¹ * α * MulAut.conj h) hα'3 hα'in H hP hU P.isPGroup'
  rwa [card_fixedSubgroup_conj'] at key

end CFSG.HardMathSupport.Lang.D4Three
