module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathOffender
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.QuasithinUnique

section Cube

variable {W : Type*} [CommGroup W] {ι : Type*} {I : ι → Subgroup W}

@[expose] noncomputable def cubeBase (hF : PlaneFamily I) : Subgroup (MulAut W) where
  carrier := {g | ∃ hg : g ∈ baseGp I, ∀ i, resPlane I i ⟨g, hg⟩ ^ 3 = 1}
  one_mem' := ⟨(baseGp I).one_mem, fun i => by
    have : (⟨1, (baseGp I).one_mem⟩ : ↥(baseGp I)) = 1 := rfl
    rw [this, map_one, one_pow]⟩
  mul_mem' := by
    rintro g g' ⟨hg, h⟩ ⟨hg', h'⟩
    refine ⟨(baseGp I).mul_mem hg hg', fun i => ?_⟩
    have := hF.klein i
    have : (⟨g * g', (baseGp I).mul_mem hg hg'⟩ : ↥(baseGp I)) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
    rw [this, map_mul]
    exact pow_three_mul (h i) (h' i)
  inv_mem' := by
    rintro g ⟨hg, h⟩
    refine ⟨(baseGp I).inv_mem hg, fun i => ?_⟩
    have : (⟨g⁻¹, (baseGp I).inv_mem hg⟩ : ↥(baseGp I)) = (⟨g, hg⟩ : ↥(baseGp I))⁻¹ := rfl
    rw [this, map_inv, inv_pow, h i, inv_one]

@[expose] noncomputable def cubeAt (hF : PlaneFamily I) (i : ι) : Subgroup (MulAut W) where
  carrier := {g | ∃ hg : g ∈ baseGp I, (∀ j, j ≠ i → resPlane I j ⟨g, hg⟩ = 1) ∧
    resPlane I i ⟨g, hg⟩ ^ 3 = 1}
  one_mem' := ⟨(baseGp I).one_mem, fun j _ => by
    have : (⟨1, (baseGp I).one_mem⟩ : ↥(baseGp I)) = 1 := rfl
    rw [this, map_one], by
    have : (⟨1, (baseGp I).one_mem⟩ : ↥(baseGp I)) = 1 := rfl
    rw [this, map_one, one_pow]⟩
  mul_mem' := by
    rintro g g' ⟨hg, h1, h2⟩ ⟨hg', h1', h2'⟩
    refine ⟨(baseGp I).mul_mem hg hg', fun j hj => ?_, ?_⟩
    · have : (⟨g * g', (baseGp I).mul_mem hg hg'⟩ : ↥(baseGp I)) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
      rw [this, map_mul, h1 j hj, h1' j hj, mul_one]
    · have := hF.klein i
      have : (⟨g * g', (baseGp I).mul_mem hg hg'⟩ : ↥(baseGp I)) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
      rw [this, map_mul]
      exact pow_three_mul h2 h2'
  inv_mem' := by
    rintro g ⟨hg, h1, h2⟩
    refine ⟨(baseGp I).inv_mem hg, fun j hj => ?_, ?_⟩
    · have : (⟨g⁻¹, (baseGp I).inv_mem hg⟩ : ↥(baseGp I)) = (⟨g, hg⟩ : ↥(baseGp I))⁻¹ := rfl
      rw [this, map_inv, h1 j hj, inv_one]
    · have : (⟨g⁻¹, (baseGp I).inv_mem hg⟩ : ↥(baseGp I)) = (⟨g, hg⟩ : ↥(baseGp I))⁻¹ := rfl
      rw [this, map_inv, inv_pow, h2, inv_one]

variable (hF : PlaneFamily I)

theorem cubeBase_le_baseGp : cubeBase hF ≤ baseGp I := fun _ hg => hg.1

theorem cubeAt_le_baseGp (i : ι) : cubeAt hF i ≤ baseGp I := fun _ hg => hg.1

theorem cubeAt_le_cubeBase (i : ι) : cubeAt hF i ≤ cubeBase hF := by
  rintro g ⟨hg, h1, h2⟩
  refine ⟨hg, fun j => ?_⟩
  by_cases hj : j = i
  · subst hj
    exact h2
  · rw [h1 j hj, one_pow]

theorem pow_three_of_mem_cubeBase {g : MulAut W} (hg : g ∈ cubeBase hF) : g ^ 3 = 1 := by
  obtain ⟨hgB, h⟩ := hg
  have h3 : (⟨g, hgB⟩ : ↥(baseGp I)) ^ 3 = 1 := by
    apply resPlane_injective hF
    funext i
    show resPlane I i ((⟨g, hgB⟩ : ↥(baseGp I)) ^ 3) = 1
    rw [map_pow, h i]
  exact congrArg Subtype.val h3

theorem sq_mem_cubeBase {g : MulAut W} (hgB : g ∈ baseGp I) : g ^ 2 ∈ cubeBase hF := by
  refine ⟨(baseGp I).pow_mem hgB 2, fun i => ?_⟩
  have := hF.klein i
  have : (⟨g ^ 2, (baseGp I).pow_mem hgB 2⟩ : ↥(baseGp I)) = (⟨g, hgB⟩ : ↥(baseGp I)) ^ 2 := rfl
  rw [this, map_pow]
  exact pow_two_pow_three _

end Cube

section Sylow

theorem isSylowTwoOf_map_hom {G K : Type*} [Group G] [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem twoPart_eq_two_pow_of_card_six {G : Type*} [Group G] {X : Subgroup G} {n : ℕ}
    (h : Nat.card X = 6 ^ n) : twoPart X = 2 ^ n := by
  unfold twoPart
  have key : (6 ^ n).factorization 2 = n := by
    have h6 : (6 : ℕ) = 2 * 3 := rfl
    rw [Nat.factorization_pow, h6, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.Prime.factorization Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 3 by norm_num)]
  rw [h, key]

variable {W : Type*} [CommGroup W] {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup W}

theorem card_baseGp (hF : PlaneFamily I) : Nat.card ↥(baseGp I) = 6 ^ Fintype.card ι := by
  rw [Nat.card_congr (blockEquiv hF).toEquiv, Nat.card_pi]
  have : ∀ i, Nat.card (MulAut ↥(I i)) = 6 := fun i => by
    have := hF.klein i
    exact card_mulAut
  simp [this]

theorem resPlane_surjective_single (hF : PlaneFamily I) (i : ι) :
    Function.Surjective (resPlane I i) := by
  intro β
  classical
  refine ⟨⟨hF.blockAut (Pi.mulSingle i β), hF.blockAut_mem _⟩, ?_⟩
  rw [hF.resPlane_blockAut]
  simp

theorem exists_isCoordProduct_of_sylow (hF : PlaneFamily I) {T : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T (baseGp I)) :
    ∃ t : ∀ i, MulAut ↥(I i), IsCoordProduct I T Finset.univ t := by
  classical
  have := hF.finite_W
  have : Finite (MulAut W) := finite_mulAut_of_finite
  have hTB : T ≤ baseGp I := hT.1
  have hcardT : Nat.card T = 2 ^ Fintype.card ι := by
    rw [(isSylowTwoOf_iff.mp hT).2.2, twoPart_eq_two_pow_of_card_six (card_baseGp hF)]
  set T' : Subgroup ↥(baseGp I) := T.subgroupOf (baseGp I) with hT'
  have hTT' : Nat.card T' = 2 ^ Fintype.card ι := by
    rw [← hcardT]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv
  let Ti : ∀ i, Subgroup (MulAut ↥(I i)) := fun i => T'.map (resPlane I i)
  have hTi : ∀ i, Nat.card (Ti i) = 2 := by
    intro i
    have hsyl := isSylowTwoOf_map_hom hT (resPlane I i)
    have hrange : (resPlane I i).range = ⊤ := MonoidHom.range_eq_top.mpr (resPlane_surjective_single hF i)
    have hc := (isSylowTwoOf_iff.mp hsyl).2.2
    rw [hrange] at hc
    have h6 : Nat.card (⊤ : Subgroup (MulAut ↥(I i))) = 6 ^ 1 := by
      have := hF.klein i
      rw [Subgroup.card_top, card_mulAut, pow_one]
    rw [twoPart_eq_two_pow_of_card_six h6, pow_one] at hc
    exact hc
  let Φ : ↥T' →* ∀ i, ↥(Ti i) :=
    MonoidHom.pi fun i => ((resPlane I i).comp T'.subtype).codRestrict (Ti i)
      (fun x => ⟨x, x.2, rfl⟩)
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    apply resPlane_injective hF
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  have hcardΦ : Nat.card (∀ i, ↥(Ti i)) = 2 ^ Fintype.card ι := by
    rw [Nat.card_pi]
    simp [hTi]
  have hΦbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by rw [hcardΦ, hTT'])
  have hone : ∀ i, ∃! x : ↥(Ti i), x ≠ 1 := fun i =>
    (Nat.card_eq_two_iff' (1 : ↥(Ti i))).mp (hTi i)
  choose x hx using hone
  refine ⟨fun i => ((x i : ↥(Ti i)) : MulAut ↥(I i)), ⟨fun i _ => ⟨fun h => (hx i).1 (Subtype.ext h), ?_⟩, ?_⟩⟩
  · have h2 : (x i) ^ Nat.card (Ti i) = 1 := pow_card_eq_one'
    rw [hTi i] at h2
    have h3 := congrArg Subtype.val h2
    simpa [pow_two] using h3
  · intro g
    constructor
    · intro hg
      have hgB : g ∈ baseGp I := hTB hg
      intro i
      have hmem : resPlane I i ⟨g, hgB⟩ ∈ Ti i := ⟨⟨g, hgB⟩, hg, rfl⟩
      by_cases h1 : (⟨resPlane I i ⟨g, hgB⟩, hmem⟩ : ↥(Ti i)) = 1
      · left
        intro y
        have e1 : resPlane I i ⟨g, hgB⟩ = 1 := congrArg Subtype.val h1
        have := congrArg (fun a : MulAut ↥(I i) => ((a y : ↥(I i)) : W)) e1
        exact this
      · right
        refine ⟨Finset.mem_univ i, fun y => ?_⟩
        have hxe : (⟨resPlane I i ⟨g, hgB⟩, hmem⟩ : ↥(Ti i)) = x i := (hx i).2 _ h1
        have := congrArg (fun a : MulAut ↥(I i) => ((a y : ↥(I i)) : W))
          (congrArg Subtype.val hxe)
        exact this
    · intro hcc
      have hgB : g ∈ baseGp I := fun i => smul_eq_of_coordCond hcc i
      have hmemi : ∀ i, resPlane I i ⟨g, hgB⟩ ∈ Ti i := by
        intro i
        rcases hcc i with hid | ⟨-, ht⟩
        · have e1 : resPlane I i ⟨g, hgB⟩ = 1 := by
            ext y
            exact hid y
          rw [e1]
          exact (Ti i).one_mem
        · have e1 : resPlane I i ⟨g, hgB⟩ = ((x i : ↥(Ti i)) : MulAut ↥(I i)) := by
            ext y
            exact ht y
          rw [e1]
          exact (x i).2
      obtain ⟨τ, hτ⟩ := hΦbij.2 (fun i => ⟨resPlane I i ⟨g, hgB⟩, hmemi i⟩)
      have hτ' : (τ : ↥(baseGp I)) = ⟨g, hgB⟩ := by
        apply resPlane_injective hF
        funext i
        exact congrArg Subtype.val (congrFun hτ i)
      have := Subgroup.mem_subgroupOf.mp τ.2
      rw [hτ'] at this
      exact this

theorem index_cubeSubgroup {U : Type*} [Group U] [IsKleinFour U] :
    (cubeSubgroup U).index = 2 := by
  have h := Subgroup.card_mul_index (cubeSubgroup U)
  rw [card_cubeSubgroup, card_mulAut] at h
  omega

theorem baseGp_le_cubeBase_sup (hF : PlaneFamily I) {T : Subgroup (MulAut W)}
    {t : ∀ i, MulAut ↥(I i)} (hT : IsCoordProduct I T Finset.univ t) :
    baseGp I ≤ cubeBase hF ⊔ T := by
  classical
  intro g hg
  let β : ∀ i, MulAut ↥(I i) := fun i => resPlane I i ⟨g, hg⟩
  let β' : ∀ i, MulAut ↥(I i) := fun i => if β i ^ 3 = 1 then 1 else t i
  have hτT : hF.blockAut β' ∈ T := by
    refine (hT.mem_iff _).mpr (coordCond_blockAut hF (J := Finset.univ) (t := t) fun i => ?_)
    by_cases h : β i ^ 3 = 1
    · left
      simp [β', h]
    · right
      exact ⟨Finset.mem_univ i, by simp [β', h]⟩
  have hτB : hF.blockAut β' ∈ baseGp I := hF.blockAut_mem β'
  have hres : ∀ i, resPlane I i ⟨hF.blockAut β', hτB⟩ = β' i :=
    fun i => hF.resPlane_blockAut β' i
  have hmem : g * (hF.blockAut β')⁻¹ ∈ cubeBase hF := by
    refine ⟨(baseGp I).mul_mem hg ((baseGp I).inv_mem hτB), fun i => ?_⟩
    have e : (⟨g * (hF.blockAut β')⁻¹, (baseGp I).mul_mem hg ((baseGp I).inv_mem hτB)⟩ :
        ↥(baseGp I)) = ⟨g, hg⟩ * (⟨hF.blockAut β', hτB⟩ : ↥(baseGp I))⁻¹ := rfl
    rw [e, map_mul, map_inv, hres i]
    have := hF.klein i
    by_cases h : β i ^ 3 = 1
    · have h1 : β' i = 1 := by simp [β', h]
      rw [h1, inv_one, mul_one]
      exact h
    · have h1 : β' i = t i := by simp [β', h]
      rw [h1]
      have hti := hT.invol i (Finset.mem_univ i)
      have ht3 : ¬ (t i) ^ 3 = 1 := by
        intro h3
        apply hti.1
        calc t i = t i * t i * t i := by rw [hti.2, one_mul]
          _ = (t i) ^ 3 := by rw [pow_succ, pow_two]
          _ = 1 := h3
      have hmul := (Subgroup.mul_mem_iff_of_index_two (index_cubeSubgroup (U := ↥(I i)))
        (a := β i) (b := (t i)⁻¹)).mpr
      have hc : β i * (t i)⁻¹ ∈ cubeSubgroup ↥(I i) := by
        apply hmul
        constructor
        · intro hb
          exact absurd (mem_cubeSubgroup.mp hb) h
        · intro hb
          exact absurd (mem_cubeSubgroup.mp ((cubeSubgroup ↥(I i)).inv_mem_iff.mp hb)) ht3
      exact mem_cubeSubgroup.mp hc
  have hτ : g = g * (hF.blockAut β')⁻¹ * hF.blockAut β' := by group
  rw [hτ]
  exact Subgroup.mul_mem_sup hmem hτT

omit [DecidableEq ι] in
theorem exists_pow_two_pow_mem_cubeBase (hF : PlaneFamily I) {Pm : Subgroup (Equiv.Perm ι)}
    (hPm : IsPGroup 2 Pm) {g : MulAut W} (hg : g ∈ wreathAut hF Pm) :
    ∃ m : ℕ, g ^ 2 ^ m ∈ cubeBase hF := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨k, hk⟩ := hPm ⟨permHom hF x, hx⟩
  have hk' : permHom hF x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxk : ((x ^ 2 ^ k : ↥(permuting I)) : MulAut W) ∈ baseGp I :=
    (mem_baseGp_iff_permHom hF).mpr ⟨(x ^ 2 ^ k).2, by
      have : (⟨((x ^ 2 ^ k : ↥(permuting I)) : MulAut W), (x ^ 2 ^ k).2⟩ : ↥(permuting I)) =
        x ^ 2 ^ k := rfl
      rw [this, map_pow, hk']⟩
  refine ⟨k + 1, ?_⟩
  have := sq_mem_cubeBase hF hxk
  rw [pow_succ, pow_mul]
  simpa using this

section CubeAt

omit [Fintype ι] [DecidableEq ι] in
theorem cubeAt_apply_of_ne (hF : PlaneFamily I) {i : ι} {d : MulAut W} (hd : d ∈ cubeAt hF i)
    {j : ι} (hj : j ≠ i) {x : W} (hx : x ∈ I j) : d x = x := by
  obtain ⟨hdB, h1, -⟩ := hd
  have := (restrictAut_eq_one_iff (I j) d (hdB j)).mp (h1 j hj) x hx
  exact this

omit [DecidableEq ι] in
theorem exists_cubeAt_nontrivial (hF : PlaneFamily I) (i : ι) :
    ∃ d ∈ cubeAt hF i, ∃ x ∈ I i, d x ≠ x := by
  classical
  have := hF.klein i
  have hcard : 1 < Nat.card (cubeSubgroup ↥(I i)) := by rw [card_cubeSubgroup]; norm_num
  have hfin : Finite ↥(cubeSubgroup ↥(I i)) := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥(cubeSubgroup ↥(I i)) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨σ, hσ⟩ := exists_ne (1 : ↥(cubeSubgroup ↥(I i)))
  have hσ3 : (σ : MulAut ↥(I i)) ^ 3 = 1 := mem_cubeSubgroup.mp σ.2
  have hσ1 : (σ : MulAut ↥(I i)) ≠ 1 := fun h => hσ (Subtype.ext h)
  refine ⟨hF.blockAut (Pi.mulSingle i (σ : MulAut ↥(I i))), ⟨hF.blockAut_mem _, fun j hj => ?_, ?_⟩, ?_⟩
  · rw [hF.resPlane_blockAut]
    simp [Pi.mulSingle_eq_of_ne hj]
  · rw [hF.resPlane_blockAut]
    simpa using hσ3
  · by_contra hcon
    push Not at hcon
    apply hσ1
    ext x
    have := hcon x x.2
    rw [hF.blockAut_apply _ x.2] at this
    simpa using this

theorem card_cubeAt (hF : PlaneFamily I) (i : ι) : Nat.card ↥(cubeAt hF i) = 3 := by
  classical
  have hk := hF.klein i
  have hc : Nat.card (cubeSubgroup ↥(I i)) = 3 := card_cubeSubgroup
  rw [← hc]
  refine Nat.card_congr
    { toFun := fun d => ⟨resPlane I i ⟨d.1, d.2.1⟩, mem_cubeSubgroup.2 d.2.2.2⟩
      invFun := fun σ => ⟨hF.blockAut (Pi.mulSingle i (σ : MulAut ↥(I i))),
        ⟨hF.blockAut_mem _, fun j hj => by
            rw [hF.resPlane_blockAut]
            simp [Pi.mulSingle_eq_of_ne hj],
          by
            rw [hF.resPlane_blockAut]
            simpa using mem_cubeSubgroup.1 σ.2⟩⟩
      left_inv := fun d => ?_
      right_inv := fun σ => ?_ }
  · apply Subtype.ext
    apply hF.autEq_of_forall_plane
    intro j x hx
    by_cases hj : j = i
    · subst hj
      show hF.blockAut (Pi.mulSingle j (resPlane I j ⟨d.1, d.2.1⟩)) x = d.1 x
      rw [hF.blockAut_apply _ hx]
      simp only [Pi.mulSingle_eq_same]
      rfl
    · show hF.blockAut (Pi.mulSingle i (resPlane I i ⟨d.1, d.2.1⟩)) x = d.1 x
      rw [hF.blockAut_apply _ hx, Pi.mulSingle_eq_of_ne hj, cubeAt_apply_of_ne hF d.2 hj hx]
      rfl
  · apply Subtype.ext
    show resPlane I i ⟨hF.blockAut (Pi.mulSingle i (σ : MulAut ↥(I i))), _⟩ = σ
    rw [hF.resPlane_blockAut]
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem cubeAt_fixed (hF : PlaneFamily I) {i : ι} {d : MulAut W} (hd : d ∈ cubeAt hF i)
    (hnt : ∃ x ∈ I i, d x ≠ x) {x : W} (hx : x ∈ I i) (hfix : d x = x) : x = 1 := by
  obtain ⟨hdB, -, h3⟩ := hd
  have := hF.klein i
  have h1 : resPlane I i ⟨d, hdB⟩ ≠ 1 := by
    intro h
    obtain ⟨y, hy, hdy⟩ := hnt
    exact hdy ((restrictAut_eq_one_iff (I i) d (hdB i)).mp h y hy)
  have hu : resPlane I i ⟨d, hdB⟩ ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext hfix
  have := eq_one_of_fixed_of_pow_three h1 h3 hu
  exact congrArg Subtype.val this

omit [Fintype ι] [DecidableEq ι] in
theorem exists_div_eq_of_cubeAt (hF : PlaneFamily I) {i : ι} {d : MulAut W}
    (hd : d ∈ cubeAt hF i) (hnt : ∃ x ∈ I i, d x ≠ x) {x : W} (hx : x ∈ I i) :
    ∃ y ∈ I i, d y * y⁻¹ = x := by
  have hfin : Finite ↥(I i) := Nat.finite_of_card_ne_zero (by rw [hF.card_I i]; norm_num)
  let φ : ↥(I i) → ↥(I i) := fun y => ⟨d y * (y : W)⁻¹, (I i).mul_mem
    (smul_mem_of_smul_eq (cubeAt_le_baseGp hF i hd i) y.2) ((I i).inv_mem y.2)⟩
  have hinj : Function.Injective φ := by
    intro y y' hyy'
    have h1 : d y * (y : W)⁻¹ = d y' * (y' : W)⁻¹ := congrArg Subtype.val hyy'
    have h2 : d ((y : W) * (y' : W)⁻¹) = (y : W) * (y' : W)⁻¹ := by
      have h1' : d y / (y : W) = d y' / (y' : W) := by simpa [div_eq_mul_inv] using h1
      have h2' := div_eq_div_iff_div_eq_div.mp h1'
      rw [map_mul, map_inv]
      simpa [div_eq_mul_inv] using h2'
    have h3 := cubeAt_fixed hF hd hnt ((I i).mul_mem y.2 ((I i).inv_mem y'.2)) h2
    exact Subtype.ext (by simpa [mul_inv_eq_one] using h3)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem eq_one_of_fixed_cubeAt (hF : PlaneFamily I) {c : W}
    (hc : ∀ i, ∀ d ∈ cubeAt hF i, d c = c) : c = 1 := by
  apply hF.eq_of_coord_eq
  intro i
  rw [map_one]
  obtain ⟨d, hd, hnt⟩ := exists_cubeAt_nontrivial hF i
  have hσ : ∀ j, d • I j = I ((1 : Equiv.Perm ι) j) := fun j => (cubeAt_le_baseGp hF i hd) j
  have h1 : ((hF.coord i (d c) : ↥(I i)) : W) = d ((hF.coord i c : ↥(I i)) : W) :=
    coord_perm hF hσ i c
  rw [hc i d hd] at h1
  exact Subtype.ext (cubeAt_fixed hF hd hnt (hF.coord i c).2 h1.symm)

theorem cubeBase_le_iSup_cubeAt (hF : PlaneFamily I) (J : Finset ι) :
    ∀ g ∈ cubeBase hF, (∀ i, i ∉ J → ∀ x ∈ I i, g x = x) → g ∈ ⨆ i ∈ J, cubeAt hF i := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro g _ hg
    have : g = 1 := by
      apply hF.autEq_of_forall_plane
      intro i x hx
      exact hg i (Finset.notMem_empty i) x hx
    rw [this]
    exact Subgroup.one_mem _
  | insert a J ha ih =>
    intro g hg hgJ
    obtain ⟨hgB, hg3⟩ := hg
    let β : ∀ i, MulAut ↥(I i) := fun i => resPlane I i ⟨g, hgB⟩
    let βs : ∀ i, MulAut ↥(I i) := Pi.mulSingle a (β a)
    let ga : MulAut W := hF.blockAut βs
    have hgaB : ga ∈ baseGp I := hF.blockAut_mem _
    have hgaD : ga ∈ cubeAt hF a := by
      refine ⟨hgaB, fun j hj => ?_, ?_⟩
      · have : resPlane I j ⟨ga, hgaB⟩ = βs j := hF.resPlane_blockAut βs j
        rw [this]
        exact Pi.mulSingle_eq_of_ne hj _
      · have : resPlane I a ⟨ga, hgaB⟩ = βs a := hF.resPlane_blockAut βs a
        rw [this]
        simpa [βs] using hg3 a
    have hga_apply : ∀ x ∈ I a, ga x = g x := fun x hx => by
      show hF.blockAut βs x = g x
      rw [hF.blockAut_apply _ hx]
      simp [βs, β, resPlane, restrictAut]
    have hg'D : g * ga⁻¹ ∈ cubeBase hF :=
      (cubeBase hF).mul_mem ⟨hgB, hg3⟩ ((cubeBase hF).inv_mem (cubeAt_le_cubeBase hF a hgaD))
    have hg'J : ∀ i, i ∉ J → ∀ x ∈ I i, (g * ga⁻¹) x = x := by
      intro i hi x hx
      by_cases hia : i = a
      · subst hia
        have hu : ga⁻¹ x ∈ I i := inv_smul_mem_of_smul_eq (hgaB i) hx
        show g (ga⁻¹ x) = x
        rw [← hga_apply _ hu]
        simp
      · have hia' : i ∉ insert a J := fun hmem => by
          rcases Finset.mem_insert.mp hmem with e | e
          · exact hia e
          · exact hi e
        have h1 : ga x = x := by
          rw [show ga x = hF.blockAut βs x from rfl, hF.blockAut_apply _ hx]
          simp [βs, Pi.mulSingle_eq_of_ne hia]
        have h2 : ga⁻¹ x = x := by
          show ga.symm x = x
          exact ga.symm_apply_eq.mpr h1.symm
        show g (ga⁻¹ x) = x
        rw [h2]
        exact hgJ i hia' x hx
    have := ih _ hg'D hg'J
    have h3 : g = (g * ga⁻¹) * ga := by group
    rw [Finset.iSup_insert, sup_comm, h3]
    exact Subgroup.mul_mem_sup this hgaD

end CubeAt

section CoordElt

@[expose] noncomputable def coordElt (hF : PlaneFamily I) (t : ∀ i, MulAut ↥(I i)) (i : ι) :
    MulAut W :=
  hF.blockAut (Pi.mulSingle i (t i))

theorem coordElt_apply_self (hF : PlaneFamily I) (t : ∀ i, MulAut ↥(I i)) (i : ι) {x : W}
    (hx : x ∈ I i) : coordElt hF t i x = ((t i ⟨x, hx⟩ : ↥(I i)) : W) := by
  unfold coordElt
  rw [hF.blockAut_apply _ hx]
  simp

theorem coordElt_apply_ne (hF : PlaneFamily I) (t : ∀ i, MulAut ↥(I i)) {i j : ι} (hj : j ≠ i)
    {x : W} (hx : x ∈ I j) : coordElt hF t i x = x := by
  unfold coordElt
  rw [hF.blockAut_apply _ hx]
  simp [Pi.mulSingle_eq_of_ne hj]

theorem coordElt_mem_baseGp (hF : PlaneFamily I) (t : ∀ i, MulAut ↥(I i)) (i : ι) :
    coordElt hF t i ∈ baseGp I := hF.blockAut_mem _

theorem coordCond_coordElt (hF : PlaneFamily I) {t : ∀ i, MulAut ↥(I i)} (i : ι) :
    CoordCond I {i} t (coordElt hF t i) := by
  intro k
  by_cases hk : k = i
  · subst hk
    right
    exact ⟨Finset.mem_singleton_self k, fun x => coordElt_apply_self hF t k x.2⟩
  · left
    intro x
    exact coordElt_apply_ne hF t hk x.2

omit [Fintype ι] [DecidableEq ι] in
theorem eq_one_of_coordCond_empty {t : ∀ i, MulAut ↥(I i)} (hF : PlaneFamily I) {g : MulAut W}
    (hg : CoordCond I ∅ t g) : g = 1 := by
  apply hF.autEq_of_forall_plane
  intro i x hx
  rcases hg i with h | ⟨h, -⟩
  · exact h ⟨x, hx⟩
  · exact absurd h (Finset.notMem_empty i)

theorem coordCond_mem_iSup (hF : PlaneFamily I) {t : ∀ i, MulAut ↥(I i)} (J : Finset ι) :
    ∀ g : MulAut W, CoordCond I J t g →
      g ∈ ⨆ i ∈ J, Subgroup.zpowers (coordElt hF t i) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro g hg
    rw [eq_one_of_coordCond_empty hF hg]
    exact Subgroup.one_mem _
  | insert a J ha ih =>
    intro g hg
    by_cases hga : ∀ x : ↥(I a), g (x : W) = x
    · have hg' : CoordCond I J t g := by
        intro k
        by_cases hk : k = a
        · subst hk
          exact Or.inl hga
        · rcases hg k with h | ⟨hkJ, h⟩
          · exact Or.inl h
          · refine Or.inr ⟨?_, h⟩
            rcases Finset.mem_insert.mp hkJ with h' | h'
            · exact absurd h' hk
            · exact h'
      rw [Finset.iSup_insert]
      exact Subgroup.mem_sup_right (ih g hg')
    · have hga2 : ∀ x : ↥(I a), g (x : W) = ((t a x : ↥(I a)) : W) := by
        rcases hg a with h | ⟨-, h⟩
        · exact absurd h hga
        · exact h
      set e := coordElt hF t a with he
      have heB : e ∈ baseGp I := coordElt_mem_baseGp hF t a
      have hek : ∀ k, k ≠ a → ∀ x : W, x ∈ I k → e⁻¹ x = x := fun k hk x hx => by
        have h1 : e x = x := coordElt_apply_ne hF t hk hx
        show e.symm x = x
        exact e.symm_apply_eq.mpr h1.symm
      have hcond : CoordCond I J t (g * e⁻¹) := by
        intro k
        by_cases hk : k = a
        · subst hk
          left
          intro x
          have hu : e⁻¹ (x : W) ∈ I k := inv_smul_mem_of_smul_eq (heB k) x.2
          have h1 : e (e⁻¹ (x : W)) = x := by simp
          have h2 : g (e⁻¹ (x : W)) = e (e⁻¹ (x : W)) := by
            have h3 : e (e⁻¹ (x : W)) = ((t k ⟨e⁻¹ (x : W), hu⟩ : ↥(I k)) : W) :=
              coordElt_apply_self hF t k hu
            rw [h3]
            exact hga2 ⟨_, hu⟩
          show g (e⁻¹ (x : W)) = x
          rw [h2, h1]
        · rcases hg k with h | ⟨hkJ, h⟩
          · left
            intro x
            show g (e⁻¹ (x : W)) = x
            rw [hek k hk x x.2]
            exact h x
          · right
            refine ⟨?_, fun x => ?_⟩
            · rcases Finset.mem_insert.mp hkJ with h' | h'
              · exact absurd h' hk
              · exact h'
            · show g (e⁻¹ (x : W)) = _
              rw [hek k hk x x.2]
              exact h x
      have h1 := ih _ hcond
      have h2 : g = (g * e⁻¹) * e := by group
      rw [Finset.iSup_insert, sup_comm, h2]
      exact Subgroup.mul_mem_sup h1 (Subgroup.mem_zpowers e)

end CoordElt

end Sylow

section SylowAux

variable {G : Type*} [Group G]

theorem isSylowTwoOf_inf_of_prod {H N S : Subgroup G} (hS : IsSylowTwoOf S H) (hNH : N ≤ H)
    (hprod : ∀ h ∈ H, ∃ n ∈ N, ∃ s ∈ S, h = n * s) : IsSylowTwoOf (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, ?_⟩
  have key : ((S ⊓ N).subgroupOf N).index = (S.subgroupOf H).index := by
    unfold Subgroup.index
    let f : N ⧸ (S ⊓ N).subgroupOf N → H ⧸ S.subgroupOf H :=
      Quotient.map' (fun n : N => (⟨n, hNH n.2⟩ : H)) (by
        intro a b hab
        have h1 : a⁻¹ * b ∈ (S ⊓ N).subgroupOf N := QuotientGroup.leftRel_apply.mp hab
        rw [QuotientGroup.leftRel_apply]
        exact (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h1).1))
    have hf : Function.Bijective f := by
      constructor
      · intro a b
        induction a using Quotient.inductionOn' with | _ a => ?_
        induction b using Quotient.inductionOn' with | _ b => ?_
        intro hab
        have h1 : (⟨(a : G), hNH a.2⟩ : H)⁻¹ * ⟨(b : G), hNH b.2⟩ ∈ S.subgroupOf H :=
          QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, ?_⟩
        exact N.mul_mem (N.inv_mem a.2) b.2
      · intro q
        induction q using Quotient.inductionOn' with | _ h => ?_
        obtain ⟨n, hn, s, hs, hh⟩ := hprod h h.2
        refine ⟨Quotient.mk'' ⟨n, hn⟩, ?_⟩
        show Quotient.mk'' (⟨n, hNH hn⟩ : H) = Quotient.mk'' h
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have : ((⟨n, hNH hn⟩ : H)⁻¹ * h : H) = ⟨s, hS.1 hs⟩ := by
          apply Subtype.ext
          show n⁻¹ * (h : G) = s
          rw [hh]
          group
        show ((⟨n, hNH hn⟩ : H)⁻¹ * h : H).1 ∈ S
        rw [this]
        exact hs
    exact (Nat.card_congr (Equiv.ofBijective f hf))
  rw [key]
  exact hS.2.2

theorem card_map_mul_card_inf_ker {K : Type*} [Group K] (ρ : G →* K) (A : Subgroup G) :
    Nat.card (A.map ρ) * Nat.card ↥(A ⊓ ρ.ker) = Nat.card A := by
  let f : ↥A →* K := ρ.comp A.subtype
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  have hrange : f.range = A.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ↥f.ker = Nat.card ↥(A ⊓ ρ.ker) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hrange, hker] at h1
  rw [mul_comm]
  exact h1

end SylowAux

section PlaneFacts

set_option synthInstance.maxSize 4096 in
theorem v4_invol_inv (c t : MulAut V4) (hc : c ^ 3 = 1) (ht : t ≠ 1) (ht2 : t * t = 1) :
    t * c⁻¹ * t = c := by revert c t; decide +kernel

set_option synthInstance.maxSize 4096 in
theorem v4_gen (c c' : MulAut V4) (hc1 : c ≠ 1) (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1) :
    ∃ j : Fin 3, c' = (c ^ 2) ^ (j : ℕ) := by revert c c'; decide +kernel

variable {U : Type*} [Group U] [IsKleinFour U]

theorem invol_inv_mul {c t : MulAut U} (hc : c ^ 3 = 1) (ht : t ≠ 1) (ht2 : t * t = 1) :
    t * c⁻¹ * t = c := by
  set e := MulAut.congr (planeEquiv U)
  have h1 : e t * (e c)⁻¹ * e t = e c := by
    apply v4_invol_inv
    · rw [← map_pow, hc, map_one]
    · intro h; apply ht; exact e.injective (h.trans (map_one e).symm)
    · rw [← map_mul, ht2, map_one]
  have := congrArg (fun x => e.symm x) h1
  simpa using this

theorem exists_pow_sq_of_cube {c c' : MulAut U} (hc1 : c ≠ 1) (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1) :
    ∃ j : ℕ, c' = (c ^ 2) ^ j := by
  set e := MulAut.congr (planeEquiv U)
  obtain ⟨j, hj⟩ := v4_gen (e c) (e c') (fun h => hc1 (e.injective (h.trans (map_one e).symm)))
    (by rw [← map_pow, hc, map_one]) (by rw [← map_pow, hc', map_one])
  refine ⟨j, e.injective ?_⟩
  rw [hj, map_pow, map_pow]

end PlaneFacts

section CoordMisc

variable {W : Type*} [CommGroup W] {ι : Type*} {I : ι → Subgroup W}

theorem IsCoordProduct.congr_family {A : Subgroup (MulAut W)} {J : Finset ι}
    {t t' : ∀ i, MulAut ↥(I i)} (hC : IsCoordProduct I A J t')
    (hte : ∀ i ∈ J, t i = t' i) : IsCoordProduct I A J t :=
  ⟨fun i hi => by rw [hte i hi]; exact hC.invol i hi, fun g => by
    rw [hC.mem_iff g]
    unfold CoordCond
    refine forall_congr' fun i => or_congr_right ?_
    constructor
    · rintro ⟨hi, hg⟩
      exact ⟨hi, fun x => by rw [hte i hi]; exact hg x⟩
    · rintro ⟨hi, hg⟩
      exact ⟨hi, fun x => by rw [← hte i hi]; exact hg x⟩⟩

theorem CoordCond.mono {t : ∀ i, MulAut ↥(I i)} {J J' : Finset ι} (hJJ : J ⊆ J') {g : MulAut W}
    (hg : CoordCond I J t g) : CoordCond I J' t g := fun i =>
  (hg i).imp_right fun ⟨hi, hx⟩ => ⟨hJJ hi, hx⟩

end CoordMisc

section Generation

variable {W : Type*} [CommGroup W] {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup W}

theorem cubeBase_le_sup_conj (hF : PlaneFamily I) {T : Subgroup (MulAut W)}
    {t : ∀ i, MulAut ↥(I i)} (hT : IsCoordProduct I T Finset.univ t) {δ : MulAut W}
    (hδ : δ ∈ cubeBase hF) (hδnt : ∀ i, ∃ x ∈ I i, δ x ≠ x) :
    cubeBase hF ≤ T ⊔ T.map (MulAut.conj δ⁻¹).toMonoidHom := by
  classical
  set Y := T ⊔ T.map (MulAut.conj δ⁻¹).toMonoidHom with hY
  obtain ⟨hδB, hδ3⟩ := hδ
  have hD : ∀ i, cubeAt hF i ≤ Y := by
    intro i d hd
    have hk := hF.klein i
    obtain ⟨hdB, hd1, hd3⟩ := hd
    set c := resPlane I i ⟨δ, hδB⟩ with hc
    have hc3 : c ^ 3 = 1 := hδ3 i
    have hc1 : c ≠ 1 := by
      intro h1
      obtain ⟨x, hx, hxne⟩ := hδnt i
      exact hxne ((restrictAut_eq_one_iff (I i) δ (hδB i)).mp h1 x hx)
    let βe : ∀ k, MulAut ↥(I k) := Pi.mulSingle i (t i)
    have he : coordElt hF t i ∈ T :=
      (hT.mem_iff _).mpr (CoordCond.mono (Finset.subset_univ _) (coordCond_coordElt hF i))
    have heB : coordElt hF t i ∈ baseGp I := coordElt_mem_baseGp hF t i
    have hek : ∀ k, resPlane I k ⟨coordElt hF t i, heB⟩ = βe k :=
      fun k => hF.resPlane_blockAut βe k
    have h1 : (MulAut.conj δ⁻¹).toMonoidHom (coordElt hF t i) = δ⁻¹ * coordElt hF t i * δ := by
      simp
    have he' : (MulAut.conj δ⁻¹).toMonoidHom (coordElt hF t i) ∈
        T.map (MulAut.conj δ⁻¹).toMonoidHom := ⟨_, he, rfl⟩
    set m : MulAut W := coordElt hF t i * (MulAut.conj δ⁻¹).toMonoidHom (coordElt hF t i)
      with hm
    have hmY : m ∈ Y := Subgroup.mul_mem_sup he he'
    have hmeq : m = coordElt hF t i * (δ⁻¹ * coordElt hF t i * δ) := by rw [hm, h1]
    have hmB : m ∈ baseGp I := by
      rw [hmeq]
      exact (baseGp I).mul_mem heB ((baseGp I).mul_mem ((baseGp I).mul_mem
        ((baseGp I).inv_mem hδB) heB) hδB)
    have hti := hT.invol i (Finset.mem_univ i)
    have e1 : (⟨m, hmB⟩ : ↥(baseGp I)) = ⟨coordElt hF t i, heB⟩ * (⟨δ, hδB⟩ : ↥(baseGp I))⁻¹ *
        ⟨coordElt hF t i, heB⟩ * ⟨δ, hδB⟩ := by
      apply Subtype.ext
      show m = coordElt hF t i * δ⁻¹ * coordElt hF t i * δ
      rw [hmeq]
      group
    have hresi : resPlane I i ⟨m, hmB⟩ = c ^ 2 := by
      rw [e1, map_mul, map_mul, map_mul, map_inv, hek i]
      have hβ : βe i = t i := by simp [βe]
      rw [hβ]
      have := invol_inv_mul hc3 hti.1 hti.2
      show t i * c⁻¹ * t i * c = c ^ 2
      rw [this, pow_two]
    have hresk : ∀ k, k ≠ i → resPlane I k ⟨m, hmB⟩ = 1 := by
      intro k hki
      rw [e1, map_mul, map_mul, map_mul, map_inv, hek k]
      have hβ : βe k = 1 := by simp [βe, Pi.mulSingle_eq_of_ne hki]
      rw [hβ]
      simp
    obtain ⟨j, hj⟩ := exists_pow_sq_of_cube hc1 hc3 hd3
    have hdm : (⟨d, hdB⟩ : ↥(baseGp I)) = (⟨m, hmB⟩ : ↥(baseGp I)) ^ j := by
      apply resPlane_injective hF
      funext k
      show resPlane I k ⟨d, hdB⟩ = resPlane I k ((⟨m, hmB⟩ : ↥(baseGp I)) ^ j)
      rw [map_pow]
      by_cases hki : k = i
      · subst hki
        rw [hresi, hj]
      · rw [hresk k hki, hd1 k hki, one_pow]
    have hdpow : d = m ^ j := congrArg Subtype.val hdm
    rw [hdpow]
    exact Y.pow_mem hmY j
  intro g hg
  have hall := cubeBase_le_iSup_cubeAt hF Finset.univ g hg
    (fun i hi => absurd (Finset.mem_univ i) hi)
  exact (iSup₂_le fun i _ => hD i : (⨆ i ∈ (Finset.univ : Finset ι), cubeAt hF i) ≤ Y) hall

omit [Fintype ι] [DecidableEq ι] in
theorem conj_cubeAt_mem (hF : PlaneFamily I) {g : MulAut W} {σ : Equiv.Perm ι}
    (hσ : ∀ j, g • I j = I (σ j)) {i : ι} {d : MulAut W} (hd : d ∈ cubeAt hF i) :
    g * d * g⁻¹ ∈ cubeAt hF (σ i) := by
  classical
  have hd3' : d ^ 3 = 1 := pow_three_of_mem_cubeBase hF (cubeAt_le_cubeBase hF i hd)
  obtain ⟨hdB, hd1, hd3⟩ := hd
  have hdB' : ∀ k, d • I k = I k := mem_baseGp.mp hdB
  have hginv : ∀ j, g⁻¹ • I j = I (σ.symm j) := fun j => by
    rw [inv_smul_eq_iff, hσ, σ.apply_symm_apply]
  have hconjB : g * d * g⁻¹ ∈ baseGp I := by
    intro j
    rw [mul_smul, mul_smul, hginv, hdB', hσ, σ.apply_symm_apply]
  have hd1' : ∀ k, k ≠ i → ∀ y ∈ I k, d y = y := fun k hk y hy =>
    (restrictAut_eq_one_iff (I k) d (hdB k)).mp (hd1 k hk) y hy
  refine ⟨hconjB, fun j hj => ?_, ?_⟩
  · show restrictAut (I j) (g * d * g⁻¹) (hconjB j) = 1
    rw [restrictAut_eq_one_iff]
    intro y hy
    have hy' : g⁻¹ y ∈ I (σ.symm j) := by
      rw [← hginv j]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, hy, rfl⟩
    have hne : σ.symm j ≠ i := fun e => hj (by rw [← e, σ.apply_symm_apply])
    show g (d (g⁻¹ y)) = y
    rw [hd1' _ hne _ hy']
    simp
  · have : (⟨g * d * g⁻¹, hconjB⟩ : ↥(baseGp I)) ^ 3 = 1 := by
      apply Subtype.ext
      simp [conj_pow, hd3']
    rw [← map_pow, this, map_one]

omit [Fintype ι] [DecidableEq ι] in
theorem mul_mul_inv_mem_cubeAt (hF : PlaneFamily I) {i : ι} {g d : MulAut W}
    (hg : g ∈ baseGp I) (hd : d ∈ cubeAt hF i) : g * d * g⁻¹ ∈ cubeAt hF i := by
  obtain ⟨hdB, h1, h3⟩ := hd
  have hB : g * d * g⁻¹ ∈ baseGp I :=
    (baseGp I).mul_mem ((baseGp I).mul_mem hg hdB) ((baseGp I).inv_mem hg)
  have e : (⟨g * d * g⁻¹, hB⟩ : ↥(baseGp I)) = ⟨g, hg⟩ * ⟨d, hdB⟩ * ⟨g, hg⟩⁻¹ := rfl
  refine ⟨hB, fun j hj => ?_, ?_⟩
  · rw [e, map_mul, map_mul, map_inv, h1 j hj, mul_one, mul_inv_cancel]
  · rw [e, map_mul, map_mul, map_inv, conj_pow, h3, mul_one, mul_inv_cancel]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_ne_of_cubeAt_ne_one (hF : PlaneFamily I) {i : ι} {d : MulAut W}
    (hd : d ∈ cubeAt hF i) (hd1 : d ≠ 1) : ∃ x ∈ I i, d x ≠ x := by
  by_contra hcon
  push Not at hcon
  apply hd1
  apply hF.autEq_of_forall_plane
  intro k x hx
  by_cases hk : k = i
  · subst hk
    exact hcon x hx
  · exact cubeAt_apply_of_ne hF hd hk hx

omit [Fintype ι] in
theorem cubeAt_le_zpowers (hF : PlaneFamily I) {i : ι} {m : MulAut W} (hm : m ∈ cubeAt hF i)
    (hnt : ∃ x ∈ I i, m x ≠ x) : cubeAt hF i ≤ Subgroup.zpowers m := by
  classical
  intro d hd
  have hk := hF.klein i
  obtain ⟨hmB, hm1, hm3⟩ := hm
  obtain ⟨hdB, hd1, hd3⟩ := hd
  set c := resPlane I i ⟨m, hmB⟩ with hc
  have hc1 : c ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxne⟩ := hnt
    exact hxne ((restrictAut_eq_one_iff (I i) m (hmB i)).mp h1 x hx)
  obtain ⟨j, hj⟩ := exists_pow_sq_of_cube hc1 hm3 hd3
  have hdm : (⟨d, hdB⟩ : ↥(baseGp I)) = ((⟨m, hmB⟩ : ↥(baseGp I)) ^ 2) ^ j := by
    apply resPlane_injective hF
    funext k
    show resPlane I k ⟨d, hdB⟩ = resPlane I k (((⟨m, hmB⟩ : ↥(baseGp I)) ^ 2) ^ j)
    rw [map_pow, map_pow]
    by_cases hki : k = i
    · subst hki
      rw [hj]
    · rw [hd1 k hki, hm1 k hki]
      simp
  have hdpow : d = (m ^ 2) ^ j := congrArg Subtype.val hdm
  rw [hdpow, ← pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers m) _

theorem PlaneFamily.blockAut_mul (hF : PlaneFamily I) (β γ : ∀ i, MulAut ↥(I i)) :
    hF.blockAut (β * γ) = hF.blockAut β * hF.blockAut γ := by
  apply hF.autEq_of_forall_plane
  intro i x hx
  rw [hF.blockAut_apply _ hx]
  show _ = hF.blockAut β (hF.blockAut γ x)
  rw [hF.blockAut_apply γ hx, hF.blockAut_apply β (γ i ⟨x, hx⟩).2]
  rfl

theorem blockAut_single_mem_sup (hF : PlaneFamily I) {T : Subgroup (MulAut W)}
    {t : ∀ i, MulAut ↥(I i)} (hT : IsCoordProduct I T Finset.univ t) (i : ι)
    (σ : MulAut ↥(I i)) : hF.blockAut (Pi.mulSingle i σ) ∈ cubeAt hF i ⊔ T := by
  classical
  have hk := hF.klein i
  have hti := hT.invol i (Finset.mem_univ i)
  by_cases hσ : σ ^ 3 = 1
  · refine Subgroup.mem_sup_left ⟨hF.blockAut_mem _, fun j hj => ?_, ?_⟩
    · rw [hF.resPlane_blockAut]
      exact Pi.mulSingle_eq_of_ne hj _
    · rw [hF.resPlane_blockAut]
      simpa using hσ
  · have ht3 : ¬ (t i) ^ 3 = 1 := by
      intro h3
      apply hti.1
      calc t i = t i * t i * t i := by rw [hti.2, one_mul]
        _ = (t i) ^ 3 := by rw [pow_succ, pow_two]
        _ = 1 := h3
    have hc : σ * (t i)⁻¹ ∈ cubeSubgroup ↥(I i) := by
      apply (Subgroup.mul_mem_iff_of_index_two (index_cubeSubgroup (U := ↥(I i)))
        (a := σ) (b := (t i)⁻¹)).mpr
      constructor
      · intro hb
        exact absurd (mem_cubeSubgroup.mp hb) hσ
      · intro hb
        exact absurd (mem_cubeSubgroup.mp ((cubeSubgroup ↥(I i)).inv_mem_iff.mp hb)) ht3
    have hdecomp : (Pi.mulSingle i σ : ∀ k, MulAut ↥(I k)) =
        Pi.mulSingle i (σ * (t i)⁻¹) * Pi.mulSingle i (t i) := by
      rw [← Pi.mulSingle_mul]
      simp
    have hd : hF.blockAut (Pi.mulSingle i (σ * (t i)⁻¹)) ∈ cubeAt hF i := by
      refine ⟨hF.blockAut_mem _, fun j hj => ?_, ?_⟩
      · rw [hF.resPlane_blockAut]
        exact Pi.mulSingle_eq_of_ne hj _
      · rw [hF.resPlane_blockAut]
        simpa using mem_cubeSubgroup.mp hc
    have he : coordElt hF t i ∈ T :=
      (hT.mem_iff _).mpr (CoordCond.mono (Finset.subset_univ _) (coordCond_coordElt hF i))
    rw [hdecomp, hF.blockAut_mul]
    exact Subgroup.mul_mem_sup hd he

theorem exists_cubeBase_nontrivial (hF : PlaneFamily I) :
    ∃ δ ∈ cubeBase hF, ∀ i, ∃ x ∈ I i, δ x ≠ x := by
  classical
  have key : ∀ i, ∃ σ : MulAut ↥(I i), σ ^ 3 = 1 ∧ σ ≠ 1 := by
    intro i
    have := hF.klein i
    have hcard : 1 < Nat.card (cubeSubgroup ↥(I i)) := by rw [card_cubeSubgroup]; norm_num
    have hfin : Finite ↥(cubeSubgroup ↥(I i)) := Nat.finite_of_card_ne_zero (by omega)
    have hnt : Nontrivial ↥(cubeSubgroup ↥(I i)) := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨σ, hσ⟩ := exists_ne (1 : ↥(cubeSubgroup ↥(I i)))
    exact ⟨σ, mem_cubeSubgroup.mp σ.2, fun h => hσ (Subtype.ext h)⟩
  choose σ hσ3 hσ1 using key
  refine ⟨hF.blockAut σ, ⟨hF.blockAut_mem σ, fun i => ?_⟩, fun i => ?_⟩
  · rw [hF.resPlane_blockAut]
    exact hσ3 i
  · by_contra hcon
    push Not at hcon
    apply hσ1 i
    ext x
    have := hcon x x.2
    rw [hF.blockAut_apply σ x.2] at this
    simpa using this

end Generation

end CFSG.QuasithinUnique.Setup.Wreath
