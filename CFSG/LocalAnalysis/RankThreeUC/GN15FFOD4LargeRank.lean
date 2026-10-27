module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.CopiesRank
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeNode
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Invol

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

@[expose] def vTwoEnds : Fin 4 → Fin Tag.D4.rank → ℤ :=
  ![(![4, 3, 6, 3] : Fin 4 → ℤ), (![3, 4, 6, 3] : Fin 4 → ℤ), (![0, 0, 0, 0] : Fin 4 → ℤ),
    (![3, 3, 6, 4] : Fin 4 → ℤ)]

@[expose] def words17 : Fin 4 → Fin 5 → Fin 17 → List (Fin 4) :=
  ![
    ![
      ![[], [2], [2, 0], [1, 2], [3, 2], [1, 2, 0], [3, 2, 0], [3, 1, 2], [3, 1, 2, 0],
        [2, 3, 1, 2], [2, 3, 1, 0, 2], [2, 3, 1, 2, 0], [1, 2, 3, 1, 0, 2], [2, 3, 1, 0, 2, 0],
        [2, 3, 2, 1, 0, 2], [1, 2, 3, 1, 0, 2, 0], [1, 2, 3, 2, 1, 0, 2]],
      ![[2], [0, 2], [2, 0], [1, 2], [1, 0, 2], [0, 2, 0], [1, 2, 0], [1, 0, 2, 0], [2, 1, 0, 2],
        [2, 3, 0, 2], [1, 2, 3, 0, 2], [2, 1, 0, 2, 0], [2, 3, 1, 0, 2], [0, 2, 3, 1, 0, 2],
        [1, 2, 3, 1, 0, 2], [2, 3, 1, 0, 2, 0], [0, 2, 3, 1, 0, 2, 0]],
      ![[], [2], [0, 2], [2, 0], [3, 2], [0, 2, 0], [3, 0, 2], [3, 2, 0], [2, 1, 0, 2],
        [2, 3, 0, 2], [3, 0, 2, 0], [2, 3, 1, 2], [2, 3, 1, 0, 2], [3, 2, 1, 0, 2], [2, 3, 0, 2, 0],
        [2, 3, 1, 2, 0], [0, 2, 3, 1, 0, 2]],
      ![[], [2], [0, 2], [2, 0], [1, 2], [1, 0, 2], [0, 2, 0], [1, 2, 0], [1, 0, 2, 0],
        [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 2], [1, 2, 3, 0, 2], [2, 1, 0, 2, 0], [2, 3, 1, 0, 2],
        [2, 3, 1, 2, 0], [0, 2, 3, 1, 0, 2]],
      ![[], [0], [2], [0, 2], [2, 0], [1, 2], [3, 2], [1, 0, 2], [0, 2, 0], [3, 0, 2], [1, 2, 0],
        [3, 2, 0], [3, 1, 2], [1, 0, 2, 0], [2, 1, 0, 2], [3, 1, 0, 2], [2, 3, 0, 2]]
    ],
    ![
      ![[2], [1, 2], [2, 1], [3, 2], [1, 2, 1], [3, 1, 2], [3, 2, 1], [2, 1, 0, 2], [2, 3, 1, 2],
        [3, 1, 2, 1], [2, 3, 1, 0, 2], [3, 2, 1, 0, 2], [2, 3, 1, 2, 1], [2, 3, 1, 0, 2, 1],
        [1, 2, 3, 1, 0, 2], [2, 3, 2, 1, 0, 2], [1, 2, 3, 1, 0, 2, 1]],
      ![[], [2], [0, 2], [1, 2], [2, 1], [0, 2, 1], [1, 0, 2], [1, 2, 1], [1, 0, 2, 1],
        [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 2], [0, 2, 3, 1, 2], [2, 1, 0, 2, 1], [2, 3, 0, 2, 1],
        [2, 3, 1, 0, 2], [0, 2, 3, 1, 0, 2]],
      ![[], [2], [0, 2], [2, 1], [3, 2], [0, 2, 1], [3, 0, 2], [3, 2, 1], [3, 0, 2, 1],
        [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 2], [2, 3, 0, 2, 1], [2, 3, 1, 0, 2], [3, 2, 1, 0, 2],
        [2, 3, 1, 2, 1], [0, 2, 3, 1, 0, 2]],
      ![[2], [0, 2], [1, 2], [2, 1], [0, 2, 1], [1, 0, 2], [1, 2, 1], [1, 0, 2, 1], [2, 1, 0, 2],
        [2, 3, 1, 2], [0, 2, 3, 1, 2], [2, 1, 0, 2, 1], [2, 3, 1, 0, 2], [0, 2, 3, 1, 0, 2],
        [2, 3, 1, 0, 2, 1], [1, 2, 3, 1, 0, 2], [1, 0, 2, 3, 1, 0, 2]],
      ![[], [1], [2], [0, 2], [1, 2], [2, 1], [3, 2], [0, 2, 1], [1, 0, 2], [3, 0, 2], [1, 2, 1],
        [3, 1, 2], [3, 2, 1], [1, 0, 2, 1], [3, 0, 2, 1], [2, 1, 0, 2], [3, 1, 0, 2]]
    ],
    (fun _ _ => []),
    ![
      ![[2], [1, 2], [2, 3], [3, 2], [1, 2, 3], [3, 1, 2], [2, 3, 2], [2, 3, 0, 2], [1, 2, 3, 2],
        [2, 3, 1, 2], [1, 2, 3, 0, 2], [2, 3, 1, 0, 2], [1, 2, 3, 1, 2], [2, 1, 0, 2, 3, 2],
        [1, 2, 3, 1, 0, 2], [2, 3, 2, 1, 0, 2], [2, 1, 0, 2, 3, 0, 2]],
      ![[], [2], [0, 2], [1, 2], [2, 3], [0, 2, 3], [1, 0, 2], [1, 2, 3], [1, 0, 2, 3],
        [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 2], [0, 2, 3, 1, 2], [2, 1, 0, 2, 3], [0, 2, 3, 0, 2],
        [2, 3, 1, 0, 2], [0, 2, 3, 1, 0, 2]],
      ![[2], [0, 2], [2, 3], [3, 2], [0, 2, 3], [3, 0, 2], [2, 3, 2], [0, 2, 3, 2], [2, 3, 0, 2],
        [2, 3, 1, 2], [0, 2, 3, 1, 2], [0, 2, 3, 0, 2], [2, 3, 1, 0, 2], [0, 2, 3, 1, 0, 2],
        [2, 1, 0, 2, 3, 2], [2, 3, 2, 1, 0, 2], [2, 1, 0, 2, 3, 1, 2]],
      ![[], [2], [0, 2], [1, 2], [2, 3], [0, 2, 3], [1, 0, 2], [1, 2, 3], [1, 0, 2, 3],
        [2, 1, 0, 2], [2, 3, 0, 2], [2, 3, 1, 2], [2, 1, 0, 2, 3], [1, 2, 3, 0, 2], [2, 3, 1, 0, 2],
        [1, 2, 3, 1, 2], [0, 2, 3, 1, 0, 2]],
      ![[], [2], [3], [0, 2], [1, 2], [2, 3], [3, 2], [0, 2, 3], [1, 0, 2], [3, 0, 2], [1, 2, 3],
        [3, 1, 2], [2, 3, 2], [1, 0, 2, 3], [0, 2, 3, 2], [2, 1, 0, 2], [3, 1, 0, 2]]
    ]
  ]

@[expose] def words24 : Fin 4 → Fin 24 → List (Fin 4) :=
  ![
    ![[], [0], [2], [0, 2], [2, 0], [1, 2], [3, 2], [1, 0, 2], [0, 2, 0], [3, 0, 2], [1, 2, 0],
      [3, 2, 0], [3, 1, 2], [1, 0, 2, 0], [2, 1, 0, 2], [3, 1, 0, 2], [2, 3, 0, 2], [3, 0, 2, 0],
      [3, 1, 2, 0], [2, 3, 1, 2], [0, 2, 3, 1, 2], [1, 2, 3, 0, 2], [2, 1, 0, 2, 0],
      [3, 1, 0, 2, 0]],
    ![[], [1], [2], [0, 2], [1, 2], [2, 1], [3, 2], [0, 2, 1], [1, 0, 2], [3, 0, 2], [1, 2, 1],
      [3, 1, 2], [3, 2, 1], [1, 0, 2, 1], [3, 0, 2, 1], [2, 1, 0, 2], [3, 1, 0, 2], [2, 3, 0, 2],
      [2, 3, 1, 2], [3, 1, 2, 1], [0, 2, 3, 1, 2], [2, 1, 0, 2, 1], [3, 1, 0, 2, 1],
      [2, 3, 0, 2, 1]],
    (fun _ => []),
    ![[], [2], [3], [0, 2], [1, 2], [2, 3], [3, 2], [0, 2, 3], [1, 0, 2], [3, 0, 2], [1, 2, 3],
      [3, 1, 2], [2, 3, 2], [1, 0, 2, 3], [0, 2, 3, 2], [2, 1, 0, 2], [3, 1, 0, 2], [2, 3, 0, 2],
      [1, 2, 3, 2], [2, 3, 1, 2], [0, 2, 3, 1, 2], [2, 1, 0, 2, 3], [1, 0, 2, 3, 2],
      [0, 2, 3, 0, 2]]
  ]

@[expose] def vec17 (e : Fin 4) (i : Fin 5) (k : Fin 17) : List ℤ :=
  (words17 e i k).foldr (reflectLG .D4) (List.ofFn (vTwoEnds e))

@[expose] def vec17' (e : Fin 4) (i : Fin 5) (k : Fin 17) : List ℤ :=
  (invWord i ++ words17 e i k).foldr (reflectLG .D4) (List.ofFn (vTwoEnds e))

theorem words17_check : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), ∀ i : Fin 5,
    (∀ a b : Fin 17, a ≠ b → vec17 e i a ≠ vec17 e i b) ∧
      (∀ a b : Fin 17, a ≠ b → vec17' e i a ≠ vec17' e i b) ∧
        ∀ a b : Fin 17, vec17 e i a ≠ vec17' e i b := by
  decide +kernel

private theorem reflectLG_vTwoEnds : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), ∀ j : Fin 4,
    j ∉ ({2, e} : Finset (Fin 4)) →
      reflectLG .D4 j (List.ofFn (vTwoEnds e)) = List.ofFn (vTwoEnds e) := by
  decide +kernel

theorem reflect_vTwoEnds : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), ∀ j : Fin 4,
    j ∉ ({2, e} : Finset (Fin 4)) → reflect .D4 j (vTwoEnds e) = vTwoEnds e := by
  intro e he j hj
  have h := ofFn_reflectG (τ := .D4) j (vTwoEnds e)
  have hl := reflectLG_vTwoEnds e he j hj
  exact List.ofFn_injective (h.trans hl)

@[expose] def copiesA : Fin 4 → List (Fin 4) := ![[1, 2], [0, 2], [3, 2], [1, 2]]

@[expose] def copiesPi : Fin 4 → Fin 8 → Fin 8 :=
  ![![2, 4, 0, 5, 1, 3, 7, 6], ![4, 2, 1, 7, 0, 6, 5, 3], ![6, 3, 7, 1, 5, 4, 0, 2],
    ![5, 7, 3, 2, 6, 0, 4, 1]]

@[expose] def copiesR : Fin 4 → Finset (Fin 8) :=
  ![{0, 1, 3, 6}, {0, 1, 3, 5}, {0, 1, 2, 4}, {0, 1, 2, 4}]

private theorem copiesR_ok : ∀ i : Fin 4,
    (∀ j ∈ copiesR i, copiesPi i j ∉ copiesR i) ∧ (copiesR i).card = 4 := by
  decide +kernel

@[expose] def conjWord (i : Fin 4) (j : Fin 8) : List (Fin 4) :=
  copiesA i ++ invWord (Fin.castSucc i) ++ (copiesA i).reverse ++ centerU j

@[expose] def conjVec (i : Fin 4) (j : Fin 8) (k : Fin 4) : List ℤ :=
  (conjWord i j).foldr (reflectLG .D4)
    (List.ofFn (Pi.single k (1 : ℤ) : Fin Tag.D4.rank → ℤ))

@[expose] def conjVec' (i : Fin 4) (j : Fin 8) (k : Fin 4) : List ℤ :=
  (centerU (copiesPi i j)).foldr (reflectLG .D4)
    (List.ofFn (Pi.single k (1 : ℤ) : Fin Tag.D4.rank → ℤ))

theorem conjVec_check : ∀ (i : Fin 4) (j : Fin 8) (k : Fin 4),
    conjVec i j k = conjVec' i j k := by
  decide +kernel

@[expose] def vec24 (e : Fin 4) (k : Fin 24) : List ℤ :=
  (words24 e k).foldr (reflectLG .D4) (List.ofFn (vTwoEnds e))

@[expose] def vec24' (e : Fin 4) (k : Fin 24) : List ℤ :=
  (invWord 4 ++ words24 e k).foldr (reflectLG .D4) (List.ofFn (vTwoEnds e))

theorem words24_check : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)),
    (∀ a b : Fin 24, a ≠ b → vec24 e a ≠ vec24 e b) ∧
      (∀ a b : Fin 24, a ≠ b → vec24' e a ≠ vec24' e b) ∧
        ∀ a b : Fin 24, vec24 e a ≠ vec24' e b := by
  decide +kernel

section Chev


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
  {k V : Type} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V] [Module k V]
  [Module.Finite k V] {ρ : Representation k (adjointGroup .D4 K) V} {y : V}
  {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)}

private theorem wordProd_smul_D4 (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem .D4).wordProd l • v = l.foldr (reflect .D4) v :=
  wordProd_smul' (τ := .D4) l v

private theorem ofFn_foldr_reflectG_D4 (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    List.ofFn (l.foldr (reflect .D4) v) = l.foldr (reflectLG .D4) (List.ofFn v) :=
  ofFn_foldr_reflectG (τ := .D4) l v

private theorem wordProd_append_D4 (l l' : List (Fin 4)) :
    (coxeterSystem .D4).wordProd (l ++ l') =
      (coxeterSystem .D4).wordProd l * (coxeterSystem .D4).wordProd l' :=
  CoxeterSystem.wordProd_append (cs := coxeterSystem .D4) l l'

private theorem range_mul_eq_map {W : Type*} [AddCommGroup W] [Module k W]
    (f g : Module.End k W) :
    LinearMap.range (f * g) = (LinearMap.range g).map f := by
  ext x
  simp only [LinearMap.mem_range, Module.End.mul_apply, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨g y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

private theorem range_sub_one_conj {W G : Type*} [AddCommGroup W] [Module k W]
    [Group G] (ρ : Representation k G W) (g t : G) :
    LinearMap.range (ρ (g * t * g⁻¹) - 1) = (LinearMap.range (ρ t - 1)).map (ρ g) := by
  have hgg : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hgg' : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hsurj : Function.Surjective (ρ g) := fun x => ⟨ρ g⁻¹ x, by
    rw [← Module.End.mul_apply, hgg]; rfl⟩
  have hmul : (ρ (g * t * g⁻¹) - 1) * ρ g = ρ g * (ρ t - 1) := by
    rw [map_mul, map_mul, sub_mul, mul_sub, mul_one, one_mul]
    rw [mul_assoc, hgg', mul_one]
  have hrange : LinearMap.range ((ρ (g * t * g⁻¹) - 1) * ρ g) =
      LinearMap.range (ρ (g * t * g⁻¹) - 1) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      exact ⟨ρ g y, rfl⟩
    · rintro x ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hsurj y
      exact ⟨z, by rw [Module.End.mul_apply, hz]⟩
  rw [← hrange, hmul, range_mul_eq_map]

private theorem seventeen_le_of_case (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (e : Fin 4) (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (i : Fin 5) (hv : ∀ j ∈ J, reflect .D4 j (vTwoEnds e) = vTwoEnds e) :
    17 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i))) - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcheck := words17_check e he i
  refine le_finrank_range_sub_one_of_isChevType (p := 2) hρ ht hv
    ((coxeterSystem .D4).wordProd (invWord i)) (m := 17)
    (fun a => (coxeterSystem .D4).wordProd (words17 e i a)) ?_ ?_
  · intro a b hab h
    refine hcheck.1 a b hab ?_
    have h1 : (words17 e i a).foldr (reflect .D4) (vTwoEnds e) =
        (words17 e i b).foldr (reflect .D4) (vTwoEnds e) := by
      simpa only [wordProd_smul_D4] using h
    have h2 := congrArg List.ofFn h1
    rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
    simpa [vec17] using h2
  · intro a b h
    refine hcheck.2.2 a b ?_
    have h1 : (words17 e i a).foldr (reflect .D4) (vTwoEnds e) =
        (invWord i ++ words17 e i b).foldr (reflect .D4) (vTwoEnds e) := by
      rw [← wordProd_append_D4] at h
      simpa only [wordProd_smul_D4] using h
    have h2 := congrArg List.ofFn h1
    rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
    simpa [vec17, vec17'] using h2

theorem seventeen_le_finrank_range_of_two_ends (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) {e : Fin 4} (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (h2 : (2 : Fin 4) ∉ J) (heJ : e ∉ J) (x : adjointGroup .D4 K) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) :
    17 ≤ Module.finrank k (LinearMap.range (ρ x - 1)) := by
  obtain ⟨i, g, hconj⟩ := exists_conj_eq_nW_invWord (hw := hw) x hx2 hx1
  have hgg' : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinj : Function.Injective (ρ g : V →ₗ[k] V) := fun u v huv => by
    calc u = ρ g⁻¹ (ρ g u) := by rw [← Module.End.mul_apply, hgg']; rfl
      _ = ρ g⁻¹ (ρ g v) := by rw [huv]
      _ = v := by rw [← Module.End.mul_apply, hgg']; rfl
  have hrange : LinearMap.range (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord i))) - 1) =
      (LinearMap.range (ρ x - 1)).map (ρ g) := by
    rw [← hconj]
    exact range_sub_one_conj ρ g x
  have hfin : Module.finrank k (LinearMap.range (ρ x - 1)) =
      Module.finrank k (LinearMap.range (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord i))) - 1)) := by
    rw [hrange]
    exact (Submodule.equivMapOfInjective (ρ g : V →ₗ[k] V) hinj
      (LinearMap.range (ρ x - 1))).finrank_eq
  rw [hfin]
  have hv : ∀ j ∈ J, reflect .D4 j (vTwoEnds e) = vTwoEnds e := by
    intro j hj
    let j4 : Fin 4 := j
    have hj2 : j4 ≠ (2 : Fin 4) := fun h => h2 (h ▸ hj)
    have hje : j4 ≠ e := fun h => heJ (h ▸ hj)
    exact reflect_vTwoEnds e he j4 (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hj2, hje⟩)
  exact seventeen_le_of_case hρ ht e he i hv

private theorem hv_two_ends (e : Fin 4) (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (h2 : (2 : Fin 4) ∉ J) (heJ : e ∉ J) :
    ∀ j ∈ J, reflect .D4 j (vTwoEnds e) = vTwoEnds e := by
  intro j hj
  let j4 : Fin 4 := j
  have hj2 : j4 ≠ (2 : Fin 4) := fun h => h2 (h ▸ hj)
  have hje : j4 ≠ e := fun h => heJ (h ▸ hj)
  exact reflect_vTwoEnds e he j4 (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hj2, hje⟩)

private theorem wordProd_conj_centerU (i : Fin 4) (j : Fin 8) :
    (coxeterSystem .D4).wordProd (copiesA i) *
      (coxeterSystem .D4).wordProd (invWord (Fin.castSucc i)) *
      ((coxeterSystem .D4).wordProd (copiesA i))⁻¹ *
      (coxeterSystem .D4).wordProd (centerU j) =
    (coxeterSystem .D4).wordProd (centerU (copiesPi i j)) := by
  have hrev : (coxeterSystem .D4).wordProd (copiesA i).reverse =
      ((coxeterSystem .D4).wordProd (copiesA i))⁻¹ :=
    (coxeterSystem .D4).wordProd_reverse (copiesA i)
  rw [← hrev]
  simp only [← wordProd_append_D4]
  apply ext_single
  intro k
  rw [wordProd_smul_D4, wordProd_smul_D4]
  apply List.ofFn_injective
  rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4]
  exact conjVec_check i j k

private theorem exists_h_nW_conj_mul {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)
    (a x u q : W) (hq : a * x * a⁻¹ * u = q) :
    ∃ h ∈ D.H, (D.nW a * D.nW x * (D.nW a)⁻¹) * D.nW u = D.nW q * h := by
  obtain ⟨h1, hh1, e1⟩ := nW_inv_mul D a u
  obtain ⟨h0, hh0, e0⟩ := nW_mul D a x
  set n : G := D.nW (a⁻¹ * u) with hn
  have h0' : n⁻¹ * h0 * n ∈ D.H := by
    rw [hn]
    exact D.nW_normH (a⁻¹ * u) hh0
  obtain ⟨h2, hh2, e2⟩ := nW_mul D (a * x) (a⁻¹ * u)
  refine ⟨h2 * (n⁻¹ * h0 * n * h1), mul_mem hh2 (mul_mem h0' hh1), ?_⟩
  have hnm : (a * x) * (a⁻¹ * u) = q := by rw [← hq]; group
  calc (D.nW a * D.nW x * (D.nW a)⁻¹) * D.nW u
      = D.nW a * D.nW x * ((D.nW a)⁻¹ * D.nW u) := by group
    _ = D.nW a * D.nW x * (n * h1) := by rw [e1]
    _ = (D.nW a * D.nW x * n) * h1 := by group
    _ = ((D.nW (a * x) * h0) * n) * h1 := by rw [e0]
    _ = (D.nW (a * x) * (h0 * n)) * h1 := by group
    _ = (D.nW (a * x) * (n * (n⁻¹ * h0 * n))) * h1 := by group
    _ = (D.nW (a * x) * n) * ((n⁻¹ * h0 * n) * h1) := by group
    _ = (D.nW ((a * x) * (a⁻¹ * u)) * h2) * ((n⁻¹ * h0 * n) * h1) := by rw [e2]
    _ = D.nW q * (h2 * (n⁻¹ * h0 * n * h1)) := by rw [hnm]; group

private theorem twentyfour_of_copies (i : Fin 4) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hρ : IsSimpleRep ρ) (ht : IsChevType .D4 K 2 hw ρ y χ J)
    (h2 : (2 : Fin 4) ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (h3 : 3 ≤ n / g)
    (hper : ∀ z : Kˣ, χ (dC .D4 K (2 : Fin 4) z) ^ (2 ^ g) = χ (dC .D4 K (2 : Fin 4) z)) :
    24 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord (Fin.castSucc i)))) - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D : CurtisDatum (adjointGroup .D4 K) (coxeterSystem .D4) 2 := chevDatum .D4 K 2 hw
  let A : WeylGroup .D4 := (coxeterSystem .D4).wordProd (copiesA i)
  let X : WeylGroup .D4 := (coxeterSystem .D4).wordProd (invWord (Fin.castSucc i))
  let b : adjointGroup .D4 K := D.nW A * D.nW X * (D.nW A)⁻¹
  have hb : ∀ j : Fin 8, ∃ h ∈ D.H,
      b * D.nW ((coxeterSystem .D4).wordProd (centerU j)) =
        D.nW ((coxeterSystem .D4).wordProd (centerU (copiesPi i j))) * h := by
    intro j
    have hq : A * X * A⁻¹ * (coxeterSystem .D4).wordProd (centerU j) =
        (coxeterSystem .D4).wordProd (centerU (copiesPi i j)) := by
      simpa [A, X] using wordProd_conj_centerU i j
    simpa [b] using exists_h_nW_conj_mul D A X
      ((coxeterSystem .D4).wordProd (centerU j))
      ((coxeterSystem .D4).wordProd (centerU (copiesPi i j))) hq
  have hR : ∀ j ∈ copiesR i, copiesPi i j ∉ copiesR i := (copiesR_ok i).1
  have hcard : (copiesR i).card = 4 := (copiesR_ok i).2
  have hbound := copies_rank_two_pow (τ := .D4) (n := n) (K := K) (k := k) (V := V)
    (hw := hw) hn hK hρ ht (s := (2 : Fin 4)) h2 hg hgn hper
    (u := fun j => (coxeterSystem .D4).wordProd (centerU j))
    (hu := fun j => centerU_smul j) (hli := linearIndependent_centerU hρ ht h2)
    (b := b) (π := copiesPi i) (hb := hb) (R := copiesR i) hR
  rw [hcard] at hbound
  have hpow : 8 ≤ 2 ^ (n / g) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n / g) := Nat.pow_le_pow_right (by norm_num) h3
  have h24 : 24 ≤ 4 * 2 ^ (n / g) := by
    calc 24 ≤ 4 * 8 := by norm_num
      _ ≤ 4 * 2 ^ (n / g) := Nat.mul_le_mul_left 4 hpow
  have hb24 : 24 ≤ Module.finrank k (LinearMap.range (ρ b - 1)) := le_trans h24 hbound
  have hconj : Module.finrank k (LinearMap.range (ρ b - 1)) =
      Module.finrank k (LinearMap.range (ρ (D.nW X) - 1)) := by
    have hgg : ρ (D.nW A)⁻¹ * ρ (D.nW A) = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hinj : Function.Injective (ρ (D.nW A) : V →ₗ[k] V) := fun u v huv => by
      calc u = ρ (D.nW A)⁻¹ (ρ (D.nW A) u) := by rw [← Module.End.mul_apply, hgg]; rfl
        _ = ρ (D.nW A)⁻¹ (ρ (D.nW A) v) := by rw [huv]
        _ = v := by rw [← Module.End.mul_apply, hgg]; rfl
    rw [show b = D.nW A * D.nW X * (D.nW A)⁻¹ from rfl,
      range_sub_one_conj ρ (D.nW A) (D.nW X)]
    exact (Submodule.equivMapOfInjective (ρ (D.nW A) : V →ₗ[k] V) hinj _).finrank_eq.symm
  rw [← hconj]
  exact hb24

private theorem twentyfour_of_w0 (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (e : Fin 4)
    (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (hv : ∀ j ∈ J, reflect .D4 j (vTwoEnds e) = vTwoEnds e) :
    24 ≤ Module.finrank k (LinearMap.range
      (ρ ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord 4))) - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcheck := words24_check e he
  refine le_finrank_range_sub_one_of_isChevType (p := 2) hρ ht hv
    ((coxeterSystem .D4).wordProd (invWord 4)) (m := 24)
    (fun a => (coxeterSystem .D4).wordProd (words24 e a)) ?_ ?_
  · intro a b hab h
    refine hcheck.1 a b hab ?_
    have h1 : (words24 e a).foldr (reflect .D4) (vTwoEnds e) =
        (words24 e b).foldr (reflect .D4) (vTwoEnds e) := by
      simpa only [wordProd_smul_D4] using h
    have h2 := congrArg List.ofFn h1
    rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
    simpa [vec24] using h2
  · intro a b h
    refine hcheck.2.2 a b ?_
    have h1 : (words24 e a).foldr (reflect .D4) (vTwoEnds e) =
        (invWord 4 ++ words24 e b).foldr (reflect .D4) (vTwoEnds e) := by
      rw [← wordProd_append_D4] at h
      simpa only [wordProd_smul_D4] using h
    have h2 := congrArg List.ofFn h1
    rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
    simpa [vec24, vec24'] using h2

theorem twentyfour_le_finrank_range_of_two_ends {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (hρ : IsSimpleRep ρ) (ht : IsChevType .D4 K 2 hw ρ y χ J)
    {e : Fin 4} (he : e ∈ ({0, 1, 3} : Finset (Fin 4))) (h2 : (2 : Fin 4) ∉ J)
    (heJ : e ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (h3 : 3 ≤ n / g)
    (hper : ∀ z : Kˣ, χ (dC .D4 K (2 : Fin 4) z) ^ (2 ^ g) = χ (dC .D4 K (2 : Fin 4) z))
    (x : adjointGroup .D4 K) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    24 ≤ Module.finrank k (LinearMap.range (ρ x - 1)) := by
  obtain ⟨i, g', hconj⟩ := exists_conj_eq_nW_invWord (hw := hw) x hx2 hx1
  have hgg' : ρ g'⁻¹ * ρ g' = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinj : Function.Injective (ρ g' : V →ₗ[k] V) := fun u v huv => by
    calc u = ρ g'⁻¹ (ρ g' u) := by rw [← Module.End.mul_apply, hgg']; rfl
      _ = ρ g'⁻¹ (ρ g' v) := by rw [huv]
      _ = v := by rw [← Module.End.mul_apply, hgg']; rfl
  have hrange : LinearMap.range (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord i))) - 1) =
      (LinearMap.range (ρ x - 1)).map (ρ g') := by
    rw [← hconj]
    exact range_sub_one_conj ρ g' x
  have hfin : Module.finrank k (LinearMap.range (ρ x - 1)) =
      Module.finrank k (LinearMap.range (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord i))) - 1)) := by
    rw [hrange]
    exact (Submodule.equivMapOfInjective (ρ g' : V →ₗ[k] V) hinj
      (LinearMap.range (ρ x - 1))).finrank_eq
  rw [hfin]
  have hv := hv_two_ends e he h2 heJ
  fin_cases i
  · exact twentyfour_of_copies (0 : Fin 4) hn hK hρ ht h2 hg hgn h3 hper
  · exact twentyfour_of_copies (1 : Fin 4) hn hK hρ ht h2 hg hgn h3 hper
  · exact twentyfour_of_copies (2 : Fin 4) hn hK hρ ht h2 hg hgn h3 hper
  · exact twentyfour_of_copies (3 : Fin 4) hn hK hρ ht h2 hg hgn h3 hper
  · exact twentyfour_of_w0 hρ ht e he hv

end Chev

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
