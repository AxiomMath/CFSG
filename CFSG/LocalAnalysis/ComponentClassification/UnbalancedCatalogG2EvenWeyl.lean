module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.LieType.Chevalley.BruhatDecomposition
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.TorusCoordinates
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def g2Pair (v : Fin Tag.G2.rank → ℤ) : ℤ × ℤ := (v g2ia, v g2ir)

theorem g2Pair_injective : Function.Injective g2Pair := by
  intro v w h
  simp only [g2Pair, Prod.mk.injEq] at h
  funext i
  match i with
  | ⟨0, _⟩ => exact h.1
  | ⟨1, _⟩ => exact h.2

theorem g2Pair_add (v w : Fin Tag.G2.rank → ℤ) : g2Pair (v + w) = g2Pair v + g2Pair w := rfl

theorem g2Pair_neg (v : Fin Tag.G2.rank → ℤ) : g2Pair (-v) = -g2Pair v := rfl

@[expose] def g2RootPairs : List (ℤ × ℤ) :=
  [(0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 3), (0, -1), (-1, 0), (-1, -1), (-1, -2),
    (-1, -3), (-2, -3)]

theorem g2Pair_mem_of_isRoot {v : Fin Tag.G2.rank → ℤ} (hv : IsRoot .G2 v) :
    g2Pair v ∈ g2RootPairs := by
  rcases g2_root_cases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

@[expose] def g2WeylPairs : List ((ℤ × ℤ) × (ℤ × ℤ)) :=
  [((1, 0), (0, 1)), ((-1, 0), (1, 1)), ((1, 3), (0, -1)), ((2, 3), (-1, -1)),
    ((-1, -3), (1, 2)), ((-2, -3), (1, 2)), ((2, 3), (-1, -2)), ((-2, -3), (1, 1)),
    ((1, 3), (-1, -2)), ((-1, -3), (0, 1)), ((1, 0), (-1, -1)), ((-1, 0), (0, -1))]

theorem g2WeylPairs_check : ∀ p ∈ g2RootPairs, ∀ q ∈ g2RootPairs,
    (p + q ∈ g2RootPairs ∧ p + (q + q) ∈ g2RootPairs ∧ p + (q + q + q) ∈ g2RootPairs) →
      (p, q) ∈ g2WeylPairs := by
  decide

theorem g2u_eq_add : g2u = g2a + g2r := List.ofFn_injective (by decide +kernel)
theorem g2v_eq_add : g2v = g2a + (g2r + g2r) := List.ofFn_injective (by decide +kernel)
theorem g2b_eq_add : g2b = g2a + (g2r + g2r + g2r) := List.ofFn_injective (by decide +kernel)
theorem g2c_eq_add : g2c = g2a + g2a + (g2r + g2r + g2r) := List.ofFn_injective (by decide +kernel)

theorem g2Pair_g2a : g2Pair g2a = (1, 0) := rfl
theorem g2Pair_g2r : g2Pair g2r = (0, 1) := rfl
theorem g2Pair_g2u : g2Pair g2u = (1, 1) := rfl
theorem g2Pair_g2v : g2Pair g2v = (1, 2) := rfl
theorem g2Pair_g2b : g2Pair g2b = (1, 3) := rfl
theorem g2Pair_g2c : g2Pair g2c = (2, 3) := rfl

theorem eq_of_g2Pair {v w : Fin Tag.G2.rank → ℤ} (h : g2Pair v = g2Pair w) : v = w :=
  g2Pair_injective h

theorem g2_weyl_cases (w : WeylGroup .G2) :
    (w • g2a = g2a ∧ w • g2r = g2r) ∨ (w • g2a = -g2a ∧ w • g2r = g2u) ∨
    (w • g2a = g2b ∧ w • g2r = -g2r) ∨ (w • g2a = g2c ∧ w • g2r = -g2u) ∨
    (w • g2a = -g2b ∧ w • g2r = g2v) ∨ (w • g2a = -g2c ∧ w • g2r = g2v) ∨
    (w • g2a = g2c ∧ w • g2r = -g2v) ∨ (w • g2a = -g2c ∧ w • g2r = g2u) ∨
    (w • g2a = g2b ∧ w • g2r = -g2v) ∨ (w • g2a = -g2b ∧ w • g2r = g2r) ∨
    (w • g2a = g2a ∧ w • g2r = -g2u) ∨ (w • g2a = -g2a ∧ w • g2r = -g2r) := by
  have hp := g2Pair_mem_of_isRoot (IsRoot.smul isRoot_g2a w)
  have hq := g2Pair_mem_of_isRoot (IsRoot.smul isRoot_g2r w)
  have h1 := g2Pair_mem_of_isRoot (IsRoot.smul isRoot_g2u w)
  have h2 := g2Pair_mem_of_isRoot (IsRoot.smul isRoot_g2v w)
  have h3 := g2Pair_mem_of_isRoot (IsRoot.smul isRoot_g2b w)
  rw [g2u_eq_add, smul_add, g2Pair_add] at h1
  rw [g2v_eq_add, smul_add, smul_add, g2Pair_add, g2Pair_add] at h2
  rw [g2b_eq_add, smul_add, smul_add, smul_add, g2Pair_add, g2Pair_add, g2Pair_add] at h3
  have key := g2WeylPairs_check _ hp _ hq ⟨h1, h2, h3⟩
  simp only [g2WeylPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at key
  rcases key with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩
  · exact Or.inl ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩
  · exact Or.inr (Or.inl ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_of_g2Pair ha,
      eq_of_g2Pair hr⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_of_g2Pair ha,
      eq_of_g2Pair hr⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eq_of_g2Pair ha,
      eq_of_g2Pair hr⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨eq_of_g2Pair ha, eq_of_g2Pair hr⟩))))))))))

theorem smul_g2u (w : WeylGroup .G2) : w • g2u = w • g2a + w • g2r := by
  rw [g2u_eq_add, smul_add]

theorem smul_g2v (w : WeylGroup .G2) : w • g2v = w • g2a + (w • g2r + w • g2r) := by
  rw [g2v_eq_add, smul_add, smul_add]

theorem smul_g2b (w : WeylGroup .G2) : w • g2b = w • g2a + (w • g2r + w • g2r + w • g2r) := by
  rw [g2b_eq_add, smul_add, smul_add, smul_add]

theorem smul_g2c (w : WeylGroup .G2) :
    w • g2c = w • g2a + w • g2a + (w • g2r + w • g2r + w • g2r) := by
  rw [g2c_eq_add, smul_add, smul_add, smul_add, smul_add]

theorem g2a_eq_single : g2a = Pi.single g2ia 1 := List.ofFn_injective (by decide +kernel)
theorem g2r_eq_single : g2r = Pi.single g2ir 1 := List.ofFn_injective (by decide +kernel)

theorem eq_one_of_smul {w : WeylGroup .G2} (ha : w • g2a = g2a) (hr : w • g2r = g2r) : w = 1 := by
  refine ext_single fun i => ?_
  rw [one_smul]
  fin_cases i
  · change w • Pi.single g2ia 1 = Pi.single g2ia 1
    rw [← g2a_eq_single, ha]
  · change w • Pi.single g2ir 1 = Pi.single g2ir 1
    rw [← g2r_eq_single, hr]

theorem eq_simple_a_of_smul {w : WeylGroup .G2} (ha : w • g2a = -g2a) (hr : w • g2r = g2u) :
    w = simple .G2 g2ia := by
  refine ext_single fun i => ?_
  rw [simple_smul]
  fin_cases i
  · change w • Pi.single g2ia 1 = reflect .G2 g2ia (Pi.single g2ia 1)
    rw [← g2a_eq_single, ha]
    exact List.ofFn_injective (by decide +kernel)
  · change w • Pi.single g2ir 1 = reflect .G2 g2ia (Pi.single g2ir 1)
    rw [← g2r_eq_single, hr]
    exact List.ofFn_injective (by decide +kernel)

theorem eq_simple_r_of_smul {w : WeylGroup .G2} (ha : w • g2a = g2b) (hr : w • g2r = -g2r) :
    w = simple .G2 g2ir := by
  refine ext_single fun i => ?_
  rw [simple_smul]
  fin_cases i
  · change w • Pi.single g2ia 1 = reflect .G2 g2ir (Pi.single g2ia 1)
    rw [← g2a_eq_single, ha]
    exact List.ofFn_injective (by decide +kernel)
  · change w • Pi.single g2ir 1 = reflect .G2 g2ir (Pi.single g2ir 1)
    rw [← g2r_eq_single, hr]
    exact List.ofFn_injective (by decide +kernel)

@[expose] def g2LongestWeyl : WeylGroup .G2 := (simple .G2 g2ia * simple .G2 g2ir) ^ 3

theorem g2LongestWeyl_smul_g2a : g2LongestWeyl • g2a = -g2a := by
  simp only [g2LongestWeyl, pow_succ, pow_zero, one_mul, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2LongestWeyl_smul_g2r : g2LongestWeyl • g2r = -g2r := by
  simp only [g2LongestWeyl, pow_succ, pow_zero, one_mul, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2LongestWeyl_smul_neg (v : Fin Tag.G2.rank → ℤ) (hv : v = g2r ∨ v = g2a ∨ v = g2u ∨
    v = g2v ∨ v = g2b ∨ v = g2c) : g2LongestWeyl • (-v) = v := by
  rw [smul_neg, neg_eq_iff_eq_neg]
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact g2LongestWeyl_smul_g2r
  · exact g2LongestWeyl_smul_g2a
  · rw [smul_g2u, g2LongestWeyl_smul_g2a, g2LongestWeyl_smul_g2r]
    exact List.ofFn_injective (by decide +kernel)
  · rw [smul_g2v, g2LongestWeyl_smul_g2a, g2LongestWeyl_smul_g2r]
    exact List.ofFn_injective (by decide +kernel)
  · rw [smul_g2b, g2LongestWeyl_smul_g2a, g2LongestWeyl_smul_g2r]
    exact List.ofFn_injective (by decide +kernel)
  · rw [smul_g2c, g2LongestWeyl_smul_g2a, g2LongestWeyl_smul_g2r]
    exact List.ofFn_injective (by decide +kernel)

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem canonicalRep_conj [CharP K 2] (w : WeylGroup .G2) {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) (x : K) :
    canonicalRep (coxeterSystem .G2) K w * X α x * (canonicalRep (coxeterSystem .G2) K w)⁻¹ =
      X (w • α) x := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hα
  rw [h, eq_one_of_mul_self_eq_one_two hε, one_mul]

theorem longest_conj_neg [CharP K 2] {γ : Fin Tag.G2.rank → ℤ} (hγ : γ = g2r ∨ γ = g2a ∨
    γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (x : K) :
    canonicalRep (coxeterSystem .G2) K g2LongestWeyl * X (-γ) x *
      (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹ = X γ x := by
  have hr : IsRoot .G2 γ := by
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [isRoot_g2r, isRoot_g2a, isRoot_g2u, isRoot_g2v, isRoot_g2b, isRoot_g2c]
  rw [canonicalRep_conj g2LongestWeyl (IsRoot.neg hr), g2LongestWeyl_smul_neg γ hγ]

theorem exists_eq_torusElt_mul {h : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K) :
    ∃ t₁ t₂ : Kˣ, h = torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ := by
  obtain ⟨t, ht⟩ := torusCoordHom_surjective (τ := .G2) (R := K) ⟨h, hh⟩
  refine ⟨t g2ia, t g2ir, ?_⟩
  have e : (torusCoordHom .G2 K t : ModGL .G2 K) = h := congrArg Subtype.val ht
  rw [← e]
  change (List.ofFn (n := 2) fun i => torusElt .G2 K i (t i)).prod = _
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem torus_conj {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (t₁ t₂ : Kˣ) (x : K) :
    torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * X α x *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ =
      X α (((t₁ ^ (∑ j, Tag.G2.cartan g2ia j * α j) * t₂ ^ (∑ j, Tag.G2.cartan g2ir j * α j) :
        Kˣ) : K) * x) := by
  have e : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * X α x *
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ =
      torusElt .G2 K g2ia t₁ * (torusElt .G2 K g2ir t₂ * X α x * (torusElt .G2 K g2ir t₂)⁻¹) *
        (torusElt .G2 K g2ia t₁)⁻¹ := by group
  rw [e, root_torus_conjugation g2ir hα, root_torus_conjugation g2ia hα, ← mul_assoc,
    ← Units.val_mul]

theorem exists_torus_scale {h : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ c : Kˣ, ∀ x, h * X α x * h⁻¹ = X α (c * x) := by
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  exact ⟨_, fun x => torus_conj hα t₁ t₂ x⟩

theorem exists_torus_mul_of_mem_borel {b : ModGL .G2 K} (hb : b ∈ borelGroup .G2 K) :
    ∃ h ∈ torusGroup .G2 K, ∃ u ∈ posUnipotent .G2 K, b = h * u := by
  have hb' : b ∈ (borelGroup .G2 K : Set (ModGL .G2 K)) := hb
  rw [(triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.1] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  exact ⟨h, hh, u, hu, rfl⟩

theorem torus_conj_mem_posUnipotent {h u : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K)
    (hu : u ∈ posUnipotent .G2 K) : h * u * h⁻¹ ∈ posUnipotent .G2 K :=
  (Subgroup.mem_normalizer_iff.1 ((triangular_borel_structure.{0, 0} .G2 K).2.2.1 hh) u).1 hu

theorem exists_bruhat {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K) :
    ∃ w : WeylGroup .G2, ∃ b₁ ∈ borelGroup .G2 K, ∃ b₂ ∈ borelGroup .G2 K,
      g = b₁ * canonicalRep (coxeterSystem .G2) K w * b₂ := by
  have hg' : g ∈ (adjointGroup .G2 K : Set (ModGL .G2 K)) := hg
  rw [adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hw
  exact ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩

theorem pinnedX_neg_mem_negUnipotent {γ : Fin Tag.G2.rank → ℤ} (hγ : γ = g2r ∨ γ = g2a ∨
    γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (x : K) : X (-γ) x ∈ negUnipotent .G2 K := by
  show X (-γ) x ∈ rootSpan .G2 K {α | IsRoot .G2 α ∧ height α < 0}
  refine pinnedX_mem_rootSpan (S := {α | IsRoot .G2 α ∧ height α < 0}) ⟨?_, ?_⟩ x
  · rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [IsRoot.neg isRoot_g2r, IsRoot.neg isRoot_g2a, IsRoot.neg isRoot_g2u,
      IsRoot.neg isRoot_g2v, IsRoot.neg isRoot_g2b, IsRoot.neg isRoot_g2c]
  · rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem eq_one_of_mem_borel_of_mem_neg {g : ModGL .G2 K} (hg : g ∈ borelGroup .G2 K)
    (hg' : g ∈ negUnipotent .G2 K) : g = 1 := by
  have h : g ∈ borelGroup .G2 K ⊓ negUnipotent .G2 K := Subgroup.mem_inf.2 ⟨hg, hg'⟩
  rwa [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at h

theorem posUnipotent_le_borelGroup : posUnipotent .G2 K ≤ borelGroup .G2 K := le_sup_right

end CFSG.ComponentClassification.UnbalancedCatalog
