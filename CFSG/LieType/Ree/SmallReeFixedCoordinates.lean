module

public import CFSG.LieType.Ree.SmallReeRootParameters
public import CFSG.LieType.Ree.SmallReeFieldPowers
public import CFSG.LieType.Ree.FixedBruhatDecomposition

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def smallReeP
    (R : Type*) [CommRing R] (c₀ c₁ c₂ c₃ c₄ c₅ : R) :
    (Module.End R (RootModule Tag.G2 R))ˣ :=
  smallReeX R 0 c₀ * smallReeX R 1 c₁ * smallReeX R 2 c₂ * smallReeX R 3 c₃ *
    smallReeX R 4 c₄ * smallReeX R 5 c₅

theorem smallReeCoord_eq_smallReeP
    (a : ℕ) (R : Type*) [CommRing R] (t b c : R) :
    smallReeCoord a R t b c = smallReeP R t (smallReeSigma a t) b c
      (smallReeSigma a b - t ^ 3 * smallReeSigma a t)
      (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2) :=
  rfl

section Relations

variable {R : Type*} [CommRing R]

theorem smallReeX_add
    (i : Fin 6) (c d : R) :
    smallReeX R i (c + d) = smallReeX R i c * smallReeX R i d :=
  pinnedX_add Tag.G2 R _ c d

theorem smallReeX_zero
    (i : Fin 6) : smallReeX R i 0 = 1 :=
  pinnedX_zero Tag.G2 R _

theorem smallReeX_mul_mul
    (i : Fin 6) (p q : R) (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeX R i p * (smallReeX R i q * Z) = smallReeX R i (p + q) * Z := by
  rw [← mul_assoc, ← smallReeX_add]

theorem smallReeP_mul_X5_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ x : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeX R 5 x * Z) =
      smallReeP R c₀ c₁ c₂ c₃ c₄ (c₅ + x) * Z := by
  simp only [smallReeP, mul_assoc]
  rw [smallReeX_mul_mul]

theorem smallReeCommPairs_spec : ∀ p ∈ smallReeCommPairs,
    p.1 < p.2 ∧ p ≠ (0, 1) ∧ p ≠ (0, 2) ∧ p ≠ (1, 4) := by
  decide

variable (h3 : (3 : R) = 0)
include h3

theorem smallRee_comm_mul
    {i j : Fin 6} (hij : (i, j) ∈ smallReeCommPairs) (x y : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeX R j y * (smallReeX R i x * Z) = smallReeX R i x * (smallReeX R j y * Z) := by
  obtain ⟨h1, h2, h4, h5⟩ := smallReeCommPairs_spec (i, j) hij
  rw [← mul_assoc, (small_Ree_collection_of_three_eq_zero h3 x y).2.2.2 i j h1 h2 h4 h5,
    mul_assoc]

theorem smallRee_swap01_mul
    (x y : R) (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeX R 1 y * (smallReeX R 0 x * Z) =
      smallReeX R 0 x * (smallReeX R 1 y * (smallReeX R 2 (x * y) * (smallReeX R 3 (x ^ 2 * y) *
        (smallReeX R 4 (-(x ^ 3 * y)) * (smallReeX R 5 (-(x ^ 3 * y ^ 2)) * Z))))) := by
  rw [← mul_assoc, (small_Ree_collection_of_three_eq_zero h3 x y).1]
  simp only [mul_assoc]

theorem smallRee_swap02_mul
    (x y : R) (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeX R 2 y * (smallReeX R 0 x * Z) =
      smallReeX R 0 x * (smallReeX R 2 y * (smallReeX R 3 (-(x * y)) * Z)) := by
  rw [← mul_assoc, (small_Ree_collection_of_three_eq_zero h3 x y).2.1]
  simp only [mul_assoc]

theorem smallRee_swap14_mul
    (x y : R) (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeX R 4 y * (smallReeX R 1 x * Z) =
      smallReeX R 1 x * (smallReeX R 4 y * (smallReeX R 5 (-(x * y)) * Z)) := by
  rw [← mul_assoc, (small_Ree_collection_of_three_eq_zero h3 x y).2.2.1]
  simp only [mul_assoc]

theorem smallReeP_mul_X4_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ x : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeX R 4 x * Z) =
      smallReeP R c₀ c₁ c₂ c₃ (c₄ + x) c₅ * Z := by
  simp only [smallReeP, mul_assoc]
  rw [smallRee_comm_mul h3 (i := 4) (j := 5) (by decide), smallReeX_mul_mul]

theorem smallReeP_mul_X3_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ x : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeX R 3 x * Z) =
      smallReeP R c₀ c₁ c₂ (c₃ + x) c₄ c₅ * Z := by
  simp only [smallReeP, mul_assoc]
  rw [smallRee_comm_mul h3 (i := 3) (j := 5) (by decide),
    smallRee_comm_mul h3 (i := 3) (j := 4) (by decide), smallReeX_mul_mul]

theorem smallReeP_mul_X2_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ x : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeX R 2 x * Z) =
      smallReeP R c₀ c₁ (c₂ + x) c₃ c₄ c₅ * Z := by
  simp only [smallReeP, mul_assoc]
  rw [smallRee_comm_mul h3 (i := 2) (j := 5) (by decide),
    smallRee_comm_mul h3 (i := 2) (j := 4) (by decide),
    smallRee_comm_mul h3 (i := 2) (j := 3) (by decide), smallReeX_mul_mul]

theorem smallReeP_mul_X1_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ x : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeX R 1 x * Z) =
      smallReeP R c₀ (c₁ + x) c₂ c₃ c₄ (-(x * c₄) + c₅) * Z := by
  simp only [smallReeP, mul_assoc]
  rw [smallRee_comm_mul h3 (i := 1) (j := 5) (by decide), smallRee_swap14_mul h3,
    smallRee_comm_mul h3 (i := 1) (j := 3) (by decide),
    smallRee_comm_mul h3 (i := 1) (j := 2) (by decide), smallReeX_mul_mul, smallReeX_mul_mul]

theorem smallReeP_mul_X0_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ x : R)
    (Z : (Module.End R (RootModule Tag.G2 R))ˣ) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * (smallReeX R 0 x * Z) =
      smallReeP R (c₀ + x) c₁ (x * c₁ + c₂) (x ^ 2 * c₁ + -(x * c₂) + c₃)
        (-(x ^ 3 * c₁) + c₄) (-(x ^ 3 * c₁ ^ 2) + c₅) * Z := by
  simp only [smallReeP, mul_assoc]
  rw [smallRee_comm_mul h3 (i := 0) (j := 5) (by decide),
    smallRee_comm_mul h3 (i := 0) (j := 4) (by decide),
    smallRee_comm_mul h3 (i := 0) (j := 3) (by decide), smallRee_swap02_mul h3,
    smallRee_swap01_mul h3, smallReeX_mul_mul,
    smallRee_comm_mul h3 (i := 2) (j := 5) (by decide),
    smallRee_comm_mul h3 (i := 2) (j := 4) (by decide),
    smallRee_comm_mul h3 (i := 2) (j := 3) (by decide), smallReeX_mul_mul,
    smallRee_comm_mul h3 (i := 3) (j := 5) (by decide),
    smallRee_comm_mul h3 (i := 3) (j := 4) (by decide), smallReeX_mul_mul,
    smallRee_comm_mul h3 (i := 3) (j := 5) (by decide),
    smallRee_comm_mul h3 (i := 3) (j := 4) (by decide), smallReeX_mul_mul,
    smallRee_comm_mul h3 (i := 4) (j := 5) (by decide), smallReeX_mul_mul, smallReeX_mul_mul]

theorem smallReeP_mul
    (c₀ c₁ c₂ c₃ c₄ c₅ d₀ d₁ d₂ d₃ d₄ d₅ : R) :
    smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ * smallReeP R d₀ d₁ d₂ d₃ d₄ d₅ =
      smallReeP R (c₀ + d₀) (c₁ + d₁) (c₂ + d₂ + d₀ * c₁) (c₃ + d₃ + d₀ ^ 2 * c₁ - d₀ * c₂)
        (c₄ + d₄ - d₀ ^ 3 * c₁) (c₅ + d₅ - d₀ ^ 3 * c₁ ^ 2 - d₁ * (c₄ - d₀ ^ 3 * c₁)) := by
  have e : smallReeP R d₀ d₁ d₂ d₃ d₄ d₅ = smallReeX R 0 d₀ * (smallReeX R 1 d₁ *
      (smallReeX R 2 d₂ * (smallReeX R 3 d₃ * (smallReeX R 4 d₄ * (smallReeX R 5 d₅ * 1))))) := by
    simp only [smallReeP, mul_one, mul_assoc]
  rw [e, smallReeP_mul_X0_mul h3, smallReeP_mul_X1_mul h3, smallReeP_mul_X2_mul h3,
    smallReeP_mul_X3_mul h3, smallReeP_mul_X4_mul h3, smallReeP_mul_X5_mul, mul_one]
  congr 1 <;> ring

theorem smallReeX_word_eq_smallReeP
    (x y p q r w : R) :
    smallReeX R 1 y * smallReeX R 0 x * smallReeX R 4 p * smallReeX R 5 q * smallReeX R 2 r *
        smallReeX R 3 w =
      smallReeP R x y (r + y * x) (w + y * x ^ 2) (p - y * x ^ 3) (q - y ^ 2 * x ^ 3) := by
  have e : smallReeX R 1 y * smallReeX R 0 x * smallReeX R 4 p * smallReeX R 5 q *
      smallReeX R 2 r * smallReeX R 3 w = smallReeP R 0 y 0 0 0 0 * (smallReeX R 0 x *
        (smallReeX R 4 p * (smallReeX R 5 q * (smallReeX R 2 r * (smallReeX R 3 w * 1))))) := by
    simp only [smallReeP, smallReeX_zero, one_mul, mul_one, mul_assoc]
  rw [e, smallReeP_mul_X0_mul h3, smallReeP_mul_X4_mul h3, smallReeP_mul_X5_mul,
    smallReeP_mul_X2_mul h3, smallReeP_mul_X3_mul h3, mul_one]
  congr 1 <;> ring

end Relations

section Bijection

theorem smallReeRoot_injective : Function.Injective smallReeRoot := by
  intro i j
  revert i j
  decide

theorem smallReePos_check : ∀ k < Tag.G2.rootCertificate.roots.length,
    0 < height (Tag.G2.rootCertificate.root k) →
      ∃ i : Fin 6, smallReeRoot i = Tag.G2.rootCertificate.root k := by
  decide

theorem range_smallReeRoot :
    Set.range smallReeRoot = {β | IsRoot Tag.G2 β ∧ 0 < height β} := by
  ext β
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨RootOps.isRootB_iff.1 (smallReeRoot_check i).1, (smallReeRoot_check i).2⟩
  · rintro ⟨hβ, hpos⟩
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.G2) hβ
    exact smallReePos_check k hk hpos

theorem smallReeP_eq_ofFn
    {R : Type*} [CommRing R] (v : Fin 6 → R) :
    smallReeP R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) =
      (List.ofFn fun i => pinnedX Tag.G2 R (smallReeRoot i) (v i)).prod := by
  simp only [smallReeP, smallReeX, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc]
  rfl

theorem bijOn_smallReeP
    (R : Type) [CommRing R] :
    Set.BijOn (fun v : Fin 6 → R => smallReeP R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) Set.univ
      (posUnipotent Tag.G2 R) := by
  have e : (fun v : Fin 6 → R => smallReeP R (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) =
      fun v => (List.ofFn fun i => pinnedX Tag.G2 R (smallReeRoot i) (v i)).prod :=
    funext smallReeP_eq_ofFn
  rw [e]
  exact (positive_root_collection Tag.G2 R).2 smallReeRoot smallReeRoot_injective
    range_smallReeRoot

theorem smallReeP_injective
    {R : Type} [CommRing R] {c₀ c₁ c₂ c₃ c₄ c₅ d₀ d₁ d₂ d₃ d₄ d₅ : R}
    (h : smallReeP R c₀ c₁ c₂ c₃ c₄ c₅ = smallReeP R d₀ d₁ d₂ d₃ d₄ d₅) :
    c₀ = d₀ ∧ c₁ = d₁ ∧ c₂ = d₂ ∧ c₃ = d₃ ∧ c₄ = d₄ ∧ c₅ = d₅ := by
  have hv := (bijOn_smallReeP R).2.1 (Set.mem_univ ![c₀, c₁, c₂, c₃, c₄, c₅])
    (Set.mem_univ ![d₀, d₁, d₂, d₃, d₄, d₅]) h
  exact ⟨congrFun hv 0, congrFun hv 1, congrFun hv 2, congrFun hv 3, congrFun hv 4,
    congrFun hv 5⟩

end Bijection

namespace ReeTag

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

omit [Finite K] in
theorem smallRee_three_eq_zero : (3 : K) = 0 := by
  have h : ((3 : ℕ) : K) = 0 := CharP.cast_eq_zero K G2.prime
  exact_mod_cast h

omit [Finite K] [CharP K G2.prime] in
theorem smallReeP_mem_adjointGroup
    (c₀ c₁ c₂ c₃ c₄ c₅ : K) :
    smallReeP K c₀ c₁ c₂ c₃ c₄ c₅ ∈ adjointGroup G2.tag K :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ c₀)
    (pinnedX_mem_adjointGroup _ c₁)) (pinnedX_mem_adjointGroup _ c₂))
    (pinnedX_mem_adjointGroup _ c₃)) (pinnedX_mem_adjointGroup _ c₄))
    (pinnedX_mem_adjointGroup _ c₅)

omit [Finite K] [CharP K G2.prime] in
theorem smallReeCoord_mem_adjointGroup
    (t b c : K) :
    smallReeCoord a K t b c ∈ adjointGroup G2.tag K :=
  smallReeP_mem_adjointGroup _ _ _ _ _ _

theorem finiteReeAut_smallReeP
    (c₀ c₁ c₂ c₃ c₄ c₅ : K) :
    ((G2.finiteReeAut K a ⟨smallReeP K c₀ c₁ c₂ c₃ c₄ c₅,
        smallReeP_mem_adjointGroup c₀ c₁ c₂ c₃ c₄ c₅⟩ : adjointGroup G2.tag K) : ModGL G2.tag K) =
      smallReeP K (c₁ ^ 3 ^ a) (smallReeSigma a c₀)
        (c₄ ^ 3 ^ a + smallReeSigma a c₀ * c₁ ^ 3 ^ a)
        (c₅ ^ 3 ^ a + smallReeSigma a c₀ * (c₁ ^ 3 ^ a) ^ 2)
        (smallReeSigma a c₂ - smallReeSigma a c₀ * (c₁ ^ 3 ^ a) ^ 3)
        (smallReeSigma a c₃ - smallReeSigma a c₀ ^ 2 * (c₁ ^ 3 ^ a) ^ 3) := by
  have h3 := smallRee_three_eq_zero (K := K)
  have e : (⟨smallReeP K c₀ c₁ c₂ c₃ c₄ c₅, smallReeP_mem_adjointGroup c₀ c₁ c₂ c₃ c₄ c₅⟩ :
      adjointGroup G2.tag K) =
      ⟨smallReeX K 0 c₀, pinnedX_mem_adjointGroup _ c₀⟩ *
        ⟨smallReeX K 1 c₁, pinnedX_mem_adjointGroup _ c₁⟩ *
        ⟨smallReeX K 2 c₂, pinnedX_mem_adjointGroup _ c₂⟩ *
        ⟨smallReeX K 3 c₃, pinnedX_mem_adjointGroup _ c₃⟩ *
        ⟨smallReeX K 4 c₄, pinnedX_mem_adjointGroup _ c₄⟩ *
        ⟨smallReeX K 5 c₅, pinnedX_mem_adjointGroup _ c₅⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, map_mul, map_mul,
    (small_Ree_positive_root_F_parameters K a c₀).1,
    (small_Ree_positive_root_F_parameters K a c₁).2.1,
    (small_Ree_positive_root_F_parameters K a c₂).2.2.1,
    (small_Ree_positive_root_F_parameters K a c₃).2.2.2.2.1,
    (small_Ree_positive_root_F_parameters K a c₄).2.2.2.1,
    (small_Ree_positive_root_F_parameters K a c₅).2.2.2.2.2]
  exact smallReeX_word_eq_smallReeP h3 _ _ _ _ _ _

theorem finiteReeAut_smallReeCoord
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (t b c : K) :
    ((G2.finiteReeAut K a ⟨smallReeCoord a K t b c, smallReeCoord_mem_adjointGroup t b c⟩ :
        adjointGroup G2.tag K) : ModGL G2.tag K) = smallReeCoord a K t b c := by
  obtain ⟨-, ρ, σ, hρ, hσ, -, hσρ, -, -⟩ := small_Ree_field_power_identities a K hK
  have hs : ∀ x, smallReeSigma a x = σ x := fun x => (hσ x).symm
  have hr : ∀ x : K, x ^ 3 ^ a = ρ x := fun x => (hρ x).symm
  have hρσ : ∀ x, ρ (σ x) = x := fun x => congrArg (fun e : K ≃+* K => e x) hσρ
  have hρ3 : ∀ x, ρ x ^ 3 = σ x := fun x => by rw [hρ, hσ, ← pow_mul, mul_comm]
  refine (finiteReeAut_smallReeP t (smallReeSigma a t) b c
    (smallReeSigma a b - t ^ 3 * smallReeSigma a t)
    (smallReeSigma a c - t ^ 3 * smallReeSigma a t ^ 2)).trans ?_
  rw [smallReeCoord_eq_smallReeP]
  simp only [hs, hr, hρσ, map_sub, map_mul, map_pow, hρ3]
  congr 1 <;> ring

theorem bijOn_smallReeCoord
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × K × K => smallReeCoord a K p.1 p.2.1 p.2.2) Set.univ
      (G2.reeFixedPosUnipotent K a : Set (ModGL G2.tag K)) := by
  obtain ⟨-, ρ, σ, hρ, hσ, hρσ', hσρ, hσσ, -⟩ := small_Ree_field_power_identities a K hK
  have hs : ∀ x, smallReeSigma a x = σ x := fun x => (hσ x).symm
  have hr : ∀ x : K, x ^ 3 ^ a = ρ x := fun x => (hρ x).symm
  have hσρx : ∀ x, σ (ρ x) = x := fun x => congrArg (fun e : K ≃+* K => e x) hρσ'
  refine ⟨fun p _ => ?_, fun p _ p' _ h => ?_, fun g hg => ?_⟩
  · exact Subgroup.mem_inf.2 ⟨smallReeCoord_mem_posUnipotent a K _ _ _,
      mem_reeGamma_of_fixed (smallReeCoord_mem_adjointGroup _ _ _)
        (finiteReeAut_smallReeCoord hK p.1 p.2.1 p.2.2)⟩
  · obtain ⟨h0, -, h2, h3, -, -⟩ := smallReeP_injective h
    exact Prod.ext h0 (Prod.ext h2 h3)
  · obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨v, -, rfl⟩ := (bijOn_smallReeP K).2.2 hgU
    have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ (smallReeP_mem_adjointGroup _ _ _ _ _ _)
    rw [finiteReeAut_smallReeP] at hF
    obtain ⟨e0, e1, e2, e3, -, -⟩ := smallReeP_injective hF
    simp only [hs, hr] at e0 e1 e2 e3
    rw [e0] at e2 e3
    have h4 : σ (v 2) - v 0 ^ 3 * σ (v 0) = v 4 := by
      have h := congrArg σ (show ρ (v 4) = v 2 - σ (v 0) * v 0 by rw [← e2]; ring)
      rw [hσρx, map_sub, map_mul, hσσ] at h
      exact h.symm
    have h5 : σ (v 3) - v 0 ^ 3 * σ (v 0) ^ 2 = v 5 := by
      have h := congrArg σ (show ρ (v 5) = v 3 - σ (v 0) * v 0 ^ 2 by rw [← e3]; ring)
      rw [hσρx, map_sub, map_mul, map_pow, hσσ] at h
      exact h.symm
    refine ⟨(v 0, v 2, v 3), Set.mem_univ _, ?_⟩
    show smallReeCoord a K (v 0) (v 2) (v 3) = smallReeP K (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
    rw [smallReeCoord_eq_smallReeP]
    simp only [hs]
    rw [h4, h5, e1]

end ReeTag

theorem small_Ree_positive_fixed_coordinates
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Set.BijOn (fun p : K × K × K => smallReeCoord a K p.1 p.2.1 p.2.2) Set.univ
        (ReeTag.G2.reeFixedPosUnipotent K a : Set (ModGL ReeTag.G2.tag K)) ∧
      Nat.card (ReeTag.G2.reeFixedPosUnipotent K a) = (3 ^ (2 * a + 1)) ^ 3 := by
  have hbij := ReeTag.bijOn_smallReeCoord (a := a) hK
  refine ⟨hbij, ?_⟩
  have h1 : Nat.card (ReeTag.G2.reeFixedPosUnipotent K a) = Nat.card (K × K × K) := by
    rw [← Nat.card_univ (α := K × K × K)]
    exact (Nat.card_congr (hbij.equiv _)).symm
  rw [h1, Nat.card_prod, Nat.card_prod, hK]
  ring

end CFSG.LieType.Ree
