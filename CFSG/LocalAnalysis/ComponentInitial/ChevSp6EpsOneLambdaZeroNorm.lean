module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextKernel
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroUnique

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Generic

variable {X : Type*} [Group X]

theorem map_conj_eq_of_unique_sq [Finite X] {B P I : Subgroup X} (hPB : P ≤ B)
    (hPsq : ∀ p ∈ P, p ^ 2 ∈ I)
    (huniq : ∀ Y : Subgroup X, Y ≤ B → Nat.card Y = Nat.card P → (∀ y ∈ Y, y ^ 2 ∈ I) → Y = P)
    {m : X} (hm : m ∈ normalizer (B : Set X)) (hmI : ∀ i ∈ I, m * i * m⁻¹ ∈ I) :
    P.map (MulAut.conj m).toMonoidHom = P := by
  refine huniq _ ?_ (card_map_of_injective (MulAut.conj m).injective) ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact (mem_normalizer_iff.1 hm q).1 (hPB hq)
  · rintro _ ⟨q, hq, rfl⟩
    have h : (MulAut.conj m).toMonoidHom q ^ 2 = m * q ^ 2 * m⁻¹ := by
      rw [← map_pow]
      rfl
    rw [h]
    exact hmI _ (hPsq q hq)

theorem conj_mem_of_map_conj_eq {P : Subgroup X} {m : X}
    (h : P.map (MulAut.conj m).toMonoidHom = P) {p : X} (hp : p ∈ P) : m * p * m⁻¹ ∈ P := by
  rw [← h]
  exact ⟨p, hp, rfl⟩

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

section Conj

variable (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
  (hσ : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (a : G) (ha : a ∈ L) (B : M₃),
    Bᵀ = B →
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
  (hσcol : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (hn : (n : G) ∈ L) (j : Fin 3),
    linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i))

include he hnd hzC hsup hz hσ hσcol in
theorem epsOne_D₂_conj_mem [Finite G] {D₂ C₂ K₀ P B : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂A : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d)
    (hC₂D : C₂ ≤ D₂) (hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂)
    (hDzC : (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G))
    (hνmul : ∀ c ∈ C₂, ∀ c' ∈ C₂, ν₂ (c * c') = ν₂ c + ν₂ c')
    (hνk : ∀ c ∈ C₂, ν₂ c = 0 ↔ c ∈ 𝒜₂)
    (hC₂comm : ∀ c ∈ C₂, ∀ d ∈ C₂, c⁻¹ * d⁻¹ * c * d ∈ 𝒜₂) (hK₀C₂ : K₀ ≤ C₂)
    (hP : P = 𝒜₂ ⊔ K₀) (hB : B = zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ K₀)
    (hBNP : B ≤ normalizer (P : Set G))
    (hγB : ∀ x ∈ B, z⁻¹ * (x⁻¹ * z * x) ∈ 𝒜₁ ⊓ 𝒜₂)
    (hK₀J : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = j) :
    ∀ d ∈ D₂, ∀ x ∈ B, d * x * d⁻¹ * x⁻¹ ∈ P := by
  classical
  have hzB : z ∈ B := by
    rw [hB]
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers z)))
  have hA₁B : 𝒜₁ ≤ B := by
    rw [hB]
    exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hA₂B : 𝒜₂ ≤ B := by
    rw [hB]
    exact le_sup_right.trans le_sup_left
  have hK₀B : K₀ ≤ B := by
    rw [hB]
    exact le_sup_right
  have hA₂P : 𝒜₂ ≤ P := by
    rw [hP]
    exact le_sup_left
  have hK₀P : K₀ ≤ P := by
    rw [hP]
    exact le_sup_right
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hz1 : z * z = 1 := z_mul_self hz
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz1
  have hν1 : ν₂ 1 = 0 := by
    have h := hνmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact (add_eq_left.1 h.symm)
  have hνP : ∀ c ∈ C₂, (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (ν₂ c : M₃) i j = 0) → c ∈ P := by
    intro c hc hsupp
    have hM := eq_jMat_iff.1 ⟨(ν₂ c).2, hsupp⟩
    have hτJ : tauHom φ he (Multiplicative.ofAdd (ν₂ c)) ∈ 𝒜₁ ⊓ 𝒜₂ := by
      refine (mem_ptA_inf_radA_iff he hb φ).2 ⟨(ν₂ c : M₃) 0 0, (ν₂ c : M₃) 0 1,
        (ν₂ c : M₃) 0 2, ?_⟩
      congr 2
      exact Subtype.ext hM.symm
    obtain ⟨k, hk, hkz⟩ := hK₀J _ hτJ
    have hkν : ν₂ k = ν₂ c := by
      rw [← tauHom_nu he φ hzC hz hν₂z (hC₂D (hK₀C₂ hk))] at hkz
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he hkz)
    have hkinv : ν₂ k⁻¹ = ν₂ k := by
      have h := hνmul k (hK₀C₂ hk) k⁻¹ (inv_mem (hK₀C₂ hk))
      rw [mul_inv_cancel, hν1] at h
      rw [← neg_eq_of_add_eq_zero_right h.symm]
      exact neg_eq_of_add_eq_zero_left (symThree_add_self _)
    have h0 : ν₂ (k⁻¹ * c) = 0 := by
      rw [hνmul _ (inv_mem (hK₀C₂ hk)) c hc, hkinv, hkν, symThree_add_self]
    have hA := (hνk _ (mul_mem (inv_mem (hK₀C₂ hk)) hc)).1 h0
    have h1 : c = k * (k⁻¹ * c) := by group
    rw [h1]
    exact mul_mem (hK₀P hk) (hA₂P hA)
  have hC₂T : ∀ c ∈ C₂, ∀ x ∈ B, c * x * c⁻¹ * x⁻¹ ∈ P := by
    intro c hc
    let T : Subgroup G :=
      { carrier := {x | x ∈ B ∧ c * x * c⁻¹ * x⁻¹ ∈ P}
        one_mem' := ⟨one_mem _, by
          rw [show c * 1 * c⁻¹ * (1 : G)⁻¹ = 1 by group]
          exact one_mem _⟩
        mul_mem' := by
          rintro x y ⟨hx, h⟩ ⟨hy, h'⟩
          refine ⟨mul_mem hx hy, ?_⟩
          have he' : c * (x * y) * c⁻¹ * (x * y)⁻¹ =
              (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
          rw [he']
          exact mul_mem h ((mem_normalizer_iff.1 (hBNP hx) _).1 h')
        inv_mem' := by
          rintro x ⟨hx, h⟩
          refine ⟨inv_mem hx, ?_⟩
          have he' : c * x⁻¹ * c⁻¹ * x⁻¹⁻¹ = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
          rw [he']
          exact (mem_normalizer_iff.1 (hBNP (inv_mem hx)) _).1 (inv_mem h) }
    have hBT : B ≤ T := by
      rw [hB]
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · rw [zpowers_le]
        refine ⟨hzB, ?_⟩
        have hγ : z⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) ∈ 𝒜₂ := by
          rw [← tauHom_nu he φ hzC hz hν₂z (inv_mem (hC₂D hc))]
          exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
        rw [inv_inv] at hγ
        have h1 : c * z * c⁻¹ * z⁻¹ = z * (z⁻¹ * (c * z * c⁻¹)) * z⁻¹ := by group
        have h2 : z * (z⁻¹ * (c * z * c⁻¹)) * z⁻¹ = z⁻¹ * (c * z * c⁻¹) := by
          rw [mul_inv_eq_iff_eq_mul, hzL _ (hA₂L hγ)]
        rw [h1, h2]
        exact hA₂P hγ
      · intro a ha
        refine ⟨hA₁B ha, ?_⟩
        have haN := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz ha
        obtain ⟨y, y', hyy⟩ := mem_lagrangianT0.1
          (sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol ⟨a⁻¹, haN⟩ (inv_mem ha))
        have hdC : a⁻¹ * c * a⁻¹⁻¹ ∈ C₂ := hC₂n _ (mem_inf.1 haN).1 c hc
        have hdν := nu_conj_sigma he φ hzC hz σ hσ hν₂z ⟨a⁻¹, haN⟩ (hC₂D hc) (hC₂D hdC)
        rw [hyy] at hdν
        rw [inv_inv] at hdC hdν
        have hcinv : ν₂ c⁻¹ = ν₂ c := by
          have h := hνmul c hc c⁻¹ (inv_mem hc)
          rw [mul_inv_cancel, hν1] at h
          rw [← neg_eq_of_add_eq_zero_right h.symm]
          exact neg_eq_of_add_eq_zero_left (symThree_add_self _)
        have hdc : a⁻¹ * c * a * c⁻¹ ∈ P := by
          refine hνP _ (mul_mem hdC (inv_mem hc)) fun i j hi hj => ?_
          rw [hνmul _ hdC _ (inv_mem hc), hdν, hcinv]
          change (t0Mat y y' * (ν₂ c : M₃) * (t0Mat y y')ᵀ + (ν₂ c : M₃)) i j = 0
          exact t0_congr_add_eq_zero y y' _ hi hj
        have h1 : c * a * c⁻¹ * a⁻¹ = a * (a⁻¹ * c * a * c⁻¹)⁻¹⁻¹ * a⁻¹ := by group
        rw [h1, inv_inv]
        exact (mem_normalizer_iff.1 (hBNP (hA₁B ha)) _).1 hdc
      · intro x hx
        refine ⟨hA₂B hx, ?_⟩
        rw [show c * x * c⁻¹ * x⁻¹ = 1 by
          rw [hD₂A c (hC₂D hc) x hx]
          group]
        exact one_mem _
      · intro x hx
        refine ⟨hK₀B hx, ?_⟩
        have h := hC₂comm c⁻¹ (inv_mem hc) x⁻¹ (inv_mem (hK₀C₂ hx))
        rw [inv_inv, inv_inv] at h
        exact hA₂P h
    exact fun x hx => (hBT hx).2
  have hzT : ∀ x ∈ B, z * x * z⁻¹ * x⁻¹ ∈ P := by
    intro x hx
    have h := hγB x⁻¹ (inv_mem hx)
    have h1 : z * x * z⁻¹ * x⁻¹ = z⁻¹ * (x⁻¹⁻¹ * z * x⁻¹) := by
      rw [hzinv, inv_inv]
      group
    rw [h1]
    exact hA₂P (mem_inf.1 h).2
  intro d hd x hx
  have hd' : d ∈ (zpowers z : Set G) * (C₂ : Set G) := by
    rw [← hDzC]
    exact hd
  obtain ⟨t, ht, c, hc, rfl⟩ := hd'
  have htB : t ∈ B := (zpowers_le.2 hzB) ht
  have htT : t * x * t⁻¹ * x⁻¹ ∈ P := by
    rcases eq_one_or_eq_of_mem_zpowers hz ht with h | h
    · rw [h, show (1 : G) * x * 1⁻¹ * x⁻¹ = 1 by group]
      exact one_mem _
    · rw [h]
      exact hzT x hx
  have he' : t * c * x * (t * c)⁻¹ * x⁻¹ =
      (t * (c * x * c⁻¹ * x⁻¹) * t⁻¹) * (t * x * t⁻¹ * x⁻¹) := by group
  rw [he']
  exact mul_mem ((mem_normalizer_iff.1 (hBNP htB) _).1 (hC₂T c hc x hx)) htT

end Conj

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
