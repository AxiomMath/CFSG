module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroNorm
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open BinarySymmetricTwoFlag
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

section Block

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
  (hσker : σ.ker = (radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G)))

include he hnd hzC hsup hinf hz hσ hσcol hσker in
theorem epsOne_lambda_zero_block [Finite G] {D₁ C₁ D₂ C₂ F₁ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    (hC₁D : C₁ ≤ D₁) (hC₁n : ∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁c : Nat.card C₁ = 1024)
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hA₁cen : ∀ a ∈ 𝒜₁, ∀ d ∈ D₁, a * d = d * a)
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) (hRD₂ : ℛ ≤ D₂)
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hD₂A : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d)
    (hC₂D : C₂ ≤ D₂) (hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂) (hC₂R : C₂ ⊓ ℛ = 𝒜₂)
    (hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂) (hDzC : (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G))
    (hνmul : ∀ c ∈ C₂, ∀ c' ∈ C₂, ν₂ (c * c') = ν₂ c + ν₂ c')
    (hνk : ∀ c ∈ C₂, ν₂ c = 0 ↔ c ∈ 𝒜₂)
    (hC₂comm : ∀ c ∈ C₂, ∀ d ∈ C₂, c⁻¹ * d⁻¹ * c * d ∈ 𝒜₂)
    (hK₀c : ∀ k ∈ C₁ ⊓ D₂, ∀ k' ∈ C₁ ⊓ D₂, k * k' = k' * k)
    (hK₀card : Nat.card (C₁ ⊓ D₂ : Subgroup G) = 64)
    (hKconj : conjClass (C₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G))
    (hK₀A : ⁅C₁ ⊓ D₂, 𝒜₂⁆ = ⊥)
    (hPc : ∀ x ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, ∀ y ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, x * y = y * x)
    (hPcard : Nat.card (𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) = 512)
    (hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)) :
    let I₁ := zpowers (ptB₁ he hb φ hzC hz)
    let K₀ := C₁ ⊓ D₂
    let P₁ := 𝒜₁ ⊔ K₀
    let P₂ := 𝒜₂ ⊔ K₀
    let A := 𝒜₁ ⊔ 𝒜₂ ⊔ K₀
    let B := zpowers z ⊔ A
    (∀ x ∈ P₁, ∀ y ∈ P₁, x * y = y * x) ∧ Nat.card P₁ = 2 ^ 8 ∧
    (∀ x ∈ P₂, ∀ y ∈ P₂, x * y = y * x) ∧ Nat.card P₂ = 2 ^ 9 ∧
    Nat.card A = 2 ^ 11 ∧ Nat.card B = 2 ^ 12 ∧
    D₂ ≤ normalizer (B : Set G) ∧ D₂ ≤ normalizer (P₁ : Set G) ∧
    D₂ ≤ normalizer (P₂ : Set G) ∧ D₂ ≤ normalizer (A : Set G) ∧
    D₂ ≤ centralizer ({ptB₁ he hb φ hzC hz} : Set G) ∧
    I₁ ≤ P₁ ∧ I₁ ≤ P₂ ∧ P₁ ≤ B ∧ P₂ ≤ B ∧ P₁ ⊔ P₂ = A ∧ B ≤ normalizer (P₂ : Set G) ∧
    (∀ x ∈ P₁, x ^ 2 ∈ I₁) ∧ (∀ x ∈ P₂, x ^ 2 ∈ I₁) ∧ (∀ x ∈ I₁, ∀ y ∈ B, x * y = y * x) ∧
    (∀ Y : Subgroup G, Y ≤ B → Nat.card Y = 2 ^ 9 → (∀ y ∈ Y, y ^ 2 ∈ I₁) → Y = P₂) ∧
    (∀ Y : Subgroup G, Y ≤ B → Nat.card Y = 2 ^ 8 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
      Nat.card (Y ⊔ P₂ : Subgroup G) = 2 ^ 11 → Y = P₁) := by
  classical
  intro I₁ K₀ P₁ P₂ A B
  set B₀ := zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ K₀ with hB₀def
  have hBB₀ : B = B₀ := by
    simp only [B, A, B₀, sup_assoc]
  have hzR : z ∈ ℛ := mem_sup_right (mem_zpowers z)
  have hzD₂ : z ∈ D₂ := hRD₂ hzR
  have hzB₁ : z ∈ ℬ₁ := mem_sup_right (mem_zpowers z)
  have hzN₁ : z ∈ 𝒩₁ := le_normalizer hzB₁
  have hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ := hC₁n z hzN₁
  have hAC₁ : 𝒜₁ ≤ C₁ := ptA_le_of_inf_eq hb φ hC₁B
  have hAL : 𝒜₁ ≤ L := pullSub_le φ _
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₂D : 𝒜₂ ≤ D₂ := le_sup_left.trans hRD₂
  have hK₀C₁ : K₀ ≤ C₁ := inf_le_left
  have hK₀D₂ : K₀ ≤ D₂ := inf_le_right
  have hK₀C₂ : K₀ ≤ C₂ := by
    intro k hk
    have h : k ∈ C₁ ⊓ C₂ := by
      rw [hC₁C₂]
      exact hk
    exact (mem_inf.1 h).2
  have hIJ : I₁ ≤ 𝒜₁ ⊓ 𝒜₂ := zpowers_ptB₁_le he hb φ hzC hz
  have hJK₀ : 𝒜₁ ⊓ 𝒜₂ ≤ K₀ := le_inf (inf_le_left.trans hAC₁) (inf_le_right.trans hA₂D)
  have hA₁c : ∀ x ∈ 𝒜₁, ∀ y ∈ 𝒜₁, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian (ptA_facts he hb hnd φ).2.1 hx hy
  have hA₁e : IsElementaryAbelian 2 𝒜₁ := (ptA_facts he hb hnd φ).2.1
  have hsqA : ∀ a ∈ 𝒜₁, a ^ 2 = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := 𝒜₁) a ha
  have hK₀A' : ∀ k ∈ K₀, ∀ a ∈ 𝒜₂, k * a = a * k := by
    rw [commutator_eq_bot_iff_le_centralizer] at hK₀A
    intro k hk a ha
    exact (mem_centralizer_iff.1 (hK₀A hk) a ha).symm
  have hA₁K₀ : ∀ a ∈ 𝒜₁, ∀ k ∈ K₀, a * k = k * a := fun a ha k hk =>
    hA₁cen a ha k (hC₁D (hK₀C₁ hk))
  obtain ⟨hBcard, -, hBV₁, -, -, hPB, hIP, -, hA₁V₁, -, hγB, hBNP⟩ :=
    degree64_next_block he hb hnd φ hzC hinf hz (D₁ := D₁) (C₁ := C₁) (D₂ := D₂) (C₂ := C₂)
      (K₀ := K₀) (P := P₂) (B := B₀) (V₁ := D₁ ⊔ 𝒜₂) hD₁N hD₁n hD₁H hγD₁ hb₁c hC₁D hC₁n hC₁z
      hC₁B hC₁c hC₁sq hD₂n hRD₂ hD₂H hν₂z hKz hC₂R hC₁C₂ rfl rfl rfl rfl hPcard
  have hA₁B : ∀ a ∈ 𝒜₁, ∀ x ∈ B₀, a⁻¹ * x⁻¹ * a * x ∈ 𝒜₁ ⊓ 𝒜₂ := fun a ha x hx =>
    hA₁V₁ a ha x (hBV₁ hx)
  have hK₀J : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = j := by
    intro j hj
    have hzj : z * j ∈ conjClass K₀ z := by
      rw [hKconj]
      exact Set.smul_mem_smul_set hj
    obtain ⟨k, hk, hkz⟩ := mem_conjClass_iff_right.1 hzj
    exact ⟨k, hk, by rw [hkz]; group⟩
  have hk₁ : ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0)) :=
    hK₀J _ ((mem_ptA_inf_radA_iff he hb φ).2 ⟨0, 1, 0, rfl⟩)
  have hA₂NK : 𝒜₂ ≤ normalizer (K₀ : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk => hK₀A' k hk a ha)
  have hA₁NK : 𝒜₁ ≤ normalizer (K₀ : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk => (hA₁K₀ a ha k hk).symm)
  have hP₂sq : ∀ p ∈ P₂, p ^ 2 ∈ I₁ := by
    intro p hp
    have hp' : p ∈ ((𝒜₂ ⊔ K₀ : Subgroup G) : Set G) := hp
    rw [coe_mul_of_left_le_normalizer_right _ _ hA₂NK] at hp'
    obtain ⟨a, ha, k, hk, rfl⟩ := hp'
    have ha2 : a ^ 2 = 1 := sq_eq_one_of_mem_radA he φ ha
    have h : (a * k) ^ 2 = k ^ 2 := by
      calc (a * k) ^ 2 = a * (k * a) * k := by rw [sq]; group
        _ = a * (a * k) * k := by rw [hK₀A' k hk a ha]
        _ = a ^ 2 * k ^ 2 := by rw [sq, sq]; group
        _ = k ^ 2 := by rw [ha2, one_mul]
    rw [h]
    exact hC₁sq k (hK₀C₁ hk)
  obtain ⟨hJB, -⟩ := epsOne_block_comm he hb hnd φ hzC hz hK₀A' hPc rfl rfl hγB hA₁B
  obtain ⟨κ, hadd, hker, hsq, hPκ, hP₁κ⟩ := epsOne_flag_package he hb hnd φ hzC hsup hinf hz σ hσ
    hσcol hσker (D₁ := D₁) (C₁ := C₁) (D₂ := D₂) (K₀ := K₀) (P := P₂) (P₁ := P₁) (B := B₀)
    (F₁ := F₁) hC₁D hC₁B hC₁sq hA₂D rfl rfl rfl rfl hF₁ hγB hA₁B hBNP hK₀A' hPc hP₂sq hk₁
  have hQ₀ : Nat.card (K₀ ⊓ F₁ : Subgroup G) = 16 :=
    card_Q₀ he hb hnd φ hzC hinf hz hD₂H hRD₂ hD₁H hC₁D hC₁B hC₁z hzC₁ hKz hF₁
  have huniq₂ : ∀ Y : Subgroup G, Y ≤ B₀ → Nat.card Y = 512 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
      Y = P₂ := fun Y hYB hYc hYsq => eq_of_flagCoord κ hadd hker hQ₀ hsq hPB hPcard
    (fun p hp => (hPκ p (hPB hp)).2 hp) hYB hYc hYsq
  have hA₁K₀J : 𝒜₁ ⊓ K₀ = 𝒜₁ ⊓ 𝒜₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxK⟩ := mem_inf.1 hx
      have hxz : x ∈ centralizer ({z} : Set G) :=
        mem_centralizer_singleton_iff.2 (hzL x (hAL hxA))
      have h : x ∈ (C₁ ⊓ D₂) ⊓ centralizer ({z} : Set G) := mem_inf.2 ⟨hxK, hxz⟩
      rw [C₁_inf_D₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B] at h
      exact h
    · exact le_inf inf_le_left hJK₀
  have hP₁card : Nat.card P₁ = 256 := by
    have h := natCard_sup_mul_inf hA₁NK
    rw [hA₁K₀J, card_ptA_inf_radA he hb φ, (ptA_facts he hb hnd φ).2.2.1, hK₀card] at h
    change Nat.card (𝒜₁ ⊔ K₀ : Subgroup G) = 256
    omega
  have hP₁C₁ : P₁ ≤ C₁ := sup_le hAC₁ hK₀C₁
  have hP₁sq : ∀ x ∈ P₁, x ^ 2 ∈ I₁ := fun x hx => hC₁sq x (hP₁C₁ hx)
  have hP₁B₀ : P₁ ≤ B₀ := sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
    le_sup_right
  have hP₁c : ∀ x ∈ P₁, ∀ y ∈ P₁, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ ((𝒜₁ ⊔ K₀ : Subgroup G) : Set G) := hx
    have hy' : y ∈ ((𝒜₁ ⊔ K₀ : Subgroup G) : Set G) := hy
    rw [coe_mul_of_left_le_normalizer_right _ _ hA₁NK] at hx' hy'
    obtain ⟨a, ha, k, hk, rfl⟩ := hx'
    obtain ⟨a', ha', k', hk', rfl⟩ := hy'
    calc a * k * (a' * k') = a * (k * a') * k' := by group
      _ = a * (a' * k) * k' := by rw [← hA₁K₀ a' ha' k hk]
      _ = (a * a') * (k * k') := by group
      _ = (a' * a) * (k' * k) := by rw [hA₁c a ha a' ha', hK₀c k hk k' hk']
      _ = a' * (a * k') * k := by group
      _ = a' * (k' * a) * k := by rw [hA₁K₀ a ha k' hk']
      _ = a' * k' * (a * k) := by group
  have hP₁P₂ : P₁ ⊓ P₂ = K₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
      have hx1' : x ∈ ((𝒜₁ ⊔ K₀ : Subgroup G) : Set G) := hx1
      rw [coe_mul_of_left_le_normalizer_right _ _ hA₁NK] at hx1'
      obtain ⟨a, ha, k, hk, rfl⟩ := hx1'
      have hK₀P₂ : K₀ ≤ P₂ := le_sup_right
      have haP : a ∈ P₂ := by
        have h := mul_mem hx2 (inv_mem (hK₀P₂ hk))
        rwa [mul_inv_cancel_right] at h
      have haP' : a ∈ ((𝒜₂ ⊔ K₀ : Subgroup G) : Set G) := haP
      rw [coe_mul_of_left_le_normalizer_right _ _ hA₂NK] at haP'
      obtain ⟨a₂, ha₂, k', hk', hak⟩ := haP'
      have hk'eq : k' = a₂⁻¹ * a := by
        rw [← hak]
        group
      have hk'L : k' ∈ L := by
        rw [hk'eq]
        exact mul_mem (inv_mem (hA₂L ha₂)) (hAL ha)
      have hk'A : k' ∈ 𝒜₂ := by
        have hk'z : k' ∈ centralizer ({z} : Set G) :=
          mem_centralizer_singleton_iff.2 (hzL k' hk'L)
        have hk'R : k' ∈ ℛ := by
          rw [← hD₂H]
          exact mem_inf.2 ⟨hK₀D₂ hk', hk'z⟩
        exact mem_radA_of_mem_radSub φ hzC hinf hk'R hk'L
      have haA₂ : a ∈ 𝒜₂ := by
        rw [← hak]
        exact mul_mem ha₂ hk'A
      exact mul_mem (hJK₀ (mem_inf.2 ⟨ha, haA₂⟩)) hk
    · exact le_inf le_sup_right le_sup_right
  have hAeq : P₁ ⊔ P₂ = A := by
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_right)
  have hAcard : Nat.card A = 2048 := by
    have h := natCard_sup_mul_inf (hP₁B₀.trans hBNP)
    rw [hP₁P₂, hAeq, hP₁card, hPcard, hK₀card] at h
    omega
  have huniq₁ : ∀ Y : Subgroup G, Y ≤ B₀ → Nat.card Y = 256 → (∀ y ∈ Y, y ^ 2 ∈ I₁) →
      Nat.card (Y ⊔ P₂ : Subgroup G) = 2048 → Y = P₁ := fun Y hYB hYc hYsq hYP =>
    eq_P₁_of_flagCoord κ hadd hker hQ₀ hsq hPB (fun p hp => (hPκ p (hPB hp)).2 hp) hBNP hP₁κ
      hP₁card hYB hYc hYsq hYP
  have hD₂T := epsOne_D₂_conj_mem he hb hnd φ hzC hsup hz σ hσ hσcol (D₂ := D₂) (C₂ := C₂)
    (K₀ := K₀) (P := P₂) (B := B₀) hν₂z hD₂A hC₂D hC₂n hDzC hνmul hνk hC₂comm hK₀C₂ rfl rfl
    hBNP hγB hK₀J
  have hD₂NB : D₂ ≤ normalizer (B₀ : Set G) := fun d hd =>
    mem_normalizer_of_conj_mem fun x hx => by
      have h1 : d * x * d⁻¹ = (d * x * d⁻¹ * x⁻¹) * x := by group
      rw [h1]
      exact mul_mem (hPB (hD₂T d hd x hx)) hx
  have hb₁A : ptB₁ he hb φ hzC hz ∈ 𝒜₂ := (hIJ (mem_zpowers _)).2
  have hD₂b₁ : D₂ ≤ centralizer ({ptB₁ he hb φ hzC hz} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hD₂A d hd _ hb₁A)
  have hD₂I : ∀ d ∈ D₂, ∀ i ∈ I₁, d * i * d⁻¹ ∈ I₁ := by
    intro d hd i hi
    rw [hD₂A d hd i (hIJ hi).2, mul_inv_cancel_right]
    exact hi
  have hP₂map : ∀ d ∈ D₂, P₂.map (MulAut.conj d).toMonoidHom = P₂ := fun d hd =>
    map_conj_eq_of_unique_sq hPB hP₂sq (fun Y hYB hYc hYsq => huniq₂ Y hYB (hYc.trans hPcard) hYsq)
      (hD₂NB hd) (hD₂I d hd)
  have hP₁map : ∀ d ∈ D₂, P₁.map (MulAut.conj d).toMonoidHom = P₁ := by
    intro d hd
    refine huniq₁ _ ?_ (by rw [card_map_of_injective (MulAut.conj d).injective, hP₁card]) ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (mem_normalizer_iff.1 (hD₂NB hd) q).1 (hP₁B₀ hq)
    · rintro _ ⟨q, hq, rfl⟩
      have h : (MulAut.conj d).toMonoidHom q ^ 2 = d * q ^ 2 * d⁻¹ := by
        rw [← map_pow]
        rfl
      rw [h]
      exact hD₂I d hd _ (hP₁sq q hq)
    · have h1 : P₁.map (MulAut.conj d).toMonoidHom ⊔ P₂ =
          (P₁ ⊔ P₂).map (MulAut.conj d).toMonoidHom := by
        rw [show (P₁ ⊔ P₂).map (MulAut.conj d).toMonoidHom = P₁.map (MulAut.conj d).toMonoidHom ⊔
          P₂.map (MulAut.conj d).toMonoidHom from Subgroup.map_sup P₁ P₂ _, hP₂map d hd]
      rw [h1, card_map_of_injective (MulAut.conj d).injective, hAeq, hAcard]
  have hAmap : ∀ d ∈ D₂, A.map (MulAut.conj d).toMonoidHom = A := fun d hd => by
    rw [← hAeq, show (P₁ ⊔ P₂).map (MulAut.conj d).toMonoidHom =
      P₁.map (MulAut.conj d).toMonoidHom ⊔ P₂.map (MulAut.conj d).toMonoidHom from
        Subgroup.map_sup P₁ P₂ _, hP₁map d hd, hP₂map d hd]
  have hnorm : ∀ {Q : Subgroup G}, (∀ d ∈ D₂, Q.map (MulAut.conj d).toMonoidHom = Q) →
      D₂ ≤ normalizer (Q : Set G) := fun hQ d hd =>
    mem_normalizer_of_conj_mem fun x hx => conj_mem_of_map_conj_eq (hQ d hd) hx
  rw [hBB₀]
  refine ⟨hP₁c, by rw [hP₁card]; norm_num, hPc, by rw [hPcard]; norm_num,
    by rw [hAcard]; norm_num, by rw [hBcard]; norm_num, hD₂NB, hnorm hP₁map, hnorm hP₂map,
    hnorm hAmap, hD₂b₁, hIJ.trans (inf_le_left.trans le_sup_left), hIP, hP₁B₀, hPB, hAeq, hBNP,
    hP₁sq, hP₂sq, fun x hx y hy => hJB x (hIJ hx) y hy,
    fun Y hYB hYc hYsq => huniq₂ Y hYB (by rw [hYc]; norm_num) hYsq,
    fun Y hYB hYc hYsq hYP => huniq₁ Y hYB (by rw [hYc]; norm_num) hYsq
      (by rw [hYP]; norm_num)⟩

end Block

theorem symThreeCongr_t0Unit_symE₂₂ :
    symThreeCongr (t0Unit 1 0) symE₂₂ + symE₂₂ = jSym 1 1 0 := by
  apply Subtype.ext
  change t0Mat 1 0 * !![0, 0, 0; 0, 1, 0; 0, 0, 0] * (t0Mat 1 0)ᵀ +
    !![(0 : ZMod 2), 0, 0; 0, 1, 0; 0, 0, 0] = jMat 1 1 0
  decide

theorem symThreeSquare_one_jSym : symThreeSquare 1 (symThreeDiag (jSym 1 1 0 : M₃)) = symE₁₁ := by
  apply Subtype.ext
  change (1 : ZMod 2) • vecMulVec (symThreeDiag (jMat 1 1 0)) (symThreeDiag (jMat 1 1 0)) =
    jMat 1 0 0
  rw [symThreeDiag_jMat, one_smul]
  decide

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

include he hnd hzC hsup hinf hz hσ hσcol in
theorem epsOne_lambda_zero_kill [Finite G] {D₁ C₁ D₂ C₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁)
    (hA₁cen : ∀ a ∈ 𝒜₁, ∀ d ∈ D₁, a * d = d * a)
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂) (hνs : ∀ B : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = B)
    (hKconj : conjClass (C₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G))
    (hK₀A : ⁅C₁ ⊓ D₂, 𝒜₂⁆ = ⊥)
    (hD₂P₁ : D₂ ≤ normalizer ((𝒜₁ ⊔ C₁ ⊓ D₂ : Subgroup G) : Set G))
    (hε : ∀ c ∈ C₂, ∀ B : ↥(binarySymMatrices 3),
      z⁻¹ * (c⁻¹ * z * c) = tauHom φ he (Multiplicative.ofAdd B) →
        c ^ 2 = tauHom φ he (Multiplicative.ofAdd (symThreeSquare 1 (symThreeDiag (B : M₃))))) :
    (∀ a ∈ 𝒜₂, ∀ x ∈ 𝒜₁ ⊔ C₁ ⊓ D₂, x * (z * a) = z * a * x → x ^ 2 = 1) ∧
      ∃ a ∈ 𝒜₂, ∃ p ∈ 𝒜₁ ⊔ C₁ ⊓ D₂, p * (z * a) = z * a * p ∧
        p ^ 2 = ptB₁ he hb φ hzC hz := by
  classical
  set K₀ := C₁ ⊓ D₂ with hK₀def
  set P₁ := 𝒜₁ ⊔ K₀ with hP₁def
  have hAC₁ : 𝒜₁ ≤ C₁ := ptA_le_of_inf_eq hb φ hC₁B
  have hAL : 𝒜₁ ≤ L := pullSub_le φ _
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₂D : 𝒜₂ ≤ D₂ := le_sup_left.trans hRD₂
  have hK₀C₁ : K₀ ≤ C₁ := inf_le_left
  have hK₀C₂ : K₀ ≤ C₂ := by
    intro k hk
    have h : k ∈ C₁ ⊓ C₂ := by
      rw [hC₁C₂]
      exact hk
    exact (mem_inf.1 h).2
  have hJK₀ : 𝒜₁ ⊓ 𝒜₂ ≤ K₀ := le_inf (inf_le_left.trans hAC₁) (inf_le_right.trans hA₂D)
  have hA₁e : IsElementaryAbelian 2 𝒜₁ := (ptA_facts he hb hnd φ).2.1
  have hsqA : ∀ a ∈ 𝒜₁, a ^ 2 = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := 𝒜₁) a ha
  have hA₁c : ∀ x ∈ 𝒜₁, ∀ y ∈ 𝒜₁, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian hA₁e hx hy
  have hK₀A' : ∀ k ∈ K₀, ∀ a ∈ 𝒜₂, k * a = a * k := by
    rw [commutator_eq_bot_iff_le_centralizer] at hK₀A
    intro k hk a ha
    exact (mem_centralizer_iff.1 (hK₀A hk) a ha).symm
  have hA₁K₀ : ∀ a ∈ 𝒜₁, ∀ k ∈ K₀, a * k = k * a := fun a ha k hk =>
    hA₁cen a ha k (hC₁D (hK₀C₁ hk))
  have hA₁NK : 𝒜₁ ≤ normalizer (K₀ : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk => (hA₁K₀ a ha k hk).symm)
  have hCz : ∀ x ∈ P₁, x * z = z * x → x ∈ 𝒜₁ := by
    intro x hx hxz
    have hx' : x ∈ ((𝒜₁ ⊔ K₀ : Subgroup G) : Set G) := hx
    rw [coe_mul_of_left_le_normalizer_right _ _ hA₁NK] at hx'
    obtain ⟨a, ha, k, hk, rfl⟩ := hx'
    have hkz : k * z = z * k := by
      have h1 : a * (k * z) = a * (z * k) := by
        calc a * (k * z) = (a * k) * z := (mul_assoc _ _ _).symm
          _ = z * (a * k) := hxz
          _ = (z * a) * k := (mul_assoc _ _ _).symm
          _ = (a * z) * k := by rw [hzL a (hAL ha)]
          _ = a * (z * k) := mul_assoc _ _ _
      exact mul_left_cancel h1
    have h : k ∈ (C₁ ⊓ D₂) ⊓ centralizer ({z} : Set G) :=
      mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 hkz⟩
    rw [C₁_inf_D₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B] at h
    exact mul_mem ha (mem_inf.1 h).1
  have hexp : ∀ a ∈ 𝒜₂, ∀ x ∈ P₁, x * (z * a) = z * a * x → x ^ 2 = 1 := by
    intro a ha x hx hxa
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    obtain ⟨c, hc, hcB⟩ := hνs (Multiplicative.toAdd B)
    have hcz : c⁻¹ * z * c = z * tauHom φ he B := by
      rw [hν₂z c hc, radHom_one_eq φ he hzC hz, hcB, ofAdd_toAdd]
    have hyP : c * x * c⁻¹ ∈ P₁ := (mem_normalizer_iff.1 (hD₂P₁ hc) x).1 hx
    have hyz : c * x * c⁻¹ * z = z * (c * x * c⁻¹) := by
      have h1 : c * x * c⁻¹ * z = c * (x * (c⁻¹ * z * c)) * c⁻¹ := by group
      have h2 : z * (c * x * c⁻¹) = c * ((c⁻¹ * z * c) * x) * c⁻¹ := by group
      rw [h1, h2, hcz, hxa]
    have hyA := hCz _ hyP hyz
    have h1 : x ^ 2 = c⁻¹ * (c * x * c⁻¹) ^ 2 * c := by
      rw [sq, sq]
      group
    rw [h1, hsqA _ hyA]
    group
  have hK₀J : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = j := by
    intro j hj
    have hzj : z * j ∈ conjClass K₀ z := by
      rw [hKconj]
      exact Set.smul_mem_smul_set hj
    obtain ⟨k, hk, hkz⟩ := mem_conjClass_iff_right.1 hzj
    exact ⟨k, hk, by rw [hkz]; group⟩
  have hf : e (Sum.inr 1) ∈ pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) :=
    inr_mem_pairOrth he (by decide)
  set h : G := ((φ.symm (pointElt hb (mem_pairOrth_left hf) 0) : L) : G) with hhdef
  have hhA : h ∈ 𝒜₁ := mem_pullSub.2 ⟨(φ.symm _).2, by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact pointElt_mem_pointRadical hb hf 0⟩
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsqA h hhA)
  have hhN : h⁻¹ ∈ (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G) :=
    ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz hhA
  have hσh : σ ⟨h⁻¹, hhN⟩ = t0Unit 1 0 := by
    rw [sigma_eq_t0Unit he hb φ σ hσcol ⟨h⁻¹, hhN⟩ hf 0 hhinv]
    simp [Basis.repr_self]
  set q : G := tauHom φ he (Multiplicative.ofAdd symE₂₂) with hqdef
  have hqA : q ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  set j : G := tauHom φ he (Multiplicative.ofAdd (jSym 1 1 0)) with hjdef
  have hjJ : j ∈ 𝒜₁ ⊓ 𝒜₂ := (mem_ptA_inf_radA_iff he hb φ).2 ⟨1, 1, 0, rfl⟩
  have hhq : h⁻¹ * q⁻¹ * h * q = j := by
    have h1 : h⁻¹ * q⁻¹ * h * q = (h⁻¹ * q * h)⁻¹ * q := by group
    rw [h1, conj_tauHom_inv he φ σ hσ hhN, tauHom_inv_mul, hσh, symThreeCongr_t0Unit_symE₂₂]
  obtain ⟨k, hk, hkz⟩ := hK₀J j hjJ
  have hqinv : q⁻¹ = q := inv_eq_of_mem_radA he φ hqA
  have hzh : z * h = h * z := (hzL h (hAL hhA)).symm
  have hqk : q * k = k * q := (hK₀A' k hk q hqA).symm
  have hjk : j * k = k * j := (hK₀A' k hk j hjJ.2).symm
  have hjj : j * j = 1 := by rw [← sq]; exact sq_eq_one_of_mem_radA he φ hjJ.2
  have e2 : q * h = h * j * q := by
    have e1 : q⁻¹ * h * q = h * j := by
      rw [← hhq]
      group
    rw [hqinv] at e1
    calc q * h = (q * h * q) * q⁻¹ := by group
      _ = (h * j) * q⁻¹ := by rw [e1]
      _ = h * j * q := by rw [hqinv]
  have e3 : z * k = k * z * j := by
    calc z * k = k * (z * (z⁻¹ * (k⁻¹ * z * k))) := by group
      _ = k * z * j := by rw [hkz]; group
  have hpP : h * k ∈ P₁ := mul_mem (mem_sup_left hhA) (mem_sup_right hk)
  have hcomm : h * k * (z * q) = z * q * (h * k) := by
    symm
    calc z * q * (h * k) = z * (q * h) * k := by group
      _ = z * (h * j * q) * k := by rw [e2]
      _ = (z * h) * j * (q * k) := by group
      _ = (h * z) * j * (k * q) := by rw [hzh, hqk]
      _ = h * z * (j * k) * q := by group
      _ = h * z * (k * j) * q := by rw [hjk]
      _ = h * (z * k) * j * q := by group
      _ = h * (k * z * j) * j * q := by rw [e3]
      _ = h * k * z * (j * j) * q := by group
      _ = h * k * (z * q) := by rw [hjj]; group
  have hk2 : k ^ 2 = ptB₁ he hb φ hzC hz := by
    rw [hε k (hK₀C₂ hk) (jSym 1 1 0) hkz, symThreeSquare_one_jSym, ptB₁_eq_tauHom]
  have hp2 : (h * k) ^ 2 = ptB₁ he hb φ hzC hz := by
    have hkh : k * h = h * k := (hA₁K₀ h hhA k hk).symm
    calc (h * k) ^ 2 = h * (k * h) * k := by rw [sq]; group
      _ = h * (h * k) * k := by rw [hkh]
      _ = h ^ 2 * k ^ 2 := by rw [sq, sq]; group
      _ = ptB₁ he hb φ hzC hz := by rw [hsqA h hhA, one_mul, hk2]
  exact ⟨hexp, q, hqA, h * k, hpP, hcomm, hp2⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
