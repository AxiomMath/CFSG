module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCentralizer

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise commutatorElement

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem zmod_two_eq_jMat : ∀ B : M₃, Bᵀ = B → (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → B i j = 0) →
    B = jMat (B 0 0) (B 0 1) (B 0 2) := by
  intro B hB h
  have h10 : B 1 0 = B 0 1 := congrFun (congrFun hB 0) 1
  have h20 : B 2 0 = B 0 2 := congrFun (congrFun hB 0) 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact h10 | exact h20 | exact h _ _ (by decide) (by decide)

theorem jMat_support (c y y' : ZMod 2) :
    ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → jMat c y y' i j = 0 := by
  intro i j hi hj
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hi | exact absurd rfl hj | rfl

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

include hnd hzC hinf hz in
theorem degree64_completion_common [Finite G] {D₁ D₂ C₁ F₁ F₂ E₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hC₁D : C₁ ≤ D₁) (hC₁n : ∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁)
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    {g : G} (hgC : g ∈ C₁) (hgD₂ : g ∈ D₂)
    (hgz : z⁻¹ * (g⁻¹ * z * g) = ptB₁ he hb φ hzC hz) (hgcen : ∀ c ∈ C₁, g * c = c * g)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he)
    (hF₂n : ∀ n ∈ 𝒩₂, ∀ f ∈ F₂, n * f * n⁻¹ ∈ F₂)
    (hE₂F : E₂ ≤ F₂) (hE₂c : IsMulCommutative E₂) (hE₂card : Nat.card E₂ = 512)
    (hE₂uniq : ∀ E' : Subgroup G, E' ≤ F₂ → IsMulCommutative E' → Nat.card E' = 512 → E' = E₂)
    (hF₂zE : (F₂ : Set G) = (zpowers z : Set G) * (E₂ : Set G)) (hE₂R : E₂ ⊓ ℛ = 𝒜₂)
    (hF₂sq : ∀ f ∈ F₂, f ^ 2 ∈ altSub φ he)
    (hY : ∀ Y : Subgroup G, Y ≤ F₂ → IsMulCommutative Y →
      4 ≤ Subgroup.relIndex 𝒜₂ (Y ⊔ 𝒜₂) → Y ≤ E₂) :
    (∀ k ∈ C₁ ⊓ D₂, ∀ k' ∈ C₁ ⊓ D₂, k * k' = k' * k) ∧
    Nat.card (C₁ ⊓ D₂ : Subgroup G) = 64 ∧ Nat.card (C₁ ⊓ F₂ : Subgroup G) = 32 ∧
    conjClass (C₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) ∧
    ⁅C₁ ⊓ D₂, 𝒜₂⁆ = ⊥ ∧
    C₁ ⊓ F₂ ≤ E₂ ∧ (∀ x ∈ E₂, x ^ 2 = 1) ∧ (∀ m ∈ 𝒩₂, ∀ x ∈ E₂, m * x * m⁻¹ ∈ E₂) ∧
    (∀ m ∈ 𝒩₂, ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), m * c * m⁻¹ ∈ D₂ ⊓ centralizer (E₂ : Set G)) ∧
    Nat.card (D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G) = 4096 ∧
    (D₂ : Set G) = (zpowers z : Set G) * ((D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G) : Set G) ∧
    (D₂ ⊓ centralizer (E₂ : Set G)) ⊓ ℛ = 𝒜₂ ∧
    (∀ c : G, (c ∈ D₂ ⊓ centralizer (E₂ : Set G) ∧ symThreeDiag (ν₂ c : M₃) = 0) ↔ c ∈ E₂) ∧
    E₂ ≤ D₂ ⊓ centralizer (E₂ : Set G) ∧
    (∀ B : ↥(binarySymMatrices 3), ∃ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ν₂ c = B) ∧
    (∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ν₂ c = 0 ↔ c ∈ 𝒜₂) ∧
    (∀ w : Fin 3 → ZMod 2, ∃ c ∈ D₂ ⊓ centralizer (E₂ : Set G), symThreeDiag (ν₂ c : M₃) = w) ∧
    C₁ ⊓ (D₂ ⊓ centralizer (E₂ : Set G)) = C₁ ⊓ D₂ ∧ C₁ ⊓ E₂ = C₁ ⊓ F₂ ∧
    (∀ x ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, ∀ y ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, x * y = y * x) ∧
    Nat.card (𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) = 512 ∧
    ((C₁ ⊓ D₂ : Subgroup G) : Set G) = ((C₁ ⊓ F₂ : Subgroup G) : Set G) * (zpowers g : Set G) ∧
    Nat.card (C₁ ⊓ F₁ : Subgroup G) = 64 ∧
    ((C₁ ⊓ F₁ ⊓ (D₂ ⊓ centralizer (E₂ : Set G)) : Subgroup G) : Set G) =
      ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) * (zpowers g : Set G) ∧
    ∃ ε : ZMod 2,
      (∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ∀ d ∈ D₂ ⊓ centralizer (E₂ : Set G),
        c ^ 2 = tauHom φ he (Multiplicative.ofAdd
          (symThreeSquare ε (symThreeDiag (ν₂ c : M₃)))) ∧
        c⁻¹ * d⁻¹ * c * d = tauHom φ he (Multiplicative.ofAdd
          (symThreeSquarePolar ε (symThreeDiag (ν₂ c : M₃)) (symThreeDiag (ν₂ d : M₃))))) ∧
      (ε = 0 → (∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), c ^ 2 = 1) ∧
        ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), ∀ d ∈ D₂ ⊓ centralizer (E₂ : Set G),
          c * d = d * c) ∧
      (ε = 1 → Monoid.exponent (D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G) = 4 ∧
        closure {x | ∃ c ∈ D₂ ⊓ centralizer (E₂ : Set G), c ^ 2 = x} = 𝒜₂ ∧
        ⁅D₂ ⊓ centralizer (E₂ : Set G), D₂ ⊓ centralizer (E₂ : Set G)⁆ = altSub φ he ∧
        (center (D₂ ⊓ centralizer (E₂ : Set G) : Subgroup G)).map
          (D₂ ⊓ centralizer (E₂ : Set G)).subtype = E₂ ∧
        ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G), c ^ 2 = 1 ↔ c ∈ E₂) ∧
      g ^ 2 = ptB₁ he hb φ hzC hz ^ ε.val := by
  classical
  have hFD : F₂ ≤ D₂ := fun x hx => ((hF₂ x).1 hx).1
  have hE₂D : E₂ ≤ D₂ := hE₂F.trans hFD
  have hAD : 𝒜₂ ≤ D₂ := le_sup_left.trans hRD₂
  have hzN₁ : z ∈ 𝒩₁ := le_normalizer (mem_sup_right (mem_zpowers z))
  have hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ := hC₁n z hzN₁
  have hcomm₂ : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d := by
    intro d hd a ha
    obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    have h := hpure d hd (Multiplicative.toAdd B) 0
    rw [zero_smul, add_zero, radHom_tau, ofAdd_toAdd] at h
    exact comm_of_inv_mul_mul_eq h
  have hAC : 𝒜₁ ≤ C₁ := fun a ha => by
    have h : a ∈ C₁ ⊓ ℬ₁ := by
      rw [hC₁B]
      exact ha
    exact (mem_inf.1 h).1
  have hgK : g ∈ C₁ ⊓ D₂ := mem_inf.2 ⟨hgC, hgD₂⟩
  have hgν : ν₂ g = jSym 1 0 0 := by
    have h := tauHom_nu he φ hzC hz hν₂z hgD₂
    rw [hgz, ptB₁_eq_tauHom] at h
    have h2 := Multiplicative.ofAdd.injective (tauHom_injective φ he h)
    exact Subtype.ext (congrArg Subtype.val h2)
  have hMsq := fun m (hm : m ∈ C₁ ⊓ F₂) =>
    sq_eq_one_of_mem_C₁_inf_F₂ he hb φ hzC hz hC₁sq hF₂sq hm
  have hME := C₁_inf_F₂_le he hb hnd φ hzC hinf hz hν₂z hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B hC₁z hzC₁
    hKz hF₂ hcomm₂ hC₁sq hF₂sq hY
  have hE₂sq := fun x (hx : x ∈ E₂) => sq_eq_one_of_mem_E₂ he hb hnd φ hzC hinf hz hν₂z hpure
    hD₂n hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B hC₁z hzC₁ hKz hF₂ hcomm₂ hC₁sq hF₂sq hE₂F hE₂c hE₂card
    hE₂uniq hE₂R hY hx
  have hcommE : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₂c.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE₂n : ∀ m ∈ 𝒩₂, ∀ x ∈ E₂, m * x * m⁻¹ ∈ E₂ := by
    intro m hm
    have heq := hE₂uniq (E₂.map (MulAut.conj m).toMonoidHom)
      (by rintro _ ⟨x, hx, rfl⟩; exact hF₂n m hm x (hE₂F hx))
      ⟨⟨fun x y => by
        obtain ⟨_, ⟨x', hx', rfl⟩⟩ := x
        obtain ⟨_, ⟨y', hy', rfl⟩⟩ := y
        apply Subtype.ext
        change m * x' * m⁻¹ * (m * y' * m⁻¹) = m * y' * m⁻¹ * (m * x' * m⁻¹)
        calc m * x' * m⁻¹ * (m * y' * m⁻¹) = m * (x' * y') * m⁻¹ := by group
          _ = m * (y' * x') * m⁻¹ := by rw [hcommE x' hx' y' hy']
          _ = m * y' * m⁻¹ * (m * x' * m⁻¹) := by group⟩⟩
      (by rw [card_map_of_injective (MulAut.conj m).injective, hE₂card])
    intro x hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  have hK₀eq := C₁_inf_D₂_eq_mul he hb φ hzC hinf hz hν₂z hpure hD₂H hγD₁ hC₁D hF₂ hgK hgν
  have hMc : ∀ m ∈ C₁ ⊓ F₂, ∀ m' ∈ C₁ ⊓ F₂, m * m' = m' * m := fun m hm m' hm' =>
    comm_of_sq_eq_one hMsq hm hm'
  have hK₀c : ∀ k ∈ C₁ ⊓ D₂, ∀ k' ∈ C₁ ⊓ D₂, k * k' = k' * k := by
    intro k hk k' hk'
    have hk1 : k ∈ ((C₁ ⊓ D₂ : Subgroup G) : Set G) := hk
    have hk2 : k' ∈ ((C₁ ⊓ D₂ : Subgroup G) : Set G) := hk'
    rw [hK₀eq] at hk1 hk2
    obtain ⟨m, hm, t, ht, rfl⟩ := hk1
    obtain ⟨m', hm', t', ht', rfl⟩ := hk2
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ht
    obtain ⟨n', rfl⟩ := mem_zpowers_iff.1 ht'
    have hgm : ∀ x ∈ C₁ ⊓ F₂, Commute (g ^ n) x ∧ Commute (g ^ n') x := fun x hx =>
      ⟨Commute.zpow_left (hgcen x (mem_inf.1 hx).1) n,
        Commute.zpow_left (hgcen x (mem_inf.1 hx).1) n'⟩
    have h1 : Commute m m' := hMc m hm m' hm'
    have h2 : Commute m (g ^ n') := ((hgm m hm).2).symm
    have h3 : Commute (g ^ n) m' := (hgm m' hm').1
    have h4 : Commute (g ^ n) (g ^ n') := Commute.zpow_zpow_self g n n'
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4) : Commute (m * g ^ n) (m' * g ^ n'))
  have hK₀A : ⁅C₁ ⊓ D₂, 𝒜₂⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    exact mem_centralizer_iff.2 fun a ha => (hcomm₂ x (mem_inf.1 hx).2 a ha).symm
  have hKN : C₁ ⊓ D₂ ≤ normalizer (𝒜₂ : Set G) := fun k hk =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
      (hcomm₂ k (mem_inf.1 hk).2 a ha).symm)
  have hPset : ((𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) : Set G) =
      ((C₁ ⊓ D₂ : Subgroup G) : Set G) * (𝒜₂ : Set G) := by
    rw [sup_comm]
    exact coe_mul_of_left_le_normalizer_right _ _ hKN
  have hKJ := C₁_inf_D₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B
  have hKconj := conjClass_C₁_inf_D₂ hb φ hRD₂ hC₁z hzC₁ hKz
    (fun k hk => conj_mem_ptA_inf_radA he hb φ hzC hz hν₂z hγD₁ hC₁D hk)
  have hPD : 𝒜₂ ⊔ C₁ ⊓ D₂ ≤ D₂ := sup_le hAD inf_le_right
  have hPc : ∀ x ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, ∀ y ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ ((𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) : Set G) := hx
    have hy' : y ∈ ((𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) : Set G) := hy
    rw [hPset] at hx' hy'
    obtain ⟨k, hk, a, ha, rfl⟩ := hx'
    obtain ⟨k', hk', a', ha', rfl⟩ := hy'
    have h1 : Commute k k' := hK₀c k hk k' hk'
    have h2 : Commute k a' := hcomm₂ k (mem_inf.1 hk).2 a' ha'
    have h3 : Commute a k' := (hcomm₂ k' (mem_inf.1 hk').2 a ha).symm
    have h4 : Commute a a' := radA_comm he φ ha ha'
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4) : Commute (k * a) (k' * a'))
  have hPc' : IsMulCommutative (𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) :=
    ⟨⟨fun x y => Subtype.ext (hPc x x.2 y y.2)⟩⟩
  have hPR : (𝒜₂ ⊔ C₁ ⊓ D₂) ⊓ ℛ = 𝒜₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxR⟩ := mem_inf.1 hx
      have hx' : x ∈ ((𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) : Set G) := hxP
      rw [hPset] at hx'
      obtain ⟨k, hk, a, ha, rfl⟩ := hx'
      have hkR : k ∈ ℛ := by
        have h := mul_mem hxR (inv_mem (mem_sup_left ha : a ∈ ℛ))
        rwa [mul_inv_cancel_right] at h
      have hkz : k ∈ centralizer ({z} : Set G) := by
        have h : k ∈ D₂ ⊓ centralizer ({z} : Set G) := by
          rw [hD₂H]
          exact hkR
        exact (mem_inf.1 h).2
      have hkJ : k ∈ 𝒜₁ ⊓ 𝒜₂ := by
        rw [← hKJ]
        exact mem_inf.2 ⟨hk, hkz⟩
      exact mul_mem (mem_inf.1 hkJ).2 ha
    · exact le_inf le_sup_left le_sup_left
  have hPJ : ∀ B : ↥(binarySymMatrices 3),
      (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (B : M₃) i j = 0) ↔ ∃ p ∈ 𝒜₂ ⊔ C₁ ⊓ D₂, ν₂ p = B := by
    intro B
    constructor
    · intro hB
      have hBj : B = jSym ((B : M₃) 0 0) ((B : M₃) 0 1) ((B : M₃) 0 2) :=
        Subtype.ext (zmod_two_eq_jMat _ B.2 hB)
      have hjJ : tauHom φ he (Multiplicative.ofAdd B) ∈ 𝒜₁ ⊓ 𝒜₂ := by
        rw [hBj]
        exact (mem_ptA_inf_radA_iff he hb φ).2 ⟨_, _, _, rfl⟩
      have hzj : z * tauHom φ he (Multiplicative.ofAdd B) ∈ conjClass (C₁ ⊓ D₂) z := by
        rw [hKconj]
        exact Set.smul_mem_smul_set hjJ
      obtain ⟨k, hk, hkz⟩ := mem_conjClass_iff_right.1 hzj
      refine ⟨k, mem_sup_right hk, ?_⟩
      have h := tauHom_nu he φ hzC hz hν₂z (mem_inf.1 hk).2
      rw [hkz, inv_mul_cancel_left] at h
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he h)
    · rintro ⟨p, hp, rfl⟩
      have hp' : p ∈ ((𝒜₂ ⊔ C₁ ⊓ D₂ : Subgroup G) : Set G) := hp
      rw [hPset] at hp'
      obtain ⟨k, hk, a, ha, rfl⟩ := hp'
      have haR : a ∈ ℛ := mem_sup_left ha
      have h1 := nu_mul he φ hzC hinf hz hν₂z hpure (mem_inf.1 hk).2 (hRD₂ haR)
      rw [(nu_eq_zero_iff he φ hzC hz hν₂z hD₂H (hRD₂ haR)).2 haR, add_zero] at h1
      obtain ⟨c, y, y', hc⟩ := nu_eq_jSym he hb φ hzC hz hν₂z hγD₁ hC₁D hk
      rw [h1, hc]
      exact jMat_support c y y'
  have hE₂levi : ∀ (g' : GL (Fin 3) (ZMod 2)), ∀ x ∈ E₂,
      leviHom φ he g' * x * (leviHom φ he g')⁻¹ ∈ E₂ := fun g' x hx =>
    hE₂n _ (leviHom_mem_normalizer_radSub φ he hzC hz g') x hx
  have hE₂Fν : ∀ d ∈ D₂, symThreeDiag (ν₂ d : M₃) = 0 ↔
      d ∈ (zpowers z : Set G) * (E₂ : Set G) := by
    intro d hd
    rw [← hF₂zE, SetLike.mem_coe, hF₂ d, ← tauHom_nu he φ hzC hz hν₂z hd]
    constructor
    · intro h
      exact ⟨hd, _, h, rfl⟩
    · rintro ⟨-, B, hB, hBx⟩
      rw [← Multiplicative.ofAdd.injective (tauHom_injective φ he hBx)]
      exact hB
  obtain ⟨hCcard, hPcard, -, hDzC, hCR, hCF, hPC, hνs, hνk, hδs, ε, hεf, hε0, hε1⟩ :=
    degree64_lagrangian_centralizer he φ hzC hinf hz hD₂n hν₂z hν₂surj hpure hRD₂ hD₂H hE₂D hE₂c
      hE₂sq hE₂R hE₂Fν hE₂levi hPD hPc' le_sup_left hPR hPJ
  have hCn : ∀ m ∈ 𝒩₂, ∀ c ∈ D₂ ⊓ centralizer (E₂ : Set G),
      m * c * m⁻¹ ∈ D₂ ⊓ centralizer (E₂ : Set G) := by
    intro m hm c hc
    obtain ⟨hcD, hcE⟩ := mem_inf.1 hc
    refine mem_inf.2 ⟨hD₂n m hm c hcD, mem_centralizer_iff.2 fun x hx => ?_⟩
    have hx' : m⁻¹ * x * m ∈ E₂ := by
      have h := hE₂n m⁻¹ (inv_mem hm) x hx
      rwa [inv_inv] at h
    have h := mem_centralizer_iff.1 hcE _ hx'
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m)) * m⁻¹ := by rw [h]
      _ = m * c * m⁻¹ * x := by group
  have hEC : E₂ ≤ D₂ ⊓ centralizer (E₂ : Set G) := fun x hx =>
    mem_inf.2 ⟨hE₂D hx, mem_centralizer_iff.2 fun y hy => hcommE y hy x hx⟩
  have hKC : C₁ ⊓ D₂ ≤ D₂ ⊓ centralizer (E₂ : Set G) := le_sup_right.trans hPC
  have hC₁C₂ : C₁ ⊓ (D₂ ⊓ centralizer (E₂ : Set G)) = C₁ ⊓ D₂ :=
    le_antisymm (inf_le_inf_left _ inf_le_left) (le_inf inf_le_left hKC)
  have hC₁E₂ : C₁ ⊓ E₂ = C₁ ⊓ F₂ :=
    le_antisymm (inf_le_inf_left _ hE₂F) (le_inf inf_le_left hME)
  have hgsq : g ^ 2 = ptB₁ he hb φ hzC hz ^ ε.val := by
    rw [(hεf g (hKC hgK) g (hKC hgK)).1, hgν]
    have hδ : symThreeDiag ((jSym 1 0 0 : ↥(binarySymMatrices 3)) : M₃) = ![1, 0, 0] :=
      symThreeDiag_jMat 1 0 0
    rw [hδ]
    rcases zmod_two_eq_zero_or_eq_one ε with rfl | rfl
    · rw [symThreeSquare_zero_left, ofAdd_zero, map_one, ZMod.val_zero, pow_zero]
    · have h1 : symThreeSquare 1 ![1, 0, 0] = jSym 1 0 0 := Subtype.ext (by
        rw [coe_symThreeSquare, one_smul]
        decide)
      rw [h1, ZMod.val_one, pow_one, ptB₁_eq_tauHom]
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  have hgF₁ : g ∈ C₁ ⊓ F₁ := mem_inf.2 ⟨hgC, (hF₁ g).2 ⟨hC₁D hgC, by rw [hgz]; exact mem_zpowers _⟩⟩
  have hBF₁ : ℬ₁ ≤ F₁ := fun x hx => by
    have hxD : x ∈ D₁ ⊓ centralizer ({z} : Set G) := by
      rw [hD₁H]
      exact hx
    refine (hF₁ x).2 ⟨(mem_inf.1 hxD).1, ?_⟩
    have h : x⁻¹ * z * x = z := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 (mem_inf.1 hxD).2, inv_mul_cancel_left]
    rw [h, inv_mul_cancel]
    exact one_mem _
  have hE₁card : Nat.card (C₁ ⊓ F₁ : Subgroup G) = 64 := by
    have hconj : conjClass (C₁ ⊓ F₁) z = z • ((zpowers (ptB₁ he hb φ hzC hz) : Subgroup G) :
        Set G) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := mem_conjClass_iff_right.1 hx
        refine ⟨z⁻¹ * (k⁻¹ * z * k), ((hF₁ k).1 (mem_inf.1 hk).2).2, ?_⟩
        change z * (z⁻¹ * (k⁻¹ * z * k)) = k⁻¹ * z * k
        group
      · rintro _ ⟨i, hi, rfl⟩
        rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hi with rfl | rfl
        · change z * 1 ∈ conjClass (C₁ ⊓ F₁) z
          rw [mul_one]
          exact self_mem_conjClass _ z
        · refine mem_conjClass_iff_right.2 ⟨g, hgF₁, ?_⟩
          change g⁻¹ * z * g = z * ptB₁ he hb φ hzC hz
          rw [← hgz]
          group
    have hcent : (C₁ ⊓ F₁) ⊓ centralizer ({z} : Set G) = 𝒜₁ := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxCF, hxz⟩ := mem_inf.1 hx
        obtain ⟨hxC, hxF⟩ := mem_inf.1 hxCF
        have hxB : x ∈ ℬ₁ := by
          rw [← hD₁H]
          exact mem_inf.2 ⟨hC₁D hxC, hxz⟩
        rw [← hC₁B]
        exact mem_inf.2 ⟨hxC, hxB⟩
      · intro a ha
        have haB : a ∈ ℬ₁ := mem_sup_left ha
        have haz : a ∈ centralizer ({z} : Set G) := by
          have h : a ∈ D₁ ⊓ centralizer ({z} : Set G) := by
            rw [hD₁H]
            exact haB
          exact (mem_inf.1 h).2
        exact mem_inf.2 ⟨mem_inf.2 ⟨hAC ha, hBF₁ haB⟩, haz⟩
    rw [card_eq_card_conjClass_mul _ z, hconj, card_smul_set, SetLike.coe_sort_coe,
      Nat.card_zpowers, hb₁ord, hcent, (ptA_facts he hb hnd φ).2.2.1]
  have hE₁C₂ : ((C₁ ⊓ F₁ ⊓ (D₂ ⊓ centralizer (E₂ : Set G)) : Subgroup G) : Set G) =
      ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) * (zpowers g : Set G) := by
    have hJE : 𝒜₁ ⊓ 𝒜₂ ≤ C₁ ⊓ F₁ ⊓ (D₂ ⊓ centralizer (E₂ : Set G)) := fun x hx =>
      mem_inf.2 ⟨mem_inf.2 ⟨hAC (mem_inf.1 hx).1, hBF₁ (mem_sup_left (mem_inf.1 hx).1)⟩,
        hPC (mem_sup_left (mem_inf.1 hx).2)⟩
    have hgE : g ∈ C₁ ⊓ F₁ ⊓ (D₂ ⊓ centralizer (E₂ : Set G)) := mem_inf.2 ⟨hgF₁, hKC hgK⟩
    ext x
    constructor
    · intro hx
      obtain ⟨hxCF, hxC₂⟩ := mem_inf.1 (by exact hx)
      obtain ⟨hxC, hxF⟩ := mem_inf.1 hxCF
      have hxK : x ∈ C₁ ⊓ D₂ := mem_inf.2 ⟨hxC, (mem_inf.1 hxC₂).1⟩
      obtain ⟨c, y, y', hc⟩ := nu_eq_jSym he hb φ hzC hz hν₂z hγD₁ hC₁D hxK
      have hI : tauHom φ he (Multiplicative.ofAdd (jSym c y y')) ∈
          zpowers (ptB₁ he hb φ hzC hz) := by
        rw [← hc, tauHom_nu he φ hzC hz hν₂z (mem_inf.1 hxK).2]
        exact ((hF₁ x).1 hxF).2
      have hyy : y = 0 ∧ y' = 0 := by
        rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hI with h | h
        · rw [← map_one (tauHom φ he), ← ofAdd_zero] at h
          have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
          exact ⟨congrFun (congrFun h1 0) 1, congrFun (congrFun h1 0) 2⟩
        · rw [ptB₁_eq_tauHom] at h
          have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
          exact ⟨congrFun (congrFun h1 0) 1, congrFun (congrFun h1 0) 2⟩
      obtain ⟨rfl, rfl⟩ := hyy
      have hJ : ∀ w ∈ C₁ ⊓ D₂, ν₂ w = 0 → w ∈ 𝒜₁ ⊓ 𝒜₂ := fun w hw hw0 => by
        rw [← hKJ]
        have hwR := (nu_eq_zero_iff he φ hzC hz hν₂z hD₂H (mem_inf.1 hw).2).1 hw0
        have h : w ∈ D₂ ⊓ centralizer ({z} : Set G) := by
          rw [hD₂H]
          exact hwR
        exact mem_inf.2 ⟨hw, (mem_inf.1 h).2⟩
      rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
      · have h0 : ν₂ x = 0 := by
          rw [hc]
          exact Subtype.ext (by decide)
        exact ⟨x, hJ x hxK h0, 1, one_mem _, mul_one x⟩
      · have hxg : x * g⁻¹ ∈ C₁ ⊓ D₂ := mul_mem hxK (inv_mem hgK)
        have h1 := nu_mul he φ hzC hinf hz hν₂z hpure hxg.2 hgD₂
        rw [inv_mul_cancel_right, hc, hgν] at h1
        have h0 : ν₂ (x * g⁻¹) = 0 := add_eq_right.1 h1.symm
        exact ⟨x * g⁻¹, hJ _ hxg h0, g, mem_zpowers g, by group⟩
    · rintro ⟨j, hj, t, ht, rfl⟩
      exact mul_mem (hJE hj) ((zpowers_le.2 hgE) ht)
  refine ⟨hK₀c, card_C₁_inf_D₂ he hb hnd φ hzC hinf hz hν₂z hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B hC₁z
      hzC₁ hKz,
    card_C₁_inf_F₂ he hb hnd φ hzC hinf hz hν₂z hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B hC₁z hzC₁ hKz hF₂,
    hKconj, hK₀A, hME, hE₂sq, hE₂n, hCn, hCcard, hDzC, hCR, hCF, hEC, hνs, hνk, hδs, hC₁C₂,
    hC₁E₂, hPc, hPcard, hK₀eq, hE₁card, hE₁C₂, ε, hεf, hε0, hε1, hgsq⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
