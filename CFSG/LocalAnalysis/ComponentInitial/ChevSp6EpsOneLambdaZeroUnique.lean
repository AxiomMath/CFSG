module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextUnique
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroFlag

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open BinarySymmetricTwoFlag
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

section Generic

variable {X : Type*} [Group X]

theorem exists_flagImage [Finite X] {B Q₀ Y : Subgroup X} (κ : X → FlagW)
    (hadd : ∀ x ∈ B, ∀ y ∈ B, κ (x * y) = κ x + κ y)
    (hker : ∀ x ∈ B, κ x = 0 ↔ x ∈ Q₀) (hYB : Y ≤ B) :
    ∃ W : Submodule (ZMod 2) FlagW, (∀ v, v ∈ W ↔ ∃ y ∈ Y, κ y = v) ∧
      Nat.card Y ≤ Nat.card Q₀ * 2 ^ finrank (ZMod 2) W := by
  classical
  have hκ1 : κ 1 = 0 := by
    have h := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact (add_eq_left.1 h.symm)
  let W : Submodule (ZMod 2) FlagW :=
    { carrier := {v | ∃ y ∈ Y, κ y = v}
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, mul_mem hx hy, hadd x (hYB hx) y (hYB hy)⟩
      zero_mem' := ⟨1, one_mem _, hκ1⟩
      smul_mem' := by
        rintro c _ ⟨y, hy, rfl⟩
        rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
        · exact ⟨1, one_mem _, by rw [hκ1, zero_smul]⟩
        · exact ⟨y, hy, by rw [one_smul]⟩ }
  refine ⟨W, fun v => Iff.rfl, ?_⟩
  let f : Y →* Multiplicative W :=
    { toFun := fun y => Multiplicative.ofAdd ⟨κ y, y, y.2, rfl⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext hκ1
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext (hadd x (hYB x.2) y (hYB y.2)) }
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨y, hy, hyw⟩ := (Multiplicative.toAdd w).2
    exact ⟨⟨y, hy⟩, Multiplicative.toAdd.injective (Subtype.ext hyw)⟩
  have hmemker : ∀ y : Y, y ∈ f.ker → (y : X) ∈ Q₀ := fun y h => by
    rw [← hker y (hYB y.2)]
    have h1 := congrArg (fun w : Multiplicative W => ((Multiplicative.toAdd w : W) : FlagW)) h
    exact h1
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hcard
  have hW : Nat.card (Multiplicative W) = 2 ^ finrank (ZMod 2) W := by
    rw [show Nat.card (Multiplicative W) = Nat.card W from rfl,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hkerle : Nat.card f.ker ≤ Nat.card Q₀ := by
    refine Nat.card_le_card_of_injective (fun y => ⟨((y : Y) : X), hmemker y y.2⟩) ?_
    intro y y' h
    have h' : ((y : Y) : X) = ((y' : Y) : X) := congrArg (fun q : Q₀ => (q : X)) h
    exact Subtype.ext (Subtype.ext h')
  rw [hcard, hW, mul_comm]
  exact Nat.mul_le_mul_right _ hkerle

theorem eq_P₁_of_flagCoord [Finite X] {B P P₁ Q₀ Y I : Subgroup X} (κ : X → FlagW)
    (hadd : ∀ x ∈ B, ∀ y ∈ B, κ (x * y) = κ x + κ y)
    (hker : ∀ x ∈ B, κ x = 0 ↔ x ∈ Q₀) (hQ : Nat.card Q₀ = 16)
    (hsq : ∀ y ∈ B, y ^ 2 ∈ I → flagQuad (κ y) = 0)
    (hPB : P ≤ B) (hPκ : ∀ p ∈ P, (κ p).2 = 0) (hBNP : B ≤ normalizer (P : Set X))
    (hP₁κ : ∀ x ∈ B, κ x ∈ flagP1Sub → x ∈ P₁) (hP₁card : Nat.card P₁ = 256)
    (hYB : Y ≤ B) (hYcard : Nat.card Y = 256) (hYsq : ∀ y ∈ Y, y ^ 2 ∈ I)
    (hYP : Nat.card (Y ⊔ P : Subgroup X) = 2048) : Y = P₁ := by
  obtain ⟨W, hW, hYW⟩ := exists_flagImage κ hadd hker hYB
  have hYPB : Y ⊔ P ≤ B := sup_le hYB hPB
  obtain ⟨W', hW', hYW'⟩ := exists_flagImage κ hadd hker hYPB
  have hW'le : W' ≤ W ⊔ flagUSub := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (hW' v).1 hv
    have hx' : x ∈ ((Y ⊔ P : Subgroup X) : Set X) := hx
    rw [coe_mul_of_left_le_normalizer_right Y P (hYB.trans hBNP)] at hx'
    obtain ⟨y, hy, p, hp, rfl⟩ := hx'
    rw [hadd y (hYB hy) p (hPB hp)]
    exact Submodule.add_mem_sup ((hW _).2 ⟨y, hy, rfl⟩) (mem_flagUSub.2 (hPκ p hp))
  rw [hQ] at hYW hYW'
  have h4 : 4 ≤ finrank (ZMod 2) W := by
    by_contra hlt
    have h1 : 2 ^ finrank (ZMod 2) W ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := hYW.trans (Nat.mul_le_mul_left 16 h1)
    rw [hYcard] at h2
    norm_num at h2
  have h7 : 7 ≤ finrank (ZMod 2) ↥(W ⊔ flagUSub) := by
    have hmono := Submodule.finrank_mono hW'le
    by_contra hlt
    have h1 : 2 ^ finrank (ZMod 2) W' ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := hYW'.trans (Nat.mul_le_mul_left 16 h1)
    rw [hYP] at h2
    norm_num at h2
  have hWq : ∀ v ∈ W, flagQuad v = 0 := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := (hW v).1 hv
    exact hsq y (hYB hy) (hYsq y hy)
  have hle := le_flagP1Sub_of_singular W hWq h4 h7
  have hYP₁ : Y ≤ P₁ := fun y hy => hP₁κ y (hYB hy) (hle ((hW _).2 ⟨y, hy, rfl⟩))
  exact Subgroup.eq_of_le_of_card_ge hYP₁ (by rw [hYcard, hP₁card])

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

include he hnd hzC hz in
theorem epsOne_block_comm {K₀ P B : Subgroup G}
    (hK₀A : ∀ k ∈ K₀, ∀ a ∈ 𝒜₂, k * a = a * k) (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hP : P = 𝒜₂ ⊔ K₀) (hB : B = zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ K₀)
    (hγB : ∀ x ∈ B, z⁻¹ * (x⁻¹ * z * x) ∈ 𝒜₁ ⊓ 𝒜₂)
    (hA₁B : ∀ a ∈ 𝒜₁, ∀ x ∈ B, a⁻¹ * x⁻¹ * a * x ∈ 𝒜₁ ⊓ 𝒜₂) :
    (∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∀ x ∈ B, j * x = x * j) ∧
      ∀ x ∈ B, ∀ y ∈ B, x⁻¹ * y⁻¹ * x * y ∈ 𝒜₁ ⊓ 𝒜₂ := by
  classical
  have hzB : z ∈ B := by
    rw [hB]
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers z)))
  have hA₁B' : 𝒜₁ ≤ B := by
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
  have hPB : P ≤ B := by
    rw [hP]
    exact sup_le hA₂B hK₀B
  have hAL : 𝒜₁ ≤ L := pullSub_le φ _
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₁c : ∀ x ∈ 𝒜₁, ∀ y ∈ 𝒜₁, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian (ptA_facts he hb hnd φ).2.1 hx hy
  have hJB : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∀ x ∈ B, j * x = x * j := by
    have hle : B ≤ centralizer ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) := by
      rw [hB]
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · rw [zpowers_le]
        exact mem_centralizer_iff.2 fun j hj => hzL j (hAL (mem_inf.1 hj).1)
      · exact fun a ha => mem_centralizer_iff.2 fun j hj => hA₁c j (mem_inf.1 hj).1 a ha
      · exact fun a ha => mem_centralizer_iff.2 fun j hj => radA_comm he φ (mem_inf.1 hj).2 ha
      · exact fun k hk => mem_centralizer_iff.2 fun j hj => (hK₀A k hk j (mem_inf.1 hj).2).symm
    exact fun j hj x hx => mem_centralizer_iff.1 (hle hx) j hj
  have hPc' : ∀ p ∈ P, ∀ q ∈ P, p⁻¹ * q⁻¹ * p * q = 1 := fun p hp q hq => by
    rw [mul_assoc, hPc p hp q hq]
    group
  have hsymm : ∀ s t : G, s⁻¹ * t⁻¹ * s * t ∈ 𝒜₁ ⊓ 𝒜₂ → t⁻¹ * s⁻¹ * t * s ∈ 𝒜₁ ⊓ 𝒜₂ :=
    fun s t h => by
      have h1 := inv_mem h
      rwa [show (s⁻¹ * t⁻¹ * s * t)⁻¹ = t⁻¹ * s⁻¹ * t * s by group] at h1
  have hzpow : ∀ s ∈ zpowers z, ∀ x ∈ B, s⁻¹ * x⁻¹ * s * x ∈ 𝒜₁ ⊓ 𝒜₂ := fun s hs x hx => by
    rcases eq_one_or_eq_of_mem_zpowers hz hs with h | h
    · rw [h, show (1 : G)⁻¹ * x⁻¹ * 1 * x = 1 by group]
      exact one_mem _
    · rw [h, show z⁻¹ * x⁻¹ * z * x = z⁻¹ * (x⁻¹ * z * x) by group]
      exact hγB x hx
  have hSB : ((zpowers z : Subgroup G) : Set G) ∪ (𝒜₁ : Set G) ∪ (𝒜₂ : Set G) ∪ (K₀ : Set G) ⊆
      B := by
    rintro x (((hx | hx) | hx) | hx)
    · exact (zpowers_le.2 hzB) hx
    · exact hA₁B' hx
    · exact hA₂B hx
    · exact hK₀B hx
  have hBS : B ≤ closure (((zpowers z : Subgroup G) : Set G) ∪ (𝒜₁ : Set G) ∪ (𝒜₂ : Set G) ∪
      (K₀ : Set G)) := by
    rw [hB]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> intro x hx <;> apply Subgroup.subset_closure
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inl (Or.inl (Or.inr hx))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hBB : ∀ x ∈ B, ∀ y ∈ B, x⁻¹ * y⁻¹ * x * y ∈ 𝒜₁ ⊓ 𝒜₂ := by
    refine comm_mem_of_gen hBS hSB hJB ?_
    intro s hs t ht
    have htB := hSB ht
    rcases hs with ((hs | hs) | hs) | hs
    · exact hzpow s hs t htB
    · exact hA₁B s hs t htB
    all_goals
      have hsP : s ∈ P := by
        first
        | exact hA₂P hs
        | exact hK₀P hs
      rcases ht with ((ht | ht) | ht) | ht
      · exact hsymm t s (hzpow t ht s (hPB hsP))
      · exact hsymm t s (hA₁B t ht s (hPB hsP))
      · rw [hPc' s hsP t (hA₂P ht)]
        exact one_mem _
      · rw [hPc' s hsP t (hK₀P ht)]
        exact one_mem _
  exact ⟨hJB, hBB⟩

section Main

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
theorem epsOne_flag_package [Finite G] {D₁ C₁ D₂ K₀ P P₁ B F₁ : Subgroup G}
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁)
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz)) (hA₂D : 𝒜₂ ≤ D₂)
    (hK₀ : K₀ = C₁ ⊓ D₂) (hP : P = 𝒜₂ ⊔ K₀) (hP₁ : P₁ = 𝒜₁ ⊔ K₀)
    (hB : B = zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ K₀)
    (hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hγB : ∀ x ∈ B, z⁻¹ * (x⁻¹ * z * x) ∈ 𝒜₁ ⊓ 𝒜₂)
    (hA₁B : ∀ a ∈ 𝒜₁, ∀ x ∈ B, a⁻¹ * x⁻¹ * a * x ∈ 𝒜₁ ⊓ 𝒜₂)
    (hBNP : B ≤ normalizer (P : Set G))
    (hK₀A : ∀ k ∈ K₀, ∀ a ∈ 𝒜₂, k * a = a * k) (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hPsq : ∀ p ∈ P, p ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hk₁ : ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0))) :
    ∃ κ : G → FlagW,
      (∀ x ∈ B, ∀ y ∈ B, κ (x * y) = κ x + κ y) ∧ (∀ x ∈ B, κ x = 0 ↔ x ∈ K₀ ⊓ F₁) ∧
      (∀ y ∈ B, y ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) → flagQuad (κ y) = 0) ∧
      (∀ x ∈ B, (κ x).2 = 0 ↔ x ∈ P) ∧ (∀ x ∈ B, κ x ∈ flagP1Sub → x ∈ P₁) := by
  classical
  have hzB : z ∈ B := by
    rw [hB]
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers z)))
  have hA₁B' : 𝒜₁ ≤ B := by
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
  have hPB : P ≤ B := by
    rw [hP]
    exact sup_le hA₂B hK₀B
  have hK₀C₁ : K₀ ≤ C₁ := by
    rw [hK₀]
    exact inf_le_left
  have hAC₁ : 𝒜₁ ≤ C₁ := ptA_le_of_inf_eq hb φ hC₁B
  have hAL : 𝒜₁ ≤ L := pullSub_le φ _
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₁c : ∀ x ∈ 𝒜₁, ∀ y ∈ 𝒜₁, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian (ptA_facts he hb hnd φ).2.1 hx hy
  have hIJ : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ ⊓ 𝒜₂ := zpowers_ptB₁_le he hb φ hzC hz
  have hJK₀ : 𝒜₁ ⊓ 𝒜₂ ≤ K₀ := by
    rw [hK₀]
    exact le_inf (inf_le_left.trans hAC₁) (inf_le_right.trans hA₂D)
  obtain ⟨hJB, hBB⟩ := epsOne_block_comm he hb hnd φ hzC hz hK₀A hPc hP hB hγB hA₁B
  have hPc' : ∀ p ∈ P, ∀ q ∈ P, p⁻¹ * q⁻¹ * p * q = 1 := fun p hp q hq => by
    rw [mul_assoc, hPc p hp q hq]
    group
  have hf : ∀ j : Fin 3, j ≠ 0 → e (Sum.inr j) ∈ 𝔼 := fun j hj => by
    rw [mem_pairOrth, bilin_inl he, bilin_inr he]
    simp [Basis.repr_self, hj]
  have hptA : ∀ (j : Fin 3) (hj : j ≠ 0),
      ((φ.symm (pointElt hb (mem_pairOrth_left (hf j hj)) 0) : L) : G) ∈ 𝒜₁ := fun j hj =>
    mem_pullSub.2 ⟨(φ.symm _).2, by
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      exact pointElt_mem_pointRadical hb (hf j hj) 0⟩
  have hA₁e : IsElementaryAbelian 2 𝒜₁ := (ptA_facts he hb hnd φ).2.1
  have hinvA : ∀ a ∈ 𝒜₁, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := 𝒜₁) a ha)
  have hsqA : ∀ a ∈ 𝒜₁, a ^ 2 = 1 := fun a ha =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := 𝒜₁) a ha
  set a₁ : G := ((φ.symm (pointElt hb (mem_pairOrth_left (hf 1 (by decide))) 0) : L) : G)
    with ha₁def
  set a₂ : G := ((φ.symm (pointElt hb (mem_pairOrth_left (hf 2 (by decide))) 0) : L) : G)
    with ha₂def
  have ha₁A : a₁ ∈ 𝒜₁ := hptA 1 (by decide)
  have ha₂A : a₂ ∈ 𝒜₁ := hptA 2 (by decide)
  have ha₁N : a₁⁻¹ ∈ 𝒩₂₀ := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz ha₁A
  have ha₂N : a₂⁻¹ ∈ 𝒩₂₀ := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz ha₂A
  have hσa₁ : σ ⟨a₁⁻¹, ha₁N⟩ = t0Unit 1 0 := by
    rw [sigma_eq_t0Unit he hb φ σ hσcol ⟨a₁⁻¹, ha₁N⟩ (hf 1 (by decide)) 0
      (hinvA a₁ ha₁A)]
    simp [Basis.repr_self]
  have hσa₂ : σ ⟨a₂⁻¹, ha₂N⟩ = t0Unit 0 1 := by
    rw [sigma_eq_t0Unit he hb φ σ hσcol ⟨a₂⁻¹, ha₂N⟩ (hf 2 (by decide)) 0
      (hinvA a₂ ha₂A)]
    simp [Basis.repr_self]
  have ha₁N' : a₁ ∈ 𝒩₂₀ := by
    have h := inv_mem ha₁N
    rwa [inv_inv] at h
  have ha₂N' : a₂ ∈ 𝒩₂₀ := by
    have h := inv_mem ha₂N
    rwa [inv_inv] at h
  have hσa₁' : σ ⟨a₁, ha₁N'⟩ = t0Unit 1 0 := by
    have h : (⟨a₁, ha₁N'⟩ : 𝒩₂₀) = ⟨a₁⁻¹, ha₁N⟩ := Subtype.ext (hinvA a₁ ha₁A).symm
    rw [h, hσa₁]
  have hσa₂' : σ ⟨a₂, ha₂N'⟩ = t0Unit 0 1 := by
    have h : (⟨a₂, ha₂N'⟩ : 𝒩₂₀) = ⟨a₂⁻¹, ha₂N⟩ := Subtype.ext (hinvA a₂ ha₂A).symm
    rw [h, hσa₂]
  set q₁ := tauHom φ he (Multiplicative.ofAdd symE₂₂) with hq₁def
  set q₂ := tauHom φ he (Multiplicative.ofAdd symE₃₃) with hq₂def
  have hq₁A : q₁ ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hq₂A : q₂ ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  obtain ⟨k₁, hk₁K, hk₁z⟩ := hk₁
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hza₁ : Commute a₁ z := hzL a₁ (hAL ha₁A)
  have hza₂ : Commute a₂ z := hzL a₂ (hAL ha₂A)
  have ha₁a₂ : Commute a₁ a₂ := hA₁c a₁ ha₁A a₂ ha₂A
  have hcs : ∀ g : G, Commute g z → Commute g a₁ → Commute g a₂ → ∀ t y y' : ZMod 2,
      Commute g (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val) := fun g h1 h2 h3 t y y' =>
    ((h1.pow_right _).mul_right (h2.pow_right _)).mul_right (h3.pow_right _)
  have hsB : ∀ t y y' : ZMod 2, z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val ∈ B := fun t y y' =>
    mul_mem (mul_mem (pow_mem hzB _) (pow_mem (hA₁B' ha₁A) _)) (pow_mem (hA₁B' ha₂A) _)
  have hs_mul : ∀ t y y' t₀ y₀ y₀' : ZMod 2,
      z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (z ^ t₀.val * a₁ ^ y₀.val * a₂ ^ y₀'.val) =
        z ^ (t + t₀).val * a₁ ^ (y + y₀).val * a₂ ^ (y' + y₀').val := by
    intro t y y' t₀ y₀ y₀'
    have hc1 : Commute (a₁ ^ y.val * a₂ ^ y'.val) (z ^ t₀.val) :=
      ((hza₁.pow_pow _ _).mul_left (hza₂.pow_pow _ _))
    have hc2 : Commute (a₂ ^ y'.val) (a₁ ^ y₀.val) := ha₁a₂.symm.pow_pow _ _
    rw [pow_val_add_of_sq hz2, pow_val_add_of_sq (hsqA a₁ ha₁A),
      pow_val_add_of_sq (hsqA a₂ ha₂A)]
    calc z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (z ^ t₀.val * a₁ ^ y₀.val * a₂ ^ y₀'.val) =
        z ^ t.val * ((a₁ ^ y.val * a₂ ^ y'.val) * z ^ t₀.val) * a₁ ^ y₀.val * a₂ ^ y₀'.val := by
          simp only [mul_assoc]
      _ = z ^ t.val * (z ^ t₀.val * (a₁ ^ y.val * a₂ ^ y'.val)) * a₁ ^ y₀.val *
          a₂ ^ y₀'.val := by rw [hc1.eq]
      _ = z ^ t.val * z ^ t₀.val * a₁ ^ y.val * (a₂ ^ y'.val * a₁ ^ y₀.val) * a₂ ^ y₀'.val := by
          simp only [mul_assoc]
      _ = z ^ t.val * z ^ t₀.val * a₁ ^ y.val * (a₁ ^ y₀.val * a₂ ^ y'.val) * a₂ ^ y₀'.val := by
          rw [hc2.eq]
      _ = _ := by simp only [mul_assoc]
  have hs_inv : ∀ t y y' : ZMod 2,
      (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val)⁻¹ = z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val := by
    intro t y y'
    refine inv_eq_of_mul_eq_one_right ?_
    rw [hs_mul, zmod_two_add_self_eq_zero, zmod_two_add_self_eq_zero, zmod_two_add_self_eq_zero,
      ZMod.val_zero, pow_zero, pow_zero, pow_zero, mul_one, mul_one]
  let T : Subgroup G :=
    { carrier := {x | ∃ t y y' : ZMod 2, ∃ p ∈ P, x = z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * p}
      one_mem' := ⟨0, 0, 0, 1, one_mem _, by
        rw [ZMod.val_zero, pow_zero, pow_zero, pow_zero, mul_one, mul_one, mul_one]⟩
      mul_mem' := by
        rintro _ _ ⟨t, y, y', p, hp, rfl⟩ ⟨t₀, y₀, y₀', p', hp', rfl⟩
        have hconj : (z ^ t₀.val * a₁ ^ y₀.val * a₂ ^ y₀'.val)⁻¹ * p *
            (z ^ t₀.val * a₁ ^ y₀.val * a₂ ^ y₀'.val) ∈ P := by
          have h := (mem_normalizer_iff.1 (hBNP (inv_mem (hsB t₀ y₀ y₀'))) p).1 hp
          rwa [inv_inv] at h
        refine ⟨t + t₀, y + y₀, y' + y₀', _, mul_mem hconj hp', ?_⟩
        rw [← hs_mul]
        group
      inv_mem' := by
        rintro _ ⟨t, y, y', p, hp, rfl⟩
        have hconj : (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val)⁻¹ * p⁻¹ *
            (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val) ∈ P := by
          have h := (mem_normalizer_iff.1 (hBNP (inv_mem (hsB t y y'))) p⁻¹).1 (inv_mem hp)
          rwa [inv_inv] at h
        refine ⟨t, y, y', _, hconj, ?_⟩
        calc (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * p)⁻¹ =
            p⁻¹ * (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val)⁻¹ := mul_inv_rev _ _
          _ = p⁻¹ * (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val) := by rw [hs_inv]
          _ = z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val *
              ((z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val)⁻¹ * p⁻¹ *
                (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val)) := by group }
  have hBT : B ≤ T := by
    rw [hB]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · rw [zpowers_le]
      exact ⟨1, 0, 0, 1, one_mem _, by
        rw [ZMod.val_one, ZMod.val_zero, pow_one, pow_zero, pow_zero, mul_one, mul_one, mul_one]⟩
    · intro a ha
      have haN : a ∈ 𝒩₂₀ := by
        have h := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz (inv_mem ha)
        rwa [inv_inv] at h
      obtain ⟨y, y', hyy⟩ := mem_lagrangianT0.1
        (sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol ⟨a, haN⟩ ha)
      set n : 𝒩₂₀ := ⟨a, haN⟩ * ((⟨a₁, ha₁N'⟩ : 𝒩₂₀) ^ y.val * (⟨a₂, ha₂N'⟩ : 𝒩₂₀) ^ y'.val)
        with hn
      have hσn : σ n = 1 := by
        rw [hn, map_mul, map_mul, map_pow, map_pow, hyy, hσa₁', hσa₂']
        apply Units.ext
        rcases zmod_two_eq_zero_or_eq_one y with rfl | rfl <;>
          rcases zmod_two_eq_zero_or_eq_one y' with rfl | rfl <;>
          simp only [Units.val_mul, Units.val_one, coe_t0Unit, ZMod.val_zero, ZMod.val_one,
            pow_zero, pow_one, mul_one] <;>
          decide
      have hnR : (n : G) ∈ ℛ := by
        have h : n ∈ σ.ker := hσn
        rw [hσker, mem_subgroupOf] at h
        exact h
      have hnval : (n : G) = a * (a₁ ^ y.val * a₂ ^ y'.val) := by
        rw [hn]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      have hr : a₁ ^ y.val * a₂ ^ y'.val ∈ 𝒜₁ := mul_mem (pow_mem ha₁A _) (pow_mem ha₂A _)
      have hnA₁ : (n : G) ∈ 𝒜₁ := by
        rw [hnval]
        exact mul_mem ha hr
      have hnA₂ : (n : G) ∈ 𝒜₂ := mem_radA_of_mem_radSub φ hzC hinf hnR (hAL hnA₁)
      refine ⟨0, y, y', (n : G), hA₂P hnA₂, ?_⟩
      have h1 : a = (n : G) * (a₁ ^ y.val * a₂ ^ y'.val)⁻¹ := by
        rw [hnval]
        group
      rw [hinvA _ hr, hA₁c _ hnA₁ _ hr] at h1
      rw [ZMod.val_zero, pow_zero, one_mul]
      exact h1
    · intro x hx
      exact ⟨0, 0, 0, x, hA₂P hx, by
        rw [ZMod.val_zero, pow_zero, pow_zero, pow_zero, one_mul, one_mul, one_mul]⟩
    · intro x hx
      exact ⟨0, 0, 0, x, hK₀P hx, by
        rw [ZMod.val_zero, pow_zero, pow_zero, pow_zero, one_mul, one_mul, one_mul]⟩
  have hA₂NK : 𝒜₂ ≤ normalizer (K₀ : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk => hK₀A k hk a ha)
  have hdec : ∀ x ∈ B, ∃ t y y' : ZMod 2, ∃ M : ↥(binarySymMatrices 3), ∃ k ∈ K₀,
      x = z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (tauHom φ he (Multiplicative.ofAdd M) * k) := by
    intro x hx
    obtain ⟨t, y, y', p, hp, rfl⟩ := hBT hx
    have hp' : p ∈ ((𝒜₂ ⊔ K₀ : Subgroup G) : Set G) := by
      rw [← hP]
      exact hp
    rw [coe_mul_of_left_le_normalizer_right _ _ hA₂NK] at hp'
    obtain ⟨a, ha, k, hk, rfl⟩ := hp'
    obtain ⟨M, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    exact ⟨t, y, y', Multiplicative.toAdd M, k, hk, by rw [ofAdd_toAdd]⟩
  have hβa₁ : ∀ M : ↥(binarySymMatrices 3),
      commLab he φ a₁ (tauHom φ he (Multiplicative.ofAdd M)) = ![(M : M₃) 1 1, (M : M₃) 1 2] :=
    fun M => by
      unfold commLab
      rw [labJ_comm_tauHom he φ σ hσ ha₁N hσa₁ M]
      simp
  have hβa₂ : ∀ M : ↥(binarySymMatrices 3),
      commLab he φ a₂ (tauHom φ he (Multiplicative.ofAdd M)) = ![(M : M₃) 2 1, (M : M₃) 2 2] :=
    fun M => by
      unfold commLab
      rw [labJ_comm_tauHom he φ σ hσ ha₂N hσa₂ M]
      simp
  have hβzL : ∀ x ∈ L, commLab he φ z x = 0 := fun x hx =>
    commLab_of_comm he φ (hzL x hx).symm
  have hβak : ∀ a ∈ 𝒜₁, ∀ k ∈ K₀, commLab he φ a k = 0 := fun a ha k hk =>
    labJ_of_mem_zpowers he hb φ hzC hz (comm_mem_of_sq_mem hC₁sq (hAC₁ ha) (hK₀C₁ hk))
  have hβzk : ∀ k : G, commLab he φ z k = labJ he φ (z⁻¹ * (k⁻¹ * z * k)) := fun k => by
    unfold commLab
    rw [show z⁻¹ * k⁻¹ * z * k = z⁻¹ * (k⁻¹ * z * k) by group]
  have hβPP : ∀ p ∈ P, ∀ q ∈ P, commLab he φ p q = 0 := fun p hp q hq => by
    unfold commLab
    rw [hPc' p hp q hq, labJ_one]
  have hβas : ∀ a ∈ 𝒜₁, ∀ t y y' : ZMod 2,
      commLab he φ a (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val) = 0 := fun a ha t y y' =>
    commLab_of_comm he φ (hcs a (hzL a (hAL ha)) (hA₁c a ha a₁ ha₁A) (hA₁c a ha a₂ ha₂A) t y y')
  have hβzs : ∀ t y y' : ZMod 2, commLab he φ z (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val) = 0 :=
    fun t y y' => commLab_of_comm he φ (hcs z (Commute.refl z) hza₁.symm hza₂.symm t y y')
  have hβsl : ∀ (t y y' : ZMod 2) (h : G), h ∈ B →
      commLab he φ (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val) h =
        t • commLab he φ z h + y • commLab he φ a₁ h + y' • commLab he φ a₂ h := by
    intro t y y' h hh
    rw [commLab_mul_left he hb φ hBB hJB (mul_mem (pow_mem hzB _) (pow_mem (hA₁B' ha₁A) _))
      (pow_mem (hA₁B' ha₂A) _) hh, commLab_mul_left he hb φ hBB hJB (pow_mem hzB _)
      (pow_mem (hA₁B' ha₁A) _) hh, commLab_pow_left, commLab_pow_left, commLab_pow_left]
  have hγk₁ : labJ he φ (z⁻¹ * (k₁⁻¹ * z * k₁)) = ![1, 0] := by
    rw [hk₁z, labJ_tau]
    funext i
    fin_cases i <;> rfl
  have hκ : ∀ (t y y' : ZMod 2) (M : ↥(binarySymMatrices 3)) (k : G), k ∈ K₀ →
      flagCoord he φ z a₁ a₂ q₁ q₂ k₁
        (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (tauHom φ he (Multiplicative.ofAdd M) * k)) =
      ((![(M : M₃) 1 1, (M : M₃) 1 2, (M : M₃) 2 2], labJ he φ (z⁻¹ * (k⁻¹ * z * k))),
        (![y, y'], t)) := by
    intro t y y' M k hk
    have hτA : tauHom φ he (Multiplicative.ofAdd M) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have hτB : tauHom φ he (Multiplicative.ofAdd M) ∈ B := hA₂B hτA
    have hkB : k ∈ B := hK₀B hk
    have hpP : tauHom φ he (Multiplicative.ofAdd M) * k ∈ P := mul_mem (hA₂P hτA) (hK₀P hk)
    have hpB : tauHom φ he (Multiplicative.ofAdd M) * k ∈ B := hPB hpP
    have h1 : ∀ a ∈ 𝒜₁, commLab he φ a
        (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (tauHom φ he (Multiplicative.ofAdd M) * k)) =
          commLab he φ a (tauHom φ he (Multiplicative.ofAdd M)) := fun a ha => by
      rw [commLab_mul_right he hb φ hBB hJB (hA₁B' ha) (hsB t y y') hpB,
        commLab_mul_right he hb φ hBB hJB (hA₁B' ha) hτB hkB, hβas a ha, hβak a ha k hk,
        zero_add, add_zero]
    have h2 : commLab he φ z
        (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (tauHom φ he (Multiplicative.ofAdd M) * k)) =
          labJ he φ (z⁻¹ * (k⁻¹ * z * k)) := by
      rw [commLab_mul_right he hb φ hBB hJB hzB (hsB t y y') hpB,
        commLab_mul_right he hb φ hBB hJB hzB hτB hkB, hβzs, hβzL _ (hA₂L hτA), hβzk,
        zero_add, zero_add]
    have h3 : ∀ q ∈ P, commLab he φ
        (z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val * (tauHom φ he (Multiplicative.ofAdd M) * k)) q =
          t • commLab he φ z q + y • commLab he φ a₁ q + y' • commLab he φ a₂ q := fun q hq => by
      rw [commLab_mul_left he hb φ hBB hJB (hsB t y y') hpB (hPB hq), hβPP _ hpP q hq, add_zero,
        hβsl t y y' q (hPB hq)]
    have hq₁v : commLab he φ a₁ q₁ = ![1, 0] := by
      rw [hq₁def, hβa₁]
      funext i
      fin_cases i <;> rfl
    have hq₁w : commLab he φ a₂ q₁ = 0 := by
      rw [hq₁def, hβa₂]
      funext i
      fin_cases i <;> rfl
    have hq₂v : commLab he φ a₁ q₂ = 0 := by
      rw [hq₂def, hβa₁]
      funext i
      fin_cases i <;> rfl
    have hq₂w : commLab he φ a₂ q₂ = ![0, 1] := by
      rw [hq₂def, hβa₂]
      funext i
      fin_cases i <;> rfl
    unfold flagCoord
    rw [h1 a₁ ha₁A, h1 a₂ ha₂A, h2, h3 q₁ (hA₂P hq₁A), h3 q₂ (hA₂P hq₂A),
      h3 k₁ (hK₀P hk₁K), hβa₁, hβa₂, hβzL q₁ (hA₂L hq₁A), hβzL q₂ (hA₂L hq₂A), hq₁v, hq₁w,
      hq₂v, hq₂w, hβzk k₁, hγk₁, hβak a₁ ha₁A k₁ hk₁K, hβak a₂ ha₂A k₁ hk₁K]
    refine Prod.ext (Prod.ext ?_ rfl) (Prod.ext ?_ ?_)
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp
    · simp
  have hadd : ∀ x ∈ B, ∀ y ∈ B, flagCoord he φ z a₁ a₂ q₁ q₂ k₁ (x * y) =
      flagCoord he φ z a₁ a₂ q₁ q₂ k₁ x + flagCoord he φ z a₁ a₂ q₁ q₂ k₁ y := by
    intro x hx y hy
    unfold flagCoord
    rw [commLab_mul_right he hb φ hBB hJB (hA₁B' ha₁A) hx hy,
      commLab_mul_right he hb φ hBB hJB (hA₁B' ha₂A) hx hy,
      commLab_mul_right he hb φ hBB hJB hzB hx hy,
      commLab_mul_left he hb φ hBB hJB hx hy (hPB (hA₂P hq₁A)),
      commLab_mul_left he hb φ hBB hJB hx hy (hPB (hA₂P hq₂A)),
      commLab_mul_left he hb φ hBB hJB hx hy (hPB (hK₀P hk₁K))]
    refine Prod.ext (Prod.ext ?_ rfl) (Prod.ext ?_ rfl)
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  have hτJ : ∀ M : ↥(binarySymMatrices 3), (M : M₃) 1 1 = 0 → (M : M₃) 1 2 = 0 →
      (M : M₃) 2 2 = 0 → tauHom φ he (Multiplicative.ofAdd M) ∈ 𝒜₁ ⊓ 𝒜₂ := by
    intro M e1 e2 e3
    have hsym : (M : M₃) 2 1 = (M : M₃) 1 2 := congrFun (congrFun M.2 1) 2
    have hMJ : (M : M₃) = jMat ((M : M₃) 0 0) ((M : M₃) 0 1) ((M : M₃) 0 2) := by
      refine eq_jMat_iff.1 ⟨M.2, fun i j hi hj => ?_⟩
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hi
        | exact absurd rfl hj
        | exact e1
        | exact e2
        | exact e3
        | exact hsym.trans e2
    refine (mem_ptA_inf_radA_iff he hb φ).2 ⟨(M : M₃) 0 0, (M : M₃) 0 1, (M : M₃) 0 2, ?_⟩
    congr 2
    exact Subtype.ext hMJ.symm
  have hQ₀B : K₀ ⊓ F₁ ≤ B := inf_le_left.trans hK₀B
  have hker : ∀ x ∈ B, flagCoord he φ z a₁ a₂ q₁ q₂ k₁ x = 0 ↔ x ∈ K₀ ⊓ F₁ := by
    intro x hx
    constructor
    · intro h0
      obtain ⟨t, y, y', M, k, hk, rfl⟩ := hdec x hx
      rw [hκ t y y' M k hk] at h0
      have e1 : (M : M₃) 1 1 = 0 := congrFun (congrArg (fun v : FlagW => v.1.1) h0) 0
      have e2 : (M : M₃) 1 2 = 0 := congrFun (congrArg (fun v : FlagW => v.1.1) h0) 1
      have e3 : (M : M₃) 2 2 = 0 := congrFun (congrArg (fun v : FlagW => v.1.1) h0) 2
      have e4 : labJ he φ (z⁻¹ * (k⁻¹ * z * k)) = 0 := congrArg (fun v : FlagW => v.1.2) h0
      have e5 : y = 0 := congrFun (congrArg (fun v : FlagW => v.2.1) h0) 0
      have e6 : y' = 0 := congrFun (congrArg (fun v : FlagW => v.2.1) h0) 1
      have e7 : t = 0 := congrArg (fun v : FlagW => v.2.2) h0
      subst e5 e6 e7
      rw [ZMod.val_zero, pow_zero, pow_zero, pow_zero, one_mul, one_mul, one_mul]
      have hJQ : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, j ∈ K₀ ⊓ F₁ := fun j hj => by
        refine mem_inf.2 ⟨hJK₀ hj, (hF₁ j).2 ⟨hC₁D (hAC₁ (mem_inf.1 hj).1), ?_⟩⟩
        have hjz : j⁻¹ * z * j = z := by
          rw [mul_assoc, ← hzL j (hAL (mem_inf.1 hj).1), inv_mul_cancel_left]
        rw [hjz, inv_mul_cancel]
        exact one_mem _
      have hkQ : k ∈ K₀ ⊓ F₁ := by
        refine mem_inf.2 ⟨hk, (hF₁ k).2 ⟨hC₁D (hK₀C₁ hk), ?_⟩⟩
        exact mem_zpowers_of_labJ he hb φ hzC hz (hγB k (hK₀B hk)) e4
      exact mul_mem (hJQ _ (hτJ M e1 e2 e3)) hkQ
    · intro hxQ
      obtain ⟨hxK, hxF⟩ := mem_inf.1 hxQ
      have hxP : x ∈ P := hK₀P hxK
      have hγx : z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) := ((hF₁ x).1 hxF).2
      unfold flagCoord
      rw [hβak a₁ ha₁A x hxK, hβak a₂ ha₂A x hxK, hβzk, labJ_of_mem_zpowers he hb φ hzC hz hγx,
        hβPP x hxP q₁ (hA₂P hq₁A), hβPP x hxP q₂ (hA₂P hq₂A), hβPP x hxP k₁ (hK₀P hk₁K)]
      refine Prod.ext (Prod.ext ?_ rfl) (Prod.ext ?_ rfl)
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i <;> rfl
  have hsq : ∀ y ∈ B, y ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) →
      flagQuad (flagCoord he φ z a₁ a₂ q₁ q₂ k₁ y) = 0 := by
    intro x hx hxI
    obtain ⟨t, y, y', M, k, hk, rfl⟩ := hdec x hx
    have hτA : tauHom φ he (Multiplicative.ofAdd M) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have hpP : tauHom φ he (Multiplicative.ofAdd M) * k ∈ P := mul_mem (hA₂P hτA) (hK₀P hk)
    have hpB : tauHom φ he (Multiplicative.ofAdd M) * k ∈ B := hPB hpP
    set s := z ^ t.val * a₁ ^ y.val * a₂ ^ y'.val with hsdef
    set p := tauHom φ he (Multiplicative.ofAdd M) * k with hpdef
    have hp2I : p ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := hPsq p hpP
    have hp2c : p ^ 2 * s⁻¹ = s⁻¹ * p ^ 2 := hJB _ (hIJ hp2I) _ (inv_mem (hsB t y y'))
    have hkey : ∀ s' p' : G, s'⁻¹ = s' → (s' * p') ^ 2 = s'⁻¹ * p' ^ 2 * p'⁻¹ * s' * p' :=
      fun s' p' h => by
        rw [h, sq, sq]
        group
    have hsq' : (s * p) ^ 2 = p ^ 2 * (s⁻¹ * p⁻¹ * s * p) := by
      calc (s * p) ^ 2 = s⁻¹ * p ^ 2 * p⁻¹ * s * p := hkey s p (hs_inv t y y')
        _ = p ^ 2 * s⁻¹ * p⁻¹ * s * p := by rw [← hp2c]
        _ = p ^ 2 * (s⁻¹ * p⁻¹ * s * p) := by group
    have hlab : labJ he φ ((s * p) ^ 2) = 0 := labJ_of_mem_zpowers he hb φ hzC hz hxI
    rw [hsq', labJ_mul he φ (hIJ hp2I).2 (hBB s (hsB t y y') p hpB).2,
      labJ_of_mem_zpowers he hb φ hzC hz hp2I, zero_add] at hlab
    change commLab he φ s p = 0 at hlab
    rw [hsdef, hpdef, hβsl t y y' _ hpB,
      commLab_mul_right he hb φ hBB hJB hzB (hA₂B hτA) (hK₀B hk),
      commLab_mul_right he hb φ hBB hJB (hA₁B' ha₁A) (hA₂B hτA) (hK₀B hk),
      commLab_mul_right he hb φ hBB hJB (hA₁B' ha₂A) (hA₂B hτA) (hK₀B hk),
      hβzL _ (hA₂L hτA), hβzk, hβa₁, hβa₂, hβak a₁ ha₁A k hk, hβak a₂ ha₂A k hk] at hlab
    rw [hκ t y y' M k hk]
    have hsym : (M : M₃) 2 1 = (M : M₃) 1 2 := congrFun (congrFun M.2 1) 2
    rw [← hlab]
    funext i
    fin_cases i
    · simp [flagQuad, BinarySymmetricTwoFlag.symMat, hsym, Matrix.vecHead, Matrix.vecTail]
      ring
    · simp [flagQuad, BinarySymmetricTwoFlag.symMat, hsym, Matrix.vecHead, Matrix.vecTail]
      ring
  have hPκ : ∀ x ∈ B, (flagCoord he φ z a₁ a₂ q₁ q₂ k₁ x).2 = 0 ↔ x ∈ P := by
    intro x hx
    constructor
    · intro h0
      obtain ⟨t, y, y', M, k, hk, rfl⟩ := hdec x hx
      rw [hκ t y y' M k hk] at h0
      have e5 : y = 0 := congrFun (congrArg (fun v : FlagY => v.1) h0) 0
      have e6 : y' = 0 := congrFun (congrArg (fun v : FlagY => v.1) h0) 1
      have e7 : t = 0 := congrArg (fun v : FlagY => v.2) h0
      subst e5 e6 e7
      rw [ZMod.val_zero, pow_zero, pow_zero, pow_zero, one_mul, one_mul, one_mul]
      exact mul_mem (hA₂P ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩)) (hK₀P hk)
    · intro hp
      unfold flagCoord
      rw [hβPP x hp q₁ (hA₂P hq₁A), hβPP x hp q₂ (hA₂P hq₂A), hβPP x hp k₁ (hK₀P hk₁K)]
      refine Prod.ext ?_ rfl
      funext i
      fin_cases i <;> rfl
  have hP₁κ : ∀ x ∈ B, flagCoord he φ z a₁ a₂ q₁ q₂ k₁ x ∈ flagP1Sub → x ∈ P₁ := by
    intro x hx h0
    obtain ⟨t, y, y', M, k, hk, rfl⟩ := hdec x hx
    rw [hκ t y y' M k hk, mem_flagP1Sub] at h0
    obtain ⟨h1, h2⟩ := h0
    have e1 : (M : M₃) 1 1 = 0 := congrFun h1 0
    have e2 : (M : M₃) 1 2 = 0 := congrFun h1 1
    have e3 : (M : M₃) 2 2 = 0 := congrFun h1 2
    change t = 0 at h2
    subst h2
    rw [ZMod.val_zero, pow_zero, one_mul]
    have hA₁P₁ : 𝒜₁ ≤ P₁ := by
      rw [hP₁]
      exact le_sup_left
    have hK₀P₁ : K₀ ≤ P₁ := by
      rw [hP₁]
      exact le_sup_right
    exact mul_mem (mul_mem (hA₁P₁ (pow_mem ha₁A _)) (hA₁P₁ (pow_mem ha₂A _)))
      (mul_mem (hK₀P₁ (hJK₀ (hτJ M e1 e2 e3))) (hK₀P₁ hk))
  exact ⟨flagCoord he φ z a₁ a₂ q₁ q₂ k₁, hadd, hker, hsq, hPκ, hP₁κ⟩

end Main

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
