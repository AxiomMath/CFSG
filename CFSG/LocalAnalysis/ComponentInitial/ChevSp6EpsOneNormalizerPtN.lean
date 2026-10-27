module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtBasic
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixFusionOrbits
import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroNorm
import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtOrders

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open SymplecticTorusWeyl
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e} {hb : b.IsAlt}
variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}
variable {D₁ C₁ F₁ : Subgroup G} {ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2}

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝐛₁" => ptB₁ he hb φ hzC hz
local notation "𝒵₁" => Subgroup.map C₁.subtype (center C₁)
local notation "𝒫₁" => 𝒜₁ ⊔ (C₁ ⊓ C₂)
local notation "𝒫₂" => 𝒜₂ ⊔ (C₁ ⊓ C₂)
local notation "𝔅" => zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))
local notation "𝔑" => normalizer ((zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) :
  Subgroup G) : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G)
local notation "𝒮_H" => zpowers z ⊔ 𝒜₂ ⊔ Subgroup.map (leviHom φ he) (unitriangularGL 3 (ZMod 2))

theorem PtBase.ptN_exists_sigma (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    ∃ σ' : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
      GL (Fin 3) (ZMod 2), σ'.ker = (radSub φ z e).subgroupOf
        (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) ∧
      (∀ (n : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)))
        (hn : (n : G) ∈ L) (j : Fin 3),
        linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ' n : M₃) i j • e (Sum.inl i)) ∧
      ∀ (n : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)))
        (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
        LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
        ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
          LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
            fromBlocks 1 ((σ' n : M₃) * B * (σ' n : M₃)ᵀ) 0 1 := by
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_basis e
  obtain ⟨σ', -, hker, hcol, hconj⟩ :=
    FusionOrbits.exists_sigma hzC h.hsup h.hinf hb h.hnd h.hV φ he
  exact ⟨σ', hker, hcol, hconj⟩

theorem ptN_sup_four {α : Type*} [Lattice α] (a b c d : α) :
    a ⊔ ((b ⊔ d) ⊔ (c ⊔ d)) = a ⊔ b ⊔ c ⊔ d := by
  apply le_antisymm
  · refine sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
      (sup_le (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right))
    · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
    · exact le_sup_right.trans le_sup_left
  · refine sup_le (sup_le (sup_le le_sup_left ?_) ?_) ?_
    · exact (le_sup_left : b ≤ b ⊔ d).trans (le_sup_left.trans le_sup_right)
    · exact (le_sup_left : c ≤ c ⊔ d).trans (le_sup_right.trans le_sup_right)
    · exact (le_sup_right : d ≤ c ⊔ d).trans (le_sup_right.trans le_sup_right)

theorem PtBase.ptN_sq_mem (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {c : G}
    (hc : c ∈ C₁) : c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  rw [← h.hC₁sq]
  exact subset_closure ⟨c, hc, rfl⟩

theorem PtBase.ptN_mem_F₁_iff (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (d : G) :
    d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz) :=
  ⟨fun hd => ⟨h.hFD₁ hd, (h.hγF₁ d (h.hFD₁ hd)).2 hd⟩, fun hd => (h.hγF₁ d hd.1).1 hd.2⟩

theorem PtBase.ptN_K₀J (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {j : G}
    (hj : j ∈ 𝒜₁ ⊓ 𝒜₂) : ∃ k ∈ C₁ ⊓ C₂, z⁻¹ * (k⁻¹ * z * k) = j := by
  have hzj : z * j ∈ conjClass (C₁ ⊓ D₂) z := by
    rw [h.hK₀z]
    exact Set.smul_mem_smul_set hj
  obtain ⟨k, hk, hkz⟩ := mem_conjClass_iff_right.1 hzj
  exact ⟨k, by rw [h.hC₁C₂]; exact hk, by rw [hkz]; group⟩

theorem PtBase.ptN_Kz (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {j : G}
    (hj : j ∈ 𝒜₁ ⊓ 𝒜₂) : ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j := by
  obtain ⟨k, hk, hkz⟩ := h.ptN_K₀J hj
  refine ⟨k, mem_inf.2 ⟨h.hC₁D (mem_inf.1 hk).1, h.toLagBase.C₂D₂ (mem_inf.1 hk).2⟩, ?_⟩
  rw [← hkz]
  group

theorem PtBase.ptN_block [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    D₁ ⊔ 𝒜₂ ≤ 𝔑 ∧ D₂ ≤ 𝔑 ∧ 𝔅 ≤ normalizer ((𝒫₂ : Subgroup G) : Set G) ∧
    (∀ x ∈ 𝒫₂, x ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧
    (∀ Y : Subgroup G, Y ≤ 𝔅 → Nat.card Y = 512 →
      (∀ y ∈ Y, y ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz)) → Y = 𝒫₂) ∧
    (∀ Y : Subgroup G, Y ≤ 𝔅 → Nat.card Y = 256 →
      (∀ y ∈ Y, y ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz)) →
      Nat.card (Y ⊔ 𝒫₂ : Subgroup G) = 2048 → Y = 𝒫₁) := by
  classical
  have hBeq : (𝔅 : Subgroup G) = zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ C₁ ⊓ C₂ := ptN_sup_four _ _ _ _
  have hPcard : Nat.card (𝒫₂ : Subgroup G) = 512 := by
    rw [h.hC₁C₂]
    exact h.hPcard
  have hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := fun c hc => h.ptN_sq_mem hc
  have hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j := fun j hj => h.ptN_Kz hj
  have hK₀J : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ C₁ ⊓ C₂, z⁻¹ * (k⁻¹ * z * k) = j := fun j hj =>
    h.ptN_K₀J hj
  obtain ⟨-, -, hBV₁, -, hV₁N, hPB, -, -, hA₁V₁, -, hγB, hBNP⟩ :=
    degree64_next_block he hb h.hnd φ hzC h.hinf hz (D₁ := D₁) (C₁ := C₁) (D₂ := D₂)
      (C₂ := C₂) (K₀ := C₁ ⊓ C₂) (P := 𝒫₂) (B := 𝔅) (V₁ := D₁ ⊔ 𝒜₂) h.hD₁N h.hD₁n h.hD₁H
      h.hγD₁ h.hb₁c h.hC₁D h.hC₁n h.hC₁z h.hC₁B h.hC₁card hC₁sq h.hD₂n h.hRD₂ h.hD₂H h.hν₂z hKz
      h.hC₂R h.hC₁C₂ h.hC₁C₂ rfl hBeq rfl hPcard
  obtain ⟨σ', hσker, hσcol, hσ'⟩ := h.ptN_exists_sigma
  have hC₂D : C₂ ≤ D₂ := h.toLagBase.C₂D₂
  have hD₂A : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d := fun d hd a ha => h.toLagBase.D₂A hd ha
  have hνmul : ∀ c ∈ C₂, ∀ c' ∈ C₂, ν₂ (c * c') = ν₂ c + ν₂ c' := fun c hc c' hc' =>
    h.toLagBase.nu_mul h.hinf (hC₂D hc) (hC₂D hc')
  have hC₂comm : ∀ c ∈ C₂, ∀ d ∈ C₂, c⁻¹ * d⁻¹ * c * d ∈ 𝒜₂ := fun c hc d hd =>
    comm_mem_of_sq_mem (C := C₂) (K := 𝒜₂) (fun y hy => by
      rw [h.hsq y hy]
      exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩) hc hd
  have hD₂T := epsOne_D₂_conj_mem he hb h.hnd φ hzC h.hsup hz σ' hσ' hσcol (D₂ := D₂)
    (C₂ := C₂) (K₀ := C₁ ⊓ C₂) (P := 𝒫₂) (B := 𝔅) h.hν₂z hD₂A hC₂D h.hC₂n h.hDzC hνmul h.hνk
    hC₂comm inf_le_right rfl hBeq hBNP hγB hK₀J
  have hIJ : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ ⊓ 𝒜₂ := zpowers_ptB₁_le he hb φ hzC hz
  have hb₁A : ptB₁ he hb φ hzC hz ∈ 𝒜₂ := (hIJ (mem_zpowers _)).2
  have hD₂N : D₂ ≤ 𝔑 := fun d hd => mem_inf.2 ⟨mem_normalizer_of_conj_mem fun x hx => by
      have h1 : d * x * d⁻¹ = (d * x * d⁻¹ * x⁻¹) * x := by group
      rw [h1]
      exact mul_mem (hPB (hD₂T d hd x hx)) hx,
    mem_centralizer_singleton_iff.2 (hD₂A d hd _ hb₁A)⟩
  have hK₀P : ∀ k ∈ C₁ ⊓ C₂, k ∈ 𝒜₂ ⊔ C₁ ⊓ D₂ := fun k hk => by
    rw [← h.hC₁C₂]
    exact mem_sup_right hk
  have hK₀A' : ∀ k ∈ C₁ ⊓ C₂, ∀ a ∈ 𝒜₂, k * a = a * k := fun k hk a ha =>
    h.hPcomm k (hK₀P k hk) a (mem_sup_left ha)
  have hPc : ∀ p ∈ 𝒫₂, ∀ q ∈ 𝒫₂, p * q = q * p := by
    rw [h.hC₁C₂]
    exact h.hPcomm
  have hA₂NK : 𝒜₂ ≤ normalizer ((C₁ ⊓ C₂ : Subgroup G) : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk => hK₀A' k hk a ha)
  have hP₂sq : ∀ p ∈ 𝒫₂, p ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    intro p hp
    have hp' : p ∈ ((𝒜₂ ⊔ C₁ ⊓ C₂ : Subgroup G) : Set G) := hp
    rw [coe_mul_of_left_le_normalizer_right _ _ hA₂NK] at hp'
    obtain ⟨a, ha, k, hk, rfl⟩ := hp'
    have ha2 : a ^ 2 = 1 := sq_eq_one_of_mem_radA he φ ha
    have h2 : (a * k) ^ 2 = k ^ 2 := by
      calc (a * k) ^ 2 = a * (k * a) * k := by rw [sq]; group
        _ = a * (a * k) * k := by rw [hK₀A' k hk a ha]
        _ = a ^ 2 * k ^ 2 := by rw [sq, sq]; group
        _ = k ^ 2 := by rw [ha2, one_mul]
    rw [h2]
    exact hC₁sq k (mem_inf.1 hk).1
  have hk₁ := hK₀J _ ((mem_ptA_inf_radA_iff he hb φ).2 ⟨0, 1, 0, rfl⟩)
  have hA₁B : ∀ a ∈ 𝒜₁, ∀ x ∈ 𝔅, a⁻¹ * x⁻¹ * a * x ∈ 𝒜₁ ⊓ 𝒜₂ := fun a ha x hx =>
    hA₁V₁ a ha x (hBV₁ hx)
  have hA₂D : 𝒜₂ ≤ D₂ := fun a ha => h.hRD₂ (mem_sup_left ha)
  obtain ⟨κ, hadd, hker, hsq, hPκ, hP₁κ⟩ := epsOne_flag_package he hb h.hnd φ hzC h.hsup h.hinf
    hz σ' hσ' hσcol hσker (D₁ := D₁) (C₁ := C₁) (D₂ := D₂) (K₀ := C₁ ⊓ C₂) (P := 𝒫₂) (P₁ := 𝒫₁)
    (B := 𝔅) (F₁ := F₁) h.hC₁D h.hC₁B hC₁sq hA₂D h.hC₁C₂ rfl rfl hBeq h.ptN_mem_F₁_iff hγB hA₁B
    hBNP hK₀A' hPc hP₂sq hk₁
  have hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ := h.hC₁n z (le_normalizer (mem_sup_right (mem_zpowers z)))
  have hQ₀ : Nat.card ((C₁ ⊓ C₂) ⊓ F₁ : Subgroup G) = 16 := by
    rw [h.hC₁C₂]
    exact card_Q₀ he hb h.hnd φ hzC h.hinf hz h.hD₂H h.hRD₂ h.hD₁H h.hC₁D h.hC₁B h.hC₁z hzC₁ hKz
      h.ptN_mem_F₁_iff
  have hP₁card : Nat.card (𝒫₁ : Subgroup G) = 256 := by
    rw [h.card_P₁]
    norm_num
  refine ⟨hV₁N, hD₂N, hBNP, hP₂sq, fun Y hYB hYc hYsq => eq_of_flagCoord κ hadd hker hQ₀ hsq hPB
    hPcard (fun p hp => (hPκ p (hPB hp)).2 hp) hYB hYc hYsq, fun Y hYB hYc hYsq hYP =>
    eq_P₁_of_flagCoord κ hadd hker hQ₀ hsq hPB (fun p hp => (hPκ p (hPB hp)).2 hp) hBNP hP₁κ
      hP₁card hYB hYc hYsq hYP⟩

theorem ptN_leviHom_apply_e₁ (φ : L ≃* bilinIsometryGroup b) (he : IsSymplecticBasis b e)
    {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ unitriangularGL 3 (ZMod 2)) :
    linOf (φ ⟨leviHom φ he g, leviHom_mem φ he g⟩) (e (Sum.inl 0)) = e (Sum.inl 0) := by
  have hg' : IsUnitriangular (g : M₃) := hg
  obtain ⟨hU, hD⟩ := hg'
  have hM := toMatrix_spHom φ he (leviSp g)
  apply e.repr.injective
  ext i
  have h1 := congrFun (congrFun hM i) (Sum.inl 0)
  rw [LinearMap.toMatrix_apply] at h1
  change e.repr (linOf (φ ⟨spHom φ he (leviSp g), spHom_mem φ he _⟩) (e (Sum.inl 0))) i = _
  rw [h1, Basis.repr_self, spMatrixOf, coe_leviSp]
  rcases i with i | i
  · rw [fromBlocks_apply₁₁]
    fin_cases i
    · simp [hD 0]
    · simp [hU (show (0 : Fin 3) < 1 by decide)]
    · simp [hU (show (0 : Fin 3) < 2 by decide)]
  · rw [fromBlocks_apply₂₁]
    simp

theorem PtBase.ptN_levi_mem [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ unitriangularGL 3 (ZMod 2)) : leviHom φ he g ∈ 𝔑 := by
  set l := leviHom φ he g with hl
  have hlL : l ∈ L := leviHom_mem φ he g
  have hlN₁ : l ∈ 𝒩₁ := by
    obtain ⟨-, -, -, -, hAN, -⟩ := ptA_facts he hb h.hnd φ
    have haV : l ∈ pullSub φ (vecStabilizer b (e (Sum.inl 0))) :=
      mem_pullSub.2 ⟨hlL, by rw [mem_vecStabilizer]; exact ptN_leviHom_apply_e₁ φ he hg⟩
    rw [← hAN] at haV
    exact inf_normalizer_le_normalizer_sup _ _
      (mem_inf.2 ⟨(mem_inf.1 haV).1, mem_normalizer_zpowers hzC hlL⟩)
  have hlN₂ : l ∈ 𝒩₂ := leviHom_mem_normalizer_radSub φ he hzC hz g
  have hlz : l * z * l⁻¹ = z := by
    rw [leviHom_mul_z φ he hzC g, mul_inv_cancel_right]
  have hle : (𝔅 : Subgroup G) ≤ (𝔅 : Subgroup G).comap (MulAut.conj l).toMonoidHom := by
    have hA₁ : ∀ a ∈ 𝒜₁, l * a * l⁻¹ ∈ 𝒜₁ := fun a ha => h.hA₁n l hlN₁ a ha
    have hA₂ : ∀ a ∈ 𝒜₂, l * a * l⁻¹ ∈ 𝒜₂ := fun a ha => by
      obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
      rw [← ofAdd_toAdd B, leviHom_conj_tauHom']
      exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have hK : ∀ k ∈ C₁ ⊓ C₂, l * k * l⁻¹ ∈ C₁ ⊓ C₂ := fun k hk =>
      mem_inf.2 ⟨h.hC₁n l hlN₁ k (mem_inf.1 hk).1, h.hC₂n l hlN₂ k (mem_inf.1 hk).2⟩
    refine sup_le ?_ (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_))
    · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hlz]
      exact mem_sup_left (mem_zpowers z)
    · intro a ha
      exact mem_sup_right (mem_sup_left (mem_sup_left (hA₁ a ha)))
    · intro k hk
      exact mem_sup_right (mem_sup_left (mem_sup_right (hK k hk)))
    · intro a ha
      exact mem_sup_right (mem_sup_right (mem_sup_left (hA₂ a ha)))
    · intro k hk
      exact mem_sup_right (mem_sup_right (mem_sup_right (hK k hk)))
  exact mem_inf.2 ⟨mem_normalizer_of_conj_mem fun x hx => hle hx,
    mem_centralizer_singleton_iff.2 (h.hb₁c l hlN₁)⟩

theorem PtBase.S₁_le_N [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    D₁ ⊔ 𝒮_H ≤ 𝔑 := by
  obtain ⟨hV₁N, -⟩ := h.ptN_block
  refine sup_le (le_sup_left.trans hV₁N) (sup_le (sup_le ?_ (le_sup_right.trans hV₁N)) ?_)
  · rw [zpowers_le]
    exact hV₁N (mem_sup_left h.zD₁)
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    exact h.ptN_levi_mem hg

theorem PtBase.S₂_le_N [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    D₂ ⊔ 𝒮_H ≤ 𝔑 := by
  obtain ⟨-, hD₂N, -⟩ := h.ptN_block
  exact sup_le hD₂N (le_sup_right.trans h.S₁_le_N)

theorem ptN_conj_I₁ {m : G} (hm : m ∈ 𝔑) {i : G} (hi : i ∈ zpowers (ptB₁ he hb φ hzC hz)) :
    m * i * m⁻¹ ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  have hmb : Commute m (ptB₁ he hb φ hzC hz) :=
    mem_centralizer_singleton_iff.1 (mem_inf.1 hm).2
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hi
  rw [(hmb.zpow_right k).eq, mul_inv_cancel_right]
  exact hi

theorem PtBase.ptN_map_P₂ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {m : G} (hm : m ∈ 𝔑) : (𝒫₂ : Subgroup G).map (MulAut.conj m).toMonoidHom = 𝒫₂ := by
  obtain ⟨-, -, -, hP₂sq, huniq₂, -⟩ := h.ptN_block
  have hPcard : Nat.card (𝒫₂ : Subgroup G) = 512 := by
    rw [h.hC₁C₂]
    exact h.hPcard
  exact map_conj_eq_of_unique_sq (le_sup_right.trans le_sup_right) hP₂sq
    (fun Y hYB hYc hYsq => huniq₂ Y hYB (hYc.trans hPcard) hYsq) (mem_inf.1 hm).1
    (fun i hi => ptN_conj_I₁ hm hi)

theorem PtBase.conj_mem_P₂ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {m : G} (hm : m ∈ 𝔑) {p : G} (hp : p ∈ 𝒫₂) : m * p * m⁻¹ ∈ 𝒫₂ :=
  conj_mem_of_map_conj_eq (h.ptN_map_P₂ hm) hp

theorem PtBase.conj_mem_P₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {m : G} (hm : m ∈ 𝔑) {p : G} (hp : p ∈ 𝒫₁) : m * p * m⁻¹ ∈ 𝒫₁ := by
  obtain ⟨-, -, -, -, -, huniq₁⟩ := h.ptN_block
  have hP₁card : Nat.card (𝒫₁ : Subgroup G) = 256 := by
    rw [h.card_P₁]
    norm_num
  have hAcard : Nat.card (𝒫₁ ⊔ 𝒫₂ : Subgroup G) = 2048 := by
    rw [h.card_A]
    norm_num
  have hP₁B : (𝒫₁ : Subgroup G) ≤ 𝔅 := le_sup_left.trans le_sup_right
  have hY : (𝒫₁ : Subgroup G).map (MulAut.conj m).toMonoidHom = 𝒫₁ := by
    refine huniq₁ _ ?_ (by rw [card_map_of_injective (MulAut.conj m).injective, hP₁card]) ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (mem_normalizer_iff.1 (mem_inf.1 hm).1 q).1 (hP₁B hq)
    · rintro _ ⟨q, hq, rfl⟩
      have h2 : (MulAut.conj m).toMonoidHom q ^ 2 = m * q ^ 2 * m⁻¹ := by
        rw [← map_pow]
        rfl
      rw [h2]
      exact ptN_conj_I₁ hm (h.ptN_sq_mem (h.P₁C₁ hq))
    · rw [← h.ptN_map_P₂ hm, ← Subgroup.map_sup, card_map_of_injective (MulAut.conj m).injective,
        hAcard]
  exact conj_mem_of_map_conj_eq hY hp

theorem PtBase.ptN_mem_zP₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {y : G} (hy : y ∈ zpowers z ⊔ 𝒫₁) : ∃ p ∈ 𝒫₁, y = p ∨ y = z * p := by
  have hzP₁ : zpowers z ≤ normalizer ((𝒫₁ : Subgroup G) : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_conj_mem fun x hx => conj_mem_sup (fun a ha => ?_)
      (fun k hk => h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk) hx
    rw [← mul_comm_z hzC (pullSub_le φ _ ha), mul_inv_cancel_right]
    exact ha
  have hy' : y ∈ ((zpowers z ⊔ 𝒫₁ : Subgroup G) : Set G) := hy
  rw [coe_mul_of_left_le_normalizer_right _ _ hzP₁] at hy'
  obtain ⟨t, ht, p, hp, rfl⟩ := hy'
  refine ⟨p, hp, ?_⟩
  rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hz ht with rfl | rfl
  · exact Or.inl (one_mul p)
  · exact Or.inr rfl

theorem PtBase.ptN_F₁_le [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    F₁ ≤ zpowers z ⊔ 𝒫₁ := by
  have hzF₁ : z ∈ F₁ := h.hBF₁ (mem_sup_right (mem_zpowers z))
  have hzC₁ : zpowers z ≤ normalizer ((C₁ : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_of_conj_mem fun c hc => h.hC₁n z z_mem_N₁ c hc
  have hE₁ : C₁ ⊓ F₁ ≤ 𝒫₁ := by
    rw [h.hE₁]
    refine sup_le le_sup_left (fun x hx => mem_sup_right (mem_inf.2 ⟨?_, h.hZ₁C₂ hx⟩))
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  intro f hf
  have hf' : f ∈ ((zpowers z ⊔ C₁ : Subgroup G) : Set G) := by
    rw [h.hC₁z]
    exact h.hFD₁ hf
  rw [coe_mul_of_left_le_normalizer_right _ _ hzC₁] at hf'
  obtain ⟨t, ht, c, hc, rfl⟩ := hf'
  have htF : t ∈ F₁ := by
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hz ht with rfl | rfl
    · exact one_mem _
    · exact hzF₁
  have hcF : c ∈ F₁ := by
    have h1 := mul_mem (inv_mem htF) hf
    rwa [inv_mul_cancel_left] at h1
  exact mul_mem (mem_sup_left ht) (mem_sup_right (hE₁ (mem_inf.2 ⟨hc, hcF⟩)))

theorem PtBase.ptN_conj_I₁_of_N₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {n : G}
    (hn : n ∈ 𝒩₁) {i : G} (hi : i ∈ zpowers (ptB₁ he hb φ hzC hz)) :
    n * i * n⁻¹ ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  have hnb : Commute n (ptB₁ he hb φ hzC hz) := h.hb₁c n hn
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hi
  rw [(hnb.zpow_right k).eq, mul_inv_cancel_right]
  exact hi

theorem PtBase.ptN_comm_mem [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {c : G} (hc : c ∈ C₁) (hcz : z⁻¹ * (c⁻¹ * z * c) ∈ zpowers (ptB₁ he hb φ hzC hz)) {y : G}
    (hy : y ∈ zpowers z ⊔ 𝒫₁) : y⁻¹ * c⁻¹ * y * c ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  have hC₁c : ∀ p ∈ C₁, p⁻¹ * c⁻¹ * p * c ∈ zpowers (ptB₁ he hb φ hzC hz) := fun p hp =>
    comm_mem_of_sq_mem (C := C₁) (fun x hx => h.ptN_sq_mem hx) hp hc
  obtain ⟨p, hp, rfl | rfl⟩ := h.ptN_mem_zP₁ hy
  · exact hC₁c _ (h.P₁C₁ hp)
  · have hpN : p⁻¹ ∈ 𝒩₁ := inv_mem (h.hD₁N (h.P₁D₁ hp))
    have h1 : (z * p)⁻¹ * c⁻¹ * (z * p) * c =
        (p⁻¹ * (z⁻¹ * (c⁻¹ * z * c)) * p⁻¹⁻¹) * (p⁻¹ * c⁻¹ * p * c) := by group
    rw [h1]
    exact mul_mem (h.ptN_conj_I₁_of_N₁ hpN hcz) (hC₁c p (h.P₁C₁ hp))

theorem PtBase.K₁_le_normalizer_F₁ [Finite G]
    (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) ≤ normalizer (F₁ : Set G) := by
  intro m hm
  obtain ⟨hmN, hmU⟩ := mem_inf.1 hm
  rw [h.U₁_eq] at hmU
  have hz1 : z * z = 1 := z_mul_self hz
  have hzF₁ : z ∈ F₁ := h.hBF₁ (mem_sup_right (mem_zpowers z))
  have hUD : zpowers z ⊔ 𝒫₁ ≤ D₁ := sup_le (zpowers_le.2 h.zD₁) h.P₁D₁
  have hw : m * z * m⁻¹ ∈ zpowers z ⊔ 𝒫₁ :=
    (mem_normalizer_iff.1 hmU z).1 (h.ptN_F₁_le hzF₁)
  obtain ⟨c, hcP, hwc⟩ := h.ptN_mem_zP₁ hw
  have hwc' : m * z * m⁻¹ = z * c := by
    rcases hwc with hwc | hwc
    · exfalso
      have h1 := h.conj_mem_P₁ (inv_mem hmN) (hwc ▸ hcP)
      rw [show m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z by group] at h1
      exact h.z_not_mem_C₁ (h.P₁C₁ h1)
    · exact hwc
  have hcC : c ∈ C₁ := h.P₁C₁ hcP
  have hw2 : z * c * z * c = 1 := by
    have h1 : (m * z * m⁻¹) * (m * z * m⁻¹) = 1 := by
      rw [show (m * z * m⁻¹) * (m * z * m⁻¹) = m * (z * z) * m⁻¹ by group, hz1, mul_one,
        mul_inv_cancel]
    rw [hwc'] at h1
    rw [← h1]
    group
  have hcinv : c⁻¹ = z * c * z := (eq_inv_of_mul_eq_one_left hw2).symm
  have hcz : z⁻¹ * (c⁻¹ * z * c) ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    have h1 : z⁻¹ * (c⁻¹ * z * c) = c ^ 2 := by
      rw [hcinv]
      calc z⁻¹ * (z * c * z * z * c) = c * (z * z) * c := by group
        _ = c ^ 2 := by rw [hz1, mul_one, sq]
    rw [h1]
    exact h.ptN_sq_mem hcC
  refine mem_normalizer_of_conj_mem fun f hf => ?_
  have hy : m * f * m⁻¹ ∈ zpowers z ⊔ 𝒫₁ := (mem_normalizer_iff.1 hmU f).1 (h.ptN_F₁_le hf)
  have hfγ := ((h.ptN_mem_F₁_iff f).1 hf).2
  have hX := ptN_conj_I₁ hmN hfγ
  have hK := h.ptN_comm_mem hcC hcz hy
  refine (h.ptN_mem_F₁_iff _).2 ⟨hUD hy, ?_⟩
  set y := m * f * m⁻¹ with hydef
  have e1 : m * (z⁻¹ * (f⁻¹ * z * f)) * m⁻¹ = (z * c)⁻¹ * y⁻¹ * (z * c) * y := by
    rw [← hwc', hydef]
    group
  rw [e1] at hX
  have e2 : z⁻¹ * (y⁻¹ * z * y) =
      c * (((z * c)⁻¹ * y⁻¹ * (z * c) * y) * (y⁻¹ * c⁻¹ * y * c)) * c⁻¹ := by group
  rw [e2]
  exact h.ptN_conj_I₁_of_N₁ (h.hD₁N (h.hC₁D hcC)) (mul_mem hX hK)

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
