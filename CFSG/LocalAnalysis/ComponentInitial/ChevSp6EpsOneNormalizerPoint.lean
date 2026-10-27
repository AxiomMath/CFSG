module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtKernel
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagrangian

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open SymplecticTorusWeyl
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem symThreeSquare_additive_eq_zero : ∀ w : Fin 3 → ZMod 2,
    (∀ w' : Fin 3 → ZMod 2, symThreeSquare 1 (w + w') = symThreeSquare 1 w + symThreeSquare 1 w') →
      w = 0 := by
  decide

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
local notation "𝒫₁" => 𝒜₁ ⊔ (C₁ ⊓ C₂)
local notation "𝒫₂" => 𝒜₂ ⊔ (C₁ ⊓ C₂)
local notation "𝔅" => zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))
local notation "𝔑" => normalizer ((zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) :
  Subgroup G) : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G)
local notation "𝒮_H" => zpowers z ⊔ 𝒜₂ ⊔ Subgroup.map (leviHom φ he) (unitriangularGL 3 (ZMod 2))
local notation "𝒰₃" => Subgroup.map (leviHom φ he) (unitriangularGL 3 (ZMod 2))

theorem LagBase.characteristic_E₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) :
    (E₂.subgroupOf D₂).Characteristic := by
  refine PtF1.characteristic_subgroupOf_of_map h.E₂D₂ fun ϕ => ?_
  refine h.eq_E₂_of_le_D₂ (map_subtype_le _) (fun x hx => ?_)
    (by rw [PtF1.card_map_aut h.E₂D₂, h.hE₂card])
  obtain ⟨k, hk, rfl⟩ := (PtF1.mem_map_aut_iff ϕ).1 hx
  have hk2 : k ^ 2 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h.hE₂sq _ hk)
  rw [← Subgroup.coe_pow, ← map_pow, hk2, map_one, Subgroup.coe_one]

theorem LagBase.characteristic_C₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) :
    (C₂.subgroupOf D₂).Characteristic := by
  have hE := characteristic_iff_map_eq.1 h.characteristic_E₂
  refine PtF1.characteristic_subgroupOf_of_map h.C₂D₂ fun ϕ => ?_
  have hle : ((C₂.subgroupOf D₂).map ϕ.toMonoidHom).map D₂.subtype ≤ C₂ := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (PtF1.mem_map_aut_iff ϕ).1 hx
    rw [h.hC₂]
    refine mem_inf.2 ⟨(ϕ k).2, mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : y ∈ ((E₂.subgroupOf D₂).map ϕ.toMonoidHom).map D₂.subtype := by
      rw [hE ϕ, map_subgroupOf_eq_of_le h.E₂D₂]
      exact hy
    obtain ⟨y', hy'E, rfl⟩ := (PtF1.mem_map_aut_iff ϕ).1 hy'
    have hc : y' * k = k * y' := Subtype.ext (h.comm_E₂ hy'E hk)
    change ((ϕ y' : D₂) : G) * ((ϕ k : D₂) : G) = ((ϕ k : D₂) : G) * ((ϕ y' : D₂) : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [PtF1.card_map_aut h.C₂D₂])

theorem LagBase.center_C₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) : (center C₂).map C₂.subtype = E₂ := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨c, hc, rfl⟩ := hx
    have hcC : (c : G) ∈ C₂ := c.2
    have hcomm : ∀ c' ∈ C₂, Commute (c : G) c' := fun c' hc' =>
      (congrArg Subtype.val ((mem_center_iff.1 hc) ⟨c', hc'⟩)).symm
    refine (h.hδk c hcC).1 (symThreeSquare_additive_eq_zero _ fun w' => ?_)
    obtain ⟨c', hc', hw'⟩ := h.hδs w'
    have h1 := h.hsq _ (mul_mem hcC hc')
    have hδ : symThreeDiag (ν₂ ((c : G) * c') : M₃) = symThreeDiag (ν₂ c : M₃) + w' := by
      rw [h.nu_mul hinf (h.C₂D₂ hcC) (h.C₂D₂ hc'), ← hw', ← symThreeDiag_add]
      rfl
    rw [hδ, (hcomm c' hc').mul_pow 2, h.hsq _ hcC, h.hsq _ hc', hw', ← map_mul,
      ← ofAdd_add] at h1
    exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h1)).symm
  · exact ⟨⟨x, h.hEC hx⟩, mem_center_iff.2 fun g => Subtype.ext (h.comm_E₂ hx g.2).symm, rfl⟩

theorem PtBase.ptB₁_mem_C₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : 𝐛₁ ∈ C₁ := by
  have h1 : 𝐛₁ ∈ Subgroup.map C₁.subtype (center C₁) ⊓ 𝒜₁ := by
    rw [h.hZ₁A]
    exact mem_zpowers _
  exact map_subtype_le _ (mem_inf.1 h1).1

theorem PtBase.sq_mem_I₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x : G}
    (hx : x ∈ C₁) : x ^ 2 ∈ zpowers 𝐛₁ := by
  rw [← h.hC₁sq]
  exact subset_closure ⟨x, hx, rfl⟩

theorem PtBase.comm_mem_I₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x y : G}
    (hx : x ∈ C₁) (hy : y ∈ C₁) : x⁻¹ * y⁻¹ * x * y ∈ zpowers 𝐛₁ := by
  rw [← h.hC₁comm]
  have h1 := commutator_mem_commutator (inv_mem hx) (inv_mem hy)
  rwa [commutatorElement_def, inv_inv, inv_inv] at h1

section Growth

variable [Finite G] (h : PtFull he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
include h

theorem PtFull.relIndex_K₂_eq_two :
    (𝔑 ⊓ 𝒩₂).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G)) = 2 := by
  rw [← h.relIndex_K₁_eq]
  exact h.relIndex_K₁_eq_two

theorem PtFull.relIndex_normalizer_D₁ : (𝒩₁).relIndex (normalizer (D₁ : Set G)) = 2 := by
  obtain ⟨hDF, -, -, hidx⟩ := h.normalizer_D₁
  have h1 : (𝒩₁).relIndex (normalizer (D₁ : Set G)) ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    intro hle
    apply h.not_K₁_le_N₁
    intro x hx
    apply hle
    rw [hDF]
    exact h.K₁_le_normalizer_F₁ hx
  have h0 : (𝒩₁).relIndex (normalizer (D₁ : Set G)) ≠ 0 := by
    intro h0
    have h5 := Subgroup.relIndex_mul_card (H := 𝒩₁) (K := normalizer (D₁ : Set G))
    rw [h0, zero_mul] at h5
    exact (Nat.card_pos (α := normalizer (D₁ : Set G))).ne' h5.symm
  omega

omit [Finite G] in
theorem PtFull.card_P₂ : Nat.card (𝒫₂ : Subgroup G) = 2 ^ 9 := by
  rw [h.K₀_eq, h.hPcard]
  norm_num

theorem PtFull.P₂_inf_H : 𝒫₂ ⊓ centralizer ({z} : Set G) = 𝒜₂ := by
  refine le_antisymm (fun p hp => ?_) (le_inf le_sup_left fun a ha =>
    mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ ha)))
  obtain ⟨hpP, hpH⟩ := mem_inf.1 hp
  have hpR : p ∈ ℛ := by
    rw [← h.hD₂H]
    exact mem_inf.2 ⟨h.P₂D₂ hpP, hpH⟩
  have hpR' : p ∈ zpowers z ⊔ 𝒜₂ := by
    rw [sup_comm]
    exact hpR
  exact mem_of_mem_zpowers_sup hz le_sup_left (fun hz' => h.z_not_mem_C₂ (h.P₂C₂ hz'))
    (fun a ha => h.conj_A₂_mem z_mem_N₂ ha) hpR' hpP

theorem PtFull.mem_D₂_of_centralizes {s : G} (hs : s ∈ D₂ ⊔ 𝒮_H)
    (hsA : ∀ a ∈ 𝒜₂, s * a = a * s) : s ∈ D₂ := by
  have hS : D₂ ⊔ 𝒮_H = D₂ ⊔ 𝒰₃ := le_antisymm (sup_le le_sup_left (sup_le (sup_le
      ((zpowers_le.2 h.zD₂).trans le_sup_left) (h.A₂D₂.trans le_sup_left)) le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have hU : 𝒰₃ ≤ normalizer (D₂ : Set G) := fun u hu => mem_normalizer_of_conj_mem fun d hd =>
    h.hD₂n u (U₃_le_N₂_of he hzC hz hu) d hd
  have hs' : s ∈ ((D₂ ⊔ 𝒰₃ : Subgroup G) : Set G) := by
    rw [← hS]
    exact hs
  rw [coe_mul_of_right_le_normalizer_left _ _ hU] at hs'
  obtain ⟨d, hd, u, hu, hdu⟩ := hs'
  beta_reduce at hdu
  subst hdu
  obtain ⟨g, -, rfl⟩ := hu
  have hgA : ∀ a ∈ 𝒜₂, leviHom φ he g * a = a * leviHom φ he g := by
    intro a ha
    have h1 := hsA a ha
    have h2 := h.toLagBase.D₂A hd ha
    calc leviHom φ he g * a = d⁻¹ * (d * leviHom φ he g * a) := by group
      _ = d⁻¹ * (a * (d * leviHom φ he g)) := by rw [h1]
      _ = d⁻¹ * (a * d) * leviHom φ he g := by group
      _ = d⁻¹ * (d * a) * leviHom φ he g := by rw [h2]
      _ = a * leviHom φ he g := by group
  have hg1 : g = 1 := by
    have hfix : ∀ B : binarySymMatrices 3, symThreeCongr g B = B := by
      intro B
      have h1 := leviHom_conj_tauHom' φ he g B
      have hτ : tauHom φ he (Multiplicative.ofAdd B) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
      rw [hgA _ hτ, mul_inv_cancel_right] at h1
      exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h1)).symm
    refine symThreeCongrHom_injective (LinearEquiv.ext fun B => ?_)
    rw [symThreeCongrHom_apply, symThreeCongrHom_apply, hfix]
    exact Subtype.ext (by simp [symThreeCongr])
  rw [hg1, map_one, mul_one]
  exact hd

theorem PtFull.exists_T₂ : ∃ T₂ : Subgroup G,
    T₂ ≤ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) ∧ D₂ ⊔ 𝒮_H < T₂ ∧
      T₂ ≤ normalizer (D₂ : Set G) ∧ Nat.card T₂ = 2 ^ 17 := by
  have hK₂card : Nat.card (𝔑 ⊓ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) : Subgroup G) =
      3 * 2 ^ 17 := by
    have h1 := relIndex_mul_card_of_le h.N_inf_N₂_le
    rw [h.relIndex_K₂_eq_two, h.card_N_inf_N₂] at h1
    omega
  obtain ⟨T₂, hTcard, hST, hTK⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := 17) (by rw [h.card_S₂]; exact pow_dvd_pow 2 (by norm_num))
    (by rw [hK₂card]; exact Dvd.intro_left 3 rfl) h.S₂_le_K₂
  refine ⟨T₂, hTK, lt_of_le_of_ne hST fun hEq => ?_, ?_, hTcard⟩
  · have h1 := h.card_S₂
    rw [hEq, hTcard] at h1
    norm_num at h1
  have hTN : T₂ ≤ 𝔑 := hTK.trans inf_le_left
  have hTU : T₂ ≤ normalizer ((𝔅 ⊓ D₂ : Subgroup G) : Set G) := hTK.trans inf_le_right
  have hidx : (D₂ ⊔ 𝒮_H).relIndex T₂ = 2 := by
    have h1 := relIndex_mul_card_of_le hST
    rw [h.card_S₂, hTcard] at h1
    omega
  have hnorm : ((D₂ ⊔ 𝒮_H).subgroupOf T₂).Normal := normal_of_index_eq_two hidx
  have hS : ∀ x ∈ T₂, ∀ s ∈ D₂ ⊔ 𝒮_H, x * s * x⁻¹ ∈ D₂ ⊔ 𝒮_H := fun x hx s hs =>
    mem_subgroupOf.1 (hnorm.conj_mem ⟨s, hST hs⟩ (mem_subgroupOf.2 hs) ⟨x, hx⟩)
  have hzU : z ∈ 𝔅 ⊓ D₂ := mem_inf.2 ⟨mem_sup_left (mem_zpowers z), h.zD₂⟩
  have hAU : ∀ a ∈ 𝒜₂, ∀ u ∈ 𝔅 ⊓ D₂, a * u = u * a := by
    intro a ha u hu
    rw [h.U₂_eq] at hu
    have haP : a ∈ 𝒜₂ ⊔ (C₁ ⊓ D₂) := mem_sup_left ha
    have hle : zpowers z ⊔ 𝒫₂ ≤ centralizer ({a} : Set G) := sup_le
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ ha)).symm))
      (fun p hp => mem_centralizer_singleton_iff.2 (h.hPcomm p (by rw [← h.K₀_eq]; exact hp) a haP))
    exact (mem_centralizer_singleton_iff.1 (hle hu)).symm
  have hA : ∀ x ∈ T₂, ∀ a ∈ 𝒜₂, x * a * x⁻¹ ∈ 𝒜₂ := by
    intro x hx a ha
    rw [← h.P₂_inf_H]
    refine mem_inf.2 ⟨h.conj_mem_P₂ (hTN hx) (mem_sup_left ha),
      mem_centralizer_singleton_iff.2 ?_⟩
    have hu : x⁻¹ * z * x⁻¹⁻¹ ∈ 𝔅 ⊓ D₂ := (mem_normalizer_iff.1 (hTU (inv_mem hx)) z).1 hzU
    rw [inv_inv] at hu
    have h1 := hAU a ha _ hu
    calc x * a * x⁻¹ * z = x * (a * (x⁻¹ * z * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * z * x) * a) * x⁻¹ := by rw [h1]
      _ = z * (x * a * x⁻¹) := by group
  refine fun x hx => mem_normalizer_of_conj_mem fun d hd => ?_
  refine h.mem_D₂_of_centralizes (hS x hx d (mem_sup_left hd)) fun a ha => ?_
  have ha' : x⁻¹ * a * x ∈ 𝒜₂ := by
    have h1 := hA x⁻¹ (inv_mem hx) a ha
    rwa [inv_inv] at h1
  have h1 := h.toLagBase.D₂A hd ha'
  calc x * d * x⁻¹ * a = x * (d * (x⁻¹ * a * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * a * x) * d) * x⁻¹ := by rw [h1]
    _ = a * (x * d * x⁻¹) := by group

end Growth

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open SymplecticTorusWeyl EpsOne
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem standard_binary_symplectic_six_epsilon_one_point_radical_normalizer :
    EpsOnePointNormalizerStmt := by
  intro G _ _ hG L hL hLn hZ hmodel T hT z hzT hz hH V _ _ _ b hb hnd hV φ e he hfull
    u f E n Q r τ θ₂ θ₁ A₂ R₂ N₂ D₂ F₂ H A₁ b₁ I₁ B₁ N₁ D₁ F₁ E₂ C₂ ν₂ hlam hexp
  obtain ⟨hzC, σ, C₁', F₁', ν₁, h, hE₂⟩ :=
    ptFull_of_setting hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull hlam hexp
  have hcomp := standard_binary_symplectic_six_degree64_lagrangian_subgroup_completion hG hL hLn
    hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull
  have hκ : ∀ κ₂ : ZMod 2, (∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = θ₂ (C, 1) → d⁻¹ * θ₂ (B, ε) * d = θ₂ (B + κ₂ • symThreePolarSym
        (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)) → κ₂ = 0 :=
    fun κ₂ hκ₂ => (hcomp κ₂ 1 hκ₂ (fun d hd a v ε h' => by
      rw [one_mul]
      exact hlam d hd a v ε h')).1
  have hb₁ : b₁ = ptB₁ he hb φ hzC hz := (ptB₁_eq he hb φ hzC hz).symm
  have hF₁ : F₁ = (F₁' : Set G) := by
    ext d
    change d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers b₁ ↔ d ∈ F₁'
    rw [hb₁]
    constructor
    · rintro ⟨hd, hdI⟩
      exact (h.hγF₁ d hd).1 hdI
    · intro hd
      exact ⟨h.hFD₁ hd, (h.hγF₁ d (h.hFD₁ hd)).2 hd⟩
  have hC₁s : sp6C₁ φ e z hb = C₁' := by
    obtain ⟨h1, h2, h3, h4, h5⟩ : zpowers b₁ ≤ sp6C₁ φ e z hb ∧ sp6C₁ φ e z hb ≤ D₁ ∧
        Nat.card (sp6C₁ φ e z hb) = 1024 ∧ (∀ x ∈ sp6C₁ φ e z hb, x ^ 2 ∈ zpowers b₁) ∧
        ∀ x ∈ sp6C₁ φ e z hb, ∀ y ∈ sp6C₁ φ e z hb, x⁻¹ * y⁻¹ * x * y ∈ zpowers b₁ :=
      Classical.epsilon_spec (p := fun C : Subgroup G => zpowers b₁ ≤ C ∧ C ≤ D₁ ∧
        Nat.card C = 1024 ∧ (∀ x ∈ C, x ^ 2 ∈ zpowers b₁) ∧
          ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y⁻¹ * x * y ∈ zpowers b₁)
        ⟨C₁', by
          rw [hb₁]
          exact ⟨zpowers_le.2 h.ptB₁_mem_C₁, h.hC₁D, h.hC₁card, fun x hx => h.sq_mem_I₁ hx,
            fun x hx y hy => h.comm_mem_I₁ hx hy⟩⟩
    rw [hb₁] at h1 h4 h5
    exact h.eq_C₁_of_le_D₁ h1 h2 h3 h4 h5
  intro C₁ E₁ Z₁ K₀ U₃ S_H S₁ S₂ P₁ P₂ A B U₁ U₂ N K₁ K₂
  have hC₁ : C₁ = C₁' := hC₁s
  clear_value C₁ F₁ b₁
  subst hC₁ hF₁ hb₁
  obtain ⟨hDF, hDC, hN₁D, -⟩ := h.normalizer_D₁
  refine ⟨hE₂, ⟨zpowers_le.2 h.ptB₁_mem_C₁, h.hC₁D, h.hC₁card, fun x hx => h.sq_mem_I₁ hx,
      fun x hx y hy => h.comm_mem_I₁ hx hy, fun C' h1 h2 h3 h4 h5 =>
        h.eq_C₁_of_le_D₁ h1 h2 h3 h4 h5⟩, hκ,
    ⟨fun d hd => (h.tau_nu hd).symm, fun d hd d' hd' => h.toLagBase.nu_mul h.hinf hd hd',
      fun B => let ⟨c, hc, hcB⟩ := h.hνs B; ⟨c, h.C₂D₂ hc, hcB⟩, fun d hd => ?_, h.hδs, h.hδk,
      fun g c hc => ⟨h.hC₂n _ (leviHom_mem_normalizer_radSub φ he hzC hz g) c hc,
        congrArg Prod.snd (h.toLagBase.kap_levi_conj g (h.C₂D₂ hc))⟩⟩,
    h.characteristic_C₁, fun α x => ?_, h.toLagBase.characteristic_E₂,
    h.toLagBase.characteristic_C₂, h.E₂D₂.trans h.hD₂N,
    isElementaryAbelian_of_forall
      (fun x hx y hy => congrArg Subtype.val (h.hE₂c.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx => (sq x).symm.trans (h.hE₂sq x hx)),
    fun X hX hXe hXc => h.toLagBase.eq_E₂_of_le_N₂ h.hinf hX hXe hXc,
    h.toLagBase.center_C₂ h.hinf, h.hZ₁iso, h.sq_center_C₁,
    by
      change (C₁ : Set G) ∩ (F₁' : Set G) = _
      rw [← Subgroup.coe_inf, h.hE₁],
    fun t ht htZ => let ⟨hF, hiso, hX⟩ := h.F₁_structure ht htZ
      ⟨by rw [hF], hiso, fun X hXF hXe hXc => hX X hXF hXe hXc⟩,
    h.sylow_S_H, h.sylow_S₁, h.sylow_S₂, h.card_S₁, h.card_S₂, h.card_P₁, h.card_P₂, h.card_A,
    h.card_B, h.B_eq_pCore, h.card_S₁_inf_S₂, h.U₁_eq, h.U₂_eq, h.P₁_eq, h.P₂_eq,
    (le_sup_left.trans le_sup_right).trans h.B_le_N, fun m hm p hp => h.conj_mem_P₁ hm hp,
    (le_sup_right.trans le_sup_right).trans h.B_le_N, fun m hm p hp => h.conj_mem_P₂ hm hp,
    le_sup_right.trans h.B_le_N, fun m hm p hp => h.conj_mem_A hm hp, h.S₁_le_N, h.S₂_le_N,
    h.coe_N_eq_S₁K₂, h.coe_N_eq_S₂K₁, h.S₁_inf_K₂, h.S₂_inf_K₁, h.N_inf_N₁_le, h.N_inf_N₂_le,
    h.relIndex_K₁_eq_two, h.relIndex_K₂_eq_two, hDF, hDC, hN₁D, h.relIndex_normalizer_D₁,
    h.exists_T₂⟩
  ·
    constructor
    · intro h0
      have h3 := h.hν₂z d hd
      have h4 : d⁻¹ * z * d = z := by
        rw [h3, show sp6ν₂ φ he z d = 0 from h0]
        exact radHom_z φ he hzC hz
      show d ∈ radSub φ z e
      rw [← h.hD₂H]
      refine mem_inf.2 ⟨hd, mem_centralizer_singleton_iff.2 ?_⟩
      calc d * z = d * (d⁻¹ * z * d) := by rw [h4]
        _ = z * d := by group
    · intro hR
      exact h.toLagBase.nu_eq_zero_of_mem h.hinf hR
  ·
    have h1 := characteristic_iff_map_eq.1 h.characteristic_F₁ α
    constructor
    · intro hx
      have h2 : α x ∈ (F₁'.subgroupOf D₁).map α.toMonoidHom := by
        rw [h1]
        exact hx
      obtain ⟨y, hy, hyx⟩ := h2
      rw [← α.injective hyx]
      exact hy
    · intro hx
      have h2 : α x ∈ (F₁'.subgroupOf D₁).map α.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1] at h2
      exact h2

theorem standard_binary_symplectic_six_epsilon_one_lagrangian_radical_normalizer :
    EpsOneLagrangianNormalizerStmt :=
  epsOneLagrangian_of_point standard_binary_symplectic_six_epsilon_one_point_radical_normalizer

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
