module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagBasic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e}

variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem LagBase.mem_A₂_iff_central (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {y : G} : (y ∈ D₂ ∧ ∀ d ∈ D₂, y * d = d * y) ↔ y ∈ 𝒜₂ := by
  constructor
  · rintro ⟨hyD, hyc⟩
    have hyR : y ∈ ℛ := by
      rw [← h.hD₂H]
      exact mem_inf.2 ⟨hyD, mem_centralizer_singleton_iff.2 (hyc z h.zD₂)⟩
    obtain ⟨B, ε, rfl⟩ := (mem_radSub_iff φ he hzC hz).1 hyR
    obtain ⟨d, hd, hdC⟩ := h.hνs (jSym 0 1 0)
    have h1 := h.hpure d (h.C₂D₂ hd) B ε
    have h2 : d⁻¹ * (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε) * d =
        tauHom φ he (Multiplicative.ofAdd B) * zPow z ε := by
      rw [mul_assoc, hyc d (h.C₂D₂ hd), inv_mul_cancel_left]
    rw [← radHom_apply φ he hzC hz] at h2
    rw [h2, hdC] at h1
    have h3 := Multiplicative.ofAdd.injective (radHom_injective φ he hzC hz hinf h1)
    have h4 := congrArg (fun p => ((p.1 : ↥(binarySymMatrices 3)) : M₃) 0 1) h3
    simp only at h4
    have hε : ε = 0 := by
      change (B : M₃) 0 1 = (B : M₃) 0 1 + ε * 1 at h4
      rw [mul_one] at h4
      exact (add_eq_left.1 h4.symm)
    subst hε
    rw [← radHom_apply φ he hzC hz, radHom_tau]
    exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  · intro hy
    exact ⟨h.hRD₂ (mem_sup_left hy), fun d hd => (h.D₂A hd hy).symm⟩

theorem LagBase.conj_mem_A₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {x : G} (hx : x ∈ normalizer (D₂ : Set G)) {a : G}
    (ha : a ∈ 𝒜₂) : x * a * x⁻¹ ∈ 𝒜₂ := by
  obtain ⟨haD, hac⟩ := (h.mem_A₂_iff_central hinf).2 ha
  refine (h.mem_A₂_iff_central hinf).1 ⟨(mem_normalizer_iff.1 hx a).1 haD, fun d hd => ?_⟩
  have hd' : x⁻¹ * d * x⁻¹⁻¹ ∈ D₂ := (mem_normalizer_iff.1 (inv_mem hx) d).1 hd
  rw [inv_inv] at hd'
  have e1 := hac _ hd'
  calc x * a * x⁻¹ * d = x * (a * (x⁻¹ * d * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * d * x) * a) * x⁻¹ := by rw [e1]
    _ = d * (x * a * x⁻¹) := by group

theorem LagBase.mem_N₂_of_conj_z [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {x : G} (hx : x ∈ normalizer (D₂ : Set G))
    (hxz : z⁻¹ * (x * z * x⁻¹) ∈ E₂) : x ∈ 𝒩₂ := by
  set e₀ := z⁻¹ * (x * z * x⁻¹) with he₀
  have hz2 : z * z = 1 := z_mul_self hz
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hxzx : x * z * x⁻¹ = z * e₀ := by rw [he₀, mul_inv_cancel_left]
  have hsq : (z * e₀) * (z * e₀) = 1 := by
    rw [← hxzx]
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact h.hE₂sq e₀ hxz
  have he₀z : e₀ * z = z * e₀ := by
    have h1 : z * e₀ * z = e₀ := by
      calc z * e₀ * z = z * e₀ * z * (e₀ * e₀) := by rw [he₀2, mul_one]
        _ = (z * e₀ * (z * e₀)) * e₀ := by group
        _ = e₀ := by rw [hsq, one_mul]
    calc e₀ * z = z * e₀ * z * z := by rw [h1]
      _ = z * e₀ := by rw [mul_assoc, hz2, mul_one]
  have he₀A : e₀ ∈ 𝒜₂ := by
    rw [← h.hE₂R]
    refine mem_inf.2 ⟨hxz, ?_⟩
    rw [← h.hD₂H]
    exact mem_inf.2 ⟨h.E₂D₂ hxz, mem_centralizer_singleton_iff.2 he₀z⟩
  refine mem_normalizer_of_conj_mem fun r hr => ?_
  obtain ⟨B, ε, rfl⟩ := (mem_radSub_iff φ he hzC hz).1 hr
  have hτ : tauHom φ he (Multiplicative.ofAdd B) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have h1 := h.conj_mem_A₂ hinf hx hτ
  have hzε : x * zPow z ε * x⁻¹ = (z * e₀) ^ ε.val := by
    rw [zPow, ← hxzx, conj_pow]
  have h2 : x * (tauHom φ he (Multiplicative.ofAdd B) * zPow z ε) * x⁻¹ =
      (x * tauHom φ he (Multiplicative.ofAdd B) * x⁻¹) * (x * zPow z ε * x⁻¹) := by group
  rw [h2, hzε]
  exact mul_mem (mem_sup_left h1) (pow_mem (mul_mem (mem_sup_right (mem_zpowers z))
    (mem_sup_left he₀A)) _)

theorem LagBase.kap_inv (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
    {d : G} (hd : d ∈ D₂) : kap C₂ ν₂ d⁻¹ = kap C₂ ν₂ d := by
  have h1 := h.kap_mul hinf (inv_mem hd) hd
  rw [inv_mul_cancel, (h.kap_eq_zero_iff).2 (one_mem _)] at h1
  have h2 : ∀ p : ZMod 2 × (Fin 3 → ZMod 2), p + p = 0 := fun p =>
    Prod.ext (ZModModule.add_self p.1) (funext fun i => ZModModule.add_self (p.2 i))
  calc kap C₂ ν₂ d⁻¹ = kap C₂ ν₂ d⁻¹ + (kap C₂ ν₂ d⁻¹ + kap C₂ ν₂ d) := by rw [← h1, add_zero]
    _ = kap C₂ ν₂ d := by rw [← add_assoc, h2, zero_add]

theorem LagBase.kap_eq_kap_iff (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {d d' : G} (hd : d ∈ D₂) (hd' : d' ∈ D₂) :
    kap C₂ ν₂ d = kap C₂ ν₂ d' ↔ d⁻¹ * d' ∈ E₂ := by
  rw [← h.kap_eq_zero_iff, h.kap_mul hinf (inv_mem hd) hd', h.kap_inv hinf hd]
  have h2 : ∀ p q : ZMod 2 × (Fin 3 → ZMod 2), p + q = 0 ↔ p = q := fun p q => by
    constructor
    · intro hpq
      have : p = -q := eq_neg_of_add_eq_zero_left hpq
      rw [this]
      exact Prod.ext (ZModModule.neg_eq_self q.1) (funext fun i => ZModModule.neg_eq_self (q.2 i))
    · rintro rfl
      exact Prod.ext (ZModModule.add_self p.1) (funext fun i => ZModModule.add_self (p.2 i))
  rw [h2]

@[expose] def actFun (ν₂ : G → ↥(binarySymMatrices 3)) (sec : (Fin 3 → ZMod 2) → G) (x : G)
    (w : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  symThreeDiag (ν₂ (x * sec w * x⁻¹) : M₃)

@[expose] def actMat (ν₂ : G → ↥(binarySymMatrices 3)) (sec : (Fin 3 → ZMod 2) → G) (x : G) :
    M₃ :=
  Matrix.of fun i j => actFun ν₂ sec x (Pi.single j 1) i

@[expose] def actVec (ν₂ : G → ↥(binarySymMatrices 3)) (z x : G) : Fin 3 → ZMod 2 :=
  symThreeDiag (ν₂ (x * z * x⁻¹) : M₃)

theorem matrix_ext_mulVec {A B : M₃} (hAB : ∀ w, A *ᵥ w = B *ᵥ w) : A = B := by
  ext i j
  have h1 := congrFun (hAB (Pi.single j 1)) i
  rwa [mulVec_single_one, mulVec_single_one] at h1

section Act

variable [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
  {sec : (Fin 3 → ZMod 2) → G}
  (hsec : ∀ w, sec w ∈ C₂ ∧ symThreeDiag (ν₂ (sec w) : M₃) = w)

include h hinf hsec

theorem LagBase.delta_conj {x : G} (hx : x ∈ normalizer (D₂ : Set G)) {c : G} (hc : c ∈ C₂) :
    symThreeDiag (ν₂ (x * c * x⁻¹) : M₃) = actFun ν₂ sec x (symThreeDiag (ν₂ c : M₃)) := by
  obtain ⟨hsC, hsw⟩ := hsec (symThreeDiag (ν₂ c : M₃))
  have hkap : kap C₂ ν₂ c = kap C₂ ν₂ (sec (symThreeDiag (ν₂ c : M₃))) :=
    Prod.ext (by rw [kap_fst_of_mem hc, kap_fst_of_mem hsC]) (by rw [kap_snd, kap_snd, hsw])
  have hE := (h.kap_eq_kap_iff hinf (h.C₂D₂ hc) (h.C₂D₂ hsC)).1 hkap
  have hE' := h.conj_mem_E₂ hx hE
  have hxc : x * c * x⁻¹ ∈ D₂ := (mem_normalizer_iff.1 hx c).1 (h.C₂D₂ hc)
  have hxs : x * sec (symThreeDiag (ν₂ c : M₃)) * x⁻¹ ∈ D₂ :=
    (mem_normalizer_iff.1 hx _).1 (h.C₂D₂ hsC)
  have h1 := (h.kap_eq_kap_iff hinf hxc hxs).2 (by
    rw [show (x * c * x⁻¹)⁻¹ * (x * sec (symThreeDiag (ν₂ c : M₃)) * x⁻¹) =
      x * (c⁻¹ * sec (symThreeDiag (ν₂ c : M₃))) * x⁻¹ by group]
    exact hE')
  exact congrArg Prod.snd h1

theorem LagBase.actFun_add {x : G} (hx : x ∈ normalizer (D₂ : Set G)) (w w' : Fin 3 → ZMod 2) :
    actFun ν₂ sec x (w + w') = actFun ν₂ sec x w + actFun ν₂ sec x w' := by
  obtain ⟨h1C, h1w⟩ := hsec w
  obtain ⟨h2C, h2w⟩ := hsec w'
  have hmul : sec w * sec w' ∈ C₂ := mul_mem h1C h2C
  have hδ : symThreeDiag (ν₂ (sec w * sec w') : M₃) = w + w' := by
    rw [h.nu_mul hinf (h.C₂D₂ h1C) (h.C₂D₂ h2C), AddSubgroup.coe_add, symThreeDiag_add, h1w, h2w]
  have e1 := h.delta_conj hinf hsec hx hmul
  rw [hδ] at e1
  rw [← e1, show x * (sec w * sec w') * x⁻¹ = (x * sec w * x⁻¹) * (x * sec w' * x⁻¹) by group,
    h.nu_mul hinf ((mem_normalizer_iff.1 hx _).1 (h.C₂D₂ h1C))
      ((mem_normalizer_iff.1 hx _).1 (h.C₂D₂ h2C)), AddSubgroup.coe_add, symThreeDiag_add]
  rfl

theorem LagBase.actFun_eq_mulVec {x : G} (hx : x ∈ normalizer (D₂ : Set G))
    (w : Fin 3 → ZMod 2) : actFun ν₂ sec x w = actMat ν₂ sec x *ᵥ w := by
  let F : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := actFun ν₂ sec x
      map_zero' := by
        have h0 := h.actFun_add hinf hsec hx 0 0
        rw [add_zero] at h0
        exact (add_eq_left.1 h0.symm)
      map_add' := h.actFun_add hinf hsec hx }
  have hM : actMat ν₂ sec x = LinearMap.toMatrix' (F.toZModLinearMap 2) := by
    ext i j
    rfl
  rw [hM, LinearMap.toMatrix'_mulVec]
  rfl

omit [Finite G] hsec in
theorem LagBase.kap_z : kap C₂ ν₂ z = (1, 0) := by
  have h1 := h.kap_zpow_mul hinf 1 (one_mem C₂)
  rw [ZMod.val_one, pow_one, mul_one, h.nu_eq_zero_of_mem hinf (one_mem _)] at h1
  rw [h1]
  rfl

theorem LagBase.kap_conj {x : G} (hx : x ∈ normalizer (D₂ : Set G)) {d : G} (hd : d ∈ D₂) :
    kap C₂ ν₂ (x * d * x⁻¹) = ((kap C₂ ν₂ d).1,
      actMat ν₂ sec x *ᵥ (kap C₂ ν₂ d).2 + (kap C₂ ν₂ d).1 • actVec ν₂ z x) := by
  by_cases hdC : d ∈ C₂
  · refine Prod.ext ?_ ?_
    · rw [kap_fst_of_mem hdC, kap_fst_of_mem (h.conj_mem_C₂ hx hdC)]
    · rw [kap_snd, kap_snd, kap_fst_of_mem hdC, zero_smul, add_zero,
        h.delta_conj hinf hsec hx hdC, h.actFun_eq_mulVec hinf hsec hx]
  · have hc : z⁻¹ * d ∈ C₂ := (h.mem_D₂_cases hd).resolve_left hdC
    have hxd : x * d * x⁻¹ ∉ C₂ := fun h1 => by
      have h2 := h.conj_mem_C₂ (inv_mem hx) h1
      rw [inv_inv, show x⁻¹ * (x * d * x⁻¹) * x = d by group] at h2
      exact hdC h2
    have hδd : symThreeDiag (ν₂ d : M₃) = symThreeDiag (ν₂ (z⁻¹ * d) : M₃) := by
      have e1 : d = z * (z⁻¹ * d) := by group
      conv_lhs => rw [e1]
      rw [h.nu_mul hinf h.zD₂ (h.C₂D₂ hc), h.nu_eq_zero_of_mem hinf (mem_sup_right
        (mem_zpowers z)), zero_add]
    refine Prod.ext ?_ ?_
    · rw [kap_fst_of_not_mem hdC, kap_fst_of_not_mem hxd]
    · rw [kap_snd, kap_snd, kap_fst_of_not_mem hdC, one_smul,
        show x * d * x⁻¹ = (x * z * x⁻¹) * (x * (z⁻¹ * d) * x⁻¹) by group,
        h.nu_mul hinf ((mem_normalizer_iff.1 hx z).1 h.zD₂)
          ((mem_normalizer_iff.1 hx _).1 (h.C₂D₂ hc)), AddSubgroup.coe_add, symThreeDiag_add,
        h.delta_conj hinf hsec hx hc, h.actFun_eq_mulVec hinf hsec hx, ← hδd, add_comm]
      rfl

omit [Finite G] h hinf in
theorem actMat_one : actMat ν₂ sec 1 = 1 := by
  ext i j
  change symThreeDiag (ν₂ (1 * sec (Pi.single j 1) * 1⁻¹) : M₃) i = (1 : M₃) i j
  rw [one_mul, inv_one, mul_one, (hsec _).2, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem LagBase.actMat_mul {x y : G} (hx : x ∈ normalizer (D₂ : Set G))
    (hy : y ∈ normalizer (D₂ : Set G)) :
    actMat ν₂ sec (x * y) = actMat ν₂ sec x * actMat ν₂ sec y := by
  refine matrix_ext_mulVec fun w => ?_
  obtain ⟨hsC, hsw⟩ := hsec w
  rw [← mulVec_mulVec, ← h.actFun_eq_mulVec hinf hsec (mul_mem hx hy),
    ← h.actFun_eq_mulVec hinf hsec hy, ← h.actFun_eq_mulVec hinf hsec hx]
  have h1 := h.delta_conj hinf hsec hy hsC
  rw [hsw] at h1
  rw [← h1, ← h.delta_conj hinf hsec hx (h.conj_mem_C₂ hy hsC)]
  change symThreeDiag (ν₂ (x * y * sec w * (x * y)⁻¹) : M₃) = _
  rw [show x * y * sec w * (x * y)⁻¹ = x * (y * sec w * y⁻¹) * x⁻¹ by group]

theorem LagBase.actVec_mul {x y : G} (hx : x ∈ normalizer (D₂ : Set G))
    (hy : y ∈ normalizer (D₂ : Set G)) :
    actVec ν₂ z (x * y) = actVec ν₂ z x + actMat ν₂ sec x *ᵥ actVec ν₂ z y := by
  have hyz : y * z * y⁻¹ ∈ D₂ := (mem_normalizer_iff.1 hy z).1 h.zD₂
  have h1 := h.kap_conj hinf hsec hy h.zD₂
  rw [h.kap_z hinf] at h1
  have h2 := h.kap_conj hinf hsec hx hyz
  rw [h1] at h2
  have h3 := congrArg Prod.snd h2
  simp only [one_smul, mulVec_zero, zero_add] at h3
  rw [kap_snd, show x * (y * z * y⁻¹) * x⁻¹ = x * y * z * (x * y)⁻¹ by group] at h3
  change actVec ν₂ z (x * y) = _ at h3 ⊢
  rw [h3, add_comm]

omit [Finite G] hsec in
theorem LagBase.kap_conj_of_mem {x d : G} (hx : x ∈ D₂) (hd : d ∈ D₂) :
    kap C₂ ν₂ (x * d * x⁻¹) = kap C₂ ν₂ d := by
  rw [h.kap_mul hinf (mul_mem hx hd) (inv_mem hx), h.kap_mul hinf hx hd, h.kap_inv hinf hx,
    add_comm (kap C₂ ν₂ x), add_assoc]
  have h2 : kap C₂ ν₂ x + kap C₂ ν₂ x = 0 :=
    Prod.ext (ZModModule.add_self _) (funext fun i => ZModModule.add_self _)
  rw [h2, add_zero]

@[expose] def matHom : normalizer (D₂ : Set G) →* M₃ where
  toFun x := actMat ν₂ sec x
  map_one' := actMat_one hsec
  map_mul' x y := h.actMat_mul hinf hsec x.2 y.2

@[expose] def psiHom : normalizer (D₂ : Set G) →* AGL32 where
  toFun x := ⟨Multiplicative.ofAdd (actVec ν₂ z x), (matHom h hinf hsec).toHomUnits x⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ (map_one _)
    change Multiplicative.ofAdd (symThreeDiag (ν₂ (1 * z * 1⁻¹) : M₃)) = 1
    rw [one_mul, inv_one, mul_one, h.nu_eq_zero_of_mem hinf (mem_sup_right (mem_zpowers z))]
    rfl
  map_mul' x y := by
    refine SemidirectProduct.ext ?_ (map_mul _ x y)
    rw [SemidirectProduct.mul_left]
    change Multiplicative.ofAdd (actVec ν₂ z ((x : G) * y)) =
      Multiplicative.ofAdd (actVec ν₂ z x) *
        Multiplicative.ofAdd (actMat ν₂ sec x *ᵥ actVec ν₂ z y)
    rw [h.actVec_mul hinf hsec x.2 y.2, ofAdd_add]

theorem psiHom_left (x : normalizer (D₂ : Set G)) :
    (psiHom h hinf hsec x).left = Multiplicative.ofAdd (actVec ν₂ z x) :=
  rfl

theorem psiHom_right (x : normalizer (D₂ : Set G)) :
    ((psiHom h hinf hsec x).right : M₃) = actMat ν₂ sec x :=
  rfl

theorem kap_conj_psiHom (x : normalizer (D₂ : Set G)) {d : G} (hd : d ∈ D₂) :
    kap C₂ ν₂ ((x : G) * d * (x : G)⁻¹) = aglLin (psiHom h hinf hsec x) (kap C₂ ν₂ d) := by
  rw [h.kap_conj hinf hsec x.2 hd]
  rfl

theorem LagBase.mem_N₂_iff {x : G} (hx : x ∈ normalizer (D₂ : Set G)) :
    x ∈ 𝒩₂ ↔ actVec ν₂ z x = 0 := by
  constructor
  · intro hxN
    have h1 : x * z * x⁻¹ ∈ conjClass 𝒩₂ z := ⟨x, hxN, rfl⟩
    rw [h.hfull] at h1
    obtain ⟨a, ha, ha'⟩ := h1
    change z * a = x * z * x⁻¹ at ha'
    change symThreeDiag (ν₂ (x * z * x⁻¹) : M₃) = 0
    rw [← ha', h.nu_mul hinf h.zD₂ (h.C₂D₂ (h.A₂C₂ ha)),
      h.nu_eq_zero_of_mem hinf (mem_sup_right (mem_zpowers z)), zero_add]
    exact (h.hδk a (h.A₂C₂ ha)).2 (h.hA₂E₂ ha)
  · intro hv
    refine h.mem_N₂_of_conj_z hinf hx ?_
    have hxz : x * z * x⁻¹ ∈ D₂ := (mem_normalizer_iff.1 hx z).1 h.zD₂
    have h1 := h.kap_conj hinf hsec hx h.zD₂
    rw [h.kap_z hinf, hv, smul_zero, add_zero, mulVec_zero] at h1
    exact (h.kap_eq_kap_iff hinf h.zD₂ hxz).1 ((h1.trans (h.kap_z hinf).symm).symm)

omit hinf hsec in
theorem LagBase.N₂_le_Q₂ : 𝒩₂ ≤ normalizer (D₂ : Set G) := fun m hm =>
  mem_normalizer_of_conj_mem fun d hd => h.hD₂n m hm d hd

theorem psiHom_levi (g : GL (Fin 3) (ZMod 2)) (hg : leviHom φ he g ∈ normalizer (D₂ : Set G)) :
    psiHom h hinf hsec ⟨_, hg⟩ = SemidirectProduct.inr g := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [psiHom_left, SemidirectProduct.left_inr]
    change Multiplicative.ofAdd
      (symThreeDiag (ν₂ (leviHom φ he g * z * (leviHom φ he g)⁻¹) : M₃)) = 1
    rw [leviHom_mul_z φ he hzC g, mul_inv_cancel_right,
      h.nu_eq_zero_of_mem hinf (mem_sup_right (mem_zpowers z))]
    rfl
  · refine Units.ext (matrix_ext_mulVec fun w => ?_)
    rw [psiHom_right, SemidirectProduct.right_inr]
    change actMat ν₂ sec (leviHom φ he g) *ᵥ w = (g : M₃) *ᵥ w
    rw [← h.actFun_eq_mulVec hinf hsec hg]
    obtain ⟨hsC, hsw⟩ := hsec w
    have h2 := congrArg Prod.snd (h.kap_levi_conj g (h.C₂D₂ hsC))
    rw [kap_snd, kap_snd, hsw] at h2
    exact h2

theorem psiHom_of_mem (x : normalizer (D₂ : Set G)) (hx : (x : G) ∈ D₂) :
    psiHom h hinf hsec x = 1 := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [psiHom_left, SemidirectProduct.one_left]
    have h1 := congrArg Prod.snd (h.kap_conj_of_mem hinf hx h.zD₂)
    rw [kap_snd, h.kap_z hinf] at h1
    change Multiplicative.ofAdd (symThreeDiag (ν₂ ((x : G) * z * (x : G)⁻¹) : M₃)) = 1
    rw [h1]
    rfl
  · refine Units.ext (matrix_ext_mulVec fun w => ?_)
    rw [psiHom_right, SemidirectProduct.one_right, Units.val_one, one_mulVec,
      ← h.actFun_eq_mulVec hinf hsec x.2]
    obtain ⟨hsC, hsw⟩ := hsec w
    have h1 := congrArg Prod.snd (h.kap_conj_of_mem hinf hx (h.C₂D₂ hsC))
    rw [kap_snd, kap_snd, hsw] at h1
    exact h1

theorem psiHom_eq_one_iff (x : normalizer (D₂ : Set G)) :
    psiHom h hinf hsec x = 1 ↔ (x : G) ∈ D₂ := by
  refine ⟨fun h1 => ?_, psiHom_of_mem h hinf hsec x⟩
  have hv : actVec ν₂ z x = 0 := by
    have h2 := congrArg (fun p : AGL32 => Multiplicative.toAdd p.left) h1
    exact h2
  have hxN := (h.mem_N₂_iff hinf hsec x.2).2 hv
  obtain ⟨d, hd, g, hdg⟩ := h.exists_levi hxN
  have hdQ : d ∈ normalizer (D₂ : Set G) := le_normalizer hd
  have hgQ : leviHom φ he g ∈ normalizer (D₂ : Set G) :=
    h.N₂_le_Q₂ (leviHom_mem_normalizer_radSub φ he hzC hz g)
  have h2 : psiHom h hinf hsec x =
      psiHom h hinf hsec ⟨d, hdQ⟩ * psiHom h hinf hsec ⟨_, hgQ⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hdg
  rw [psiHom_of_mem h hinf hsec ⟨d, hdQ⟩ hd, one_mul, psiHom_levi h hinf hsec g hgQ, h1] at h2
  have hg1 : g = 1 := (SemidirectProduct.inr_injective (h2.symm.trans
    (map_one SemidirectProduct.inr).symm))
  rw [hdg, hg1, map_one, mul_one]
  exact hd

theorem ker_psiHom : (psiHom h hinf hsec).ker = D₂.subgroupOf (normalizer (D₂ : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, mem_subgroupOf, psiHom_eq_one_iff]

end Act

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
