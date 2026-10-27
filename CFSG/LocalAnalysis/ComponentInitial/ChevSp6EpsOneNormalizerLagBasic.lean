module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerStatements

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

structure LagBase (D₂ C₂ E₂ : Subgroup G) (ν₂ : G → ↥(binarySymMatrices 3))
    (σ : 𝒩₂₀ →* GL (Fin 3) (ZMod 2)) : Prop where
  hRc : centralizer (ℛ : Set G) = ℛ
  hσ : ∀ (n : 𝒩₂₀) (a : G) (ha : a ∈ L) (B : M₃), Bᵀ = B →
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1
  hfull : conjClass 𝒩₂ z = z • (𝒜₂ : Set G)
  hD₂N : D₂ ≤ 𝒩₂
  hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂
  hRD₂ : ℛ ≤ D₂
  hD₂card : Nat.card D₂ = 8192
  hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ
  hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c
  hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1))
  hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
    d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
      radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε))
  hE₂c : IsMulCommutative E₂
  hE₂card : Nat.card E₂ = 512
  hE₂sq : ∀ x ∈ E₂, x ^ 2 = 1
  hA₂E₂ : 𝒜₂ ≤ E₂
  hE₂R : E₂ ⊓ ℛ = 𝒜₂
  hC₂ : C₂ = D₂ ⊓ centralizer (E₂ : Set G)
  hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂
  hC₂card : Nat.card C₂ = 4096
  hDzC : (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G)
  hC₂R : C₂ ⊓ ℛ = 𝒜₂
  hEC : E₂ ≤ C₂
  hinv : ∀ c ∈ C₂, c ^ 2 = 1 ↔ c ∈ E₂
  hνs : ∀ B : ↥(binarySymMatrices 3), ∃ c ∈ C₂, ν₂ c = B
  hνk : ∀ c ∈ C₂, ν₂ c = 0 ↔ c ∈ 𝒜₂
  hδs : ∀ w : Fin 3 → ZMod 2, ∃ c ∈ C₂, symThreeDiag (ν₂ c : M₃) = w
  hδk : ∀ c ∈ C₂, symThreeDiag (ν₂ c : M₃) = 0 ↔ c ∈ E₂
  hsq : ∀ c ∈ C₂, c ^ 2 =
    tauHom φ he (Multiplicative.ofAdd (symThreeSquare 1 (symThreeDiag (ν₂ c : M₃))))

structure LagData (D₂ C₂ E₂ : Subgroup G) (ν₂ : G → ↥(binarySymMatrices 3))
    (σ : 𝒩₂₀ →* GL (Fin 3) (ZMod 2)) : Prop extends LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ where
  hgrow : ∃ x ∈ normalizer (D₂ : Set G), x ∉ 𝒩₂

section Basic

variable {he φ hzC hz}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem LagBase.zD₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) : z ∈ D₂ :=
  h.hRD₂ (mem_sup_right (mem_zpowers z))

theorem LagBase.C₂D₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) : C₂ ≤ D₂ := by
  rw [h.hC₂]
  exact inf_le_left

theorem LagBase.E₂D₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) : E₂ ≤ D₂ :=
  h.hEC.trans h.C₂D₂

theorem LagBase.A₂C₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) : 𝒜₂ ≤ C₂ :=
  radA_le_of_inf_eq φ h.hC₂R

include hinf in
theorem LagBase.z_not_mem_C₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) : z ∉ C₂ :=
  z_not_mem_of_inf_eq φ hinf hz h.hC₂R

theorem LagBase.comm_E₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {x c : G} (hx : x ∈ E₂)
    (hc : c ∈ C₂) : x * c = c * x := by
  rw [h.hC₂] at hc
  exact mem_centralizer_iff.1 (mem_inf.1 hc).2 x hx

theorem LagBase.nu_mul (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
    {d d' : G} (hd : d ∈ D₂) (hd' : d' ∈ D₂) : ν₂ (d * d') = ν₂ d + ν₂ d' :=
  Degree64.nu_mul he φ hzC hinf hz h.hν₂z h.hpure hd hd'

theorem LagBase.tau_nu (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {d : G} (hd : d ∈ D₂) :
    tauHom φ he (Multiplicative.ofAdd (ν₂ d)) = z⁻¹ * (d⁻¹ * z * d) :=
  tauHom_nu he φ hzC hz h.hν₂z hd

theorem LagBase.D₂A (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {d a : G} (hd : d ∈ D₂)
    (ha : a ∈ 𝒜₂) : d * a = a * d := by
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
  have h1 := h.hpure d hd (Multiplicative.toAdd B) 0
  rw [zero_smul, add_zero, radHom_tau, ofAdd_toAdd] at h1
  calc d * tauHom φ he B = d * (d⁻¹ * tauHom φ he B * d) := by rw [h1]
    _ = tauHom φ he B * d := by group

theorem LagBase.nu_eq_zero_of_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (hinf : L ⊓ zpowers z = ⊥) {r : G} (hr : r ∈ ℛ) : ν₂ r = 0 := by
  have hrH : r ∈ centralizer ({z} : Set G) := by
    rw [← h.hD₂H] at hr
    exact (mem_inf.1 hr).2
  have hrz : r⁻¹ * z * r = z := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hrH, inv_mul_cancel_left]
  have h2 := (radHom_z φ he hzC hz).trans (hrz.symm.trans (h.hν₂z r (h.hRD₂ hr)))
  exact (congrArg Prod.fst (Multiplicative.ofAdd.injective
    (radHom_injective φ he hzC hz hinf h2))).symm

theorem LagBase.z_conj_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {c : G} (hc : c ∈ C₂) :
    z * c * z⁻¹ ∈ C₂ :=
  h.hC₂n z (le_normalizer (mem_sup_right (mem_zpowers z))) c hc

theorem LagBase.mem_D₂_cases (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {d : G} (hd : d ∈ D₂) :
    d ∈ C₂ ∨ z⁻¹ * d ∈ C₂ := by
  have hd' : d ∈ (zpowers z : Set G) * (C₂ : Set G) := by
    rw [← h.hDzC]
    exact hd
  obtain ⟨t, ht, c, hc, rfl⟩ := hd'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
  have hk : z ^ k = z ^ (k % 2) := by
    rw [← zpow_mod_orderOf z k, hz]
    norm_num
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    change z ^ k * c ∈ C₂
    rw [hk, h0, zpow_zero, one_mul]
    exact hc
  · right
    change z⁻¹ * (z ^ k * c) ∈ C₂
    rw [hk, h1, zpow_one, inv_mul_cancel_left]
    exact hc

theorem LagBase.mul_mem_C₂_iff (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {d d' : G} (hd : d ∈ D₂) (hd' : d' ∈ D₂) :
    d * d' ∈ C₂ ↔ (d ∈ C₂ ↔ d' ∈ C₂) := by
  have hz2 : z * z = 1 := z_mul_self hz
  by_cases hdC : d ∈ C₂
  · refine ⟨fun h2 => ⟨fun _ => ?_, fun _ => hdC⟩, fun h2 => mul_mem hdC (h2.1 hdC)⟩
    have := mul_mem (inv_mem hdC) h2
    rwa [inv_mul_cancel_left] at this
  · have h1 := (h.mem_D₂_cases hd).resolve_left hdC
    by_cases hd'C : d' ∈ C₂
    · refine ⟨fun h3 => absurd ?_ hdC, fun h3 => absurd (h3.2 hd'C) hdC⟩
      have := mul_mem h3 (inv_mem hd'C)
      rwa [mul_inv_cancel_right] at this
    · have h2 := (h.mem_D₂_cases hd').resolve_left hd'C
      have h5 : d * d' = (z * (z⁻¹ * d) * z⁻¹) * (z * z) * (z⁻¹ * d') := by group
      rw [hz2, mul_one] at h5
      refine ⟨fun _ => ⟨fun h6 => absurd h6 hdC, fun h6 => absurd h6 hd'C⟩, fun _ => ?_⟩
      rw [h5]
      exact mul_mem (h.z_conj_mem h1) h2

end Basic

open Classical in
@[expose] def kap (C₂ : Subgroup G) (ν₂ : G → ↥(binarySymMatrices 3)) (d : G) :
    ZMod 2 × (Fin 3 → ZMod 2) :=
  (if d ∈ C₂ then 0 else 1, symThreeDiag (ν₂ d : M₃))

theorem symThreeDiag_add (A B : M₃) : symThreeDiag (A + B) = symThreeDiag A + symThreeDiag B :=
  rfl

section Kap

variable {he φ hzC hz}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem kap_fst_of_mem {d : G} (hd : d ∈ C₂) : (kap C₂ ν₂ d).1 = 0 := by
  classical
  simp [kap, hd]

theorem kap_fst_of_not_mem {d : G} (hd : d ∉ C₂) : (kap C₂ ν₂ d).1 = 1 := by
  classical
  simp [kap, hd]

theorem kap_snd (d : G) : (kap C₂ ν₂ d).2 = symThreeDiag (ν₂ d : M₃) := rfl

theorem kap_fst_eq_zero_iff {d : G} : (kap C₂ ν₂ d).1 = 0 ↔ d ∈ C₂ := by
  by_cases hd : d ∈ C₂
  · exact ⟨fun _ => hd, fun _ => kap_fst_of_mem hd⟩
  · rw [kap_fst_of_not_mem hd]
    exact ⟨fun h => absurd h one_ne_zero, fun h => absurd h hd⟩

theorem LagBase.kap_mul (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
    {d d' : G} (hd : d ∈ D₂) (hd' : d' ∈ D₂) :
    kap C₂ ν₂ (d * d') = kap C₂ ν₂ d + kap C₂ ν₂ d' := by
  refine Prod.ext ?_ ?_
  · have hiff := h.mul_mem_C₂_iff hd hd'
    by_cases h1 : d ∈ C₂ <;> by_cases h2 : d' ∈ C₂
    · rw [Prod.fst_add, kap_fst_of_mem (hiff.2 (iff_of_true h1 h2)), kap_fst_of_mem h1,
        kap_fst_of_mem h2, add_zero]
    · rw [Prod.fst_add, kap_fst_of_not_mem (fun h3 => h2 ((hiff.1 h3).1 h1)), kap_fst_of_mem h1,
        kap_fst_of_not_mem h2, zero_add]
    · rw [Prod.fst_add, kap_fst_of_not_mem (fun h3 => h1 ((hiff.1 h3).2 h2)),
        kap_fst_of_not_mem h1, kap_fst_of_mem h2, add_zero]
    · rw [Prod.fst_add, kap_fst_of_mem (hiff.2 (iff_of_false h1 h2)), kap_fst_of_not_mem h1,
        kap_fst_of_not_mem h2]
      decide
  · rw [Prod.snd_add, kap_snd, kap_snd, kap_snd, h.nu_mul hinf hd hd', AddSubgroup.coe_add,
      symThreeDiag_add]

theorem LagBase.kap_eq_zero_iff (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {d : G} :
    kap C₂ ν₂ d = 0 ↔ d ∈ E₂ := by
  constructor
  · intro h0
    have hdC : d ∈ C₂ := kap_fst_eq_zero_iff.1 (congrArg Prod.fst h0)
    exact (h.hδk d hdC).1 (congrArg Prod.snd h0)
  · intro hdE
    have hdC := h.hEC hdE
    exact Prod.ext (kap_fst_of_mem hdC) ((h.hδk d hdC).2 hdE)

theorem LagBase.kap_zpow_mul (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
    (s : ZMod 2) {c : G} (hc : c ∈ C₂) :
    kap C₂ ν₂ (z ^ s.val * c) = (s, symThreeDiag (ν₂ c : M₃)) := by
  have hzs : z ^ s.val ∈ D₂ := pow_mem h.zD₂ _
  rw [h.kap_mul hinf hzs (h.C₂D₂ hc)]
  have hνz : ν₂ (z ^ s.val) = 0 := h.nu_eq_zero_of_mem hinf (pow_mem (mem_sup_right (mem_zpowers z)) _)
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, kap_fst_of_mem hc, add_zero]
    rcases zmod_two_eq_zero_or_eq_one s with rfl | rfl
    · exact kap_fst_of_mem (by rw [ZMod.val_zero, pow_zero]; exact one_mem _)
    · exact kap_fst_of_not_mem (by rw [ZMod.val_one, pow_one]; exact h.z_not_mem_C₂ hinf)
  · rw [Prod.snd_add, kap_snd, kap_snd, hνz, ZeroMemClass.coe_zero,
      show symThreeDiag (0 : M₃) = 0 from rfl, zero_add]

theorem LagBase.kap_surjective (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (hinf : L ⊓ zpowers z = ⊥)
    (p : ZMod 2 × (Fin 3 → ZMod 2)) : ∃ d ∈ D₂, kap C₂ ν₂ d = p := by
  obtain ⟨c, hc, hcw⟩ := h.hδs p.2
  refine ⟨z ^ p.1.val * c, mul_mem (pow_mem h.zD₂ _) (h.C₂D₂ hc), ?_⟩
  rw [h.kap_zpow_mul hinf p.1 hc, hcw]

end Kap

section Normal

variable {he φ hzC hz}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem LagBase.relIndex_C₂ (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) : C₂.relIndex D₂ = 2 := by
  have h1 := Subgroup.relIndex_mul_card (H := C₂) (K := D₂)
  rw [inf_of_le_left h.C₂D₂, h.hC₂card, h.hD₂card] at h1
  omega

theorem LagBase.eq_E₂_of_le_D₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    {P : Subgroup G} (hPD : P ≤ D₂) (hPsq : ∀ x ∈ P, x ^ 2 = 1) (hPcard : Nat.card P = 512) :
    P = E₂ := by
  by_cases hPC : P ≤ C₂
  · have hPE : P ≤ E₂ := fun x hx => (h.hinv x (hPC hx)).1 (hPsq x hx)
    exact Subgroup.eq_of_le_of_card_ge hPE (by rw [hPcard, h.hE₂card])
  · exfalso
    obtain ⟨p, hpP, hpC⟩ := Set.not_subset.1 hPC
    have hc := (h.mem_D₂_cases (hPD hpP)).resolve_left hpC
    have hle : P ⊓ C₂ ≤ 𝒜₂ := by
      intro q hq
      obtain ⟨hqP, hqC⟩ := mem_inf.1 hq
      have hqE : q ∈ E₂ := (h.hinv q hqC).1 (hPsq q hqP)
      have e1 : p * q = q * p := comm_of_sq_eq_one hPsq hpP hqP
      have e2 : (z⁻¹ * p) * q = q * (z⁻¹ * p) := (h.comm_E₂ hqE hc).symm
      have hqz : z * q = q * z := by
        calc z * q = z * (q * (z⁻¹ * p)) * (z⁻¹ * p)⁻¹ := by group
          _ = z * ((z⁻¹ * p) * q) * (z⁻¹ * p)⁻¹ := by rw [e2]
          _ = p * q * (z⁻¹ * p)⁻¹ := by group
          _ = q * p * (z⁻¹ * p)⁻¹ := by rw [e1]
          _ = q * z := by group
      have hqR : q ∈ ℛ := by
        rw [← h.hD₂H]
        exact mem_inf.2 ⟨h.E₂D₂ hqE, mem_centralizer_singleton_iff.2 hqz.symm⟩
      rw [← h.hE₂R]
      exact mem_inf.2 ⟨hqE, hqR⟩
    have h1 : Nat.card (C₂ ⊓ P : Subgroup G) ≤ 64 := by
      rw [← card_pullSub_radA he φ, inf_comm]
      exact Subgroup.card_le_of_le hle
    have h2 : C₂.relIndex P ≤ 2 := by
      rw [← h.relIndex_C₂]
      exact Subgroup.relIndex_le_of_le_right hPD (by rw [h.relIndex_C₂]; norm_num)
    have h3 := Subgroup.relIndex_mul_card (H := C₂) (K := P)
    rw [hPcard] at h3
    have h4 := Nat.mul_le_mul h2 h1
    omega

theorem LagBase.conj_mem_E₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {x : G}
    (hx : x ∈ normalizer (D₂ : Set G)) {y : G} (hy : y ∈ E₂) : x * y * x⁻¹ ∈ E₂ := by
  set P := E₂.map (MulAut.conj x).toMonoidHom with hP
  have hPD : P ≤ D₂ := by
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.1 hx w).1 (h.E₂D₂ hw)
  have hPsq : ∀ w ∈ P, w ^ 2 = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_pow, h.hE₂sq w hw, map_one]
  have hPcard : Nat.card P = 512 := by
    rw [hP, Subgroup.card_map_of_injective (MulAut.conj x).injective, h.hE₂card]
  have hPE := h.eq_E₂_of_le_D₂ hPD hPsq hPcard
  rw [← hPE]
  exact ⟨y, hy, rfl⟩

theorem LagBase.conj_mem_C₂ [Finite G] (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {x : G}
    (hx : x ∈ normalizer (D₂ : Set G)) {c : G} (hc : c ∈ C₂) : x * c * x⁻¹ ∈ C₂ := by
  have hc' := hc
  rw [h.hC₂] at hc' ⊢
  obtain ⟨hcD, hcE⟩ := mem_inf.1 hc'
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hx c).1 hcD, mem_centralizer_iff.2 fun y hy => ?_⟩
  have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ E₂ := h.conj_mem_E₂ (inv_mem hx) hy
  rw [inv_inv] at hy'
  have e := mem_centralizer_iff.1 hcE _ hy'
  calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [e]
    _ = x * c * x⁻¹ * y := by group

end Normal

section Levi

variable {he φ hzC hz}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}

theorem LagBase.mul_levi_inv_mem (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ)
    (n : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G))) :
    (n : G) * (leviHom φ he (σ n))⁻¹ ∈ ℛ := by
  set g := σ n with hg
  have hnz : (n : G) * z = z * (n : G) :=
    (mem_centralizer_singleton_iff.1 (mem_inf.1 n.2).2)
  have hyA : ∀ M : ↥(binarySymMatrices 3), (n : G) * (leviHom φ he g)⁻¹ *
      tauHom φ he (Multiplicative.ofAdd M) * ((n : G) * (leviHom φ he g)⁻¹)⁻¹ =
        tauHom φ he (Multiplicative.ofAdd M) := by
    intro M
    have h1 := leviHom_conj_tauHom' φ he g⁻¹ M
    rw [map_inv, inv_inv] at h1
    have h2 := conj_tauHom_of_sigma φ he σ h.hσ n (symThreeCongr g⁻¹ M)
    rw [← hg, ← symThreeCongr_mul, mul_inv_cancel, symThreeCongr_one] at h2
    calc (n : G) * (leviHom φ he g)⁻¹ * tauHom φ he (Multiplicative.ofAdd M) *
        ((n : G) * (leviHom φ he g)⁻¹)⁻¹ =
        (n : G) * ((leviHom φ he g)⁻¹ * tauHom φ he (Multiplicative.ofAdd M) *
          leviHom φ he g) * (n : G)⁻¹ := by group
      _ = _ := by rw [h1]; exact h2
  have hyz : (n : G) * (leviHom φ he g)⁻¹ * z = z * ((n : G) * (leviHom φ he g)⁻¹) := by
    have h1 : (leviHom φ he g)⁻¹ * z = z * (leviHom φ he g)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, leviHom_mul_z φ he hzC g, mul_inv_cancel_right]
    rw [mul_assoc, h1, ← mul_assoc, hnz, mul_assoc]
  have hcen : ∀ y : G, (∀ r ∈ ℛ, r * y = y * r) → y ∈ ℛ := fun y hy => by
    rw [← h.hRc]
    exact mem_centralizer_iff.2 hy
  refine hcen _ fun r hr => ?_
  refine mem_centralizer_singleton_iff.1 ((sup_le (fun a ha => ?_) ?_ :
    ℛ ≤ centralizer ({(n : G) * (leviHom φ he g)⁻¹} : Set G)) hr)
  · obtain ⟨M, rfl⟩ := (mem_pullSub_iff φ he).1 ha
    refine mem_centralizer_singleton_iff.2 ?_
    have h1 := hyA (Multiplicative.toAdd M)
    rw [ofAdd_toAdd] at h1
    calc tauHom φ he M * ((n : G) * (leviHom φ he g)⁻¹) =
        ((n : G) * (leviHom φ he g)⁻¹ * tauHom φ he M *
          ((n : G) * (leviHom φ he g)⁻¹)⁻¹) * ((n : G) * (leviHom φ he g)⁻¹) := by
          rw [h1]
      _ = (n : G) * (leviHom φ he g)⁻¹ * tauHom φ he M := by group
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 hyz.symm

theorem LagBase.exists_levi (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) {m : G} (hm : m ∈ 𝒩₂) :
    ∃ d ∈ D₂, ∃ g : GL (Fin 3) (ZMod 2), m = d * leviHom φ he g := by
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₂ m hm
  have h1 := h.mul_levi_inv_mem ⟨c, hc⟩
  refine ⟨d * (c * (leviHom φ he (σ ⟨c, hc⟩))⁻¹), mul_mem hd (h.hRD₂ h1), σ ⟨c, hc⟩, ?_⟩
  group

theorem LagBase.kap_levi_conj (h : LagBase he φ hzC hz D₂ C₂ E₂ ν₂ σ) (g : GL (Fin 3) (ZMod 2))
    {d : G} (hd : d ∈ D₂) :
    kap C₂ ν₂ (leviHom φ he g * d * (leviHom φ he g)⁻¹) =
      ((kap C₂ ν₂ d).1, (g : M₃) *ᵥ (kap C₂ ν₂ d).2) := by
  have hlev := leviHom_mem_normalizer_radSub φ he hzC hz g
  refine Prod.ext ?_ ?_
  · by_cases hdC : d ∈ C₂
    · rw [kap_fst_of_mem hdC, kap_fst_of_mem (h.hC₂n _ hlev d hdC)]
    · rw [kap_fst_of_not_mem hdC, kap_fst_of_not_mem]
      intro h1
      apply hdC
      have h2 := h.hC₂n _ (inv_mem hlev) _ h1
      rwa [inv_inv, show (leviHom φ he g)⁻¹ * (leviHom φ he g * d * (leviHom φ he g)⁻¹) *
        leviHom φ he g = d by group] at h2
  · rw [kap_snd, kap_snd, nu_conj_levi he φ hzC hz h.hν₂z h.hD₂n g hd, coe_symThreeCongr]
    exact symThreeDiag_congr _ _ (ν₂ d).2

end Levi

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
