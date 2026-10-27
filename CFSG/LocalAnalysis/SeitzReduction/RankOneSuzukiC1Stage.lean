module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiUSylow

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

structure SzC1Stage (G : Type) [Group G] [Finite G] (L : Subgroup G) (f a : ℕ) (t : G)
    (T : Subgroup G) (d : G) (V U U₁ : Subgroup G) (k : ℕ) : Prop where
  start : SzStart G L f t T
  hfa : f = 2 * a + 1
  ha : 1 ≤ a
  coords : ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2) (u v : G → K) (κ : K),
    Fintype.card K = 2 ^ f ∧ SzRootCoords (szT₁ L T) a d u v κ ∧
      ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w
  d_mem_L : d ∈ L
  d_odd : Odd (orderOf d)
  le_centralizer : V ≤ centralizer (szT₁ L T : Set G)
  comm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x
  card : Nat.card V = (2 ^ f) ^ (k + 1)
  omega : ∀ x ∈ V, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)
  pow : ∀ x ∈ V, x ^ 2 ^ (k + 1) = 1
  le : szA₁ (szT₁ L T) ≤ V
  inv : ∀ x ∈ V, t * x * t⁻¹ = x⁻¹
  d_norm : d ∈ normalizer (V : Set G) ⊓ normalizer (szT₁ L T : Set G) ⊓ centralizer ({t} : Set G)
  U_le : U ≤ normalizer (szR (szT₁ L T) V t : Set G)
  U_normal : normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (U : Set G)
  isSylowOf : IsSylowOf 2 U (normalizer (szR (szT₁ L T) V t : Set G))
  card_U : Nat.card U = 2 * (2 ^ f) ^ (k + 3)
  szR_le : szR (szT₁ L T) V t ≤ U
  conj_t_not_mem : ∀ u ∈ U, u ∉ szR (szT₁ L T) V t → u * t * u⁻¹ ∉ szA L T t
  conj_szA₁ : ∀ u ∈ U, ∀ b ∈ szA₁ (szT₁ L T), u * b * u⁻¹ = b
  conj_T₁ : ∀ u ∈ U, ∀ y ∈ szT₁ L T, y⁻¹ * (u * y * u⁻¹) ∈ szA₁ (szT₁ L T)
  conj_V₁ : ∀ u ∈ U₁, ∀ r ∈ V, r⁻¹ * (u * r * u⁻¹) ∈ szA₁ (szT₁ L T)
  inf_centralizer : U ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t
  U₁_le : U₁ ≤ U
  U₁_normal : U ≤ normalizer (U₁ : Set G)
  sup_eq : U₁ ⊔ zpowers t = U
  t_not_mem : t ∉ U₁
  inf_eq : U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V
  d_mem_U₁ : d ∈ normalizer (U₁ : Set G)

namespace SzC1

variable {G : Type} [Group G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ U U₁ : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K}

theorem comm_eq_sq_of_inv {r : G} (h : t * r * t⁻¹ = r⁻¹) : r * t * r⁻¹ * t⁻¹ = r ^ 2 := by
  have h1 : t * r⁻¹ * t⁻¹ = r := by
    rw [show t * r⁻¹ * t⁻¹ = (t * r * t⁻¹)⁻¹ by group, h, inv_inv]
  calc r * t * r⁻¹ * t⁻¹ = r * (t * r⁻¹ * t⁻¹) := by group
    _ = r ^ 2 := by rw [h1, sq]

theorem mem_szA₁_of_sq_eq_one (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {y : G} (hy : y ∈ T₁) (h : y ^ 2 = 1) :
    y ∈ szA₁ T₁ := by
  refine (hc.mem_szA₁_iff ha hK hy).mpr ?_
  have e := (hc.sq hy).2
  rw [h, hc.v_one] at e
  exact pow_eq_zero_iff (Nat.succ_ne_zero _) |>.mp e.symm

theorem sq_mul_mul_t (hS : SzR2 T₁ R₂ t d) (hTR : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {y r : G} (hy : y ∈ T₁) (hr : r ∈ R₂) :
    (y * r * t) ^ 2 = y ^ 2 := by
  have e1 : t * y = y * t := (hS.t_comm y hy).symm
  have e2 : t * r = r⁻¹ * t := by
    calc t * r = (t * r * t⁻¹) * t := by group
      _ = r⁻¹ * t := by rw [hinv r hr]
  have e3 : r * y = y * r := (hTR y hy r hr).symm
  have htt : t * t = 1 := by rw [← sq]; exact hS.t_sq
  calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
    _ = y * (r * y) * (t * r) * t := by rw [e1]; group
    _ = y * (y * r) * (r⁻¹ * t) * t := by rw [e3, e2]
    _ = y * y * (t * t) := by group
    _ = y ^ 2 := by rw [htt, mul_one, sq]

theorem conj_t_mem_mul (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hTR : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {q : ℕ} (hU : SzU T₁ R₂ t d q U U₁) {x : G}
    (hx : x ∈ U) : ∃ σ ∈ R₂, x * t * x⁻¹ = σ * t := by
  have ht' : x * t * x⁻¹ ∈ szR T₁ R₂ t :=
    (mem_normalizer_iff.mp (hU.le_normalizer hx) t).mp (mem_szR_right T₁ R₂ t)
  have hle : T₁ ⊔ R₂ ≤ U₁ := hU.inf_eq ▸ inf_le_left
  have hnot : x * t * x⁻¹ ∉ T₁ ⊔ R₂ := fun h =>
    hU.t_not_mem ((mem_normalizer_iff.mp (hU.le_normalizer_U₁ hx) t).mpr (hle h))
  obtain ⟨y, hy, r, hr, h1 | h1⟩ := hS.exists_decomp ht'
  · exact absurd (h1 ▸ mul_mem (mem_sup_left hy) (mem_sup_right hr)) hnot
  · have hsq : (x * t * x⁻¹) ^ 2 = 1 := by
      rw [sq, show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, ← sq, hS.t_sq,
        mul_one, mul_inv_cancel]
    rw [h1, sq_mul_mul_t hS hTR hinv hy hr] at hsq
    exact ⟨y * r, mul_mem (hS.le_R₂ (mem_szA₁_of_sq_eq_one hc ha hK hy hsq)) hr, h1⟩

theorem conj_T₁ (hS : SzR2 T₁ R₂ t d) (hc : SzRootCoords T₁ a d u v κ) (ha : 1 ≤ a)
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) (hTR : ∀ x ∈ T₁, ∀ r ∈ R₂, x * r = r * x)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {q : ℕ} (hU : SzU T₁ R₂ t d q U U₁) {x : G}
    (hx : x ∈ U) {y : G} (hy : y ∈ T₁) : y⁻¹ * (x * y * x⁻¹) ∈ szA₁ T₁ := by
  obtain ⟨σ, hσ, hxt⟩ := conj_t_mem_mul hS hc ha hK hTR hinv hU hx
  set r := y⁻¹ * (x * y * x⁻¹) with hrdef
  have hr : r ∈ R₂ := hU.conj_sup x hx y (mem_sup_left hy)
  have hz : x * y * x⁻¹ = y * r := by rw [hrdef]; group
  have hcomm : (x * y * x⁻¹) * (x * t * x⁻¹) = (x * t * x⁻¹) * (x * y * x⁻¹) := by
    calc (x * y * x⁻¹) * (x * t * x⁻¹) = x * (y * t) * x⁻¹ := by group
      _ = x * (t * y) * x⁻¹ := by rw [hS.t_comm y hy]
      _ = (x * t * x⁻¹) * (x * y * x⁻¹) := by group
  rw [hz, hxt] at hcomm
  have e1 : t * y = y * t := (hS.t_comm y hy).symm
  have e2 : t * r = r⁻¹ * t := by
    calc t * r = (t * r * t⁻¹) * t := by group
      _ = r⁻¹ * t := by rw [hinv r hr]
  have hyσ : y * σ = σ * y := hTR y hy σ hσ
  have hrσ : r * σ = σ * r := hS.R₂_comm r hr σ hσ
  have h3 : σ * y * r * t = σ * y * r⁻¹ * t := by
    calc σ * y * r * t = y * σ * r * t := by rw [← hyσ]
      _ = y * (σ * r) * t := by group
      _ = y * (r * σ) * t := by rw [hrσ]
      _ = y * r * (σ * t) := by group
      _ = σ * t * (y * r) := hcomm
      _ = σ * (t * y) * r := by group
      _ = σ * (y * t) * r := by rw [e1]
      _ = σ * y * (t * r) := by group
      _ = σ * y * (r⁻¹ * t) := by rw [e2]
      _ = σ * y * r⁻¹ * t := by group
  have hrr : r = r⁻¹ := mul_left_cancel (mul_right_cancel h3)
  have hr2 : r ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hrr]
    exact mul_inv_cancel r
  exact hS.rho_ker r hr (by rw [comm_eq_sq_of_inv (hinv r hr), hr2])

end SzC1

theorem SzC1Stage.of_data {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} {a : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2] {d : G}
    {u v : G → K} {κ : K} {R₂ U U₁ : Subgroup G} (h : SzStart G L f t T) (ha : 1 ≤ a)
    (hfa : f = 2 * a + 1) (hK : Fintype.card K = 2 ^ f) (hdL : d ∈ L) (hdodd : Odd (orderOf d))
    (hc : SzRootCoords (szT₁ L T) a d u v κ) (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hR : SzR2 (szT₁ L T) R₂ t d) (hTR : ∀ x ∈ szT₁ L T, ∀ r ∈ R₂, x * r = r * x)
    (hU : SzU (szT₁ L T) R₂ t d (2 ^ f) U U₁) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    SzC1Stage G L f a t T d R₂ U U₁ 1 := by
  have hK' : Fintype.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have hcardK : Nat.card K = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card, hK']
  have hμ := pow_theta_succ_generator_of_generator ha hcardK hκ
  obtain ⟨φ, γ, c, hcoords⟩ := hR.exists_coords hc ha hK' hμ
  have hsq : ∀ r ∈ R₂, r ^ 2 ∈ szA₁ (szT₁ L T) := fun r hr => by
    rw [← SzC1.comm_eq_sq_of_inv (hinv r hr)]
    exact hR.rho_mem r hr
  refine
    { start := h
      hfa := hfa
      ha := ha
      coords := ⟨K, inferInstance, inferInstance, inferInstance, u, v, κ, hK, hc, hκ⟩
      d_mem_L := hdL
      d_odd := hdodd
      le_centralizer := fun r hr => mem_centralizer_iff.mpr fun x hx => hTR x hx r hr
      comm := hR.R₂_comm
      card := ?_
      omega := fun r hr hr2 => hR.rho_ker r hr (by rw [SzC1.comm_eq_sq_of_inv (hinv r hr), hr2])
      pow := fun r hr => by
        rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul]
        exact hc.sq_eq_one_of_mem_szA₁ ha hK' (hsq r hr)
      le := hR.le_R₂
      inv := hinv
      d_norm := ⟨⟨hR.d_mem, mem_normalizer_of_forall_inv_mul_mul_mem hc.conj_mem⟩,
        mem_centralizer_iff.mpr fun g hg => by
          rw [Set.mem_singleton_iff.mp hg]
          exact hR.d_comm.symm⟩
      U_le := hU.le_normalizer
      U_normal := hU.normalizer_le
      isSylowOf := hU.isSylowOf
      card_U := by rw [hU.card]
      szR_le := hU.szR_le
      conj_t_not_mem := hU.conj_t_not_mem_szA
      conj_szA₁ := hU.conj_szA₁
      conj_T₁ := fun x hx y hy => SzC1.conj_T₁ hR hc ha hK' hTR hinv hU hx hy
      conj_V₁ := fun x hx r hr => hU.conj_R₂ x (hU.U₁_le hx) r hr
      inf_centralizer := hU.inf_centralizer
      U₁_le := hU.U₁_le
      U₁_normal := hU.le_normalizer_U₁
      sup_eq := hU.sup_eq
      t_not_mem := hU.t_not_mem
      inf_eq := hU.inf_eq
      d_mem_U₁ := hU.d_mem }
  rw [hcoords.card_R₂ hR, hc.card_szA₁ ha hK', Nat.card_eq_fintype_card, hK]
  ring

end CFSG.SeitzReduction.RankOne
