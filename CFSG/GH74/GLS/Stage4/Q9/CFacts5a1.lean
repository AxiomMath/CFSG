module

public import CFSG.GH74.GLS.Stage4.Q9.DFacts
public import CFSG.GH74.GLS.Stage4.Q9.Link1
public import CFSG.GH74.GLS.Stage4.Q9.Link2
public import CFSG.GH74.GLS.Stage4.Q9.SettingFacts
public import CFSG.GH74.GLS.Stage4.Q9.Swap
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem fac720_three : (720 : ℕ).factorization 3 = 2 := by
  have : (720 : ℕ) = 2 ^ 4 * (3 ^ 2 * 5) := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Nat.prime_two.factorization,
    Nat.prime_three.factorization, Nat.prime_five.factorization]
  simp

theorem exists_sylow3 {G : Type*} [Group G] {K : Subgroup G} (hK : Nat.card K = 720) :
    ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 3 P ∧ Nat.card P = 9 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 K := default
  have hP : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity, hK, fac720_three]
    norm_num
  refine ⟨(P : Subgroup K).map K.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map K.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact hP

namespace Q9Setting

variable {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
  (S : Q9Setting G z K₁ K₂ F₁ F₂)

include S

theorem z_comm₁ {k : G} (hk : k ∈ K₁) : z * k = k * z := (S.comm k hk z S.z_mem₂).symm

theorem mem_Hs_of_fixed {ψ₁ : ↥K₁ ≃* SL2}
    (ht₁ : ∀ k k' : ↥K₁, (k' : G) = S.t * (k : G) * S.t⁻¹ → ψ₁ k' = sigmaAut (ψ₁ k))
    {x : G} (hx : x ∈ K₁) (hfix : sigmaAut (ψ₁ ⟨x, hx⟩) = ψ₁ ⟨x, hx⟩) : x ∈ S.Hs := by
  have hxt : S.t * x = x * S.t := by
    have hk' : S.t * x * S.t⁻¹ ∈ K₁ := S.normal₁ S.t S.t_mem x hx
    have h := ht₁ ⟨x, hx⟩ ⟨S.t * x * S.t⁻¹, hk'⟩ rfl
    rw [hfix] at h
    have h2 : S.t * x * S.t⁻¹ = x := congrArg Subtype.val (ψ₁.injective h)
    calc S.t * x = S.t * x * S.t⁻¹ * S.t := by group
      _ = x * S.t := by rw [h2]
  have hxz : z * x = x * z := S.z_comm₁ hx
  have hcl : (closure ({z, S.t} : Set G) : Subgroup G) ≤ centralizer ({x} : Set G) := by
    rw [closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact mem_centralizer_singleton_iff.mpr hxz
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact mem_centralizer_singleton_iff.mpr hxt
  apply S.Hs_ge₁
  refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
  rw [mem_centralizer_iff]
  intro h hh
  exact mem_centralizer_singleton_iff.mp (hcl hh)

theorem exists_x5 : ∃ x ∈ K₁, x ∈ S.Hs ∧ orderOf x = 5 := by
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  obtain ⟨M, hσ, hM⟩ := exists_fixed5
  refine ⟨((ψ₁.symm M : ↥K₁) : G), (ψ₁.symm M).2, ?_, ?_⟩
  · apply S.mem_Hs_of_fixed ht₁ (ψ₁.symm M).2
    simpa using hσ
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq ψ₁.symm, hM]

theorem conj_x5_into_Hs
    : ∀ x ∈ K₁, orderOf x = 5 → ∃ k ∈ K₁, k * x * k⁻¹ ∈ S.Hs := by
  intro x hx hx5
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  have hM : orderOf (ψ₁ ⟨x, hx⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx5]
  obtain ⟨k₀, hk₀⟩ := conj_fixed5 _ hM
  set k : ↥K₁ := ψ₁.symm k₀ with hk
  refine ⟨(k : G), k.2, ?_⟩
  have hxk : (k : G) * x * (k : G)⁻¹ ∈ K₁ := mul_mem (mul_mem k.2 hx) (inv_mem k.2)
  apply S.mem_Hs_of_fixed ht₁ hxk
  have h1 : ψ₁ ⟨(k : G) * x * (k : G)⁻¹, hxk⟩ = k₀ * ψ₁ ⟨x, hx⟩ * k₀⁻¹ := by
    have : (⟨(k : G) * x * (k : G)⁻¹, hxk⟩ : ↥K₁) = k * ⟨x, hx⟩ * k⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hk, MulEquiv.apply_symm_apply]
  rw [h1]
  exact hk₀

theorem exists_h16 :
    ∃ h : G, orderOf h = 16 ∧ S.t * h * S.t⁻¹ = h ^ 7 ∧ h ^ 8 = z ∧
    ∀ x : G, x ∈ K₁ → S.t * x = x * S.t → h * x = x * h := by
  obtain ⟨ψ₁, ψ₂, hz₁, hz₂, ht₁, ht₂⟩ := q9_link S
  obtain ⟨ι₁, ι₂, π, hι₁, hι₂, hι₁i, hι₂i, hι₁t, hι₂t, -⟩ := q9_link2 S ψ₁ ψ₂ hz₁ hz₂ ht₁ ht₂
  obtain ⟨l, hlp, hlo, hlt, hl8⟩ := _root_.CFSG.GH74.GLS.Stage4.Q9.exists_h16
  refine ⟨ι₂ l, ?_, ?_, ?_, ?_⟩
  · rw [← hlo]
    exact orderOf_injective ι₂ hι₂ l
  · have := congrArg ι₂ hlt
    rw [map_mul, map_mul, map_inv, hι₂t, map_pow] at this
    exact this
  · rw [← map_pow, hl8, hι₂i]
    have hzk : ((⟨z, S.z_mem₂⟩ : ↥K₂)) = ψ₂.symm minusOne := by
      rw [← hz₂ ⟨z, S.z_mem₂⟩ rfl]; simp
    rw [← hzk]
  · intro x hx hxt
    have hl : ι₂ l = ι₂ (innerL l.left) * ι₂ (SemidirectProduct.inr l.right) := by
      have h := SemidirectProduct.inl_left_mul_inr_right l
      conv_lhs => rw [← h]
      exact map_mul ι₂ _ _
    have hcomm1 : ι₂ (innerL l.left) * x = x * ι₂ (innerL l.left) := by
      rw [hι₂i]
      exact (S.comm x hx _ (ψ₂.symm l.left).2).symm
    have hcomm2 : ι₂ (SemidirectProduct.inr l.right) * x =
        x * ι₂ (SemidirectProduct.inr l.right) := by
      rcases Link2.eq_one_or_eq_ofAdd_one l.right with h | h
      · rw [h]
        have h1 : (SemidirectProduct.inr (1 : Multiplicative (ZMod 2)) : Lg) = 1 := map_one _
        rw [h1, map_one, one_mul, mul_one]
      · rw [h]
        have h1 : (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) : Lg) = tauL := rfl
        rw [h1, hι₂t]
        exact hxt
    rw [hl, mul_assoc, hcomm2, ← mul_assoc, hcomm1, mul_assoc]

theorem htns_x5 : ∀ x ∈ S.Hs, x ≠ 1 → ∀ n ∈ centralizer ({x} : Set G),
    (∀ y ∈ closure ({z, S.t} : Set G), n * y * n⁻¹ ∈ closure ({z, S.t} : Set G)) →
      orderOf n ≠ 3 := by
  intro x hx hx1 n hn hnorm h3
  have hn3 : n * n * n = 1 := by
    have := pow_orderOf_eq_one n
    rw [h3] at this
    simpa [pow_succ] using this
  have hninv : n⁻¹ = n * n := by
    have : n * (n * n) = 1 := by rw [← mul_assoc]; exact hn3
    exact inv_eq_of_mul_eq_one_right this
  have hnN : n ∈ normalizer ((closure ({z, S.t} : Set G) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hnorm y hy
    · intro hy
      have h2 := hnorm _ (hnorm _ hy)
      have : n * (n * (n * y * n⁻¹) * n⁻¹) * n⁻¹ = y := by
        have e : n * (n * (n * y * n⁻¹) * n⁻¹) * n⁻¹ = (n * n * n) * y * (n * n * n)⁻¹ := by group
        rw [e, hn3]; group
      rw [this] at h2
      exact h2
  rw [S.normalizer_eq] at hnN
  have := S.tns n hnN h3 x hx hx1
  apply this
  rw [mem_centralizer_singleton_iff.mp hn]
  group

theorem sylow3_K₂ : ∃ P : Subgroup G, P ≤ K₂ ∧ IsPGroup 3 P ∧ Nat.card P = 9 :=
  exists_sylow3 S.card_K₂

theorem exists_x5' : ∃ x ∈ K₂, x ∈ S.Hs ∧ orderOf x = 5 := S.swap.exists_x5

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
