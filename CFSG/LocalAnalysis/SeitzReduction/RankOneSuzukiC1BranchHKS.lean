module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchFam
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1BranchStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}
  {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}

theorem d_mem_normalizer_U (h : SzC1Stage G L f a t T d V U U₁ k) :
    d ∈ normalizer (U : Set G) := by
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.mp h.d_norm.2
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  have hdU₁ : ∀ w ∈ U₁, d⁻¹ * w * d ∈ U₁ := fun w hw => by
    simpa using (mem_normalizer_iff.mp (inv_mem h.d_mem_U₁) w).mp hw
  rcases h.mem_or_mul_t_mem hx with h1 | h1
  · exact h.U₁_le (hdU₁ x h1)
  · have e : d⁻¹ * x * d = (d⁻¹ * (x * t) * d) * t := by
      rw [show d⁻¹ * (x * t) * d * t = d⁻¹ * x * (t * d) * t by group, ← hdt]
      rw [show d⁻¹ * x * (d * t) * t = d⁻¹ * x * d * (t * t) by group, h.t_mul_self, mul_one]
    rw [e]
    exact mul_mem (h.U₁_le (hdU₁ _ h1)) h.t_mem_U

section Fam

variable (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem famPerm_d_inv
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (c : K) :
    h.famPerm hK hc hμ hlam ⟨d⁻¹, inv_mem h.d_mem_normalizer_U⟩ c = κ * c := by
  apply h.fam_injective hK hc hμ
  rw [← h.famPerm_spec hK hc hμ hlam]
  show (SzC1.szFam U₁ t hc c).map (MulAut.conj d⁻¹).toMonoidHom = _
  rw [SzC1.szFam, h.map_conj_d_cent, SzC1.szFam, ← mul_one (d⁻¹ * SzC1.szSec hc c * d),
    ← mul_one (SzC1.szSec hc (κ * c))]
  exact h.cent_eq_of_u_eq hK hc hμ (hc.conj_mem _ (SzC1.szSec_mem hc c)) (SzC1.szSec_mem hc _)
    (by rw [hc.conj_u _ (SzC1.szSec_mem hc c), SzC1.szSec_u hc, SzC1.szSec_u hc]) (one_mem _)
    (one_mem _)

theorem famPerm_zero_iff
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (n : normalizer (U : Set G)) :
    h.famPerm hK hc hμ hlam n 0 = 0 ↔ (n : G) ∈ normalizer (szT₁ L T : Set G) := by
  have hspec := h.famPerm_spec hK hc hμ hlam n 0
  rw [h.fam_zero hK hc hμ] at hspec
  constructor
  · intro h0
    rw [h0, h.fam_zero hK hc hμ] at hspec
    exact SzC1.mem_normalizer_of_map_le hspec.le
  · intro hn
    apply h.fam_injective hK hc hμ
    rw [← hspec, SzC1.map_conj_eq_of_mem_normalizer hn, h.fam_zero hK hc hμ]

theorem exists_famPerm_eq
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) (c : K) :
    ∃ n : normalizer (U : Set G), h.famPerm hK hc hμ hlam n 0 = c := by
  by_cases hc0 : c = 0
  · exact ⟨1, by rw [map_one, Equiv.Perm.one_apply, hc0]⟩
  obtain ⟨g, hgN, hgU, P, hP2, hUP, hgP⟩ := exists_normalizer_not_mem_of_not_isSylow h.isPGroup_U hU
  have hUT : U ≤ normalizer (szT₁ L T : Set G) := fun x hx =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      simpa using h.conj_T₁_mem (inv_mem hx) hy
  have hgT : (g : G) ∉ normalizer (szT₁ L T : Set G) := by
    intro hgT
    have hle : U ⊔ zpowers g ≤ normalizer (szT₁ L T : Set G) :=
      sup_le hUT (zpowers_le.mpr hgT)
    have heq := h.eq_of_le_normalizer_T₁ hμ hlam hν (hP2.to_le (sup_le hUP (zpowers_le.mpr hgP)))
      le_sup_left hle
    exact hgU (heq ▸ mem_sup_right (mem_zpowers g))
  set c₀ := h.famPerm hK hc hμ hlam ⟨g, hgN⟩ 0 with hc₀
  have hc₀0 : c₀ ≠ 0 := fun h0 => hgT ((h.famPerm_zero_iff hK hc hμ hlam ⟨g, hgN⟩).mp h0)
  obtain ⟨m, hm⟩ := hκ (c / c₀) (div_ne_zero hc0 hc₀0)
  set δ : normalizer (U : Set G) := ⟨d⁻¹, inv_mem h.d_mem_normalizer_U⟩ with hδ
  have key : ∀ j : ℕ, h.famPerm hK hc hμ hlam (δ ^ j * ⟨g, hgN⟩) 0 = κ ^ j * c₀ := by
    intro j
    induction j with
    | zero => simp [hc₀]
    | succ j ih =>
      rw [pow_succ', mul_assoc, map_mul, Equiv.Perm.mul_apply, ih, h.famPerm_d_inv hK hc hμ hlam,
        pow_succ', mul_assoc]
  exact ⟨δ ^ m * ⟨g, hgN⟩, by rw [key, hm, div_mul_cancel₀ c hc₀0]⟩

theorem famPerm_eq_of_mem_U
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) (x : normalizer (U : Set G))
    (hx : (x : G) ∈ U) (c : K) : h.famPerm hK hc hμ hlam x c = c := by
  obtain ⟨n, hn⟩ := h.exists_famPerm_eq hK hc hκ hμ hlam hν hU c
  have hm : ((n⁻¹ * x * n : normalizer (U : Set G)) : G) ∈ U := by
    show (n : G)⁻¹ * x * n ∈ U
    have := (mem_normalizer_iff.mp (inv_mem n.2) (x : G)).mp hx
    rwa [inv_inv] at this
  have hmT : ((n⁻¹ * x * n : normalizer (U : Set G)) : G) ∈ normalizer (szT₁ L T : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      have := h.conj_T₁_mem (inv_mem hm) hy
      rwa [inv_inv] at this
  have e := (h.famPerm_zero_iff hK hc hμ hlam _).mpr hmT
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hn] at e
  have e2 := congrArg (h.famPerm hK hc hμ hlam n) e
  rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply,
    hn] at e2
  exact e2

theorem famPerm_two_transitive
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∀ a₁ b₁ c₁ e₁ : K, a₁ ≠ b₁ → c₁ ≠ e₁ →
      ∃ x ∈ (h.famPerm hK hc hμ hlam).range, x a₁ = c₁ ∧ x b₁ = e₁ := by
  intro a₁ b₁ c₁ e₁ hab hce
  set φ := h.famPerm hK hc hμ hlam with hφ
  obtain ⟨n₁, hn₁⟩ := h.exists_famPerm_eq hK hc hκ hμ hlam hν hU a₁
  obtain ⟨n₂, hn₂⟩ := h.exists_famPerm_eq hK hc hκ hμ hlam hν hU c₁
  set β := φ n₁⁻¹ b₁ with hβ
  set γ := φ n₂⁻¹ e₁ with hγ
  have hinv : ∀ (n : normalizer (U : Set G)) (z : K), φ n⁻¹ (φ n z) = z := fun n z => by
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hab
    rw [← hn₁]
    have := congrArg (φ n₁) h0
    rw [hβ, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply] at this
    exact this.symm
  have hγ0 : γ ≠ 0 := by
    intro h0
    apply hce
    rw [← hn₂]
    have := congrArg (φ n₂) h0
    rw [hγ, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply] at this
    exact this.symm
  obtain ⟨j, hj⟩ := hκ (γ / β) (div_ne_zero hγ0 hβ0)
  set δ : normalizer (U : Set G) := ⟨d⁻¹, inv_mem h.d_mem_normalizer_U⟩ with hδ
  have hpow : ∀ (i : ℕ) (z : K), φ (δ ^ i) z = κ ^ i * z := by
    intro i
    induction i with
    | zero => intro z; simp
    | succ i ih =>
      intro z
      rw [pow_succ', map_mul, Equiv.Perm.mul_apply, ih, h.famPerm_d_inv hK hc hμ hlam, pow_succ']
      ring
  refine ⟨φ (n₂ * δ ^ j * n₁⁻¹), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hn₁, hinv, hpow,
      mul_zero, hn₂]
  · rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hβ, hpow, hj,
      div_mul_cancel₀ γ hβ0, hγ, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply]


theorem famPerm_stabilizer
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    Odd (Nat.card ((h.famPerm hK hc hμ hlam).range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) :
      Subgroup (Equiv.Perm K))) ∧
    Nat.card ((h.famPerm hK hc hμ hlam).range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) :
      Subgroup (Equiv.Perm K)) ∣ (2 ^ f - 1) * f := by
  let φ := h.famPerm hK hc hμ hlam
  let W : Subgroup (normalizer (U : Set G)) :=
    (normalizer (szT₁ L T : Set G)).subgroupOf (normalizer (U : Set G))
  have hS₀ : φ.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) = W.map φ := by
    ext p
    constructor
    · rintro ⟨⟨n, rfl⟩, hn0⟩
      refine ⟨n, mem_subgroupOf.mpr ((h.famPerm_zero_iff hK hc hμ hlam n).mp ?_), rfl⟩
      exact MulAction.mem_stabilizer_iff.mp hn0
    · rintro ⟨n, hnW, rfl⟩
      refine ⟨⟨n, rfl⟩, MulAction.mem_stabilizer_iff.mpr ?_⟩
      exact (h.famPerm_zero_iff hK hc hμ hlam n).mpr (mem_subgroupOf.mp hnW)
  have hker : φ.ker ≤ W := fun n hn => mem_subgroupOf.mpr
    ((h.famPerm_zero_iff hK hc hμ hlam n).mp (by
      have hn' : φ n = 1 := hn
      show φ n 0 = 0
      rw [hn', Equiv.Perm.one_apply]))
  have hcardW := card_eq_card_map_mul_card_ker_of_ker_le φ hker
  have hWY : Nat.card W =
      Nat.card (normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective (normalizer (U : Set G)).subtype_injective,
      subgroupOf_map_subtype, inf_comm]
  have hUker : Nat.card U ∣ Nat.card φ.ker := by
    have hle : U.subgroupOf (normalizer (U : Set G)) ≤ φ.ker := fun x hx => by
      rw [MonoidHom.mem_ker]
      exact Equiv.ext fun c => h.famPerm_eq_of_mem_U hK hc hκ hμ hlam hν hU x
        (mem_subgroupOf.mp hx) c
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv] at this
  obtain ⟨m, hm⟩ := hUker
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have hY := relIndex_mul_card (H := U) (K := normalizer (U : Set G) ⊓
    normalizer (szT₁ L T : Set G))
  have hUY : U ≤ normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G) :=
    le_inf le_normalizer fun x hx => mem_normalizer_of_forall_inv_mul_mul_mem fun y hy => by
      simpa using h.conj_T₁_mem (inv_mem hx) hy
  rw [inf_of_le_left hUY] at hY
  rw [hS₀]
  have key : Nat.card (W.map φ) * m =
      U.relIndex (normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G)) := by
    have e : Nat.card (W.map φ) * m * Nat.card U =
        U.relIndex (normalizer (U : Set G) ⊓ normalizer (szT₁ L T : Set G)) * Nat.card U := by
      rw [hY, ← hWY, hcardW, hm]
      ring
    exact Nat.eq_of_mul_eq_mul_right hU0 e
  refine ⟨?_, ?_⟩
  · have hodd := h.not_two_dvd_relIndex hμ hlam hν
    rw [← key] at hodd
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2 => hodd (h2.trans (dvd_mul_right _ _))
  · have hdvd := h.card_normalizer_inf_dvd hμ hlam hν
    rw [← hY, ← key, mul_comm (Nat.card (W.map φ) * m)] at hdvd
    have hdvd' : Nat.card U * Nat.card (W.map φ) ∣ Nat.card U * ((2 ^ f - 1) * f) := by
      exact (Nat.mul_dvd_mul_left _ (dvd_mul_right _ _)).trans hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hU0 hdvd'

theorem conj_mem_mul_V_of_translation
    (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) (n : normalizer (U : Set G))
    (htr : ∀ c, h.famPerm hK hc hμ hlam n c = h.famPerm hK hc hμ hlam n 0 + c) {y : G}
    (hy : y ∈ szT₁ L T) : ∃ r ∈ V, (n : G) * y * (n : G)⁻¹ = y * r := by
  have hK' := h.card_K hK hc
  have hn := n.2
  obtain ⟨y₀, hy₀, w, hw, hx, -⟩ := h.map_conj_T₁_eq hK hc hμ hlam hn
  have hval : ∀ c {y' r : G}, y' ∈ szT₁ L T → r ∈ V →
      (n : G) * SzC1.szSec hc c * (n : G)⁻¹ = y' * r →
      h.famPerm hK hc hμ hlam n c = u y' + u y₀ := fun c y' r hy' hr hyr =>
    h.fam_injective hK hc hμ (((h.famPerm_spec hK hc hμ hlam n c).symm).trans
      (h.map_conj_fam hK hc hμ hn hy' hr hyr hy₀ hw hx))
  have hA0 := (hc.mem_szA₁_iff h.ha hK' (SzC1.szSec_mem hc 0)).mpr (SzC1.szSec_u hc 0)
  have hA0' := h.conj_mem_szA₁_of_normalizer hμ hn hA0
  have h0 := hval 0 (one_mem _) (h.le hA0') (one_mul _).symm
  rw [hc.u_one, zero_add] at h0
  obtain ⟨y', hy', r, hr, hyr⟩ :=
    h.exists_conj_decomp hK hc hμ hlam hn (SzC1.szSec_mem hc (u y))
  have hc1 := hval (u y) hy' hr hyr
  rw [htr, h0] at hc1
  have hu' : u y' = u y := by linear_combination -hc1
  have hb := hc.inv_mul_mem_szA₁_of_u_eq h.ha hK' hy hy' hu'.symm
  have ha := hc.inv_mul_mem_szA₁_of_u_eq h.ha hK' (SzC1.szSec_mem hc (u y)) hy (SzC1.szSec_u hc _)
  have ha' := h.conj_mem_szA₁_of_normalizer hμ hn ha
  refine ⟨(y⁻¹ * y') * r * ((n : G) * ((SzC1.szSec hc (u y))⁻¹ * y) * (n : G)⁻¹),
    mul_mem (mul_mem (h.le hb) hr) (h.le ha'), ?_⟩
  calc (n : G) * y * (n : G)⁻¹ = ((n : G) * SzC1.szSec hc (u y) * (n : G)⁻¹) *
        ((n : G) * ((SzC1.szSec hc (u y))⁻¹ * y) * (n : G)⁻¹) := by group
    _ = y * ((y⁻¹ * y') * r * ((n : G) * ((SzC1.szSec hc (u y))⁻¹ * y) * (n : G)⁻¹)) := by
        rw [hyr]; group

end Fam

end SzC1Stage

end CFSG.SeitzReduction.RankOne
