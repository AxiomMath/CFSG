module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Grp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4B0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem O_normal_M (t tau x₁ x₂ : G) : NormalIn (ctxO t tau x₁ x₂) (ctxM t tau x₁ x₂) :=
  ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 (ctxM t tau x₁ x₂), fun _ hg _ hk =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ctxM t tau x₁ x₂) hg) _).mp hk⟩

section Basic

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

theorem U_le_M : ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ := hc.U_sylow.1

theorem O_le_U : ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam := le_sup_left

theorem q_mem_U : t * lam ∈ ctxU t tau x₁ x₂ lam :=
  mul_mem (mem_sup_left hc.toCtx4Q.t_mem_O) (mem_sup_right (mem_zpowers lam))

theorem q_mem_M : t * lam ∈ ctxM t tau x₁ x₂ := U_le_M hc (q_mem_U hc)

theorem q_conj_O {a : G} (ha : a ∈ ctxO t tau x₁ x₂) :
    (t * lam) * a * (t * lam)⁻¹ ∈ ctxO t tau x₁ x₂ :=
  (O_normal_M t tau x₁ x₂).2 _ (q_mem_M hc) a ha

theorem q_conj_X {x : G} (hx : x ∈ ctxX t tau x₁ x₂) :
    (t * lam) * x * (t * lam)⁻¹ ∈ ctxX t tau x₁ x₂ :=
  (Subgroup.mem_normalizer_iff.mp (q_mem_M hc) x).mp hx

theorem norm_U_le_LO :
    normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) ≤ ctxLO t tau x₁ x₂ :=
  normalizer_le_of_charIn hc.char_O

theorem card_U : Nat.card (ctxU t tau x₁ x₂ lam) = 2 ^ 9 := by
  have hfac : (3 * 2 ^ 9).factorization 2 = 9 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
      Nat.factorization_pow_self Nat.prime_two]
  rw [S4B.card_eq_of_isSylowIn hc.U_sylow, hc.card_M, hfac]

theorem card_X : Nat.card (ctxX t tau x₁ x₂) = 16 :=
  (Ctx4.ctxX_facts hc.toCtx4).2.1

theorem X_le_O : ctxX t tau x₁ x₂ ≤ ctxO t tau x₁ x₂ := by
  rw [ctxX, Subgroup.closure_le]
  rintro u (rfl | rfl | rfl | rfl)
  · exact hc.toCtx4Q.t_mem_O
  · exact hc.toCtx4Q.tau_mem_O
  · exact hc.toCtx4Q.Q_le_O (hc.toCtx4Q.V_le_Q
      (by rw [fourGrp]; exact Subgroup.subset_closure (by simp)))
  · exact hc.toCtx4Q.Q_le_O (hc.toCtx4Q.V_le_Q
      (by rw [fourGrp]; exact Subgroup.subset_closure (by simp)))

theorem X_normal_O {a x : G} (ha : a ∈ ctxO t tau x₁ x₂) (hx : x ∈ ctxX t tau x₁ x₂) :
    a * x * a⁻¹ ∈ ctxX t tau x₁ x₂ :=
  (Subgroup.mem_normalizer_iff.mp (hc.toCtx4Q.O_le_M ha) x).mp hx

theorem lam_not_mem_O : lam ∉ ctxO t tau x₁ x₂ := by
  intro hlam
  have hU_eq : ctxU t tau x₁ x₂ lam = ctxO t tau x₁ x₂ := by
    rw [ctxU, sup_eq_left]
    exact Subgroup.zpowers_le.mpr hlam
  have h1 : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 9 := by
    rw [← hU_eq]
    exact card_U hc
  rw [hc.card_O] at h1
  exact absurd h1 (by norm_num)

theorem q_not_mem_O : t * lam ∉ ctxO t tau x₁ x₂ := by
  intro h
  apply lam_not_mem_O hc
  have h2 : t⁻¹ * (t * lam) ∈ ctxO t tau x₁ x₂ :=
    mul_mem (inv_mem hc.toCtx4Q.t_mem_O) h
  have h3 : t⁻¹ * (t * lam) = lam := by group
  rwa [h3] at h2

theorem inv_mul_mem_O {a b : G} (ha : a ∈ ctxU t tau x₁ x₂ lam) (hb : b ∈ ctxU t tau x₁ x₂ lam)
    (ha' : a ∉ ctxO t tau x₁ x₂) (hb' : b ∉ ctxO t tau x₁ x₂) : a⁻¹ * b ∈ ctxO t tau x₁ x₂ := by
  have hrel : (ctxO t tau x₁ x₂).relIndex (ctxU t tau x₁ x₂ lam) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := ctxO t tau x₁ x₂) (K := ctxU t tau x₁ x₂ lam)
    rw [inf_eq_left.mpr (O_le_U hc), card_U hc, hc.card_O] at h
    have h9 : (2 : ℕ) ^ 9 = 2 * 2 ^ 8 := by norm_num
    rw [h9] at h
    exact Nat.mul_right_cancel (by norm_num) h
  let H : Subgroup ↥(ctxU t tau x₁ x₂ lam) :=
    (ctxO t tau x₁ x₂).subgroupOf (ctxU t tau x₁ x₂ lam)
  have hidx : H.index = 2 := hrel
  have hnotA : (⟨a, ha⟩ : ↥(ctxU t tau x₁ x₂ lam)) ∉ H := fun hh =>
    ha' (Subgroup.mem_subgroupOf.mp hh)
  have hnotB : (⟨b, hb⟩ : ↥(ctxU t tau x₁ x₂ lam)) ∉ H := fun hh =>
    hb' (Subgroup.mem_subgroupOf.mp hh)
  have hnotAinv : (⟨a, ha⟩ : ↥(ctxU t tau x₁ x₂ lam))⁻¹ ∉ H := fun hh =>
    hnotA (by simpa using H.inv_mem hh)
  have hmem : (⟨a, ha⟩ : ↥(ctxU t tau x₁ x₂ lam))⁻¹ * ⟨b, hb⟩ ∈ H :=
    (Subgroup.mul_mem_iff_of_index_two hidx).mpr
      ⟨fun hA => absurd hA hnotAinv, fun hB => absurd hB hnotB⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

end Basic

section Sylow

variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

theorem exists_n_W : ∃ (W : Subgroup G) (n : G), IsSylowIn 2 W (ctxLO t tau x₁ x₂) ∧
    ctxU t tau x₁ x₂ lam ≤ W ∧ n ∈ W ∧
    n ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) ∧
    n ∉ ctxU t tau x₁ x₂ lam ∧ n ^ 2 ∈ ctxU t tau x₁ x₂ lam := by
  classical
  have hU2 : IsPGroup 2 (ctxU t tau x₁ x₂ lam) := hc.U_sylow.2.1
  obtain ⟨𝒮, h𝒮, hU𝒮⟩ :=
    S4B.exists_isSylowIn_of_le (K := ⊤) (U := ctxU t tau x₁ x₂ lam) le_top hU2
  have hne : ctxU t tau x₁ x₂ lam ≠ 𝒮 := by
    intro hEq
    apply hc.U_not_sylow
    rw [hEq]
    exact h𝒮
  have hexists : ∃ n₀ ∈ 𝒮,
      (∀ x ∈ ctxU t tau x₁ x₂ lam, n₀ * x * n₀⁻¹ ∈ ctxU t tau x₁ x₂ lam) ∧
      n₀ ∉ ctxU t tau x₁ x₂ lam := by
    by_contra h
    push Not at h
    exact hne (S4B.eq_of_forall_normalizes h𝒮.2.1 hU𝒮 h)
  obtain ⟨n₀, hn₀𝒮, hn₀conj, hn₀U⟩ := hexists
  let φ : G →* G := MulAut.conj n₀
  have hφ : ∀ y : G, φ y = n₀ * y * n₀⁻¹ := fun y => rfl
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h : n₀ * x * n₀⁻¹ = n₀ * y * n₀⁻¹ := hxy
    exact mul_left_cancel (mul_right_cancel h)
  have hmap_le : (ctxU t tau x₁ x₂ lam).map φ ≤ ctxU t tau x₁ x₂ lam := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hn₀conj y hy
  have hmap_card : Nat.card ((ctxU t tau x₁ x₂ lam).map φ) =
      Nat.card (ctxU t tau x₁ x₂ lam) :=
    Subgroup.card_map_of_injective (f := φ) hφ_inj
  have hmap_eq : (ctxU t tau x₁ x₂ lam).map φ = ctxU t tau x₁ x₂ lam :=
    Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hmap_card.symm)
  have hn₀_norm : n₀ ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : φ x ∈ (ctxU t tau x₁ x₂ lam).map φ := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hmap_eq] at hx'
      simpa [hφ x] using hx'
    · intro hx
      have hx' : n₀ * x * n₀⁻¹ ∈ (ctxU t tau x₁ x₂ lam).map φ := by
        rw [hmap_eq]
        exact hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      have hxy : φ y = φ x := by rw [hyx, hφ x]
      rw [hφ_inj hxy] at hy
      exact hy
  obtain ⟨m, hm⟩ := h𝒮.2.1.exists_pow_pow_eq_one (⟨n₀, hn₀𝒮⟩ : ↥𝒮)
  have hm' : n₀ ^ (2 ^ m) = 1 := by
    simpa using congrArg Subtype.val hm
  have hex : ∃ k, n₀ ^ (2 ^ k) ∈ ctxU t tau x₁ x₂ lam :=
    ⟨m, by rw [hm']; exact one_mem _⟩
  have hk : n₀ ^ (2 ^ Nat.find hex) ∈ ctxU t tau x₁ x₂ lam := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    exact hn₀U (by simpa [h0] using hk)
  have hk1 : 1 ≤ Nat.find hex := Nat.one_le_iff_ne_zero.mpr hk0
  have hlt : Nat.find hex - 1 < Nat.find hex := by omega
  have hnotP : n₀ ^ (2 ^ (Nat.find hex - 1)) ∉ ctxU t tau x₁ x₂ lam := Nat.find_min hex hlt
  set n : G := n₀ ^ (2 ^ (Nat.find hex - 1)) with hn_def
  have hnU : n ∉ ctxU t tau x₁ x₂ lam := by
    intro hn
    rw [hn_def] at hn
    exact hnotP hn
  have hn_sq : n ^ 2 ∈ ctxU t tau x₁ x₂ lam := by
    have hpow : 2 ^ (Nat.find hex - 1) * 2 = 2 ^ Nat.find hex := by
      rw [← pow_succ, Nat.sub_add_cancel hk1]
    have hn2 : n ^ 2 = n₀ ^ (2 ^ Nat.find hex) := by
      rw [hn_def, ← pow_mul, hpow]
    rw [hn2]
    exact hk
  have hn𝒮 : n ∈ 𝒮 := by
    rw [hn_def]
    exact Subgroup.pow_mem 𝒮 hn₀𝒮 _
  have hn_norm : n ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G) := by
    rw [hn_def]
    exact Subgroup.pow_mem (normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G)) hn₀_norm _
  have hU_LO : ctxU t tau x₁ x₂ lam ≤ ctxLO t tau x₁ x₂ :=
    le_trans Subgroup.le_normalizer (norm_U_le_LO hc)
  have hz_LO : zpowers n ≤ ctxLO t tau x₁ x₂ :=
    le_trans (Subgroup.zpowers_le.mpr hn_norm) (norm_U_le_LO hc)
  have hle : ctxU t tau x₁ x₂ lam ⊔ zpowers n ≤ ctxLO t tau x₁ x₂ := sup_le hU_LO hz_LO
  have hp : IsPGroup 2 ((ctxU t tau x₁ x₂ lam ⊔ zpowers n : Subgroup G)) :=
    IsPGroup.to_le h𝒮.2.1 (sup_le hU𝒮 (Subgroup.zpowers_le.mpr hn𝒮))
  obtain ⟨W, hW, hleW⟩ := S4B.exists_isSylowIn_of_le hle hp
  exact ⟨W, n, hW, le_sup_left.trans hleW,
    hleW (Subgroup.mem_sup_right (Subgroup.mem_zpowers n)), hn_norm, hnU, hn_sq⟩

end Sylow

end CFSG.OddStandard.SmallF3.HarrisU33.L34
