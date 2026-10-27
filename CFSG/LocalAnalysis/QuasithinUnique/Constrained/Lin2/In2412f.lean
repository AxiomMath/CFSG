module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412e
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412c

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

section Center

variable {G : Type} [Group G]

theorem mulVec_slUpper {K : Type*} [Field K] (s : K) (v : Fin 2 → K) :
    ((slUpper s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec v = ![v 0 + s * v 1, v 1] := by
  rw [slUpper_val]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem centerOf_eq_of_coordinates {L R : Subgroup G} {n : ℕ} {K : Type} [Field K] [Fintype K]
    (A : Adapted L R n K) (hZ : blockZ L = ⊥)
    (hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L) (hUR : blockU L ≤ R)
    (hCU : centerOf R ≤ blockU L) {N' : Subgroup G}
    (hmemN : ∀ x : G, x ∈ N' ↔ ∃ h : x ∈ blockU L, Multiplicative.toAdd (A.β ⟨x, h⟩) 1 = 0) :
    centerOf R = N' := by
  have hβk : ∀ u : blockU L, A.β u = 1 ↔ (u : G) ∈ blockZ L := fun u => by
    rw [← MonoidHom.mem_ker, A.β_ker, Subgroup.mem_subgroupOf]
  have hβinj : Function.Injective A.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : G) ∈ blockZ L := (hβk u).1 hu
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  apply le_antisymm
  · intro z hz
    have hzc : ∀ r ∈ R, r * z = z * r := Subgroup.mem_centralizer_iff.1 hz.2
    have hzU : z ∈ blockU L := hCU hz
    obtain ⟨ℓ, hℓ⟩ := A.α_surj (slUpper 1)
    have hℓR : (ℓ : G) ∈ R := (A.mem_P ℓ).2 (hℓ ▸ slUpper_mem_slUni _)
    have h1 := A.β_equiv ℓ ⟨z, hzU⟩ ⟨z, hzU⟩ (by
      show z = (ℓ : G) * z * (ℓ : G)⁻¹
      rw [hzc (ℓ : G) hℓR]
      group)
    rw [hℓ, mulVec_slUpper] at h1
    refine (hmemN z).2 ⟨hzU, ?_⟩
    have h2 : Multiplicative.toAdd (A.β ⟨z, hzU⟩) 0 =
        Multiplicative.toAdd (A.β ⟨z, hzU⟩) 0 + 1 * Multiplicative.toAdd (A.β ⟨z, hzU⟩) 1 := by
      simpa using congrFun h1 0
    linear_combination -h2
  · intro x hx
    obtain ⟨hxU, hx1⟩ := (hmemN x).1 hx
    refine Subgroup.mem_inf.2 ⟨hUR hxU, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    have hrL : r ∈ L := A.P_le hr
    obtain ⟨s, hs⟩ := mem_slUni.1 ((A.mem_P ⟨r, hrL⟩).1 hr)
    have hv : r * x * r⁻¹ ∈ blockU L := hLU r hrL x hxU
    have h1 := A.β_equiv ⟨r, hrL⟩ ⟨x, hxU⟩ ⟨r * x * r⁻¹, hv⟩ rfl
    rw [hs, mulVec_slUpper, hx1, mul_zero, add_zero] at h1
    have h2 : A.β ⟨r * x * r⁻¹, hv⟩ = A.β ⟨x, hxU⟩ := by
      apply Multiplicative.toAdd.injective
      rw [h1]
      ext i
      fin_cases i
      · simp
      · simpa using hx1.symm
    have h3 : r * x * r⁻¹ = x := congrArg Subtype.val (hβinj h2)
    calc r * x = r * x * r⁻¹ * r := by group
      _ = x * r := by rw [h3]

end Center

section Field

theorem exists_half_of_twisted {K : Type} [Field K] [Fintype K] {n : ℕ} (hK2 : (2 : K) = 0)
    (hcard : Fintype.card K = 2 ^ n) (σ : K ≃+* K) (hσσ : ∀ v, σ (σ v) = v) (hσ : σ ≠ 1) :
    (∃ θ : K, σ θ ≠ θ) ∧ ∃ m : ℕ, n = m + m ∧ ∀ c : K, c * σ c = 1 →
      Nat.card {v : K // c * σ v = v} = 2 ^ m := by
  obtain ⟨θ, hθ⟩ : ∃ θ : K, σ θ ≠ θ := by
    by_contra hcon
    have hall : ∀ x : K, σ x = x := fun x => by
      by_contra hne
      exact hcon ⟨x, hne⟩
    exact hσ (RingEquiv.ext hall)
  refine ⟨⟨θ, hθ⟩, ?_⟩
  have hKcard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have h1 := card_twisted_fixed hK2 σ hσσ θ hθ 1 (by simp)
  rw [hKcard] at h1
  have hdvd : Nat.card {a : K // 1 * σ a = a} ∣ 2 ^ n :=
    Dvd.intro (Nat.card {a : K // 1 * σ a = a}) (by rw [← sq]; exact h1)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hnm : n = m + m := by
    have h2 : 2 ^ (m + m) = 2 ^ n := by rw [pow_add, ← hm, ← sq]; exact h1
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  refine ⟨m, hnm, fun c hcc => ?_⟩
  have h2 := card_twisted_fixed hK2 σ hσσ θ hθ c hcc
  rw [hKcard] at h2
  have h3 : (Nat.card {v : K // c * σ v = v}) ^ 2 = (2 ^ m) ^ 2 := by
    rw [h2, hnm, ← pow_mul]
    congr 1
    ring
  exact Nat.pow_left_injective (by norm_num) h3

end Field

section Counts

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.eq_one_of_inner (h : Lin2Cfg G T M H S L n D) (hQL : pCoreOf 2 L = pCoreOf 2 H)
    {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFL : F ⊓ L = ⊥) (hHF : H = L ⊔ F)
    {K : Type} [Field K] [Fintype K] {P : Subgroup G} (A : Adapted L P n K) {f : G} (hf : f ∈ F)
    (hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L) (k : SL(2, K))
    (hk : ∀ ℓ : L, A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ = k * A.α ℓ * k⁻¹) : f = 1 := by
  obtain ⟨ℓ₀, rfl⟩ := A.α_surj k
  have hFH : F ≤ H := le_sup_right.trans hHF.ge
  have hcH : (ℓ₀ : G)⁻¹ * f ∈ H := H.mul_mem (H.inv_mem (h.L_le_H ℓ₀.2)) (hFH hf)
  have hc : ∀ x ∈ L, ((ℓ₀ : G)⁻¹ * f) * x * ((ℓ₀ : G)⁻¹ * f)⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
    intro x hx
    set ℓ : L := ⟨x, hx⟩
    rw [show x = (ℓ : G) from rfl]
    have hα : A.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ = A.α (ℓ₀ * ℓ * ℓ₀⁻¹) := by rw [hk ℓ]; simp
    have h1 : (ℓ₀⁻¹ * ((⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ : L) * (ℓ₀ * ℓ * ℓ₀⁻¹)⁻¹) * ℓ₀ : L) ∈
        A.α.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hα]
      simp
    have h2 := (A.mem_pCoreOf_iff _).2 h1
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcQ := h.mem_pCoreOf_of_commutator_le hQL hF2 hHF A hcH hc
  have hfL' : f ∈ L := by
    have := L.mul_mem ℓ₀.2 ((hQL ▸ hcQ : (ℓ₀ : G)⁻¹ * f ∈ pCoreOf 2 L) |>
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L))
    simpa using this
  have : f ∈ F ⊓ L := ⟨hf, hfL'⟩
  rw [hFL, Subgroup.mem_bot] at this
  exact this

theorem counts_Zeq1 (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L = ⊥)
    {f : G} (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hf1 : f ≠ 1) (hf2 : f ^ 2 = 1) :
    (∀ r ∈ thompsonJ S, (f * r) ^ 2 = 1 → ∃ s ∈ thompsonJ S, s⁻¹ * f * s = f * r) ∧
      Nat.card (lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
        2 ^ (n / 2) ∧
      Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
        2 ^ (3 * n / 2) ∧
      ∀ x ∈ blockU L, (f * x) * (f * x) = 1 → ∃ m ∈ blockU L, m⁻¹ * f * m = f * x := by
  have hff : f * f = 1 := by rw [← sq]; exact hf2
  obtain ⟨hQL, -, -, hF3, hF4⟩ := complement_facts h8 hcfg hB
  obtain ⟨⟨-, -, hTnR⟩, ⟨hOL, hUQ⟩, ⟨-, hRsyl, h3⟩, -, -, -, h7, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hRUU, hZR, -, -⟩ := h3 x₀ hx₀T hx₀S
  have hUel : IsElemAbelian 2 (blockU L) := (h7 x₀ hx₀T hx₀S).1
  obtain ⟨K, _, _, ⟨A⟩⟩ := exists_adapted hcfg.one_pos hcfg.lin2 hRsyl
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card hcfg.one_pos A.card_eq
  have hfS : f ∈ S := hf.1
  have hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hcfg.S_le_normalizer hfS) x).1 hx
  have hHU : H ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [hUQ]; exact hcfg.H_le_normalizer_Q
  have hfU : ∀ x ∈ blockU L, f * x * f⁻¹ ∈ blockU L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hHU (hcfg.S_le_H hfS)) x).1 hx
  have hfR : ∀ x ∈ thompsonJ S, f * x * f⁻¹ ∈ thompsonJ S := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hTnR (hcfg.S_le_T hfS)) x).1 hx
  have hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L := by
    intro ℓ hℓ u hu
    have hn : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
      rw [← hOL]
      exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
    exact (Subgroup.mem_normalizer_iff.1 (hn hℓ) u).1 hu
  obtain ⟨σ, a, c', -, hσσ, hc3, hc2, hc1, hT, hU, hN, -, -, hσ1⟩ :=
    hcfg.link A hOL hff hfL hfU hfR
  have hFp : IsPGroup 2 ((S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G)) :=
    hcfg.S_isPGroup.to_le inf_le_left
  have hσ : σ ≠ 1 := by
    intro hσ
    obtain ⟨k, hk⟩ := hσ1 hσ
    exact hf1 (hcfg.eq_one_of_inner hQL hFp (by rw [inf_comm]; exact hF3) hF4 A hf hfL k hk)
  obtain ⟨⟨θ, hθ⟩, m, hnm, hfixcard⟩ := exists_half_of_twisted hK2 A.card_eq σ hσσ hσ
  have hUR : blockU L ≤ thompsonJ S := by rw [hRUU]; exact le_sup_left
  have hCU : centerOf (thompsonJ S) ≤ blockU L := by rw [← hZR]; exact inf_le_left
  have hZL : blockZ L = ⊥ := by rw [blockZ_eq_centerOf hcfg.charTwo_L hOL]; exact hc
  have hUcond : ∀ ℓ : L, (ℓ : G) ∈ blockU L ↔ A.α ℓ = 1 := fun ℓ => by
    rw [← hOL]; exact A.mem_pCoreOf_iff ℓ
  have hβk : ∀ u : blockU L, A.β u = 1 ↔ (u : G) ∈ blockZ L := fun u => by
    rw [← MonoidHom.mem_ker, A.β_ker, Subgroup.mem_subgroupOf]
  obtain ⟨γ₃, hγ₃s, hγ₃k, hγ₃v⟩ := exists_gamma_top A hUcond
  obtain ⟨N', hN'U, γ₂, γ₁, hγ₂s, hγ₂k, hγ₂v, hγ₁s, hγ₁k, hγ₁v, hmemN⟩ :=
    exists_gamma_mid A.β A.β_surj hβk
  have hfN' : ∀ x ∈ N', f * x * f⁻¹ ∈ N' := by
    intro x hx
    obtain ⟨hxU, hx1⟩ := (hmemN x).1 hx
    refine (hmemN _).2 ⟨hfU x hxU, ?_⟩
    have h1 := hU ⟨x, hxU⟩
    rw [hx1, map_zero, mul_zero] at h1
    exact h1
  have hfbot : ∀ x ∈ (⊥ : Subgroup G), f * x * f⁻¹ ∈ (⊥ : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_bot.1 hx]
    simp
  have hTrBot : ∀ x ∈ (⊥ : Subgroup G), (f * x) * (f * x) = 1 →
      ∃ m ∈ (⊥ : Subgroup G), m⁻¹ * f * m = f * x := by
    intro x hx _
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [Subgroup.mem_bot.1 hx]
    simp
  have hbotab : ∀ a ∈ (⊥ : Subgroup G), ∀ b ∈ (⊥ : Subgroup G), a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  have hbotsq : ∀ a ∈ (⊥ : Subgroup G), a * a = 1 := by
    intro a ha
    rw [Subgroup.mem_bot.1 ha]
    simp
  obtain ⟨hTr1, hcard1⟩ := layer_step σ (c' * a) hK2 hσσ θ hθ hc1 (bot_le : (⊥ : Subgroup G) ≤ N')
    hff hfN' hfbot γ₁ hγ₁s (fun y => by rw [hγ₁k, hZL])
    (fun y => by
      rw [hγ₁v, hγ₁v]
      obtain ⟨hyU, hy1⟩ := (hmemN y).1 y.2
      exact hN ⟨y, hyU⟩ hy1)
    hbotab hbotsq hTrBot
  obtain ⟨hTr2, hcard2⟩ := layer_step σ (c' * a⁻¹) hK2 hσσ θ hθ hc2 hN'U hff hfU hfN' γ₂ hγ₂s
    hγ₂k (fun u => by rw [hγ₂v, hγ₂v]; exact hU u)
    (fun x hx y hy => IsElemAbelian.comm hUel (hN'U hx) (hN'U hy))
    (fun x hx => by rw [← sq]; exact hUel.2 x (hN'U hx)) hTr1
  obtain ⟨hTr3, hcard3⟩ := layer_step σ (a * a) hK2 hσσ θ hθ hc3 hUR hff hfR hfU γ₃ hγ₃s hγ₃k
    (fun r => by rw [hγ₃v, hγ₃v]; exact hT ⟨r, A.P_le r.2⟩ r.2)
    (fun x hx y hy => IsElemAbelian.comm hUel hx hy)
    (fun x hx => by rw [← sq]; exact hUel.2 x hx) hTr2
  have hZR' : centerOf (thompsonJ S) = N' :=
    centerOf_eq_of_coordinates A hZL hLU hUR hCU hmemN
  have hlin : lin2Z L (thompsonJ S) = N' := by
    rw [← hZR']; simp [lin2Z, hc]
  have hb1 : Nat.card ((⊥ : Subgroup G) ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = 1 := by
    rw [bot_inf_eq]; exact Subgroup.card_bot
  have hN1 : Nat.card (N' ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = 2 ^ m := by
    rw [hcard1, hb1, hfixcard _ hc1, one_mul]
  have hU1 : Nat.card (blockU L ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
      2 ^ (m + m) := by
    rw [hcard2, hN1, hfixcard _ hc2, pow_add]
  have hR1 : Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) =
      2 ^ (3 * m) := by
    rw [hcard3, hU1, hfixcard _ hc3, ← pow_add]
    congr 1
    omega
  have e1 : n / 2 = m := by omega
  have e2 : 3 * n / 2 = 3 * m := by omega
  refine ⟨fun r hr hr2 => hTr3 r hr (by rw [← sq]; exact hr2), ?_, ?_, hTr2⟩
  · rw [hlin, e1]; exact hN1
  · rw [e2]; exact hR1

end Counts

end CFSG.QuasithinUnique.Lin2
