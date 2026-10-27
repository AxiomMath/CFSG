module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AM13C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q14D

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q14_conj_F {g : G} (hg : g ∈ l41M t x₁ x₂ rho) {f : G} (hf : f ∈ l41F t x₁ x₂ rho) :
    g * f * g⁻¹ ∈ l41F t x₁ x₂ rho :=
  (Subgroup.mem_normalizer_iff.mp hg f).mp hf

theorem q14_F_isPGroup (h : L41GPh8 t L S x₁ x₂ lam rho) : IsPGroup 2 (l41F t x₁ x₂ rho) :=
  IsPGroup.of_card (by rw [m13_card_F h])

theorem q14_F_le_M (t x₁ x₂ rho : G) : l41F t x₁ x₂ rho ≤ l41M t x₁ x₂ rho :=
  Subgroup.le_normalizer

theorem q14_t_mem_F (t x₁ x₂ rho : G) : t ∈ l41F t x₁ x₂ rho :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem q14_K_le_M (h : L41GPh8 t L S x₁ x₂ lam rho) :
    closure {rho, lam} ≤ l41M t x₁ x₂ rho :=
  (n4_K_le_N h.toL41GPh1).trans (m13_N_le_M h)

theorem q14_rho_mem_M (h : L41GPh8 t L S x₁ x₂ lam rho) : rho ∈ l41M t x₁ x₂ rho :=
  q14_K_le_M h (Subgroup.subset_closure (by simp))

theorem q14_lam_mem_M (h : L41GPh8 t L S x₁ x₂ lam rho) : lam ∈ l41M t x₁ x₂ rho :=
  q14_K_le_M h (Subgroup.subset_closure (by simp))

theorem q14_card_K (h : L41GPh1 t L S x₁ x₂ lam rho) :
    Nat.card ↥(closure {rho, lam}) = 6 := by
  obtain ⟨e⟩ := h.basic.sigma3
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

theorem q14_card_W (h : L41GPh5 t L S x₁ x₂ lam rho) : Nat.card (ctxW t x₁ x₂) = 32 := by
  have hP : twoCore t = zpowers t := h.p2
  have hcP : Nat.card (twoCore t) = 2 := by
    rw [hP, Nat.card_zpowers, h.hyp.ord_t]
  have hW := pt_card_W h.toCtx0
  rw [hcP] at hW
  omega

theorem q14_normalizer_V_le_M (h : L41GPh10 t L S x₁ x₂ lam rho) :
    normalizer ((l41V S t x₁ x₂ : Subgroup G) : Set G) ≤ l41M t x₁ x₂ rho := by
  intro n hn
  refine mem_normalizer_of_conj_mem fun f hf => ?_
  exact m11_autInv_F h ((l41V S t x₁ x₂).normalizerMonoidHom ⟨n, hn⟩)
    ⟨f, m11_F_le_V h.toL41GPh8 hf⟩ hf

theorem q14_card_M (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nat.card (l41M t x₁ x₂ rho) = 3072 := by
  rcases m13_card_M_cases h with h768 | h3072
  swap
  · exact h3072
  exfalso
  obtain ⟨Sy, hVS⟩ := exists_sylow_gt h.normalizerFacts.V_pGroup h.normalizerFacts.V_not_sylow
  obtain ⟨n, hnSy, hnN, hnV⟩ := exists_mem_normalizer_not_mem Sy.isPGroup' hVS
  have hnM : n ∈ l41M t x₁ x₂ rho := q14_normalizer_V_le_M h hnN
  have hUSy : l41V S t x₁ x₂ ⊔ zpowers n ≤ (Sy : Subgroup G) :=
    sup_le hVS.le (Subgroup.zpowers_le.mpr hnSy)
  have hUp : IsPGroup 2 ↥(l41V S t x₁ x₂ ⊔ zpowers n) := Sy.isPGroup'.to_le hUSy
  have hUM : l41V S t x₁ x₂ ⊔ zpowers n ≤ l41M t x₁ x₂ rho :=
    sup_le (h.normalizerFacts.V_le.trans (m13_N_le_M h.toL41GPh8))
      (Subgroup.zpowers_le.mpr hnM)
  have hVU : l41V S t x₁ x₂ < l41V S t x₁ x₂ ⊔ zpowers n :=
    lt_of_le_of_ne le_sup_left fun heq =>
      hnV (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hUp)
  have hlt := Subgroup.card_lt_of_lt hVU
  have hdvd := Subgroup.card_dvd_of_le hUM
  rw [m11_card_V h.toL41GPh8] at hlt
  rw [hk, h768] at hdvd
  have hk9 : 9 ≤ k := by
    by_contra hk8
    have : 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h512 : 2 ^ 9 ∣ 2 ^ k := pow_dvd_pow 2 hk9
  have := h512.trans hdvd
  omega

theorem q14_card_cent_M_t (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nat.card ↥(l41M t x₁ x₂ rho ⊓ centralizer ({t} : Set G)) = 192 := by
  have hC : l41M t x₁ x₂ rho ⊓ centralizer ({t} : Set G) =
      l41N t x₁ x₂ ⊓ centralizer ({t} : Set G) := by
    apply le_antisymm
    · have h1 : invCent t ⊓ l41M t x₁ x₂ rho ≤ l41N t x₁ x₂ := by
        rw [m13_cent_M_t h]
        exact sup_le (n4_W_le_N h.toL41GPh1) (n4_K_le_N h.toL41GPh1)
      intro g hg
      obtain ⟨hgM, hgc⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr ⟨h1 (Subgroup.mem_inf.mpr ⟨hgc, hgM⟩), hgc⟩
    · exact inf_le_inf_right _ (m13_N_le_M h.toL41GPh8)
  have h2 := m13_card_conjIn_mul (l41N t x₁ x₂) t
  rw [h.normalizerFacts.orbit_t] at h2
  have h4 : (t • (fourGrp x₁ x₂ : Set G)).ncard = 4 := by
    rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq]
    exact n4_card_four h.toCtx0
  rw [h4, m13_card_N h.toL41GPh8, ← hC] at h2
  omega

end Q14D

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
