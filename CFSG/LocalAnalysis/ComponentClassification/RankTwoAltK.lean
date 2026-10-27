module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltNormal

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {x : G} (h : ∀ t ∈ H, x * t * x⁻¹ ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  refine eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

@[expose] def NormalizesV {n : ℕ} (h : 4 ≤ n) (π : Perm (Fin n)) : Prop :=
  ∀ k ∈ kleinFour, π * viaEmbeddingHom (fourEmb h) k * π⁻¹ ∈ rootVP n

theorem normalizesV_viaEmbeddingHom {n : ℕ} (h : 4 ≤ n) (k : Perm (Fin 4)) :
    NormalizesV h (viaEmbeddingHom (fourEmb h) k) := by
  intro m hm
  rw [rootVP_eq h, ← map_inv, ← map_mul, ← map_mul]
  exact ⟨_, conj_mem_kleinFour k hm, rfl⟩

theorem normalizesV_mul_swap {n : ℕ} (h : 4 ≤ n) {r s : Fin n}
    (hr : r ∉ Set.range (fourEmb h)) (hs : s ∉ Set.range (fourEmb h)) (k : Perm (Fin 4)) :
    NormalizesV h (viaEmbeddingHom (fourEmb h) k * swap r s) := by
  intro m hm
  rw [conj_mul_swap _ hr hs, rootVP_eq h]
  exact ⟨_, conj_mem_kleinFour k hm, rfl⟩

section Sec3Facts

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem normalizer_T_le : normalizer (T : Set G) ≤ normalizer (rightConjugate A g : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKt := tightlyEmbedded_rightConjugate' (tightlyEmbedded_centralizer_of_standard
    hc.hyp.standard) g
  intro x hx
  have h1 := normalizer_two_subgroup_le _ T hKt hc.sylowT.isPGroup hc.sylowT.le hc.T_ne_bot hx
  rw [mem_normalizer_rightConjugate_iff] at h1 ⊢
  rwa [normalizer_centralizer_eq hc.hyp.standard] at h1

theorem normalizer_R_le : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKt := tightlyEmbedded_centralizer_of_standard hc.hyp.standard
  intro x hx
  have h1 := normalizer_two_subgroup_le _ R hKt hc.sylowR.isPGroup hc.sylowR.le hc.R_ne_bot hx
  rwa [normalizer_centralizer_eq hc.hyp.standard] at h1

theorem commute_of_mem_B {x t : G} (hx : x ∈ rightConjugate A g) (ht : t ∈ T) :
    x * t = t * x := by
  have htK : t ∈ Subgroup.centralizer (rightConjugate A g : Set G) := by
    rw [centralizer_rightConjugate]
    exact hc.sylowT.le ht
  exact (mem_centralizer_iff.mp htK x hx)

end Sec3Facts

namespace NormPair

variable {A R T : Subgroup G} {g : G} {n : ℕ} (np : NormPair A R T g n)
include np

omit [Finite G] in
theorem exists_T_of_mem {σ : Perm (Fin n)} (hσ : σ ∈ rootVP n) :
    ∃ t : normalizer (A : Set G), (t : G) ∈ T ∧ np.ψA t = σ := by
  rw [← np.map_T] at hσ
  obtain ⟨t, ht, rfl⟩ := hσ
  exact ⟨t, ht, rfl⟩

omit [Finite G] in
theorem exists_R_of_mem {σ : Perm (Fin n)} (hσ : σ ∈ rootVP n) :
    ∃ r : normalizer (rightConjugate A g : Set G), (r : G) ∈ R ∧ np.ψB r = σ := by
  rw [← np.map_R] at hσ
  obtain ⟨r, hr, rfl⟩ := hσ
  exact ⟨r, hr, rfl⟩

omit [Finite G] in
theorem ψA_mem_of_T {t : normalizer (A : Set G)} (ht : (t : G) ∈ T) : np.ψA t ∈ rootVP n := by
  rw [← np.map_T]
  exact ⟨t, ht, rfl⟩

omit [Finite G] in
theorem ψB_mem_of_R {r : normalizer (rightConjugate A g : Set G)} (hr : (r : G) ∈ R) :
    np.ψB r ∈ rootVP n := by
  rw [← np.map_R]
  exact ⟨r, hr, rfl⟩

theorem mem_normalizer_T (h : 4 ≤ n) {x : normalizer (A : Set G)} (hx : (x : G) ∈ A)
    (hxV : NormalizesV h (np.ψA x)) : (x : G) ∈ normalizer (T : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro t ht
  have htN : t ∈ normalizer (A : Set G) := le_normalizer (np.le_A ht)
  have h1 : np.ψA (x * ⟨t, htN⟩ * x⁻¹) ∈ rootVP n := by
    have hψt := np.ψA_mem_of_T (t := ⟨t, htN⟩) ht
    rw [rootVP_eq h] at hψt
    obtain ⟨k, hk, hke⟩ := hψt
    rw [map_mul, map_mul, map_inv, ← hke]
    exact hxV k hk
  obtain ⟨t', ht', ht'e⟩ := np.exists_T_of_mem h1
  have heq := np.injA (np.le_A ht') (mul_mem (mul_mem hx (np.le_A ht)) (inv_mem hx)) ht'e
  have : (t' : G) = x * t * (x : G)⁻¹ := congrArg Subtype.val heq
  rw [← this]
  exact ht'

theorem mem_normalizer_R (h : 4 ≤ n) {x : normalizer (rightConjugate A g : Set G)}
    (hx : (x : G) ∈ rightConjugate A g) (hxV : NormalizesV h (np.ψB x)) :
    (x : G) ∈ normalizer (R : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro r hr
  have hrN : r ∈ normalizer (rightConjugate A g : Set G) := le_normalizer (np.le_B hr)
  have h1 : np.ψB (x * ⟨r, hrN⟩ * x⁻¹) ∈ rootVP n := by
    have hψr := np.ψB_mem_of_R (r := ⟨r, hrN⟩) hr
    rw [rootVP_eq h] at hψr
    obtain ⟨k, hk, hke⟩ := hψr
    rw [map_mul, map_mul, map_inv, ← hke]
    exact hxV k hk
  obtain ⟨r', hr', hr'e⟩ := np.exists_R_of_mem h1
  have heq := np.injB (np.le_B hr') (mul_mem (mul_mem hx (np.le_B hr)) (inv_mem hx)) hr'e
  have : (r' : G) = x * r * (x : G)⁻¹ := congrArg Subtype.val heq
  rw [← this]
  exact hr'

variable (hc : Sec3 A R T g)
include hc

theorem YT_le (hn : 7 ≤ n) {y : normalizer (A : Set G)} (hy : (y : G) ∈ A)
    (hyY : np.ψA y ∈ rootAltP n) : (y : G) ∈ Subgroup.centralizer (rightConjugate A g : Set G) := by
  have h4 : 4 ≤ n := by omega
  rw [rootAltP_eq h4] at hyY
  obtain ⟨k₀, hk₀, hk₀y⟩ := hyY
  have hyB : (y : G) ∈ normalizer (rightConjugate A g : Set G) :=
    normalizer_T_le hc (np.mem_normalizer_T h4 hy (by
      rw [← hk₀y]
      exact normalizesV_viaEmbeddingHom h4 k₀))
  set yB : normalizer (rightConjugate A g : Set G) := ⟨y, hyB⟩
  have hkey : ∀ x : normalizer (rightConjugate A g : Set G), (x : G) ∈ rightConjugate A g →
      NormalizesV h4 (np.ψB x) → Commute (np.ψB yB) (np.ψB x) := by
    intro x hx hxV
    have hxA : (x : G) ∈ normalizer (A : Set G) :=
      normalizer_R_le hc (np.mem_normalizer_R h4 hx hxV)
    set xA : normalizer (A : Set G) := ⟨x, hxA⟩
    have hcomm : ∀ k ∈ kleinFour, Commute (np.ψA xA) (viaEmbeddingHom (fourEmb h4) k) := by
      intro k hk
      obtain ⟨t, ht, hte⟩ := np.exists_T_of_mem (show viaEmbeddingHom (fourEmb h4) k ∈ rootVP n by
        rw [rootVP_eq h4]
        exact ⟨k, hk, rfl⟩)
      rw [← hte, Commute, SemiconjBy, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (commute_of_mem_B hc hx ht)
    obtain ⟨v, hv, hvx⟩ := exists_kleinFour_of_commute (fourEmb h4)
      (hcomm _ swap_mem_kleinFour_one) (hcomm _ swap_mem_kleinFour_two)
    obtain ⟨t, ht, hte⟩ := np.exists_T_of_mem (show viaEmbeddingHom (fourEmb h4) v ∈ rootVP n by
      rw [rootVP_eq h4]
      exact ⟨v, hv, rfl⟩)
    have hfix : ∀ i, np.ψA (t⁻¹ * xA) (fourEmb h4 i) = fourEmb h4 i := by
      intro i
      rw [map_mul, map_inv, Perm.mul_apply, hvx, hte, Perm.inv_eq_iff_eq,
        viaEmbeddingHom_apply_image]
    have hcy : (t⁻¹ * xA) * y = y * (t⁻¹ * xA) := by
      have h1 : np.ψA ((t⁻¹ * xA) * y * (t⁻¹ * xA)⁻¹) = np.ψA y := by
        rw [map_mul, map_mul, map_inv, ← hk₀y,
          (commute_of_apply_eq (fourEmb h4) hfix k₀).eq, mul_inv_cancel_right]
      have hmem : (((t⁻¹ * xA) * y * (t⁻¹ * xA)⁻¹ : normalizer (A : Set G)) : G) ∈ A := by
        have htx : (((t⁻¹ * xA : normalizer (A : Set G))) : G) ∈ normalizer (A : Set G) :=
          (t⁻¹ * xA).2
        exact (mem_normalizer_iff.mp htx y).mp hy
      have h2 := np.injA hmem hy h1
      calc (t⁻¹ * xA) * y = ((t⁻¹ * xA) * y * (t⁻¹ * xA)⁻¹) * (t⁻¹ * xA) := by group
        _ = y * (t⁻¹ * xA) := by rw [h2]
    have htB : (t : G) ∈ normalizer (rightConjugate A g : Set G) :=
      normalizer_T_le hc ((le_normalizer : T ≤ normalizer (T : Set G)) ht)
    have ht1 : np.ψB ⟨t, htB⟩ = 1 := by
      rw [np.hψB.eq_one_iff, centralizer_rightConjugate]
      exact hc.sylowT.le ht
    have hc' : (⟨t, htB⟩ : normalizer (rightConjugate A g : Set G))⁻¹ * x * yB =
        yB * ((⟨t, htB⟩ : normalizer (rightConjugate A g : Set G))⁻¹ * x) := by
      apply Subtype.ext
      have := congrArg Subtype.val hcy
      simpa [xA, yB] using this
    have h3 := congrArg np.ψB hc'
    rw [map_mul, map_mul, map_inv, ht1, inv_one, one_mul, map_mul, map_mul, map_inv, ht1,
      inv_one, one_mul] at h3
    exact h3.symm
  have hone : np.ψB yB = 1 := by
    apply eq_one_of_commute_stab (fourEmb h4) (by simp only [Fintype.card_fin]; omega)
    · intro k hk
      obtain ⟨x, hx, hxe⟩ := np.hψB.exists_eq _ (viaEmbeddingHom_mem_alternatingGroup' _ hk)
      rw [← hxe]
      exact hkey _ hx (by rw [hxe]; exact normalizesV_viaEmbeddingHom h4 k)
    · intro r s hr hs hrs
      have h01 : (0 : Fin 4) ≠ 1 := by decide
      have hmem := mul_swap_mem_alternatingGroup (fourEmb h4) hrs h01
      obtain ⟨x, hx, hxe⟩ := np.hψB.exists_eq _ hmem
      rw [← viaEmbeddingHom_swap, ← hxe]
      exact hkey _ hx (by rw [hxe]; exact normalizesV_mul_swap h4 hr hs _)
  exact (np.hψB.eq_one_iff yB).mp hone

theorem YR_le (hn : 7 ≤ n) {y : normalizer (rightConjugate A g : Set G)}
    (hy : (y : G) ∈ rightConjugate A g) (hyY : np.ψB y ∈ rootAltP n) :
    (y : G) ∈ Subgroup.centralizer (A : Set G) := by
  have hyA : g * (y : G) * g⁻¹ ∈ A := (mem_rightConjugate_iff A g y).mp hy
  have hback : conjNInv A g (conjN A g y) = y := by
    apply Subtype.ext
    rw [conjNInv_coe, conjN_coe]
    group
  have h := np.swap.YT_le hc.swap hn (y := conjN A g y) hyA (by
    rw [swap_ψA, hback]
    exact hyY)
  rw [centralizer_rightConjugate, mem_rightConjugate_iff, conjN_coe] at h
  simpa [mul_assoc] using h

theorem ψB_apply_of_mem_A (hn : 7 ≤ n) {x : normalizer (rightConjugate A g : Set G)}
    (hx : (x : G) ∈ A) (i : Fin 4) :
    np.ψB x (fourEmb (by omega : 4 ≤ n) i) = fourEmb (by omega : 4 ≤ n) i := by
  have h4 : 4 ≤ n := by omega
  refine apply_eq_of_commute_alternating (fourEmb h4) (fun k hk => ?_) i
  obtain ⟨y, hy, hye⟩ := np.hψB.exists_eq _ (viaEmbeddingHom_mem_alternatingGroup' (fourEmb h4) hk)
  have hyK := np.YR_le hc hn (y := ⟨y, le_normalizer hy⟩) hy (by
    rw [hye, rootAltP_eq h4]
    exact ⟨k, hk, rfl⟩)
  rw [← hye, Commute, SemiconjBy, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp hyK x hx)

theorem ψA_apply_of_mem_B (hn : 7 ≤ n) {y : normalizer (A : Set G)}
    (hy : (y : G) ∈ rightConjugate A g) (i : Fin 4) :
    np.ψA y (fourEmb (by omega : 4 ≤ n) i) = fourEmb (by omega : 4 ≤ n) i := by
  have h4 : 4 ≤ n := by omega
  refine apply_eq_of_commute_alternating (fourEmb h4) (fun k hk => ?_) i
  obtain ⟨x, hx, hxe⟩ := np.hψA.exists_eq _ (viaEmbeddingHom_mem_alternatingGroup' (fourEmb h4) hk)
  have hxK := np.YT_le hc hn (y := ⟨x, le_normalizer hx⟩) hx (by
    rw [hxe, rootAltP_eq h4]
    exact ⟨k, hk, rfl⟩)
  rw [← hxe, Commute, SemiconjBy, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp hxK y hy)

end NormPair

end CFSG.ComponentClassification.RankTwoAlt
