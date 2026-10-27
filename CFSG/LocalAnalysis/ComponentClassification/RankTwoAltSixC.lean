module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixCoords

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

theorem a6c013_mem_rootAlt : a6c013 ∈ rootAlt 6 := by
  rw [mem_rootAlt_iff (by decide)]
  refine ⟨swap 0 1 * swap 1 3, mem_alternatingGroup.mpr (by decide), ?_⟩
  rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
  rfl

theorem cube_mem_kleinFour :
    ∀ k : Perm (Fin 4), sign k = 1 → ∃ i : Fin 4, k * k * k = kOf i := by
  decide

theorem cube_mem_rootV {z : alternatingGroup (Fin 6)} (hz : z ∈ rootAlt 6) :
    z * z * z ∈ rootV 6 := by
  obtain ⟨k, hk, hkz⟩ := (mem_rootAlt_iff (by decide) z).mp hz
  obtain ⟨i, hi⟩ := cube_mem_kleinFour k (mem_alternatingGroup.mp hk)
  rw [mem_rootV_iff (by decide)]
  exact ⟨kOf i, kOf_mem i, by rw [← hi, map_mul, map_mul, hkz]; rfl⟩

theorem stabO_of_fix45 {π : Perm (Fin 6)} (h4 : π 4 = 4) (h5 : π 5 = 5) : StabO π := by
  have key : ∀ i : Fin 6, (i : ℕ) < 4 → ((π i : Fin 6) : ℕ) < 4 := by
    intro i hi
    have hne4 : ((π i : Fin 6) : ℕ) ≠ 4 := fun h => by
      have := π.injective ((Fin.ext h : π i = 4).trans h4.symm)
      rw [this] at hi
      exact absurd hi (by decide)
    have hne5 : ((π i : Fin 6) : ℕ) ≠ 5 := fun h => by
      have := π.injective ((Fin.ext h : π i = 5).trans h5.symm)
      rw [this] at hi
      exact absurd hi (by decide)
    have := (π i).isLt
    omega
  intro i
  by_cases hi : 4 ≤ (i : ℕ)
  · rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
    · rw [show i = 4 from Fin.ext h, h4]
    · rw [show i = 5 from Fin.ext h, h5]
  · push Not at hi
    have := key i hi
    constructor <;> intro h <;> omega

theorem apply45_of_stabO {σ : Perm (Fin 6)} (hs : StabO σ) :
    (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4) := by
  have h4 := (hs 4).mpr (by decide)
  have h5 := (hs 5).mpr (by decide)
  have hne : ((σ 4 : Fin 6) : ℕ) ≠ σ 5 := fun h => absurd (σ.injective (Fin.ext h)) (by decide)
  have l4 := (σ 4).isLt
  have l5 := (σ 5).isLt
  rcases (by omega : ((σ 4 : ℕ) = 4 ∧ (σ 5 : ℕ) = 5) ∨ ((σ 4 : ℕ) = 5 ∧ (σ 5 : ℕ) = 4)) with
    ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨Fin.ext a, Fin.ext b⟩
  · exact Or.inr ⟨Fin.ext a, Fin.ext b⟩

theorem apply45_of_commute {σ : Perm (Fin 6)} (h : σ * swap 4 5 = swap 4 5 * σ) :
    (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4) := by
  have e : σ 5 = swap 4 5 (σ 4) := by
    have := DFunLike.congr_fun h 4
    rwa [Perm.mul_apply, Perm.mul_apply, swap_apply_left] at this
  by_cases h4 : σ 4 = 4
  · exact Or.inl ⟨h4, by rw [e, h4, swap_apply_left]⟩
  · by_cases h5 : σ 4 = 5
    · exact Or.inr ⟨h5, by rw [e, h5, swap_apply_right]⟩
    · exfalso
      rw [swap_apply_of_ne_of_ne h4 h5] at e
      exact absurd (σ.injective e) (by decide)

theorem restrictO_eq_one_of {σ : Perm (Fin 6)} (hs : StabO σ) (h4 : σ 4 = 4) (h5 : σ 5 = 5) :
    restrictO σ = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : 4 ≤ (i : ℕ)
  · rw [restrictO_apply_of_ge hs hi]
    rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
    · rw [show i = 4 from Fin.ext h, h4]
      rfl
    · rw [show i = 5 from Fin.ext h, h5]
      rfl
  · push Not at hi
    rw [restrictO_apply_of_lt hs hi]
    rfl

theorem restrictO_eq_swap45_of {σ : Perm (Fin 6)} (hs : StabO σ) (h4 : σ 4 = 5) (h5 : σ 5 = 4) :
    restrictO σ = swap 4 5 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : 4 ≤ (i : ℕ)
  · rw [restrictO_apply_of_ge hs hi]
    rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
    · rw [show i = 4 from Fin.ext h, h4, swap_apply_left]
    · rw [show i = 5 from Fin.ext h, h5, swap_apply_right]
  · push Not at hi
    rw [restrictO_apply_of_lt hs hi, swap_apply_of_ne_of_ne]
    · intro h
      rw [h] at hi
      exact absurd hi (by decide)
    · intro h
      rw [h] at hi
      exact absurd hi (by decide)

@[expose] def NormV6 (z : alternatingGroup (Fin 6)) : Prop :=
  ∀ u ∈ rootV 6, z * u * z⁻¹ ∈ rootV 6

theorem normV6_of_stabO {z : alternatingGroup (Fin 6)} (hz : StabO (z : Perm (Fin 6))) :
    NormV6 z := by
  intro u hu
  obtain ⟨k, hk, hku⟩ := (mem_rootV_iff (by decide) u).mp hu
  have h2 := normalizesV_of_stabO (by decide : 4 ≤ 6) hz k hk
  rw [hku, rootVP, Subgroup.mem_map] at h2
  obtain ⟨w, hw, hwe⟩ := h2
  have : w = z * u * z⁻¹ := Subtype.ext hwe
  rw [← this]
  exact hw

theorem normV6_of_mem_rootAlt {z : alternatingGroup (Fin 6)} (hz : z ∈ rootAlt 6) : NormV6 z := by
  obtain ⟨h4, h5⟩ := apply_four_five_of_mem_rootAlt hz
  exact normV6_of_stabO (stabO_of_fix45 h4 h5)

theorem conjPerm_swap45_ne_one : conjPerm 6 (swap 4 5) ≠ 1 := fun h => by
  have := conjPerm_injective (n := 6) (by decide) (h.trans (map_one _).symm)
  exact absurd this (by decide)

theorem conjPerm_swap45_mul_self : conjPerm 6 (swap 4 5) * conjPerm 6 (swap 4 5) = 1 := by
  rw [← map_mul, swap_mul_self, map_one]

@[expose] def s0145 : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩

theorem stabO_s0145 : StabO (s0145 : Perm (Fin 6)) :=
  (restrictO_swap01_mul_swap (by decide : 4 ≤ 6) (a := 4) (b := 5) (by decide) (by decide)).1

theorem fix_four_of_sylow {K : Type*} [Group K] [Finite K] (Q : Sylow 2 K)
    (f : K →* Perm (Fin 6)) (hf : ∀ k, f k * swap 4 5 = swap 4 5 * f k)
    (hQ : ∀ q ∈ (Q : Subgroup K), f q 4 = 4) (k : K) : f k 4 = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h45 : ∀ k, (f k 4 = 4 ∧ f k 5 = 5) ∨ (f k 4 = 5 ∧ f k 5 = 4) := fun k =>
    apply45_of_commute (hf k)
  set H : Subgroup K := (MulAction.stabilizer (Perm (Fin 6)) (4 : Fin 6)).comap f with hH
  have hmem : ∀ k, k ∈ H ↔ f k 4 = 4 := fun k => by
    rw [hH, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    rfl
  by_contra hk
  have hk5 : f k 4 = 5 := ((h45 k).resolve_left (fun h => hk h.1)).1
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨k, fun b => ?_⟩
    rw [hmem, hmem, map_mul, Perm.mul_apply, hk5]
    rcases h45 b with ⟨hb4, hb5⟩ | ⟨hb4, hb5⟩
    · rw [hb5, hb4]
      exact Or.inr ⟨rfl, by decide⟩
    · rw [hb5, hb4]
      exact Or.inl ⟨rfl, by decide⟩
  have hle : (Q : Subgroup K) ≤ H := fun q hq => (hmem q).mpr (hQ q hq)
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  exact Q.not_dvd_index hdvd

namespace SixPair

variable {G : Type} [Group G] {A R T : Subgroup G} {g : G} (np : SixPair A R T g)
include np

theorem exists_T_of_mem {z : alternatingGroup (Fin 6)} (hz : z ∈ rootV 6) :
    ∃ t : ↥A, (t : G) ∈ T ∧ np.ψA t = z :=
  ⟨np.ψA.symm z, (np.mem_T _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hz),
    MulEquiv.apply_symm_apply _ _⟩

theorem exists_R_of_mem {z : alternatingGroup (Fin 6)} (hz : z ∈ rootV 6) :
    ∃ r : ↥(rightConjugate A g), (r : G) ∈ R ∧ np.ψB r = z :=
  ⟨np.ψB.symm z, (np.mem_R _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hz),
    MulEquiv.apply_symm_apply _ _⟩

variable [Finite G]

theorem eq_one_of_mem_T_of_mem_B (hc : Sec3 A R T g) {z : G} (hzT : z ∈ T)
    (hzB : z ∈ rightConjugate A g) : z = 1 :=
  eq_one_of_mem_centralizer_six np.ψB hzB (by
    rw [centralizer_rightConjugate]
    exact hc.sylowT.le hzT)

theorem mem_normalizer_T (x : ↥A) (hx : NormV6 (np.ψA x)) : (x : G) ∈ normalizer (T : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro t ht
  have htA := np.le_A ht
  have h1 : np.ψA (x * ⟨t, htA⟩ * x⁻¹) ∈ rootV 6 := by
    rw [map_mul, map_mul, map_inv]
    exact hx _ ((np.mem_T ⟨t, htA⟩).mp ht)
  exact (np.mem_T _).mpr h1

theorem mem_normalizer_R (x : ↥(rightConjugate A g)) (hx : NormV6 (np.ψB x)) :
    (x : G) ∈ normalizer (R : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro r hr
  have hrB := np.le_B hr
  have h1 : np.ψB (x * ⟨r, hrB⟩ * x⁻¹) ∈ rootV 6 := by
    rw [map_mul, map_mul, map_inv]
    exact hx _ ((np.mem_R ⟨r, hrB⟩).mp hr)
  exact (np.mem_R _).mpr h1

variable (hc : Sec3 A R T g)
include hc

theorem YT_le (y : ↥A) (hyY : np.ψA y ∈ rootAlt 6) :
    (y : G) ∈ centralizer (rightConjugate A g : Set G) := by
  have hyT := np.mem_normalizer_T y (normV6_of_mem_rootAlt hyY)
  have hyB : (y : G) ∈ normalizer (rightConjugate A g : Set G) := normalizer_T_le hc hyT
  set yB : normalizer (rightConjugate A g : Set G) := ⟨y, hyB⟩ with hyBdef
  have hfix : ∀ w ∈ rootAlt 6, actAut np.ψB yB w = w := by
    intro w hw
    set x := np.ψB.symm w with hxdef
    have hψx : np.ψB x = w := MulEquiv.apply_symm_apply _ _
    have hxR : (x : G) ∈ normalizer (R : Set G) :=
      np.mem_normalizer_R x (by rw [hψx]; exact normV6_of_mem_rootAlt hw)
    have hxA : (x : G) ∈ normalizer (A : Set G) := normalizer_R_le hc hxR
    set xA : normalizer (A : Set G) := ⟨x, hxA⟩ with hxAdef
    have hfixV : ∀ u : alternatingGroup (Fin 6), InV0 (u : Perm (Fin 6)) →
        actAut np.ψA xA u = u := by
      intro u hu
      obtain ⟨t, htT, rfl⟩ := np.exists_T_of_mem (mem_rootV_six_iff.mpr (Or.inr hu))
      rw [actAut_apply]
      congr 1
      apply Subtype.ext
      show (x : G) * t * (x : G)⁻¹ = t
      rw [commute_of_mem_B hc x.2 htT, mul_inv_cancel_right]
    obtain ⟨v, hv, hve⟩ := exists_conj_of_fix_rootV _ hfixV
    have hvV' : v = 1 ∨ InV0 v := by
      rcases List.mem_cons.mp hv with h | h
      · exact Or.inl h
      · exact Or.inr (inV0_iff.mpr h)
    have hvA : v ∈ alternatingGroup (Fin 6) := by
      rcases hvV' with h | h
      · rw [h]
        exact one_mem _
      · exact mem_alternatingGroup.mpr (inV0_sign h)
    obtain ⟨t, htT, hte⟩ := np.exists_T_of_mem (z := ⟨v, hvA⟩) (mem_rootV_six_iff.mpr hvV')
    have hxyA : (x : G) * y * (x : G)⁻¹ ∈ A := (mem_normalizer_iff.mp hxA y).mp y.2
    have hxy : (x : G) * y * (x : G)⁻¹ = t * y * (t : G)⁻¹ := by
      have h1 : np.ψA ⟨(x : G) * y * (x : G)⁻¹, hxyA⟩ = np.ψA (t * y * t⁻¹) := by
        apply Subtype.ext
        rw [← actAut_apply np.ψA xA y, hve _ hyY, map_mul, map_mul, map_inv, hte]
        rfl
      exact congrArg Subtype.val (np.ψA.injective h1)
    have hz : (y : G) * x * (y : G)⁻¹ = x := by
      have hzT : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ T := by
        have e : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ = y * t * (y : G)⁻¹ * (t : G)⁻¹ := by
          calc (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ = y * ((x : G) * y * (x : G)⁻¹)⁻¹ := by
                group
            _ = y * ((t : G) * y * (t : G)⁻¹)⁻¹ := by rw [hxy]
            _ = y * t * (y : G)⁻¹ * (t : G)⁻¹ := by group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.mp hyT t).mp htT) (inv_mem htT)
      have hzB : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ rightConjugate A g :=
        mul_mem ((mem_normalizer_iff.mp hyB x).mp x.2) (inv_mem x.2)
      have := np.eq_one_of_mem_T_of_mem_B hc hzT hzB
      rwa [mul_inv_eq_one] at this
    rw [← hψx, actAut_apply]
    congr 1
    exact Subtype.ext hz
  have h01 := eq_one_or_eq_conj45 (hfix _ a6c012_mem_rootAlt) (hfix _ a6c013_mem_rootAlt)
  have hy3 : actAut np.ψB (yB * yB * yB) = 1 := by
    rw [actAut_eq_one_iff, centralizer_rightConjugate]
    apply hc.sylowT.le
    show (y : G) * y * y ∈ T
    exact (np.mem_T (y * y * y)).mpr (by rw [map_mul, map_mul]; exact cube_mem_rootV hyY)
  rcases h01 with h | h
  · exact (actAut_eq_one_iff _ _).mp h
  · rw [map_mul, map_mul, h, conjPerm_swap45_mul_self, one_mul] at hy3
    exact absurd hy3 conjPerm_swap45_ne_one

theorem YR_le (y : ↥(rightConjugate A g)) (hyY : np.ψB y ∈ rootAlt 6) :
    (y : G) ∈ centralizer (A : Set G) := by
  have h := np.swap.YT_le hc.swap (conjEquiv A g y)
    (by rw [SixPair.swap_ψA, MulEquiv.symm_apply_apply]; exact hyY)
  rw [centralizer_rightConjugate, mem_rightConjugate_iff, conjEquiv_apply] at h
  rwa [show g⁻¹ * (g * (y : G) * g⁻¹) * g⁻¹⁻¹ = y by group] at h

theorem actAut_fix (x : ↥A) (hxB : (x : G) ∈ normalizer (rightConjugate A g : Set G)) :
    actAut np.ψB ⟨x, hxB⟩ = 1 ∨ actAut np.ψB ⟨x, hxB⟩ = conjPerm 6 (Equiv.swap 4 5) := by
  have hfix : ∀ z ∈ rootAlt 6, actAut np.ψB ⟨x, hxB⟩ z = z := by
    intro z hz
    set y := np.ψB.symm z with hydef
    have hψy : np.ψB y = z := MulEquiv.apply_symm_apply _ _
    have hyA := np.YR_le hc y (by rw [hψy]; exact hz)
    rw [← hψy, actAut_apply]
    congr 1
    apply Subtype.ext
    show (x : G) * y * (x : G)⁻¹ = y
    rw [mem_centralizer_iff.mp hyA _ x.2, mul_inv_cancel_right]
  exact eq_one_or_eq_conj45 (hfix _ a6c012_mem_rootAlt) (hfix _ a6c013_mem_rootAlt)

theorem mem_centralizer_of_fix45 (x : ↥A) (h4 : (np.ψA x : Perm (Fin 6)) 4 = 4)
    (h5 : (np.ψA x : Perm (Fin 6)) 5 = 5) :
    (x : G) ∈ centralizer (rightConjugate A g : Set G) := by
  apply np.YT_le hc x
  have h := mem_rootAltP_of_fix (by decide : 4 ≤ 6) (np.ψA x).2 (fun i hi => by
    rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
    · rw [show i = 4 from Fin.ext h]
      exact h4
    · rw [show i = 5 from Fin.ext h]
      exact h5)
  rw [rootAltP, Subgroup.mem_map] at h
  obtain ⟨w, hw, hwe⟩ := h
  rwa [show w = np.ψA x from Subtype.ext hwe] at hw

theorem actAut_x₁
    (hxB : ((np.ψA.symm s0145 : ↥A) : G) ∈ normalizer (rightConjugate A g : Set G)) :
    actAut np.ψB ⟨_, hxB⟩ = conjPerm 6 (Equiv.swap 4 5) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases np.actAut_fix hc _ hxB with h | h
  · exfalso
    have hxK := (actAut_eq_one_iff _ _).mp h
    set x := np.ψA.symm s0145 with hxdef
    have hψx : np.ψA x = s0145 := MulEquiv.apply_symm_apply _ _
    have hx2 : (x : G) * x = 1 := by
      have : x * x = 1 := np.ψA.injective (by rw [map_mul, hψx, map_one]; decide)
      exact congrArg Subtype.val this
    have hxN : (x : G) ∈ normalizer (T : Set G) :=
      np.mem_normalizer_T x (by rw [hψx]; exact normV6_of_stabO stabO_s0145)
    have hzp : IsPGroup 2 (zpowers (x : G)) := by
      have hdvd : orderOf (x : G) ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hx2])
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hsup : IsPGroup 2 ↥(T ⊔ zpowers (x : G)) :=
      IsPGroup.to_sup_of_normal_left' hc.sylowT.isPGroup hzp (zpowers_le.mpr hxN)
    have hxKg : (x : G) ∈ rightConjugate (centralizer (A : Set G)) g := by
      rw [← centralizer_rightConjugate]
      exact hxK
    have heq := hc.sylowT.eq_of_le le_sup_left (sup_le hc.sylowT.le (zpowers_le.mpr hxKg)) hsup
    have hxT : (x : G) ∈ T := heq ▸ (le_sup_right (a := T) (mem_zpowers (x : G)))
    have hV := (np.mem_T x).mp hxT
    rw [hψx, mem_rootV_six_iff] at hV
    revert hV
    decide
  · exact h

theorem actAut_of_stabO (x : ↥A) (hs : StabO (np.ψA x : Perm (Fin 6))) :
    ∃ hxB : (x : G) ∈ normalizer (rightConjugate A g : Set G),
      actAut np.ψB ⟨x, hxB⟩ = conjPerm 6 (restrictO (np.ψA x : Perm (Fin 6))) := by
  have hxB := normalizer_T_le hc (np.mem_normalizer_T x (normV6_of_stabO hs))
  refine ⟨hxB, ?_⟩
  rcases apply45_of_stabO hs with ⟨h4, h5⟩ | ⟨h4, h5⟩
  · rw [(actAut_eq_one_iff _ _).mpr (np.mem_centralizer_of_fix45 hc x h4 h5),
      restrictO_eq_one_of hs h4 h5, map_one]
  · set x₁ := np.ψA.symm s0145 with hx₁def
    have hψx₁ : np.ψA x₁ = s0145 := MulEquiv.apply_symm_apply _ _
    have hx₁B : (x₁ : G) ∈ normalizer (rightConjugate A g : Set G) :=
      normalizer_T_le hc (np.mem_normalizer_T x₁ (by rw [hψx₁]; exact normV6_of_stabO stabO_s0145))
    have hψ : (np.ψA (x * x₁) : Perm (Fin 6)) =
        (np.ψA x : Perm (Fin 6)) * (Equiv.swap 0 1 * Equiv.swap 4 5) := by
      rw [map_mul, Subgroup.coe_mul, hψx₁]
      rfl
    have hK := np.mem_centralizer_of_fix45 hc (x * x₁)
      (by rw [hψ, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
        swap_apply_of_ne_of_ne (by decide) (by decide), h5])
      (by rw [hψ, Perm.mul_apply, Perm.mul_apply, swap_apply_right,
        swap_apply_of_ne_of_ne (by decide) (by decide), h4])
    have e1 : actAut np.ψB ⟨x, hxB⟩ * actAut np.ψB ⟨x₁, hx₁B⟩ = 1 := by
      rw [← map_mul]
      exact (actAut_eq_one_iff _ _).mpr hK
    rw [np.actAut_x₁ hc hx₁B] at e1
    rw [mul_eq_one_iff_eq_inv.mp e1, ← map_inv, swap_inv, restrictO_eq_swap45_of hs h4 h5]

theorem exists_hom_K : ∃ f : ↥(centralizer (A : Set G)) →* Perm (Fin 6),
    (∀ k, f k 4 = 4 ∧ f k 5 = 5) ∧
    (∀ k : ↥(centralizer (A : Set G)),
      ∃ hkB : (k : G) ∈ normalizer (rightConjugate A g : Set G),
        actAut np.ψB ⟨k, hkB⟩ = conjPerm 6 (f k)) ∧
    (∀ (k : ↥(centralizer (A : Set G))) (hk : (k : G) ∈ rightConjugate A g),
      f k = np.ψB ⟨k, hk⟩) := by
  set K := centralizer (A : Set G) with hKdef
  have hKB : K ≤ normalizer (rightConjugate A g : Set G) :=
    NormPair.centralizer_le_normalizer_B hc np.le_A
  set F : ↥K →* MulAut (alternatingGroup (Fin 6)) :=
    (actAut np.ψB).comp (Subgroup.inclusion hKB) with hFdef
  set x₁ := np.ψA.symm s0145 with hx₁def
  have hψx₁ : np.ψA x₁ = s0145 := MulEquiv.apply_symm_apply _ _
  have hx₁B : (x₁ : G) ∈ normalizer (rightConjugate A g : Set G) :=
    normalizer_T_le hc (np.mem_normalizer_T x₁ (by rw [hψx₁]; exact normV6_of_stabO stabO_s0145))
  have hc45 := np.actAut_x₁ hc hx₁B
  have hcomm : ∀ k : ↥K, F k * conjPerm 6 (Equiv.swap 4 5) = conjPerm 6 (Equiv.swap 4 5) * F k := by
    intro k
    rw [← hc45]
    show actAut np.ψB (Subgroup.inclusion hKB k) * actAut np.ψB ⟨x₁, hx₁B⟩ =
      actAut np.ψB ⟨x₁, hx₁B⟩ * actAut np.ψB (Subgroup.inclusion hKB k)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.mp k.2 _ x₁.2).symm
  have hperm : ∀ k : ↥K, ∃ σ : Perm (Fin 6), σ * Equiv.swap 4 5 = Equiv.swap 4 5 * σ ∧
      F k = conjPerm 6 σ := by
    intro k
    obtain ⟨σ, hσ45, hσ⟩ := exists_perm_of_commute_swap45 (F k) (fun x => by
      have := DFunLike.congr_fun (hcomm k) x
      rwa [MulAut.mul_apply, MulAut.mul_apply] at this)
    refine ⟨σ, hσ45, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hσ x, conjPerm_apply]
  have hrange : ∀ k : ↥K, F k ∈ (conjPerm 6).range := fun k => by
    obtain ⟨σ, -, hσ⟩ := hperm k
    exact ⟨σ, hσ.symm⟩
  have hinj : Function.Injective (conjPerm 6) := conjPerm_injective (by decide)
  set f : ↥K →* Perm (Fin 6) :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (F.codRestrict _ hrange) with hfdef
  have hfF : ∀ k, conjPerm 6 (f k) = F k := by
    intro k
    have := (MonoidHom.ofInjective hinj).apply_symm_apply (F.codRestrict _ hrange k)
    exact congrArg Subtype.val this
  have hf45 : ∀ k, f k * Equiv.swap 4 5 = Equiv.swap 4 5 * f k := by
    intro k
    obtain ⟨σ, hσ45, hσ⟩ := hperm k
    rw [show f k = σ from hinj ((hfF k).trans hσ)]
    exact hσ45
  have hfB : ∀ (k : ↥K) (hk : (k : G) ∈ rightConjugate A g), f k = np.ψB ⟨k, hk⟩ := by
    intro k hk
    apply hinj
    rw [hfF, ← conj_eq_conjPerm]
    exact actAut_of_mem np.ψB (y := Subgroup.inclusion hKB k) hk
  obtain ⟨Q, hQ⟩ := hc.sylowR
  have hQ4 : ∀ q ∈ (Q : Subgroup ↥K), f q 4 = 4 := by
    intro q hq
    have hqR : (q : G) ∈ R := by
      rw [← hQ]
      exact ⟨q, hq, rfl⟩
    rw [hfB q (np.le_B hqR)]
    exact apply_eq_of_mem_rootVP (by decide)
      (Subgroup.mem_map_of_mem _ ((np.mem_R _).mp hqR)) (by decide)
  have h4 := fix_four_of_sylow Q f hf45 hQ4
  refine ⟨f, fun k => ⟨h4 k, ?_⟩, fun k => ⟨hKB k.2, by rw [hfF]; rfl⟩, hfB⟩
  rcases apply45_of_commute (hf45 k) with ⟨-, h5⟩ | ⟨h, -⟩
  · exact h5
  · exact absurd (h.symm.trans (h4 k)) (by decide)

theorem le_of_odd_normal {N : Subgroup G} (hNK : N ≤ centralizer (A : Set G))
    (hNn : ∀ k ∈ centralizer (A : Set G), ∀ m ∈ N, k * m * k⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ centralizer (rightConjugate A g : Set G) := by
  have h4 : 4 ≤ 6 := by decide
  obtain ⟨f, hf45, hfact, hfB⟩ := np.exists_hom_K hc
  have hoddOf : ∀ m ∈ N, Odd (orderOf m) := fun m hm =>
    hodd.of_dvd_nat (N.orderOf_dvd_natCard hm)
  intro m hm
  set mK : ↥(centralizer (A : Set G)) := ⟨m, hNK hm⟩ with hmK
  have hoddf : Odd (orderOf (f mK)) :=
    (hoddOf m hm).of_dvd_nat ((orderOf_map_dvd f mK).trans (orderOf_mk m _).dvd)
  have heven : f mK ∈ alternatingGroup (Fin 6) := by
    rw [mem_alternatingGroup]
    have h := congrArg sign (pow_orderOf_eq_one (f mK))
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (sign (f mK)) with hs | hs
    · exact hs
    · rw [hs, hoddf.neg_one_pow] at h
      exact absurd h (by decide)
  have hAlt := mem_rootAltP_of_fix h4 heven (fun i hi => by
    rcases (show (i : ℕ) = 4 ∨ (i : ℕ) = 5 by have := i.isLt; omega) with h | h
    · rw [show i = 4 from Fin.ext h]
      exact (hf45 mK).1
    · rw [show i = 5 from Fin.ext h]
      exact (hf45 mK).2)
  rw [rootAltP_eq h4] at hAlt
  obtain ⟨a, ha, hae⟩ := hAlt
  have hcomm : ∀ v ∈ kleinFour, a * v = v * a := by
    intro v hv
    have hvV : (⟨_, viaEmbeddingHom_mem_alternatingGroup' (fourEmb h4)
        (kleinFour_le_alternatingGroup hv)⟩ : alternatingGroup (Fin 6)) ∈ rootV 6 :=
      (mem_rootV_iff h4 _).mpr ⟨v, hv, rfl⟩
    obtain ⟨r, hr, hre⟩ := np.exists_R_of_mem hvV
    have hrK : (r : G) ∈ centralizer (A : Set G) := hc.sylowR.le hr
    set rK : ↥(centralizer (A : Set G)) := ⟨r, hrK⟩ with hrKdef
    have hfr : f rK = viaEmbeddingHom (fourEmb h4) v := by
      rw [hfB rK r.2]
      exact congrArg Subtype.val hre
    set w : ↥(centralizer (A : Set G)) := mK * rK * mK⁻¹ * rK⁻¹ with hwdef
    have hw : (w : G) ∈ N := by
      show m * (r : G) * m⁻¹ * (r : G)⁻¹ ∈ N
      have h2 := hNn _ hrK _ (inv_mem hm)
      have h3 : m * (r : G) * m⁻¹ * (r : G)⁻¹ = m * ((r : G) * m⁻¹ * (r : G)⁻¹) := by group
      rw [h3]
      exact mul_mem hm h2
    have hwf : f w = viaEmbeddingHom (fourEmb h4) (a * v * a⁻¹ * v⁻¹) := by
      simp only [w, map_mul, map_inv, hfr, ← hae]
    have hwV : a * v * a⁻¹ * v⁻¹ ∈ kleinFour :=
      mul_mem (conj_mem_kleinFour a hv) (inv_mem hv)
    have hoddw : Odd (orderOf (f w)) :=
      (hoddOf _ hw).of_dvd_nat ((orderOf_map_dvd f w).trans (orderOf_coe w).symm.dvd)
    rw [hwf] at hoddw
    have h1' : viaEmbeddingHom (fourEmb h4) (a * v * a⁻¹ * v⁻¹) = 1 :=
      eq_one_of_odd_of_mul_self hoddw (by rw [← map_mul, mul_self_of_mem_kleinFour hwV, map_one])
    have h2' : a * v * a⁻¹ * v⁻¹ = 1 :=
      (viaEmbeddingHom_injective (fourEmb h4)) (h1'.trans (map_one _).symm)
    calc a * v = (a * v * a⁻¹ * v⁻¹) * v * a := by group
      _ = v * a := by rw [h2', one_mul]
  have ha2 : a * a = 1 :=
    mul_self_of_commute_kleinFour a (hcomm _ swap_mem_kleinFour_one)
      (hcomm _ swap_mem_kleinFour_two)
  have hf1 : f mK = 1 := by
    rw [← hae] at hoddf ⊢
    exact eq_one_of_odd_of_mul_self hoddf (by rw [← map_mul, ha2, map_one])
  obtain ⟨hmB, hmact⟩ := hfact mK
  rw [hf1, map_one] at hmact
  exact (actAut_eq_one_iff _ _).mp hmact

theorem normalizer_le_inf :
    normalizer (A : Set G) ≤ normalizer ((centralizer (A : Set G) ⊓
      centralizer (rightConjugate A g : Set G) : Subgroup G) : Set G) := by
  intro x hx
  set K := centralizer (A : Set G)
  set Kg := centralizer (rightConjugate A g : Set G)
  have hxK : x ∈ normalizer (K : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hx
  have hKN : ∀ k ∈ K, ∀ m ∈ K ⊓ Kg, k * m * k⁻¹ ∈ K ⊓ Kg := by
    intro k hk m hm
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hm.1) (inv_mem hk), ?_⟩
    have hkB := NormPair.centralizer_le_normalizer_B hc np.le_A hk
    have hKgN : k ∈ normalizer (Kg : Set G) := (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer _) hkB
    exact (mem_normalizer_iff.mp hKgN m).mp hm.2
  set N := (K ⊓ Kg).map (MulAut.conj x).toMonoidHom
  have hNK : N ≤ K := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_normalizer_iff.mp hxK m).mp hm.1
  have hNn : ∀ k ∈ K, ∀ m ∈ N, k * m * k⁻¹ ∈ N := by
    rintro k hk _ ⟨m, hm, rfl⟩
    have hk' : x⁻¹ * k * x ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hxK) k).mp hk
      simpa using this
    refine ⟨x⁻¹ * k * x * m * (x⁻¹ * k * x)⁻¹, hKN _ hk' _ hm, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hoddN : Odd (Nat.card N) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    have hKt := tightlyEmbedded_centralizer_of_standard hc.hyp.standard
    have h := hKt.2 g (by rw [normalizer_centralizer_eq hc.hyp.standard]; exact hc.not_mem)
    rwa [← centralizer_rightConjugate] at h
  have hle := np.le_of_odd_normal hc hNK hNn hoddN
  apply mem_normalizer_of_conj_mem
  intro m hm
  exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hxK m).mp hm.1, hle ⟨m, hm, rfl⟩⟩

end SixPair

end CFSG.ComponentClassification.RankTwoAlt
