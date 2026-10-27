module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Q8D8

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem threeComm_mem_zpowers {t g : K} (ht2 : t ^ 2 = 1) (hg : g ∈ zpowers t) : g = 1 ∨ g = t := by
  obtain ⟨n, rfl⟩ := hg
  have h1 : t ^ (2 : ℤ) = 1 := by exact_mod_cast ht2
  have h2 : t ^ n = (t ^ (2 : ℤ)) ^ (n / 2) * t ^ (n % 2) := by
    rw [← zpow_mul, ← zpow_add, Int.mul_ediv_add_emod]
  show t ^ n = 1 ∨ t ^ n = t
  rw [h2, h1, one_zpow, one_mul]
  have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h3 with h3 | h3
  · left
    rw [h3]
    simp
  · right
    rw [h3]
    simp

theorem threeComm_mul_self {t g : K} (ht2 : t ^ 2 = 1) (hg : g ∈ zpowers t) : g * g = 1 := by
  rcases threeComm_mem_zpowers ht2 hg with rfl | rfl
  · simp
  · rw [← pow_two]
    exact ht2

theorem threeComm_inv_eq {t g : K} (ht2 : t ^ 2 = 1) (hg : g ∈ zpowers t) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (threeComm_mul_self ht2 hg)

theorem threeComm_cent {t r g : K} (hr : r * t = t * r) (hg : g ∈ zpowers t) : r * g = g * r := by
  obtain ⟨n, rfl⟩ := hg
  exact ((show Commute r t from hr).zpow_right n).eq

theorem threeComm_zpowers_comm {t g h : K} (hg : g ∈ zpowers t) (hh : h ∈ zpowers t) :
    g * h = h * g := by
  obtain ⟨m, rfl⟩ := hg
  obtain ⟨n, rfl⟩ := hh
  exact (Commute.zpow_zpow_self t m n).eq

theorem threeComm_coset {R : Subgroup K} {t : K} (hR : IsExt2 R t) {g h : K} (hg : g ∈ R)
    (hgh : g * h ∈ zpowers t) : h = g ∨ h = g * t := by
  have hsq : (g ^ 2)⁻¹ ∈ zpowers t := inv_mem (hR.sq_mem g hg)
  have hs : (g ^ 2)⁻¹ * (g * h) ∈ zpowers t := mul_mem hsq hgh
  have e : h = g * ((g ^ 2)⁻¹ * (g * h)) := by group
  rcases threeComm_mem_zpowers hR.t_sq hs with h1 | h1
  · left
    calc h = g * ((g ^ 2)⁻¹ * (g * h)) := e
      _ = g * 1 := by rw [h1]
      _ = g := mul_one g
  · right
    calc h = g * ((g ^ 2)⁻¹ * (g * h)) := e
      _ = g * t := by rw [h1]

theorem threeComm_nmem {t w : K} (ht2 : t ^ 2 = 1) {l : List K} (h1 : (1 : K) ∈ l) (ht : t ∈ l)
    (hw : w ∉ l) : w ∉ zpowers t := by
  intro h
  rcases threeComm_mem_zpowers ht2 h with rfl | rfl
  · exact hw h1
  · exact hw ht

theorem threeComm_exists_not_mem {R : Subgroup K} (l : List K) (hl : l.length < Nat.card R) :
    ∃ w ∈ R, w ∉ l := by
  classical
  by_contra hcon
  have hsub : (R : Set K) ⊆ (l.toFinset : Set K) := fun w hw => by
    by_contra hw'
    exact hcon ⟨w, hw, by simpa using hw'⟩
  have h1 : Nat.card R ≤ l.toFinset.card := by
    calc Nat.card R = (R : Set K).ncard := Nat.card_coe_set_eq (R : Set K)
      _ ≤ (l.toFinset : Set K).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = l.toFinset.card := Set.ncard_coe_finset _
  have h2 := List.toFinset_card_le l
  omega

theorem threeComm_comm_mul_right {R : Subgroup K} {t : K} (hR : IsExt2 R t) {a b c : K} (ha : a ∈ R)
    (hb : b ∈ R) (hc : c ∈ R) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h1 : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h2 : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ := by
    rw [threeComm_cent (hR.t_comm b hb) (hR.comm_mem a ha c hc)]
    simp
  rw [h1, h2]

theorem threeComm_comm_mul_left {R : Subgroup K} {t : K} (hR : IsExt2 R t) {a b c : K} (ha : a ∈ R)
    (hb : b ∈ R) (hc : c ∈ R) : ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have h1 : ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    group
  have h2 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    rw [threeComm_cent (hR.t_comm a ha) (hR.comm_mem b hb c hc)]
    simp
  rw [h1, h2]
  exact threeComm_zpowers_comm (hR.comm_mem b hb c hc) (hR.comm_mem a ha c hc)

theorem threeComm_comm_symm {R : Subgroup K} {t : K} (hR : IsExt2 R t) {a b : K} (ha : a ∈ R)
    (hb : b ∈ R) : ⁅b, a⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv a b]
  exact threeComm_inv_eq hR.t_sq (hR.comm_mem a ha b hb)

theorem threeComm_conj_comm (z : K) {a b : K} (h : a * b = b * a) :
    (z * a * z⁻¹) * (z * b * z⁻¹) = (z * b * z⁻¹) * (z * a * z⁻¹) := by
  have h1 : (z * a * z⁻¹) * (z * b * z⁻¹) = z * (a * b) * z⁻¹ := by group
  have h2 : (z * b * z⁻¹) * (z * a * z⁻¹) = z * (b * a) * z⁻¹ := by group
  rw [h1, h2, h]

theorem threeComm_conj3 {z : K} (hz : z ^ 3 = 1) (x : K) :
    z * (z * (z * x * z⁻¹) * z⁻¹) * z⁻¹ = x := by
  have h : z * (z * (z * x * z⁻¹) * z⁻¹) * z⁻¹ = z ^ 3 * x * (z ^ 3)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [h, hz]
  simp

theorem threeComm_triple_central {R : Subgroup K} {z x x₁ x₂ : K} (hz : z ^ 3 = 1)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z)
    (hx : x ∈ R) (hx₁ : x₁ ∈ R) (hx₂ : x₂ ∈ R) (hz1 : z * x * z⁻¹ = x₁)
    (hz2 : z * x₁ * z⁻¹ = x₂) (hz3 : z * x₂ * z⁻¹ = x) (hc01 : x * x₁ = x₁ * x) :
    z * x = x * z := by
  have hc12 : x₁ * x₂ = x₂ * x₁ := by
    have := threeComm_conj_comm z hc01
    rwa [hz1, hz2] at this
  have hc20 : x₂ * x = x * x₂ := by
    have := threeComm_conj_comm z hc12
    rwa [hz2, hz3] at this
  have hcomm : ∀ a ∈ ({x, x₁, x₂} : Set K), ∀ b ∈ ({x, x₁, x₂} : Set K), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb]
    · exact hc01
    · exact hc20.symm
    · exact hc01.symm
    · exact hc12
    · exact hc20
    · exact hc12.symm
  have hAR : closure ({x, x₁, x₂} : Set K) ≤ R := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg <;> rw [hg]
    · exact hx
    · exact hx₁
    · exact hx₂
  have hgen : ∀ g ∈ ({x, x₁, x₂} : Set K),
      z * g * z⁻¹ ∈ closure ({x, x₁, x₂} : Set K) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg <;> rw [hg]
    · rw [hz1]
      exact subset_closure (by simp)
    · rw [hz2]
      exact subset_closure (by simp)
    · rw [hz3]
      exact subset_closure (by simp)
  have hfwd : ∀ g ∈ closure ({x, x₁, x₂} : Set K),
      z * g * z⁻¹ ∈ closure ({x, x₁, x₂} : Set K) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hgen s hs
    | one => simpa using one_mem _
    | mul a b _ _ ha hb =>
      have e : z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  have hzA : z ∈ normalizer ((closure ({x, x₁, x₂} : Set K) : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hfwd g, fun hg => ?_⟩
    have h2 := hfwd _ (hfwd _ hg)
    rwa [threeComm_conj3 hz g] at h2
  have hAcomm : ∀ a ∈ closure ({x, x₁, x₂} : Set K), ∀ b ∈ closure ({x, x₁, x₂} : Set K),
      a * b = b * a := by
    haveI := Subgroup.isMulCommutative_closure (k := ({x, x₁, x₂} : Set K))
      (fun a ha b hb _ => (hcomm a ha b hb : Commute a b))
    intro a ha b hb
    exact setLike_mul_comm ha hb
  exact hstar _ hAR hAcomm hzA x (subset_closure (by simp))

theorem comm_conj_eq_t {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 3 = 1)
    (hzR : z ∈ normalizer (R : Set K)) (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z) {x : K} (hx : x ∈ R)
    (hxt : x ∉ zpowers t) : ⁅x, z * x * z⁻¹⁆ = t := by
  have hx1 : z * x * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hzR x).mp hx
  have hx2 : z * (z * x * z⁻¹) * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hzR _).mp hx1
  rcases threeComm_mem_zpowers hR.t_sq (hR.comm_mem x hx _ hx1) with h1 | h1
  swap
  · exact h1
  exfalso
  apply hxt
  apply hfix x hx
  have hc01 : x * (z * x * z⁻¹) = (z * x * z⁻¹) * x :=
    commutatorElement_eq_one_iff_mul_comm.mp h1
  exact threeComm_triple_central hz hstar hx hx1 hx2 rfl rfl (threeComm_conj3 hz x) hc01

theorem triple_mem {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 3 = 1)
    (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t) {x : K} (hx : x ∈ R) :
    x * (z * x * z⁻¹) * (z ^ 2 * x * (z ^ 2)⁻¹) ∈ zpowers t := by
  have hx1 : z * x * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hzR x).mp hx
  have hx2 : z ^ 2 * x * (z ^ 2)⁻¹ ∈ R := by
    have e : z ^ 2 * x * (z ^ 2)⁻¹ = z * (z * x * z⁻¹) * z⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hzR _).mp hx1
  obtain ⟨u, hu⟩ : ∃ u, u = x * (z * x * z⁻¹) * (z ^ 2 * x * (z ^ 2)⁻¹) := ⟨_, rfl⟩
  rw [← hu]
  have huR : u ∈ R := by
    rw [hu]
    exact mul_mem (mul_mem hx hx1) hx2
  have h3 : z * (z ^ 2 * x * (z ^ 2)⁻¹) * z⁻¹ = x := by
    have e : z * (z ^ 2 * x * (z ^ 2)⁻¹) * z⁻¹ = z ^ 3 * x * (z ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hz]
    simp
  have h1 : z * u * z⁻¹ = x⁻¹ * u * x := by
    have e1 : z * u * z⁻¹ = (z * x * z⁻¹) * (z * (z * x * z⁻¹) * z⁻¹) *
        (z * (z ^ 2 * x * (z ^ 2)⁻¹) * z⁻¹) := by
      rw [hu]
      group
    rw [e1, h3, hu]
    group
  obtain ⟨c, hcdef⟩ : ∃ c, c = u⁻¹ * (z * u * z⁻¹) := ⟨_, rfl⟩
  have hc : c ∈ zpowers t := by
    rw [hcdef, h1]
    have := hR.comm_mem u⁻¹ (inv_mem huR) x⁻¹ (inv_mem hx)
    simpa [commutatorElement_def, mul_assoc] using this
  have hzu : z * u * z⁻¹ = u * c := by
    rw [hcdef]
    simp
  have hzc : z * c * z⁻¹ = c := by
    rw [threeComm_cent hzt hc]
    simp
  have hcc : c * c = 1 := threeComm_mul_self hR.t_sq hc
  have e2 : z * (z * u * z⁻¹) * z⁻¹ = u := by
    calc z * (z * u * z⁻¹) * z⁻¹ = z * (u * c) * z⁻¹ := by rw [hzu]
      _ = (z * u * z⁻¹) * (z * c * z⁻¹) := by group
      _ = (u * c) * c := by rw [hzu, hzc]
      _ = u := by rw [mul_assoc, hcc, mul_one]
  have e3 : z * u * z⁻¹ = u := by
    have := threeComm_conj3 hz u
    rwa [e2] at this
  exact hfix u huR (mul_inv_eq_iff_eq_mul.mp e3)

theorem comm_eq_t_of_three {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 3 = 1)
    (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z) {x y : K} (hx : x ∈ R) (hy : y ∈ R)
    (hxt : x ∉ zpowers t) (hyt : y ∉ zpowers t) (hxy : x * y ∉ zpowers t) : ⁅x, y⁆ = t := by
  have ht2' : t * t = 1 := by
    rw [← pow_two]
    exact hR.t_sq
  have hx1 : z * x * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hzR x).mp hx
  have hy1 : z * y * z⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hzR y).mp hy
  have hy2 : z ^ 2 * y * (z ^ 2)⁻¹ ∈ R := by
    have e : z ^ 2 * y * (z ^ 2)⁻¹ = z * (z * y * z⁻¹) * z⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hzR _).mp hy1
  have hxyR : x * y ∈ R := mul_mem hx hy
  have hA := comm_conj_eq_t hR hz hzR hfix hstar hx hxt
  have hB := comm_conj_eq_t hR hz hzR hfix hstar hy hyt
  have hC := comm_conj_eq_t hR hz hzR hfix hstar hxyR hxy
  have hσ : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
  rw [hσ] at hC
  have hexp : ⁅x * y, (z * x * z⁻¹) * (z * y * z⁻¹)⁆ =
      (⁅x, z * x * z⁻¹⁆ * ⁅y, z * x * z⁻¹⁆) * (⁅x, z * y * z⁻¹⁆ * ⁅y, z * y * z⁻¹⁆) := by
    rw [threeComm_comm_mul_right hR hxyR hx1 hy1, threeComm_comm_mul_left hR hx hy hx1,
      threeComm_comm_mul_left hR hx hy hy1]
  rw [hexp, hA, hB] at hC
  have hP := hR.comm_mem x hx _ hy1
  have hQ := hR.comm_mem y hy _ hx1
  have hPQ : ⁅x, z * y * z⁻¹⁆ * ⁅y, z * x * z⁻¹⁆ = t := by
    rcases threeComm_mem_zpowers hR.t_sq hP with hP' | hP' <;>
      rcases threeComm_mem_zpowers hR.t_sq hQ with hQ' | hQ' <;> rw [hP', hQ'] at hC ⊢
    · exfalso
      simp [ht2'] at hC
      first | exact hR.t_ne hC | exact hR.t_ne hC.symm
    · simp
    · simp
    · exfalso
      simp [ht2'] at hC
      first | exact hR.t_ne hC | exact hR.t_ne hC.symm
  have hy3 : z * (z ^ 2 * y * (z ^ 2)⁻¹) * z⁻¹ = y := by
    have e : z * (z ^ 2 * y * (z ^ 2)⁻¹) * z⁻¹ = z ^ 3 * y * (z ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hz]
    simp
  have hQ2 : ⁅y, z * x * z⁻¹⁆ = ⁅x, z ^ 2 * y * (z ^ 2)⁻¹⁆ := by
    rw [threeComm_comm_symm hR hx1 hy]
    have e : ⁅z * x * z⁻¹, y⁆ = z * ⁅x, z ^ 2 * y * (z ^ 2)⁻¹⁆ * z⁻¹ := by
      conv_lhs => rw [← hy3]
      simp only [commutatorElement_def]
      group
    rw [e, threeComm_cent hzt (hR.comm_mem x hx _ hy2)]
    simp
  have hT := triple_mem hR hz hzR hzt hfix hy
  have hxw : ⁅x, y * (z * y * z⁻¹ * (z ^ 2 * y * (z ^ 2)⁻¹))⁆ = 1 := by
    rw [← mul_assoc]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (threeComm_cent (hR.t_comm x hx) hT)
  rw [threeComm_comm_mul_right hR hx hy (mul_mem hy1 hy2), threeComm_comm_mul_right hR hx hy1 hy2,
    ← hQ2, hPQ] at hxw
  rw [eq_inv_of_mul_eq_one_left hxw]
  exact inv_eq_of_mul_eq_one_right ht2'

theorem card_le_eight_of_three {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 3 = 1)
    (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t)
    (hstar : ∀ A : Subgroup K, A ≤ R → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      z ∈ normalizer (A : Set K) → ∀ a ∈ A, z * a = a * z) : Nat.card R ≤ 8 := by
  by_contra hcon
  have h9 : 8 < Nat.card R := by omega
  have ht2' : t * t = 1 := by
    rw [← pow_two]
    exact hR.t_sq
  obtain ⟨x, hxR, hx⟩ := threeComm_exists_not_mem (R := R) [1, t]
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hxt : x ∉ zpowers t := threeComm_nmem hR.t_sq (by simp) (by simp) hx
  obtain ⟨y, hyR, hy⟩ := threeComm_exists_not_mem (R := R) [1, t, x, x * t]
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hyt : y ∉ zpowers t := threeComm_nmem hR.t_sq (by simp) (by simp) hy
  have hxy : x * y ∉ zpowers t := fun h => hy (by
    rcases threeComm_coset hR hxR h with h1 | h1 <;> simp [h1])
  obtain ⟨w, hwR, hw⟩ := threeComm_exists_not_mem (R := R)
    [1, t, x, x * t, y, y * t, x * y, x * y * t]
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwt : w ∉ zpowers t := threeComm_nmem hR.t_sq (by simp) (by simp) hw
  have hxw : x * w ∉ zpowers t := fun h => hw (by
    rcases threeComm_coset hR hxR h with h1 | h1 <;> simp [h1])
  have hyw : y * w ∉ zpowers t := fun h => hw (by
    rcases threeComm_coset hR hyR h with h1 | h1 <;> simp [h1])
  have hxyw : x * y * w ∉ zpowers t := fun h => hw (by
    rcases threeComm_coset hR (mul_mem hxR hyR) h with h1 | h1 <;> simp [h1])
  have hxyw' : x * (y * w) ∉ zpowers t := by
    rw [← mul_assoc]
    exact hxyw
  have h1 := comm_eq_t_of_three hR hz hzR hzt hfix hstar hxR hyR hxt hyt hxy
  have h2 := comm_eq_t_of_three hR hz hzR hzt hfix hstar hxR hwR hxt hwt hxw
  have h3 := comm_eq_t_of_three hR hz hzR hzt hfix hstar hxR (mul_mem hyR hwR) hxt hyw hxyw'
  rw [threeComm_comm_mul_right hR hxR hyR hwR, h1, h2, ht2'] at h3
  exact hR.t_ne h3.symm
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem shapeThree_mem_zpowers {t : K} (ht2 : t ^ 2 = 1) {a : K} (ha : a ∈ zpowers t) :
    a = 1 ∨ a = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
  have h2 : ∀ m : ℤ, t ^ (2 * m) = 1 := by
    intro m
    rw [zpow_mul, zpow_two, ← pow_two, ht2, one_zpow]
  have hn : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod n 2, zpow_add, h2, one_mul]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [hn, h, zpow_zero]
  · right
    rw [hn, h, zpow_one]

theorem shapeThree_central {R : Subgroup K} {t : K} (hR : IsExt2 R t) {a r : K} (ha : a ∈ zpowers t)
    (hr : r ∈ R) : r * a = a * r := by
  rcases shapeThree_mem_zpowers hR.t_sq ha with rfl | rfl
  · simp
  · exact hR.t_comm r hr

theorem shapeThree_conj_fix {t z : K} (ht2 : t ^ 2 = 1) (hzt : z * t = t * z) {a : K}
    (ha : a ∈ zpowers t) : z * a * z⁻¹ = a := by
  rcases shapeThree_mem_zpowers ht2 ha with rfl | rfl
  · simp
  · rw [hzt, mul_inv_cancel_right]

theorem shapeThree_exists_not_mem {R : Subgroup K} {t : K} (hR : IsExt2 R t)
    (hcard : Nat.card R = 8) : ∃ x ∈ R, x ∉ zpowers t := by
  by_contra hcon
  have hle : R ≤ zpowers t := fun x hx => by
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  have h1 : Nat.card R ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hle
  have h2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hR.t_sq hR.t_ne
  omega

theorem shapeThree_conj_mem {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hz : z ^ 3 = 1)
    (hzt : z * t = t * z) (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t) {u : K} (hu : u ∈ R)
    (h : u⁻¹ * (z * u * z⁻¹) ∈ zpowers t) : u ∈ zpowers t := by
  apply hfix u hu
  set e := u⁻¹ * (z * u * z⁻¹) with he_def
  have hge : z * u * z⁻¹ = u * e := by rw [he_def, mul_inv_cancel_left]
  have hfe : z * e * z⁻¹ = e := shapeThree_conj_fix hR.t_sq hzt h
  have hee : e * e = 1 := by
    rcases shapeThree_mem_zpowers hR.t_sq h with h1 | h1
    · rw [h1, mul_one]
    · rw [h1, ← pow_two, hR.t_sq]
  have h2 : z * (z * u * z⁻¹) * z⁻¹ = u := by
    calc z * (z * u * z⁻¹) * z⁻¹ = z * (u * e) * z⁻¹ := by rw [hge]
      _ = (z * u * z⁻¹) * (z * e * z⁻¹) := by group
      _ = u := by rw [hge, hfe, mul_assoc, hee, mul_one]
  have h3 : z * (z * (z * u * z⁻¹) * z⁻¹) * z⁻¹ = u := by
    calc z * (z * (z * u * z⁻¹) * z⁻¹) * z⁻¹ = z ^ 3 * u * (z ^ 3)⁻¹ := by
          rw [pow_three]; simp only [mul_inv_rev, mul_assoc]
      _ = u := by rw [hz]; simp
  rw [h2] at h3
  calc z * u = z * u * z⁻¹ * z := by group
    _ = u * z := by rw [h3]

theorem shapeThree_comm_ne {R : Subgroup K} {t x y : K} (hR : IsExt2 R t) (hcard : Nat.card R = 8)
    (hxR : x ∈ R) (hyR : y ∈ R) (hxT : x ∉ zpowers t) (hyT : y ∉ zpowers t)
    (hxyT : x⁻¹ * y ∉ zpowers t) : x * y ≠ y * x := by
  intro hxy
  let C : Subgroup K := centralizer ({x} : Set K) ⊓ R
  have hCR : C ≤ R := inf_le_right
  have hxtT : x * t ∉ zpowers t := by
    intro h
    apply hxT
    have := mul_mem h (inv_mem (mem_zpowers t))
    simpa using this
  have h1t : (1 : K) ≠ t := hR.t_ne.symm
  have h1x : (1 : K) ≠ x := fun h => hxT (by rw [← h]; exact one_mem _)
  have h1xt : (1 : K) ≠ x * t := fun h => hxtT (by rw [← h]; exact one_mem _)
  have h1y : (1 : K) ≠ y := fun h => hyT (by rw [← h]; exact one_mem _)
  have htx : t ≠ x := fun h => hxT (by rw [← h]; exact mem_zpowers t)
  have htxt : t ≠ x * t := fun h => hxtT (by rw [← h]; exact mem_zpowers t)
  have hty : t ≠ y := fun h => hyT (by rw [← h]; exact mem_zpowers t)
  have hxxt : x ≠ x * t := fun h =>
    hR.t_ne (mul_left_cancel (a := x) (by rw [mul_one]; exact h.symm))
  have hxy' : x ≠ y := fun h => hxyT (by rw [h, inv_mul_cancel]; exact one_mem _)
  have hxty : x * t ≠ y := fun h => hxyT (by rw [← h, inv_mul_cancel_left]; exact mem_zpowers t)
  have hcard5 : 5 ≤ Nat.card C := by
    have hsub : ({1, t, x, x * t, y} : Set K) ⊆ (C : Set K) := by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact one_mem C
      · refine ⟨mem_centralizer_iff.mpr ?_, hR.t_mem⟩
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hR.t_comm x hxR
      · exact ⟨mem_centralizer_iff.mpr (fun h hh => by rw [Set.mem_singleton_iff.mp hh]), hxR⟩
      · refine ⟨mem_centralizer_iff.mpr ?_, mul_mem hxR hR.t_mem⟩
        intro h hh
        rw [Set.mem_singleton_iff.mp hh, mul_assoc, hR.t_comm x hxR]
      · exact ⟨mem_centralizer_iff.mpr (fun h hh => by rw [Set.mem_singleton_iff.mp hh]; exact hxy),
          hyR⟩
    have hncard : ({1, t, x, x * t, y} : Set K).ncard = 5 := by
      simp [Set.ncard_insert_of_notMem, h1t, h1x, h1xt, h1y, htx, htxt, hty, hxxt, hxy', hxty]
    calc 5 = ({1, t, x, x * t, y} : Set K).ncard := hncard.symm
      _ ≤ (C : Set K).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card C := (Nat.card_coe_set_eq _).symm
  have hdvd : Nat.card C ∣ 8 := hcard ▸ Subgroup.card_dvd_of_le hCR
  have hC8 : Nat.card C = 8 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨n, hn⟩ : ∃ n, n = Nat.card C := ⟨_, rfl⟩
    rw [← hn] at hcard5 hle hdvd ⊢
    interval_cases n <;> omega
  have hCeq : C = R := Subgroup.eq_of_le_of_card_ge hCR (by rw [hcard, hC8])
  apply hxT
  apply hR.center_le x hxR
  intro r hr
  have hrC : r ∈ C := hCeq ▸ hr
  exact (mem_centralizer_iff.mp hrC.1) x (Set.mem_singleton x)

theorem shapeThree_sq_eq_t {R : Subgroup K} {t x y w : K} (hR : IsExt2 R t) (hxR : x ∈ R)
    (hyR : y ∈ R) (hcomm : x * y = t * (y * x)) (hy2 : y ^ 2 = x ^ 2) (hw2 : w ^ 2 = x ^ 2)
    (htriple : x * y * w ∈ zpowers t) : x ^ 2 = t := by
  have hx2 : x ^ 2 ∈ zpowers t := hR.sq_mem x hxR
  have hsq : ∀ a ∈ zpowers t, a * a = 1 := by
    intro a ha
    rcases shapeThree_mem_zpowers hR.t_sq ha with h | h
    · rw [h, mul_one]
    · rw [h, ← pow_two, hR.t_sq]
  have hc : y * x ^ 2 = x ^ 2 * y := shapeThree_central hR hx2 hyR
  have hxy2 : (x * y) ^ 2 = t := by
    calc (x * y) ^ 2 = (x * y) * (x * y) := pow_two _
      _ = (t * (y * x)) * (x * y) := by rw [← hcomm]
      _ = t * (y * x ^ 2 * y) := by simp only [pow_two, mul_assoc]
      _ = t * (x ^ 2 * y * y) := by rw [hc]
      _ = t * (x ^ 2 * y ^ 2) := by simp only [pow_two, mul_assoc]
      _ = t * (x ^ 2 * x ^ 2) := by rw [hy2]
      _ = t := by rw [hsq _ hx2, mul_one]
  have hwe : w = (x * y)⁻¹ * (x * y * w) := by rw [inv_mul_cancel_left]
  have hcomm' : Commute (x * y)⁻¹ (x * y * w) :=
    shapeThree_central hR htriple (inv_mem (mul_mem hxR hyR))
  have hw2t : w ^ 2 = t := by
    rw [hwe, hcomm'.mul_pow, inv_pow, hxy2, pow_two (x * y * w), hsq _ htriple, mul_one]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hR.t_sq)
  exact hw2.symm.trans hw2t

theorem shape_three {R : Subgroup K} {t z : K} (hR : IsExt2 R t) (hcard : Nat.card R = 8)
    (hz : z ^ 3 = 1) (hzR : z ∈ normalizer (R : Set K)) (hzt : z * t = t * z)
    (hfix : ∀ r ∈ R, z * r = r * z → r ∈ zpowers t) : Nonempty (↥R ≃* QuaternionGroup 2) := by
  obtain ⟨x, hxR, hxT⟩ := shapeThree_exists_not_mem hR hcard
  have hyR : z * x * z⁻¹ ∈ R := (mem_set_normalizer_iff.mp hzR x).mp hxR
  have hzt2 : z ^ 2 * t = t * z ^ 2 := Commute.pow_left hzt 2
  have hx2 : x ^ 2 ∈ zpowers t := hR.sq_mem x hxR
  have hy2 : (z * x * z⁻¹) ^ 2 = x ^ 2 := by
    rw [conj_pow]
    exact shapeThree_conj_fix hR.t_sq hzt hx2
  have hw2 : (z ^ 2 * x * (z ^ 2)⁻¹) ^ 2 = x ^ 2 := by
    rw [conj_pow]
    exact shapeThree_conj_fix hR.t_sq hzt2 hx2
  have htriple := triple_mem hR hz hzR hzt hfix hxR
  have hyT : z * x * z⁻¹ ∉ zpowers t := by
    intro hyt
    apply hxT
    have h1 : z * (z * x * z⁻¹) * z⁻¹ = z * x * z⁻¹ := shapeThree_conj_fix hR.t_sq hzt hyt
    have h2 : z * (z * x * z⁻¹) = z * x := mul_right_cancel h1
    have h3 : z * x * z⁻¹ = x := mul_left_cancel h2
    rw [← h3]
    exact hyt
  have hxyT : x⁻¹ * (z * x * z⁻¹) ∉ zpowers t := fun h =>
    hxT (shapeThree_conj_mem hR hz hzt hfix hxR h)
  have hne := shapeThree_comm_ne hR hcard hxR hyR hxT hyT hxyT
  have hcomm : ⁅x, z * x * z⁻¹⁆ = t := by
    rcases shapeThree_mem_zpowers hR.t_sq (hR.comm_mem x hxR _ hyR) with h | h
    · exact absurd (commutatorElement_eq_one_iff_mul_comm.mp h) hne
    · exact h
  have hcomm' : x * (z * x * z⁻¹) = t * ((z * x * z⁻¹) * x) := by
    rw [commutatorElement_def] at hcomm
    calc x * (z * x * z⁻¹) = (x * (z * x * z⁻¹) * x⁻¹ * (z * x * z⁻¹)⁻¹) * ((z * x * z⁻¹) * x) := by
          group
      _ = t * ((z * x * z⁻¹) * x) := by rw [hcomm]
  have hxt : x ^ 2 = t := shapeThree_sq_eq_t hR hxR hyR hcomm' hy2 hw2 htriple
  have hyt : (z * x * z⁻¹) ^ 2 = t := hy2.trans hxt
  obtain ⟨⟨e⟩, hcl8, -⟩ := exists_Q8_subgroup hxt hyt hcomm hR.t_sq hR.t_ne
  have hle : Subgroup.closure ({x, z * x * z⁻¹} : Set K) ≤ R := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact hxR
    · rw [Set.mem_singleton_iff.mp hg]
      exact hyR
  have heq : Subgroup.closure ({x, z * x * z⁻¹} : Set K) = R :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcl8, hcard])
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
