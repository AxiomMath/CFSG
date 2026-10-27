module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankSer
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankComm

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem comm_mul_left (x y z : G) : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right (x y z : G) : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_mul_mem {U M : Subgroup G} (hM : ∀ u ∈ U, ∀ m ∈ M, u * m * u⁻¹ ∈ M)
    {x y g h : G} (hx : x ∈ U) (hy : y ∈ U) (hgy : ⁅g, y⁆ ∈ M) (hgh : ⁅g, h⁆ ∈ M)
    (hhx : ⁅h, x⁆ ∈ M) : ⁅x * g, y * h⁆ * ⁅x, y⁆⁻¹ ∈ M := by
  have e : ⁅x * g, y * h⁆ * ⁅x, y⁆⁻¹ = (x * ⁅g, y⁆ * x⁻¹) * ((x * y) * ⁅g, h⁆ * (x * y)⁻¹) *
      ((x * y * x⁻¹) * ⁅h, x⁆⁻¹ * (x * y * x⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine mul_mem (mul_mem (hM x hx _ hgy) (hM (x * y) (mul_mem hx hy) _ hgh)) ?_
  exact hM (x * y * x⁻¹) (mul_mem (mul_mem hx hy) (inv_mem hx)) _ (inv_mem hhx)

theorem comm_mul_mul_eq {x y g h : G} (hgy : ⁅g, y⁆ = 1) (hgh : ⁅g, h⁆ = 1) (hhx : ⁅h, x⁆ = 1) :
    ⁅x * g, y * h⁆ = ⁅x, y⁆ := by
  have e : ⁅x * g, y * h⁆ * ⁅x, y⁆⁻¹ = (x * ⁅g, y⁆ * x⁻¹) * ((x * y) * ⁅g, h⁆ * (x * y)⁻¹) *
      ((x * y * x⁻¹) * ⁅h, x⁆⁻¹ * (x * y * x⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hgy, hgh, hhx] at e
  simp only [mul_one, inv_one, one_mul, mul_inv_cancel] at e
  exact mul_inv_eq_one.1 e

end Abstract

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47
open scoped commutatorElement


section Series

variable {F : Type} [Field F]

theorem hs_normalized (h : ℤ) : ∀ u ∈ heightSeries .G2 F 1, ∀ m ∈ heightSeries .G2 F h,
    u * m * u⁻¹ ∈ heightSeries .G2 F h := by
  intro u hu m hm
  rw [heightSeries_one] at hu
  exact (Subgroup.mem_normalizer_iff.1 (heightSeries_le_normalizer F h hu) m).1 hm

theorem comm_hs {h k m : ℤ} (hm : h + k = m) {x y : ModGL .G2 F}
    (hx : x ∈ heightSeries .G2 F h) (hy : y ∈ heightSeries .G2 F k) :
    ⁅x, y⁆ ∈ heightSeries .G2 F m := by
  rw [← hm]
  exact commutator_heightSeries_le F h k (Subgroup.commutator_mem_commutator hx hy)

theorem hs_mono {h h' : ℤ} (hh : h ≤ h') : heightSeries .G2 F h' ≤ heightSeries .G2 F h :=
  heightSeries_antitone hh

theorem comm_hs_one [Finite F] {h k : ℤ} (hm : 6 ≤ h + k) {x y : ModGL .G2 F}
    (hx : x ∈ heightSeries .G2 F h) (hy : y ∈ heightSeries .G2 F k) : ⁅x, y⁆ = 1 := by
  have h1 := hs_mono (F := F) hm (comm_hs rfl hx hy)
  rw [hs_six_eq_bot] at h1
  exact Subgroup.mem_bot.1 h1

theorem Xr_mem_one (x : F) : Xr x ∈ heightSeries .G2 F 1 := Xr_mem_hs le_rfl x
theorem Xa_mem_one (x : F) : Xa x ∈ heightSeries .G2 F 1 := Xa_mem_hs le_rfl x

theorem mem_one_of_mem {h : ℤ} (hh : 1 ≤ h) {g : ModGL .G2 F} (hg : g ∈ heightSeries .G2 F h) :
    g ∈ heightSeries .G2 F 1 :=
  hs_mono hh hg

theorem patB [Finite F] (h3 : (3 : F) ≠ 0) {e₃ e₄ : ModGL .G2 F}
    (h3m : e₃ ∈ heightSeries .G2 F 2) (h3n : e₃ ∉ heightSeries .G2 F 3)
    (h4m : e₄ ∈ heightSeries .G2 F 3) (h4n : e₄ ∉ heightSeries .G2 F 4)
    (hc : ⁅e₃, e₄⁆ = 1) : False := by
  obtain ⟨w, n₂, hn₂, rfl⟩ := dec2 h3m
  obtain ⟨x, n₃, hn₃, rfl⟩ := dec3 h4m
  have hw : w ≠ 0 := by
    rintro rfl
    apply h3n
    rw [Xu_zero, one_mul]
    exact hn₂
  have hx : x ≠ 0 := by
    rintro rfl
    apply h4n
    rw [Xv_zero, one_mul]
    exact hn₃
  have hXu : Xu w ∈ heightSeries .G2 F 2 := Xu_mem_hs le_rfl w
  have hXv : Xv x ∈ heightSeries .G2 F 3 := Xv_mem_hs le_rfl x
  have e1 : ⁅Xu w * n₂, Xv x * n₃⁆ = ⁅Xu w, Xv x⁆ :=
    comm_mul_mul_eq (comm_hs_one (by norm_num) hn₂ hXv) (comm_hs_one (by norm_num) hn₂ hn₃)
      (comm_hs_one (by norm_num) hn₃ hXu)
  obtain ⟨e, he, hrel⟩ := rel_uv_full (K := F)
  rw [e1, hrel] at hc
  have h0 : Xc (e * (3 * (w * x))) = Xc 0 := by rw [hc, Xc_zero]
  have h2 := eq_zero_of_sign_mul' he (Xc_injective h0)
  rcases mul_eq_zero.1 h2 with h | h
  · exact h3 h
  · rcases mul_eq_zero.1 h with h | h
    · exact hw h
    · exact hx h

theorem patA [Finite F] {f g : ModGL .G2 F} (hf : f ∈ heightSeries .G2 F 1) (hfW : f ∉ Wg F)
    (hg : g ∈ Wg F) (hgU : g ∉ heightSeries .G2 F 2) (hc : ⁅g, f⁆ = 1) : False := by
  obtain ⟨t, s, n, hn, rfl⟩ := dec1 hf
  obtain ⟨s₁, n₁, hn₁, rfl⟩ := decW hg
  have ht : t ≠ 0 := by
    rintro rfl
    apply hfW
    rw [Xr_zero, one_mul]
    exact mul_mem (Xa_mem_Wg s) (hs_two_le_Wg hn)
  have hs₁ : s₁ ≠ 0 := by
    rintro rfl
    apply hgU
    rw [Xa_zero, one_mul]
    exact hn₁
  have hx : Xa s₁ ∈ heightSeries .G2 F 1 := Xa_mem_one s₁
  have hy : Xr t * Xa s ∈ heightSeries .G2 F 1 := mul_mem (Xr_mem_one t) (Xa_mem_one s)
  have key := comm_mul_mul_mem (hs_normalized (F := F) 3) hx hy (g := n₁) (h := n)
    (comm_hs (by norm_num) hn₁ hy)
    (hs_mono (by norm_num) (comm_hs (h := 2) (k := 2) (m := 4) (by norm_num) hn₁ hn))
    (comm_hs (by norm_num) hn hx)
  rw [hc, one_mul, inv_mem_iff] at key
  have k2 : ⁅Xa s₁, Xr t⁆ ∈ heightSeries .G2 F 3 := by
    have e1 : ⁅Xa s₁, Xr t * Xa s⁆ = ⁅Xa s₁, Xr t⁆ := by
      rw [comm_mul_right, commutatorElement_eq_one_iff_commute.2 (Xa_comm s₁ s)]
      simp
    rwa [e1] at key
  obtain ⟨e₁, e₂, e₃, e₄, he₁, -, -, -, hrel⟩ := rel_ar (K := F)
  rw [hrel] at k2
  have hT : Xv (e₂ * (s₁ * t ^ 2)) * (Xb (e₃ * (s₁ * t ^ 3)) * Xc (e₄ * (s₁ ^ 2 * t ^ 3))) ∈
      heightSeries .G2 F 3 :=
    mul_mem (Xv_mem_hs le_rfl _) (mul_mem (Xb_mem_hs (by norm_num) _)
      (Xc_mem_hs (by norm_num) _))
  have k3 : Xu (e₁ * (s₁ * t)) ∈ heightSeries .G2 F 3 := by
    rw [mul_assoc, mul_assoc] at k2
    exact (Subgroup.mul_mem_cancel_right _ hT).1 (by simpa only [mul_assoc] using k2)
  have h0 := eq_zero_of_sign_mul' he₁ (eq_zero_of_Xu_mem k3)
  exact mul_ne_zero hs₁ ht h0

theorem patC [Finite F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {f e₅ e' : ModGL .G2 F}
    (hf : f ∈ heightSeries .G2 F 1) (hfn : f ∉ heightSeries .G2 F 2)
    (h5 : e₅ ∈ heightSeries .G2 F 4) (h5n : e₅ ∉ heightSeries .G2 F 5)
    (he : (e' ∈ heightSeries .G2 F 2 ∧ e' ∉ heightSeries .G2 F 3) ∨
      (e' ∈ heightSeries .G2 F 3 ∧ e' ∉ heightSeries .G2 F 4))
    (hc5 : ⁅f, e₅⁆ = 1) (hc' : ⁅f, e'⁆ = 1) : False := by
  obtain ⟨t, s, n, hn, rfl⟩ := dec1 hf
  obtain ⟨y, n₄, hn₄, rfl⟩ := dec4 h5
  have hy : y ≠ 0 := by
    rintro rfl
    apply h5n
    rw [Xb_zero, one_mul]
    exact hn₄
  have hx : Xr t * Xa s ∈ heightSeries .G2 F 1 := mul_mem (Xr_mem_one t) (Xa_mem_one s)
  have hXb : Xb y ∈ heightSeries .G2 F 4 := Xb_mem_hs le_rfl y
  have hs : s = 0 := by
    have e1 : ⁅Xr t * Xa s * n, Xb y * n₄⁆ = ⁅Xr t * Xa s, Xb y⁆ :=
      comm_mul_mul_eq (comm_hs_one (by norm_num) hn hXb) (comm_hs_one (by norm_num) hn hn₄)
        (comm_hs_one (by norm_num) hn₄ hx)
    obtain ⟨e, he', hab⟩ := rel_ab (K := F)
    have e2 : ⁅Xr t * Xa s, Xb y⁆ = Xc (e * (s * y)) := by
      rw [comm_mul_left, hab, commutatorElement_eq_one_iff_commute.2 (comm_rb t y), mul_one,
        (comm_rc t (e * (s * y))).eq]
      simp
    rw [e1, e2] at hc5
    have h0 : Xc (e * (s * y)) = Xc 0 := by rw [hc5, Xc_zero]
    have h1 := eq_zero_of_sign_mul' he' (Xc_injective h0)
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h hy
  have ht : t = 0 := by
    rcases he with ⟨he2, he2n⟩ | ⟨he3, he3n⟩
    · obtain ⟨w, n₂, hn₂, rfl⟩ := dec2 he2
      have hw : w ≠ 0 := by
        rintro rfl
        apply he2n
        rw [Xu_zero, one_mul]
        exact hn₂
      have hXu : Xu w ∈ heightSeries .G2 F 2 := Xu_mem_hs le_rfl w
      have key := comm_mul_mul_mem (hs_normalized (F := F) 4) hx
        (mem_one_of_mem (by norm_num) hXu) (g := n) (h := n₂)
        (comm_hs (by norm_num) hn hXu)
        (hs_mono (by norm_num) (comm_hs (h := 2) (k := 3) (m := 5) (by norm_num) hn hn₂))
        (comm_hs (by norm_num) hn₂ hx)
      rw [hc', one_mul, inv_mem_iff] at key
      have e1 : ⁅Xr t * Xa s, Xu w⁆ = ⁅Xr t, Xu w⁆ := by
        rw [comm_mul_left, commutatorElement_eq_one_iff_commute.2 (comm_au s w)]
        simp
      rw [e1] at key
      obtain ⟨e₁, e₂, e₃, he₁, -, -, hrel⟩ := rel_ru_full (K := F)
      rw [hrel] at key
      have hT : Xc (e₂ * (-3 * (t * w ^ 2))) * Xb (e₃ * (-3 * (t ^ 2 * w))) ∈
          heightSeries .G2 F 4 :=
        mul_mem (Xc_mem_hs (by norm_num) _) (Xb_mem_hs le_rfl _)
      have k3 : Xv (e₁ * (-2 * (t * w))) ∈ heightSeries .G2 F 4 :=
        (Subgroup.mul_mem_cancel_right _ hT).1 (by simpa only [mul_assoc] using key)
      have h0 := eq_zero_of_sign_mul' he₁ (eq_zero_of_Xv_mem k3)
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (neg_eq_zero.1 h) h2
      · rcases mul_eq_zero.1 h with h | h
        · exact h
        · exact absurd h hw
    · obtain ⟨x', n₃, hn₃, rfl⟩ := dec3 he3
      have hx' : x' ≠ 0 := by
        rintro rfl
        apply he3n
        rw [Xv_zero, one_mul]
        exact hn₃
      have hXv : Xv x' ∈ heightSeries .G2 F 3 := Xv_mem_hs le_rfl x'
      have key := comm_mul_mul_mem (hs_normalized (F := F) 5) hx
        (mem_one_of_mem (by norm_num) hXv) (g := n) (h := n₃)
        (comm_hs (by norm_num) hn hXv)
        (hs_mono (by norm_num) (comm_hs (h := 2) (k := 4) (m := 6) (by norm_num) hn hn₃))
        (comm_hs (by norm_num) hn₃ hx)
      rw [hc', one_mul, inv_mem_iff] at key
      have e1 : ⁅Xr t * Xa s, Xv x'⁆ = ⁅Xr t, Xv x'⁆ := by
        rw [comm_mul_left, commutatorElement_eq_one_iff_commute.2 (comm_av s x')]
        simp
      rw [e1] at key
      obtain ⟨e, he', hrel⟩ := rel_rv_full (K := F)
      rw [hrel] at key
      have h0 := eq_zero_of_sign_mul' he' (eq_zero_of_Xb_mem key)
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h h3
      · rcases mul_eq_zero.1 h with h | h
        · exact h
        · exact absurd h hx'
  subst hs
  subst ht
  apply hfn
  rw [Xr_zero, Xa_zero, one_mul, one_mul]
  exact hn

end Series

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank
