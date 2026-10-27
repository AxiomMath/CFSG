module

public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3Main
public import CFSG.ClassicalInvolution.Asc77.AscT7ERNoFour

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T7T

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_oddCore {H T : Subgroup G} (hT : IsPGroup 2 T) {c : ↥H}
    (hc : c ∈ classicalInvolutionOddCore ↥H) (hcT : (c : G) ∈ T) : c = 1 := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  have h1 : orderOf c ∣ Nat.card (classicalInvolutionOddCore ↥H) := by
    have := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore ↥H) hc
    simpa using this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨(c : G), hcT⟩
  have h2 : orderOf c = 2 ^ k := by
    rw [← hk]
    simp [← Subgroup.orderOf_coe]
  have h3 : orderOf c = 1 := by
    rw [h2] at h1 ⊢
    have h4 : 2 ^ k ∣ Nat.card (classicalInvolutionOddCore ↥H) := h1
    have : Nat.Coprime (2 ^ k) (Nat.card (classicalInvolutionOddCore ↥H)) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have := Nat.Coprime.eq_one_of_dvd this h4
    simpa using this
  exact orderOf_eq_one_iff.mp h3

theorem le_centralizer_of_mem_zStarOf {H T : Subgroup G} {z : G} (hz : z ∈ zStarOf H)
    (hzT : z ∈ T) (hTH : T ≤ H) (hT : IsPGroup 2 T) :
    T ≤ Subgroup.centralizer ({z} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  unfold zStarOf at hz
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hz
  rw [Subgroup.mem_comap] at hh
  have hc := Subgroup.mem_center_iff.mp hh
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) ⟨y, hTH hy⟩)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hc
  have hzT' : (H.subtype h) ∈ T := hzT
  have hcT : (((⟨y, hTH hy⟩ : ↥H) * h)⁻¹ * (h * ⟨y, hTH hy⟩) : ↥H) = 1 := by
    refine eq_one_of_mem_oddCore (T := T) hT hc ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact T.mul_mem (T.inv_mem (T.mul_mem hy hzT')) (T.mul_mem hzT' hy)
  have h5 : (⟨y, hTH hy⟩ : ↥H) * h = h * ⟨y, hTH hy⟩ := inv_mul_eq_one.mp hcT
  have h6 := congrArg Subtype.val h5
  simpa using h6


theorem comm_of_sq_eq_one {A : Subgroup G} (hA : ∀ x ∈ A, x * x = 1) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) : x * y = y * x := by
  have h1 := hA (x * y) (A.mul_mem hx hy)
  have h2 := hA x hx
  have h3 := hA y hy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right h2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right h3
  have h4 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, hxi, hyi] at h4
  exact h4.symm

theorem eq_one_or_eq_of_isPGroup {B : Subgroup G} (hB : IsPGroup 2 B) {z : G}
    (hnosq : ∀ b ∈ B, b * b ≠ z)
    (hinv : ∀ c ∈ B, c * c = 1 → c ≠ 1 → c ≠ z → False) :
    ∀ b ∈ B, b = 1 ∨ b = z := by
  intro b
  induction h : orderOf b using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    intro hb
    by_contra hcon
    push Not at hcon
    obtain ⟨hb1, hbz⟩ := hcon
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hB) ⟨b, hb⟩
    have hord : orderOf b = 2 ^ k := by rw [← hk]; simp [← Subgroup.orderOf_coe]
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hord
      exact hb1 hord
    by_cases hk1 : k = 1
    · subst hk1
      have hb2 : b * b = 1 := by
        rw [← pow_two]
        exact orderOf_dvd_iff_pow_eq_one.mp (by simp [hord])
      exact hinv b hb hb2 hb1 hbz
    · have hk2 : 2 ≤ k := by omega
      have hbb : b * b ∈ B := B.mul_mem hb hb
      have hbbord : orderOf (b * b) = 2 ^ (k - 1) := by
        rw [← pow_two, orderOf_pow' _ (by norm_num : (2:ℕ) ≠ 0), hord]
        have : Nat.gcd (2 ^ k) 2 = 2 :=
          Nat.gcd_eq_right (dvd_pow_self 2 hk0)
        rw [this]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp [pow_succ]
      have hlt : orderOf (b * b) < n := by
        rw [hbbord, ← h, hord]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      rcases ih _ hlt (b * b) rfl hbb with h1 | h1
      · have h2 : orderOf b ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h1
        rw [hord] at h2
        have := Nat.le_of_dvd (by norm_num) h2
        have h3 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      · exact hnosq b hb h1

variable {p f : ℕ} [Fact p.Prime]

theorem c25_3_proved : C25_3 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp A hA hzA hAt
  by_contra hcon
  push Not at hcon
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  obtain ⟨htS, htz, g, hg⟩ := hyp.ht
  have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have htJ : IsUniqueInvolution (conjSub g K) t := by
    have := hz.conj g
    rwa [hg] at this
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 2) hA.1
  have hAC : A ≤ Subgroup.centralizer ({t} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAt a ha)
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA2 hAC
  have hP : PartIHyp p f Ω := ⟨hp, hq, hΩ, hst.aEmpty⟩
  have hΓ : gamma1 A (V ⊓ ⨆ L ∈ twinSet Ω (conjSub g K), L) ≤
      Subgroup.centralizer ({z} : Set G) := by
    unfold gamma1
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    intro y hy
    obtain ⟨⟨hyV, -⟩, hyw⟩ := (Subgroup.mem_inf.mp hy) |>.imp Subgroup.mem_inf.mp id
    have hzV : z ∈ V := hAV hzA
    have hTV : Subgroup.closure ({y, z} : Set G) ≤ V := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hyV
      · exact hzV
    have hT2 : IsPGroup 2 (Subgroup.closure ({y, z} : Set G)) := hV.2.1.to_le hTV
    have hTw : Subgroup.closure ({y, z} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hyw
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_sq_eq_one hA.2 hzA hw)
    have hzT : z ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyT : y ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    exact le_centralizer_of_mem_zStarOf (hcon w hw hw1) hzT hTw hT2 hyT
  obtain ⟨x, hxJ, hx4, hxz⟩ := l9_3 (p := p) (f := f) G Ω hP (conjSub g K) hJ t htJ V hV A hAV
    hA z hzA hz.ne_one hΓ
  refine T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ htJ (y := 1) ?_ hxJ hx4 ?_
  · simpa using htz.symm
  · simpa using hxz.symm

end T7T

end CFSG.ClassicalInvolution.Asc77
