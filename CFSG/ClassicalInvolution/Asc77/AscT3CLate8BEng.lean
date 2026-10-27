module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate8AEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20G.late_stepA (d : Std20G K K' J S R R' W V z t)
    (hc7 : centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z) {x : G}
    (hx : x ∈ centralizerModOdd (S : Subgroup G) K) : x ∈ R' := by
  obtain ⟨r', hr', hy⟩ := d.late_exists_y hx
  obtain ⟨y, hyx⟩ : ∃ y, y = r'⁻¹ * x := ⟨_, rfl⟩
  rw [← hyx] at hy
  have hyc : y ∈ centralizerModOdd (S : Subgroup G) K := by
    rw [hyx]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (d.late_R'_le_cmo hr')) hx
  obtain ⟨hyS, hyN, -, -⟩ := late_mem_cmoE.mp hyc
  have hWc := d.late_hWc
  have hyW : y ∈ W := by
    have hy2 : IsPGroup 2 ↥(Subgroup.zpowers y) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)
    have hyt : y * t = t * y := by
      calc y * t = (y * t * y⁻¹) * y := by group
        _ = t * y := by rw [hy]
    have hXt : ∀ w ∈ Subgroup.zpowers y, w * t = t * w := fun w hw => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (show Commute y t from hyt) n).eq
    have hXK : ∀ w ∈ Subgroup.zpowers y, conjSub w K = K := fun w hw =>
      mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr hyN hw)
    have hcommW : ∀ w ∈ Subgroup.zpowers y, ∀ v ∈ W ⊓ K, w * v = v * w := fun w hw =>
      d.late_cmo_comm_W (Subgroup.zpowers_le.mpr hyc hw)
    obtain ⟨A, hAeq, -, hAcomm, hAcmo, -⟩ :=
      (d.late_98 d.late_JW d.late_hW hy2 (Subgroup.zpowers_le.mpr hyS) hXt hXK).2 hcommW
    have hAS : A ≤ (S : Subgroup G) := by
      have h1 : A ≤ ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A := le_sup_right
      rw [← hAeq] at h1
      exact h1.trans (sup_le (sup_le (inf_le_left.trans d.hWS) (inf_le_left.trans d.hWS))
        (Subgroup.zpowers_le.mpr hyS))
    have hAz : A ≤ Subgroup.zpowers z := by
      intro a ha
      obtain ⟨-, h2, h3, h4⟩ := late_mem_cmoE.mp (hAcmo ha)
      rw [← hc7]
      exact late_mem_cmoE.mpr ⟨hAS ha, h2, h3, h4⟩
    have hyY : y ∈ ((W ⊓ J) ⊔ (W ⊓ K)) ⊔ A := by
      rw [← hAeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hAN : A ≤ Subgroup.normalizer ((((W ⊓ J) ⊔ (W ⊓ K) : Subgroup G)) : Set G) :=
      fun a ha => Subgroup.centralizer_le_normalizer
        ((((W ⊓ J) ⊔ (W ⊓ K) : Subgroup G)) : Set G)
        (Subgroup.mem_centralizer_iff.mpr fun y₀ hy₀ => (hAcomm a ha y₀ hy₀).symm)
    obtain ⟨η₀, hη₀, a, ha, hya⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hAN hyY
    have hzY : z ∈ (W ⊓ J) ⊔ (W ⊓ K) :=
      Subgroup.mem_sup_right ⟨d.late_z_mem_W, d.viol.hzK.mem⟩
    have haY : a ∈ (W ⊓ J) ⊔ (W ⊓ K) := (Subgroup.zpowers_le.mpr hzY) (hAz ha)
    have hyY' : y ∈ (W ⊓ J) ⊔ (W ⊓ K) := hya ▸ Subgroup.mul_mem _ hη₀ haY
    exact (sup_le inf_le_left inf_le_left : (W ⊓ J) ⊔ (W ⊓ K) ≤ W) hyY'
  obtain ⟨u₀, hu₀S, hu₀K⟩ := d.late_exists_swap
  obtain ⟨hu₀K', -, hu₀W, hu₀S'⟩ := d.late_swap_data hu₀S hu₀K
  have hWeq' : W = (W ⊓ K') ⊔ (W ⊓ conjSub u₀ J) := by
    calc W = conjSub u₀ W := hu₀W.symm
      _ = conjSub u₀ ((W ⊓ K) ⊔ (W ⊓ J)) := congrArg (conjSub u₀) d.late_hW
      _ = (conjSub u₀ W ⊓ conjSub u₀ K) ⊔ (conjSub u₀ W ⊓ conjSub u₀ J) := by
        rw [late_conjSub_supE, late_conjSub_infE, late_conjSub_infE]
      _ = (W ⊓ K') ⊔ (W ⊓ conjSub u₀ J) := by rw [hu₀W, hu₀K]
  have hN' : W ⊓ conjSub u₀ J ≤ Subgroup.normalizer ((W ⊓ K' : Subgroup G) : Set G) :=
    fun g hg => Subgroup.centralizer_le_normalizer ((W ⊓ K' : Subgroup G) : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun h hh => hWc h hh.1 g hg.1)
  have hyW' : y ∈ (W ⊓ K') ⊔ (W ⊓ conjSub u₀ J) := hWeq' ▸ hyW
  obtain ⟨a₁, ha₁, b₁, hb₁, hyab⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN' hyW'
  have ha₁R' : a₁ ∈ R' := by
    rw [d.late_R'_eq]
    exact ⟨ha₁.2, d.hWS ha₁.1⟩
  have hb₁c : b₁ ∈ centralizerModOdd (S : Subgroup G) K := by
    have : b₁ = a₁⁻¹ * y := by rw [hyab]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (d.late_R'_le_cmo ha₁R')) hyc
  have hb₁1 : b₁ = 1 := by
    by_contra hne
    have h2g : IsPGroup 2 ↥(Subgroup.zpowers b₁) :=
      S.isPGroup'.to_le ((Subgroup.zpowers_le.mpr hb₁.1).trans d.hWS)
    obtain ⟨n, hn2, hn1⟩ := late_exists_pow_involE h2g hne
    have hJu : IsUniqueInvolution (conjSub u₀ J) (u₀ * t * u₀⁻¹) := d.viol.hzJ.conj u₀
    have hbn : b₁ ^ n = u₀ * t * u₀⁻¹ :=
      (hJu.unique _ (Subgroup.pow_mem _ hb₁.2 n) hn2).resolve_left hn1
    have htuc : u₀ * t * u₀⁻¹ ∈ centralizerModOdd (S : Subgroup G) K :=
      hbn ▸ Subgroup.pow_mem _ hb₁c n
    have htuW : u₀ * t * u₀⁻¹ ∈ W := by
      have := conj_mem_conjSub (n := u₀) d.late_t_mem_W
      rwa [hu₀W] at this
    have htu2 : (u₀ * t * u₀⁻¹) * (u₀ * t * u₀⁻¹) = 1 := by
      calc (u₀ * t * u₀⁻¹) * (u₀ * t * u₀⁻¹) = u₀ * (t * t) * u₀⁻¹ := by group
        _ = 1 := by rw [d.viol.hzJ.sq]; group
    obtain ⟨r, hr, -, -, -, hrt⟩ := d.late_tor d.late_JW d.late_hW
    have hrK : r ∈ K := d.hR.1 hr
    have hrz : r * z * r⁻¹ = z := d.viol.hzK.conj_eq (conjSub_eq_self_of_mem hrK)
    have hz2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right d.viol.hzK.sq
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right d.viol.hzJ.sq
    have hcomm : ∀ {e : G}, e ∈ centralizerModOdd (S : Subgroup G) K → ⁅e, r⁆ ∈ oddCoreOf K :=
      fun he => (late_mem_cmoE.mp he).2.2.2 r hrK
    have hzO : z ∈ oddCoreOf K → False := fun hz =>
      d.viol.hzK.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hz
        (isPGroup_zpowers_of_mul_self_eq_one d.viol.hzK.sq d.viol.hzK.ne_one))
    rcases d.late_inv_W _ htuW htu2 with h | h | h | h
    · exact d.viol.hzJ.ne_one (by
        have : u₀ * t * u₀⁻¹ = 1 := h
        calc t = u₀⁻¹ * (u₀ * t * u₀⁻¹) * u₀ := by group
          _ = 1 := by rw [this]; group)
    · exact d.late_ne_inv (by
        have hu₀z : u₀ * z * u₀⁻¹ = z := by
          have := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hu₀S)
          calc u₀ * z * u₀⁻¹ = z * u₀ * u₀⁻¹ := by rw [this]
            _ = z := by group
        calc t = u₀⁻¹ * (u₀ * t * u₀⁻¹) * u₀ := by group
          _ = u₀⁻¹ * z * u₀ := by rw [h]
          _ = z := by
            calc u₀⁻¹ * z * u₀ = u₀⁻¹ * (u₀ * z * u₀⁻¹) * u₀ := by rw [hu₀z]
              _ = z := by group)
    · rw [h] at htuc
      apply hzO
      have h1 := hcomm htuc
      have : ⁅t, r⁆ = z := by
        calc ⁅t, r⁆ = t * (r * t * r⁻¹)⁻¹ := by rw [commutatorElement_def]; group
          _ = t * (z * t)⁻¹ := by rw [hrt]
          _ = z⁻¹ := by group
          _ = z := hz2
      rwa [this] at h1
    · rw [h] at htuc
      apply hzO
      have h1 := hcomm htuc
      have hr2 : r * (z * t) * r⁻¹ = t := by
        calc r * (z * t) * r⁻¹ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
          _ = z * (z * t) := by rw [hrz, hrt]
          _ = t := by rw [← mul_assoc, d.viol.hzK.sq, one_mul]
      have : ⁅z * t, r⁆ = z := by
        calc ⁅z * t, r⁆ = (z * t) * (r * (z * t) * r⁻¹)⁻¹ := by
              rw [commutatorElement_def]; group
          _ = (z * t) * t⁻¹ := by rw [hr2]
          _ = z := by group
      rwa [this] at h1
  have hyR' : y ∈ R' := by
    rw [hyab, hb₁1, mul_one]
    exact ha₁R'
  rw [show x = r' * y by rw [hyx]; group]
  exact R'.mul_mem hr' hyR'

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
