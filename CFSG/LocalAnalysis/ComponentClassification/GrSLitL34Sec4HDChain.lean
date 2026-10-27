module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Inner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDTarget

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X]

theorem eight_le_card_of_not_mem {G H : Subgroup X} (h4 : 4 ≤ Nat.card ↥(G ⊓ H)) {x : X}
    (hxG : x ∈ G) (hxH : x ∉ H) : 8 ≤ Nat.card G := by
  obtain ⟨m, hm⟩ := card_dvd_of_le (inf_le_left : G ⊓ H ≤ G)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hxH ((eq_of_le_of_card_ge (inf_le_left : G ⊓ H ≤ G) hm.le) ▸ hxG).2
  rw [hm]
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Nat.card ↥(G ⊓ H) * m := Nat.mul_le_mul h4 (by omega)

omit [Finite X] in
theorem inf_normalizer_inf (T K : Subgroup X) : T ⊓ normalizer (K : Set X) ⊓ K = T ⊓ K := by
  rw [inf_assoc, inf_of_le_right (le_normalizer : K ≤ normalizer (K : Set X))]

omit [Finite X] in
theorem conj_mem_coreActionKernel_of_mem {K : Subgroup X} {n x : X}
    (hn : n ∈ normalizer (K : Set X)) (hx : x ∈ coreActionKernel K) :
    n * x * n⁻¹ ∈ coreActionKernel K := by
  apply FooteLit.mem_coreActionKernel_conjugate_iff.mp
  rw [conjugate_eq_of_mem_normalizer hn]
  exact hx

theorem exists_chain_outer
    {K₀ T : Subgroup X}
    (e₀ : K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* Blueprint.NativeSporadic.He) (hOut : HeldOuterInvolutionRank)
    (hT2 : IsPGroup 2 T) (h1024 : Nat.card ↥(T ⊓ normalizer (K₀ : Set X) ⊓ K₀) = 1024)
    {ζ : X} (hζT : ζ ∈ T) (hζ2 : orderOf ζ = 2) (hζc : ∀ s ∈ T, s * ζ = ζ * s)
    (hζK : ζ ∈ K₀ ⊔ coreActionKernel K₀) {F : Subgroup X}
    (hFS : F ≤ T ⊓ normalizer (K₀ : Set X)) (hF : IsElemTwo F) (hF8 : Nat.card F = 8) {x : X}
    (hxF : x ∈ F) (hxK : x ∉ K₀ ⊔ coreActionKernel K₀) :
    ∃ A' : Subgroup X, A' ≤ T ⊓ K₀ ∧ IsAbelianTwoOfRank 3 A' ∧ AbelianConnectedIn T 3 F A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := T ⊓ normalizer (K₀ : Set X) with hSdef
  have hS2 : IsPGroup 2 S := hT2.to_le inf_le_left
  have hSN : S ≤ normalizer (K₀ : Set X) := inf_le_right
  have hR2 : IsPGroup 2 ↥(S ⊓ K₀) := hS2.to_le inf_le_left
  have hζζ : ζ * ζ = 1 := by rw [← pow_two, ← hζ2, pow_orderOf_eq_one]
  have hζ1 : ζ ≠ 1 := fun h => by rw [h, orderOf_one] at hζ2; exact absurd hζ2 (by norm_num)
  have hcard := card_le_two_mul_card_inf e₀ (hFS.trans hSN)
  obtain ⟨b, hbF, hbLK, hb1, hbz⟩ :
      ∃ b ∈ F, b ∈ K₀ ⊔ coreActionKernel K₀ ∧ b ≠ 1 ∧ b ≠ ζ := by
    by_contra h
    push Not at h
    have hle : F ⊓ (K₀ ⊔ coreActionKernel K₀) ≤ zpowers ζ := by
      intro w hw
      obtain ⟨hwF, hwLK⟩ := mem_inf.mp hw
      by_cases hw1 : w = 1
      · rw [hw1]
        exact one_mem _
      · rw [h w hwF hwLK hw1]
        exact mem_zpowers ζ
    have h2 := card_le_of_le hle
    rw [Nat.card_zpowers, hζ2] at h2
    omega
  have hbS : b ∈ S := hFS hbF
  have hPR : S ⊓ coreActionKernel K₀ ≤ normalizer ((S ⊓ K₀ : Subgroup X) : Set X) :=
    fun p hp => mem_normalizer_inf (le_normalizer (mem_inf.mp hp).1)
      (mem_coreActionKernel.mp (mem_inf.mp hp).2).1
  have hbset : b ∈ ((S ⊓ K₀ : Subgroup X) : Set X) *
      ((S ⊓ coreActionKernel K₀ : Subgroup X) : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hPR]
    exact inf_sup_coreActionKernel_le' e₀ hSN hS2 h1024 (mem_inf.mpr ⟨hbS, hbLK⟩)
  obtain ⟨tb, htb, pb, hpb, hbeq₀⟩ := hbset
  have hbeq : tb * pb = b := hbeq₀
  have hcomm : ∀ r ∈ S ⊓ K₀, r * pb = pb * r := fun r hr =>
    commute_of_mem_coreActionKernel hS2 (mem_inf.mp hpb).1 (mem_inf.mp hpb).2
      (mem_inf.mp hr).1 (mem_inf.mp hr).2
  have hbb : b * b = 1 := hF.2 b hbF
  have htb2 : tb * tb = 1 := by
    have htp := hcomm tb htb
    have h1 : tb * tb = (pb * pb)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      calc tb * tb * (pb * pb) = tb * (tb * pb) * pb := by group
        _ = tb * (pb * tb) * pb := by rw [htp]
        _ = tb * pb * (tb * pb) := by group
        _ = 1 := by rw [hbeq]; exact hbb
    refine eq_one_of_mem_coreActionKernel e₀ hS2 (mul_mem (mem_inf.mp htb).1 (mem_inf.mp htb).1)
      (mul_mem (mem_inf.mp htb).2 (mem_inf.mp htb).2) ?_
    rw [h1]
    exact inv_mem (mul_mem (mem_inf.mp hpb).2 (mem_inf.mp hpb).2)
  have hxS : x ∈ S := hFS hxF
  have hxN : x ∈ normalizer (K₀ : Set X) := (mem_inf.mp hxS).2
  have hxR : x ∈ normalizer ((S ⊓ K₀ : Subgroup X) : Set X) :=
    mem_normalizer_inf (le_normalizer hxS) hxN
  have hab : x * b = b * x := hF.1 x hxF b hbF
  have hatb : tb * x = x * tb := by
    have h1 : x * tb * x⁻¹ ∈ S ⊓ K₀ := (mem_normalizer_iff.mp hxR tb).mp htb
    have h2 : x * pb * x⁻¹ ∈ S ⊓ coreActionKernel K₀ :=
      mem_inf.mpr ⟨mul_mem (mul_mem hxS (mem_inf.mp hpb).1) (inv_mem hxS),
        conj_mem_coreActionKernel_of_mem hxN (mem_inf.mp hpb).2⟩
    have h3 : (x * tb * x⁻¹) * (x * pb * x⁻¹) = tb * pb := by
      calc (x * tb * x⁻¹) * (x * pb * x⁻¹) = x * (tb * pb) * x⁻¹ := by group
        _ = tb * pb := by rw [hbeq, hab]; group
    have h4 : tb⁻¹ * (x * tb * x⁻¹) = 1 := by
      refine eq_one_of_mem_coreActionKernel e₀ hS2 (mul_mem (inv_mem (mem_inf.mp htb).1)
        (mem_inf.mp h1).1) (mul_mem (inv_mem (mem_inf.mp htb).2) (mem_inf.mp h1).2) ?_
      have h5 : tb⁻¹ * (x * tb * x⁻¹) = pb * (x * pb * x⁻¹)⁻¹ := by
        rw [← mul_inv_eq_one, mul_inv_rev, inv_inv]
        calc tb⁻¹ * (x * tb * x⁻¹) * ((x * pb * x⁻¹) * pb⁻¹) =
            tb⁻¹ * ((x * tb * x⁻¹) * (x * pb * x⁻¹)) * pb⁻¹ := by group
          _ = 1 := by rw [h3]; group
      rw [h5]
      exact mul_mem (mem_inf.mp hpb).2 (inv_mem (mem_inf.mp h2).2)
    have h5 : x * tb * x⁻¹ = tb := by
      calc x * tb * x⁻¹ = tb * (tb⁻¹ * (x * tb * x⁻¹)) := by group
        _ = tb := by rw [h4, mul_one]
    calc tb * x = x * tb * x⁻¹ * x := by rw [h5]
      _ = x * tb := by group
  have hxx : x * x ∈ coreActionKernel K₀ := by rw [hF.2 x hxF]; exact one_mem _
  obtain ⟨F₂, hF₂R, hF₂x, hF₂tb, hF₂, hF₂8⟩ :=
    exists_outer_eight e₀ hOut inf_le_right hR2 h1024 hxN hxR hxK hxx htb htb2 hatb
  have hzb : ∀ u ∈ zpowers b, ∀ v ∈ zpowers ζ, u * v = v * u :=
    commute_zpowers_left fun v hv => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (show Commute b ζ from hζc b (mem_inf.mp hbS).1) k).eq
  have hD : IsElemTwo (zpowers b ⊔ zpowers ζ) :=
    (isElemTwo_zpowers hbb).sup (isElemTwo_zpowers hζζ) hzb
  have hxD : ∀ u ∈ zpowers x, ∀ v ∈ zpowers b ⊔ zpowers ζ, u * v = v * u :=
    commute_zpowers_left fun v hv => by
      refine commute_sup_right (fun u hu w hw => ?_) (fun u hu w hw => ?_) x (mem_zpowers x) v hv
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
        obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hw
        exact (Commute.zpow_zpow (show Commute x b from hab) k l).eq
      · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
        obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hw
        exact (Commute.zpow_zpow (show Commute x ζ from hζc x (mem_inf.mp hxS).1) k l).eq
  set G : Subgroup X := zpowers x ⊔ (zpowers b ⊔ zpowers ζ) with hG
  have hGe : IsElemTwo G := (isElemTwo_zpowers (hF.2 x hxF)).sup hD hxD
  have hGT : G ≤ T := sup_le (zpowers_le.mpr (mem_inf.mp hxS).1)
    (sup_le (zpowers_le.mpr (mem_inf.mp hbS).1) (zpowers_le.mpr hζT))
  have hD4 : 4 ≤ Nat.card ↥(zpowers b ⊔ zpowers ζ) :=
    four_le_card_sup_zpowers hbb hζζ hb1 hζ1 hbz (hζc b (mem_inf.mp hbS).1)
  have hG8 : 8 ≤ Nat.card G := by
    refine eight_le_card_of_not_mem (H := K₀ ⊔ coreActionKernel K₀) (hD4.trans (card_le_of_le
      (le_inf le_sup_right (sup_le (zpowers_le.mpr hbLK) (zpowers_le.mpr hζK))))) ?_ hxK
    exact mem_sup_left (mem_zpowers x)
  have hGr : IsAbelianTwoOfRank 3 G := hGe.isAbelianTwoOfRank hG8
  have hFr : IsAbelianTwoOfRank 3 F := hF.isAbelianTwoOfRank (by omega)
  have hF₂r : IsAbelianTwoOfRank 3 F₂ := hF₂.isAbelianTwoOfRank (by omega)
  have hFT : F ≤ T := hFS.trans inf_le_left
  have hcz : ∀ u ∈ T, ∀ v ∈ zpowers ζ, u * v = v * u := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
    exact (Commute.zpow_right (show Commute u ζ from hζc u hu) k).eq
  have hFG : ∀ u ∈ F, ∀ v ∈ G, u * v = v * u := by
    refine commute_sup_right (fun u hu v hv => ?_) (commute_sup_right (fun u hu v hv => ?_)
      (fun u hu v hv => hcz u (hFT hu) v hv))
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (show Commute u x from hF.1 u hu x hxF) k).eq
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (show Commute u b from hF.1 u hu b hbF) k).eq
  have hGF₂ : ∀ u ∈ G, ∀ v ∈ F₂, u * v = v * u := by
    refine commute_sup_left (commute_zpowers_left fun v hv => ?_)
      (commute_sup_left (commute_zpowers_left fun v hv => ?_)
        (fun u hu v hv => (hcz v ((hF₂R.trans inf_le_left).trans inf_le_left hv) u hu).symm))
    · exact (mem_centralizer_singleton_iff.mp (hF₂x hv)).symm
    · have h1 := mem_centralizer_singleton_iff.mp (hF₂tb hv)
      have h2 := hcomm v (hF₂R hv)
      rw [← hbeq]
      calc tb * pb * v = tb * (v * pb) := by rw [mul_assoc, ← h2]
        _ = v * tb * pb := by rw [← mul_assoc, ← h1]
        _ = v * (tb * pb) := by group
  refine ⟨F₂, le_inf ((hF₂R.trans inf_le_left).trans inf_le_left) (hF₂R.trans inf_le_right),
    hF₂r, hFT, hFr,
    (Relation.ReflTransGen.single ⟨hGT, hGr, hFG⟩).tail
      ⟨(hF₂R.trans inf_le_left).trans inf_le_left, hF₂r, hGF₂⟩⟩

end CFSG.ComponentClassification.GrSLit.HeDiag
