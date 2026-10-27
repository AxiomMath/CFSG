module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoSix
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoEight

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open
open AschbacherComponentAction
open scoped Pointwise

variable {H : Type*} [Group H] [Finite H]

theorem centralizer_quotient_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {u : H} (hu : IsPGroup 2 (Subgroup.zpowers u)) :
    Subgroup.centralizer ({QuotientGroup.mk' N u} : Set (H ⧸ N)) =
      (Subgroup.centralizer ({u} : Set H)).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · intro q hq
    let act : Subgroup.zpowers u →* MulAut H := MulAut.conj.comp (Subgroup.zpowers u).subtype
    have hNinv : ∀ a : Subgroup.zpowers u, ∀ n ∈ N, act a n ∈ N := fun a n hn =>
      (inferInstance : N.Normal).conj_mem n hn a
    have hcop : ¬ 2 ∣ Nat.card N := fun h =>
      (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
    have hfix := Semidihedral.Principal.coprime_fixed_point_lifting 2 hu act N hNinv hcop
    have hq' : q ∈ {q : H ⧸ N | ∀ a : Subgroup.zpowers u,
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction act N hNinv a q = q} := by
      intro a
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hc : Commute (QuotientGroup.mk' N h) (QuotientGroup.mk' N u) :=
        Subgroup.mem_centralizer_singleton_iff.mp hq
      change QuotientGroup.mk' N ((a : H) * h * (a : H)⁻¹) = QuotientGroup.mk' N h
      rw [map_mul, map_mul, map_inv, ← hk, map_zpow, ((hc.zpow_right k).eq).symm,
        mul_inv_cancel_right]
    rw [hfix] at hq'
    obtain ⟨c, hc, hcq⟩ := hq'
    refine ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr ?_, hcq⟩
    have h1 : u * c * u⁻¹ = c := hc ⟨u, Subgroup.mem_zpowers u⟩
    calc c * u = (u * c * u⁻¹) * u := by rw [h1]
      _ = u * c := by group
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']

omit [Finite H] in
theorem isPGroup_zpowers_of_orderOf_eq_two {u : H} (hu : orderOf u = 2) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])

theorem centralizer_quotient_odd (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    (u : H) (hu : orderOf u = 2) :
    Subgroup.centralizer ({QuotientGroup.mk' N u} : Set (H ⧸ N)) =
      (Subgroup.centralizer ({u} : Set H)).map (QuotientGroup.mk' N) :=
  centralizer_quotient_of_isPGroup N hN (isPGroup_zpowers_of_orderOf_eq_two hu)

theorem mem_normalizer_of_conj_le {V : Subgroup H} {g : H}
    (h : ∀ v ∈ V, g * v * g⁻¹ ∈ V) : g ∈ Subgroup.normalizer (V : Set H) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem normalizer_quotient_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {V : Subgroup H} (hV : IsPGroup 2 V) :
    Subgroup.normalizer ((V.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) =
      (Subgroup.normalizer (V : Set H)).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm _ (Subgroup.le_normalizer_map _)
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  set W := V ⊔ N with hWdef
  have hVW : V ≤ W := le_sup_left
  have hxW : x ∈ Subgroup.normalizer (W : Set H) := by
    have hW : (V.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = W := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← hW]
    exact Subgroup.le_normalizer_comap _ hq
  have hNodd : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have hVN : N ⊓ V = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_of_coprime hV hNodd
  have hcardW : Nat.card W = Nat.card N * Nat.card V := by
    have h1 := Subgroup.relIndex_mul_card (H := N) (K := W)
    rw [inf_of_le_left (le_sup_right : N ≤ W), Subgroup.relIndex_sup_right,
      ← Subgroup.inf_relIndex_right, hVN, Subgroup.relIndex_bot_left] at h1
    rw [← h1, mul_comm]
  have hindex : ∀ V' : Subgroup H, V' ≤ W → Nat.card V' = Nat.card V →
      ¬ 2 ∣ (V'.subgroupOf W).index := by
    intro V' hV'W hV'card
    have h1 := Subgroup.relIndex_mul_card (H := V') (K := W)
    rw [inf_of_le_left hV'W, hcardW, hV'card] at h1
    have h2 : V'.relIndex W = Nat.card N := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    change ¬ 2 ∣ V'.relIndex W
    rw [h2]
    exact hNodd
  let P₁ : Sylow 2 W := (hV.comap_subtype (K := W)).toSylow (hindex V hVW rfl)
  set V' : Subgroup H := MulAut.conj x • V with hV'
  have hV'W : V' ≤ W := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hy' : x⁻¹ * y * x ∈ W := by
      have : (MulAut.conj x)⁻¹ • y = x⁻¹ * y * x := by
        rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
      exact hVW (this ▸ hy)
    have := (Subgroup.mem_normalizer_iff.mp hxW (x⁻¹ * y * x)).mp hy'
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using this
  have hV'card : Nat.card V' = Nat.card V :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj x) V).toEquiv).symm
  have hV'2 : IsPGroup 2 V' := hV.of_equiv (Subgroup.equivSMul (MulAut.conj x) V)
  let P₂ : Sylow 2 W := (hV'2.comap_subtype (K := W)).toSylow (hindex V' hV'W hV'card)
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W P₁ P₂
  have hsub : (MulAut.conj (w : H) • V).subgroupOf W = V'.subgroupOf W := by
    rw [← Subgroup.conj_smul_subgroupOf hVW w]
    have h1 : ((w • P₁ : Sylow 2 W) : Subgroup W) = MulAut.conj w • V.subgroupOf W := rfl
    have h2 : ((P₂ : Sylow 2 W) : Subgroup W) = V'.subgroupOf W := rfl
    rw [← h1, ← h2, hw]
  have hconjV : MulAut.conj (w : H) • V = V' := by
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (Subgroup.conj_smul_le_of_le hVW w),
      inf_of_le_left hV'W] at hsub
    exact hsub
  have hnorm : (w : H)⁻¹ * x ∈ Subgroup.normalizer (V : Set H) := by
    apply mem_normalizer_of_conj_le
    intro v hv
    have hxv : x * v * x⁻¹ ∈ MulAut.conj (w : H) • V := by
      rw [hconjV, hV']
      have := Subgroup.smul_mem_pointwise_smul v (MulAut.conj x) V hv
      simpa only [MulAut.smul_def, MulAut.conj_apply] using this
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv] at hxv
    have heq : (w : H)⁻¹ * x * v * ((w : H)⁻¹ * x)⁻¹ = (w : H)⁻¹ * (x * v * x⁻¹) * (w : H) := by
      group
    rw [heq]
    exact hxv
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp w.2
  refine ⟨y * ((w : H)⁻¹ * x), (Subgroup.normalizer (V : Set H)).mul_mem
    (Subgroup.le_normalizer hy) hnorm, ?_⟩
  have hz1 : QuotientGroup.mk' N z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
  calc QuotientGroup.mk' N (y * ((w : H)⁻¹ * x))
      = QuotientGroup.mk' N y * QuotientGroup.mk' N z * QuotientGroup.mk' N ((w : H)⁻¹ * x) := by
        rw [hz1, mul_one, map_mul]
    _ = QuotientGroup.mk' N x := by
        rw [← map_mul, ← map_mul, ← mul_assoc, hyz, mul_inv_cancel, one_mul]

theorem quotient_injective_on_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {U : Subgroup H} (hU : IsPGroup 2 U) {u v : H} (hu : u ∈ U) (hv : v ∈ U)
    (h : QuotientGroup.mk' N u = QuotientGroup.mk' N v) : u = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNodd : ¬ 2 ∣ Nat.card N := fun h =>
    (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have hUN := inf_eq_bot_of_isPGroup_of_coprime hU hNodd
  have hmem : u⁻¹ * v ∈ U ⊓ N := ⟨U.mul_mem (U.inv_mem hu) hv, QuotientGroup.eq.mp h⟩
  rw [hUN, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem)

theorem map_ne_bot_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {V : Subgroup H} (hV : IsPGroup 2 V) (hne : V ≠ ⊥) :
    V.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hbot
  apply hne
  rw [eq_bot_iff]
  intro v hv
  have h1 : QuotientGroup.mk' N v = QuotientGroup.mk' N 1 := by
    rw [map_one]
    exact (Subgroup.map_eq_bot_iff _).mp hbot hv
  exact Subgroup.mem_bot.mpr (quotient_injective_on_of_isPGroup N hN hV hv V.one_mem h1)

theorem gammaOne_quotient_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {U : Subgroup H} (hU : IsPGroup 2 U) :
    gammaOne (U.map (QuotientGroup.mk' N)) = (gammaOne U).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨Vb, hVbU, hVbne, rfl⟩
    set V := Vb.comap π ⊓ U with hVdef
    have hVU : V ≤ U := inf_le_right
    have hV2 : IsPGroup 2 V := hU.to_le hVU
    have hVmap : V.map π = Vb := by
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        exact hv.1
      · intro q hq
        obtain ⟨u, huU, rfl⟩ := hVbU hq
        exact ⟨u, ⟨hq, huU⟩, rfl⟩
    have hVne : V ≠ ⊥ := by
      intro hbot
      apply hVbne
      rw [← hVmap, hbot, Subgroup.map_bot]
    rw [← hVmap, normalizer_quotient_of_isPGroup N hN hV2]
    exact Subgroup.map_mono (normalizer_le_gammaOne U V hVU hVne)
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    rintro _ ⟨V, hVU, hVne, rfl⟩
    rw [← Subgroup.map_le_iff_le_comap, ← normalizer_quotient_of_isPGroup N hN (hU.to_le hVU)]
    exact normalizer_le_gammaOne _ _ (Subgroup.map_mono hVU)
      (map_ne_bot_of_isPGroup N hN (hU.to_le hVU) hVne)

theorem centralizerJoin_quotient_of_isPGroup (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N))
    {U : Subgroup H} (hU : IsPGroup 2 U) :
    centralizerJoin (U.map (QuotientGroup.mk' N)) =
      (centralizerJoin U).map (QuotientGroup.mk' N) := by
  set π := QuotientGroup.mk' N
  have hzp : ∀ u ∈ U, IsPGroup 2 (Subgroup.zpowers u) := fun u hu =>
    hU.to_le (Subgroup.zpowers_le.mpr hu)
  apply le_antisymm
  · apply iSup₂_le
    rintro ⟨q, hq⟩ hne
    obtain ⟨u, huU, rfl⟩ := hq
    have hune : u ≠ 1 := by
      rintro rfl
      exact hne (map_one π)
    change Subgroup.centralizer ({π u} : Set (H ⧸ N)) ≤ _
    rw [centralizer_quotient_of_isPGroup N hN (hzp u huU)]
    exact Subgroup.map_mono (centralizer_le_centralizerJoin U huU hune)
  · rw [centralizerJoin, Subgroup.map_iSup]
    apply iSup_le
    rintro ⟨u, huU⟩
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hune
    change (Subgroup.centralizer ({u} : Set H)).map π ≤ _
    rw [← centralizer_quotient_of_isPGroup N hN (hzp u huU)]
    apply centralizer_le_centralizerJoin _ (Subgroup.mem_map_of_mem π huU)
    intro h1
    apply hune
    exact quotient_injective_on_of_isPGroup N hN hU huU U.one_mem (h1.trans (map_one π).symm)

end CFSG.ComponentClassification.AschbacherToolkit
