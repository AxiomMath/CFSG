module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoMain
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3G2E9

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2

open Subgroup CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBN CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem cube_roots_cases {L : Type} [Field L] {u v : Lˣ} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    u = 1 ∨ v = 1 ∨ u * v = 1 ∨ u * v ^ 2 = 1 := by
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  by_cases hv1 : v = 1
  · exact Or.inr (Or.inl hv1)
  have hquad : ∀ w : Lˣ, w ^ 3 = 1 → w ≠ 1 → (w : L) ^ 2 + (w : L) + 1 = 0 := by
    intro w hw3 hw1
    have h3 : (w : L) ^ 3 = 1 := by
      have := congrArg Units.val hw3
      simpa using this
    have hne : (w : L) ≠ 1 := fun h => hw1 (Units.ext h)
    have h0 : ((w : L) - 1) * ((w : L) ^ 2 + (w : L) + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
  have hu2 := hquad u hu hu1
  have hv2 := hquad v hv hv1
  have hfac : ((u : L) - v) * ((u : L) + v + 1) = 0 := by linear_combination hu2 - hv2
  rcases mul_eq_zero.1 hfac with h | h
  · refine Or.inr (Or.inr (Or.inr (Units.ext ?_)))
    have huv : (v : L) = u := (sub_eq_zero.1 h).symm
    push_cast
    rw [huv]
    linear_combination ((u : L) - 1) * hu2
  · refine Or.inr (Or.inr (Or.inl (Units.ext ?_)))
    have hv' : (v : L) = -1 - u := by linear_combination h
    push_cast
    rw [hv']
    linear_combination -hu2

theorem exists_root_rootChar_eq_one
    {L : Type} [Field L] {c : Fin Tag.G2.rank → Lˣ} (hc : ∀ i, c i ^ 3 = 1) :
    ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootChar c α = 1 := by
  have hgu : g2u g2ia = 1 ∧ g2u g2ir = 1 := ⟨rfl, rfl⟩
  have hgv : g2v g2ia = 1 ∧ g2v g2ir = 2 := ⟨rfl, rfl⟩
  rcases cube_roots_cases (hc g2ia) (hc g2ir) with h | h | h | h
  · exact ⟨g2a, isRoot_g2a, by rw [rootChar_g2a]; exact h⟩
  · exact ⟨g2r, isRoot_g2r, by rw [rootChar_g2r]; exact h⟩
  · refine ⟨g2u, isRoot_g2u, ?_⟩
    rw [rootChar_G2, hgu.1, hgu.2, zpow_one, zpow_one]
    exact h
  · refine ⟨g2v, isRoot_g2v, ?_⟩
    rw [rootChar_G2, hgv.1, hgv.2, zpow_one]
    exact h


theorem exists_rgroup_of_inner_twist {K : Type} [Field K] [Finite K] {r f : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = r ^ f) (h3q : 3 ∣ Nat.card K + 1)
    {x : ↥(adjointGroup Tag.G2 K)} (hx : orderOf x = 3) :
    ∃ E : Subgroup ↥(adjointGroup Tag.G2 K), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ z ∈ E, MulAut.conj x z ∈ E := by
  classical
  have hr : r.Prime := Fact.out
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hr.odd_of_ne_two hr2).pow
  have hK2 : ringChar K ≠ 2 :=
    CFSG.RankThree.Chevalley.ringChar_ne_two_of_odd_natCard hKodd
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius hK2
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have hfin : Finite K₂ := Module.finite_of_finite K
  obtain ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ, hinv⟩ := exists_g2_twisted_data hKodd hdeg σ hσ
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 :=
    CFSG.RankThree.Chevalley.natCard_eq_sq_of_finrank_eq_two hdeg
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    refine h3q.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hK1.le, Nat.one_le_pow 2 _ hK1.le]
    ring
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one (k := K₂) Nat.prime_three h3₂
  obtain ⟨hω, hω1⟩ := cube_root_of_orderOf_eq_three hζ
  have hcent : ∀ y ∈ adjointGroup .G2 K₂, (∀ v ∈ torusTorsion K₂ 3, y * v = v * y) →
      y ∈ torusGroup .G2 K₂ := fun y hy hc =>
    centralizer_torusTorsion_three_le (ζ : K₂) hω hω1 y hy hc
  have hvfix : ∀ v ∈ torusTorsion K₂ 3, twistedEntrywise z (σ : K₂ →+* K₂) v = v := by
    intro v hv
    obtain ⟨hvT, hv3⟩ := mem_torusTorsion_iff.1 hv
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvT
    have hc3 : c ^ 3 = 1 := by
      apply rootDiagUnit_injective (τ := .G2) (K := K₂)
      rw [← rootDiagUnit_pow, hv3, rootDiagUnit_one]
    rw [twistedEntrywise_rootDiagUnit hzN hw (σ : K₂ →+* K₂) hσ c]
    congr 1
    funext i
    have h3i : (c i) ^ 3 = 1 := by
      have := congrFun hc3 i
      simpa using this
    obtain ⟨m, hm⟩ := h3q
    have h1 : (c i) ^ (Nat.card K + 1) = 1 := by
      rw [hm, pow_mul, h3i, one_pow]
    have h2 : (c i) ^ Nat.card K * c i = 1 := by rw [← pow_succ]; exact h1
    simp only [Pi.inv_apply, Pi.pow_apply]
    exact inv_eq_iff_eq_inv.2 (eq_inv_of_mul_eq_one_left h2)
  have hH3 : torusTorsion K₂ 3 ≤ conjEntrywiseImage K g := by
    intro v hv
    rw [hΓ]
    have hvT := (mem_torusTorsion_iff.1 hv).1
    exact ⟨monomialSubgroup_le_adjointGroup' (torusGroup_le_monomialSubgroup hvT), hvfix v hv⟩
  set E₀ : Subgroup ↥(adjointGroup .G2 K) := (torusTorsion K₂ 3).comap (twistEmb g) with hE₀
  have hE₀map : E₀.map (twistEmb g) = torusTorsion K₂ 3 := by
    rw [hE₀, Subgroup.map_comap_eq, MonoidHom.range_eq_map, map_twistEmb_top]
    exact inf_of_le_right hH3
  have hE₀card : Nat.card E₀ = 9 := by
    rw [← Subgroup.card_map_of_injective (twistEmb_injective (K := K) g), hE₀map,
      natCard_torusTorsion h3₂]
    norm_num
  have hE₀exp : ∀ e ∈ E₀, e ^ 3 = 1 := by
    intro e he
    apply twistEmb_injective (K := K) g
    rw [map_pow, map_one]
    exact (mem_torusTorsion_iff.1 he).2
  obtain ⟨E, hxE, hEe, hEc⟩ := exists_plane_through hE₀card hE₀exp hx
  obtain ⟨g', hg', hzdef', hEtor⟩ := exists_g_planeToTorsion h3q hdeg σ hσ hg hzC hzdef hzN hw
    hΓ hinv hcent E hEc
  have hxT : twistEmb g' x ∈ torusTorsion K₂ 3 := hEtor ▸ mem_map_of_mem _ hxE
  obtain ⟨hxT1, hx3⟩ := mem_torusTorsion_iff.1 hxT
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT1
  have hc3 : ∀ i, c i ^ 3 = 1 := by
    have hc3' : c ^ 3 = 1 := by
      apply rootDiagUnit_injective (τ := .G2) (K := K₂)
      rw [← rootDiagUnit_pow, ← hc, hx3, rootDiagUnit_one]
    intro i
    have := congrFun hc3' i
    simpa using this
  obtain ⟨α, hα, hχ⟩ := exists_root_rootChar_eq_one hc3
  let S : Subgroup ↥(adjointGroup Tag.G2 K) :=
    (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g').comap (twistEmb g')
  have hScard : Nat.card S = Nat.card K * (Nat.card K ^ 2 - 1) := by
    have h1 : S.map (twistEmb g') = rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g' := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, map_twistEmb_top]
      exact inf_of_le_right inf_le_right
    rw [← Subgroup.card_map_of_injective (twistEmb_injective (K := K) g'), h1]
    exact natCard_rootRankOne_inf_conjEntrywiseImage hKodd hdeg σ hσ hg' hzdef' hzN hw hα
  have hrS : r ∣ Nat.card S := by
    rw [hScard, hK]
    exact Dvd.dvd.mul_right (dvd_pow_self r (by omega)) _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) r hrS
  have hux : (u : ↥(adjointGroup Tag.G2 K)) * x = x * u :=
    commute_of_mem_rootRankOne hα hχ u.2.1 hc
  have huo : orderOf (u : ↥(adjointGroup Tag.G2 K)) = r := by
    rw [Subgroup.orderOf_coe, hu]
  refine ⟨zpowers (u : ↥(adjointGroup Tag.G2 K)), ?_, ?_, ?_⟩
  · intro h
    have h1 : (u : ↥(adjointGroup Tag.G2 K)) = 1 := by
      have : (u : ↥(adjointGroup Tag.G2 K)) ∈ zpowers (u : ↥(adjointGroup Tag.G2 K)) :=
        mem_zpowers _
      rwa [h, mem_bot] at this
    rw [h1, orderOf_one] at huo
    exact hr.one_lt.ne huo
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huo, pow_one])
  · intro y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hcomm : Commute x ((u : ↥(adjointGroup Tag.G2 K)) ^ n) :=
      (Commute.zpow_right (show Commute x (u : ↥(adjointGroup Tag.G2 K)) from hux.symm) n)
    rw [MulAut.conj_apply, hcomm.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) n

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2
