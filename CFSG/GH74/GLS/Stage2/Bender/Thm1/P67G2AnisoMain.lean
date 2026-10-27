module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoRank1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoData
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2AnisoCent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2OuterFix
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67InnerTools
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusLocalCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.SteinbergBN CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

section Pure

theorem cube_root_of_orderOf_eq_three {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3) :
    (ζ : L) ^ 2 + (ζ : L) + 1 = 0 ∧ (ζ : L) ≠ 1 := by
  have hζ1 : (ζ : L) ≠ 1 := fun h => by
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ
    omega
  refine ⟨?_, hζ1⟩
  have h3 : (ζ : L) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    exact congrArg Units.val this |>.trans (by simp)
  have h0 : ((ζ : L) - 1) * ((ζ : L) ^ 2 + (ζ : L) + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hζ1)

theorem five_le_of_odd_of_three_dvd_succ {q : ℕ} (hq1 : 2 ≤ q) (hodd : Odd q)
    (h3 : 3 ∣ q + 1) : 5 ≤ q := by
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨m, hm⟩ := h3
  omega

end Pure

section Plane12


variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

theorem torus_of_commute_plane {g' : ModGL .G2 K₂}
    (hΓY : conjEntrywiseImage K g' ≤ adjointGroup .G2 K₂)
    (hcent : ∀ x ∈ adjointGroup .G2 K₂, (∀ v ∈ torusTorsion K₂ 3, x * v = v * x) →
      x ∈ torusGroup .G2 K₂)
    {E : Subgroup ↥(adjointGroup .G2 K)} (hEtor : E.map (twistEmb g') = torusTorsion K₂ 3)
    {t : ↥(adjointGroup .G2 K)} (ht : ∀ e ∈ E, t * e = e * t) :
    twistEmb g' t ∈ torusGroup .G2 K₂ := by
  have htY : twistEmb g' t ∈ adjointGroup .G2 K₂ := hΓY (by
    rw [← map_twistEmb_top]
    exact Subgroup.mem_map.2 ⟨t, Subgroup.mem_top t, rfl⟩)
  refine hcent _ htY fun v hv => ?_
  rw [← hEtor] at hv
  obtain ⟨e, he, rfl⟩ := hv
  rw [← map_mul, ← map_mul, ht e he]

theorem exists_plane_elt_mulSingle {g' : ModGL .G2 K₂}
    {E : Subgroup ↥(adjointGroup .G2 K)} (hEtor : E.map (twistEmb g') = torusTorsion K₂ 3)
    {ζ : K₂ˣ} (hζ : orderOf ζ = 3) (i : Fin Tag.G2.rank) :
    ∃ a ∈ E, a ≠ 1 ∧ twistEmb g' a = rootDiagUnit .G2 (Pi.mulSingle i ζ) := by
  have hmem := rootDiagUnit_mulSingle_mem_torusTorsion (k := K₂) hζ i
  rw [← hEtor] at hmem
  obtain ⟨a, ha, hψ⟩ := hmem
  refine ⟨a, ha, fun h1 => ?_, hψ⟩
  rw [h1, map_one] at hψ
  have h2 : Pi.mulSingle i ζ = (1 : Fin Tag.G2.rank → K₂ˣ) :=
    rootDiagUnit_injective (τ := .G2) (K := K₂) (hψ.symm.trans rootDiagUnit_one.symm)
  have h3 := congrFun h2 i
  simp only [Pi.mulSingle_eq_same, Pi.one_apply] at h3
  rw [h3, orderOf_one] at hζ
  omega

end Plane12

section Plane3

variable {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]

theorem commute_of_mem_rootRankOne {g' : ModGL .G2 K₂} {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) {c : Fin Tag.G2.rank → K₂ˣ} (hχ : rootChar c α = 1)
    {s a : ↥(adjointGroup .G2 K)} (hs : twistEmb g' s ∈ rootRankOneGroup .G2 K₂ α)
    (ha : twistEmb g' a = rootDiagUnit .G2 c) : s * a = a * s := by
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hs
  apply twistEmb_injective (K := K) g'
  rw [map_mul, map_mul, ha, ← hA]
  exact commute_rootSL2_diag_of_rootChar_eq_one hα c hχ A

end Plane3


section Last

theorem g2_false_of_qplus_three {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ f) (h3q : 3 ∣ Nat.card K + 1)
    {V Z : Subgroup (MulAut (adjointGroup Tag.G2 K))}
    (h2 : N2Cfg (adjointGroup Tag.G2 K) 3 V Z) (h3 : N3Full (adjointGroup Tag.G2 K) V Z)
    (hinn : ∀ v ∈ V, v ∈
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range) :
    False := by
  classical
  have hcen : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)) :=
    mulAut_conj_injective_of_center_bot hcen
  obtain ⟨-, -, hVe, hVc, -, hZodd, hZcop, hZbot, hcomm⟩ := id h2
  have := hVe
  obtain ⟨E, hEe, hEc, hEV⟩ := exists_plane_of_inner hcen hVe hVc hinn
  have := hEe
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_odd_natCard hKodd
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hK5 : 5 ≤ Nat.card K := five_le_of_odd_of_three_dvd_succ hK1 hKodd h3q
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius hK2
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have hfin : Finite K₂ := Module.finite_of_finite K
  obtain ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ, hinv⟩ := exists_g2_twisted_data hKodd hdeg σ hσ
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have h3₂ : 3 ∣ Nat.card K₂ - 1 := by
    refine h3q.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hK1.le, Nat.one_le_pow 2 _ hK1.le]
    ring
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one (k := K₂) Nat.prime_three h3₂
  obtain ⟨hω, hω1⟩ := cube_root_of_orderOf_eq_three hζ
  have hcent : ∀ x ∈ adjointGroup .G2 K₂, (∀ v ∈ torusTorsion K₂ 3, x * v = v * x) →
      x ∈ torusGroup .G2 K₂ := fun x hx hc =>
    centralizer_torusTorsion_three_le (ζ : K₂) hω hω1 x hx hc
  obtain ⟨g', hg', hzdef', hEtor⟩ := exists_g_planeToTorsion h3q hdeg σ hσ hg hzC hzdef hzN hw
    hΓ hinv hcent E hEc
  have hΓ' := conjEntrywiseImage_eq_fixed σ hσ hg' hzdef'
  have hΓY : conjEntrywiseImage K g' ≤ adjointGroup .G2 K₂ := hΓ'.le.trans inf_le_left
  have hF1 : ∀ t : adjointGroup Tag.G2 K, MulAut.conj t ∈ Z → ∀ e ∈ E, t * e = e * t := by
    intro t ht e he
    have hv : MulAut.conj e ∈ V := by
      rw [← hEV]
      exact Subgroup.mem_map_of_mem _ he
    have hc := hcomm _ hv _ ht
    exact hinj (by rw [map_mul, map_mul]; exact hc.symm)
  have hF2 : ∀ a ∈ E, a ≠ 1 → ∀ s : adjointGroup Tag.G2 K, s * a = a * s →
      MulAut.conj s ∈ Subgroup.normalizer (Z : Set (MulAut (adjointGroup Tag.G2 K))) := by
    intro a ha ha1 s hsa
    have hv : MulAut.conj a ∈ V := by
      rw [← hEV]
      exact Subgroup.mem_map_of_mem _ ha
    have hv1 : MulAut.conj a ≠ 1 := fun h => ha1 (hinj (by rw [h, map_one]))
    refine h3 _ hv hv1 s ?_
    rw [mem_fixSub, MulAut.conj_apply]
    calc a * s * a⁻¹ = s * a * a⁻¹ := by rw [← hsa]
      _ = s := by group
  have hF3 : ∀ t s : adjointGroup Tag.G2 K, MulAut.conj t ∈ Z →
      MulAut.conj s ∈ Subgroup.normalizer (Z : Set (MulAut (adjointGroup Tag.G2 K))) →
      MulAut.conj (s * t * s⁻¹) ∈ Z := by
    intro t s ht hs
    have h := (Subgroup.mem_normalizer_iff.1 hs (MulAut.conj t)).1 ht
    simpa [map_mul, map_inv] using h
  have hker : ∀ α : Fin Tag.G2.rank → ℤ, (α = g2a ∨ α = g2r) → ∃ a ∈ E, a ≠ 1 ∧
      ∃ c : Fin Tag.G2.rank → K₂ˣ, twistEmb g' a = rootDiagUnit .G2 c ∧ rootChar c α = 1 := by
    rintro α (rfl | rfl)
    · obtain ⟨a, ha, ha1, hψ⟩ := exists_plane_elt_mulSingle hEtor hζ g2ir
      exact ⟨a, ha, ha1, _, hψ, by rw [rootChar_mulSingle_eq_zpow, g2a_ir, zpow_zero]⟩
    · obtain ⟨a, ha, ha1, hψ⟩ := exists_plane_elt_mulSingle hEtor hζ g2ia
      exact ⟨a, ha, ha1, _, hψ, by rw [rootChar_mulSingle_eq_zpow, g2r_ia, zpow_zero]⟩
  have hC : ∀ t : adjointGroup Tag.G2 K, MulAut.conj t ∈ Z → t = 1 := by
    intro t ht
    have htT := torus_of_commute_plane hΓY hcent hEtor (hF1 t ht)
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htT
    have hχ : ∀ α : Fin Tag.G2.rank → ℤ, (α = g2a ∨ α = g2r) → rootChar c α = 1 := by
      intro α hα
      have hαroot : IsRoot .G2 α := by
        rcases hα with rfl | rfl
        · exact isRoot_g2a
        · exact isRoot_g2r
      obtain ⟨a, ha, ha1, ca, hca, hχa⟩ := hker α hα
      refine rootChar_eq_one_of_conj_mem_torus_fixed hKodd (by omega) hdeg σ hσ hg' hzdef' hzN
        hw hαroot c ?_
      rintro r ⟨hrQ, hrΓ⟩
      rw [← map_twistEmb_top] at hrΓ
      obtain ⟨s, -, rfl⟩ := hrΓ
      have hsa : s * a = a * s := commute_of_mem_rootRankOne hαroot hχa hrQ hca
      have hst := hF1 _ (hF3 t s ht (hF2 a ha ha1 s hsa))
      have h := torus_of_commute_plane hΓY hcent hEtor hst
      simpa [map_mul, map_inv, hc] using h
    have hc1 : c = 1 := by
      funext i
      rcases fin_G2_cases i with rfl | rfl
      · have h := hχ g2a (Or.inl rfl)
        rw [rootChar_g2a] at h
        simpa using h
      · have h := hχ g2r (Or.inr rfl)
        rw [rootChar_g2r] at h
        simpa using h
    rw [hc1, rootDiagUnit_one] at hc
    exact twistEmb_injective (K := K) g' (by rw [hc, map_one])
  let S : Subgroup (adjointGroup Tag.G2 K) :=
    (rootRankOneGroup .G2 K₂ g2a ⊓ conjEntrywiseImage K g').comap (twistEmb g')
  have hScard : Nat.card S = Nat.card K * (Nat.card K ^ 2 - 1) := by
    have h1 : S.map (twistEmb g') = rootRankOneGroup .G2 K₂ g2a ⊓ conjEntrywiseImage K g' := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, map_twistEmb_top]
      exact inf_of_le_right inf_le_right
    rw [← Subgroup.card_map_of_injective (twistEmb_injective (K := K) g'), h1]
    exact natCard_rootRankOne_inf_conjEntrywiseImage hKodd hdeg σ hσ hg' hzdef' hzN hw isRoot_g2a
  have hSfix : ∀ z' ∈ Z, ∀ s ∈ S, z' s = s := by
    intro z' hz' s hs
    obtain ⟨a, ha, ha1, ca, hca, hχa⟩ := hker g2a (Or.inl rfl)
    have hsa : s * a = a * s := commute_of_mem_rootRankOne isRoot_g2a hχa hs.1 hca
    have hnorm := hF2 a ha ha1 s hsa
    have hmem : MulAut.conj s * z' * (MulAut.conj s)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.1 hnorm z').1 hz'
    have hmem2 : MulAut.conj s * z' * (MulAut.conj s)⁻¹ * z'⁻¹ ∈ Z :=
      Z.mul_mem hmem (Z.inv_mem hz')
    have e1 : MulAut.conj s * z' * (MulAut.conj s)⁻¹ * z'⁻¹ = MulAut.conj (s * (z' s)⁻¹) := by
      have h := mul_mulAutConj_mul_inv z' s
      calc MulAut.conj s * z' * (MulAut.conj s)⁻¹ * z'⁻¹ =
          MulAut.conj s * (z' * (MulAut.conj s)⁻¹ * z'⁻¹) := by group
        _ = MulAut.conj s * (z' * MulAut.conj s * z'⁻¹)⁻¹ := by group
        _ = MulAut.conj s * (MulAut.conj (z' s))⁻¹ := by rw [h]
        _ = MulAut.conj (s * (z' s)⁻¹) := by rw [map_mul, map_inv]
    rw [e1] at hmem2
    have h1 := hC _ hmem2
    exact (mul_inv_eq_one.1 h1).symm
  obtain ⟨z', hz'Z, hz'1⟩ : ∃ z' ∈ Z, z' ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZbot (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  have hz'ord : orderOf z' ≠ 1 := fun h => hz'1 (orderOf_eq_one_iff.1 h)
  have hodvd : orderOf z' ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hz'Z
  have hspr : (Nat.minFac (orderOf z')).Prime := Nat.minFac_prime hz'ord
  have hsdvd : Nat.minFac (orderOf z') ∣ orderOf z' := Nat.minFac_dvd _
  have hsZ : Nat.minFac (orderOf z') ∣ Nat.card Z := hsdvd.trans hodvd
  have hs2 : Nat.minFac (orderOf z') ≠ 2 := fun h => by
    rw [h] at hsZ
    exact (Nat.not_even_iff_odd.2 hZodd) (even_iff_two_dvd.2 hsZ)
  have hs3 : Nat.minFac (orderOf z') ≠ 3 := fun h => by
    rw [h] at hsZ
    have := Nat.Coprime.eq_one_of_dvd hZcop.symm hsZ
    omega
  have hs5 : 5 ≤ Nat.minFac (orderOf z') := by
    have h2le := hspr.two_le
    have h4 : Nat.minFac (orderOf z') ≠ 4 := fun h => by
      rw [h] at hspr
      exact absurd hspr (by decide)
    omega
  have hz1Z : z' ^ (orderOf z' / Nat.minFac (orderOf z')) ∈ Z := Z.pow_mem hz'Z _
  have hz1ord : orderOf (z' ^ (orderOf z' / Nat.minFac (orderOf z'))) =
      Nat.minFac (orderOf z') :=
    orderOf_pow_orderOf_div (orderOf_pos z').ne' hsdvd
  have hz1inn : ¬ IsInnerAut (z' ^ (orderOf z' / Nat.minFac (orderOf z'))) := by
    rintro ⟨t, ht⟩
    have ht1 : t = 1 := hC t (by rw [ht]; exact hz1Z)
    rw [ht1, map_one] at ht
    rw [← ht, orderOf_one] at hz1ord
    omega
  exact g2_false_of_outer_fixing_sl2 hp hp2 hf K hK hspr hs5 _ hz1ord hz1inn S hScard
    (fun x hx => hSfix _ hz1Z x hx)

end Last

end CFSG.GH74.GLS.Stage2.Bender.Thm1
