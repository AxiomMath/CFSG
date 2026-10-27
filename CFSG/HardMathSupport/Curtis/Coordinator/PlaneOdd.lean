module

public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneBlock
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceOddMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeDefs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

@[expose] def KFactBlockPlaneIbOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsParabolicTwo L J → J ≠ L →
    (∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
    Odd (Nat.card (Subgroup.center ↥L)) →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IbPerfectSections p J →
    ∀ x ∈ L, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∃ V : Subgroup Y, ⁅V, V⁆ = V ∧ V ≤ Subgroup.normalizer (L : Set Y) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 J : Set Y) ∧ x ∈ V) →
    (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) →
    ∀ E : Subgroup Y, E ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) → IsElemAbelian p E →
      Nat.card E = p ^ 2 → x ∈ E →
    ∀ y ∈ Subgroup.normalizer (L : Set Y), y ∈ Subgroup.normalizer (E : Set Y) →
      (∃ k : ℕ, y ^ p ^ k = 1) → ∀ e ∈ E, y * e * y⁻¹ = e

theorem kFactBlockPlaneIbOdd_of (hC : KFactFixCensusPrime) : KFactBlockPlaneIbOdd := by
  intro Y _ _ L J hL hcl hP hJL hJB hodd p hp hp5 hIb x hxL hxp hxC hV hfix E hE hEel hEc hxE
    y hyL hyE hyp
  have hCP : CompParab L J := ⟨hL, hcl, hodd, hP, hJL, hJB⟩
  obtain ⟨hZ, hcase⟩ := hC Y L J hCP p hp hp5 (cycPerfect_of_ib hp hIb) x
    (Subgroup.mem_sup_left hxL) hxp hxC hV hfix
  rcases hcase with hcyc | ⟨e, -, ⟨φ⟩⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hEp : IsPGroup p E := IsPGroup.of_card (n := 2) hEc
    exact absurd (hcyc E hE hEp)
      (ToralCensus.not_isCyclic_of_elemAbelian_pow hp (by norm_num) hEel hEc)
  · exact plane_core hp hp5 hZ φ (hE.trans inf_le_left) hEel hEc hyL hyE hyp

theorem twoCenterMk_mem_normalizer_map {Y : Type} [Group Y] {L A : Subgroup Y}
    {n : ↥(Subgroup.normalizer (L : Set Y))} (hn : (n : Y) ∈ Subgroup.normalizer (A : Set Y)) :
    twoCenterMk L n ∈
      Subgroup.normalizer (((A.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set _) := by
  have key : ∀ m : ↥(Subgroup.normalizer (L : Set Y)), (m : Y) ∈ Subgroup.normalizer (A : Set Y) →
      ∀ y ∈ (A.subgroupOf L).map (twoCenterHom L),
        twoCenterMk L m * y * (twoCenterMk L m)⁻¹ ∈ (A.subgroupOf L).map (twoCenterHom L) := by
    rintro m hm _ ⟨a, ha, rfl⟩
    rw [twoCenterMk_conj m a]
    exact ⟨_, (Subgroup.mem_normalizer_iff.mp hm a).mp ha, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key n hn y hy, fun hy => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hy
  simpa [mul_assoc] using this

theorem kFactBlockPlaneIb_of_odd (h : KFactBlockPlaneIbOdd) : KFactBlockPlaneIb := by
  intro Y _ _ L J hL hcl hP hJL hJB p hp hp5 hIb x hxL hxp hxC hV hfix E hEle hEel hEc hxE
    y hyL hyE hyp e he
  obtain ⟨V, hVp, hVL, hVO, hxV⟩ := hV
  obtain ⟨k, hk⟩ := hyp
  have hJLe : J ≤ L := hP.1
  have hZJ := twoCenter_le_of_isParabolicTwo hP
  have hZO : twoCenter L ≤ pCoreOf 2 J :=
    normal_pSubgroup_le_pCoreOf 2 hZJ (twoCenter_subgroupOf_normal hJLe) isPGroup_twoCenter
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hxp' : (⟨x, hxL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hEL : E ≤ L := hEle.trans inf_le_left
  let f : ↥(E.subgroupOf L) →* TwoCenterQuot L :=
    (twoCenterHom L).comp (E.subgroupOf L).subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hz : ((e : ↥L) : Y) ∈ twoCenter L := twoCenterHom_eq_one_iff.mp he
    have hep : ((e : ↥L) : Y) ^ p = 1 := hEel.2 _ e.2
    exact Subtype.ext (Subtype.ext (eq_one_of_mem_twoCenter hz hodd hep))
  have hfr : f.range = (E.subgroupOf L).map (twoCenterHom L) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEbc : Nat.card ((E.subgroupOf L).map (twoCenterHom L)) = p ^ 2 := by
    rw [← hfr, ← hEc, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hEbel : IsElemAbelian p ((E.subgroupOf L).map (twoCenterHom L)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨e₁, he₁, rfl⟩⟩ := a
      obtain ⟨_, ⟨e₂, he₂, rfl⟩⟩ := b
      apply Subtype.ext
      change twoCenterHom L e₁ * twoCenterHom L e₂ = twoCenterHom L e₂ * twoCenterHom L e₁
      rw [← map_mul, ← map_mul]
      congr 1
      have := hEel.1.is_comm.comm (⟨e₁, he₁⟩ : ↥E) ⟨e₂, he₂⟩
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    · rintro _ ⟨e, he, rfl⟩
      rw [← map_pow]
      have : e ^ p = 1 := Subtype.ext (by simpa using hEel.2 _ he)
      rw [this, map_one]
  have hEbx : ∀ e ∈ (E.subgroupOf L).map (twoCenterHom L),
      e ∈ (twoCenterHom L).range ⊓ Subgroup.centralizer
        ({twoCenterHom L ⟨x, hxL⟩} : Set (TwoCenterQuot L)) := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨⟨e, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    rw [Set.mem_singleton_iff.mp hk, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEle he).2 x rfl)
  have hnorm : twoCenterMk L ⟨y, hyL⟩ ∈
      Subgroup.normalizer (((E.subgroupOf L).map (twoCenterHom L) : Subgroup _) : Set _) :=
    twoCenterMk_mem_normalizer_map hyE
  have hypbar : ∃ k : ℕ, (twoCenterMk L ⟨y, hyL⟩) ^ p ^ k = 1 := by
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set Y))) ^ p ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hkey : ∀ ē ∈ (E.subgroupOf L).map (twoCenterHom L),
      twoCenterMk L ⟨y, hyL⟩ * ē * (twoCenterMk L ⟨y, hyL⟩)⁻¹ = ē := by
    refine h (TwoCenterQuot L) (twoCenterHom L).range ((J.subgroupOf L).map (twoCenterHom L))
      (isComponentOf_range hL) (isClassicalTwoOrG2_of_iso (centerQuotEquiv hL.2.2) hcl)
      (isParabolicTwo_map hP) (map_ne_range hP hJL) (ne_borel_map hP hJB)
      (odd_card_center_range hL.2.2) p hp hp5 (ibPerfectSections_map hJLe hIb)
      (twoCenterHom L ⟨x, hxL⟩) ⟨_, rfl⟩ (by rw [← map_pow, hxp', map_one]) ?_ ?_ ?_
      ((E.subgroupOf L).map (twoCenterHom L)) (fun e he => hEbx e he) hEbel hEbc
      ⟨⟨x, hxL⟩, hxE, rfl⟩ (twoCenterMk L ⟨y, hyL⟩) (by
        rw [Subgroup.normalizer_eq_top (twoCenterHom L).range]; exact Subgroup.mem_top _)
      hnorm hypbar
    ·
      intro hc
      apply hxC
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := Subgroup.mem_centralizer_iff.mp hc (twoCenterHom L ⟨l, hl⟩) ⟨_, rfl⟩
      have h2 : twoCenterHom L (⟨x, hxL⟩ * ⟨l, hl⟩ * ⟨x, hxL⟩⁻¹) = twoCenterHom L ⟨l, hl⟩ := by
        rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]
      have h3 := congrArg Subtype.val (commute_of_twoCenterHom_conj hodd hxp' h2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      calc l * x = x * l * x⁻¹ * x := by rw [h3]
        _ = x * l := by group
    ·
      refine ⟨(V.subgroupOf (Subgroup.normalizer (L : Set Y))).map (twoCenterMk L), ?_, ?_, ?_,
        ⟨⟨x, Subgroup.le_normalizer hxL⟩, hxV, rfl⟩⟩
      · rw [← Subgroup.map_commutator, commutator_subgroupOf_eq hVL hVp]
      · intro y _
        rw [Subgroup.normalizer_eq_top (twoCenterHom L).range]
        exact Subgroup.mem_top y
      · rintro _ ⟨n, hn, rfl⟩
        rw [pCoreOf_map_twoCenterHom hP]
        exact twoCenterMk_mem_normalizer hZO (hVO hn)
    ·
      rintro _ ⟨l, rfl⟩ hl
      have h2 : twoCenterHom L (⟨x, hxL⟩ * l * ⟨x, hxL⟩⁻¹) = twoCenterHom L l := by
        rw [map_mul, map_mul, map_inv]
        exact hl
      have h3 := congrArg Subtype.val (commute_of_twoCenterHom_conj hodd hxp' h2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      exact ⟨l, hfix l l.2 h3, rfl⟩
  have h1 := hkey (twoCenterHom L ⟨e, hEL he⟩) ⟨⟨e, hEL he⟩, he, rfl⟩
  rw [twoCenterMk_conj, twoCenterHom_eq_iff] at h1
  have hye : y * e * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hyE e).mp he
  have hzE : (y * e * y⁻¹)⁻¹ * e ∈ E := E.mul_mem (E.inv_mem hye) he
  have hz1 : (y * e * y⁻¹)⁻¹ * e = 1 :=
    eq_one_of_mem_twoCenter h1 hodd (hEel.2 _ hzE)
  exact inv_mul_eq_one.mp hz1

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
