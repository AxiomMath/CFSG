module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeKey

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem exists_partner_of_cube {G : Type} [Group G] {a : G} (ha1 : a ≠ 1)
    {E : Subgroup G} (hE : IsElemTwo 3 E)
    (h6 : Nat.card {x : G // x ∈ E ∧ IsConj a x} = 6)
    {x : G} (hxE : x ∈ E) (hx : IsConj a x) :
    ∃ y ∈ E, IsConj a y ∧ IsConj a (x * y) := by
  classical
  haveI hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE.2]; norm_num)
  let T : Set G := {z : G | z ∈ E ∧ IsConj a z}
  have hTcard : T.ncard = 6 := by
    rw [← Nat.card_coe_set_eq]
    exact h6
  have h1notT : (1 : G) ∉ T := by
    intro h
    exact ha1 (isConj_one_left.mp h.2)
  let E1 : Set G := (E : Set G) \ {1}
  have hEcard : (E : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hE.2
  have hE1card : E1.ncard = 7 := by
    change ((E : Set G) \ {1}).ncard = 7
    rw [Set.ncard_sdiff_singleton_of_mem E.one_mem, hEcard]
  have hEfinSet : (E : Set G).Finite := Set.toFinite _
  have hTsub : T ⊆ E1 := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hz1
    exact h1notT (hz1 ▸ hz)
  have hlt : T.ncard < E1.ncard := by
    rw [hTcard, hE1card]
    norm_num
  have hTsubE : T ⊆ (E : Set G) := fun z hz => hz.1
  have hTfin : T.Finite := hEfinSet.subset hTsubE
  obtain ⟨c, hcE1, hcT⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt hTfin
  have hcE : c ∈ E := hcE1.1
  have hc1 : c ≠ 1 := by
    intro h
    exact hcE1.2 (by simpa [h])
  have hcnot : ¬ IsConj a c := fun hc => hcT ⟨hcE, hc⟩
  have hEq : ((E : Set G) \ {1, c}) = E1 \ {c} := by
    ext z
    constructor
    · rintro ⟨hzE, hz⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
      exact ⟨⟨hzE, by simpa using hz.1⟩, by simpa using hz.2⟩
    · rintro ⟨hzE1, hzc⟩
      exact ⟨hzE1.1, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨by simpa using hzE1.2, by simpa using hzc⟩⟩
  have hE2card : ((E : Set G) \ {1, c}).ncard = 6 := by
    rw [hEq, Set.ncard_sdiff_singleton_of_mem hcE1, hE1card]
  have hTsubE2 : T ⊆ (E : Set G) \ {1, c} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => h1notT (h ▸ hz), fun h => hcT (h ▸ hz)⟩
  have hTeq : T = (E : Set G) \ {1, c} :=
    Set.eq_of_subset_of_ncard_le hTsubE2 (by rw [hE2card, hTcard])
      (hEfinSet.subset (by intro z hz; exact hz.1))
  have hxT : x ∈ T := ⟨hxE, hx⟩
  have hxE2 : x ∈ (E : Set G) \ {1, c} := by
    rw [← hTeq]
    exact hxT
  have hx1 : x ≠ 1 := by
    intro h
    exact hxE2.2 (by simp [h])
  have hxc : x ≠ c := by
    intro h
    exact hxE2.2 (by simp [h])
  have hx2 : x ^ 2 = 1 := hE.1.2 x hxE
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx2)
  have hxcomm : x * c = c * x :=
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hxE⟩ ⟨c, hcE⟩)
  have hBadle : ({1, c, x, c * x} : Set G).ncard ≤ 4 := by
    have h1 := Set.ncard_insert_le (1 : G) (insert c (insert x ({(c * x)} : Set G)))
    have h2 := Set.ncard_insert_le c (insert x ({(c * x)} : Set G))
    have h3 := Set.ncard_insert_le x ({(c * x)} : Set G)
    rw [Set.ncard_singleton] at h3
    have hgoal : ({1, c, x, c * x} : Set G).ncard =
        (insert (1 : G) (insert c (insert x ({(c * x)} : Set G)))).ncard := rfl
    rw [hgoal]
    omega
  have hBadfin : ({1, c, x, c * x} : Set G).Finite :=
    Set.Finite.insert (1 : G)
      (Set.Finite.insert c (Set.Finite.insert x (Set.finite_singleton (c * x))))
  have hlt2 : ({1, c, x, c * x} : Set G).ncard < (E : Set G).ncard := by
    rw [hEcard]
    omega
  obtain ⟨y, hyE, hyBad⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt2 hBadfin
  have hy1 : y ≠ 1 := by
    intro h
    exact hyBad (by simp [h])
  have hyc : y ≠ c := by
    intro h
    exact hyBad (by simp [h])
  have hyx : y ≠ x := by
    intro h
    exact hyBad (by simp [h])
  have hycx : y ≠ c * x := by
    intro h
    exact hyBad (by simp [h])
  have hyT : y ∈ T := by
    rw [hTeq]
    refine ⟨hyE, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hy1, hyc⟩
  have hxyE : x * y ∈ E := E.mul_mem hxE hyE
  have hxy1 : x * y ≠ 1 := by
    intro h
    have hy_eq : y = x := by
      calc y = x⁻¹ * (x * y) := by group
        _ = x⁻¹ * 1 := by rw [h]
        _ = x⁻¹ := by rw [mul_one]
        _ = x := hxinv
    exact hyx hy_eq
  have hxyc : x * y ≠ c := by
    intro h
    have hy_eq : y = c * x := by
      calc y = x⁻¹ * (x * y) := by group
        _ = x⁻¹ * c := by rw [h]
        _ = x * c := by rw [hxinv]
        _ = c * x := hxcomm
    exact hycx hy_eq
  have hxyT : x * y ∈ T := by
    rw [hTeq]
    refine ⟨hxyE, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxy1, hxyc⟩
  exact ⟨y, hyE, hyT.2, hxyT.2⟩

theorem cube_transitive_of_fusion3 (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hA8 : Vert A8Shapes a z) :
    ∀ E : Subgroup G, IsElemTwo 3 E → Nat.card {x : G // x ∈ E ∧ IsConj a x} = 6 →
      (∀ x ∈ E, IsConj a x → ∀ y ∈ E, IsConj a y → ∃ g ∈ Subgroup.normalizer (E : Set G),
        g * x * g⁻¹ = y) ∧
      (∀ a' ∈ E, IsConj a a' → ∀ x ∈ (E : Set G) ∩ orb2A a a', ∀ y ∈ (E : Set G) ∩ orb2A a a',
        ∃ g ∈ Subgroup.normalizer (E : Set G) ⊓ Gx a', g * x * g⁻¹ = y) := by
  intro E hE h6
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact absurd h.orderOf_a (by rw [orderOf_one]; norm_num)
  constructor
  · intro x hxE hx y hyE hy
    obtain ⟨p, hpE, hpconj, hxp⟩ := exists_partner_of_cube ha1 hE h6 hxE hx
    obtain ⟨q, hqE, hqconj, hyq⟩ := exists_partner_of_cube ha1 hE h6 hyE hy
    obtain ⟨k, hk, hkx, -⟩ :=
      exists_mem_normalizer_conj_pair hI h hF1 hF2 hF3 hA8 hE h6
        hxE hpE hyE hqE hx hpconj hxp hy hqconj hyq
    exact ⟨k, hk, hkx⟩
  · intro a' ha'E ha' x hx y hy
    have hxE : x ∈ E := hx.1
    have hxconj : IsConj a x := hx.2.1
    have hax : IsConj a (a' * x) := hx.2.2
    have hyE : y ∈ E := hy.1
    have hyconj : IsConj a y := hy.2.1
    have hay : IsConj a (a' * y) := hy.2.2
    obtain ⟨k, hk, hka', hkx⟩ :=
      exists_mem_normalizer_conj_pair hI h hF1 hF2 hF3 hA8 hE h6
        ha'E hxE ha'E hyE ha' hxconj hax ha' hyconj hay
    refine ⟨k, ?_, hkx⟩
    rw [Subgroup.mem_inf]
    refine ⟨hk, ?_⟩
    rw [mem_Gx]
    have hcomm' : k * a' = a' * k := by
      calc k * a' = (k * a' * k⁻¹) * k := by group
        _ = a' * k := by rw [hka']
    exact hcomm'.symm

end CFSG.EvenSporadicStandard.HNRecog.Section3
