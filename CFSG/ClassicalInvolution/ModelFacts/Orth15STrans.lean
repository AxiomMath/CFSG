module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15SNbr

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

section Group

variable {G : Type} [Group G]

theorem map_le_normalizer_map {Y : Subgroup G} {R S : Subgroup Y}
    (h : R ≤ Subgroup.normalizer (S : Set Y)) :
    R.map Y.subtype ≤ Subgroup.normalizer ((S.map Y.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨r, hr, rfl⟩
  have hSY : S.map Y.subtype ≤ Y := Subgroup.map_subtype_le S
  refine (mem_normalizer_subgroupOf_iff hSY).mpr ?_
  rw [subgroupOf_map_subtype']
  exact h hr

end Group

section Trans

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_USet_of_exact (hΩ : HypOmegaMod p f Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {U : Subgroup G} (hU : U ∈ USet (centralizingMembers (exactFamily Ω c) {c})) :
    U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨⟨K, hK, rfl⟩, -⟩ := hL
  have hRK : IsSylow2In R K := ((isSylow2In_exactCore_iff hΩ hc2 hK.1 hK.2).mp hRL).1
  exact ⟨R, mem_RSet_of_isSylow2In hK.1 hRK, hUR, hcyc, hidx⟩

theorem isUniqueInvolution_of_le_member (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K A : Subgroup G} (hK : K ∈ Ω) (hAK : A ≤ K) {z : G} (hz : IsUniqueInvolution A z) :
    IsUniqueInvolution K z := by
  obtain ⟨b, hb⟩ := hΩ.classical K hK
  have hbK : IsUniqueInvolution K b := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hb
  have hzb : z = b := by
    rcases hbK.unique z (hAK hz.mem) hz.sq with h | h
    · exact absurd h hz.ne_one
    · exact h
  rw [hzb]
  exact hbK

end Trans

section Cfg

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

abbrev exLayer (Ω : Set (Subgroup G)) (c : G) : Subgroup G :=
  centralizingLayer (exactFamily Ω c) {c}

theorem cfg64_of_exact (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {K J : Subgroup G} (hK : K ∈ tqMembers Ω c)
    (hJ : J ∈ tqMembers Ω c)
    {zK zJ u v : ↥(exLayer Ω c)}
    {R T : Subgroup ↥(exLayer Ω c)}
    (h : Cfg64 (restrictFamily (centralizingMembers (exactFamily Ω c) {c})
        (exLayer Ω c))
      ((exactCore c K).subgroupOf (exLayer Ω c))
      ((exactCore c J).subgroupOf (exLayer Ω c)) zK zJ u v R T) :
    Cfg64 Ω K J (zK : G) (zJ : G) (u : G) (v : G)
      (R.map (exLayer Ω c).subtype)
      (T.map (exLayer Ω c).subtype) := by
  have hKc : exactCore c K ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hK, exactCore_le_centralizer c K⟩
  have hJc : exactCore c J ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hJ, exactCore_le_centralizer c J⟩
  have hKY : exactCore c K ≤ (exLayer Ω c) := le_centLayer hKc
  have hJY : exactCore c J ≤ (exLayer Ω c) := le_centLayer hJc
  have hKJ : K ≠ J := fun e => h.hKJ (by rw [e])
  have hzKc : IsUniqueInvolution (exactCore c K) (zK : G) :=
    isUniqueInvolution_of_subgroupOf h.hz hKY
  have hzJc : IsUniqueInvolution (exactCore c J) (zJ : G) :=
    isUniqueInvolution_of_subgroupOf h.hj hJY
  have hzK : IsUniqueInvolution K (zK : G) :=
    isUniqueInvolution_of_le_member hp hq hΩ hK.1 (exactCore_le_left c K) hzKc
  have hzJ : IsUniqueInvolution J (zJ : G) :=
    isUniqueInvolution_of_le_member hp hq hΩ hJ.1 (exactCore_le_left c J) hzJc
  have hnbrJ : ¬ ∃ T' : Subgroup G, IsSylow2In T' (exactCore c J) ∧
      T' ≤ Subgroup.normalizer ((exactCore c K : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notJ ⟨subgroupOf_mem_restrictFamily hJc hJY, h.hKJ.symm, T'.subgroupOf (exLayer Ω c),
      mem_RSet_restrict hJc hJY hT', Subgroup.subgroupOf_mono (exLayer Ω c) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hKY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hnbrK : ¬ ∃ T' : Subgroup G, IsSylow2In T' (exactCore c K) ∧
      T' ≤ Subgroup.normalizer ((exactCore c J : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notK ⟨subgroupOf_mem_restrictFamily hKc hKY, h.hKJ, T'.subgroupOf (exLayer Ω c),
      mem_RSet_restrict hKc hKY hT', Subgroup.subgroupOf_mono (exLayer Ω c) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hJY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hUmap : (Subgroup.zpowers u).map (exLayer Ω c).subtype = Subgroup.zpowers (u : G) :=
    MonoidHom.map_zpowers _ _
  have hVmap : (Subgroup.zpowers v).map (exLayer Ω c).subtype = Subgroup.zpowers (v : G) :=
    MonoidHom.map_zpowers _ _
  have hUG : Subgroup.zpowers (u : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hU
    rw [hUmap] at h1
    exact mem_USet_of_exact hΩ hc2 h1
  have hVG : Subgroup.zpowers (v : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hV
    rw [hVmap] at h1
    exact mem_USet_of_exact hΩ hc2 h1
  have hUK : Subgroup.zpowers (u : G) ≤ K := by
    rw [← hUmap]
    refine (Subgroup.map_mono h.hUK).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hKY]
    exact exactCore_le_left c K
  have hVJ : Subgroup.zpowers (v : G) ≤ J := by
    rw [← hVmap]
    refine (Subgroup.map_mono h.hVJ).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
    exact exactCore_le_left c J
  have hUV : Commutes (Subgroup.zpowers (u : G)) (Subgroup.zpowers (v : G)) := by
    rw [← hUmap, ← hVmap]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (h.hUV a ha b hb)
  have hRKc : IsSylow2In (R.map (exLayer Ω c).subtype) (exactCore c K) := by
    have := (isSylow2In_map_subtype_iff (Y := exLayer Ω c)).mpr h.hR
    rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
  have hTJc : IsSylow2In (T.map (exLayer Ω c).subtype) (exactCore c J) := by
    have := (isSylow2In_map_subtype_iff (Y := exLayer Ω c)).mpr h.hT
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  have hUVmap : (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map (exLayer Ω c).subtype =
      Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers (v : G) := by
    rw [Subgroup.map_sup, hUmap, hVmap]
  exact
    { hΩ := hypOmegaGen_of_mod hp hq hΩ
      hK := hK.1
      hJ := hJ.1
      hKJ := hKJ
      hz := hzK
      hj := hzJ
      notJ := not_mem_omegaNbr_of_exact hp hq hΩ hc2 hK hJ hKJ hzK hzKc.mem hnbrJ
      notK := not_mem_omegaNbr_of_exact hp hq hΩ hc2 hJ hK hKJ.symm hzJ hzJc.mem hnbrK
      hU := hUG
      hUK := hUK
      hV := hVG
      hVJ := hVJ
      hUV := hUV
      hR := ((isSylow2In_exactCore_iff hΩ hc2 hK.1 hK.2).mp hRKc).1
      hT := ((isSylow2In_exactCore_iff hΩ hc2 hJ.1 hJ.2).mp hTJc).1
      huR := by
        rw [← hUmap]
        exact Subgroup.map_mono h.huR
      hvT := by
        rw [← hVmap]
        exact Subgroup.map_mono h.hvT
      hRN := by
        rw [← hUVmap]
        exact map_le_normalizer_map h.hRN
      hTN := by
        rw [← hUVmap]
        exact map_le_normalizer_map h.hTN }

end Cfg

end CFSG.ClassicalInvolution.Asc77
