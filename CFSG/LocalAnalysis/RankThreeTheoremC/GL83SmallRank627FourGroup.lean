module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Faithful
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure SmallRankFourGroup (M : Subgroup G) (x z : G) (U : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 U
  card_eq : Nat.card U = 4
  le_centralizer : U ≤ centralizer ({x} : Set G)
  normalized : zpowers x ⊔ zpowers z ≤ normalizer (U : Set G)
  not_le : ¬ U ≤ M
  eq_of_normalized : ∀ S : Subgroup G, S ≤ U → S ≠ ⊥ →
    zpowers x ⊔ zpowers z ≤ normalizer (S : Set G) → S = U
  le_or_le : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer ({x} : Set G) →
    zpowers x ⊔ zpowers z ≤ normalizer (S : Set G) → S ≤ M ∨ S ≤ U
  exists_inverting : ∃ t ∈ centralizer ({x} : Set G) ⊓ normalizer (U : Set G),
    t * z * t⁻¹ = z⁻¹

namespace SmallRankFourGroup

omit [Finite G] in
theorem mem_normalizer_map_subtype_iff (C : Subgroup G) (S : Subgroup C) (t : C) :
    (t : G) ∈ normalizer ((S.map C.subtype : Subgroup G) : Set G) ↔
      t ∈ normalizer (S : Set C) := by
  have h1 : (S.map C.subtype).subgroupOf C = S :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective S
  have h := Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le S)
  rw [h1] at h
  rw [← h]
  exact Iff.rfl

omit [Finite G] in
theorem mem_centralizer_map_subtype_iff (C : Subgroup G) (S : Subgroup C) (t : C) :
    (t : G) ∈ centralizer ((S.map C.subtype : Subgroup G) : Set G) ↔
      t ∈ centralizer (S : Set C) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  refine ⟨fun h s hs => Subtype.ext (h (s : G) (Subgroup.mem_map_of_mem _ hs)), fun h g hg => ?_⟩
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
  exact congrArg Subtype.val (h s hs)

omit [Finite G] in
theorem map_subtype_zpowers_sup {C : Subgroup G} {x z : G} {x' z' : C} (hx : (x' : G) = x)
    (hz : (z' : G) = z) : (zpowers x' ⊔ zpowers z').map C.subtype = zpowers x ⊔ zpowers z := by
  subst hx hz
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
theorem plane_le_normalizer_map_iff {C : Subgroup G} {x z : G} {x' z' : C} (hx : (x' : G) = x)
    (hz : (z' : G) = z) (S : Subgroup C) :
    zpowers x ⊔ zpowers z ≤ normalizer ((S.map C.subtype : Subgroup G) : Set G) ↔
      zpowers x' ⊔ zpowers z' ≤ normalizer (S : Set C) := by
  rw [← map_subtype_zpowers_sup hx hz]
  refine ⟨fun h b hb => ?_, fun h g hg => ?_⟩
  · exact (mem_normalizer_map_subtype_iff C S b).mp (h (Subgroup.mem_map_of_mem _ hb))
  · obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
    exact (mem_normalizer_map_subtype_iff C S b).mpr (h hb)

theorem isElemAbelian_card_of_mulEquiv {H : Type*} [Group H] {V : Subgroup H}
    (e : V ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun v hv => ?_⟩, ?_⟩
  · apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · have hw : ∀ w : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), w ^ 2 = 1 := by decide
    have h : (⟨v, hv⟩ : V) ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      exact hw _
    exact congrArg Subtype.val h
  · rw [Nat.card_congr e.toEquiv]
    simp

omit [Finite G] in
theorem of_map {M : Subgroup G} {x z : G} (C : Subgroup G) (hC : C = centralizer ({x} : Set G))
    {x' z' : C} (hx : (x' : G) = x) (hz : (z' : G) = z) {U : Subgroup C}
    (hel : IsElemAbelian 2 U) (hcard : Nat.card U = 4)
    (hB : zpowers x' ⊔ zpowers z' ≤ normalizer (U : Set C))
    (hnot : ¬ U ≤ M.comap C.subtype)
    (hirr : ∀ S : Subgroup C, S ≤ U → S ≠ ⊥ → zpowers x' ⊔ zpowers z' ≤ normalizer (S : Set C) →
      S = U)
    (hle : ∀ S : Subgroup C, IsPGroup 2 S → zpowers x' ⊔ zpowers z' ≤ normalizer (S : Set C) →
      S ≤ M.comap C.subtype ∨ S ≤ U)
    (hinv : ∃ t ∈ normalizer (U : Set C), t * z' * t⁻¹ = z'⁻¹) :
    SmallRankFourGroup M x z (U.map C.subtype) := by
  have hUC : U.map C.subtype ≤ C := Subgroup.map_subtype_le U
  have hSmap : ∀ S : Subgroup G, S ≤ C → (S.subgroupOf C).map C.subtype = S := fun S hSC => by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hSC]
  refine ⟨CFSG.SectionRank.isElemAbelian_map hel _, ?_, hUC.trans hC.le,
    (plane_le_normalizer_map_iff hx hz U).mpr hB, fun h => hnot fun u hu =>
      h (Subgroup.mem_map_of_mem _ hu), fun S hSU hS0 hSB => ?_, fun S hS2 hSC hSB => ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hcard
  · have hSC : S ≤ C := hSU.trans hUC
    have hS' : (S.subgroupOf C).map C.subtype = S := hSmap S hSC
    have h1 : S.subgroupOf C ≤ U := by
      rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, hS']
      exact hSU
    have h2 : S.subgroupOf C ≠ ⊥ := fun h => hS0 (by rw [← hS', h, Subgroup.map_bot])
    have h3 : zpowers x' ⊔ zpowers z' ≤ normalizer ((S.subgroupOf C : Subgroup C) : Set C) := by
      rw [← plane_le_normalizer_map_iff hx hz, hS']
      exact hSB
    rw [← hS', hirr _ h1 h2 h3]
  · have hSC' : S ≤ C := hSC.trans hC.ge
    have hS' : (S.subgroupOf C).map C.subtype = S := hSmap S hSC'
    have h3 : zpowers x' ⊔ zpowers z' ≤ normalizer ((S.subgroupOf C : Subgroup C) : Set C) := by
      rw [← plane_le_normalizer_map_iff hx hz, hS']
      exact hSB
    rcases hle _ (IsPGroup.comap_subtype hS2) h3 with h | h
    · left
      rw [← hS']
      exact Subgroup.map_le_iff_le_comap.mpr h
    · right
      rw [← hS']
      exact Subgroup.map_mono h
  · obtain ⟨t, ht, htz⟩ := hinv
    refine ⟨(t : G), Subgroup.mem_inf.mpr ⟨hC.le t.2,
      (mem_normalizer_map_subtype_iff C U t).mpr ht⟩, ?_⟩
    have h := congrArg Subtype.val htz
    simpa [hz] using h

end SmallRankFourGroup

theorem exists_smallRankFourGroup_of_caseOne (hS : Setting G) (hU0 : FullCoreLocal G)
    (h614 : GL83SmallRankProp614 G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {T : Subgroup G} (hT : SmallRankSylowTwo P M T)
    (h1 : SmallRankCaseOne x T) : ∃ U : Subgroup G, SmallRankFourGroup M x z U := by
  classical
  obtain ⟨⟨eV⟩, hcases⟩ := h1
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hzC : z ∈ C :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes x hx.mem).symm
  obtain ⟨x', hx'⟩ : ∃ x' : C, (x' : G) = x := ⟨⟨x, hxC⟩, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : C, (z' : G) = z := ⟨⟨z, hzC⟩, rfl⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) :=
    sup_le (zpowers_le.mpr hx.mem) (zpowers_le.mpr hz.mem)
  have hBM : zpowers x ⊔ zpowers z ≤ M := hBP.trans hPM
  have hBC : zpowers x ⊔ zpowers z ≤ C := sup_le (zpowers_le.mpr hxC) (zpowers_le.mpr hzC)
  have hplane : SmallRankPlane 3 (P : Subgroup G) x z := SmallRankPlane.of_situation hS hsit hx hz
  have hzx : z ∉ zpowers x := by
    intro hzmem
    have h9 := hplane.card_eq
    rw [sup_eq_left.mpr (zpowers_le.mpr hzmem), Nat.card_zpowers,
      orderOf_eq_prime hx.pow_eq_one hx.ne_one] at h9
    norm_num at h9
  have hNBM := normalizer_plane_le hS hU0 hsit hx hz
  have hCBM := centralizer_plane_le hS hsit hx hz
  have hNBz := normalizer_plane_le_normalizer_zpowers hS hsit hx hz
  have hVM : T ⊓ C ≤ M := inf_le_left.trans (hT.le_core.trans (sSup_le fun N hN => hN.1))
  have hV4 : Nat.card ↥(T ⊓ C) = 4 := (SmallRankFourGroup.isElemAbelian_card_of_mulEquiv eV).2
  have hVB : zpowers x ⊔ zpowers z ≤ normalizer ((T ⊓ C : Subgroup G) : Set G) := by
    intro b hb
    have hbT : b ∈ normalizer (T : Set G) := hT.normalized (hBP hb)
    have hbC : b ∈ normalizer (C : Set G) := Subgroup.le_normalizer (hBC hb)
    rw [mem_normalizer_iff] at hbT hbC ⊢
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (hbT h) (hbC h)
  have hVne : T ⊓ C ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hV4
    omega
  have hV2 : IsPGroup 2 ↥(T ⊓ C) := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  have hNV : normalizer ((T ⊓ C : Subgroup G) : Set G) ≤ M :=
    h614 3 P M hsit x z hx hz _ ⟨T ⊓ C, hVne, hV2, rfl⟩ hVB
      ⟨T ⊓ C, le_inf Subgroup.le_normalizer hVM, hV2, hVne, hVB⟩
  have hxcen : x' ∈ center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hx']
    exact mem_centralizer_singleton_iff.mp c.2
  have hx1 : x' ≠ 1 := fun h => hx.ne_one (by rw [← hx', h]; rfl)
  have hx3 : x' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hx']; exact hx.pow_eq_one)
  have hz1 : z' ≠ 1 := fun h => hz.ne_one (by rw [← hz', h]; rfl)
  have hz3 : z' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hz']; exact hz.pow_eq_one)
  have hzx' : z' ∉ zpowers x' := by
    intro h
    apply hzx
    have h' : C.subtype z' ∈ zpowers (C.subtype x') := by
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem _ h
    rwa [show C.subtype x' = x from hx', show C.subtype z' = z from hz'] at h'
  have hZmap : (zpowers z').map C.subtype = zpowers z := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers hz'
  have hBK : zpowers x' ⊔ zpowers z' ≤ M.comap C.subtype := by
    rw [← Subgroup.map_le_iff_le_comap, SmallRankFourGroup.map_subtype_zpowers_sup hx' hz']
    exact hBM
  have hK : M.comap C.subtype ≠ ⊤ := by
    intro h
    apply hx.not_centralizer_le
    intro c hc
    have h' : (⟨c, hc⟩ : C) ∈ M.comap C.subtype := by
      rw [h]
      exact Subgroup.mem_top _
    exact h'
  have hCK : centralizer ((zpowers x' ⊔ zpowers z' : Subgroup C) : Set C) ≤ M.comap C.subtype := by
    intro t ht
    have h := (SmallRankFourGroup.mem_centralizer_map_subtype_iff C _ t).mpr ht
    rw [SmallRankFourGroup.map_subtype_zpowers_sup hx' hz'] at h
    exact hCBM h
  have hNK : normalizer ((zpowers x' ⊔ zpowers z' : Subgroup C) : Set C) ≤ M.comap C.subtype := by
    intro t ht
    have h := (SmallRankFourGroup.mem_normalizer_map_subtype_iff C _ t).mpr ht
    rw [SmallRankFourGroup.map_subtype_zpowers_sup hx' hz'] at h
    exact hNBM h
  have hNz : normalizer ((zpowers x' ⊔ zpowers z' : Subgroup C) : Set C) ≤
      normalizer ((zpowers z' : Subgroup C) : Set C) := by
    intro t ht
    have h := (SmallRankFourGroup.mem_normalizer_map_subtype_iff C _ t).mpr ht
    rw [SmallRankFourGroup.map_subtype_zpowers_sup hx' hz'] at h
    refine (SmallRankFourGroup.mem_normalizer_map_subtype_iff C (zpowers z') t).mp ?_
    rw [hZmap]
    exact hNBz h
  obtain ⟨V', hV'map, hV'el, hV'4⟩ : ∃ V' : Subgroup C, V'.map C.subtype = T ⊓ C ∧
      IsElemAbelian 2 V' ∧ Nat.card V' = 4 := by
    refine ⟨(T ⊓ C).subgroupOf C, ?_, ?_⟩
    · rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
    · exact SmallRankFourGroup.isElemAbelian_card_of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ C ≤ C)).trans eV)
  have hVK : V' ≤ M.comap C.subtype := by
    rw [← Subgroup.map_le_iff_le_comap, hV'map]
    exact hVM
  have hVB' : zpowers x' ⊔ zpowers z' ≤ normalizer (V' : Set C) := by
    rw [← SmallRankFourGroup.plane_le_normalizer_map_iff hx' hz', hV'map]
    exact hVB
  have hVz : ∃ v ∈ V', z' * v * z'⁻¹ ≠ v := by
    obtain ⟨v, hvV, hvz⟩ := exists_mem_inf_centralizer_not_commute hS hsit hx hz hT
    have hvC : v ∈ C := (Subgroup.mem_inf.mp hvV).2
    refine ⟨⟨v, hvC⟩, ?_, fun h => hvz ?_⟩
    · have hv : v ∈ V'.map C.subtype := by
        rw [hV'map]
        exact hvV
      obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hv
      have hwv' : w = ⟨v, hvC⟩ := Subtype.ext hwv
      rwa [hwv'] at hw
    · have h' := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz'] at h'
      exact mul_inv_eq_iff_eq_mul.mp h'
  have hNV' : normalizer (V' : Set C) ≤ M.comap C.subtype := by
    intro t ht
    have h := (SmallRankFourGroup.mem_normalizer_map_subtype_iff C V' t).mpr ht
    rw [hV'map] at h
    exact hNV h
  rcases hcases with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨U, hel, hcard, hB, hnot, hirr, hle, t, ht, htz⟩ :=
      l32_inspection_of_prod e hxcen hx1 hx3 hz1 hz3 hzx' hBK hK hCK hNK hNz hV'el hV'4 hVK
        hVB' hVz hNV'
    exact ⟨U.map C.subtype,
      SmallRankFourGroup.of_map C hC hx' hz' hel hcard hB hnot hirr hle ⟨t, ht, htz⟩⟩
  · exact (false_of_l32_aut_prod e hxcen hx1 hx3 hz1 hz3 hzx' hBK hK hCK hNK hV'el hV'4 hVK
      hVB' hVz hNV').elim

end CFSG.LocalAnalysis.RankThreeTheoremC
