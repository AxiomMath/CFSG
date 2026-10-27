module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2PB
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P2GlueKernel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoComponents
import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.AGLEmbedding
  KFactsPair CFSG.Open

private theorem exists_mul_mem_comap_of_mem_sup {X : Type} [Group X] {T : Subgroup X}
    {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) :
    ∀ m : ↥((oddHull P ⊔ gnImg T T).comap (toStar T)),
      ∃ c ∈ (oddHull P).comap (toStar T), ∃ t ∈ T, (m : X) = c * t := by
  intro m
  have hSK : gnImg T T ≤ Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)) :=
    hTP.trans (normalizer_le_normalizer_oddHull P)
  have hm : toStar T (m : X) ∈
      ((oddHull P ⊔ gnImg T T : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := m.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (oddHull P) (gnImg T T) hSK,
    Set.mem_mul] at hm
  obtain ⟨k, hk, s, hs, hks⟩ := hm
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨(m : X) * t⁻¹, ?_, t, ht, by group⟩
  change toStar T ((m : X) * t⁻¹) ∈ oddHull P
  rw [map_mul, map_inv, ← hks, mul_inv_cancel_right]
  exact hk

private theorem oddHull_comap_subgroupOf_normal {X : Type} [Group X] {T : Subgroup X}
    {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) :
    (((oddHull P).comap (toStar T)).subgroupOf
      ((oddHull P ⊔ gnImg T T).comap (toStar T))).Normal := by
  have hSK : gnImg T T ≤ Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)) :=
    hTP.trans (normalizer_le_normalizer_oddHull P)
  have hle : oddHull P ⊔ gnImg T T ≤
      Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)) :=
    sup_le Subgroup.le_normalizer hSK
  refine (Subgroup.normal_subgroupOf_iff (Subgroup.comap_mono le_sup_left)).2 ?_
  intro h k hh hk
  rw [Subgroup.mem_comap] at hh ⊢
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.le_normalizer_iff.1 hle (toStar T k) hk (toStar T h) hh

private theorem isSolvable_quotient_comap_oddHull {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {P : Subgroup (X ⧸ gnC T)}
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)))
    (hN : (Subgroup.map
      (toStar (T.subgroupOf ((oddHull P ⊔ gnImg T T).comap (toStar T))))
      (((oddHull P).comap (toStar T)).subgroupOf
        ((oddHull P ⊔ gnImg T T).comap (toStar T)))).Normal) :
    Group.IsSolvable
      ((↥((oddHull P ⊔ gnImg T T).comap (toStar T)) ⧸
          gnC (T.subgroupOf ((oddHull P ⊔ gnImg T T).comap (toStar T)))) ⧸
        (Subgroup.map
          (toStar (T.subgroupOf ((oddHull P ⊔ gnImg T T).comap (toStar T))))
          (((oddHull P).comap (toStar T)).subgroupOf
            ((oddHull P ⊔ gnImg T T).comap (toStar T))))) := by
  let M : Subgroup X := (oddHull P ⊔ gnImg T T).comap (toStar T)
  let T' : Subgroup ↥M := T.subgroupOf M
  let Kt : Subgroup ↥M := ((oddHull P).comap (toStar T)).subgroupOf M
  let N : Subgroup (↥M ⧸ gnC T') := Kt.map (toStar T')
  change Group.IsSolvable ((↥M ⧸ gnC T') ⧸ N)
  haveI : N.Normal := hN
  have hTM : T ≤ M := by
    intro t ht
    change toStar T t ∈ oddHull P ⊔ gnImg T T
    exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (toStar T) ht)
  have hT'2 : IsPGroup 2 T' := hT.2.1.comap_of_injective M.subtype M.subtype_injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T' := IsPGroup.isNilpotent hT'2
  haveI : Group.IsSolvable ↥T' := IsNilpotent.to_isSolvable
  let f : ↥T' →* (↥M ⧸ gnC T') ⧸ N :=
    (QuotientGroup.mk' N).comp ((QuotientGroup.mk' (gnC T')).comp T'.subtype)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y'
    obtain ⟨c, hc, t, ht, hct⟩ :=
      exists_mul_mem_comap_of_mem_sup (T := T) (P := P) hTP m
    have hcM : c ∈ M :=
      Subgroup.comap_mono (le_sup_left : oddHull P ≤ oddHull P ⊔ gnImg T T) hc
    let t' : T' := ⟨⟨t, hTM ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩
    refine ⟨t', ?_⟩
    change (QuotientGroup.mk (s := N) ((QuotientGroup.mk' (gnC T')) (t' : ↥M))) =
      (QuotientGroup.mk (s := N) ((QuotientGroup.mk' (gnC T')) m))
    symm
    rw [QuotientGroup.eq_iff_div_mem, ← map_div]
    have hcm : m / (t' : ↥M) = ⟨c, hcM⟩ := by
      apply Subtype.ext
      change (m : X) / t = c
      rw [hct, div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [hcm]
    exact Subgroup.mem_map_of_mem (toStar T') (Subgroup.mem_subgroupOf.mpr hc)
  exact Group.isSolvable_of_surjective (f := f) hf

private theorem exists_surjective_alt_five_quotient_oddHull {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {P : Subgroup (X ⧸ gnC T)} (hP : IsTwoFourSFive P)
    (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) :
    ∃ θ : alternatingGroup (Fin 5) →*
      ↥(Subgroup.map
        (toStar (T.subgroupOf ((oddHull P ⊔ gnImg T T).comap (toStar T))))
        (((oddHull P).comap (toStar T)).subgroupOf
          ((oddHull P ⊔ gnImg T T).comap (toStar T)))),
      Function.Surjective θ := by
  let M : Subgroup X := (oddHull P ⊔ gnImg T T).comap (toStar T)
  let T' : Subgroup ↥M := T.subgroupOf M
  let Kt : Subgroup ↥M := ((oddHull P).comap (toStar T)).subgroupOf M
  let N : Subgroup (↥M ⧸ gnC T') := Kt.map (toStar T')
  change ∃ θ : alternatingGroup (Fin 5) →* ↥N, Function.Surjective θ
  obtain ⟨ψ, hψ, hψker⟩ := exists_alt_five_of_isTwoFourSFive hP
  let φK : ↥Kt →* X ⧸ gnC T := (toStar T).comp (M.subtype.comp Kt.subtype)
  let π : ↥Kt →* ↥(oddHull P) :=
    φK.codRestrict (oddHull P) fun k =>
      Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp k.2)
  have hπ : Function.Surjective π := by
    intro k
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (k : X ⧸ gnC T)
    have hxM : x ∈ M := by
      change (x : X ⧸ gnC T) ∈ oddHull P ⊔ gnImg T T
      rw [hx]
      exact Subgroup.mem_sup_left k.2
    refine ⟨⟨⟨x, hxM⟩, ?_⟩, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_comap.mpr ?_)
      change (x : X ⧸ gnC T) ∈ oddHull P
      rw [hx]
      exact k.2
    · apply Subtype.ext
      change toStar T x = (k : X ⧸ gnC T)
      exact hx
  let h : ↥Kt →* alternatingGroup (Fin 5) := ψ.comp π
  have hh : Function.Surjective h := hψ.comp hπ
  let f : ↥Kt →* ↥M ⧸ gnC T' := (QuotientGroup.mk' (gnC T')).comp Kt.subtype
  let fN : ↥Kt →* ↥N := f.codRestrict N fun k =>
    Subgroup.mem_map_of_mem (toStar T') k.2
  have hfN : Function.Surjective fN := by
    intro n
    obtain ⟨k, hk, hkn⟩ := Subgroup.mem_map.mp n.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkn⟩
  have hker : h.ker ≤ fN.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have hp : toStar T ((k : ↥M) : X) ∈ pCoreOf 2 P := (hψker (π k)).1 hk
    have hgn : (k : ↥M) ∈ gnC T' :=
      mem_gnC_subgroupOf_of_mem_pCoreOf hT hTP (k : ↥M) hp
    apply Subtype.ext
    change (QuotientGroup.mk (s := gnC T') (k : ↥M)) = 1
    exact (QuotientGroup.eq_one_iff (k : ↥M)).2 hgn
  refine ⟨MonoidHom.liftOfSurjective h hh ⟨fN, hker⟩, ?_⟩
  intro n
  obtain ⟨k, rfl⟩ := hfN n
  exact ⟨h k, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k⟩

theorem nonempty_mulEquiv_alt_five_of_isComponentOf {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) {P : Subgroup (X ⧸ gnC T)}
    (hP : IsTwoFourSFive P) (hTP : gnImg T T ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T)))
    {Lc : Subgroup (↥((oddHull P ⊔ gnImg T T).comap (toStar T)) ⧸
      gnC (T.subgroupOf ((oddHull P ⊔ gnImg T T).comap (toStar T))))}
    (hLc : IsComponentOf Lc ⊤) : Nonempty (↥Lc ≃* alternatingGroup (Fin 5)) := by
  let M : Subgroup X := (oddHull P ⊔ gnImg T T).comap (toStar T)
  let T' : Subgroup ↥M := T.subgroupOf M
  let Kt : Subgroup ↥M := ((oddHull P).comap (toStar T)).subgroupOf M
  let N : Subgroup (↥M ⧸ gnC T') := Kt.map (toStar T')
  have hKtn : Kt.Normal := oddHull_comap_subgroupOf_normal hTP
  haveI : N.Normal := hKtn.map (toStar T') (QuotientGroup.mk'_surjective _)
  have hsolv : Group.IsSolvable ((↥M ⧸ gnC T') ⧸ N) :=
    isSolvable_quotient_comap_oddHull hT hTP (by simpa using (inferInstance : N.Normal))
  haveI : Group.IsSolvable ((↥M ⧸ gnC T') ⧸ N) := hsolv
  haveI : Group.IsPerfect ↥Lc := ⟨hLc.2.2.1⟩
  have hLcN : Lc ≤ N :=
    CFSG.ComponentClassification.CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient N Lc
  haveI : Nontrivial (↥Lc ⧸ Subgroup.center ↥Lc) := hLc.2.2.2.toNontrivial
  have hLcNt : Nontrivial ↥Lc :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥Lc)).nontrivial
  have hLcne : Lc ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot Lc).mp hLcNt
  have hNne : N ≠ ⊥ := fun h => hLcne (le_bot_iff.mp (h ▸ hLcN))
  obtain ⟨θ, hθsurj⟩ := exists_surjective_alt_five_quotient_oddHull hT hP hTP
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases Subgroup.Normal.eq_bot_or_eq_top θ.ker with h | h
    · exact h
    · exfalso
      haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
      obtain ⟨n, hn⟩ := exists_ne (1 : ↥N)
      obtain ⟨x, hx⟩ := hθsurj n
      have hx1 : θ x = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)
      exact hn (hx.symm.trans hx1)
  let eN : ↥N ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩).symm
  haveI : IsSimpleGroup ↥N := MulEquiv.isSimpleGroup eN
  have hLcsub : CFSG.Open.IsSubnormal Lc N := by
    have h := CFSG.Open.IsSubnormal.inf_of_le (L := N) hLc.2.1 le_top
    rwa [inf_eq_left.mpr hLcN] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hLcsub
      (inferInstance : IsSimpleGroup ↥N) with hbot | htop
  · exact absurd hbot hLcne
  · exact ⟨(MulEquiv.subgroupCongr htop).trans eN⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
