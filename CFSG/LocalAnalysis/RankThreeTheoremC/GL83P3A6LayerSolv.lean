module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6Point
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerPoint

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

section PSolv

theorem isPSolvable_of_isPGroup_three {X : Type} [Group X] [Finite X] (h : IsPGroup 3 X) :
    CFSG.HallHigman.IsPSolvable 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro H _ T _ hs
  left
  have hQ : IsPGroup 3 (↥H ⧸ T) := ((h.to_subgroup H).to_quotient T)
  haveI := hs
  have hnt : Nontrivial (↥H ⧸ T) := IsSimpleGroup.toNontrivial
  have hcen : center (↥H ⧸ T) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥H ⧸ T)) with hb | ht
    · exact absurd hb ((Subgroup.nontrivial_iff_ne_bot _).mp hQ.center_nontrivial)
    · exact ht
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a := fun a b =>
    (mem_center_iff.mp (hcen ▸ mem_top b) a)
  haveI : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hprime : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [Subgroup.index_eq_card, hk]
  rw [hk] at hprime
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero] at hprime
    exact absurd hprime Nat.not_prime_one
  · rcases hprime.eq_one_or_self_of_dvd 3 (dvd_pow_self 3 hkpos.ne') with h1 | h1
    · omega
    · exact h1.symm

theorem isPSolvable_of_coprime_three {X : Type} [Group X] [Finite X]
    (h : Nat.Coprime 3 (Nat.card X)) : CFSG.HallHigman.IsPSolvable 3 X := by
  intro H _ T _ _
  right
  refine Nat.Coprime.coprime_dvd_right ?_ h
  exact (T.index_dvd_card).trans (Subgroup.card_subgroup_dvd_card H)

theorem isPSolvable_of_hom {X Y : Type} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hker : CFSG.HallHigman.IsPSolvable 3 ↥f.ker)
    (him : CFSG.HallHigman.IsPSolvable 3 ↥f.range) : CFSG.HallHigman.IsPSolvable 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isPSolvable_of_normal f.ker hker
    (isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange f).symm him)

theorem isPSolvable_of_le_hom {X Y : Type} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (H : Subgroup X) (hker : CFSG.HallHigman.IsPSolvable 3 ↥f.ker)
    (him : CFSG.HallHigman.IsPSolvable 3 ↥(H.map f)) : CFSG.HallHigman.IsPSolvable 3 ↥H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set g : ↥H →* Y := f.comp H.subtype with hg
  have hker' : g.ker = f.ker.subgroupOf H := by
    ext h
    simp [hg, mem_subgroupOf]
  have hrange : g.range = H.map f := by
    rw [hg, MonoidHom.range_comp, range_subtype]
  refine isPSolvable_of_hom g ?_ (by rw [hrange]; exact him)
  rw [hker']
  have h1 : CFSG.HallHigman.IsPSolvable 3 ↥(f.ker ⊓ H) := isPSolvable_of_le hker inf_le_left
  have h2 : (f.ker.subgroupOf H).map H.subtype = f.ker ⊓ H := Subgroup.subgroupOf_map_subtype _ _
  rw [← h2] at h1
  exact isPSolvable_of_mulEquiv
    ((f.ker.subgroupOf H).equivMapOfInjective H.subtype H.subtype_injective).symm h1

end PSolv

namespace PointData

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M J : Subgroup G} {x e₂ e₃ t ρ : G}
  {s : ℤ} (hpd : PointData P M J x e₂ e₃ t ρ s)

include hpd

theorem isPSolvable_inf_centralizer (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) (hM : IsCoreMaxLocal 3 P M) (hgen : IsGenericPoint 3 P M x)
    (hJ : IsA6Normal M x J) :
    CFSG.HallHigman.IsPSolvable 3 ↥(M ⊓ centralizer ({x} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA1 : A6SylowData := a6SylowData_proved
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  have hJC : J ≤ C := hJ.le_centralizer
  set O' : Subgroup ↥C := primeComplementCore (G := ↥C) 3 with hO'
  set ψ : ↥C →* GenericReduced 3 x := QuotientGroup.mk' O' with hψ
  set D : Subgroup (GenericReduced 3 x) := reducedCentralizerOfJ x J with hD
  have hDn : D.Normal := a6_reducedCentralizer_normal hJ
  have hDp : IsPGroup 3 D := a6_reducedCentralizer_isPGroup hS hU0 hA1 hp hM hgen hJ
  set φ : ↥C →* L34Quot x J := l34Hom x J with hφ
  have hφs : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hφψ : ∀ c : ↥C, φ c = QuotientGroup.mk' D.normalCore (ψ c) := fun c => rfl
  have hker : CFSG.HallHigman.IsPSolvable 3 ↥φ.ker := by
    refine isPSolvable_of_le_hom ψ φ.ker ?_ ?_
    · refine isPSolvable_of_coprime_three ?_
      rw [hψ, QuotientGroup.ker_mk']
      exact primeComplementCore_coprime 3
    · refine isPSolvable_of_isPGroup_three ?_
      refine hDp.to_le ?_
      rintro _ ⟨c, hc, rfl⟩
      have h1 : QuotientGroup.mk' D.normalCore (ψ c) = 1 := by rw [← hφψ]; exact hc
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self] at h1
      exact h1
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have he₂C : e₂ ∈ C := hJC (mem_inf.mp hpd.e₂_mem).2
  have he₃C : e₃ ∈ C := hJC (mem_inf.mp hpd.e₃_mem).2
  set T : Subgroup (L34Quot x J) := l34Img x J ((P : Subgroup G) ⊓ J) with hTdef
  have hQC : Qf x e₂ e₃ ≤ C := hpd.Q_eq ▸ inf_le_right
  have hQsub : (Qf x e₂ e₃).subgroupOf C = Qf (⟨x, hxC⟩ : C) ⟨e₂, he₂C⟩ ⟨e₃, he₃C⟩ := by
    have h := map_Qf C.subtype (⟨x, hxC⟩ : C) ⟨e₂, he₂C⟩ ⟨e₃, he₃C⟩
    simp only [Subgroup.subtype_apply] at h
    rw [← h]
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hS0 : l34Img x J ((P : Subgroup G) ⊓ C) = T := by
    apply le_antisymm
    · rw [← hpd.Q_eq]
      unfold l34Img
      rw [hQsub, map_Qf, a6_hom_x hS hU0 hp hM hgen hJ]
      refine sup_le ?_ (sup_le ?_ ?_)
      · rw [zpowers_one_eq_bot]; exact bot_le
      · exact zpowers_le.mpr ⟨⟨e₂, he₂C⟩, mem_subgroupOf.mpr hpd.e₂_mem, rfl⟩
      · exact zpowers_le.mpr ⟨⟨e₃, he₃C⟩, mem_subgroupOf.mpr hpd.e₃_mem, rfl⟩
    · exact Subgroup.map_mono (Subgroup.comap_mono (inf_le_inf_left _ hJC))
  obtain ⟨T₀, hT₀⟩ := hgen.2.2.1.exists_sylow_eq_subgroupOf
  set S : Sylow 3 (L34Quot x J) := T₀.mapSurjective hφs with hSdef
  have hST : (S : Subgroup (L34Quot x J)) = T := by
    rw [hSdef, Sylow.coe_mapSurjective, hT₀, ← hS0]
    rfl
  set N : Subgroup (L34Quot x J) := normalizer (T : Set (L34Quot x J)) with hNdef
  have hNsolv : CFSG.HallHigman.IsPSolvable 3 ↥N := by
    have hTN : T ≤ N := Subgroup.le_normalizer
    haveI hTn : (T.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr le_rfl
    refine isPSolvable_of_normal (T.subgroupOf N) ?_ ?_
    · refine isPSolvable_of_isPGroup_three ?_
      have : IsPGroup 3 T := hST ▸ S.isPGroup'
      exact this.comap_subtype
    · refine isPSolvable_of_coprime_three ?_
      rw [← Subgroup.index_eq_card]
      have hidx : (T.subgroupOf N).index = T.relIndex N := rfl
      rw [hidx]
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hdvd => ?_
      have h1 : T.relIndex N ∣ T.index := Subgroup.relIndex_dvd_index_of_le hTN
      have := S.not_dvd_index
      rw [hST] at this
      exact this (hdvd.trans h1)
  set H₀ : Subgroup ↥C := (M ⊓ C).subgroupOf C with hH₀
  have hnorm := (a6l43_point_facts hS hU0 hA1 hp hM hgen hJ).2.2
  set W : Subgroup G := ((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C with hW
  have hWC : W ≤ C := sup_le (inf_le_right.trans hJC) (glbPrimeCore_le 3 C)
  have hWsub : W.subgroupOf C = ((P : Subgroup G) ⊓ J).subgroupOf C ⊔ O' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hWC, inf_eq_left.mpr (inf_le_right.trans hJC), hO',
      ← glbPrimeCore_subgroupOf, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (glbPrimeCore_le 3 C)]
  have hWimg : (W.subgroupOf C).map φ = T := by
    rw [hWsub, Subgroup.map_sup]
    have hO'φ : O'.map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro c hc
      rw [MonoidHom.mem_ker, hφψ]
      have : ψ c = 1 := by
        rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hc
      rw [this, map_one]
    rw [hO'φ, sup_bot_eq]
    rfl
  have himage : H₀.map φ ≤ N := by
    rintro _ ⟨c, hc, rfl⟩
    have hcW : (c : G) ∈ normalizer (W : Set G) := hnorm (mem_subgroupOf.mp hc)
    have hcW' : c ∈ normalizer ((W.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
      rw [mem_normalizer_iff]
      intro w
      simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mem_normalizer_iff.mp hcW w
    have := Subgroup.le_normalizer_map φ ⟨c, hcW', rfl⟩
    rw [hWimg] at this
    exact this
  have hH₀ : CFSG.HallHigman.IsPSolvable 3 ↥H₀ :=
    isPSolvable_of_le_hom φ H₀ hker (isPSolvable_of_le hNsolv himage)
  exact isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_right) hH₀

variable [((GLBPrimeCore 3 M).subgroupOf M).Normal]

theorem isPSolvable_centralizer_bar (hS : Setting G) (hU0 : FullCoreLocal G)
    (hp : 3 ∈ rankThreeSigmaA G) (hM : IsCoreMaxLocal 3 P M) (hgen : IsGenericPoint 3 P M x)
    (hJ : IsA6Normal M x J) :
    CFSG.HallHigman.IsPSolvable 3 ↥(centralizer
      ({QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M)} :
        Set (M ⧸ (GLBPrimeCore 3 M).subgroupOf M))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup ↥M := (GLBPrimeCore 3 M).subgroupOf M with hK
  set π := QuotientGroup.mk' K with hπ
  set xm : ↥M := ⟨x, hpd.x_memM⟩ with hxm
  have hKc : Nat.Coprime 3 (Nat.card K) := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le 3 M)).toEquiv]
    exact glbPrimeCore_coprime 3 M
  have hA : IsPGroup 3 (zpowers xm) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      have : orderOf xm = orderOf x := Subgroup.orderOf_mk x hpd.x_memM
      rw [this, orderOf_eq_prime hpd.tri.x_pow hpd.tri.x_ne])
  have hle : centralizer ({π xm} : Set (M ⧸ K)) ≤ (centralizer ({xm} : Set ↥M)).map π := by
    intro y hy
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective K y
    have h1 : n ∈ (centralizer (((zpowers xm).map π : Subgroup (M ⧸ K)) :
        Set (M ⧸ K))).comap π := by
      rw [Subgroup.mem_comap, MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure]
      exact hy
    have h2 := Subgroup.mem_map_of_mem π (comap_centralizer_map_le_sup Nat.prime_three K hKc hA h1)
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' K).ge,
      bot_sup_eq, zpowers_eq_closure, centralizer_closure] at h2
  refine isPSolvable_of_le (isPSolvable_map π ?_) hle
  have hmap : (centralizer ({xm} : Set ↥M)).map M.subtype = M ⊓ centralizer ({x} : Set G) := by
    ext g
    simp only [mem_map, mem_centralizer_singleton_iff, mem_inf, Subgroup.subtype_apply]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, by simpa [xm] using congrArg Subtype.val hm⟩
    · rintro ⟨hgM, hgx⟩
      exact ⟨⟨g, hgM⟩, Subtype.ext (by simpa [xm] using hgx), rfl⟩
  have h := hpd.isPSolvable_inf_centralizer hS hU0 hp hM hgen hJ
  rw [← hmap] at h
  exact isPSolvable_of_mulEquiv
    ((centralizer ({xm} : Set ↥M)).equivMapOfInjective M.subtype M.subtype_injective).symm h

end PointData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
