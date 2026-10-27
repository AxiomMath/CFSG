module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4S
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4Group
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftCtx
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FF
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.E81
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5PairDerive
public import CFSG.LocalAnalysis.SignalizerFunctor

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Open
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

@[expose] def radJ {K : Type*} [Group K] (D : UniversalRootDatum K) (J : Set (Fin D.rank)) :
    Subgroup K := ⨆ k ∈ {k | k ∉ J}, radical D k

section K

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem radJ_le_posUnipotent (J : Set (Fin D.rank)) : radJ D J ≤ posUnipotent D :=
  iSup₂_le fun k _ => radical_le_posUnipotent k

theorem rootGroup_single_le_radJ {J : Set (Fin D.rank)} {k : Fin D.rank} (hk : k ∉ J) :
    D.rootGroup (Pi.single k 1) ≤ radJ D J := by
  have hα : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
  exact (rootGroup_le_radical hα (by simp)).trans
    (le_iSup₂ (f := fun k (_ : k ∈ {k | k ∉ J}) => radical D k) k hk)

theorem parJ_le_normalizer_radJ (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (J : Set (Fin D.rank)) : parJ D H J ≤ Subgroup.normalizer (radJ D J : Set K) :=
  le_normalizer_iSup fun k => le_normalizer_iSup fun hk => parJ_le_normalizer_radical hct hext hk

end K

section W

set_option hygiene false in
set_option quotPrecheck false in
local notation "qq" => QuotientGroup.mk' (Subgroup.center ↥L)

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {K : Type} [Group K] [Finite K]
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
  {π : K →* ↥L ⧸ Subgroup.center ↥L}

@[expose] def liftSub (L : Subgroup Y) (π : K →* ↥L ⧸ Subgroup.center ↥L) (A : Subgroup K) :
    Subgroup Y :=
  ((A.map π).comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype

theorem liftSub_mono {A B : Subgroup K} (h : A ≤ B) : liftSub L π A ≤ liftSub L π B :=
  Subgroup.map_mono (Subgroup.comap_mono (Subgroup.map_mono h))

theorem liftSub_le (A : Subgroup K) : liftSub L π A ≤ L := Subgroup.map_subtype_le _

theorem mem_liftSub {A : Subgroup K} {x : Y} :
    x ∈ liftSub L π A ↔ ∃ a : ↥L, (a : Y) = x ∧ (qq) a ∈ A.map π := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩

theorem pElementSubgroup_mono' {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    pElementSubgroup 2 A ≤ pElementSubgroup 2 B :=
  Subgroup.closure_mono fun x hx => ⟨h hx.1, hx.2⟩

theorem odd_centralizes_of_hVD {Q : Subgroup Y} (hQL : Q ≤ L)
    {Nb : Subgroup (↥L ⧸ Subgroup.center ↥L)} (hNb2 : IsPGroup 2 ↥Nb)
    (hnorm : ∀ w₀ : ↥L, (w₀ : Y) ∈ pElementSubgroup 2 Q →
      (QuotientGroup.mk' (Subgroup.center ↥L)) w₀ ∈ Subgroup.normalizer (Nb : Set _))
    (hlift : ∀ c ∈ Nb, ∃ u : ↥L, (QuotientGroup.mk' (Subgroup.center ↥L)) u = c ∧
      (u : Y) ∈ pElementSubgroup 2 Q ∧ ∃ s : ℕ, orderOf u = 2 ^ s)
    (hVD : ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 Q)),
      twoResidual (pElementSubgroup 2 Q)⁆ = ⊥) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ yb ∈ ((pElementSubgroup 2 Q).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
        (∃ a : ℕ, orderOf yb = p ^ a) → ∀ cb ∈ Nb, yb * cb * yb⁻¹ = cb := by
  classical
  intro p hp hp2 yb hyb ⟨a, ha⟩ cb hcb
  set W : Subgroup Y := pElementSubgroup 2 Q with hW
  obtain ⟨w₀, hw₀, rfl⟩ := hyb
  have hw₀W : (w₀ : Y) ∈ W := Subgroup.mem_subgroupOf.1 hw₀
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, ⟨a', ha'⟩, hfe⟩ := CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.exists_pElement_lift
    (QuotientGroup.mk' (Subgroup.center ↥L)) (p := p) (x := w₀) ⟨a, ha⟩
  have hw₁W : ((w₀ ^ e : ↥L) : Y) ∈ W := by
    have : ((w₀ ^ e : ↥L) : Y) = (w₀ : Y) ^ e := by simp
    rw [this]; exact W.pow_mem hw₀W e
  have hodd1 : Odd (orderOf ((w₀ ^ e : ↥L) : Y)) := by
    rw [Subgroup.orderOf_coe, ha']
    exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨u, hu1, huW, s, hs⟩ := hlift cb hcb
  haveI : Group.IsNilpotent ↥Nb := hNb2.isNilpotent
  have hNilL : Group.IsNilpotent ↥(Nb.comap (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    refine Subgroup.isNilpotent_of_ker_le_center
      (((QuotientGroup.mk' (Subgroup.center ↥L)).comp
        (Nb.comap (QuotientGroup.mk' (Subgroup.center ↥L))).subtype).codRestrict Nb
        (fun x => x.2)) ?_
    intro x hx
    have hx1 : (QuotientGroup.mk' (Subgroup.center ↥L)) (x : ↥L) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact this
    have hxc : (x : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 hx1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc (g : ↥L))
  set Ñ : Subgroup Y := (Nb.comap (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype
    with hÑ
  have hNil : Group.IsNilpotent ↥Ñ :=
    Group.nilpotent_of_surjective
      (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).toMonoidHom
      (MulEquiv.surjective _)
  have hWQ : W ≤ Q := pElementSubgroup_le Q
  have hWÑ : W ≤ Subgroup.normalizer (Ñ : Set Y) := by
    refine le_normalizer_of_conj_mem W Ñ ?_
    intro g hg r hr
    obtain ⟨x, hx, rfl⟩ := hr
    have hgL : g ∈ L := hQL (hWQ hg)
    refine ⟨(⟨g, hgL⟩ : ↥L) * x * (⟨g, hgL⟩ : ↥L)⁻¹, ?_, rfl⟩
    have hn := Subgroup.mem_normalizer_iff.1 (hnorm ⟨g, hgL⟩ hg)
      ((QuotientGroup.mk' (Subgroup.center ↥L)) x)
    show (QuotientGroup.mk' (Subgroup.center ↥L)) ((⟨g, hgL⟩ : ↥L) * x * (⟨g, hgL⟩ : ↥L)⁻¹) ∈ Nb
    rw [map_mul, map_mul, map_inv]
    exact hn.1 hx
  have huÑ : (u : Y) ∈ Ñ := ⟨u, by
    show (QuotientGroup.mk' (Subgroup.center ↥L)) u ∈ Nb
    rw [hu1]; exact hcb, rfl⟩
  obtain ⟨𝒮, h𝒮Ñ, h𝒮, hW𝒮, h𝒮u⟩ := exists_normalized_sylow_two hNil hWÑ
  have hu𝒮 : (u : Y) ∈ 𝒮 := h𝒮u _ huÑ ⟨s, by rw [Subgroup.orderOf_coe]; exact hs⟩
  have key := odd_action_trivial (W := W) (D := twoResidual W) (twoResidual_le W)
    (le_normalizer_twoResidual W) (fun x hx ho => mem_twoResidual_of_odd hx ho) h𝒮 hW𝒮 hVD
    hw₁W hodd1 hu𝒮 huW
  have hkey : (w₀ ^ e : ↥L) * u * (w₀ ^ e : ↥L)⁻¹ = u := Subtype.ext key
  have h3 := congrArg (QuotientGroup.mk' (Subgroup.center ↥L)) hkey
  rw [map_mul, map_mul, map_inv, hfe, hu1] at h3
  exact h3

theorem clause_four_core (hπ : BorelQuotient D n H π M)
    (hSimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L))
    (hZ : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥)
    {J : Set (Fin D.rank)} (hJne : J.Nonempty) (hJc : ∃ k, k ∉ J)
    {Q : Subgroup Y} (hQ : Q = ⨆ j ∈ J, liftSub L π (parJ D H {j})) :
    ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 Q)),
      twoResidual (pElementSubgroup 2 Q)⁆ ≠ ⊥ := by
  classical
  intro hVD
  obtain ⟨j, hj, k, hk, hcart⟩ := exists_adj_of_proper hπ hSimple hZ hJne hJc
  have hjk : j ≠ k := fun e => hk (e ▸ hj)
  set W : Subgroup Y := pElementSubgroup 2 Q with hW
  have hPjQ : ∀ j' ∈ J, liftSub L π (parJ D H {j'}) ≤ Q := fun j' hj' => by
    rw [hQ]
    exact le_iSup₂_of_le (f := fun j (_ : j ∈ J) => liftSub L π (parJ D H {j})) j' hj' le_rfl
  have hQJ : Q ≤ liftSub L π (parJ D H J) := by
    rw [hQ]
    refine iSup₂_le fun j' hj' => liftSub_mono ?_
    exact sup_le (borel_le_parJ J) (iSup₂_le fun i hi => by
      rw [Set.mem_singleton_iff.1 hi]; exact rankOne_le_parJ hj')
  have hQL : Q ≤ L := hQJ.trans (liftSub_le _)
  have hWQ : W ≤ Q := pElementSubgroup_le Q
  have hWq : ∀ w₀ : ↥L, (w₀ : Y) ∈ W → (QuotientGroup.mk' (Subgroup.center ↥L)) w₀ ∈
      (parJ D H J).map π := by
    intro w₀ hw₀
    obtain ⟨a, ha, haq⟩ := (mem_liftSub (π := π)).1 (hQJ (hWQ hw₀))
    have : a = w₀ := Subtype.ext ha
    exact this ▸ haq
  have hWnorm : ∀ w₀ : ↥L, (w₀ : Y) ∈ W → (QuotientGroup.mk' (Subgroup.center ↥L)) w₀ ∈
      Subgroup.normalizer (((radJ D J).map π : Subgroup _) : Set _) := fun w₀ hw₀ =>
    ((Subgroup.map_mono (parJ_le_normalizer_radJ hπ.ct hπ.extras J)).trans
      (Subgroup.le_normalizer_map π)) (hWq w₀ hw₀)
  set Wb : Subgroup (↥L ⧸ Subgroup.center ↥L) :=
    (W.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) with hWb
  set Nb : Subgroup (↥L ⧸ Subgroup.center ↥L) := (radJ D J).map π with hNb
  refine false_of_odd_centralizes hπ hjk hcart (Wb := Wb) (Nb := Nb) ?_ ?_
    (Subgroup.map_mono (rootGroup_single_le_radJ hk)) ?_
  ·
    rintro _ ⟨w₀, hw₀, rfl⟩
    exact hWnorm w₀ hw₀
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hg1 : g ∈ pElementSubgroup 2 (parJ D H {j}) :=
      rankOne_le_pElementSubgroup hπ (rankOne_le_parJ (J := {j}) (H := H) rfl) hg
    have hg2 : π g ∈ pElementSubgroup 2 ((parJ D H {j}).map π) :=
      map_pElementSubgroup_le_pElementSubgroup_map π _ ⟨g, hg1, rfl⟩
    obtain ⟨a, ha, haq⟩ := pElementSubgroup_le_map_pElementSubgroup_comap (L := L) _ hg2
    have h3 : (a : Y) ∈ pElementSubgroup 2 (liftSub L π (parJ D H {j})) :=
      map_pElementSubgroup_le _ ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.2 (pElementSubgroup_mono' (hPjQ j hj) h3), haq⟩
  ·
    have hlift : ∀ c ∈ Nb, ∃ u : ↥L, (QuotientGroup.mk' (Subgroup.center ↥L)) u = c ∧
        (u : Y) ∈ pElementSubgroup 2 Q ∧ ∃ s : ℕ, orderOf u = 2 ^ s := by
      intro cb hcb
      obtain ⟨c, hc, rfl⟩ := hcb
      obtain ⟨j₁, hj₁⟩ := hJne
      have hcU : c ∈ posUnipotent D := radJ_le_posUnipotent J hc
      have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos hπ.extras hπ.pGroup
      have hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1 := by
        obtain ⟨k, hk⟩ := hU2 ⟨c, hcU⟩
        exact ⟨k, congrArg Subtype.val hk⟩
      have hcP : c ∈ parJ D H {j₁} := posUnipotent_le_borel.trans (borel_le_parJ _) hcU
      obtain ⟨u, hu1, hu2, s, hs⟩ := exists_two_lift (π := π) (parJ D H {j₁}) hc2 hcP
      refine ⟨u, hu1, ?_, s, hs⟩
      have h1 : (u : Y) ∈ liftSub L π (parJ D H {j₁}) := ⟨u, hu2, rfl⟩
      have h2 : (u : Y) ∈ pElementSubgroup 2 (liftSub L π (parJ D H {j₁})) :=
        Subgroup.subset_closure ⟨h1, s, by rw [Subgroup.orderOf_coe]; exact hs⟩
      exact pElementSubgroup_mono' (hPjQ j₁ hj₁) h2
    have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos hπ.extras hπ.pGroup
    have hNb2 : IsPGroup 2 ↥Nb := (hU2.to_le (radJ_le_posUnipotent J)).map π
    exact odd_centralizes_of_hVD hQL hNb2 hWnorm hlift hVD

theorem center_quotient_eq_bot {G : Type*} [Group G] (hG : Open.IsQuasisimple G) :
    Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
  haveI := hG.2
  haveI : (Subgroup.center (G ⧸ Subgroup.center G)).Normal := inferInstance
  rcases hG.2.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.center G)) with h | h
  · exact h
  · exfalso
    have hker : commutator G ≤ (QuotientGroup.mk' (Subgroup.center G)).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hc : QuotientGroup.mk' (Subgroup.center G) y ∈ Subgroup.center (G ⧸ Subgroup.center G) := by
        rw [h]; exact Subgroup.mem_top _
      rw [commutatorElement_def, mul_inv_eq_one]
      exact mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_center_iff.1 hc _)
    have htop : (QuotientGroup.mk' (Subgroup.center G)).ker = ⊤ := by
      rw [eq_top_iff, ← hG.1]; exact hker
    haveI := hG.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (G ⧸ Subgroup.center G)
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : (QuotientGroup.mk' (Subgroup.center G)) a₀ = 1 :=
      MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top _)
    have hb : (QuotientGroup.mk' (Subgroup.center G)) b₀ = 1 :=
      MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top _)
    exact hab (ha.trans hb.symm)

theorem iSup_liftSub_eq (hπ : BorelQuotient D n H π M) [Nonempty (Fin D.rank)] :
    (⨆ j, liftSub L π (parJ D H {j})) = L := by
  have hK : (⊤ : Subgroup K) ≤ ⨆ i, parJ D H {i} := by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin D.rank))
    rw [eq_parJ_negIndices hπ.ct hπ.extras (A := ⊤) le_top]
    refine sup_le ((borel_le_parJ ({i₀} : Set (Fin D.rank))).trans
      (le_iSup (fun i => parJ D H {i}) i₀)) (iSup₂_le fun i _ => ?_)
    exact (rankOne_le_parJ (J := {i}) rfl).trans (le_iSup (fun i => parJ D H {i}) i)
  have hS : (⨆ i, (parJ D H {i}).map π) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective π hπ.surj, ← Subgroup.map_iSup]
    exact Subgroup.map_mono hK
  have hq : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hC : (⨆ i, ((parJ D H {i}).map π).comap (QuotientGroup.mk' (Subgroup.center ↥L))) = ⊤ := by
    set C := ⨆ i, ((parJ D H {i}).map π).comap (QuotientGroup.mk' (Subgroup.center ↥L)) with hCdef
    obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin D.rank))
    have hZC : Subgroup.center ↥L ≤ C := by
      refine le_trans ?_ (le_iSup _ i₀)
      intro z hz
      rw [Subgroup.mem_comap]
      have : (QuotientGroup.mk' (Subgroup.center ↥L)) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
      rw [this]; exact one_mem _
    have hmapC : C.map (QuotientGroup.mk' (Subgroup.center ↥L)) = ⊤ := by
      rw [hCdef, Subgroup.map_iSup]
      simp only [Subgroup.map_comap_eq_self_of_surjective hq]
      exact hS
    have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center ↥L)) C
    rw [hmapC, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hZC] at this
    exact this.symm
  unfold liftSub
  rw [← Subgroup.map_iSup, hC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem clause_four_of_borelQuotient {R P : Subgroup Y} (hL : Open.IsQuasisimple ↥L)
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hS : IsSylowTwoOf (R ⊓ L) L)
    (hP : IsMinOverBorel L (R ⊓ L) P) (hπ : BorelQuotient D n H π M) :
    conjClosure P R ≠ L →
      ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
        twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥ := by
  intro hQL
  obtain ⟨π', hπ', hT⟩ := exists_borelQuotient_conj hS hπ
  let D0 := minParData_of_borelQuotient' hπ' hT.symm
  let DW := minParData_of_center D0 hS
  have hex : ∃ J : Set (Fin D.rank), J.Nonempty ∧
      conjClosure P R = ⨆ j ∈ J, liftSub L π' (parJ D H {j}) :=
    exists_iSup_conjClosure hR hP DW
  obtain ⟨J, hJne, hQ'⟩ := hex
  have hJc : ∃ k, k ∉ J := by
    by_contra hall
    push Not at hall
    apply hQL
    haveI : Nonempty (Fin D.rank) := ⟨hJne.some⟩
    have hall' : (⨆ j ∈ J, liftSub L π' (parJ D H {j})) = ⨆ j, liftSub L π' (parJ D H {j}) :=
      le_antisymm (iSup₂_le fun j _ => le_iSup (fun j => liftSub L π' (parJ D H {j})) j)
        (iSup_le fun j => le_iSup₂_of_le (f := fun j (_ : j ∈ J) =>
          liftSub L π' (parJ D H {j})) j (hall j) le_rfl)
    rw [hQ', hall']
    exact iSup_liftSub_eq hπ'
  exact clause_four_core hπ' hL.2 (center_quotient_eq_bot hL) hJne hJc hQ'

theorem kFact_of_hasBQ {R P : Subgroup Y} (hL : Open.IsQuasisimple ↥L)
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (h : HasBQ (↥L ⧸ Subgroup.center ↥L)) :
    (∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
      (conjClosure P R ≠ L →
        ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
          twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥) := by
  refine ⟨minParabolic_of_hasBQ hR hR2 hS hP h, ?_⟩
  obtain ⟨K, _, _, D, n, H, π, M, hπ⟩ := h
  exact clause_four_of_borelQuotient hL hR hS hP hπ

end W

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
