module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.GroupTheory.SurjectiveRangeFactor
import CFSG.LocalAnalysis.AGLEmbedding.ReducedNotConstrained
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BKernel
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowU43
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Cat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

private theorem eq_bot_of_not_isPGroup {p : ℕ} {T : Type*} [Group T] [IsSimpleGroup T]
    (hT : ¬ IsPGroup p T) (M : Subgroup T) (hMn : M.Normal) (hM : IsPGroup p M) : M = ⊥ := by
  haveI := hMn
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal M).resolve_right fun hMt =>
    hT ((hM.of_equiv (MulEquiv.subgroupCongr hMt)).of_equiv Subgroup.topEquiv)

private theorem not_isPGroup_of_card_ne {p : ℕ} (hp : p.Prime) {T : Type*} [Group T] [Finite T]
    [IsSimpleGroup T] (hT : Nat.card T ≠ p) : ¬ IsPGroup p T := fun h => by
  have : Fact p.Prime := ⟨hp⟩
  exact hT (h.isSimpleGroup_iff_card_eq.1 inferInstance)

private theorem eq_bot_prod {p : ℕ} {T : Type*} [Group T] [IsSimpleGroup T]
    (hT : ¬ IsPGroup p T) (M : Subgroup (T × T)) (hMn : M.Normal) (hM : IsPGroup p M) :
    M = ⊥ := by
  have h1 := eq_bot_of_not_isPGroup hT _ (hMn.map (MonoidHom.fst T T) fun t => ⟨(t, 1), rfl⟩)
    (hM.map (MonoidHom.fst T T))
  have h2 := eq_bot_of_not_isPGroup hT _ (hMn.map (MonoidHom.snd T T) fun t => ⟨(1, t), rfl⟩)
    (hM.map (MonoidHom.snd T T))
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => Prod.ext ?_ ?_
  · exact (Subgroup.eq_bot_iff_forall _).1 h1 _ ⟨x, hx, rfl⟩
  · exact (Subgroup.eq_bot_iff_forall _).1 h2 _ ⟨x, hx, rfl⟩

variable {G : Type} [Group G] [Finite G]

private theorem exists_surj_img {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} {J H : Subgroup G}
    (ha : orderOf a = p) (hJ : GLAPComponent p (cx a) J)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p)
    (hH : H ≤ cx a) {T : Type*} [Group T] (τ : PQuot p H →* T) (hτ : Function.Surjective τ)
    (hT : ∀ M : Subgroup T, M.Normal → IsPGroup p M → M = ⊥) :
    ∃ f : ↥((H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J)) →* T,
      Function.Surjective f := by
  have hHN : H ≤ Subgroup.normalizer (J : Set G) :=
    hH.trans (cx_le_normalizer_of_rankOne hp hp2 ha hJ hrk1)
  set π : ↥H →* PQuot p H := QuotientGroup.mk' (GLAPPrimeCore p ↥H) with hπ
  set C : Subgroup ↥H := (centModSubgroup p J).subgroupOf H with hC
  have hCn : C.Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by
    simpa using L62.conj_mem_centModSubgroup (hHN g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
  have hCp : IsPGroup p (C.map π) := by
    rintro ⟨_, d, hd, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_core_of_centMod hp hp2 ha hJ hrk1 (hH d.2)
      (centMod_iff.2 (Subgroup.mem_subgroupOf.1 hd))
    have hkH : (d : G) ^ (p ^ k) ∈ GLAPPrimeCoreOf p H := by
      have h1 := HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp (cx a) H
        ⟨hk, H.pow_mem d.2 _⟩
      rwa [inf_eq_right.2 hH] at h1
    obtain ⟨x, hx, hxe⟩ := hkH
    have hxd : x = d ^ (p ^ k) := Subtype.ext (by simpa using hxe)
    refine ⟨k, Subtype.ext ?_⟩
    show π d ^ (p ^ k) = 1
    rw [← map_pow, ← hxd]
    exact (QuotientGroup.eq_one_iff _).2 hx
  have hbot := hT ((C.map π).map τ) ((hCn.map π (QuotientGroup.mk'_surjective _)).map τ hτ)
    (hCp.map τ)
  set ψ := (L62.phiC p J).comp (Subgroup.inclusion hHN) with hψ
  have hrange : ψ.range = (H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  rw [← hrange]
  refine CFSG.exists_surjective_range_of_ker_le ψ (τ.comp π)
    (hτ.comp (QuotientGroup.mk'_surjective _)) fun h hh => ?_
  have hg : (h : G) ∈ centModSubgroup p J :=
    centMod_iff.1 ((L62.phiC_eq_one_iff hp hJ (hHN h.2)).1 (MonoidHom.mem_ker.1 hh))
  have hmem : τ (π h) ∈ (C.map π).map τ :=
    Subgroup.mem_map_of_mem τ (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hg))
  rw [hbot] at hmem
  exact MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 hmem)

private theorem mapsOntoType_of_simple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G}
    {J H : Subgroup G} (ha : orderOf a = p) (hJ : GLAPComponent p (cx a) J)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p)
    (hH : H ≤ cx a) (hs : IsSimpleGroup (PSimple p H)) (hne : ¬ IsPGroup p (PSimple p H))
    {Q : TauCeti.CFSGIndex → Prop} (hcat : catalogIs (PSimple p H) Q) :
    MapsOntoType ((H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J)) Q := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  obtain ⟨f, hf⟩ := exists_surj_img hp hp2 ha hJ hrk1 hH
    (QuotientGroup.mk' (Subgroup.center (PQuot p H))) (QuotientGroup.mk'_surjective _)
    (eq_bot_of_not_isPGroup hne)
  exact ⟨i, hi, e.toMonoidHom.comp f, e.surjective.comp hf⟩

theorem mapsOntoType_phiC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} {J Y I : Subgroup G}
    (ha : orderOf a = p) (hJ : GLAPComponent p (cx a) J)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p)
    (hI : GLAPComponent p Y I) (hIX : I ≤ cx a) {Q : TauCeti.CFSGIndex → Prop}
    (hIcat : catalogIs (PSimple p I) Q) :
    MapsOntoType ((I.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J)) Q := by
  have : Fact p.Prime := ⟨hp⟩
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hI
  haveI : IsSimpleGroup (PSimple p I) := hq.2
  exact mapsOntoType_of_simple hp hp2 ha hJ hrk1 hIX hq.2
    (AGLEmbedding.not_isPGroup_of_isSimpleGroup
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq)) hIcat

theorem rowKS_phiC {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} {J K : Subgroup G} {row : Row}
    (ha : orderOf a = p) (hJ : GLAPComponent p (cx a) J)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p)
    (hprow : p = row.prime) (hKX : K ≤ cx a) (hK : RowK row p K) :
    RowKS row ((K.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J)) := by
  subst hprow
  cases row with
  | ly | fi24 | fi24h | suz | suzh | th =>
    show _ = ⊥
    rw [show K = ⊥ from hK, Subgroup.bot_subgroupOf, Subgroup.map_bot]
  | co1 => trivial
  | co2 =>
    obtain ⟨hs, hc⟩ := CatB.I1431YU5.isA6_isSimpleGroup hK.1
    exact mapsOntoType_of_simple hp hp2 ha hJ hrk1 hKX hs
      (not_isPGroup_of_card_ne hp (by rw [hc]; decide)) hK.1
  | m3 =>
    obtain ⟨e₀⟩ := H1420.nonempty_equiv_X₀_of_isU4of_three hK.1
    haveI : IsSimpleGroup CFSG.LieType.Multipliers.U43.X₀ :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
        CFSG.LieType.Multipliers.U43.F9 3 1
        (by rw [Nat.card_eq_fintype_card, CFSG.LieType.Multipliers.U43.F9.card_eq]; norm_num) 4
        (by norm_num) (by decide)
    haveI : IsSimpleGroup (PSimple Row.m3.prime K) := e₀.isSimpleGroup
    exact mapsOntoType_of_simple hp hp2 ha hJ hrk1 hKX inferInstance
      (not_isPGroup_of_card_ne hp (by rw [H1420.card_eq_of_isU4of_three hK.1]; decide)) hK.1
  | m5 =>
    obtain ⟨e⟩ := hK
    have h60 : Nat.card (alternatingGroup (Fin 5)) ≠ Row.m5.prime := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact exists_surj_img hp hp2 ha hJ hrk1 hKX e.toMonoidHom e.surjective
      (eq_bot_prod (not_isPGroup_of_card_ne hp h60))

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
