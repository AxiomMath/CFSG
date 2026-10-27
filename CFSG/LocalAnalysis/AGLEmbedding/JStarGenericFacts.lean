module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericDefs
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalElementary
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem JStarTargetBase.isPerfect {p B : ℕ} {L : Type} [Group L] [Finite L]
    (hT : JStarTargetBase p B L) : Group.IsPerfect L := by
  have := hT.simple
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hT.nonabelian
    have h1 : (⊤ : Subgroup L) ≤ Subgroup.centralizer ((⊤ : Subgroup L) : Set L) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact hbot)
    exact hab (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top b)) a trivial)
  · exact htop

theorem exists_elem_le_sylow_of_le_pRank {p k : ℕ} {L : Type} [Group L] [Finite L]
    [Fact p.Prime] (hk : k ≤ Open.pRank p (⊤ : Subgroup L)) (S : Sylow p L) :
    ∃ E : Subgroup L, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  have hp : p.Prime := Fact.out
  have hS := (CFSG.SectionRank.pRank_sylow S).1
  obtain ⟨E₀, hE₀S, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (S : Subgroup L)
  have hk : k ≤ Open.pRank p (S : Subgroup L) := hS ▸ hk
  have hE₀p : IsPGroup p E₀ := IsPGroup.of_card hcard
  obtain ⟨E₁, hE₁⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hE₀p
    (show p ^ k ≤ Nat.card E₀ by rw [hcard]; exact Nat.pow_le_pow_right hp.pos hk)
  exact ⟨E₁.map E₀.subtype, (Subgroup.map_subtype_le _).trans hE₀S,
    CFSG.LargeEvenClassification.Helpers.elementary_subgroup_of_le _ _ hE₀
      (Subgroup.map_subtype_le _), by rw [Subgroup.card_map_of_injective E₀.subtype_injective, hE₁]⟩

theorem JStarTarget.exists_elem_le_sylow {p B : ℕ} {L : Type} [Group L] [Finite L]
    [Fact p.Prime] (hT : JStarTarget p B L) (S : Sylow p L) :
    ∃ E : Subgroup L, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 :=
  exists_elem_le_sylow_of_le_pRank hT.three_le_pRank S

theorem JStarTargetBase.exists_elem_le_sylow {p B : ℕ} {L : Type} [Group L] [Finite L]
    [Fact p.Prime] (hT : JStarTargetBase p B L) (S : Sylow p L) :
    ∃ E : Subgroup L, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 :=
  exists_elem_le_sylow_of_le_pRank hT.two_le_pRank S

namespace JStarHypOf

variable {Y : Type} [Group Y] [Finite Y] {T : Type} [Group T] [Finite T] {p B : ℕ}
  [Fact p.Prime] {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* T}

theorem eq_of_inf_le (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) {K : Subgroup Y} (hKJ : K ≤ Jt)
    (hJK : Jt ≤ Subgroup.normalizer (K : Set Y)) (hXK : Xt ⊓ Jt ≤ K) : K = Jt := by
  refine le_antisymm hKJ ?_
  have h1 : nclIn Jt (Xt ⊓ Jt) = nclIn Jt Xt := by
    simp only [nclIn, Subgroup.inf_subgroupOf_right]
  rw [← h.ncl, ← h1]
  exact nclIn_le hXK hKJ hJK

theorem eq_top_of_coprime_card_quotient (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (V : Subgroup Jt)
    [V.Normal] (hV : p.Coprime (Nat.card (Jt ⧸ V))) : V = ⊤ := by
  have hX : ∀ x : Jt, (x : Y) ∈ Xt → x ∈ V := by
    intro x hxX
    obtain ⟨k, hk⟩ := Rb.isPGroup' ⟨x, h.le_R hxX⟩
    have hxk : x ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : orderOf (x : Jt ⧸ V) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, hxk, QuotientGroup.mk_one])
    have h3 : orderOf (x : Jt ⧸ V) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hV.pow_left k) h1 (orderOf_dvd_natCard _)
    rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  have hVJ : V.map Jt.subtype ≤ Jt := Subgroup.map_subtype_le V
  have hJV : Jt ≤ Subgroup.normalizer ((V.map Jt.subtype : Subgroup Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVJ).mp (by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Jt.subtype_injective]
      infer_instance)
  have hXV : Xt ⊓ Jt ≤ V.map Jt.subtype := fun x hx => ⟨⟨x, hx.2⟩, hX ⟨x, hx.2⟩ hx.1, rfl⟩
  have heq := h.eq_of_inf_le hVJ hJV hXV
  rw [eq_top_iff]
  intro x _
  have hx : (x : Y) ∈ V.map Jt.subtype := by rw [heq]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [Subtype.ext hyx] at hy

theorem eq_top_of_map_eq_top (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (V : Subgroup Jt) [V.Normal]
    (hV : V.map φ = ⊤) : V = ⊤ := by
  refine h.eq_top_of_coprime_card_quotient V (Nat.Coprime.coprime_dvd_right ?_ h.coprime)
  refine Subgroup.card_dvd_of_surjective (f := (QuotientGroup.mk' V).comp φ.ker.subtype) ?_
  intro q
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨v, hv, hvj⟩ : φ j ∈ V.map φ := hV ▸ Subgroup.mem_top _
  refine ⟨⟨v⁻¹ * j, by rw [MonoidHom.mem_ker, map_mul, map_inv, hvj, inv_mul_cancel]⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff v).mpr hv, inv_one,
    one_mul]

theorem eq_top_or_le_ker (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T)
    (V : Subgroup Jt) [hV : V.Normal] : V = ⊤ ∨ V ≤ φ.ker := by
  have : IsSimpleGroup T := hT.simple
  have := hV.map φ h.surj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.map φ) with hbot | htop
  · exact Or.inr ((Subgroup.map_eq_bot_iff _).mp hbot)
  · exact Or.inl (h.eq_top_of_map_eq_top V htop)

theorem eq_or_le_ker (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T)
    {V : Subgroup Y} (hVJ : V ≤ Jt) (hJV : Jt ≤ Subgroup.normalizer (V : Set Y)) :
    V = Jt ∨ V ≤ φ.ker.map Jt.subtype := by
  have : (V.subgroupOf Jt).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVJ).mpr hJV
  rcases h.eq_top_or_le_ker hT (V.subgroupOf Jt) with htop | hle
  · exact Or.inl (le_antisymm hVJ (Subgroup.subgroupOf_eq_top.mp htop))
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hVJ]
    exact Subgroup.map_mono hle

theorem commutator_eq_top (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T) :
    commutator Jt = ⊤ := by
  refine h.eq_top_of_map_eq_top _ ?_
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ h.surj,
    ← commutator_def]
  exact hT.isPerfect.commutator_eq_top

theorem isPerfect (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T) :
    Group.IsPerfect Jt :=
  ⟨h.commutator_eq_top hT⟩

theorem commutator_eq (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T) :
    ⁅Jt, Jt⁆ = Jt :=
  Subgroup.isPerfect_iff.mp (h.isPerfect hT)

theorem nontrivial (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T) :
    Nontrivial Jt := by
  have : IsSimpleGroup T := hT.simple
  exact h.surj.nontrivial

theorem not_isPGroup (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T) :
    ¬ IsPGroup p Jt := fun hJ => by
  have := h.nontrivial hT
  have := h.isPerfect hT
  exact Group.IsPerfect.not_isNilpotent Jt hJ.isNilpotent

theorem inf_ker_eq_bot (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) {S : Subgroup Y}
    (hS : IsPGroup p S) : S ⊓ φ.ker.map Jt.subtype = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk, Subgroup.card_map_of_injective Jt.subtype_injective]
  exact h.coprime.pow_left k

theorem eq_bot_of_isPGroup (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTargetBase p B T)
    {V : Subgroup Y} (hVJ : V ≤ Jt) (hJV : Jt ≤ Subgroup.normalizer (V : Set Y))
    (hV : IsPGroup p V) : V = ⊥ := by
  rcases h.eq_or_le_ker hT hVJ hJV with rfl | hle
  · exact absurd hV (h.not_isPGroup hT)
  · rw [← inf_eq_left.mpr hle]
    exact h.inf_ker_eq_bot hV

theorem exists_elem_le_sylow_of_le_pRank (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) {k : ℕ}
    (hk : k ≤ Open.pRank p (⊤ : Subgroup T)) (S : Sylow p Jt) :
    ∃ E : Subgroup Jt, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  have hdisj : (S : Subgroup Jt) ⊓ φ.ker = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    exact (Subgroup.disjoint_of_coprime_natCard (hk ▸ h.coprime.pow_left k)).eq_bot
  set ψ : (S : Subgroup Jt) →* T := φ.comp (S : Subgroup Jt).subtype
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hs' : (s : Jt) ∈ (S : Subgroup Jt) ⊓ φ.ker := ⟨s.2, hs⟩
    rw [hdisj, Subgroup.mem_bot] at hs'
    exact Subgroup.mem_bot.mpr (Subtype.ext hs')
  obtain ⟨E, hES, hE, hEcard⟩ :=
    CFSG.AGLEmbedding.exists_elem_le_sylow_of_le_pRank hk (S.mapSurjective h.surj)
  rw [Sylow.coe_mapSurjective] at hES
  have hrange : ψ.range = (S : Subgroup Jt).map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEψ : E ≤ ψ.range := hrange ▸ hES
  refine ⟨((E.comap ψ).map (S : Subgroup Jt).subtype), Subgroup.map_subtype_le _,
    elementary_abelian_map p (isElemAbelian_comap_of_injective hinj hE) _, ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ← hEcard,
    ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hEψ]

theorem exists_elem_le_sylow (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) (hT : JStarTarget p B T)
    (S : Sylow p Jt) : ∃ E : Subgroup Jt, E ≤ S ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 :=
  h.exists_elem_le_sylow_of_le_pRank hT.three_le_pRank S

theorem le_normalizer_component (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : Jt ≤ Subgroup.normalizer (L : Set Y) := by
  set N := (Subgroup.normalizer (L : Set Y)).normalCore
  have hK : Jt ⊓ N = Jt := h.eq_of_inf_le inf_le_left
    ((le_inf Subgroup.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    (fun x hx => ⟨hx.2, h.red.sylow_le_normalCore_normalizer_component hL (h.le_R hx.1)⟩)
  calc Jt = Jt ⊓ N := hK.symm
    _ ≤ N := inf_le_right
    _ ≤ _ := Subgroup.normalCore_le _

theorem le_normalizer_inf_centralizer (h : JStarHypOf p Rb Y₀ Jt Xt T B φ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    Jt ≤ Subgroup.normalizer ((Jt ⊓ Subgroup.centralizer (L : Set Y) : Subgroup Y) : Set Y) :=
  (le_inf Subgroup.le_normalizer ((h.le_normalizer_component hL).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance))).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_centralizer_or_inf_le_ker (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    Jt ≤ Subgroup.centralizer (L : Set Y) ∨
      Jt ⊓ Subgroup.centralizer (L : Set Y) ≤ φ.ker.map Jt.subtype := by
  rcases h.eq_or_le_ker hT inf_le_left (h.le_normalizer_inf_centralizer hL) with heq | hle
  · exact Or.inl (inf_eq_left.mp heq)
  · exact Or.inr hle

end JStarHypOf

end CFSG.AGLEmbedding
