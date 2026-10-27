module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

structure JStarHyp {Y : Type} [Group Y] [Finite Y] (p n : ℕ) [Fact p.Prime] (Rb : Sylow p Y)
    (Y₀ : Subgroup Y) (Jt Xt : Subgroup Y) (φ : Jt →* PSL2GF p n) : Prop where
  ne_two : p ≠ 2
  three_le : 3 ≤ n
  red : ReducedNongeneration p Y Rb Y₀
  catalog : CatalogSimpleSections Y
  surj : Function.Surjective φ
  coprime : p.Coprime (Nat.card φ.ker)
  le_R : Xt ≤ (Rb : Subgroup Y)
  ncl : nclIn Jt Xt = Jt
  le_normalizer : (Rb : Subgroup Y) ≤ Subgroup.normalizer (Jt : Set Y)
  faithful : ∀ z ∈ (Rb : Subgroup Y),
    (∀ j ∈ Jt, z * j * z⁻¹ * j⁻¹ ∈ φ.ker.map Jt.subtype) → z = 1
  card_dvd : ∀ S : Subgroup Y, IsPGroup p S → Nat.card S ∣ p ^ n * n

@[expose] def JStarConcl {Y : Type} [Group Y] (p n : ℕ) [Fact p.Prime] (Jt : Subgroup Y) : Prop :=
  Jt.Normal ∧ Nonempty (Jt ≃* PSL2GF p n) ∧ Subgroup.centralizer (Jt : Set Y) = ⊥

@[expose] def StmtJStarO1 : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}, JStarHyp p n Rb Y₀ Jt Xt φ →
    (∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧ Subgroup.centralizer (O : Set Y) ≤ O) → False

@[expose] def StmtJStarII : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}, JStarHyp p n Rb Y₀ Jt Xt φ →
    (∃ L : Subgroup Y, IsComponentOf L ⊤) →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) →
    False

@[expose] def StmtJStarI : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}, JStarHyp p n Rb Y₀ Jt Xt φ →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ →
    ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) → ¬ K ≤ Y₀ →
    ∀ z ∈ (Rb : Subgroup Y), z ∉ K → orderOf z = p →
      z ∈ Subgroup.centralizer (K : Set Y) → False

@[expose] def StmtJStarIII : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}, JStarHyp p n Rb Y₀ Jt Xt φ →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
    ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
    (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) → JStarConcl p n Jt

theorem jStarConcl_of_cases (hO1 : StmtJStarO1) (hII : StmtJStarII) (hI : StmtJStarI)
    (hIII : StmtJStarIII) {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime]
    {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}
    (h : JStarHyp p n Rb Y₀ Jt Xt φ)
    (hcomp : (¬ ∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧
      Subgroup.centralizer (O : Set Y) ≤ O) → ∃ L : Subgroup Y, IsComponentOf L ⊤) :
    JStarConcl p n Jt := by
  by_cases hcon : ∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧
      Subgroup.centralizer (O : Set Y) ≤ O
  · exact (hO1 h hcon).elim
  have hE := hcomp hcon
  by_cases hall : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)
  · exact (hII h hE hall).elim
  push Not at hall
  obtain ⟨K, hK, hnc⟩ := hall
  rcases h.red.rankOne_or_center hK hnc with ⟨z, hzR, hzK, hzp, hzc, -, hKY₀, -, -⟩ | hcent
  · exact (hI h K hK hnc hKY₀ z hzR hzK hzp hzc).elim
  · exact hIII h K hK (fun L hL => h.red.eq_of_forall_mem_center hK hL hcent) hnc hcent

namespace JStarHyp

variable {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* PSL2GF p n}

theorem eq_of_inf_le (h : JStarHyp p n Rb Y₀ Jt Xt φ) {K : Subgroup Y} (hKJ : K ≤ Jt)
    (hJK : Jt ≤ Subgroup.normalizer (K : Set Y)) (hXK : Xt ⊓ Jt ≤ K) : K = Jt := by
  refine le_antisymm hKJ ?_
  have h1 : nclIn Jt (Xt ⊓ Jt) = nclIn Jt Xt := by
    simp only [nclIn, Subgroup.inf_subgroupOf_right]
  rw [← h.ncl, ← h1]
  exact nclIn_le hXK hKJ hJK

theorem eq_top_of_coprime_card_quotient (h : JStarHyp p n Rb Y₀ Jt Xt φ) (V : Subgroup Jt)
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

theorem eq_of_coprime_relIndex (h : JStarHyp p n Rb Y₀ Jt Xt φ) {V : Subgroup Y} (hVJ : V ≤ Jt)
    (hJV : Jt ≤ Subgroup.normalizer (V : Set Y)) (hV : p.Coprime (V.relIndex Jt)) : V = Jt := by
  have : (V.subgroupOf Jt).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVJ).mpr hJV
  have htop := h.eq_top_of_coprime_card_quotient (V.subgroupOf Jt) hV
  exact le_antisymm hVJ (Subgroup.subgroupOf_eq_top.mp htop)

theorem eq_top_of_map_eq_top (h : JStarHyp p n Rb Y₀ Jt Xt φ) (V : Subgroup Jt) [V.Normal]
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

theorem eq_top_or_le_ker (h : JStarHyp p n Rb Y₀ Jt Xt φ) (V : Subgroup Jt) [hV : V.Normal] :
    V = ⊤ ∨ V ≤ φ.ker := by
  have : IsSimpleGroup (PSL2GF p n) :=
    isSimpleGroup_psl2GF_of_two_le (by have := h.three_le; omega)
  have := hV.map φ h.surj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.map φ) with hbot | htop
  · exact Or.inr ((Subgroup.map_eq_bot_iff _).mp hbot)
  · exact Or.inl (h.eq_top_of_map_eq_top V htop)

theorem eq_or_le_ker (h : JStarHyp p n Rb Y₀ Jt Xt φ) {V : Subgroup Y} (hVJ : V ≤ Jt)
    (hJV : Jt ≤ Subgroup.normalizer (V : Set Y)) : V = Jt ∨ V ≤ φ.ker.map Jt.subtype := by
  have : (V.subgroupOf Jt).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVJ).mpr hJV
  rcases h.eq_top_or_le_ker (V.subgroupOf Jt) with htop | hle
  · exact Or.inl (le_antisymm hVJ (Subgroup.subgroupOf_eq_top.mp htop))
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hVJ]
    exact Subgroup.map_mono hle

theorem nonempty_mulEquiv_of_isSimpleGroup (h : JStarHyp p n Rb Y₀ Jt Xt φ)
    (hs : IsSimpleGroup Jt) : Nonempty (Jt ≃* PSL2GF p n) := by
  have hker : φ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
    · exact hbot
    · obtain ⟨x, hx⟩ := exists_ne (1 : PSL2GF p n)
      obtain ⟨j, rfl⟩ := h.surj x
      exact absurd (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top j)) hx
  exact ⟨MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hker, h.surj⟩⟩

theorem commutator_eq_top (h : JStarHyp p n Rb Y₀ Jt Xt φ) : commutator Jt = ⊤ := by
  refine h.eq_top_of_map_eq_top _ ?_
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ h.surj,
    ← commutator_def]
  exact (psl2GF_isPerfect (by have := h.three_le; omega)).commutator_eq_top

theorem isPerfect (h : JStarHyp p n Rb Y₀ Jt Xt φ) : Group.IsPerfect Jt :=
  ⟨h.commutator_eq_top⟩

theorem commutator_eq (h : JStarHyp p n Rb Y₀ Jt Xt φ) : ⁅Jt, Jt⁆ = Jt :=
  Subgroup.isPerfect_iff.mp h.isPerfect

theorem nontrivial (h : JStarHyp p n Rb Y₀ Jt Xt φ) : Nontrivial Jt :=
  h.surj.nontrivial

theorem not_isPGroup (h : JStarHyp p n Rb Y₀ Jt Xt φ) : ¬ IsPGroup p Jt := fun hJ => by
  have := h.nontrivial
  have := h.isPerfect
  exact Group.IsPerfect.not_isNilpotent Jt hJ.isNilpotent

theorem inf_ker_eq_bot (h : JStarHyp p n Rb Y₀ Jt Xt φ) {S : Subgroup Y} (hS : IsPGroup p S) :
    S ⊓ φ.ker.map Jt.subtype = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
  rw [hk, Subgroup.card_map_of_injective Jt.subtype_injective]
  exact h.coprime.pow_left k

theorem eq_bot_of_isPGroup (h : JStarHyp p n Rb Y₀ Jt Xt φ) {V : Subgroup Y} (hVJ : V ≤ Jt)
    (hJV : Jt ≤ Subgroup.normalizer (V : Set Y)) (hV : IsPGroup p V) : V = ⊥ := by
  rcases h.eq_or_le_ker hVJ hJV with rfl | hle
  · exact absurd hV h.not_isPGroup
  · rw [← inf_eq_left.mpr hle]
    exact h.inf_ker_eq_bot hV

theorem sylow_isElemAbelian (h : JStarHyp p n Rb Y₀ Jt Xt φ) (S : Sylow p Jt) :
    IsElemAbelian p (S : Subgroup Jt) ∧ Nat.card (S : Subgroup Jt) = p ^ n := by
  have hn : 1 ≤ n := by have := h.three_le; omega
  have hT := psl2GF_sylow p n hn (S.mapSurjective h.surj)
  rw [Sylow.coe_mapSurjective] at hT
  have hdisj : (S : Subgroup Jt) ⊓ φ.ker = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
    exact (Subgroup.disjoint_of_coprime_natCard (hk ▸ h.coprime.pow_left k)).eq_bot
  set ψ : (S : Subgroup Jt) →* PSL2GF p n := φ.comp (S : Subgroup Jt).subtype
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    have hs' : (s : Jt) ∈ (S : Subgroup Jt) ⊓ φ.ker := ⟨s.2, hs⟩
    rw [hdisj, Subgroup.mem_bot] at hs'
    exact Subgroup.mem_bot.mpr (Subtype.ext hs')
  have hmem : ∀ s : (S : Subgroup Jt), ψ s ∈ (S : Subgroup Jt).map φ := fun s =>
    Subgroup.mem_map_of_mem φ s.2
  have : IsMulCommutative ((S : Subgroup Jt).map φ) := hT.1.1
  refine ⟨⟨IsMulCommutative.of_comm fun a b => hinj ?_, fun s hs => ?_⟩, ?_⟩
  · rw [map_mul, map_mul]
    exact setLike_mul_comm (hmem a) (hmem b)
  · have hsp : ψ ⟨s, hs⟩ ^ p = 1 := hT.1.2 _ (hmem ⟨s, hs⟩)
    rw [← map_pow, ← map_one ψ] at hsp
    simpa using congrArg Subtype.val (hinj hsp)
  · have hrange : ψ.range = (S : Subgroup Jt).map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hT.2, ← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv

theorem exists_isElemAbelian (h : JStarHyp p n Rb Y₀ Jt Xt φ) :
    ∃ E : Subgroup Y, E ≤ Jt ∧ IsElemAbelian p E ∧ Nat.card E = p ^ n := by
  obtain ⟨S⟩ : Nonempty (Sylow p Jt) := inferInstance
  obtain ⟨hS, hcard⟩ := h.sylow_isElemAbelian S
  exact ⟨(S : Subgroup Jt).map Jt.subtype, Subgroup.map_subtype_le _,
    elementary_abelian_map p hS _, by rw [Subgroup.card_map_of_injective Jt.subtype_injective,
      hcard]⟩

theorem le_normalizer_component (h : JStarHyp p n Rb Y₀ Jt Xt φ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) : Jt ≤ Subgroup.normalizer (L : Set Y) := by
  set N := (Subgroup.normalizer (L : Set Y)).normalCore
  have hK : Jt ⊓ N = Jt := h.eq_of_inf_le inf_le_left
    ((le_inf Subgroup.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    (fun x hx => ⟨hx.2, h.red.sylow_le_normalCore_normalizer_component hL (h.le_R hx.1)⟩)
  calc Jt = Jt ⊓ N := hK.symm
    _ ≤ N := inf_le_right
    _ ≤ _ := Subgroup.normalCore_le _

theorem le_normalizer_inf_centralizer (h : JStarHyp p n Rb Y₀ Jt Xt φ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    Jt ≤ Subgroup.normalizer ((Jt ⊓ Subgroup.centralizer (L : Set Y) : Subgroup Y) : Set Y) :=
  (le_inf Subgroup.le_normalizer ((h.le_normalizer_component hL).trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      inferInstance))).trans Subgroup.inf_normalizer_le_normalizer_inf

theorem le_centralizer_or_inf_le_ker (h : JStarHyp p n Rb Y₀ Jt Xt φ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    Jt ≤ Subgroup.centralizer (L : Set Y) ∨
      Jt ⊓ Subgroup.centralizer (L : Set Y) ≤ φ.ker.map Jt.subtype := by
  rcases h.eq_or_le_ker inf_le_left (h.le_normalizer_inf_centralizer hL) with heq | hle
  · exact Or.inl (inf_eq_left.mp heq)
  · exact Or.inr hle

end JStarHyp

end CFSG.AGLEmbedding
