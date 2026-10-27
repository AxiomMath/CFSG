module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def HasLabel (X : Type) [Group X] (S : GLALabel → Prop) : Prop :=
  GLAMarking X fun lab _ _ _ _ _ => S lab

theorem labelOf_iff_hasLabel {G : Type} [Group G] (K : Subgroup G) (lab : GLALabel) :
    LabelOf K lab ↔ HasLabel ↥K (· = lab) := Iff.rfl

theorem hasLabel_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (S : GLALabel → Prop) :
    HasLabel X S ↔ HasLabel Y S :=
  ⟨fun h => CFSG.StandardType.largeEvenMarking_of_mulEquiv e.symm h,
    fun h => CFSG.StandardType.largeEvenMarking_of_mulEquiv e h⟩

theorem hasLabel_mono {X : Type} [Group X] {S T : GLALabel → Prop} (hST : ∀ l, S l → T l)
    (h : HasLabel X S) : HasLabel X T :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun lab _ _ _ _ _ hl => hST lab hl) h

theorem glaMarking_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {P : GLAMarkProp X} {P' : GLAMarkProp Y}
    (hPP' : ∀ (lab : GLALabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), P' lab R I F θ →
        P lab R I F ((CFSG.StandardType.centerQuotCongr e).trans θ))
    (h : GLAMarking Y P') : GLAMarking X P := by
  obtain ⟨hY, lab, hlab, hraw⟩ := h
  have hperf : Group.IsPerfect Y := ⟨hY⟩
  have hX : commutator X = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, (CFSG.StandardType.centerQuotCongr e).trans θ, hPP' lab R I F θ hθ⟩

variable {G : Type} [Group G]

theorem hasLabel_subgroupOf_iff {K J : Subgroup G} (hJK : J ≤ K) (S : GLALabel → Prop) :
    HasLabel ↥J S ↔ HasLabel ↥(J.subgroupOf K) S :=
  (hasLabel_congr (Subgroup.subgroupOfEquivOfLe hJK) S).symm

theorem isElemAbelian_map_subtype_iff {p : ℕ} {K : Subgroup G} (H' : Subgroup K) :
    IsElemAbelian p (H'.map K.subtype) ↔ IsElemAbelian p H' := by
  constructor
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · simpa using isElemAbelian_commute h (Subgroup.mem_map_of_mem K.subtype a.2)
        (Subgroup.mem_map_of_mem K.subtype b.2)
    · have := h.2 (x : G) (Subgroup.mem_map_of_mem K.subtype hx)
      exact Subtype.ext this
  · intro h
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
      show (a : G) * b = b * a
      rw [← ha, ← hb]
      have := isElemAbelian_commute h ha' hb'
      exact congrArg Subtype.val this
    · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
      have := h.2 x' hx'
      show (K.subtype x') ^ p = 1
      rw [← map_pow, this, map_one]

theorem card_map_subtype {K : Subgroup G} (H' : Subgroup K) :
    Nat.card (H'.map K.subtype) = Nat.card H' :=
  Subgroup.card_map_of_injective K.subtype_injective

theorem subgroupOf_map_subtype_of_le {K H : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hHK]

theorem map_subtype_subgroupOf {K : Subgroup G} (H' : Subgroup K) :
    (H'.map K.subtype).subgroupOf K = H' :=
  Subgroup.comap_map_eq_self_of_injective K.subtype_injective H'

theorem map_subtype_le {K : Subgroup G} (H' : Subgroup K) : H'.map K.subtype ≤ K := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem isElemAbelian_subgroupOf_iff {p : ℕ} {K H : Subgroup G} (hHK : H ≤ K) :
    IsElemAbelian p (H.subgroupOf K) ↔ IsElemAbelian p H := by
  rw [← isElemAbelian_map_subtype_iff, subgroupOf_map_subtype_of_le hHK]

theorem card_subgroupOf {K H : Subgroup G} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  rw [← card_map_subtype, subgroupOf_map_subtype_of_le hHK]

theorem pRank_map_subtype [Finite G] {p : ℕ} {K : Subgroup G} (H' : Subgroup K) :
    CFSG.Open.pRank p (H'.map K.subtype) = CFSG.Open.pRank p H' := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hE, hEA, hcard⟩
    have hEK : E ≤ K := hE.trans (map_subtype_le H')
    refine ⟨E.subgroupOf K, ?_, (isElemAbelian_subgroupOf_iff hEK).2 hEA, ?_⟩
    · intro x hx
      have := hE (Subgroup.mem_subgroupOf.1 hx)
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 this
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
    · rw [card_subgroupOf hEK]; exact hcard
  · rintro ⟨E', hE', hE'A, hcard⟩
    refine ⟨E'.map K.subtype, Subgroup.map_mono hE', (isElemAbelian_map_subtype_iff E').2 hE'A, ?_⟩
    rw [card_map_subtype]; exact hcard

theorem pRank_subgroupOf [Finite G] {p : ℕ} {K H : Subgroup G} (hHK : H ≤ K) :
    CFSG.Open.pRank p (H.subgroupOf K) = CFSG.Open.pRank p H := by
  rw [← pRank_map_subtype, subgroupOf_map_subtype_of_le hHK]

theorem map_centralizer_subtype {K : Subgroup G} (D' : Subgroup K) :
    (Subgroup.centralizer (D' : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer ((D'.map K.subtype : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val (hc d hd)
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    intro d hd
    exact Subtype.ext (hx (d : G) ⟨d, hd, rfl⟩)

theorem map_normalizer_subtype {K : Subgroup G} (D' : Subgroup K) :
    (Subgroup.normalizer (D' : Set K)).map K.subtype =
      K ⊓ Subgroup.normalizer ((D'.map K.subtype : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_normalizer_iff, SetLike.mem_coe,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun h => ?_⟩
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨c * d * c⁻¹, (hc d).1 hd, rfl⟩
    · rintro ⟨e, he, hex⟩
      have hhK : h ∈ K := by
        have h1 : (c : G) * h * (c : G)⁻¹ = e := hex.symm
        have : h = (c : G)⁻¹ * (e : G) * c := by rw [← h1]; group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem c.2) e.2) c.2
      refine ⟨⟨h, hhK⟩, (hc ⟨h, hhK⟩).2 ?_, rfl⟩
      have : (c * ⟨h, hhK⟩ * c⁻¹ : K) = e := Subtype.ext hex.symm
      rw [this]; exact he
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, fun h => ?_, rfl⟩
    constructor
    · intro hh
      obtain ⟨e, he, hex⟩ := (hx (h : G)).1 ⟨h, hh, rfl⟩
      have : e = ⟨x, hxK⟩ * h * ⟨x, hxK⟩⁻¹ := Subtype.ext hex
      exact this ▸ he
    · intro hh
      obtain ⟨e, he, hex⟩ := (hx (h : G)).2 ⟨_, hh, rfl⟩
      have : e = h := Subtype.ext hex
      exact this ▸ he

theorem isPGroup_map_subtype_iff {p : ℕ} {K : Subgroup G} (H' : Subgroup K) :
    IsPGroup p ↥(H'.map K.subtype) ↔ IsPGroup p ↥H' := by
  constructor
  · intro h
    exact h.of_injective (Subgroup.equivMapOfInjective H' K.subtype K.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective H' K.subtype K.subtype_injective).injective
  · intro h
    exact h.of_injective
      (Subgroup.equivMapOfInjective H' K.subtype K.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective H' K.subtype K.subtype_injective).symm.injective

theorem isPGroup_subgroupOf_iff {p : ℕ} {K H : Subgroup G} (hHK : H ≤ K) :
    IsPGroup p ↥(H.subgroupOf K) ↔ IsPGroup p ↥H := by
  rw [← isPGroup_map_subtype_iff, subgroupOf_map_subtype_of_le hHK]

theorem orderOf_subtype {K : Subgroup G} (g : K) : orderOf (g : G) = orderOf g :=
  Subgroup.orderOf_coe g

theorem isSCIn_iff {p : ℕ} {K A : Subgroup G} :
    IsSCIn p K A ↔ A ≤ K ∧ IsElemAbelian p (A.subgroupOf K) ∧
      ∀ g : K, g ∈ Subgroup.centralizer ((A.subgroupOf K : Subgroup K) : Set K) →
        orderOf g = p → g ∈ A.subgroupOf K := by
  constructor
  · rintro ⟨hAK, hA, hSC⟩
    refine ⟨hAK, (isElemAbelian_subgroupOf_iff hAK).2 hA, fun g hg hord => ?_⟩
    have hg' : (g : G) ∈ K ⊓ Subgroup.centralizer (A : Set G) := by
      have := Subgroup.mem_map_of_mem K.subtype hg
      rw [map_centralizer_subtype, subgroupOf_map_subtype_of_le hAK] at this
      exact this
    exact hSC g hg' (by rw [orderOf_subtype]; exact hord)
  · rintro ⟨hAK, hA, hSC⟩
    refine ⟨hAK, (isElemAbelian_subgroupOf_iff hAK).1 hA, fun g hg hord => ?_⟩
    have hgK : g ∈ K := hg.1
    have hg' : (⟨g, hgK⟩ : K) ∈ Subgroup.centralizer ((A.subgroupOf K : Subgroup K) : Set K) := by
      have h2 : g ∈ (Subgroup.centralizer ((A.subgroupOf K : Subgroup K) : Set K)).map K.subtype := by
        rw [map_centralizer_subtype, subgroupOf_map_subtype_of_le hAK]; exact hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 h2
      have : y = ⟨g, hgK⟩ := Subtype.ext hyg
      exact this ▸ hy
    exact hSC ⟨g, hgK⟩ hg' (by rw [← orderOf_subtype]; exact hord)

section Components

variable {G' : Type} [Group G']

theorem isComponentOf_map_iff {ι : G →* G'} (hι : Function.Injective ι) {L H : Subgroup G} :
    CFSG.Open.IsComponentOf (L.map ι) (H.map ι) ↔ CFSG.Open.IsComponentOf L H := by
  constructor
  · rintro ⟨hle, hsn, hqs⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hι).1 hle, ?_, ?_⟩
    · have := CFSG.Open.IsSubnormal.comap ι hsn
      rwa [Subgroup.comap_map_eq_self_of_injective hι, Subgroup.comap_map_eq_self_of_injective hι]
        at this
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective L ι hι) hqs
  · rintro ⟨hle, hsn, hqs⟩
    exact ⟨Subgroup.map_mono hle, hsn.map ι,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective L ι hι).symm hqs⟩

theorem glaLayer_map {ι : G →* G'} (hι : Function.Injective ι) (H : Subgroup G) :
    GLALayer (H.map ι) = (GLALayer H).map ι := by
  have hset : {K' : Subgroup G' | CFSG.Open.IsComponentOf K' (H.map ι)} =
      (Subgroup.map ι) '' {K : Subgroup G | CFSG.Open.IsComponentOf K H} := by
    ext K'
    constructor
    · intro hK'
      have hle : K' ≤ ι.range := hK'.1.trans (Subgroup.map_le_range ι H)
      refine ⟨K'.comap ι, ?_, Subgroup.map_comap_eq_self hle⟩
      show CFSG.Open.IsComponentOf (K'.comap ι) H
      rw [← isComponentOf_map_iff hι, Subgroup.map_comap_eq_self hle]
      exact hK'
    · rintro ⟨K, hK, rfl⟩
      exact (isComponentOf_map_iff hι).2 hK
  show sSup {K' : Subgroup G' | CFSG.Open.IsComponentOf K' (H.map ι)} =
    (sSup {K : Subgroup G | CFSG.Open.IsComponentOf K H}).map ι
  rw [hset, sSup_image, ((Subgroup.gc_map_comap ι).l_sSup)]

theorem glaLayer_le (H : Subgroup G) : GLALayer H ≤ H :=
  sSup_le fun _ hK => hK.1

theorem glaPComponent_map_iff [Finite G] {p : ℕ} (hp : p.Prime) {ι : G →* G'} (hι : Function.Injective ι)
    {X J : Subgroup G} :
    GLAPComponent p (X.map ι) (J.map ι) ↔ GLAPComponent p X J := by
  have hker : Nat.Coprime p (Nat.card ↥(X ⊓ ι.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff ι).2 hι, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  constructor
  · intro h
    obtain ⟨J₀, hJ₀, hmap⟩ := exists_glaPComponent_map_eq hp ι hker h
    have : J₀ = J := Subgroup.map_injective hι hmap
    exact this ▸ hJ₀
  · exact glaPComponent_map hp ι hker

theorem glaPLayer_map [Finite G] {p : ℕ} (hp : p.Prime) {ι : G →* G'} (hι : Function.Injective ι)
    (X : Subgroup G) : GLAPLayer p (X.map ι) = (GLAPLayer p X).map ι := by
  have hset : {K' : Subgroup G' | GLAPComponent p (X.map ι) K'} =
      (Subgroup.map ι) '' {K : Subgroup G | GLAPComponent p X K} := by
    ext K'
    constructor
    · intro hK'
      have hker : Nat.Coprime p (Nat.card ↥(X ⊓ ι.ker)) := by
        rw [(MonoidHom.ker_eq_bot_iff ι).2 hι, inf_bot_eq, Subgroup.card_bot]
        exact Nat.coprime_one_right p
      obtain ⟨K, hK, hmap⟩ := exists_glaPComponent_map_eq hp ι hker hK'
      exact ⟨K, hK, hmap⟩
    · rintro ⟨K, hK, rfl⟩
      exact (glaPComponent_map_iff hp hι).2 hK
  show sSup {K' : Subgroup G' | GLAPComponent p (X.map ι) K'} =
    (sSup {K : Subgroup G | GLAPComponent p X K}).map ι
  rw [hset, sSup_image, ((Subgroup.gc_map_comap ι).l_sSup)]

end Components

theorem map_centralizer_singleton_subtype {K : Subgroup G} (y : K) :
    (Subgroup.centralizer ({y} : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    exact congrArg Subtype.val hc
  · rintro ⟨hxK, hx⟩
    exact ⟨⟨x, hxK⟩, Subtype.ext hx, rfl⟩

theorem subgroupOf_eq_comap {K H : Subgroup G} : H.subgroupOf K = H.comap K.subtype := rfl

theorem subgroupOf_eq_of_map_eq {K : Subgroup G} {H : Subgroup G} {H' : Subgroup K}
    (h : H'.map K.subtype = H) : H.subgroupOf K = H' := by
  rw [← h]; exact map_subtype_subgroupOf H'

@[expose] def conjAut (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    MulAut K :=
  K.normalizerMonoidHom ⟨g⁻¹, Subgroup.inv_mem _ hg⟩

theorem coe_conjAut (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (l : K) :
    ((conjAut K g hg l : K) : G) = g⁻¹ * l * g := by
  show (g⁻¹ * (l : G) * g⁻¹⁻¹ : G) = _
  simp

@[expose] def conjAut' (K : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    MulAut K :=
  K.normalizerMonoidHom ⟨g, hg⟩

theorem coe_conjAut' (K : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) (l : K) :
    ((conjAut' K g hg l : K) : G) = g * l * g⁻¹ := rfl

theorem nGen_map_subtype {K : Subgroup G} (B' : Subgroup K) :
    nGen (B'.map K.subtype) K = (nGen B' (⊤ : Subgroup K)).map K.subtype := by
  apply le_antisymm
  · refine iSup₂_le fun T ⟨hTK, hT2, hBT⟩ => ?_
    have hT' : T = (T.subgroupOf K).map K.subtype := (subgroupOf_map_subtype_of_le hTK).symm
    refine le_trans (le_of_eq hT') (Subgroup.map_mono ?_)
    refine le_iSup₂_of_le (T.subgroupOf K) ⟨le_top, (isPGroup_subgroupOf_iff hTK).2 hT2, ?_⟩ le_rfl
    intro b hb
    have h1 : K.subtype b ∈ Subgroup.normalizer (T : Set G) := hBT (Subgroup.mem_map_of_mem _ hb)
    have h2 : K.subtype b ∈ (Subgroup.normalizer ((T.subgroupOf K : Subgroup K) : Set K)).map K.subtype := by
      rw [map_normalizer_subtype, subgroupOf_map_subtype_of_le hTK]
      exact ⟨b.2, h1⟩
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.1 h2
    have : c = b := Subtype.ext hcb
    exact this ▸ hc
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun T' ⟨_, hT2, hBT⟩ => ?_
    refine le_trans (Subgroup.le_comap_map K.subtype T') (Subgroup.comap_mono ?_)
    refine le_iSup₂_of_le (T'.map K.subtype) ⟨map_subtype_le T', (isPGroup_map_subtype_iff T').2 hT2, ?_⟩ le_rfl
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have : b' ∈ Subgroup.normalizer (T' : Set K) := hBT hb'
    have h2 := Subgroup.mem_map_of_mem K.subtype this
    rw [map_normalizer_subtype] at h2
    exact h2.2

theorem map_le_normalizer_map {K : Subgroup G} {A' J' : Subgroup K}
    (h : A' ≤ Subgroup.normalizer (J' : Set K)) :
    A'.map K.subtype ≤ Subgroup.normalizer ((J'.map K.subtype : Subgroup G) : Set G) := by
  intro a ha
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
  have h2 : K.subtype a' ∈ (Subgroup.normalizer (J' : Set K)).map K.subtype :=
    Subgroup.mem_map_of_mem _ (h ha')
  rw [map_normalizer_subtype] at h2
  exact h2.2

theorem le_normalizer_of_map_le {K : Subgroup G} {A' J' : Subgroup K}
    (h : A'.map K.subtype ≤ Subgroup.normalizer ((J'.map K.subtype : Subgroup G) : Set G)) :
    A' ≤ Subgroup.normalizer (J' : Set K) := by
  intro a ha
  have h1 : K.subtype a ∈ K ⊓ Subgroup.normalizer ((J'.map K.subtype : Subgroup G) : Set G) :=
    ⟨a.2, h (Subgroup.mem_map_of_mem _ ha)⟩
  rw [← map_normalizer_subtype] at h1
  obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.1 h1
  have : c = a := Subtype.ext hca
  exact this ▸ hc

theorem map_le_centralizer_iff {K : Subgroup G} {F' D' : Subgroup K} :
    F'.map K.subtype ≤ K ⊓ Subgroup.centralizer ((D'.map K.subtype : Subgroup G) : Set G) ↔
      F' ≤ Subgroup.centralizer (D' : Set K) := by
  rw [← map_centralizer_subtype, Subgroup.map_le_map_iff_of_injective K.subtype_injective]

theorem inf_centralizer_map {K : Subgroup G} (J' E' : Subgroup K) :
    J'.map K.subtype ⊓ Subgroup.centralizer ((E'.map K.subtype : Subgroup G) : Set G) =
      (J' ⊓ Subgroup.centralizer (E' : Set K)).map K.subtype := by
  rw [Subgroup.map_inf _ _ _ K.subtype_injective, map_centralizer_subtype,
    ← inf_assoc, inf_eq_left.2 (map_subtype_le J')]

theorem map_subtype_eq_bot_iff {K : Subgroup G} (H' : Subgroup K) :
    H'.map K.subtype = ⊥ ↔ H' = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective H' K.subtype_injective

end CFSG.LocalAnalysis.GLTheoremA.Y10F
