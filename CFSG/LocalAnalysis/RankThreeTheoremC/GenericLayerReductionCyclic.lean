module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionMetacyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section CentralizerQuotient

variable {Y : Type*} [Group Y] (L : Subgroup Y) [L.Normal]

omit [L.Normal] in
theorem inf_centralizer_eq_bot (hZ : center L = ⊥) : L ⊓ centralizer (L : Set Y) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgL, hgC⟩
  have : (⟨g, hgL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hgC l l.2)
  rw [hZ, mem_bot] at this
  exact (mem_bot).mpr (congrArg Subtype.val this)

theorem injective_restrict_centralizer (hZ : center L = ⊥) :
    Function.Injective ((QuotientGroup.mk' (centralizer (L : Set Y))).comp L.subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgC : (g : Y) ∈ centralizer (L : Set Y) :=
    (QuotientGroup.eq_one_iff (N := centralizer (L : Set Y)) (g : Y)).mp hg
  have h2 : (g : Y) ∈ L ⊓ centralizer (L : Set Y) := ⟨g.2, hgC⟩
  rw [inf_centralizer_eq_bot L hZ, mem_bot] at h2
  exact Subtype.ext h2

noncomputable def mulEquivMapCentralizer (hZ : center L = ⊥) :
    L ≃* L.map (QuotientGroup.mk' (centralizer (L : Set Y))) :=
  (MonoidHom.ofInjective (injective_restrict_centralizer L hZ)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem centralizer_map_centralizer_eq_bot (hZ : center L = ⊥) :
    centralizer (((L.map (QuotientGroup.mk' (centralizer (L : Set Y)))) :
      Subgroup (Y ⧸ centralizer (L : Set Y))) : Set (Y ⧸ centralizer (L : Set Y))) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (centralizer (L : Set Y)) x
  have hy : y ∈ centralizer (L : Set Y) := by
    rw [mem_centralizer_iff]
    intro l hl
    have hcomm := mem_centralizer_iff.mp hx _ (mem_map_of_mem _ hl)
    have hker : l * y * l⁻¹ * y⁻¹ ∈ centralizer (L : Set Y) := by
      apply (QuotientGroup.eq_one_iff (N := centralizer (L : Set Y)) _).mp
      show QuotientGroup.mk' (centralizer (L : Set Y)) (l * y * l⁻¹ * y⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    have hL : l * y * l⁻¹ * y⁻¹ ∈ L := by
      have : l * (y * l⁻¹ * y⁻¹) = l * y * l⁻¹ * y⁻¹ := by group
      rw [← this]
      exact L.mul_mem hl (‹L.Normal›.conj_mem _ (L.inv_mem hl) y)
    have h2 : l * y * l⁻¹ * y⁻¹ ∈ L ⊓ centralizer (L : Set Y) := ⟨hL, hker⟩
    rw [inf_centralizer_eq_bot L hZ, mem_bot] at h2
    have : l * y = y * l := by
      have h3 : l * y * l⁻¹ = y := mul_inv_eq_one.mp h2
      calc l * y = (l * y * l⁻¹) * l := by group
        _ = y * l := by rw [h3]
    exact this
  exact (QuotientGroup.eq_one_iff y).mpr hy

theorem isCyclic_of_isPGroup_of_isCyclic_sylow {A : Type*} [Group A] [Finite A] {p : ℕ}
    [Fact p.Prime] (T : Sylow p A) (hT : IsCyclic T) {V : Subgroup A} (hV : IsPGroup p V) :
    IsCyclic V := by
  obtain ⟨T', hVT'⟩ := hV.exists_le_sylow
  have : IsCyclic T' := (MulEquiv.isCyclic (Sylow.equiv T' T)).mpr hT
  exact Subgroup.isCyclic_of_le hVT'

theorem isCyclic_inf_map_centralizer {p : ℕ} [Fact p.Prime] [Finite Y] (S : Sylow p Y)
    (hZ : center L = ⊥) (T : Sylow p L) (hTc : IsCyclic ↥(T : Subgroup L)) :
    IsCyclic ↥((S : Subgroup Y).map (QuotientGroup.mk' (centralizer (L : Set Y))) ⊓
      L.map (QuotientGroup.mk' (centralizer (L : Set Y)))) := by
  set ρ := QuotientGroup.mk' (centralizer (L : Set Y)) with hρ
  set V := (S : Subgroup Y).map ρ ⊓ L.map ρ with hV
  have hinj := injective_restrict_centralizer L hZ
  set ρL : L →* Y ⧸ centralizer (L : Set Y) := ρ.comp L.subtype with hρL
  have hVp : IsPGroup p V := (S.isPGroup'.map ρ).to_le inf_le_left
  have hrange : ρL.range = L.map ρ := by
    rw [hρL, MonoidHom.range_comp, Subgroup.range_subtype]
  have hVL : IsPGroup p (V.comap ρL) := hVp.comap_of_injective ρL hinj
  have hcyc : IsCyclic (V.comap ρL) := isCyclic_of_isPGroup_of_isCyclic_sylow T hTc hVL
  have hmap : (V.comap ρL).map ρL = V :=
    Subgroup.map_comap_eq_self (hrange ▸ inf_le_right)
  have : IsCyclic ↥((V.comap ρL).map ρL) :=
    isCyclic_of_surjective (ρL.subgroupMap (V.comap ρL)) (MonoidHom.subgroupMap_surjective _ _)
  rwa [hmap] at this

end CentralizerQuotient

namespace GenericShadow

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {S : Sylow p Y} {z : Y} {Γ : Subgroup Y}

theorem isCyclic_inf_centralizer (h : GenericShadow p S z Γ)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    IsCyclic ↥((S : Subgroup Y) ⊓ centralizer (L : Set Y)) := by
  by_contra hnc
  have h2 := two_le_pRank_of_not_isCyclic h.prime h.ne_two (S.isPGroup'.to_inf_left) hnc
  have hN := h.normalizer_le _ inf_le_left h2
  apply h.not_le_of_isComponentOf hL
  refine le_trans ?_ hN
  refine le_trans ?_ (centralizer_le_normalizer _)
  intro l hl
  rw [mem_centralizer_iff]
  intro g hg
  exact (mem_centralizer_iff.mp hg.2 l hl).symm

theorem centralizer_le (h : GenericShadow p S z Γ)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤) : centralizer (L : Set Y) ≤ Γ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ⟨htS, htL⟩, hto, htZ⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot S hL
  have hzc : zpowers z ≤ centralizer (L : Set Y) := fun x hx =>
    mem_centralizer_iff.mpr fun l _ => (mem_center_iff.mp (zpowers_le.mpr h.mem_center hx) l)
  have htz : t ∉ zpowers z := fun ht => htZ (hzc ht)
  have h2 := h.two_le_pRank_zpowers_sup hto htz
  have hDS : zpowers z ⊔ zpowers t ≤ (S : Subgroup Y) :=
    sup_le (zpowers_le.mpr h.mem_sylow) (zpowers_le.mpr htS)
  have hDC : zpowers z ⊔ zpowers t ≤ centralizer (centralizer (L : Set Y) : Set Y) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      intro c _
      exact mem_center_iff.mp (zpowers_le.mpr h.mem_center hx) c
    · rw [mem_centralizer_iff]
      intro c hc
      have hxL : x ∈ L := (zpowers_le.mpr htL) hx
      exact (mem_centralizer_iff.mp hc x hxL).symm
  exact (le_centralizer_iff.mp hDC).trans
    ((centralizer_le_normalizer _).trans (h.normalizer_le _ hDS h2))

omit [Finite Y] in
theorem map_ne_top_of_centralizer_le {L : Subgroup Y} [L.Normal]
    (hΓ : Γ ≠ ⊤) (hC : centralizer (L : Set Y) ≤ Γ) :
    Γ.map (QuotientGroup.mk' (centralizer (L : Set Y))) ≠ ⊤ := by
  intro htop
  apply hΓ
  have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (centralizer (L : Set Y))) Γ
  rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hC] at hcomap
  exact hcomap.symm

theorem exists_isElemAbelian_map (h : GenericShadow p S z Γ) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) [L.Normal] :
    ∃ E ≤ (S : Subgroup Y), IsElemAbelian p E ∧
      p ^ 2 ≤ Nat.card (E.map (QuotientGroup.mk' (centralizer (L : Set Y)))) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set ρ := QuotientGroup.mk' (centralizer (L : Set Y)) with hρ
  obtain ⟨E, hES, hE, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
    (S : Subgroup Y)
  rw [h.rank_eq] at hEc
  refine ⟨E, hES, hE, ?_⟩
  let φ : E →* Y ⧸ centralizer (L : Set Y) := ρ.comp E.subtype
  have hcyc := h.isCyclic_inf_centralizer hL
  have hker : Nat.card φ.ker ≤ p := by
    have hmem : ∀ e : φ.ker, ((e : E) : Y) ∈ (S : Subgroup Y) ⊓ centralizer (L : Set Y) := by
      intro e
      exact ⟨hES e.1.2, (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp e.2)⟩
    let f : φ.ker →* ↥((S : Subgroup Y) ⊓ centralizer (L : Set Y)) :=
      ((E.subtype.comp φ.ker.subtype).codRestrict _ hmem)
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : (((f a : _) : Y)) = (((f b : _) : Y)) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    have : IsCyclic φ.ker := isCyclic_of_injective f hf
    exact CFSG.AGLEmbedding.card_le_of_isCyclic_of_forall_pow_eq_one hp.pos fun a =>
      Subtype.ext (Subtype.ext (hE.2 _ a.1.2))
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hEc] at hmul
  have hrange : p ^ 2 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range < p * p ^ 2 := by
      calc Nat.card φ.ker * Nat.card φ.range ≤ p * Nat.card φ.range := Nat.mul_le_mul_right _ hker
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hp.pos
    rw [hmul] at this
    nlinarith
  have hφr : φ.range = E.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rwa [hφr] at hrange

theorem two_le_pRank_map (h : GenericShadow p S z Γ) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    [L.Normal] :
    2 ≤ CFSG.Open.pRank p
      ((S : Subgroup Y).map (QuotientGroup.mk' (centralizer (L : Set Y)))) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hES, hE, hEc⟩ := h.exists_isElemAbelian_map hL
  have hel := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE
    (QuotientGroup.mk' (centralizer (L : Set Y)))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p _ hel)
  rw [hm] at hEc
  have h2m : 2 ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp hEc
  exact h2m.trans (le_pRank_of_elemAbelian_card (Subgroup.map_mono hES) hel hm)

end GenericShadow

section Metacyclic

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {X : Type} [Group X]

theorem mem_of_conjNormal_mem_inner (K : Subgroup X) [K.Normal]
    (hKC : centralizer (K : Set X) = ⊥) {x : X}
    (hx : (MulAut.conjNormal (H := K)) x ∈ inner K) : x ∈ K := by
  obtain ⟨k, hk⟩ := hx
  have h1 : ∀ y ∈ K, (k : X) * y * (k : X)⁻¹ = x * y * x⁻¹ := by
    intro y hy
    have := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hk
    simpa using this
  have hc : (k : X)⁻¹ * x ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have := h1 y hy
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [this]
      _ = (k : X)⁻¹ * x * y := by group
  rw [hKC, mem_bot] at hc
  have : x = (k : X) := by
    calc x = (k : X) * ((k : X)⁻¹ * x) := by group
      _ = k := by rw [hc, mul_one]
  exact this ▸ k.2

variable [Finite X]

theorem isCyclic_quotient_of_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Subgroup X)
    [K.Normal] (hKC : centralizer (K : Set X) = ⊥) (P : Subgroup X) (hP : IsPGroup p P)
    (hout : CFSG.Open.pRank p (⊤ : Subgroup (Outer ↥K)) ≤ 1) :
    IsCyclic (↥P ⧸ K.subgroupOf P) := by
  let θ : P →* Outer ↥K :=
    (QuotientGroup.mk' (inner K)).comp ((MulAut.conjNormal (H := K)).comp P.subtype)
  have hker : θ.ker = K.subgroupOf P := by
    ext x
    constructor
    · intro hx
      have := (QuotientGroup.eq_one_iff (N := inner K) _).mp (MonoidHom.mem_ker.mp hx)
      exact mem_of_conjNormal_mem_inner K hKC this
    · intro hx
      rw [MonoidHom.mem_ker]
      apply (QuotientGroup.eq_one_iff (N := inner K) _).mpr
      refine ⟨⟨(x : X), hx⟩, ?_⟩
      rw [← MulAut.conjNormal_val]
      rfl
  have hrange : IsPGroup p θ.range :=
    hP.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hcyc : IsCyclic θ.range := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic hp hp2 hrange hnc
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (le_top : θ.range ≤ ⊤)
    omega
  have e := (QuotientGroup.quotientKerEquivRange θ)
  have e2 := QuotientGroup.quotientMulEquivOfEq hker
  exact (MulEquiv.isCyclic (e2.symm.trans e)).mpr hcyc

theorem mem_of_pow_eq_one_of_outer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Subgroup X)
    [K.Normal] (hKC : centralizer (K : Set X) = ⊥) (P : Subgroup X) (hP : IsPGroup p P)
    (hPK : IsCyclic ↥(P ⊓ K)) (hout : CFSG.Open.pRank p (⊤ : Subgroup (Outer ↥K)) ≤ 1)
    (E : Subgroup X) (hEP : E ≤ P) (hE : ∀ x ∈ E, x ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E)
    {x : X} (hxP : x ∈ P) (hx : x ^ p = 1) : x ∈ E := by
  have hq := isCyclic_quotient_of_outer hp hp2 K hKC P hP hout
  have hN : IsCyclic ↥(K.subgroupOf P) := by
    have h1 : (P ⊓ K).subgroupOf P = K.subgroupOf P := by
      ext y; simp [Subgroup.mem_subgroupOf]
    rw [← h1]
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ K ≤ P))).mpr hPK
  have := mem_of_pow_eq_one_of_isCyclic_quotient hp hp2 hP (K.subgroupOf P) hN hq
    (E.subgroupOf P) (fun y hy => Subtype.ext (hE _ hy))
    (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv])
    (x := ⟨x, hxP⟩) (Subtype.ext hx)
  exact this

end Metacyclic

section CardComap

theorem card_inf_comap {X Y : Type*} [Group X] [Group Y] (ρ : Y →* X) (T : Subgroup Y)
    (V : Subgroup X) (hV : V ≤ T.map ρ) :
    Nat.card ↥(T ⊓ V.comap ρ) = Nat.card ↥(T ⊓ ρ.ker) * Nat.card V := by
  let f : ↥(T ⊓ V.comap ρ) →* X := ρ.comp (T ⊓ V.comap ρ).subtype
  have hr : f.range = V := by
    ext v
    constructor
    · rintro ⟨⟨t, ht⟩, rfl⟩
      exact ht.2
    · intro hv
      obtain ⟨t, ht, htv⟩ := hV hv
      exact ⟨⟨t, ht, by simpa [htv] using hv⟩, htv⟩
  have hk : Nat.card f.ker = Nat.card ↥(T ⊓ ρ.ker) := Nat.card_congr
    { toFun := fun e => ⟨(e.1 : Y), e.1.2.1, MonoidHom.mem_ker.mp e.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1, by
          show ρ y.1 ∈ V
          rw [MonoidHom.mem_ker.mp y.2.2]; exact V.one_mem⟩, MonoidHom.mem_ker.mpr y.2.2⟩
      left_inv := fun e => rfl
      right_inv := fun y => rfl }
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hk, hr] at hmul
  exact hmul.symm

end CardComap

namespace GenericShadow

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {S : Sylow p Y} {z : Y} {Γ : Subgroup Y}

theorem normalizer_map_le (h : GenericShadow p S z Γ) {L : Subgroup Y} [L.Normal]
    (hC : centralizer (L : Set Y) ≤ Γ) (E : Subgroup Y) (hES : E ≤ (S : Subgroup Y))
    (hE : ∀ x ∈ E, x ^ p = 1) (V : Subgroup (Y ⧸ centralizer (L : Set Y)))
    (hVE : V ≤ E.map (QuotientGroup.mk' (centralizer (L : Set Y)))) (hV1 : V ≠ ⊥) :
    normalizer (V : Set (Y ⧸ centralizer (L : Set Y))) ≤
      Γ.map (QuotientGroup.mk' (centralizer (L : Set Y))) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set C := centralizer (L : Set Y) with hCdef
  set ρ := QuotientGroup.mk' C with hρ
  have hVS : V ≤ (S : Subgroup Y).map ρ := hVE.trans (Subgroup.map_mono hES)
  intro nb hnb
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective C nb
  set W := V.comap ρ with hW
  have hρC : ∀ c ∈ C, ρ c = 1 := fun c hc => (QuotientGroup.eq_one_iff c).mpr hc
  have hCW : C ≤ W := fun c hc => by
    show ρ c ∈ V
    rw [hρC c hc]; exact V.one_mem
  have hnW : n ∈ normalizer (W : Set Y) := by
    rw [mem_normalizer_iff]
    intro w
    have := mem_normalizer_iff.mp hnb (ρ w)
    simpa [hρ, hW, mem_comap, map_mul, map_inv, QuotientGroup.mk'_apply] using this
  set Wh : Subgroup Y := (S : Subgroup Y) ⊓ W with hWh
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV1
  obtain ⟨e₁, he₁E, he₁v⟩ := hVE hv
  have he₁W : e₁ ∈ W := by
    show ρ e₁ ∈ V
    rw [he₁v]; exact hv
  have hzC : z ∈ C := by
    rw [hCdef, mem_centralizer_iff]
    intro l _
    exact mem_center_iff.mp h.mem_center l
  have hzW : z ∈ W := hCW hzC
  have he₁z : e₁ ∉ zpowers z := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hρz : ρ z = 1 := hρC z hzC
    apply hv1
    apply Subtype.ext
    show v = 1
    rw [← he₁v, ← hk, map_zpow, hρz, one_zpow]
  have hrank : 2 ≤ CFSG.Open.pRank p Wh :=
    CFSG.AGLEmbedding.two_le_pRank_of_commute_of_not_mem_zpowers hp h.orderOf_eq (hE e₁ he₁E)
      he₁z (mem_center_iff.mp h.mem_center e₁).symm ⟨h.mem_sylow, hzW⟩ ⟨hES he₁E, he₁W⟩
  have hWhN : normalizer (Wh : Set Y) ≤ Γ := h.normalizer_le _ inf_le_left hrank
  have hker : ρ.ker = C := QuotientGroup.ker_mk' C
  have hWhcard : Nat.card Wh = Nat.card ↥((S : Subgroup Y) ⊓ C) * Nat.card V := by
    have := card_inf_comap ρ (S : Subgroup Y) V hVS
    rwa [hker] at this
  have hWcard : Nat.card W = Nat.card C * Nat.card V := by
    have := card_inf_comap ρ ⊤ V (by
      rw [Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective C)]; exact le_top)
    rw [hker, top_inf_eq, top_inf_eq] at this
    exact this
  have hSC : Nat.card ↥((S : Subgroup Y) ⊓ C) = p ^ (Nat.card C).factorization p := by
    obtain ⟨P', hP'⟩ := CFSG.Glauberman.sylow_inf_normal S (N := C)
    have h1 := P'.card_eq_multiplicity
    rw [hP'] at h1
    rw [← h1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  obtain ⟨b, hb⟩ : ∃ b, Nat.card V = p ^ b :=
    IsPGroup.iff_card.mp ((S.isPGroup'.map ρ).to_le hVS)
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p Wh W := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right ?_
    rw [hWhcard, hWcard, hSC, hb]
    have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hC0 (pow_ne_zero b hp.ne_zero)]
    simp [hp.factorization, pow_add]
  have hfr := le_sup_normalizer_of_isSylowOf (Subgroup.zpowers_le.mpr hnW) hsyl
  have hWΓ : W ≤ Γ := by
    intro w hw
    obtain ⟨s, hs, hsw⟩ := hVS (hw : ρ w ∈ V)
    have hsW : s ∈ W := by
      show ρ s ∈ V
      rw [hsw]; exact hw
    have hc : s⁻¹ * w ∈ C := by
      apply (QuotientGroup.eq_one_iff (N := C) _).mp
      show ρ (s⁻¹ * w) = 1
      rw [map_mul, map_inv]
      have : ρ s = ρ w := hsw
      rw [this, inv_mul_cancel]
    have hsΓ : s ∈ Γ := hWhN (Subgroup.le_normalizer ⟨hs, hsW⟩)
    have := Γ.mul_mem hsΓ (hC hc)
    simpa using this
  have hnΓ : n ∈ Γ := (sup_le hWΓ hWhN) (hfr (Subgroup.mem_zpowers n))
  exact Subgroup.mem_map_of_mem ρ hnΓ

theorem isoLie_suzuki_of_isCyclic (h : GenericShadow p S z Γ) (hK4 : KF1On Y)
    (hK2 : StronglyEmbeddedCyclicOuterKFact) (hK3 : KFactOutCyclic) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ↥((S : Subgroup Y) ⊓ L)) :
    p = 5 ∧ IsoLie ↥L (.suzuki 2) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hLn : L.Normal := h.normal_of_isComponentOf hL
  have hZ := h.center_eq_bot hK4 hL
  obtain ⟨hsimple, hnonab, hcat⟩ := h.simple_nonab_catalog hK4 hL
  set C := centralizer (L : Set Y) with hCdef
  set ρ := QuotientGroup.mk' C with hρ
  set K := L.map ρ with hK
  have hKn : K.Normal := Subgroup.Normal.map hLn ρ (QuotientGroup.mk'_surjective C)
  let eL : L ≃* K := mulEquivMapCentralizer L hZ
  have hKsimple : IsSimpleGroup ↥K := eL.symm.isSimpleGroup
  have hKnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eL a, eL b, fun hba => hab (eL.injective (by simpa only [map_mul] using hba))⟩
  have hKcat : IsCatalogGroup ↥K := CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv eL.symm hcat
  have hKC : centralizer (K : Set (Y ⧸ C)) = ⊥ := centralizer_map_centralizer_eq_bot L hZ
  obtain ⟨T, hT⟩ := h.exists_sylow_map_eq_inf hL
  have hTc : IsCyclic ↥(T : Subgroup L) := by
    have e : ↥(T : Subgroup L) ≃* ↥((S : Subgroup Y) ⊓ L) :=
      (T.1.equivMapOfInjective L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hT)
    exact (MulEquiv.isCyclic e).mpr hcyc
  let P : Sylow p (Y ⧸ C) := S.mapSurjective (QuotientGroup.mk'_surjective C)
  have hP : (P : Subgroup (Y ⧸ C)) = (S : Subgroup Y).map ρ := Sylow.coe_mapSurjective _ _
  have hPK : IsCyclic ↥((P : Subgroup (Y ⧸ C)) ⊓ K) := by
    rw [hP]; exact isCyclic_inf_map_centralizer L S hZ T hTc
  have hrank : 2 ≤ CFSG.Open.pRank p (P : Subgroup (Y ⧸ C)) := by
    rw [hP]; exact h.two_le_pRank_map hL
  have hCΓ : C ≤ Γ := h.centralizer_le hL
  have hΓK : Γ.map ρ ≠ ⊤ := map_ne_top_of_centralizer_le h.ne_top hCΓ
  have hout : CFSG.Open.pRank p
      (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K)) ≤ 1 := by
    let TK : Sylow p ↥K := T.mapSurjective (f := eL.toMonoidHom) eL.surjective
    have hTKmap : (TK : Subgroup ↥K) = (T : Subgroup L).map eL.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    have hTKc : IsCyclic ↥(TK : Subgroup K) := by
      rw [hTKmap]
      exact isCyclic_of_surjective ((eL.toMonoidHom).subgroupMap (T : Subgroup L))
        (MonoidHom.subgroupMap_surjective _ _)
    exact hK3 K hKsimple hKnonab hKcat p hp h.ne_two TK hTKc
  obtain ⟨E, hES, hE, hEc⟩ := h.exists_isElemAbelian_map hL
  have hEP : E.map ρ ≤ (P : Subgroup (Y ⧸ C)) := hP ▸ Subgroup.map_mono hES
  have hEexp : ∀ x ∈ E.map ρ, x ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE.2 e he, map_one]
  have hKS : ∀ x ∈ (P : Subgroup (Y ⧸ C)), x ^ p = 1 → x ∈ E.map ρ := fun x hx hxp =>
    mem_of_pow_eq_one_of_outer hp h.ne_two K hKC (P : Subgroup (Y ⧸ C)) P.isPGroup' hPK hout
      (E.map ρ) hEP hEexp hEc hx hxp
  have hGamma : rankThreeGamma 1 p (P : Subgroup (Y ⧸ C)) ≠ ⊤ := by
    have hle : rankThreeGamma 1 p (P : Subgroup (Y ⧸ C)) ≤ Γ.map ρ := by
      refine sSup_le ?_
      rintro N ⟨Q, hQP, hQ1, rfl⟩
      obtain ⟨q, hqQ, hqo⟩ := exists_orderOf_eq_of_one_le_pRank hp hQ1
      set V : Subgroup (Y ⧸ C) := Q ⊓ E.map ρ with hV
      have hVE : V ≤ E.map ρ := inf_le_right
      have hqV : q ∈ V := ⟨hqQ, hKS q (hQP hqQ) (hqo ▸ pow_orderOf_eq_one q)⟩
      have hV1 : V ≠ ⊥ := by
        intro hbot
        rw [hbot, mem_bot] at hqV
        rw [hqV, orderOf_one] at hqo
        exact hp.one_lt.ne hqo
      refine le_trans ?_ (h.normalizer_map_le hCΓ E hES hE.2 V hVE hV1)
      intro nb hnb
      have hmap : V.map (MulAut.conj nb).toMonoidHom ≤ V := by
        rintro _ ⟨v, ⟨hvQ, hvE⟩, rfl⟩
        have hQ' : (MulAut.conj nb) v ∈ Q := by
          have := (mem_normalizer_iff.mp hnb v).mp hvQ
          simpa [MulAut.conj_apply] using this
        refine ⟨hQ', hKS _ (hQP hQ') ?_⟩
        show ((MulAut.conj nb) v) ^ p = 1
        rw [← map_pow, hEexp v hvE, map_one]
      have hVeq : V.map (MulAut.conj nb).toMonoidHom = V :=
        Subgroup.eq_of_le_of_card_ge hmap
          (Subgroup.card_map_of_injective (MulAut.conj nb).injective).ge
      exact mem_normalizer_iff_map_conj_eq.mpr hVeq
    intro htop
    rw [htop, top_le_iff] at hle
    exact hΓK hle
  rcases hK2 (Y ⧸ C) K hKn hKsimple hKnonab hKcat hKC p hp h.ne_two P hPK hrank hGamma with
    ⟨h3, -⟩ | ⟨h5, hsuz⟩
  · have := h.five_le
    omega
  · exact ⟨h5, isoLie_of_mulEquiv eL.symm hsuz⟩

end GenericShadow

end CFSG.LocalAnalysis.RankThreeTheoremC
