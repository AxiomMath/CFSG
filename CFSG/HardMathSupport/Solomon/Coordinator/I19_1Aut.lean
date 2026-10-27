module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Core
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Balance

open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem conj_mem_gLAPPrimeCoreOf_of_mem_normalizer {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J) :
    g * y * g⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨J.normalizerMonoidHom ⟨g, hg⟩ y',
    map_gLAPPrimeCore_le p (J.normalizerMonoidHom ⟨g, hg⟩) ⟨y', hy', rfl⟩, ?_⟩
  rfl

theorem mem_centralizerQuot_iff_barAut_eq_one (p : ℕ) {J : Subgroup G}
    (g : ↥(Subgroup.normalizer (J : Set G))) :
    (g : G) ∈ centralizerQuot J (GLAPPrimeCoreOf p J) ↔ barAut p J g = 1 := by
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom g y : ↥J) : G) = g * y * (g : G)⁻¹ := fun _ => rfl
  constructor
  · rintro ⟨-, -, hc⟩
    ext z
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [barAut_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq]
    have := hc (y : G)⁻¹ (J.inv_mem y.2)
    refine (Subgroup.mem_map_iff_mem J.subtype_injective).1
      (?_ : J.subtype _ ∈ GLAPPrimeCoreOf p J)
    simpa [mul_assoc, hs] using this
  · intro h
    refine ⟨g.2, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_gLAPPrimeCoreOf_of_mem_normalizer g.2 hy, fun hy => ?_⟩
      have := conj_mem_gLAPPrimeCoreOf_of_mem_normalizer (inv_mem g.2) hy
      simpa [mul_assoc] using this
    · have h1 := congrArg (fun φ => φ (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥J))) h
      simp only [barAut_mk, MulAut.one_apply] at h1
      rw [eq_comm, QuotientGroup.eq] at h1
      have h2 : J.subtype _ ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map_of_mem J.subtype h1
      simpa [mul_assoc, hs] using h2

end Basic

section Image

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem map_mem_centralizer_core {Z : Type} [Group Z] (hH1 : H1Stmt.{0}) (hp : p.Prime)
    {A : Subgroup G} (π : ↥A →* Z) (hπ : Function.Surjective π) {e : ↥A} (hpe : e ^ p = 1)
    {x : ↥A} (hx : (x : G) ∈ GLAPPrimeCoreOf p (A ⊓ Subgroup.centralizer ({(e : G)} : Set G))) :
    π x ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({π e} : Set Z)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [gLAPPrimeCoreOf_inf_centralizer_eq_map p A e.2] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  have hQ : IsPGroup p (Subgroup.zpowers e) := isPGroup_zpowers_of_pow_eq_one hp hpe
  have h1 := hH1 π hπ hp hQ
  have e1 : (Subgroup.centralizer ((Subgroup.zpowers e : Subgroup ↥A) : Set ↥A)) =
      Subgroup.centralizer ({e} : Set ↥A) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure _
  have e2 : ((Subgroup.zpowers e).map π : Subgroup Z) = Subgroup.zpowers (π e) :=
    MonoidHom.map_zpowers _ e
  have e3 : (Subgroup.centralizer ((Subgroup.zpowers (π e) : Subgroup Z) : Set Z)) =
      Subgroup.centralizer ({π e} : Set Z) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure _
  rw [e1] at h1
  rw [e2, e3] at h1
  exact h1 ⟨y, hy, rfl⟩

variable {X D S : Subgroup G}

theorem InDelta.map_le_localDeltaIn (hH1 : H1Stmt.{0}) (hp : p.Prime) (h : InDelta p X D S)
    {L : Subgroup G} (hLX : L ≤ X) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hDN : D ≤ Subgroup.normalizer (L : Set G)) :
    (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
      localDeltaIn p
        (((S ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))
        ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) := by
  classical
  set N := Subgroup.normalizer (L : Set G) with hN
  set A : Subgroup G := S ⊔ L ⊔ D with hA
  have hAN : A ≤ N := sup_le (sup_le hSN L.le_normalizer) hDN
  have hAX : A ≤ X := sup_le (sup_le h.S_le hLX) h.D_le
  set ρ : ↥A →* MulAut (barOf p L) := (barAut p L).comp (Subgroup.inclusion hAN) with hρ
  rintro _ ⟨⟨s, hsN⟩, hs, rfl⟩
  have hsS : s ∈ S := (Subgroup.mem_subgroupOf).1 hs
  simp only [localDeltaIn, Subgroup.mem_iInf]
  rintro _ ⟨⟨e, heN⟩, he, rfl⟩ hne
  have heD : e ∈ D := (Subgroup.mem_subgroupOf).1 he
  have he1 : e ≠ 1 := fun h1 => hne (by
    have : (⟨e, heN⟩ : ↥N) = 1 := Subtype.ext h1
    rw [this, map_one])
  have hSA : S ≤ A := le_sup_left.trans le_sup_left
  have hDA : D ≤ A := le_sup_right
  have hSLA : S ⊔ L ≤ A := le_sup_left
  have hSSL : S ≤ S ⊔ L := le_sup_left
  have hsA : s ∈ A := hSA hsS
  have heA : e ∈ A := hDA heD
  have hcore := h.le_core e heD he1 hsS
  have hsCe : s ∈ Subgroup.centralizer ({e} : Set G) :=
    (Subgroup.mem_inf.1 (Subgroup.map_subtype_le _ hcore)).2
  have hx : ((⟨s, hsA⟩ : ↥A) : G) ∈
      GLAPPrimeCoreOf p (A ⊓ Subgroup.centralizer ({((⟨e, heA⟩ : ↥A) : G)} : Set G)) :=
    inf_glaPPrimeCoreOf_le (H := A ⊓ Subgroup.centralizer ({e} : Set G))
      (A := X ⊓ Subgroup.centralizer ({e} : Set G)) hp (inf_le_inf_right _ hAX)
      (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hsA, hsCe⟩, hcore⟩)
  have hpe : (⟨e, heA⟩ : ↥A) ^ p = 1 := Subtype.ext (h.elem.2 e heD)
  have key := map_mem_centralizer_core hH1 hp ρ.rangeRestrict ρ.rangeRestrict_surjective hpe hx
  have hmem1 : ρ ⟨s, hsA⟩ ∈ GLAPPrimeCoreOf p
      (ρ.range ⊓ Subgroup.centralizer ({ρ ⟨e, heA⟩} : Set (MulAut (barOf p L)))) := by
    rw [gLAPPrimeCoreOf_inf_centralizer_eq_map p ρ.range (⟨⟨e, heA⟩, rfl⟩ : ρ ⟨e, heA⟩ ∈ ρ.range)]
    exact ⟨ρ.rangeRestrict ⟨s, hsA⟩, key, rfl⟩
  have hH'Z : (((S ⊔ L).subgroupOf N).map (barAut p L)) ≤ ρ.range := by
    rintro _ ⟨⟨t, htN⟩, ht, rfl⟩
    exact ⟨⟨t, hSLA (Subgroup.mem_subgroupOf.1 ht)⟩, rfl⟩
  have hmemH : barAut p L ⟨s, hsN⟩ ∈ (((S ⊔ L).subgroupOf N).map (barAut p L)) :=
    ⟨⟨s, hsN⟩, (Subgroup.mem_subgroupOf).2 (hSSL hsS), rfl⟩
  have hmemC : barAut p L ⟨s, hsN⟩ ∈
      Subgroup.centralizer ({barAut p L ⟨e, heN⟩} : Set (MulAut (barOf p L))) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hsCe)
  exact inf_glaPPrimeCoreOf_le
    (H := ((S ⊔ L).subgroupOf N).map (barAut p L) ⊓
      Subgroup.centralizer ({barAut p L ⟨e, heN⟩} : Set (MulAut (barOf p L))))
    (A := ρ.range ⊓ Subgroup.centralizer ({ρ ⟨e, heA⟩} : Set (MulAut (barOf p L)))) hp
    (inf_le_inf_right _ hH'Z) (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hmemH, hmemC⟩, hmem1⟩)

theorem InDelta.map_ne_bot (hp : p.Prime) {L : Subgroup G}
    (hL : GLAPComponent p X L) (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hn : ¬ ⁅L, S⁆ ≤ GLAPPrimeCoreOf p X) :
    (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥ := by
  intro hbot
  refine hn (Subgroup.commutator_le.2 fun x hx s hs => ?_)
  have h1 : barAut p L ⟨s, hSN hs⟩ = 1 := by
    have : barAut p L ⟨s, hSN hs⟩ ∈
        (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) :=
      ⟨⟨s, hSN hs⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩
    rw [hbot] at this
    exact this
  obtain ⟨-, -, hc⟩ := (mem_centralizerQuot_iff_barAut_eq_one p ⟨s, hSN hs⟩).2 h1
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hc x hx)

omit [Finite G] in
theorem barAut_injOn_of_kerB_eq_bot {D L : Subgroup G} (hker : kerB p D L = ⊥) :
    Function.Injective ((barAut p L).domRestrict
      (D.subgroupOf (Subgroup.normalizer (L : Set G)))) := by
  intro a b hab
  have h1 : barAut p L ((a : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * b) = 1 := by
    have : barAut p L a = barAut p L b := hab
    rw [map_mul, map_inv, this, inv_mul_cancel]
  have h2 := (mem_centralizerQuot_iff_barAut_eq_one p _).2 h1
  have h3 : (((a : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * b : ↥(Subgroup.normalizer (L : Set G))) : G)
      ∈ kerB p D L := by
    refine ⟨?_, h2⟩
    have := D.mul_mem (D.inv_mem ((Subgroup.mem_subgroupOf).1 a.2))
      ((Subgroup.mem_subgroupOf).1 b.2)
    simpa using this
  rw [hker, Subgroup.mem_bot] at h3
  have h4 : ((a : ↥(Subgroup.normalizer (L : Set G))) : G)⁻¹ * (b : G) = 1 := by simpa using h3
  exact Subtype.ext (Subtype.ext (inv_mul_eq_one.1 h4))

omit [Finite G] in
theorem card_map_barAut {D L : Subgroup G} (hDN : D ≤ Subgroup.normalizer (L : Set G))
    (hker : kerB p D L = ⊥) :
    Nat.card ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) = Nat.card D := by
  rw [← MonoidHom.domRestrict_range]
  exact ((Nat.card_congr (MonoidHom.ofInjective (barAut_injOn_of_kerB_eq_bot hker)).toEquiv).symm
    ).trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv)

omit [Finite G] in
theorem conj_mem_sup_of_mem_normalizer {S L : Subgroup G} {e : G}
    (hS : e ∈ Subgroup.normalizer (S : Set G)) (hL : e ∈ Subgroup.normalizer (L : Set G))
    {t : G} (ht : t ∈ S ⊔ L) : e * t * e⁻¹ ∈ S ⊔ L := by
  have : S ⊔ L ≤ (S ⊔ L).comap (MulAut.conj e).toMonoidHom := by
    refine sup_le (fun s hs => ?_) (fun l hl => ?_)
    · exact (le_sup_left : S ≤ S ⊔ L) ((Subgroup.mem_normalizer_iff.1 hS s).1 hs)
    · exact (le_sup_right : L ≤ S ⊔ L) ((Subgroup.mem_normalizer_iff.1 hL l).1 hl)
  exact this ht

omit [Finite G] in
theorem innerAut_le_map {S L : Subgroup G} :
    innerAut (barOf p L) ≤
      ((S ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) := by
  rintro _ ⟨z, rfl⟩
  induction z using QuotientGroup.induction_on with | H l => ?_
  refine ⟨⟨(l : G), L.le_normalizer l.2⟩,
    (Subgroup.mem_subgroupOf).2 ((le_sup_right : L ≤ S ⊔ L) l.2), ?_⟩
  ext w
  induction w using QuotientGroup.induction_on with | H w => ?_
  have h1 : L.normalizerMonoidHom ⟨(l : G), L.le_normalizer l.2⟩ w = l * w * l⁻¹ :=
    Subtype.ext rfl
  show barAut p L ⟨(l : G), L.le_normalizer l.2⟩ (QuotientGroup.mk w) = _
  rw [barAut_mk, h1]
  simp [MulAut.conj_apply]

theorem map_subgroupOf_le_normalizer_map {E S L : Subgroup G}
    (hES : E ≤ Subgroup.normalizer (S : Set G)) (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    (E.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
      Subgroup.normalizer ((((S ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map
        (barAut p L) : Subgroup (MulAut (barOf p L))) : Set (MulAut (barOf p L))) := by
  rintro _ ⟨⟨e, heN⟩, he, rfl⟩
  have heE : e ∈ E := (Subgroup.mem_subgroupOf).1 he
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨⟨t, htN⟩, ht, rfl⟩ := hn
  have htSL : t ∈ S ⊔ L := (Subgroup.mem_subgroupOf).1 ht
  have hconj := conj_mem_sup_of_mem_normalizer (hES heE) (hEL heE) htSL
  have hconjN : e * t * e⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (mul_mem heN htN) (inv_mem heN)
  refine ⟨⟨e * t * e⁻¹, hconjN⟩, (Subgroup.mem_subgroupOf).2 hconj, ?_⟩
  show barAut p L (⟨e, heN⟩ * ⟨t, htN⟩ * ⟨e, heN⟩⁻¹) = _
  rw [map_mul, map_mul, map_inv]

theorem not_isCompLocallyBalanced {k : ℕ} {D S L : Subgroup G} (hel : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ k) (hDN : D ≤ Subgroup.normalizer (L : Set G))
    (hker : kerB p D L = ⊥) (hDS : D ≤ Subgroup.normalizer (S : Set G))
    (hne : (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥)
    (hle : (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
      localDeltaIn p
        (((S ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))
        ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))) :
    ¬ IsCompLocallyBalanced p k D L := by
  intro hbal
  have hA : autBar p D L = (D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) := by
    unfold autBar
    rw [inf_eq_left.2 hDN]
  rw [IsCompLocallyBalanced, hA] at hbal
  have hE : IsEkIn p k ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))
      ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)) :=
    ⟨le_rfl, isElemAbelian_map (isElemAbelian_subgroupOf hel) _,
      (card_map_barAut hDN hker).trans hcard⟩
  have := hbal _ hE _ innerAut_le_map (map_subgroupOf_le_normalizer_map hDS hDN)
  exact hne (le_bot_iff.1 (hle.trans this.le))

theorem InDelta.conclusions_nocard (hH1 : H1Stmt.{0}) (hp : p.Prime) (h : InDelta p X D S)
    {L : Subgroup G} (hL : GLAPComponent p X L) (hn : ¬ ⁅L, S⁆ ≤ GLAPPrimeCoreOf p X) :
    S ≤ Subgroup.normalizer (L : Set G) ∧ D ≤ Subgroup.normalizer (L : Set G) ∧ kerB p D L = ⊥ ∧
      (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥ ∧
      ((S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
        localDeltaIn p
          (((S ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))
          ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))) := by
  obtain ⟨hSN, hmain⟩ := h.main hH1 hp hL
  obtain ⟨hDN, hker⟩ := hmain hn
  exact ⟨hSN, hDN, hker, InDelta.map_ne_bot hp hL hSN hn,
    h.map_le_localDeltaIn hH1 hp hL.1 hSN hDN⟩

theorem InDelta.conclusions (hH1 : H1Stmt.{0}) (hp : p.Prime) (h : InDelta p X D S) {L : Subgroup G}
    (hL : GLAPComponent p X L) {k : ℕ} (hcard : Nat.card D = p ^ k)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hn : ¬ ⁅L, S⁆ ≤ GLAPPrimeCoreOf p X) :
    D ≤ Subgroup.normalizer (L : Set G) ∧ kerB p D L = ⊥ ∧
      (S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥ ∧
      ((S.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
        localDeltaIn p
          (((S ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))
          ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L))) ∧
      ¬ IsCompLocallyBalanced p k D L := by
  obtain ⟨hSN, hDN, hker, hne, hle⟩ := h.conclusions_nocard hH1 hp hL hn
  exact ⟨hDN, hker, hne, hle, not_isCompLocallyBalanced h.elem hcard hDN hker hDS hne hle⟩

end Image

end CFSG.HardMathSupport.Solomon.Coordinator
