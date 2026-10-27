module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Cases
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Bar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L221Bar

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace F3L226

section Components

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isSubnormal_subgroupOf_mono {A D C : Subgroup Q} (hDC : D ≤ C)
    (h : (A.subgroupOf C).IsSubnormal) : (A.subgroupOf D).IsSubnormal := by
  have h1 := h.subgroupOf (K := D.subgroupOf C)
  have heq : A.subgroupOf D = ((A.subgroupOf C).subgroupOf (D.subgroupOf C)).comap
      (subgroupOfEquivOfLe hDC).symm.toMonoidHom := by
    ext x
    exact Iff.rfl
  rw [heq]
  exact h1.comap _

omit [Finite Q] in
theorem isQuasisimple_of_gw (hD : GorensteinWalter.IsQuasisimple Q) : IsQuasisimple Q := by
  obtain ⟨hnt, hc, hs⟩ := hD
  refine ⟨Group.isPerfect_def.mpr hc, hs, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ center Q := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hab (QuotientGroup.mk a) (QuotientGroup.mk b)]
    group
  rw [hc] at hle
  have hab' : ∀ a b : Q, a * b = b * a := fun a b => mem_center_iff.mp (hle (mem_top b)) a
  have hbot : commutator Q = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun a _ => mem_centralizer_iff.mpr fun b _ => hab' b a
  rw [hc] at hbot
  obtain ⟨a, b, hne⟩ := exists_pair_ne Q
  have ha : a ∈ (⊥ : Subgroup Q) := hbot ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup Q) := hbot ▸ mem_top b
  rw [mem_bot] at ha hb
  exact hne (ha.trans hb.symm)

omit [Finite Q] in
theorem isSubnormal_of_isComponentOf {D : Subgroup Q}
    (hD : GorensteinWalter.IsComponentOf D ⊤) : D.IsSubnormal := by
  have h := hD.2.1.map (f := (⊤ : Subgroup Q).subtype) (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
  rwa [subgroupOf_map_subtype, inf_top_eq] at h

omit [Finite Q] in
theorem isComponentOf_map_conj {D : Subgroup Q} (hD : GorensteinWalter.IsComponentOf D ⊤)
    (g : Q) : GorensteinWalter.IsComponentOf (D.map (MulAut.conj g).toMonoidHom) ⊤ := by
  refine ⟨le_top, ((isSubnormal_of_isComponentOf hD).map (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective).subgroupOf, ?_⟩
  exact F3L221.gwIsQuasisimple (LocalCores.isQuasisimple_of_mulEquiv
    (D.equivMapOfInjective _ (MulAut.conj g).injective) (isQuasisimple_of_gw hD.2.2))

@[expose] def compCentralizer (Q : Type*) [Group Q] : Subgroup Q :=
  ⨅ (D : Subgroup Q) (_ : GorensteinWalter.IsComponentOf D ⊤), centralizer (D : Set Q)

omit [Finite Q] in
theorem mem_compCentralizer {x : Q} :
    x ∈ compCentralizer Q ↔
      ∀ D : Subgroup Q, GorensteinWalter.IsComponentOf D ⊤ → ∀ d ∈ D, d * x = x * d := by
  simp only [compCentralizer, mem_iInf, mem_centralizer_iff, SetLike.mem_coe]

omit [Finite Q] in
theorem compCentralizer_normal : (compCentralizer Q).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_compCentralizer] at hn ⊢
  intro D hD d hd
  have hD' := isComponentOf_map_conj hD g⁻¹
  have hd' : g⁻¹ * d * g⁻¹⁻¹ ∈ D.map (MulAut.conj g⁻¹).toMonoidHom := ⟨d, hd, rfl⟩
  have h1 := hn _ hD' _ hd'
  rw [inv_inv] at h1
  calc d * (g * n * g⁻¹) = g * ((g⁻¹ * d * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * d * g)) * g⁻¹ := by rw [h1]
    _ = g * n * g⁻¹ * d := by group

theorem le_compCentralizer {t : Q} {D₀ X : Subgroup Q}
    (hD₀ : GorensteinWalter.IsComponentOf D₀ ⊤) (htD₀ : t ∈ D₀)
    (hXC : X ≤ centralizer {t}) (hXs : (X.subgroupOf (centralizer {t})).IsSubnormal)
    (hXsol : Group.IsSolvable ↥X) (hXD₀ : ∀ x ∈ X, ∀ d ∈ D₀, d * x = x * d) :
    X ≤ compCentralizer Q := by
  intro x hx
  rw [mem_compCentralizer]
  intro D hD d hd
  by_cases hDD : D = D₀
  · subst hDD
    exact hXD₀ x hx d hd
  have hcomm : ∀ a ∈ D, a * t = t * a := by
    intro a ha
    have h1 := commutator_mem_commutator ha htD₀
    rw [GorensteinWalter.component_commute_of_ne hD hD₀ hDD, mem_bot, commutatorElement_def] at h1
    calc a * t = (a * t * a⁻¹ * t⁻¹) * (t * a) := by group
      _ = t * a := by rw [h1, one_mul]
  have hDC : D ≤ centralizer ({t} : Set Q) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (hcomm a ha)
  exact (F3L221.commute_of_isQuasisimple hDC (isSubnormal_of_isComponentOf hD).subgroupOf
    (isQuasisimple_of_gw hD.2.2) hXC hXs hXsol x hx d hd).symm

omit [Finite Q] in
theorem isSubnormal_of_le_compCentralizer {t : Q} {X : Subgroup Q}
    (hX : X ≤ compCentralizer Q) (hNt : compCentralizer Q ≤ centralizer {t})
    (hXs : (X.subgroupOf (centralizer {t})).IsSubnormal) : X.IsSubnormal := by
  have h1 : (X.subgroupOf (compCentralizer Q)).IsSubnormal :=
    isSubnormal_subgroupOf_mono hNt hXs
  have : (compCentralizer Q).Normal := compCentralizer_normal
  have h2 : ((compCentralizer Q).subgroupOf ⊤).IsSubnormal :=
    (Subgroup.Normal.subgroupOf inferInstance ⊤).isSubnormal
  have h3 := CFSG.GroupTheory.isSubnormal_subgroupOf_trans hX le_top h1 h2
  have h4 := h3.map (f := (⊤ : Subgroup Q).subtype) (fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
  rwa [subgroupOf_map_subtype, inf_top_eq] at h4

omit [Finite Q] in
theorem compCentralizer_le_centralizer {t : Q} {D₀ : Subgroup Q}
    (hD₀ : GorensteinWalter.IsComponentOf D₀ ⊤) (htD₀ : t ∈ D₀) :
    compCentralizer Q ≤ centralizer {t} := fun _ hx =>
  mem_centralizer_singleton_iff.mpr ((mem_compCentralizer.mp hx D₀ hD₀ t htD₀)).symm

omit [Finite Q] in
theorem commutator_le_of_le_normalizer {D X : Subgroup Q} (hXN : X ≤ normalizer (D : Set Q)) :
    ⁅D, X⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro d hd x hx
  have h1 : x * d⁻¹ * x⁻¹ ∈ D := (mem_normalizer_iff.mp (hXN hx) _).mp (inv_mem hd)
  rw [commutatorElement_def, show d * x * d⁻¹ * x⁻¹ = d * (x * d⁻¹ * x⁻¹) by group]
  exact mul_mem hd h1

omit [Finite Q] in
theorem commutator_normal_subgroupOf {D X : Subgroup Q} :
    ((⁅D, X⁆).subgroupOf D).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have key : ⁅D, X⁆ ≤ (⁅D, X⁆).comap (MulAut.conj (g : Q)).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    rw [mem_comap]
    have h1 : (MulAut.conj (g : Q)).toMonoidHom ⁅a, x⁆ = ⁅(g : Q) * a, x⁆ * ⁅(g : Q), x⁆⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [h1]
    exact mul_mem (commutator_mem_commutator (mul_mem g.2 ha) hx)
      (inv_mem (commutator_mem_commutator g.2 hx))
  have h2 := key hn
  rw [mem_comap] at h2
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using h2

omit [Finite Q] in
theorem commute_of_commutator_mem_center {L : Subgroup Q} (hLp : Group.IsPerfect ↥L) {x : Q}
    (hxN : x ∈ normalizer (L : Set Q))
    (hx : ∀ l ∈ L, ∀ m ∈ L, (l * x * l⁻¹ * x⁻¹) * m = m * (l * x * l⁻¹ * x⁻¹)) :
    ∀ l ∈ L, l * x = x * l := by
  have hmem : ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ L := by
    intro l hl
    have h1 : x * l⁻¹ * x⁻¹ ∈ L := (mem_normalizer_iff.mp hxN _).mp (inv_mem hl)
    have h2 : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rw [h2]
    exact mul_mem hl h1
  let φ : ↥L →* ↥(center ↥L) :=
    { toFun := fun l => ⟨⟨l * x * (l : Q)⁻¹ * x⁻¹, hmem l l.2⟩, mem_center_iff.mpr fun m =>
        Subtype.ext (hx l l.2 m m.2).symm⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        have hc := hx b b.2 _ (hmem a a.2)
        have hc2 := hx b b.2 a a.2
        simp only [Subgroup.coe_mul]
        calc (a : Q) * b * x * ((a : Q) * b)⁻¹ * x⁻¹
            = (a : Q) * ((b * x * (b : Q)⁻¹ * x⁻¹) * (x * (a : Q)⁻¹ * x⁻¹)) := by group
          _ = (b * x * (b : Q)⁻¹ * x⁻¹) * (a : Q) * (x * (a : Q)⁻¹ * x⁻¹) := by
            rw [← mul_assoc, ← hc2]
          _ = (b * x * (b : Q)⁻¹ * x⁻¹) * ((a : Q) * x * (a : Q)⁻¹ * x⁻¹) := by group
          _ = ((a : Q) * x * (a : Q)⁻¹ * x⁻¹) * (b * x * (b : Q)⁻¹ * x⁻¹) := hc }
  have hker : φ.ker = ⊤ := by
    have h1 : commutator ↥L ≤ φ.ker := Abelianization.commutator_subset_ker φ
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact top_unique h1
  intro l hl
  have h1 : φ ⟨l, hl⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_top _
  have h2 : l * x * l⁻¹ * x⁻¹ = 1 := congrArg (fun w : ↥(center ↥L) => ((w : ↥L) : Q)) h1
  calc l * x = (l * x * l⁻¹ * x⁻¹) * (x * l) := by group
    _ = x * l := by rw [h2, one_mul]

omit [Finite Q] in
theorem commute_or_le_commutator {D X : Subgroup Q} (hD : GorensteinWalter.IsComponentOf D ⊤)
    (hXN : X ≤ normalizer (D : Set Q)) :
    (∀ x ∈ X, ∀ d ∈ D, d * x = x * d) ∨ D ≤ ⁅D, X⁆ := by
  have hNn : ((⁅D, X⁆).subgroupOf D).Normal := commutator_normal_subgroupOf
  rcases GorensteinWalter.normal_subgroup_le_center_or_eq_top hD.2.2 _ hNn with h | h
  · left
    intro x hx
    have hp : Group.IsPerfect ↥D := Group.isPerfect_def.mpr hD.2.2.2.1
    refine commute_of_commutator_mem_center hp (hXN hx) fun l hl m hm => ?_
    have h1 : l * x * l⁻¹ * x⁻¹ ∈ ⁅D, X⁆ := by
      have h0 := commutator_mem_commutator hl hx
      rwa [commutatorElement_def] at h0
    have h2 : (⟨_, commutator_le_of_le_normalizer hXN h1⟩ : ↥D) ∈ center ↥D :=
      h (by rw [mem_subgroupOf]; exact h1)
    have h3 := mem_center_iff.mp h2 ⟨m, hm⟩
    exact (congrArg Subtype.val h3).symm
  · right
    intro d hd
    have h1 : (⟨d, hd⟩ : ↥D) ∈ (⁅D, X⁆).subgroupOf D := h ▸ mem_top _
    exact h1

end Components

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_mk_eq {w v : G} (hvM : v ∈ centralizer ({w} : Set G)) :
    centralizer ({(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))} :
        Set ↥(centralizer ({w} : Set G))) =
      (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf (centralizer {w}) := by
  ext x
  rw [mem_subgroupOf, mem_inf]
  constructor
  · intro h
    have h' : x * ⟨v, hvM⟩ = ⟨v, hvM⟩ * x := mem_centralizer_singleton_iff.mp h
    exact ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h')⟩
  · rintro ⟨-, h⟩
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))

omit [Finite G] in
theorem isSolvableTwoComponentIn_subgroupOf {J A M : Subgroup G} (hJA : J ≤ A)
    (hAM : A ≤ M) (h : IsSolvableTwoComponentIn J A) :
    IsSolvableTwoComponentIn (J.subgroupOf M) (A.subgroupOf M) := by
  have hJM : J ≤ M := hJA.trans hAM
  let eA : ↥(A.subgroupOf M) ≃* ↥A := subgroupOfEquivOfLe hAM
  let eJ : ↥(J.subgroupOf M) ≃* ↥J := subgroupOfEquivOfLe hJM
  refine ⟨fun x hx => hJA hx, ?_, ?_, ?_⟩
  · have hmap : (J.subgroupOf A).map eA.symm.toMonoidHom =
        (J.subgroupOf M).subgroupOf (A.subgroupOf M) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨eA x, hx, eA.symm_apply_apply x⟩
    rw [← hmap]
    exact h.2.1.map eA.symm.surjective
  · apply map_injective M.subtype_injective
    rw [map_map, map_map]
    have h1 : M.subtype.comp (J.subgroupOf M).subtype = J.subtype.comp eJ.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    have h2 : M.subtype.comp (A.subgroupOf M).subtype = A.subtype.comp eA.toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    rw [h1, h2, ← map_map, ← map_map, pPrimeCore_map_iso 2 eJ, pPrimeCore_map_iso 2 eA]
    exact h.2.2.1
  · rcases h.2.2.2 with h1 | h1
    · obtain ⟨e⟩ := h1
      exact .inl ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans e⟩
    · obtain ⟨e⟩ := h1
      exact .inr ⟨(QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans e⟩

theorem isSolvableTwoComponentIn_hatIn {w v : G} (hv : orderOf v = 2)
    (hvM : v ∈ centralizer ({w} : Set G)) {J : Subgroup G}
    (hJ : IsSolvableTwoComponentIn J (centralizer {w} ⊓ centralizer {v})) :
    IsSolvableTwoComponentIn (hatIn w J)
      (centralizer {(QuotientGroup.mk (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G))) : MBar w)}) := by
  have hv' : orderOf (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hv
  have hJ' : IsSolvableTwoComponentIn (J.subgroupOf (centralizer {w}))
      (centralizer {(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))}) := by
    rw [centralizer_mk_eq hvM]
    exact isSolvableTwoComponentIn_subgroupOf hJ.1 inf_le_left hJ
  exact F3L221.isSolvableTwoComponentIn_map_mk hv' hJ'

theorem isComponentOf_hatIn {w : G} {K : Subgroup G} (hK : IsTwoComponentIn K (centralizer {w})) :
    GorensteinWalter.IsComponentOf (hatIn w K) ⊤ ∧ IsQuasisimple ↥(hatIn w K) := by
  obtain ⟨hcomp, hO, -⟩ := hatIn_spec hK
  have hq : IsQuasisimple ↥(hatIn w K) :=
    LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot) hcomp.2.2
  exact ⟨⟨le_top, hcomp.1.subgroupOf, F3L221.gwIsQuasisimple hq⟩, hq⟩

end F3L226

end CFSG.ComponentClassification.HarrisLit.T1
