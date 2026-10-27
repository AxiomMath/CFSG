module

public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionQuotient

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.RankOneRecog

@[expose] def InvolutionCentralizerComponent (X : Type*) [Group X] : Prop :=
  ∀ t : X, t ≠ 1 → t * t = 1 → ∃ A : Subgroup X, A ≠ ⊥ ∧ ⁅A, A⁆ = A ∧
    (∀ a ∈ A, a * t = t * a) ∧ (∀ c : X, c * t = t * c → ∀ a ∈ A, c⁻¹ * a * c ∈ A) ∧
    (∀ M : Subgroup X, M ≤ A → (∀ a ∈ A, ∀ m ∈ M, a⁻¹ * m * a ∈ M) → IsPGroup 2 M → M = ⊥)

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem InvolutionCentralizerComponent.of_mulEquiv (e : X ≃* Y)
    (h : InvolutionCentralizerComponent Y) : InvolutionCentralizerComponent X := by
  intro t ht1 ht2
  obtain ⟨A, hA1, hAp, hAc, hAn, hA2⟩ := h (e t) (fun h => ht1 (e.injective (by simpa using h)))
    (by rw [← map_mul, ht2, map_one])
  have hmemA : ∀ a ∈ A, e.symm a ∈ A.map e.symm.toMonoidHom := fun a ha =>
    Subgroup.mem_map_of_mem e.symm.toMonoidHom ha
  refine ⟨A.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hA1 ((Subgroup.map_eq_bot_iff_of_injective (f := e.symm.toMonoidHom) _
      e.symm.injective).mp hbot)
  · rw [← Subgroup.map_commutator, hAp]
  · rintro _ ⟨a, ha, rfl⟩
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
    exact hAc a ha
  · rintro c hc _ ⟨a, ha, rfl⟩
    have hc' : e c * e t = e t * e c := by rw [← map_mul, ← map_mul, hc]
    have := hAn (e c) hc' a ha
    refine ⟨(e c)⁻¹ * a * e c, this, ?_⟩
    simp
  · intro M hMA hMn hMp
    have hM := hA2 (M.map e.toMonoidHom) (by
        rintro _ ⟨m, hm, rfl⟩
        obtain ⟨a, ha, hma⟩ := hMA hm
        have : e m = a := by rw [← hma]; simp
        show e m ∈ A
        rw [this]
        exact ha)
      (by
        rintro a ha _ ⟨m, hm, rfl⟩
        have ha' : e.symm a ∈ A.map e.symm.toMonoidHom := hmemA a ha
        refine ⟨(e.symm a)⁻¹ * m * e.symm a, hMn _ ha' m hm, ?_⟩
        simp)
      (hMp.map e.toMonoidHom)
    exact (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp hM

end Transport

section Core

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem false_of_charTwo_component (Z : Subgroup Λ) [Z.Normal] (hZ : Z ≤ Subgroup.center Λ)
    (x : Λ) (hchar : CharTwo (Subgroup.centralizer ({x} : Set Λ)))
    (A : Subgroup (Λ ⧸ Z)) (hA1 : A ≠ ⊥) (hAperf : ⁅A, A⁆ = A)
    (hAc : ∀ a ∈ A, a * (x : Λ ⧸ Z) = (x : Λ ⧸ Z) * a)
    (hAn : ∀ c : Λ ⧸ Z, c * (x : Λ ⧸ Z) = (x : Λ ⧸ Z) * c → ∀ a ∈ A, c⁻¹ * a * c ∈ A)
    (hA2 : ∀ M : Subgroup (Λ ⧸ Z), M ≤ A →
      (∀ a ∈ A, ∀ m ∈ M, a⁻¹ * m * a ∈ M) → IsPGroup 2 M → M = ⊥) : False := by
  obtain ⟨π, hπ⟩ : ∃ π : Λ →* Λ ⧸ Z, π = QuotientGroup.mk' Z := ⟨_, rfl⟩
  have hπapp : ∀ g : Λ, π g = (g : Λ ⧸ Z) := fun g => by rw [hπ]; rfl
  have hπsurj : Function.Surjective π := by rw [hπ]; exact QuotientGroup.mk'_surjective Z
  have hπker : ∀ g : Λ, π g = 1 ↔ g ∈ Z := fun g => by rw [hπapp]; exact QuotientGroup.eq_one_iff g
  obtain ⟨At, hAtdef⟩ : ∃ At : Subgroup Λ, At = A.comap π := ⟨_, rfl⟩
  have hAt_mem : ∀ a : Λ, a ∈ At ↔ π a ∈ A := fun a => by rw [hAtdef]; rfl
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup Λ, E = ⁅At, At⁆ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup Λ, D = Subgroup.centralizer ({x} : Set Λ) := ⟨_, rfl⟩
  have hπE : E.map π = A := by
    rw [hEdef, Subgroup.map_commutator, hAtdef,
      Subgroup.map_comap_eq_self_of_surjective hπsurj]
    exact hAperf
  have hAt : ∀ a ∈ At, a⁻¹ * x⁻¹ * a * x ∈ Z := by
    intro a ha
    have h : π a * π x = π x * π a := by rw [hπapp x]; exact hAc _ ((hAt_mem a).mp ha)
    rw [← hπker]
    simp only [map_mul, map_inv]
    calc (π a)⁻¹ * (π x)⁻¹ * π a * π x = (π x * π a)⁻¹ * (π a * π x) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  have hED : E ≤ D := by
    rw [hEdef, hDdef, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hs := hAt a ha
    have hr := hAt b hb
    have hsc : ∀ g : Λ, g * (a⁻¹ * x⁻¹ * a * x) = (a⁻¹ * x⁻¹ * a * x) * g :=
      Subgroup.mem_center_iff.mp (hZ hs)
    have hrc : ∀ g : Λ, g * (b⁻¹ * x⁻¹ * b * x) = (b⁻¹ * x⁻¹ * b * x) * g :=
      Subgroup.mem_center_iff.mp (hZ hr)
    set s := a⁻¹ * x⁻¹ * a * x with hsdef
    set r := b⁻¹ * x⁻¹ * b * x with hrdef
    have hxa : x⁻¹ * a * x = a * s := by rw [hsdef]; group
    have hxb : x⁻¹ * b * x = b * r := by rw [hrdef]; group
    have key : x⁻¹ * (a * b * a⁻¹ * b⁻¹) * x = a * b * a⁻¹ * b⁻¹ := by
      have e : x⁻¹ * (a * b * a⁻¹ * b⁻¹) * x =
          (x⁻¹ * a * x) * (x⁻¹ * b * x) * (x⁻¹ * a * x)⁻¹ * (x⁻¹ * b * x)⁻¹ := by group
      rw [e, hxa, hxb]
      calc a * s * (b * r) * (a * s)⁻¹ * (b * r)⁻¹
          = a * (s * b) * r * (s⁻¹ * a⁻¹) * (r⁻¹ * b⁻¹) := by group
        _ = a * (b * s) * r * (s⁻¹ * a⁻¹) * (r⁻¹ * b⁻¹) := by rw [← hsc b]
        _ = a * b * (s * r * s⁻¹) * a⁻¹ * (r⁻¹ * b⁻¹) := by group
        _ = a * b * r * a⁻¹ * (r⁻¹ * b⁻¹) := by
            rw [show s * r * s⁻¹ = r by rw [hrc s]; group]
        _ = a * b * (a⁻¹ * r) * (r⁻¹ * b⁻¹) := by rw [hrc a⁻¹]; group
        _ = a * b * a⁻¹ * b⁻¹ := by group
    calc a * b * a⁻¹ * b⁻¹ * x = x * (x⁻¹ * (a * b * a⁻¹ * b⁻¹) * x) := by group
      _ = x * (a * b * a⁻¹ * b⁻¹) := by rw [key]
  have hEn : (E.subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Λ) ∈ E := hn
    have hg : (g : Λ) * x = x * (g : Λ) := by
      have h1 : (g : Λ) ∈ Subgroup.centralizer ({x} : Set Λ) := by rw [← hDdef]; exact g.2
      exact Subgroup.mem_centralizer_singleton_iff.mp h1
    have hgAt : ∀ a ∈ At, (g : Λ) * a * (g : Λ)⁻¹ ∈ At := by
      intro a ha
      have hc : (π g)⁻¹ * π x = π x * (π g)⁻¹ := by
        have h : π g * π x = π x * π g := by rw [← map_mul, ← map_mul, hg]
        calc (π g)⁻¹ * π x = (π g)⁻¹ * (π x * π g) * (π g)⁻¹ := by group
          _ = (π g)⁻¹ * (π g * π x) * (π g)⁻¹ := by rw [h]
          _ = π x * (π g)⁻¹ := by group
      have hc' : (π g)⁻¹ * (x : Λ ⧸ Z) = (x : Λ ⧸ Z) * (π g)⁻¹ := by
        rw [← hπapp x]; exact hc
      have := hAn _ hc' (π a) ((hAt_mem a).mp ha)
      rw [hAt_mem, map_mul, map_mul, map_inv]
      simpa using this
    have hmap : E.map (MulAut.conj (g : Λ)).toMonoidHom ≤ E := by
      rw [hEdef, Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_ <;>
      · rintro _ ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply] using hgAt a ha
    show (g : Λ) * (n : Λ) * (g : Λ)⁻¹ ∈ E
    exact hmap ⟨n, hn', by simp [MulAut.conj_apply]⟩
  have hchar' : CharTwo D := by rw [hDdef]; exact hchar
  have hE : CharTwo E := CharTwo.of_normal hchar' hED hEn
  have hcore : pCoreOf 2 E ≤ Z := by
    rintro g ⟨g', hg', rfl⟩
    obtain ⟨ψ, hψ⟩ : ∃ ψ : E →* Λ ⧸ Z, ψ = π.comp E.subtype := ⟨_, rfl⟩
    have hψapp : ∀ e : E, ψ e = π (e : Λ) := fun e => by rw [hψ]; rfl
    have hker : CFSG.Open.pCore 2 E ≤ ψ.ker := by
      rw [CFSG.pCore_eq_iSup]
      refine iSup_le fun N => ?_
      refine iSup_le fun hN => ?_
      refine iSup_le fun hP => ?_
      intro n hn
      have hMA : N.map ψ ≤ A := by
        rintro _ ⟨m, hm, rfl⟩
        rw [← hπE, hψapp]
        exact ⟨(m : Λ), m.2, rfl⟩
      have hMn : ∀ a ∈ A, ∀ m ∈ N.map ψ, a⁻¹ * m * a ∈ N.map ψ := by
        intro a ha m hm
        rw [← hπE] at ha
        obtain ⟨e, he, rfl⟩ := ha
        obtain ⟨m', hm', rfl⟩ := hm
        refine ⟨(⟨e, he⟩ : E)⁻¹ * m' * ⟨e, he⟩, hN.conj_mem' m' hm' ⟨e, he⟩, ?_⟩
        rw [map_mul, map_mul, map_inv, hψapp, hψapp]
      have hbot := hA2 (N.map ψ) hMA hMn (hP.map ψ)
      have : ψ n ∈ N.map ψ := Subgroup.mem_map_of_mem ψ hn
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have h1 : ψ g' = 1 := hker hg'
    rw [hψapp] at h1
    exact (hπker _).mp h1
  have hEZ : E ≤ Z := by
    intro g hg
    have hc : g ∈ E ⊓ Subgroup.centralizer (pCoreOf 2 E : Set Λ) := by
      refine ⟨hg, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      exact (Subgroup.mem_center_iff.mp (hZ (hcore hh)) g).symm
    exact hcore (hE hc)
  apply hA1
  rw [← hπE, eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot]
  exact (hπker g).mpr (hEZ hg)

end Core

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_inner_of_autInner {L : Subgroup G} (hperf : Group.IsPerfect L)
    (hA : ∀ β : (L ⧸ Subgroup.center L) ≃* (L ⧸ Subgroup.center L),
      ∃ x : L ⧸ Subgroup.center L, ∀ y, β y = x⁻¹ * y * x)
    {w : G} (hwN : w ∈ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ L, ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x := by
  have := hperf
  let c : L ≃* L := conjAutOfNormalizer L hwN
  have hcc : (Subgroup.center L).map c.toMonoidHom = Subgroup.center L := Subgroup.map_center_eq c
  let β : L ⧸ Subgroup.center L ≃* L ⧸ Subgroup.center L :=
    QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) c hcc
  have hβ : ∀ y : L, β (y : L ⧸ Subgroup.center L) = ((c y : L) : L ⧸ Subgroup.center L) :=
    fun y => rfl
  obtain ⟨xb, hxb⟩ := hA β
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
  have hcen : ∀ y : L, (x⁻¹ * y * x)⁻¹ * c y ∈ Subgroup.center L := by
    intro y
    have h1 := hxb (y : L ⧸ Subgroup.center L)
    rw [hβ] at h1
    rw [← QuotientGroup.eq]
    rw [h1]
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hc := eq_conj_of_central_displacement c x hcen
  exact ⟨(x : G), x.2, fun y hy => congrArg (fun z : L => (z : G)) (hc ⟨y, hy⟩)⟩

omit [Finite G] in
theorem charTwo_centralizer_subtype {L : Subgroup G} {w x : G} (hxL : x ∈ L)
    (hact : ∀ y ∈ L, w⁻¹ * y * w = x⁻¹ * y * x)
    (hchar : CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G))) :
    CharTwo (Subgroup.centralizer ({(⟨x, hxL⟩ : L)} : Set L)) := by
  have hD : L ⊓ Subgroup.centralizer ({w} : Set G) =
      (Subgroup.centralizer ({(⟨x, hxL⟩ : L)} : Set L)).map L.subtype := by
    ext g
    constructor
    · rintro ⟨hgL, hgw⟩
      refine ⟨⟨g, hgL⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply Subtype.ext
      have hgw' : g * w = w * g := Subgroup.mem_centralizer_singleton_iff.mp hgw
      have h1 : w⁻¹ * g * w = g := by
        calc w⁻¹ * g * w = w⁻¹ * (g * w) := by group
          _ = w⁻¹ * (w * g) := by rw [hgw']
          _ = g := by group
      have h2 := hact g hgL
      rw [h1] at h2
      change g * x = x * g
      calc g * x = x * (x⁻¹ * g * x) := by group
        _ = x * g := by rw [← h2]
    · rintro ⟨g', hg', rfl⟩
      refine ⟨g'.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hg'x : (g' : G) * x = x * (g' : G) :=
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg')
      have h2 := hact g' g'.2
      have h3 : x⁻¹ * (g' : G) * x = g' := by
        calc x⁻¹ * (g' : G) * x = x⁻¹ * ((g' : G) * x) := by group
          _ = x⁻¹ * (x * g') := by rw [hg'x]
          _ = g' := by group
      rw [h3] at h2
      change (g' : G) * w = w * g'
      calc (g' : G) * w = w * (w⁻¹ * g' * w) := by group
        _ = w * g' := by rw [h2]
  rw [hD] at hchar
  have h1 := charTwo_iff_internal.mp hchar
  exact charTwo_iff_internal.mpr
    (CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
      ((Subgroup.centralizer ({(⟨x, hxL⟩ : L)} : Set L)).equivMapOfInjective L.subtype
        L.subtype_injective).symm h1)

theorem false_of_charTwo_inner {U L : Subgroup G} (hU : IsElemAbelian 2 U)
    (hperf : Group.IsPerfect L) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hA : ∀ β : (L ⧸ Subgroup.center L) ≃* (L ⧸ Subgroup.center L),
      ∃ x : L ⧸ Subgroup.center L, ∀ y, β y = x⁻¹ * y * x)
    (hcomp : InvolutionCentralizerComponent (L ⧸ Subgroup.center L))
    {w : G} (hwU : w ∈ U) (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G))
    (hchar : CharTwo (L ⊓ Subgroup.centralizer ({w} : Set G))) : False := by
  obtain ⟨x, hxL, hact⟩ := exists_inner_of_autInner hperf hA (hUL hwU)
  have hw2 : w * w = 1 := by rw [← sq]; exact hU.2 w hwU
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  let x' : L := ⟨x, hxL⟩
  have hx2 : x' * x' ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := hact y y.2
    have hy' : x⁻¹ * (y : G) * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hxL) y.2) hxL
    have h2 := hact _ hy'
    have key : x⁻¹ * (x⁻¹ * (y : G) * x) * x = y := by
      calc x⁻¹ * (x⁻¹ * (y : G) * x) * x = w⁻¹ * (x⁻¹ * y * x) * w := h2.symm
        _ = w⁻¹ * (w⁻¹ * y * w) * w := by rw [h1]
        _ = w * (w * y * w) * w := by rw [hw']
        _ = (w * w) * y * (w * w) := by group
        _ = y := by rw [hw2]; group
    change (y : G) * (x * x) = x * x * (y : G)
    calc (y : G) * (x * x) = (x * x) * ((x * x)⁻¹ * y * (x * x)) := by group
      _ = (x * x) * y := by
          congr 1
          calc (x * x)⁻¹ * (y : G) * (x * x) = x⁻¹ * (x⁻¹ * (y : G) * x) * x := by group
            _ = y := key
  have ht2 : (QuotientGroup.mk x' : L ⧸ Subgroup.center L) * QuotientGroup.mk x' = 1 := by
    rw [← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hx2
  have ht1 : (QuotientGroup.mk x' : L ⧸ Subgroup.center L) ≠ 1 := by
    intro h
    have hxc : x' ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).mp h
    apply hnc
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxy : (y : G) * x = x * y :=
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxc) ⟨y, hy⟩)
    have h1 := hact y hy
    have h3 : x⁻¹ * y * x = y := by
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
        _ = x⁻¹ * (x * y) := by rw [hxy]
        _ = y := by group
    rw [h3] at h1
    calc y * w = w * (w⁻¹ * y * w) := by group
      _ = w * y := by rw [h1]
  obtain ⟨A, hA1, hAp, hAc, hAn, hA2⟩ := hcomp _ ht1 ht2
  exact false_of_charTwo_component (Subgroup.center L) le_rfl x' (charTwo_centralizer_subtype hxL
    hact hchar) A hA1 hAp hAc hAn hA2

end Main

end CFSG.QuasithinUnique.K1
