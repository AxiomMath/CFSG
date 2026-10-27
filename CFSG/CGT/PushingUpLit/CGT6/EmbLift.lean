module

public import CFSG.CGT.PushingUpLit.CGT6.EmbArrow
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.CGT.PushingUpLit.CGT6.EmbHol

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp
open scoped commutatorElement

section Prelim

variable {V : Type} [CommGroup V] [Finite V]

theorem classX4_iff {Y : Subgroup (MulAut V)} :
    ClassX4 Y ↔ InClassX ↥(yuHol Y) ∨ ∃ n : ℕ, 2 ≤ n ∧ NatOmegaN n Y := by
  unfold ClassX4 NatOmegaN
  constructor
  · rintro (h | ⟨n, hn, h⟩ | ⟨n, hn, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, hn, Or.inr h⟩
    · exact Or.inr ⟨n, hn, Or.inl h⟩
  · rintro (h | ⟨n, hn, h | h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨n, hn, h⟩)
    · exact Or.inr (Or.inl ⟨n, hn, h⟩)

omit [Finite V] in
theorem isPGroup_yuHol_of_isPGroup (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (hY : IsPGroup 2 ↥Y) : IsPGroup 2 ↥(yuHol Y) := by
  have h1 : IsPGroup 2 ↥(⊤ : Subgroup ↥Y) :=
    IsPGroup.of_surjective hY (Subgroup.topEquiv (G := ↥Y)).symm.toMonoidHom
      (Subgroup.topEquiv (G := ↥Y)).symm.surjective
  have h2 := IsPGroup.comap_of_ker_isPGroup h1 (yuProj Y) (isPGroup_ker_yuProj Y hV)
  rw [Subgroup.comap_top] at h2
  exact IsPGroup.of_surjective h2 (Subgroup.topEquiv (G := ↥(yuHol Y))).toMonoidHom
    (Subgroup.topEquiv (G := ↥(yuHol Y))).surjective

theorem ClassX4.not_isPGroup (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)}
    (h : ClassX4 Y) : ¬ IsPGroup 2 ↥Y := by
  rcases classX4_iff.mp h with hc | ⟨n, hn, hΩ⟩
  · exact fun hY => InClassX.not_isPGroup hc (isPGroup_yuHol_of_isPGroup hV hY)
  · exact hΩ.not_isPGroup hn

theorem Lift4.eq_of_natOmega (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n)
    {G X X' : Subgroup (MulAut V)} (hX : NatOmegaN n X) (h : Lift4 G X X') : X' = X := by
  obtain ⟨-, -, -, h4⟩ := h
  have h0 : pCore 2 ↥X = ⊥ := hX.pCore_eq_bot hn
  rcases h4 with ⟨-, harr⟩ | ⟨n₂, hn₂, -, hsplit⟩
  · rcases harr with heq | ⟨-, b, -, -, ⟨ψ⟩, -⟩
    · exact (yuHol_inj heq).symm
    · exact absurd ⟨(yuTop' X hV h0).symm.trans ψ⟩ (hX.not_equiv_alt hn)
  · rcases hsplit with heq | ⟨-, ⟨e⟩, hcard⟩
    · exact heq.symm
    · exact (hX.false_of_sl2 hn hn₂ e hcard).elim

theorem Lift4.conjClosure_eq (hV : ∀ v : V, v ^ 2 = 1) {G Y X : Subgroup (MulAut V)}
    (hY2 : ¬ IsPGroup 2 ↥Y) (h : Lift4 G Y X) : conjClosure Y X = X := by
  obtain ⟨hYX, -, -, h4⟩ := h
  have hle : conjClosure Y X ≤ X := conjClosure_le hYX
  have hn : ((conjClosure Y X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 le_normalizer_conjClosure
  rcases h4 with ⟨hc, -⟩ | ⟨n, hn2, hΩ, hsplit⟩
  · exact eq_of_inClassX_yuHol hle hn hc fun hp => hY2 (hp.to_le le_conjClosure)
  · by_cases hYX' : Y = X
    · exact le_antisymm hle (hYX' ▸ le_conjClosure)
    · rcases hsplit with heq | ⟨hc, hSL, hcard⟩
      · exact absurd heq hYX'
      · exact (embOmega_holds V hV X Y n hn2 hΩ hYX hYX' hSL hcard).1 _ le_conjClosure hle hn

omit [Finite V] in
theorem arrowNat_false_of_sl2 (hV : ∀ v : V, v ^ 2 = 1) {Y X : Subgroup (MulAut V)}
    (hne : Y ≠ X) (hperf : ⁅Y, Y⁆ = Y) (hY2 : ¬ IsPGroup 2 ↥Y) {k : ℕ} (hk : 2 ≤ k)
    (e : ↥X ≃* SLq k) (harr : ArrowNat (yuHol Y) (yuHol X)) : False := by
  classical
  have h0 : pCore 2 ↥X = ⊥ := pCore_eq_bot_of_equiv e (pCore_sl2_eq_bot hk)
  rcases harr with heq | ⟨a, b, φ, F, -, -, -, -, hYX, himg⟩
  · exact hne (yuHol_inj heq)
  have hYX' : Y ≤ X := fun α hα => (hYX (show (⟨1, α⟩ : Hol V) ∈ yuHol Y from ⟨one_mem _, hα⟩)).2
  let ψ : ↥X ≃* alternatingGroup (Fin (2 * a + 1)) := (yuTop' X hV h0).symm.trans φ
  have himg' : (Y.subgroupOf X).map ψ.toMonoidHom = altStabilizer (2 * a + 1) F := by
    rw [← himg, ← yuTop'_image X hV h0 Y, Subgroup.map_map]
    congr 1
    ext x
    simp [ψ]
  have hm5 : 5 ≤ 2 * a + 1 := by
    by_contra hlt
    have hs : Group.IsSolvable (alternatingGroup (Fin (2 * a + 1))) :=
      alternatingGroup.isSolvable (by simp; omega)
    exact sl2_not_isSolvable hk (Group.isSolvable_of_surjective
      (f := (ψ.symm.trans e).toMonoidHom) (ψ.symm.trans e).surjective)
  have ha5 := (alt_sl2_iso hm5 hk (ψ.symm.trans e)).1
  by_cases hF : F = ∅
  · apply hne
    have h1 : (Y.subgroupOf X).map ψ.toMonoidHom = ⊤ := by
      rw [himg', hF]
      ext σ
      simp [mem_altStabilizer']
    refine le_antisymm hYX' fun x hx => ?_
    have hx1 : ψ ⟨x, hx⟩ ∈ (Y.subgroupOf X).map ψ.toMonoidHom := by
      rw [h1]
      trivial
    obtain ⟨y, hy, hyx⟩ := hx1
    have : y = ⟨x, hx⟩ := ψ.injective hyx
    subst this
    exact hy
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have hcard : Nat.card ↥({i}ᶜ : Finset (Fin (2 * a + 1))) ≤ 4 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl,
        Finset.card_singleton, Fintype.card_fin]
      omega
    have hsolvA : Group.IsSolvable (alternatingGroup ↥({i}ᶜ : Finset (Fin (2 * a + 1)))) :=
      alternatingGroup.isSolvable hcard
    have hstab : Group.IsSolvable ↥(altStabilizer (2 * a + 1) {i}) := by
      rw [← range_ofSubtype_compl]
      exact Group.isSolvable_of_surjective
        (f := (alternatingGroup.ofSubtype ({i}ᶜ : Finset (Fin (2 * a + 1)))).rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _)
    have hle : altStabilizer (2 * a + 1) F ≤ altStabilizer (2 * a + 1) {i} := by
      intro σ hσ
      rw [mem_altStabilizer'] at hσ ⊢
      intro j hj
      rw [Finset.mem_singleton] at hj
      exact hj ▸ hσ i hi
    have hsolvF : Group.IsSolvable ↥(altStabilizer (2 * a + 1) F) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    have hsolvY : Group.IsSolvable ↥Y := by
      have h1 : ↥Y ≃* ↥(altStabilizer (2 * a + 1) F) :=
        ((Subgroup.subgroupOfEquivOfLe hYX').symm.trans
          (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective)).trans
          (MulEquiv.subgroupCongr himg')
      exact Group.isSolvable_of_isSolvable_injective (f := h1.toMonoidHom) h1.injective
    have hperfY : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
    have hY1 : Subsingleton ↥Y := by
      by_contra hns
      have : Nontrivial ↥Y := not_subsingleton_iff_nontrivial.mp hns
      exact Group.IsPerfect.not_isSolvable ↥Y hsolvY
    exact hY2 (IsPGroup.of_card (n := 0) (by simp [Nat.card_unique]))

omit [Finite V] in
theorem arrowNat_top_simple_of_perfect (hV : ∀ v : V, v ^ 2 = 1) {Y X : Subgroup (MulAut V)}
    (hY2 : ¬ IsPGroup 2 ↥Y) (hperf : ⁅X, X⁆ = X) (hne : Y ≠ X)
    (harr : ArrowNat (yuHol Y) (yuHol X)) :
    IsSimpleGroup (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) ∧
      ∃ a b : ↥(yuHol X) ⧸ pCore 2 ↥(yuHol X), a * b ≠ b * a := by
  rcases harr with heq | ⟨a, b, φ, F, -, -, -, -, hYX, -⟩
  · exact absurd (yuHol_inj heq) hne
  have hYX' : Y ≤ X := fun α hα => (hYX (show (⟨1, α⟩ : Hol V) ∈ yuHol Y from ⟨one_mem _, hα⟩)).2
  have hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
  have hqperf : Group.IsPerfect (↥X ⧸ pCore 2 ↥X) := inferInstance
  have htopperf : Group.IsPerfect (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) :=
    Group.IsPerfect.ofSurjective (f := (yuTop X hV).symm.toMonoidHom) (yuTop X hV).symm.surjective
  have hAperf : Group.IsPerfect (alternatingGroup (Fin (2 * a + 1))) :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
  have hnt : Nontrivial (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) := by
    by_contra hnt
    have hsub : Subsingleton (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) :=
      not_nontrivial_iff_subsingleton.mp hnt
    apply hY2
    have htop : pCore 2 ↥(yuHol X) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : (x : ↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp this
    have h1 : IsPGroup 2 ↥(yuHol X) := by
      have := pCore_isPGroup (p := 2) (G := ↥(yuHol X))
      rw [htop] at this
      exact IsPGroup.of_surjective this (Subgroup.topEquiv (G := ↥(yuHol X))).toMonoidHom
        (Subgroup.topEquiv (G := ↥(yuHol X))).surjective
    have h2 : IsPGroup 2 ↥(yuHol Y) := (h1.of_injective (Subgroup.inclusion hYX)
      (Subgroup.inclusion_injective hYX))
    intro y
    obtain ⟨k, hk⟩ := h2 ⟨⟨1, (y : MulAut V)⟩, one_mem _, y.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h3 : SemidirectProduct.rightHom
        ((⟨⟨1, (y : MulAut V)⟩, one_mem _, y.2⟩ : ↥(yuHol Y)) ^ 2 ^ k : ↥(yuHol Y)).1 = 1 := by
      rw [hk]
      rfl
    rw [Subgroup.coe_pow, map_pow] at h3
    exact h3
  have hm5 : 5 ≤ 2 * a + 1 := by
    by_contra hlt
    have hs : Group.IsSolvable (alternatingGroup (Fin (2 * a + 1))) :=
      alternatingGroup.isSolvable (by simp; omega)
    have : Nontrivial (alternatingGroup (Fin (2 * a + 1))) := φ.symm.toEquiv.nontrivial
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin (2 * a + 1))) hs
  have hsimpleA : IsSimpleGroup (alternatingGroup (Fin (2 * a + 1))) :=
    alternatingGroup.isSimpleGroup (by simpa using hm5)
  refine ⟨φ.isSimpleGroup, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) := ⟨⟨fun x y => hcomm x y⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) this

theorem Lift4.trans (hV : ∀ v : V, v ^ 2 = 1) {G H Y X₁ X' : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hY : ClassX4 Y) (h1 : Lift4 H Y X₁) (_hHG : H ≤ G)
    (h2 : Lift4 G X₁ X') : Lift4 G Y X' := by
  have hY2 : ¬ IsPGroup 2 ↥Y := hY.not_isPGroup hV
  obtain ⟨hYX₁, hX₁H, hs1, hr1⟩ := h1
  obtain ⟨hX₁X', hX'G, hsub, hr2⟩ := h2
  refine ⟨hYX₁.trans hX₁X', hX'G, hsub, ?_⟩
  by_cases hXX : X₁ = X'
  · subst hXX
    exact hr1
  by_cases hYX : Y = X₁
  · subst hYX
    exact hr2
  rcases hr1 with ⟨hc1, harr1⟩ | ⟨n₁, hn₁, hnat1, -⟩
  ·
    have hYc : InClassX ↥(yuHol Y) := by
      rcases classX4_iff.mp hY with h | ⟨n, hn, hΩ⟩
      · exact h
      · exact absurd (Lift4.eq_of_natOmega hV hn hΩ
          ⟨hYX₁, hX₁H, hs1, Or.inl ⟨hc1, harr1⟩⟩).symm hYX
    rcases hr2 with ⟨hc2, harr2⟩ | ⟨n₂, hn₂, -, hx2⟩
    · exact Or.inl ⟨hc2, ArrowNat.trans_of_inClassX hYc hc1 harr1 harr2⟩
    · rcases hx2 with heq | ⟨-, ⟨e⟩, -⟩
      · exact absurd heq hXX
      · exact (arrowNat_false_of_sl2 hV hYX hperf hY2 hn₂ e harr1).elim
  · exact absurd (Lift4.eq_of_natOmega hV hn₁ hnat1 ⟨hX₁X', hX'G, hsub, hr2⟩).symm hXX

theorem Lift5.trans (hV : ∀ v : V, v ^ 2 = 1) (hM6 : Omega4OrderThree)
    {G H Y X₁ X' : Subgroup (MulAut V)} (h3 : Nat.card ↥Y = 3) (h4 : Nat.card ↥(commV Y) = 4)
    (hX₁ : Y = X₁ ∨ ⁅X₁, X₁⁆ = X₁) (h1 : Lift5 H Y X₁) (_hHG : H ≤ G) (h2 : Lift4 G X₁ X') :
    Lift5 G Y X' := by
  have hY2 : ¬ IsPGroup 2 ↥Y := by
    intro hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    rw [h3] at hk
    have h2k : 2 ∣ 3 := by
      rcases k with _ | k
      · simp at hk
      · rw [pow_succ] at hk
        exact ⟨2 ^ k, by omega⟩
    omega
  obtain ⟨hYX₁, hX₁H, -, hc1, harr1⟩ := h1
  obtain ⟨hX₁X', hX'G, hsub, hr2⟩ := h2
  refine ⟨hYX₁.trans hX₁X', hX'G, hsub, ?_⟩
  by_cases hXX : X₁ = X'
  · subst hXX
    exact ⟨hc1, harr1⟩
  rcases hr2 with ⟨hc2, harr2⟩ | ⟨n₂, hn₂, hnat2, hx2⟩
  · refine ⟨hc2, ?_⟩
    by_cases hYX : Y = X₁
    · subst hYX
      exact harr2
    · have hperf : ⁅X₁, X₁⁆ = X₁ := hX₁.resolve_left hYX
      exact ArrowNat.trans (fun _ _ => arrowNat_top_simple_of_perfect hV hY2 hperf hYX harr1)
        harr1 harr2
  · exfalso
    rcases hx2 with heq | -
    · exact hXX heq
    · have := hM6 V hV n₂ hn₂ X' Y hnat2 (hYX₁.trans hX₁X') h3
      omega

theorem Lift4.classX4 {G Y X : Subgroup (MulAut V)} (h : Lift4 G Y X) : ClassX4 X := by
  obtain ⟨-, -, -, h4⟩ := h
  rcases h4 with ⟨hc, -⟩ | ⟨n, hn, hΩ, -⟩
  · exact classX4_iff.mpr (Or.inl hc)
  · exact classX4_iff.mpr (Or.inr ⟨n, hn, hΩ⟩)

omit [Finite V] in
theorem commutator_eq_of_yuHol {X : Subgroup (MulAut V)}
    (h : ⁅yuHol X, yuHol X⁆ = yuHol X) : ⁅X, X⁆ = X := by
  have hmap : (yuHol X).map (SemidirectProduct.rightHom : Hol V →* MulAut V) = X := by
    ext α
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hα
      exact ⟨⟨1, α⟩, ⟨one_mem _, hα⟩, rfl⟩
  calc ⁅X, X⁆ = ⁅(yuHol X).map (SemidirectProduct.rightHom : Hol V →* MulAut V),
        (yuHol X).map (SemidirectProduct.rightHom : Hol V →* MulAut V)⁆ := by rw [hmap]
    _ = (⁅yuHol X, yuHol X⁆).map (SemidirectProduct.rightHom : Hol V →* MulAut V) :=
        (Subgroup.map_commutator _ _ _).symm
    _ = X := by rw [h, hmap]

theorem Lift4.commutator_eq_self (hV : ∀ v : V, v ^ 2 = 1) {G Y X : Subgroup (MulAut V)}
    (hperf : ⁅Y, Y⁆ = Y) (hY : ClassX4 Y) (h : Lift4 G Y X) : ⁅X, X⁆ = X := by
  by_cases hYX : Y = X
  · exact hYX ▸ hperf
  have h' := h
  obtain ⟨hYX', -, -, h4⟩ := h
  rcases h4 with ⟨hc, harr⟩ | ⟨n, hn, hΩ, -⟩
  · have hYc : InClassX ↥(yuHol Y) := by
      rcases classX4_iff.mp hY with hY1 | ⟨n, hn, hΩ⟩
      · exact hY1
      · exact absurd (Lift4.eq_of_natOmega hV hn hΩ h').symm hYX
    obtain ⟨-, hnab⟩ := arrow_top_simple hYc hc (yuHol_mono hYX') (fun hh => hYX (yuHol_inj hh))
      harr.arrow
    rcases hc.1.quotient_type with hq | hp
    · exact commutator_eq_of_yuHol (inClassX_commutator_eq_self hc hq)
    · exfalso
      have : Fact (Nat.card (↥(yuHol X) ⧸ pCore 2 ↥(yuHol X))).Prime := ⟨hp⟩
      have hcyc := isCyclic_of_prime_card (α := ↥(yuHol X) ⧸ pCore 2 ↥(yuHol X)) rfl
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (mul_comm' x y)
  · exact NatOmegaN.commutator_eq_self hn hΩ

end Prelim

end CFSG.CGT.PushingUpLit.CGT6
