module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Theta
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
public import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderAlt

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open Equiv Equiv.Perm MulAction

variable {X : Type} [Group X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

abbrev SixCtx.img (c : SixCtx T L) (A : Subgroup X) : Subgroup (Perm (Fin 7)) :=
  (A.subgroupOf (nL T L)).map c.θ

theorem SixCtx.mem_img (c : SixCtx T L) {A : Subgroup X} (hA : A ≤ nL T L) {σ : Perm (Fin 7)} :
    σ ∈ c.img A ↔ ∃ (a : X) (ha : a ∈ A), c.θ ⟨a, hA ha⟩ = σ := by
  constructor
  · rintro ⟨⟨a, ha'⟩, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem isElemAbelian_sup_of_commute {A B : Subgroup X} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB h

namespace SixCtx

variable [Finite X] (c : SixCtx T L)

theorem nV_le (hX : GNSetting X T) : nV T L ≤ T :=
  (Subgroup.commutator_le_left _ _).trans
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.gnV_le T hX)

theorem isElemAbelian_nV (hX : GNSetting X T) : IsElemAbelian 2 (nV T L) := by
  have hV := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hle : nV T L ≤ gnV T := Subgroup.commutator_le_left _ _
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hV.2 x (hle hx)⟩
  have h2 := congrArg Subtype.val (hV.1.1.comm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩)
  apply Subtype.ext
  simpa using h2

theorem offIdx_le (hX : GNSetting X T) (hTL : T ≤ nL T L) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) : (altFix 7 (c.img A)).index ≤ Nat.card (c.img A) := by
  classical
  have hV : (gnV T).Normal := Subgroup.normalClosure_normal
  set N := nV T L with hNdef
  have hAL : A ≤ nL T L := hA.1.trans hTL
  have hNT : N ≤ T := nV_le hX
  have hNe := isElemAbelian_nV (L := L) hX
  set A' : Subgroup X := A ⊓ Subgroup.centralizer (N : Set X) with hA'
  have hker : ∀ a (ha : a ∈ A), c.θ ⟨a, hAL ha⟩ = 1 ↔ a ∈ A' := by
    intro a ha
    rw [c.theta_eq_one_iff hV]
    constructor
    · intro h
      refine ⟨ha, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have := h u hu
      calc u * a = a * u * a⁻¹ * a := by rw [this]
        _ = a * u := by group
    · rintro ⟨-, hc⟩ u hu
      have := Subgroup.mem_centralizer_iff.1 hc u hu
      rw [← this]; group
  have hcardE : Nat.card (c.img A) * Nat.card A' = Nat.card A := by
    let f : ↥(A.subgroupOf (nL T L)) →* Perm (Fin 7) := c.θ.comp (A.subgroupOf (nL T L)).subtype
    have hrange : f.range = c.img A := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkerf : Nat.card f.ker = Nat.card A' := by
      refine Nat.card_congr ⟨fun x => ⟨((x : ↥(A.subgroupOf (nL T L))) : X),
          (hker _ (x : ↥(A.subgroupOf (nL T L))).2).1 x.2⟩,
        fun y => ⟨⟨⟨y, hAL y.2.1⟩, y.2.1⟩, (hker _ y.2.1).2 y.2⟩, fun x => rfl, fun y => rfl⟩
    have h1 := f.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, hkerf] at h1
    rw [mul_comm, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv]
  have hNA : ∀ u ∈ N, u ∈ A ↔ ∀ a ∈ A, a * u * a⁻¹ = u := by
    intro u hu
    constructor
    · intro huA a ha
      have := congrArg Subtype.val (hA.2.1.1.1.comm ⟨a, ha⟩ ⟨u, huA⟩)
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    · intro h
      rw [eq_omegaOneOf_centralizer hA]
      refine Subgroup.subset_closure ⟨⟨hNT hu, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩,
        hNe.2 u hu⟩
      have := h a ha
      calc a * u = a * u * a⁻¹ * a := by group
        _ = u * a := by rw [this]
  have hineq : Nat.card N * Nat.card A' ≤ Nat.card A * Nat.card (N ⊓ A : Subgroup X) := by
    have hcomm : ∀ x ∈ N, ∀ y ∈ A', x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 hy.2 x hx
    have hsup := CFSG.RankThree.PartOne.PlaneCommuting.card_sup_mul_card_inf hcomm
    have hinf : N ⊓ A' = N ⊓ A := by
      refine le_antisymm (inf_le_inf_left _ inf_le_left) fun x hx => ⟨hx.1, hx.2, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      exact congrArg Subtype.val (hNe.1.1.comm ⟨u, hu⟩ ⟨x, hx.1⟩)
    have hA'e : IsElemAbelian 2 A' := by
      refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => hA.2.1.2 x hx.1⟩
      have h2 := congrArg Subtype.val (hA.2.1.1.1.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩)
      apply Subtype.ext
      simpa using h2
    have hBe : IsElemAbelian 2 (N ⊔ A') := isElemAbelian_sup_of_commute hNe hA'e hcomm
    have hBT : N ⊔ A' ≤ T := sup_le hNT (inf_le_left.trans hA.1)
    have hle := hA.2.2 _ hBT hBe
    rw [hinf] at hsup
    rw [← hsup]
    exact Nat.mul_le_mul_right _ hle
  have hfix : Nat.card (altFix 7 (c.img A)) = Nat.card (N ⊓ A : Subgroup X) := by
    have hmem : ∀ u : ↥N, Multiplicative.toAdd (c.φ u) ∈ altFix 7 (c.img A) ↔ (u : X) ∈ A := by
      intro u
      rw [mem_altFix_iff, hNA u u.2]
      constructor
      · intro h a ha
        have hv : (a : X) * u * a⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.1 (nL_le_normalizer_nV hV (hAL ha)) u).1 u.2
        have h1 := c.hφe' ⟨a, hAL ha⟩ u ⟨_, hv⟩ rfl
        obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (c.φ u))
        have h2 := h (c.θ ⟨a, hAL ha⟩) ⟨⟨a, hAL ha⟩, ha, rfl⟩ x hx
        rw [← altAct_mk, hx] at h2
        rw [h2] at h1
        exact congrArg Subtype.val (c.hφ.1 (Multiplicative.toAdd.injective h1))
      · intro h σ hσ x hx
        obtain ⟨a, ha, rfl⟩ := (c.mem_img hAL).1 hσ
        rw [← altAct_mk, hx]
        have h1 := c.hφe' ⟨a, hAL ha⟩ u u (h a ha).symm
        exact h1.symm
    let f : ↥(N ⊓ A : Subgroup X) → ↥(altFix 7 (c.img A)) := fun x =>
      ⟨Multiplicative.toAdd (c.φ ⟨x, x.2.1⟩), (hmem ⟨x, x.2.1⟩).2 x.2.2⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => ?_, fun v => ?_⟩
      · have h1 : c.φ ⟨x, x.2.1⟩ = c.φ ⟨y, y.2.1⟩ :=
          Multiplicative.toAdd.injective (congrArg Subtype.val hxy)
        have h2 := congrArg Subtype.val (c.hφ.1 h1)
        exact Subtype.ext h2
      · obtain ⟨u, hu⟩ := c.hφ.2 (Multiplicative.ofAdd (v : altHeart 7))
        have huA : (u : X) ∈ A := (hmem u).1 (by rw [hu]; exact v.2)
        refine ⟨⟨u, u.2, huA⟩, Subtype.ext ?_⟩
        show Multiplicative.toAdd (c.φ ⟨(u : X), u.2⟩) = (v : altHeart 7)
        rw [show (⟨(u : X), u.2⟩ : ↥N) = u from rfl, hu]
        rfl
    have e := Equiv.ofBijective f hf
    exact (Nat.card_congr e).symm
  have hcardH : Nat.card (altHeart 7) = Nat.card N :=
    (Nat.card_congr (Equiv.ofBijective c.φ c.hφ)).symm.trans rfl
  have hidx := (altFix 7 (c.img A)).index_mul_card
  rw [hfix, hcardH] at hidx
  have hpos1 : 0 < Nat.card A' := Nat.card_pos
  have hpos2 : 0 < Nat.card (N ⊓ A : Subgroup X) := Nat.card_pos
  have h3 : (altFix 7 (c.img A)).index * Nat.card (N ⊓ A : Subgroup X) * Nat.card A' ≤
      Nat.card (c.img A) * Nat.card A' * Nat.card (N ⊓ A : Subgroup X) := by
    rw [hidx, hcardE]
    exact hineq
  have h4 : (altFix 7 (c.img A)).index * (Nat.card (N ⊓ A : Subgroup X) * Nat.card A') ≤
      Nat.card (c.img A) * (Nat.card (N ⊓ A : Subgroup X) * Nat.card A') := by
    calc _ = (altFix 7 (c.img A)).index * Nat.card (N ⊓ A : Subgroup X) * Nat.card A' := by ring
      _ ≤ _ := h3
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h4 (Nat.mul_pos hpos2 hpos1)

omit [Finite X] in
theorem img_sq (hTL : T ≤ nL T L) {A : Subgroup X} (hA : IsMaxElemAbelian T A) :
    ∀ σ ∈ c.img A, σ * σ = 1 := by
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := (c.mem_img (hA.1.trans hTL)).1 hσ
  rw [← map_mul, ← map_one c.θ]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
  exact hA.2.1.2 a ha

theorem offenderShape (hX : GNSetting X T) (hTL : T ≤ nL T L) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) : Offender.OffenderShapeConcl (c.img A) :=
  offender_shape_altHeart (Or.inl rfl) _ (c.img_sq hTL hA) (c.offIdx_le hX hTL hA)

theorem exists_fixed_of_isPGroup {E : Subgroup (Perm (Fin 7))} (hE : IsPGroup 2 E) :
    ∃ p, ∀ g ∈ E, g p = p := by
  classical
  have h := hE.card_modEq_card_fixedPoints (α := Fin 7)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hne : (MulAction.fixedPoints E (Fin 7)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have h0 : Nat.card (MulAction.fixedPoints E (Fin 7)) = 0 := by
      rw [hcon]; simp
    rw [h0] at h
    exact absurd h (by decide)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, fun g hg => hp ⟨g, hg⟩⟩

theorem swap_mem_theta (hX : GNSetting X T) (hTL : T ≤ nL T L) {A : Subgroup X}
    (hA : IsMaxElemAbelian T A) {σ : Perm (Fin 7)} (hσ : σ ∈ c.img A) {i : Fin 7}
    (hi : σ i ≠ i) : swap i (σ i) ∈ c.img A := by
  classical
  have hsq := c.img_sq hTL hA
  have hp : IsPGroup 2 (c.img A) := fun g => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
    exact hsq g g.2)⟩
  obtain ⟨p, hp'⟩ := exists_fixed_of_isPGroup hp
  obtain ⟨-, hE⟩ := (c.offenderShape hX hTL hA).1 ⟨p, hp'⟩
  rw [hE]
  intro j
  by_cases hji : j = i
  · subst hji
    rw [swap_apply_left]
    exact ⟨⟨σ, hσ⟩, rfl⟩
  by_cases hjs : j = σ i
  · subst hjs
    rw [swap_apply_right]
    refine ⟨⟨σ, hσ⟩, ?_⟩
    show σ (σ i) = i
    rw [← Perm.mul_apply, hsq σ hσ, one_apply]
  · rw [swap_apply_of_ne_of_ne hji hjs]
    exact mem_orbit_self j

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
