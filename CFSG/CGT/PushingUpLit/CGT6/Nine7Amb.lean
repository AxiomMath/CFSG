module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Glauberman
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoEight
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.AschbacherComponentTypeTheorem5MilestoneDefs

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open CFSG.Open
open CFSG.ComponentClassification
open scoped commutatorElement

section GlaubermanTransport

theorem GlaubermanAt.congr {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y] (e : X ≃* Y)
    (h : GlaubermanAt X) : GlaubermanAt Y := by
  intro hY hnc hev S K hK hfix
  have hX : IsSimpleGroup X := e.isSimpleGroup
  have hnc' : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e.symm a, e.symm b, fun hc => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  have hev' : Even (Nat.card X) := by rwa [Nat.card_congr e.toEquiv]
  let S' : Sylow 2 X := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let f : MulAut Y →* MulAut X := (MulAut.congr e.symm).toMonoidHom
  have hS' : (S' : Subgroup X) = (S : Subgroup Y).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective e.symm.surjective S
  have hperf : Group.IsPerfect ↥(K.map f) := by
    rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hK]
  have hfix' : ∀ α ∈ K.map f, ∀ s ∈ (S' : Subgroup X), α s = s := by
    rintro _ ⟨α, hα, rfl⟩ s hs
    rw [hS'] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    change e.symm (α (e (e.symm s₀))) = e.symm s₀
    rw [e.apply_symm_apply]
    exact congrArg e.symm (hfix α hα s₀ hs₀)
  have hbot := h hX hnc' hev' S' (K.map f) hperf hfix'
  exact (Subgroup.map_eq_bot_iff_of_injective K (MulAut.congr e.symm).injective).1 hbot

theorem glaubermanAt_quotient_congr {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q]
    (e : P ≃* Q) (h : GlaubermanAt (P ⧸ Subgroup.center P)) :
    GlaubermanAt (Q ⧸ Subgroup.center Q) :=
  GlaubermanAt.congr (QuotientGroup.congr (Subgroup.center P) (Subgroup.center Q) e
    (OuterAutomorphisms.center_map_equiv e)) h

variable {G : Type} [Group G] [Finite G]

theorem glaubermanAt_conjugate {A : Subgroup G} (g : G)
    (h : GlaubermanAt (↥A ⧸ Subgroup.center ↥A)) :
    GlaubermanAt (↥(conjugate A g) ⧸ Subgroup.center ↥(conjugate A g)) :=
  glaubermanAt_quotient_congr
    (A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective) h

theorem glaubermanAt_of_mem_ConjCl {A B : Subgroup G} (hB : B ∈ ConjCl A)
    (h : GlaubermanAt (↥A ⧸ Subgroup.center ↥A)) :
    GlaubermanAt (↥B ⧸ Subgroup.center ↥B) := by
  obtain ⟨g, rfl⟩ := hB
  exact glaubermanAt_conjugate g h

theorem glaubermanAt_subgroupOf {L H : Subgroup G} (hLH : L ≤ H)
    (h : GlaubermanAt (↥L ⧸ Subgroup.center ↥L)) :
    GlaubermanAt (↥(L.subgroupOf H) ⧸ Subgroup.center ↥(L.subgroupOf H)) :=
  glaubermanAt_quotient_congr (Subgroup.subgroupOfEquivOfLe hLH).symm h

end GlaubermanTransport

section FourGroup

open CFSG.ComponentClassification.AschbacherKnownGroup (IsFourGroup)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fourGroup_sq_eq_one {U : Subgroup G} (hU : IsFourGroup U) {x : G} (hx : x ∈ U) :
    x ^ 2 = 1 := hU.1.2 x hx

omit [Finite G] in
theorem fourGroup_comm {U : Subgroup G} (hU : IsFourGroup U) {x y : G} (hx : x ∈ U) (hy : y ∈ U) :
    x * y = y * x := by
  have := hU.1.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : U) ⟨y, hy⟩)

omit [Finite G] in
theorem fourGroup_orderOf {U : Subgroup G} (hU : IsFourGroup U) {x : G} (hx : x ∈ U)
    (hne : x ≠ 1) : orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (fourGroup_sq_eq_one hU hx) hne

omit [Finite G] in
theorem fourGroup_exists_ne_one {U : Subgroup G} (hU : IsFourGroup U) : ∃ u ∈ U, u ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).2 hcon
  have := hU.2
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem fourGroup_exists_gen {U : Subgroup G} (hU : IsFourGroup U) {u : G} (hu : u ∈ U)
    (hu1 : u ≠ 1) :
    ∃ v ∈ U, v ≠ 1 ∧ v ≠ u ∧ Subgroup.zpowers u ⊔ Subgroup.zpowers v = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf u = 2 := fourGroup_orderOf hU hu hu1
  have hZU : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.2 hu
  have hcardZ : Nat.card (Subgroup.zpowers u) = 2 := by rw [Nat.card_zpowers, hord]
  have hcardU : Nat.card U = 4 := hU.2
  have hex : ∃ v ∈ U, v ∉ Subgroup.zpowers u := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show U ≤ Subgroup.zpowers u from fun x hx => hcon x hx)
    omega
  obtain ⟨v, hvU, hvZ⟩ := hex
  refine ⟨v, hvU, ?_, ?_, ?_⟩
  · rintro rfl
    exact hvZ (Subgroup.one_mem _)
  · rintro rfl
    exact hvZ (Subgroup.mem_zpowers _)
  · set U₀ : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hU₀def
    have hU₀ : U₀ ≤ U := sup_le hZU (Subgroup.zpowers_le.2 hvU)
    have h1 : 2 ∣ Nat.card U₀ := by
      rw [← hcardZ]; exact Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card U₀ ∣ 4 := by
      rw [← hcardU]; exact Subgroup.card_dvd_of_le hU₀
    have h3 : Nat.card U₀ ≠ 2 := by
      intro h
      have heq : Subgroup.zpowers u = U₀ := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      exact hvZ (heq ▸ (le_sup_right : Subgroup.zpowers v ≤ U₀) (Subgroup.mem_zpowers v))
    have h4 : Nat.card U₀ = 4 := by
      have hle : Nat.card U₀ ≤ 4 := Nat.le_of_dvd (by norm_num) h2
      have hpos : 0 < Nat.card U₀ := Nat.card_pos
      obtain ⟨k, hk⟩ := h1
      omega
    exact Subgroup.eq_of_le_of_card_ge hU₀ (by omega)

theorem fourGroup_exists_three {U : Subgroup G} (hU : IsFourGroup U) :
    ∃ w₁ ∈ U, ∃ w₂ ∈ U, w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₁ ≠ w₂ ∧ w₁ * w₂ ≠ 1 := by
  obtain ⟨u, hu, hu1⟩ := fourGroup_exists_ne_one hU
  obtain ⟨v, hv, hv1, hvu, -⟩ := fourGroup_exists_gen hU hu hu1
  refine ⟨u, hu, v, hv, hu1, hv1, hvu.symm, fun h => hvu ?_⟩
  have hv2 : v * v = 1 := by rw [← pow_two]; exact fourGroup_sq_eq_one hU hv
  have : u = v⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [this, inv_eq_of_mul_eq_one_right hv2]

omit [Finite G] in
theorem isFourGroup_conjugate {U : Subgroup G} (hU : IsFourGroup U) (g : G) :
    IsFourGroup (conjugate U g) :=
  ⟨SectionRank.isElemAbelian_map hU.1 _, by rw [card_conjugate, hU.2]⟩

omit [Finite G] in
theorem isFourGroup_subgroupOf {U H : Subgroup G} (hUH : U ≤ H) (hU : IsFourGroup U) :
    IsFourGroup (U.subgroupOf H) := by
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩, ?_⟩
  · exact fourGroup_comm hU a.2 b.2
  · apply Subtype.ext
    exact fourGroup_sq_eq_one hU hx
  · rw [← hU.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv

theorem exists_fourGroup_of_two_le_pRank {X : Subgroup G} (h : 2 ≤ Open.pRank 2 X) :
    ∃ V : Subgroup G, V ≤ X ∧ IsFourGroup V := by
  obtain ⟨E, hEX, hE, hcard⟩ := SectionRank.exists_pRank (by norm_num : 1 < 2) X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 2 ∣ Nat.card E := by rw [hcard]; exact pow_dvd_pow 2 h
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hEc := hE.1
  refine ⟨V₀.map E.subtype, (Subgroup.map_subtype_le V₀).trans hEX,
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a₀, -, ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b₀, -, hb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← ha, ← hb]
    exact congrArg Subtype.val (mul_comm' a₀ b₀)
  · obtain ⟨x₀, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact hE.2 x₀ x₀.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hV₀]
    norm_num

theorem two_le_pRank_of_fourGroup {V X : Subgroup G} (hVX : V ≤ X) (hV : IsFourGroup V) :
    2 ≤ Open.pRank 2 X :=
  SectionRank.le_pRank (by norm_num) hVX hV.1 (by rw [hV.2]; norm_num)

theorem one_le_pRank_of_involution {X : Subgroup G} {t : G} (ht : t ∈ X) (ht2 : orderOf t = 2) :
    1 ≤ Open.pRank 2 X := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have hcases : ∀ x ∈ Subgroup.zpowers t, x = 1 ∨ x = t := fun x hx =>
    CFSG.ComponentClassification.AschbacherComponentAction.cyclic_involution_cases t htt hx
  refine SectionRank.le_pRank (E := Subgroup.zpowers t) (by norm_num)
    (Subgroup.zpowers_le.2 ht) ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩ ?_
  · apply Subtype.ext
    change (a : G) * b = b * a
    rcases hcases a a.2 with ha | ha <;> rcases hcases b b.2 with hb | hb <;> simp [ha, hb]
  · rcases hcases x hx with rfl | rfl
    · exact one_pow 2
    · rw [pow_two]; exact htt
  · rw [Nat.card_zpowers, ht2]
    norm_num

end FourGroup

section Algebra

variable {G : Type} [Group G]

theorem mul_comm_of_commutator_eq_bot {H N : Subgroup G} (h : ⁅H, N⁆ = ⊥) {x y : G} (hx : x ∈ H)
    (hy : y ∈ N) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hx) y hy).symm

theorem commutator_eq_bot_of_forall_comm {H N : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ N, x * y = y * x) : ⁅H, N⁆ = ⊥ :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (h x hx y hy).symm

theorem mem_sup_iff_of_comm {H N : Subgroup G} (h : ⁅H, N⁆ = ⊥) {x : G} :
    x ∈ H ⊔ N ↔ ∃ a ∈ H, ∃ b ∈ N, a * b = x := by
  have hle : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans
      (Subgroup.centralizer_le_normalizer _)
  have hco := Subgroup.coe_mul_of_left_le_normalizer_right H N hle
  constructor
  · intro hx
    have hx' : x ∈ (↑(H ⊔ N) : Set G) := hx
    rw [hco] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem commutator_self_le (M : Subgroup G) : ⁅M, M⁆ ≤ M :=
  Subgroup.commutator_le.2 fun _ hx _ hy =>
    M.mul_mem (M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)) (M.inv_mem hy)

theorem semisimple_of_clique [Finite G] (S : Set (Subgroup G)) (hne : S.Nonempty)
    (hq : ∀ B ∈ S, QS B) (hc : ∀ B ∈ S, ∀ B' ∈ S, B ≠ B' → ⁅B, B'⁆ = ⊥) :
    aschbacherThm5IsSemisimple (⨆ B ∈ S, B) := by
  classical
  have : Finite S := Subtype.finite
  let e : S ≃ Fin (Nat.card S) := Finite.equivFin S
  refine ⟨Nat.card S, fun l => (e.symm l).1, ?_, ?_, ?_, ?_⟩
  · exact Nat.card_pos_iff.2 ⟨hne.to_subtype, inferInstance⟩
  · intro l
    exact ⟨le_iSup₂_of_le _ (e.symm l).2 le_rfl, hq _ (e.symm l).2⟩
  · intro l m hlm x hx y hy
    exact mul_comm_of_commutator_eq_bot
      (hc _ (e.symm l).2 _ (e.symm m).2 (fun h => hlm (e.symm.injective (Subtype.ext h)))) hx hy
  · apply le_antisymm
    · exact iSup_le fun l => le_iSup₂_of_le _ (e.symm l).2 le_rfl
    · refine iSup₂_le fun B hB => le_iSup_of_le (e ⟨B, hB⟩) ?_
      dsimp only
      rw [Equiv.symm_apply_apply]

theorem centralizes_of_perfect {P Z : Subgroup G} (hP : Group.IsPerfect P)
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) (hPZ : ∀ x ∈ P, ∀ z ∈ Z, x * z = z * x) {t : G}
    (ht : ∀ x ∈ P, t⁻¹ * x⁻¹ * t * x ∈ Z) : P ≤ Subgroup.centralizer ({t} : Set G) := by
  set c : G → G := fun x => t⁻¹ * x⁻¹ * t * x with hc
  have hmul : ∀ x ∈ P, ∀ y ∈ P, c (x * y) = c x * c y := by
    intro x hx y hy
    have hcx : c x ∈ Z := ht x hx
    have hcomm : y⁻¹ * c x * y = c x := by
      have h1 := hPZ y hy (c x) hcx
      calc y⁻¹ * c x * y = y⁻¹ * (c x * y) := by group
        _ = y⁻¹ * (y * c x) := by rw [h1]
        _ = c x := by group
    have hcc : c y * c x = c x * c y := hZ _ (ht y hy) _ hcx
    calc c (x * y) = (t⁻¹ * y⁻¹ * t * y) * (y⁻¹ * (t⁻¹ * x⁻¹ * t * x) * y) := by
          simp only [hc]; group
      _ = c y * (y⁻¹ * c x * y) := rfl
      _ = c y * c x := by rw [hcomm]
      _ = c x * c y := hcc
  let φ : P →* Z :=
    { toFun := fun x => ⟨c x, ht x x.2⟩
      map_one' := Subtype.ext (by simp [hc])
      map_mul' := fun x y => Subtype.ext (hmul x x.2 y y.2) }
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ ≤ Subgroup.centralizer ({t} : Set G) := by
      refine Subgroup.commutator_le.2 fun x hx y hy => ?_
      have h1 : φ ⁅(⟨x, hx⟩ : P), ⟨y, hy⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext (hZ _ (ht x hx) _ (ht y hy))
      have h2 : t⁻¹ * ⁅x, y⁆⁻¹ * t * ⁅x, y⁆ = 1 := congrArg Subtype.val h1
      rw [mem_centralizer_single]
      have h3 : (⁅x, y⁆ * t)⁻¹ * (t * ⁅x, y⁆) = 1 := by
        calc (⁅x, y⁆ * t)⁻¹ * (t * ⁅x, y⁆) = t⁻¹ * ⁅x, y⁆⁻¹ * t * ⁅x, y⁆ := by group
          _ = 1 := h2
      exact (inv_mul_eq_one.1 h3).symm

theorem perfect_le_of_le_mul {P X D Zc : Subgroup G} (hP : Group.IsPerfect P) (hPD : P ≤ D)
    (hZD : Zc ≤ D) (hZc : ∀ z ∈ Zc, ∀ d ∈ D, z * d = d * z)
    (h : ∀ a ∈ P, ∃ x ∈ X, ∃ o ∈ Zc, a = x * o) : P ≤ X := by
  calc P = ⁅P, P⁆ := (Subgroup.isPerfect_iff.mp hP).symm
    _ ≤ X := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      obtain ⟨x, hx, o, ho, rfl⟩ := h a ha
      obtain ⟨y, hy, o', ho', rfl⟩ := h b hb
      have hxD : x ∈ D := by
        have := D.mul_mem (hPD ha) (D.inv_mem (hZD ho))
        simpa using this
      have hyD : y ∈ D := by
        have := D.mul_mem (hPD hb) (D.inv_mem (hZD ho'))
        simpa using this
      have h1 : o * y = y * o := hZc o ho y hyD
      have h2 : o * o' = o' * o := hZc o ho o' (hZD ho')
      have h3 : o' * x⁻¹ = x⁻¹ * o' := hZc o' ho' x⁻¹ (D.inv_mem hxD)
      have key : ⁅x * o, y * o'⁆ = ⁅x, y⁆ := by
        simp only [commutatorElement_def, mul_inv_rev]
        calc x * o * (y * o') * (o⁻¹ * x⁻¹) * (o'⁻¹ * y⁻¹)
            = x * (o * y) * o' * o⁻¹ * x⁻¹ * o'⁻¹ * y⁻¹ := by group
          _ = x * (y * o) * o' * o⁻¹ * x⁻¹ * o'⁻¹ * y⁻¹ := by rw [h1]
          _ = x * y * (o * o' * o⁻¹) * x⁻¹ * o'⁻¹ * y⁻¹ := by group
          _ = x * y * o' * x⁻¹ * o'⁻¹ * y⁻¹ := by rw [h2, mul_inv_cancel_right]
          _ = x * y * (o' * x⁻¹) * o'⁻¹ * y⁻¹ := by group
          _ = x * y * (x⁻¹ * o') * o'⁻¹ * y⁻¹ := by rw [h3]
          _ = x * y * x⁻¹ * y⁻¹ := by group
      rw [key]
      exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)

end Algebra

section Ambient

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AschbacherComponentAction (rightComponent)
open CFSG.ComponentClassification.AschbacherKnownGroup (IsFourGroup)

omit [Finite G] in
theorem rightComponent_eq_conjugate (L : Subgroup G) (g : G) : rightComponent L g = conjugate L g :=
  rfl

omit [Finite G] in
theorem map_subtype_conjugate {H : Subgroup G} (L : Subgroup H) (a : H) :
    (conjugate L a).map H.subtype = conjugate (L.map H.subtype) (a : G) := by
  have hcomp : H.subtype.comp (MulAut.conj a⁻¹).toMonoidHom =
      (MulAut.conj (a : G)⁻¹).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  change (L.map (MulAut.conj a⁻¹).toMonoidHom).map H.subtype =
    (L.map H.subtype).map (MulAut.conj (a : G)⁻¹).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

omit [Finite G] in
theorem isComponentOf_subgroupOf {L H : Subgroup G} (h : IsCompIn L H) :
    IsComponentOf (L.subgroupOf H) ⊤ :=
  (OrdinaryComponentTransport.subgroupOf_iff L H h.1).2 ⟨h.2.1, h.2.2⟩

omit [Finite G] in
theorem isCompIn_inf_centralizer {A H : Subgroup G} (hA : QS A) (hs : Star A) (hAH : A ≤ H)
    {w : G} (hw : orderOf w = 2) (hAw : A ≤ Subgroup.centralizer ({w} : Set G)) :
    IsCompIn A (H ⊓ Subgroup.centralizer ({w} : Set G)) :=
  ⟨le_inf hAH hAw,
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_right (hs w hw hAw), hA⟩

theorem lemma_2_7_two_amb {H : Subgroup G} {t : G} (htH : t ∈ H) (ht : orderOf t = 2)
    {K L : Subgroup G} (hK : IsCompIn K (H ⊓ Subgroup.centralizer ({t} : Set G)))
    (hL : IsCompIn L H) (hglaub : GlaubermanAt (↥L ⧸ Subgroup.center ↥L)) :
    ⁅K, L⁆ = ⊥ ∨ K ≤ L ∨ (conjugate L t ≠ L ∧ K ≤ ⁅L, Subgroup.zpowers t⁆) := by
  have hKH : K ≤ H := hK.1.trans inf_le_left
  have hLH : L ≤ H := hL.1
  set a : H := ⟨t, htH⟩ with ha_def
  have ha : orderOf a = 2 := by rw [← ht]; exact Subgroup.orderOf_mk t htH
  have hmapK : (K.subgroupOf H).map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  have hmapL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hCeq : Subgroup.centralizer ({a} : Set H) =
      (H ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf H := by
    ext x
    rw [mem_centralizer_single, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_single]
    constructor
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hKC : K.subgroupOf H ≤ Subgroup.centralizer ({a} : Set H) := by
    rw [hCeq]
    intro x hx
    exact hK.1 (Subgroup.mem_subgroupOf.1 hx)
  have hKsub : ((K.subgroupOf H).subgroupOf (Subgroup.centralizer ({a} : Set H))).IsSubnormal := by
    let φ : ↥(Subgroup.centralizer ({a} : Set H)) →*
        ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) :=
      { toFun := fun x => ⟨(x.1 : G), x.1.2,
          mem_centralizer_single.2 (congrArg Subtype.val (mem_centralizer_single.1 x.2))⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have h1 := hK.2.1.comap φ
    have heq : (K.subgroupOf (H ⊓ Subgroup.centralizer ({t} : Set G))).comap φ =
        (K.subgroupOf H).subgroupOf (Subgroup.centralizer ({a} : Set H)) :=
      Subgroup.ext fun x => Iff.rfl
    rwa [heq] at h1
  have hKqs : QS (K.subgroupOf H) :=
    Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hKH) hK.2.2
  have hK' : IsComponentOf ((K.subgroupOf H).subgroupOf (Subgroup.centralizer ({a} : Set H))) ⊤ :=
    (OrdinaryComponentTransport.subgroupOf_iff _ _ hKC).2 ⟨hKsub, hKqs⟩
  have key := lemma_2_7_two_at a ha (K.subgroupOf H) (L.subgroupOf H)
    (glaubermanAt_subgroupOf hLH hglaub) hKC hK' (isComponentOf_subgroupOf hL)
  rcases key with h | h | ⟨h3, h3'⟩ | ⟨-, h4⟩
  · right; left
    rw [← hmapK, ← hmapL, h]
  · left
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_commutator, hmapK, hmapL, Subgroup.map_bot] at this
  · right; right
    refine ⟨?_, ?_⟩
    · intro hcon
      apply h3
      apply Subgroup.map_injective H.subtype_injective
      rw [rightComponent_eq_conjugate, map_subtype_conjugate, hmapL]
      exact hcon
    · have hle : K.subgroupOf H ≤ ⁅L.subgroupOf H, Subgroup.zpowers a⁆ := by
        rw [h3']
        exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans (commutator_self_le _)
      have := Subgroup.map_mono (f := H.subtype) hle
      rwa [hmapK, Subgroup.map_commutator, hmapL, MonoidHom.map_zpowers] at this
  · right; left
    have := Subgroup.map_mono (f := H.subtype) h4
    rwa [hmapK, hmapL] at this

theorem lemma_2_8_amb {H U : Subgroup G} (hUH : U ≤ H) (hU : IsFourGroup U) {L : Subgroup G}
    (hL : IsCompIn L H) {u : G} (hu : u ∈ U) (hmoved : conjugate L u ≠ L) {M : Subgroup G}
    (hM : ∀ w ∈ U, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ M) : L ≤ M := by
  have hu1 : u ≠ 1 := fun h => hmoved (h ▸ conjugate_one L)
  have hLH : L ≤ H := hL.1
  set U' : Subgroup H := U.subgroupOf H with hU'def
  have hU' : IsFourGroup U' := isFourGroup_subgroupOf hUH hU
  set u' : H := ⟨u, hUH hu⟩ with hu'def
  have hu'U : u' ∈ U' := hu
  have hu'1 : u' ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  obtain ⟨v', hv'U, hv'1, hv'u, hgen⟩ := fourGroup_exists_gen hU' hu'U hu'1
  have hu'2 : orderOf u' = 2 := fourGroup_orderOf hU' hu'U hu'1
  have hv'2 : orderOf v' = 2 := fourGroup_orderOf hU' hv'U hv'1
  have hmoved' : rightComponent (L.subgroupOf H) u' ≠ L.subgroupOf H := by
    intro h
    apply hmoved
    have := congrArg (Subgroup.map H.subtype) h
    rwa [rightComponent_eq_conjugate, map_subtype_conjugate,
      Subgroup.map_subgroupOf_eq_of_le hLH] at this
  have h28 := (CFSG.ComponentClassification.AschbacherToolkit.lemma_2_8_centralizers U' hU'.1
    hU'.2 u' v' hu'2 hv'2 (Ne.symm hv'u) hgen (L.subgroupOf H) (isComponentOf_subgroupOf hL)
    hmoved').1
  have hsup : (⨆ (w : U') (_ : (w : H) ≠ 1), Subgroup.centralizer ({(w : H)} : Set H)) ≤
      M.comap H.subtype := by
    refine iSup₂_le fun w hw x hx => ?_
    have hwU : ((w : H) : G) ∈ U := w.2
    have hw1 : ((w : H) : G) ≠ 1 := fun h => hw (Subtype.ext h)
    apply hM _ hwU hw1
    exact mem_centralizer_single.2 (congrArg Subtype.val (mem_centralizer_single.1 hx))
  intro l hl
  exact hsup (h28 (show (⟨l, hLH hl⟩ : H) ∈ L.subgroupOf H from hl))

end Ambient

end CFSG.CGT.PushingUpLit.CGT6.Nine7
