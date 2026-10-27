module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.CharacterTheory.Semidihedral.FourPointLifts

public noncomputable section

namespace CFSG.Wreathed.UniqueInvolutionLift

open scoped Classical

universe u v

variable {H : Type u} {Γ : Type v} [Group H] [Group Γ]

@[expose] def liftedSubgroup (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) : Subgroup H :=
  T ⊓ L.comap φ

instance liftedSubgroup_normal (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    [T.Normal] [L.Normal] : (liftedSubgroup φ T L).Normal := by
  unfold liftedSubgroup
  infer_instance

@[expose] def restrictedMap (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) :
    liftedSubgroup φ T L →* L :=
  (φ.domRestrict (liftedSubgroup φ T L)).codRestrict L (fun x => x.property.2)

theorem restrictedMap_coe (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (x : liftedSubgroup φ T L) : (restrictedMap φ T L x : Γ) = φ (x : H) := rfl

theorem restrictedMap_surjective (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (hLT : L ≤ T.map φ) : Function.Surjective (restrictedMap φ T L) := by
  intro l
  obtain ⟨t, ht, heq⟩ := Subgroup.mem_map.mp (hLT l.property)
  refine ⟨⟨t, ht, ?_⟩, Subtype.ext heq⟩
  change φ t ∈ L
  exact heq.symm ▸ l.property

theorem restrictedMap_ker (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) :
    (restrictedMap φ T L).ker = φ.ker.subgroupOf (liftedSubgroup φ T L) := by
  ext x
  change restrictedMap φ T L x = 1 ↔ φ (x : H) = 1
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem restrictedMap_ker_eq_involution (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (c : H) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c) :
    (restrictedMap φ T L).ker = (Subgroup.zpowers c).subgroupOf (liftedSubgroup φ T L) := by
  rw [restrictedMap_ker]
  ext x
  change x.val ∈ φ.ker ↔ x.val ∈ Subgroup.zpowers c
  rw [← hintersection]
  exact ⟨fun hx => ⟨hx, x.property.1⟩, And.left⟩

theorem involution_mem_lift (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (c : H) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c) : c ∈ liftedSubgroup φ T L := by
  have hc : c ∈ φ.ker ⊓ T := hintersection.symm ▸ Subgroup.mem_zpowers c
  exact ⟨hc.2, by change φ c ∈ L; rw [MonoidHom.mem_ker.mp hc.1]; exact L.one_mem⟩

theorem perfect_of_unique_involution_double_cover
    [Finite H] [Finite Γ] [Group.IsPerfect Γ]
    (φ : H →* Γ) (hφ : Function.Surjective φ) (heven : Even (Nat.card Γ))
    (c : H) (hc : orderOf c = 2) (hker : φ.ker = Subgroup.zpowers c)
    (hunique : ∀ x : H, orderOf x = 2 → x = c) : Group.IsPerfect H := by
  have hderived := CFSG.RankThreeCoreUniqueness.Helpers.surjective_perfect_image_derived_surjective
    φ hφ
  have hcderived : c ∈ commutator H := by
    by_contra hnot
    let f := φ.comp (commutator H).subtype
    have hinjective : Function.Injective f := by
      apply f.ker_eq_bot_iff.mp
      apply le_antisymm _ bot_le
      intro d hd
      have hdker : (d : H) ∈ Subgroup.zpowers c := by
        rw [← hker]
        exact hd
      rcases (CFSG.Semidihedral.FourPointLifts.mem_zpowers_order_two_iff c d hc).mp hdker with
        hone | heq
      · exact Subtype.ext hone
      · exact (hnot (heq ▸ d.property)).elim
    let e : commutator H ≃* Γ := MulEquiv.ofBijective f ⟨hinjective, hderived⟩
    have hevend : 2 ∣ Nat.card (commutator H) := by
      rw [Nat.card_congr e.toEquiv]
      exact even_iff_two_dvd.mp heven
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := commutator H) 2 hevend
    have heq : (d : H) = c := hunique d ((Subgroup.orderOf_coe d).trans hd)
    exact hnot (heq ▸ d.property)
  apply Group.isPerfect_def.mpr
  have hkerle : φ.ker ≤ commutator H := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hcderived
  simpa only [sup_eq_left.mpr hkerle] using
    CFSG.RankThreeCoreUniqueness.Helpers.surjective_perfect_image_derived_sup_kernel_eq_top φ hφ


@[expose] def liftedInvolution (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (c : H) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c) : liftedSubgroup φ T L :=
  ⟨c, involution_mem_lift φ T L c hintersection⟩

theorem restrictedMap_kernel_zpowers (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (c : H) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c) :
    (restrictedMap φ T L).ker = Subgroup.zpowers (liftedInvolution φ T L c hintersection) := by
  rw [restrictedMap_ker_eq_involution φ T L c hintersection]
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le
    (Subgroup.zpowers_le.mpr (involution_mem_lift φ T L c hintersection)), MonoidHom.map_zpowers]
  rfl

theorem restrictedMap_kernel_central (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (hcentral : φ.ker ≤ Subgroup.center H) :
    (restrictedMap φ T L).ker ≤ Subgroup.center (liftedSubgroup φ T L) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hcentral (congrArg Subtype.val hx)) y.val

theorem liftedSubgroup_perfect [Finite H] [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (c : H) (hc : orderOf c = 2)
    (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c) :
    Group.IsPerfect (liftedSubgroup φ T L) := by
  let : Group.IsPerfect L := CFSG.RankThreeCoreUniqueness.Helpers.nonabelian_simple_isPerfect hnonab
  apply perfect_of_unique_involution_double_cover (restrictedMap φ T L)
    (restrictedMap_surjective φ T L hLT) heven (liftedInvolution φ T L c hintersection)
    ((Subgroup.orderOf_coe _).symm.trans hc)
    (restrictedMap_kernel_zpowers φ T L c hintersection)
  intro x hx
  apply Subtype.ext
  exact hunique x x.property.1 ((Subgroup.orderOf_coe x).trans hx)

theorem liftedSubgroup_center
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (hcentral : φ.ker ≤ Subgroup.center H) (c : H)
    (hintersection : φ.ker ⊓ T = Subgroup.zpowers c) :
    Subgroup.center (liftedSubgroup φ T L) =
      (Subgroup.zpowers c).subgroupOf (liftedSubgroup φ T L) := by
  rw [← restrictedMap_ker_eq_involution φ T L c hintersection]
  exact CFSG.RankThreeCoreUniqueness.Helpers.surjective_centerless_image_center_eq_kernel
    (restrictedMap φ T L) (restrictedMap_surjective φ T L hLT)
    (restrictedMap_kernel_central φ T L hcentral)
    (CFSG.RankThreeCoreUniqueness.Helpers.nonabelian_simple_center_eq_bot hnonab)

theorem liftedSubgroup_quasisimple [Finite H] [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (hcentral : φ.ker ≤ Subgroup.center H)
    (c : H) (hc : orderOf c = 2) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c) :
    CFSG.Open.IsQuasisimple (liftedSubgroup φ T L) := by
  let : Group.IsPerfect (liftedSubgroup φ T L) :=
    liftedSubgroup_perfect φ T L hLT hnonab heven c hc hintersection hunique
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_central_extension_simple_image_quasisimple
    (restrictedMap φ T L) (restrictedMap_surjective φ T L hLT)
    (restrictedMap_kernel_central φ T L hcentral) hnonab

theorem liftedSubgroup_component [Finite H] [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [T.Normal] [L.Normal] [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (hcentral : φ.ker ≤ Subgroup.center H)
    (c : H) (hc : orderOf c = 2) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c) :
    CFSG.IsComponent (liftedSubgroup φ T L) := by
  apply (CFSG.isComponent_iff_open _).mpr
  exact ⟨le_top, CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
    (inferInstance : (liftedSubgroup φ T L).Normal).isSubnormal,
    liftedSubgroup_quasisimple φ T L hLT hnonab heven hcentral c hc hintersection hunique⟩


theorem liftedSubgroup_centralizer (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (hLT : L ≤ T.map φ) (hcentral : φ.ker ≤ Subgroup.center H)
    (hself : Subgroup.centralizer (L : Set Γ) = ⊥) :
    Subgroup.centralizer (liftedSubgroup φ T L : Set H) = φ.ker := by
  apply le_antisymm
  · intro h hh
    have himage : φ h ∈ Subgroup.centralizer (L : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨m, hm⟩ := restrictedMap_surjective φ T L hLT ⟨l, hl⟩
      have hφm : φ (m : H) = l := congrArg Subtype.val hm
      rw [← hφm]
      simpa only [map_mul] using congrArg φ
        (Subgroup.mem_centralizer_iff.mp hh m m.property)
    exact Subgroup.mem_bot.mp (hself ▸ himage)
  · exact hcentral.trans (Subgroup.center_le_centralizer _)

theorem ambient_center (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (hLT : L ≤ T.map φ) (hcentral : φ.ker ≤ Subgroup.center H)
    (hself : Subgroup.centralizer (L : Set Γ) = ⊥) : Subgroup.center H = φ.ker := by
  apply le_antisymm _ hcentral
  exact (Subgroup.center_le_centralizer (liftedSubgroup φ T L : Set H)).trans
    (liftedSubgroup_centralizer φ T L hLT hcentral hself).le

theorem component_eq_liftedSubgroup [Finite H] [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [T.Normal] [L.Normal] [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (hcentral : φ.ker ≤ Subgroup.center H)
    (hself : Subgroup.centralizer (L : Set Γ) = ⊥)
    (c : H) (hc : orderOf c = 2) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c)
    (D : Subgroup H) (hD : CFSG.IsComponent D) : D = liftedSubgroup φ T L := by
  by_contra hne
  have hM := liftedSubgroup_component φ T L hLT hnonab heven hcentral c hc hintersection hunique
  have hDopen := (CFSG.isComponent_iff_open D).mp hD
  have hMopen := (CFSG.isComponent_iff_open _).mp hM
  have hcommutes := CFSG.ComponentClassification.LocalComponents.commute_of_ne
    D (liftedSubgroup φ T L) hDopen hMopen hne
  have hbound : D ≤ Subgroup.center H := by
    have hDC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes
    rw [liftedSubgroup_centralizer φ T L hLT hcentral hself] at hDC
    exact hDC.trans hcentral
  let : Group.IsPerfect D := hD.1.1
  let : Nontrivial D := CFSG.ComponentClassification.Quasisimple.nontrivial hDopen.2.2
  have hab : IsMulCommutative D := isMulCommutative_iff.mpr (by
    intro a b
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hbound b.property) a.val))
  exact Group.IsPerfect.not_isMulCommutative D hab

theorem layer_eq_liftedSubgroup [Finite H] [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [T.Normal] [L.Normal] [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (hcentral : φ.ker ≤ Subgroup.center H)
    (hself : Subgroup.centralizer (L : Set Γ) = ⊥)
    (c : H) (hc : orderOf c = 2) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c) :
    CFSG.layer H = liftedSubgroup φ T L := by
  apply le_antisymm
  · apply sSup_le
    intro D hD
    exact (component_eq_liftedSubgroup φ T L hLT hnonab heven hcentral hself
      c hc hintersection hunique D hD).le
  · exact le_sSup (liftedSubgroup_component φ T L hLT hnonab heven hcentral
      c hc hintersection hunique)

theorem liftedSubgroup_characteristic [Finite H] [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) [T.Normal] [L.Normal] [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (hcentral : φ.ker ≤ Subgroup.center H)
    (hself : Subgroup.centralizer (L : Set Γ) = ⊥)
    (c : H) (hc : orderOf c = 2) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c) :
    (liftedSubgroup φ T L).Characteristic := by
  rw [← layer_eq_liftedSubgroup φ T L hLT hnonab heven hcentral hself
    c hc hintersection hunique, CFSG.layer_eq_componentClassification]
  exact CFSG.ComponentClassification.Layer.characteristic H

theorem restrictedMap_no_section [Finite Γ]
    (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ) (heven : Even (Nat.card L))
    (c : H) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c)
    (σ : L →* liftedSubgroup φ T L) :
    (restrictedMap φ T L).comp σ ≠ MonoidHom.id L := by
  intro hsection
  have hleft : Function.LeftInverse (restrictedMap φ T L) σ := by
    intro l
    exact congrArg (fun f : L →* L => f l) hsection
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (even_iff_two_dvd.mp heven)
  have horder : orderOf (σ l) = 2 := (orderOf_injective σ hleft.injective l).trans hl
  have heq : ((σ l : liftedSubgroup φ T L) : H) = c :=
    hunique _ (σ l).property.1 ((Subgroup.orderOf_coe _).trans horder)
  have hcφ : φ c = 1 := MonoidHom.mem_ker.mp
    ((hintersection.symm ▸ Subgroup.mem_zpowers c).1)
  have hσzero : restrictedMap φ T L (σ l) = 1 := by
    apply Subtype.ext
    change φ ((σ l : liftedSubgroup φ T L) : H) = 1
    rw [heq]
    exact hcφ
  have hlone : l = 1 := (hleft l).symm.trans hσzero
  rw [hlone, orderOf_one] at hl
  omega


@[expose] def liftedQuotientEquiv (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (hLT : L ≤ T.map φ) :
    liftedSubgroup φ T L ⧸ (restrictedMap φ T L).ker ≃* L :=
  QuotientGroup.quotientKerEquivOfSurjective (restrictedMap φ T L)
    (restrictedMap_surjective φ T L hLT)

theorem liftedQuotientEquiv_mk (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (hLT : L ≤ T.map φ) (m : liftedSubgroup φ T L) :
    liftedQuotientEquiv φ T L hLT ((QuotientGroup.mk' (restrictedMap φ T L).ker) m) =
      restrictedMap φ T L m := rfl

structure UniqueInvolutionLiftData (φ : H →* Γ) (T : Subgroup H) (L : Subgroup Γ)
    (c : H) : Prop where
  normal : (liftedSubgroup φ T L).Normal
  involution_mem : c ∈ liftedSubgroup φ T L
  restriction_surjective : Function.Surjective (restrictedMap φ T L)
  restriction_kernel : (restrictedMap φ T L).ker =
    (Subgroup.zpowers c).subgroupOf (liftedSubgroup φ T L)
  perfect : Group.IsPerfect (liftedSubgroup φ T L)
  center : Subgroup.center (liftedSubgroup φ T L) =
    (Subgroup.zpowers c).subgroupOf (liftedSubgroup φ T L)
  actual_quotient : Nonempty (liftedSubgroup φ T L ⧸ (restrictedMap φ T L).ker ≃* L)
  quasisimple : CFSG.IsQuasisimple (liftedSubgroup φ T L)
  component : CFSG.IsComponent (liftedSubgroup φ T L)
  only_component : ∀ D : Subgroup H, CFSG.IsComponent D → D = liftedSubgroup φ T L
  layer : CFSG.layer H = liftedSubgroup φ T L
  characteristic : (liftedSubgroup φ T L).Characteristic
  ambient_center : Subgroup.center H = φ.ker
  centralizer : Subgroup.centralizer (liftedSubgroup φ T L : Set H) = φ.ker
  no_section : ∀ σ : L →* liftedSubgroup φ T L,
    (restrictedMap φ T L).comp σ ≠ MonoidHom.id L

theorem unique_involution_residual_lifts_simple_layer [Finite H] [Finite Γ]
    (φ : H →* Γ) (_hφ : Function.Surjective φ)
    (T : Subgroup H) (L : Subgroup Γ) [T.Normal] [L.Normal] [IsSimpleGroup L]
    (hLT : L ≤ T.map φ) (hnonab : ∃ a b : L, a * b ≠ b * a)
    (heven : Even (Nat.card L)) (hcentral : φ.ker ≤ Subgroup.center H)
    (hself : Subgroup.centralizer (L : Set Γ) = ⊥)
    (c : H) (hc : orderOf c = 2) (hintersection : φ.ker ⊓ T = Subgroup.zpowers c)
    (hunique : ∀ t : H, t ∈ T → orderOf t = 2 → t = c) :
    UniqueInvolutionLiftData φ T L c := by
  have hcomponent := liftedSubgroup_component φ T L hLT hnonab heven hcentral
    c hc hintersection hunique
  exact ⟨inferInstance, involution_mem_lift φ T L c hintersection,
    restrictedMap_surjective φ T L hLT, restrictedMap_ker_eq_involution φ T L c hintersection,
    hcomponent.1.1, liftedSubgroup_center φ T L hLT hnonab hcentral c hintersection,
    ⟨liftedQuotientEquiv φ T L hLT⟩, hcomponent.1, hcomponent,
    component_eq_liftedSubgroup φ T L hLT hnonab heven hcentral hself
      c hc hintersection hunique,
    layer_eq_liftedSubgroup φ T L hLT hnonab heven hcentral hself
      c hc hintersection hunique,
    liftedSubgroup_characteristic φ T L hLT hnonab heven hcentral hself
      c hc hintersection hunique,
    ambient_center φ T L hLT hcentral hself,
    liftedSubgroup_centralizer φ T L hLT hcentral hself,
    restrictedMap_no_section φ T L heven c hintersection hunique⟩

end CFSG.Wreathed.UniqueInvolutionLift
