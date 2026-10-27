module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverDihedral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverSemidihedral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralTwoCoverTransfer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {J : Type*} [Group J] [Finite J]

noncomputable abbrev centralSylow (Q : Sylow 2 J) : Sylow 2 (J ⧸ Subgroup.center J) :=
  Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))

theorem mk_mem_centralSylow (Q : Sylow 2 J) (q : (Q : Subgroup J)) :
    ((q : J) : J ⧸ Subgroup.center J) ∈ (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) :=
  Subgroup.mem_map_of_mem _ q.2

@[expose] noncomputable def centralSylowMap (Q : Sylow 2 J) :
    (Q : Subgroup J) →* (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) :=
  ((QuotientGroup.mk' (Subgroup.center J)).comp (Q : Subgroup J).subtype).codRestrict _
    (mk_mem_centralSylow Q)

@[expose] noncomputable def coverHom (Q : Sylow 2 J) {X : Type*} [Group X]
    (e : (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) ≃* X) : (Q : Subgroup J) →* X :=
  e.toMonoidHom.comp (centralSylowMap Q)

theorem centralSylowMap_surjective (Q : Sylow 2 J) : Function.Surjective (centralSylowMap Q) := by
  rintro ⟨x, q, hq, rfl⟩
  exact ⟨⟨q, hq⟩, rfl⟩

variable {Q : Sylow 2 J} {X : Type*} [Group X]
  {e : (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) ≃* X}

theorem coverHom_surjective : Function.Surjective (coverHom Q e) :=
  e.surjective.comp (centralSylowMap_surjective Q)

theorem coverHom_apply (q : (Q : Subgroup J)) :
    coverHom Q e q = e ⟨((q : J) : J ⧸ Subgroup.center J), mk_mem_centralSylow Q q⟩ :=
  rfl

theorem coverHom_eq_one_iff (q : (Q : Subgroup J)) :
    coverHom Q e q = 1 ↔ (q : J) ∈ Subgroup.center J := by
  rw [coverHom_apply, map_eq_one_iff _ e.injective, ← QuotientGroup.eq_one_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem coverHom_central (c : (Q : Subgroup J)) (hc : coverHom Q e c = 1) (g : (Q : Subgroup J)) :
    g * c = c * g :=
  Subtype.ext (Subgroup.mem_center_iff.mp ((coverHom_eq_one_iff c).mp hc) g)

theorem coverHom_mem_commutator (hperf : commutator J = ⊤) (c : (Q : Subgroup J))
    (hc : coverHom Q e c = 1) : c ∈ commutator (Q : Subgroup J) :=
  CFSG.ProperTwoGeneratedCore.CentralTwoCover.mem_commutator_of_mem_center_of_perfect hperf Q
    ((coverHom_eq_one_iff c).mp hc) c.2

theorem center_eq_bot_of_coverHom (hZ : IsPGroup 2 (Subgroup.center J))
    (h : ∀ c : (Q : Subgroup J), coverHom Q e c = 1 → c = 1) : Subgroup.center J = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzQ : z ∈ (Q : Subgroup J) := hZ.le_sylow_of_normal Q hz
  have := h ⟨z, hzQ⟩ ((coverHom_eq_one_iff _).mpr hz)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

theorem mem_center_of_dihedral (hperf : commutator J = ⊤) (hZ : IsPGroup 2 (Subgroup.center J))
    (hZne : Subgroup.center J ≠ ⊥) (Q : Sylow 2 J) {m : ℕ} (hm : 2 ≤ m)
    (e : (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) ≃* DihedralGroup m) {y : J}
    (hy : orderOf y = 2) : y ∈ Subgroup.center J := by
  obtain ⟨x, hx, hkerx⟩ := exists_cyclic_index_two_of_dihedral Q.isPGroup' hm (coverHom Q e)
    coverHom_surjective coverHom_central (coverHom_mem_commutator hperf)
  have hsub : (Subgroup.zpowers (x : J)).subgroupOf (Q : Subgroup J) = Subgroup.zpowers x := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [Subgroup.coe_zpow]⟩
  refine mem_center_of_cyclic_index_two hperf hZ hZne Q x.2 ?_ ?_ hy
  · rw [Subgroup.relIndex, hsub, hx]
  · intro z hz
    have hzQ : z ∈ (Q : Subgroup J) := hZ.le_sylow_of_normal Q hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (hkerx ⟨z, hzQ⟩ ((coverHom_eq_one_iff _).mpr hz))
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩

theorem false_of_semidihedral (hperf : commutator J = ⊤) (hZ : IsPGroup 2 (Subgroup.center J))
    (hZne : Subgroup.center J ≠ ⊥) (Q : Sylow 2 J) {n : ℕ} (hn : 4 ≤ n)
    (e : (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) ≃*
      CFSG.Open.SemidihedralGroup n) : False :=
  hZne (center_eq_bot_of_coverHom hZ fun c hc =>
    eq_one_of_semidihedral hn (coverHom Q e) coverHom_surjective coverHom_central hc
      (coverHom_mem_commutator hperf c hc))

end CFSG.ProperTwoGeneratedCore.Lemma37
