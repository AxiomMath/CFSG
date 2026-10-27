module

public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup
open scoped commutatorElement

theorem commutatorElement_mul_central {G : Type*} [Group G] (a b c d : G)
    (hc : c ∈ center G) (hd : d ∈ center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have h1 : ⁅c, b * d⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hc (b * d)).symm
  have h2 : ⁅a, d⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hd a)
  rw [commutatorElement_mul_left_eq_conj_mul, h1, commutatorElement_mul_right_eq_mul_conj, h2]
  group

theorem conj_eq_of_mem_center {G : Type*} [Group G] {c : G} (hc : c ∈ center G) (a : G) :
    a * c * a⁻¹ = c := by
  rw [mem_center_iff.mp hc a, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_mem_center {G : Type*} [Group G] {y a b : G}
    (hb : ⁅y, b⁆ ∈ center G) : ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆ := by
  have key : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    simp only [mul_assoc]
  rw [key, conj_eq_of_mem_center hb]

theorem mem_center_of_commutator_mem {G : Type*} [Group G] [Group.IsPerfect G] (y : G)
    (Z : Subgroup G) (hZ : ∀ z ∈ Z, z ∈ center G) (h : ∀ g : G, ⁅y, g⁆ ∈ Z) :
    y ∈ center G := by
  let φ : G →* Z :=
    { toFun := fun g => ⟨⁅y, g⁆, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (commutatorElement_mul_right_of_mem_center (hZ _ (h b))) }
  have hcomm : ∀ a b : G, Commute (φ a) (φ b) := fun a b =>
    Subtype.ext (mem_center_iff.mp (hZ _ (h a)) ⁅y, b⁆).symm
  have hkill : ∀ a b : G, ⁅y, ⁅a, b⁆⁆ = 1 := by
    intro a b
    have h3 : φ ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement]
      exact (hcomm a b).commutator_eq
    exact congrArg Subtype.val h3
  have hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have htop : (⊤ : Subgroup G) ≤ centralizer ({y} : Set G) := by
    refine hperf.symm.le.trans ?_
    rw [commutator_le]
    intro a _ b _
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hkill a b)
  refine mem_center_iff.mpr (fun g => ?_)
  have hg := htop (mem_top g)
  rw [mem_centralizer_iff] at hg
  exact (hg y (Set.mem_singleton y)).symm

theorem commutator_commutator_eq_self {M : Type*} [Group M] {X Y : Subgroup M}
    (hY : Y = ⁅X, X⁆) (hX : ∀ x ∈ X, ∃ y ∈ Y, ∃ c ∈ center M, x = y * c) :
    ⁅Y, Y⁆ = Y := by
  subst hY
  have hYX : ⁅X, X⁆ ≤ X := commutator_le_of_le le_rfl le_rfl
  refine le_antisymm (commutator_mono hYX hYX) ?_
  rw [commutator_le]
  intro x hx x' hx'
  obtain ⟨y, hy, c, hc, rfl⟩ := hX x hx
  obtain ⟨y', hy', c', hc', rfl⟩ := hX x' hx'
  rw [commutatorElement_mul_central _ _ _ _ hc hc']
  exact commutator_mem_commutator hy hy'

theorem mk'_eq_one_iff' {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (x : G) :
    QuotientGroup.mk' N x = 1 ↔ x ∈ N :=
  QuotientGroup.eq_one_iff x

theorem exists_mul_central_of_mem_map {Y : Type*} [Group Y] (N : Subgroup Y) {a : Y}
    (h : QuotientGroup.mk' (center Y) a ∈ N.map (QuotientGroup.mk' (center Y))) :
    ∃ n ∈ N, ∃ z ∈ center Y, a = n * z := by
  obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.mp h
  exact ⟨n, hn, n⁻¹ * a, QuotientGroup.eq.mp hna, (mul_inv_cancel_left n a).symm⟩

theorem le_center_of_normal_isSolvable {Y : Type*} [Group Y] (hY : CFSG.IsQuasisimple Y)
    (N : Subgroup Y) [N.Normal] [Group.IsSolvable N] : N ≤ center Y := by
  obtain ⟨hYp, hYs, -⟩ := hY
  haveI : Group.IsPerfect Y := hYp
  haveI : IsSimpleGroup (Y ⧸ center Y) := hYs
  haveI : Nontrivial Y := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (Y ⧸ center Y) (QuotientGroup.mk'_surjective (center Y)).subsingleton
  haveI : (N.map (QuotientGroup.mk' (center Y))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective (center Y))
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map (QuotientGroup.mk' (center Y))) with hbot | htop
  · intro x hx
    have hmem : QuotientGroup.mk' (center Y) x ∈ N.map (QuotientGroup.mk' (center Y)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (mk'_eq_one_iff' _ _).mp hmem
  · exfalso
    have hdec : ∀ a : Y, ∃ n ∈ N, ∃ z ∈ center Y, a = n * z := fun a =>
      exists_mul_central_of_mem_map N (by rw [htop]; exact Subgroup.mem_top _)
    have hcomm : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ ≤ N := by
      rw [commutator_le]
      intro a _ b _
      obtain ⟨n, hn, za, hza, rfl⟩ := hdec a
      obtain ⟨n', hn', zb, hzb, rfl⟩ := hdec b
      rw [commutatorElement_mul_central _ _ _ _ hza hzb]
      exact commutator_le_of_le le_rfl le_rfl (commutator_mem_commutator hn hn')
    have hperf : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
    have hNtop : N = ⊤ := eq_top_iff.mpr (hperf.symm.le.trans hcomm)
    have hsurj : Function.Surjective N.subtype := fun y =>
      ⟨⟨y, by rw [hNtop]; exact Subgroup.mem_top y⟩, rfl⟩
    exact Group.IsPerfect.not_isSolvable Y (Group.isSolvable_of_surjective hsurj)

theorem exists_quasisimple_lift_of_hom {M Q : Type*} [Group M] [Group Q] (f : M →* Q)
    (hker : f.ker ≤ center M) (K : Subgroup Q) (hK : CFSG.IsQuasisimple K)
    (hKf : K ≤ f.range) :
    ∃ Y : Subgroup M, CFSG.IsQuasisimple Y ∧ Y.map f = K ∧
      (∀ y ∈ Y, (∀ k ∈ K, k * f y = f y * k) → ∀ y' ∈ Y, y' * y = y * y') ∧
      Nonempty (↥Y ⧸ center ↥Y ≃* ↥K ⧸ center ↥K) := by
  obtain ⟨hKp, hKs, a0, b0, hKab⟩ := hK
  haveI : Group.IsPerfect K := hKp
  haveI : IsSimpleGroup (K ⧸ center K) := hKs
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup M, X = K.comap f := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup M, Y = ⁅X, X⁆ := ⟨_, rfl⟩
  have hXK : X.map f = K := by
    rw [hXdef]
    exact Subgroup.map_comap_eq_self hKf
  have hYf : Y.map f = K := by
    rw [hYdef, Subgroup.map_commutator, hXK, Subgroup.commutator_eq_self]
  have hfX : ∀ x, x ∈ X ↔ f x ∈ K := fun x => by
    rw [hXdef, Subgroup.mem_comap]
  have hdec : ∀ x ∈ X, ∃ y ∈ Y, ∃ c ∈ center M, x = y * c := by
    intro x hx
    have hfx : f x ∈ Y.map f := by
      rw [hYf]
      exact (hfX x).mp hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hfx
    refine ⟨y, hy, y⁻¹ * x, hker ?_, (mul_inv_cancel_left y x).symm⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have hYY : ⁅Y, Y⁆ = Y := commutator_commutator_eq_self hYdef hdec
  haveI : Group.IsPerfect Y := Subgroup.isPerfect_iff.mpr hYY
  have hfY : ∀ g ∈ Y, f g ∈ K := fun g hg => by
    rw [← hYf]
    exact Subgroup.mem_map_of_mem f hg
  have hYcent : ∀ y ∈ Y, (∀ k ∈ K, k * f y = f y * k) → ∀ y' ∈ Y, y' * y = y * y' := by
    intro y hy hcent
    have hc : (⟨y, hy⟩ : ↥Y) ∈ center ↥Y := by
      refine mem_center_of_commutator_mem (⟨y, hy⟩ : ↥Y) (f.ker.subgroupOf Y) ?_ ?_
      · intro z hz
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp (hker (Subgroup.mem_subgroupOf.mp hz)) (g : M)
      · intro g
        rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
        change f ⁅y, (g : M)⁆ = 1
        rw [map_commutatorElement]
        exact Commute.commutator_eq (hcent _ (hfY g g.2)).symm
    intro y' hy'
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y', hy'⟩)
  have hsub : ∀ y : ↥Y, (f.comp Y.subtype) y ∈ K := fun y => hfY y y.2
  let ψ : ↥Y →* ↥K ⧸ center ↥K :=
    (QuotientGroup.mk' (center ↥K)).comp ((f.comp Y.subtype).codRestrict K hsub)
  have hψ : ∀ y : ↥Y, ψ y = QuotientGroup.mk' (center ↥K) ⟨f y, hfY y y.2⟩ := fun y => rfl
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center ↥K) q
    have hk : (k : Q) ∈ Y.map f := by
      rw [hYf]
      exact k.2
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hψ]
    exact congrArg (QuotientGroup.mk' (center ↥K)) (Subtype.ext hyk)
  have hkerψ : ψ.ker = center ↥Y := by
    ext y
    rw [MonoidHom.mem_ker, hψ, mk'_eq_one_iff']
    constructor
    · intro hmem
      have hcent : ∀ k ∈ K, k * f y = f y * k := fun k hk =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨k, hk⟩)
      exact Subgroup.mem_center_iff.mpr (fun g => Subtype.ext (hYcent y y.2 hcent g g.2))
    · intro hyc
      refine Subgroup.mem_center_iff.mpr (fun r => Subtype.ext ?_)
      have hr : (r : Q) ∈ Y.map f := by
        rw [hYf]
        exact r.2
      obtain ⟨g, hg, hgr⟩ := Subgroup.mem_map.mp hr
      have hgy : g * (y : M) = (y : M) * g :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨g, hg⟩)
      show (r : Q) * f y = f y * (r : Q)
      rw [← hgr, ← map_mul, ← map_mul, hgy]
  have hiso : ↥Y ⧸ center ↥Y ≃* ↥K ⧸ center ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  refine ⟨Y, ?_, hYf, hYcent, ⟨hiso⟩⟩
  unfold CFSG.IsQuasisimple
  refine ⟨inferInstance, hiso.isSimpleGroup, hiso.symm a0, hiso.symm b0, fun h => hKab ?_⟩
  have h' := congrArg hiso h
  simpa using h'

theorem quasisimple_range_of_ker_le_center {Y Q : Type*} [Group Y] [Group Q]
    (hY : CFSG.IsQuasisimple Y) (f : Y →* Q) (hker : f.ker ≤ center Y) :
    CFSG.IsQuasisimple f.range ∧ Nonempty (↥f.range ⧸ center ↥f.range ≃* Y ⧸ center Y) := by
  obtain ⟨hYp, hYs, a0, b0, hab0⟩ := hY
  haveI : Group.IsPerfect Y := hYp
  haveI : IsSimpleGroup (Y ⧸ center Y) := hYs
  let ψ : Y →* f.range ⧸ center f.range :=
    (QuotientGroup.mk' (center f.range)).comp f.rangeRestrict
  have hψ : ∀ y : Y, ψ y = QuotientGroup.mk' (center f.range) (f.rangeRestrict y) :=
    fun y => rfl
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (center f.range) q
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp r.2
    refine ⟨y, ?_⟩
    rw [hψ]
    exact congrArg (QuotientGroup.mk' (center f.range)) (Subtype.ext hy)
  have hkerψ : ψ.ker = center Y := by
    ext y
    rw [MonoidHom.mem_ker, hψ, mk'_eq_one_iff']
    constructor
    · intro hc
      refine mem_center_of_commutator_mem y f.ker (fun z hz => hker hz) (fun g => ?_)
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply Commute.commutator_eq
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc (f.rangeRestrict g))
      exact this.symm
    · intro hyc
      refine Subgroup.mem_center_iff.mpr (fun r => Subtype.ext ?_)
      obtain ⟨g, hgr⟩ := MonoidHom.mem_range.mp r.2
      have hgy : g * y = y * g := Subgroup.mem_center_iff.mp hyc g
      show (r : Q) * f y = f y * (r : Q)
      rw [← hgr, ← map_mul, ← map_mul, hgy]
  let e : Y ⧸ center Y ≃* f.range ⧸ center f.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
  refine ⟨?_, ⟨e.symm⟩⟩
  unfold CFSG.IsQuasisimple
  refine ⟨Group.IsPerfect.range f, e.symm.isSimpleGroup, e a0, e b0, fun h => hab0 ?_⟩
  have h' := congrArg e.symm h
  simpa using h'

theorem exists_quasisimple_lift {M : Type*} [Group M] (C : Subgroup M) [C.Normal]
    (hC : C ≤ center M) (K : Subgroup (M ⧸ C)) (hK : CFSG.IsQuasisimple K) :
    ∃ Y : Subgroup M, CFSG.IsQuasisimple Y ∧ Nonempty (↥Y ⧸ center ↥Y ≃* ↥K ⧸ center ↥K) := by
  have hker : (QuotientGroup.mk' C : M →* M ⧸ C).ker ≤ center M := by
    rw [QuotientGroup.ker_mk']
    exact hC
  have hKf : K ≤ (QuotientGroup.mk' C : M →* M ⧸ C).range := by
    rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective C)]
    exact le_top
  obtain ⟨Y, hYq, -, -, he⟩ :=
    exists_quasisimple_lift_of_hom (QuotientGroup.mk' C) hker K hK hKf
  exact ⟨Y, hYq, he⟩

end CFSG.ComponentClassification.CatFC.KGHS3
