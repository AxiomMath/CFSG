module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCore
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Foundations.Basic
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR.E1

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Foote5.OddLieCore (oddFixed)

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_of_open {Y X : Subgroup G} (h : CFSG.Open.IsSubnormal Y X) :
    (Y.subgroupOf X).IsSubnormal :=
  h.subgroupOf

theorem isSubnormal_subgroupOf_mono {Y N B : Subgroup G} (hNB : N ≤ B)
    (h : (Y.subgroupOf B).IsSubnormal) : (Y.subgroupOf N).IsSubnormal := by
  have h' := h.comap (inclusion hNB)
  convert h' using 1
  ext x
  simp [mem_subgroupOf]

theorem isSubnormal_subgroupOf_trans {Y A B : Subgroup G} (hYA : Y ≤ A) (hAB : A ≤ B)
    (hY : (Y.subgroupOf A).IsSubnormal) (hA : (A.subgroupOf B).Normal) :
    (Y.subgroupOf B).IsSubnormal := by
  refine IsSubnormal.trans (K := A.subgroupOf B)
    (fun x hx => mem_subgroupOf.2 (hYA (mem_subgroupOf.1 hx))) ?_ hA.isSubnormal
  have h' := hY.comap (subgroupOfEquivOfLe hAB).toMonoidHom
  convert h' using 1
  ext x
  simp only [mem_subgroupOf, mem_comap, MulEquiv.coe_toMonoidHom]
  rfl

theorem isSubnormal_subgroupOf_map {G' : Type*} [Group G'] (f : G →* G')
    (hf : Function.Injective f) {Y B : Subgroup G} (hYB : Y ≤ B)
    (h : (Y.subgroupOf B).IsSubnormal) : ((Y.map f).subgroupOf (B.map f)).IsSubnormal := by
  have h' := h.map (f := (B.equivMapOfInjective f hf).toMonoidHom)
    (B.equivMapOfInjective f hf).surjective
  convert h' using 1
  ext x
  rw [mem_subgroupOf, mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨⟨a, hYB ha⟩, mem_subgroupOf.2 ha, Subtype.ext ?_⟩
    simp [hax]
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, mem_subgroupOf.1 hb, rfl⟩

end Subnormal

section Quasisimple

theorem gw_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : GorensteinWalter.IsQuasisimple A) : GorensteinWalter.IsQuasisimple B := by
  obtain ⟨hnt, hp, hs⟩ := hA
  have hc : (center A).map (e : A →* B) = center B := map_center_eq e
  let e' : A ⧸ center A ≃* B ⧸ center B := QuotientGroup.congr _ _ e hc
  refine ⟨e.symm.toEquiv.nontrivial, ?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← map_top_of_surjective (e : A →* B) e.surjective, ← map_commutator, hp]

theorem gw_isQuasisimple_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    GorensteinWalter.IsQuasisimple Q := by
  obtain ⟨hp, hs, a, b, hab⟩ := h
  refine ⟨?_, hp.commutator_eq_top, hs⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a * b, b * a, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem commutator_eq_self_of_gw {G : Type*} [Group G] {Y : Subgroup G}
    (h : GorensteinWalter.IsQuasisimple Y) : ⁅Y, Y⁆ = Y :=
  isPerfect_iff.1 (Group.isPerfect_def.2 h.2.1)

end Quasisimple

section Odd

variable {G : Type*} [Group G]

theorem subsingleton_of_perfect_solvable {Q : Type*} [Group Q] (hp : commutator Q = ⊤)
    [hs : Group.IsSolvable Q] : Subsingleton Q := by
  obtain ⟨n, hn⟩ := hs.solvable
  have htop : ∀ m, derivedSeries Q m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hp]
  rw [htop] at hn
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup Q) := hn ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup Q) := hn ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

theorem le_closure_odd_of_commutator_eq [Finite G] {X : Subgroup G} (hX : ⁅X, X⁆ = X) :
    X ≤ closure {y | y ∈ X ∧ Odd (orderOf y)} := by
  set T := closure {y | y ∈ X ∧ Odd (orderOf y)} with hT
  have hTX : T ≤ X := (closure_le _).2 fun y hy => hy.1
  have hTn : (T.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hmap : T.map (MulAut.conj (g : G)).toMonoidHom ≤ T := by
      rw [hT, MonoidHom.map_closure]
      refine closure_mono ?_
      rintro _ ⟨y, ⟨hyX, hyo⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · exact mul_mem (mul_mem g.2 hyX) (inv_mem g.2)
      · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
        exact hyo
    exact hmap ⟨_, hn, by simp⟩
  let Q := X ⧸ T.subgroupOf X
  have h2 : IsPGroup 2 Q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd hx0
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have hdvd : 2 ^ a ∣ orderOf x := ⟨m, hxm⟩
    have ho := orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd
    rw [hxm, Nat.mul_div_cancel_left _ (pow_pos two_pos a)] at ho
    have hodd : Odd (orderOf ((x : G) ^ 2 ^ a)) := by
      rw [← SubmonoidClass.coe_pow, Subgroup.orderOf_coe, ho]
      exact hm
    have hmem : (x : G) ^ 2 ^ a ∈ T := subset_closure ⟨pow_mem x.2 _, hodd⟩
    simpa using hmem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent Q := h2.isNilpotent
  have hXp : commutator X = ⊤ := Group.isPerfect_def.1 (isPerfect_iff.2 hX)
  have hQp : commutator Q = ⊤ := by
    rw [_root_.commutator_def] at hXp ⊢
    rw [← map_top_of_surjective (QuotientGroup.mk' (T.subgroupOf X))
      (QuotientGroup.mk'_surjective _), ← map_commutator, hXp]
  have hsub := subsingleton_of_perfect_solvable hQp
  intro x hx
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : X) : Q) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

theorem oddFixed_le_fixedSubgroup {S : Type} [Group S] (α : MulAut S) :
    oddFixed α ≤ fixedSubgroup α :=
  (closure_le _).2 fun _ hs => hs.1

end Odd

section Component

variable {S G : Type} [Group S] [Group G]

theorem isComponentOf_oddFixed_of_map [Finite S] (α : MulAut S) (φ : S →* G)
    (hφ : Function.Injective φ) {N Y : Subgroup G} (hmap : (fixedSubgroup α).map φ = N)
    (hYN : Y ≤ N) (hY : (Y.subgroupOf N).IsSubnormal)
    (hq : GorensteinWalter.IsQuasisimple Y) :
    GorensteinWalter.IsComponentOf (Y.comap φ) (oddFixed α) ∧ (Y.comap φ).map φ = Y := by
  set F := fixedSubgroup α with hF
  set X := Y.comap φ with hX
  have hYr : Y ≤ φ.range := hYN.trans (hmap ▸ map_le_range φ F)
  have hXY : X.map φ = Y := map_comap_eq_self hYr
  have hXF : X ≤ F := by
    intro s hs
    have h1 : φ s ∈ F.map φ := by
      rw [hmap]
      exact hYN hs
    obtain ⟨s', hs', he⟩ := h1
    rw [← hφ he]
    exact hs'
  let e : X ≃* Y := (X.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hXY)
  have hXq : GorensteinWalter.IsQuasisimple X := gw_isQuasisimple_of_mulEquiv e.symm hq
  let eF : F ≃* N := (F.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hmap)
  have hXsF : (X.subgroupOf F).IsSubnormal := by
    have h' := hY.comap eF.toMonoidHom
    convert h' using 1
    ext
    simp only [mem_subgroupOf, mem_comap, MulEquiv.coe_toMonoidHom]
    rfl
  have hXo : X ≤ oddFixed α := by
    refine (le_closure_odd_of_commutator_eq (commutator_eq_self_of_gw hXq)).trans ?_
    refine closure_mono ?_
    rintro y ⟨hyX, hyo⟩
    exact ⟨hXF hyX, hyo⟩
  exact ⟨⟨hXo, isSubnormal_subgroupOf_mono (oddFixed_le_fixedSubgroup α) hXsF, hXq⟩, hXY⟩

theorem perfect_even_of_isComponentOf [Finite S] {α : MulAut S} {X : Subgroup S}
    (h : GorensteinWalter.IsComponentOf X (oddFixed α)) :
    X ≤ fixedSubgroup α ∧ ⁅X, X⁆ = X ∧ 2 ∣ Nat.card X := by
  obtain ⟨hXo, -, hq⟩ := h
  refine ⟨hXo.trans (oddFixed_le_fixedSubgroup α), commutator_eq_self_of_gw hq, ?_⟩
  by_contra h2
  have hodd : Odd (Nat.card X) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  have := CFSG.FeitThompson.isSolvable_of_odd_natCard X hodd
  have hsub := subsingleton_of_perfect_solvable hq.2.1
  obtain ⟨a, b, hab⟩ := hq.1
  exact hab (Subsingleton.elim a b)

end Component

end CFSG.ComponentClassification.HarrisLit.L33.SR.E1
