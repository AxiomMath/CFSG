module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Open

@[expose] def GoodSub {X : Type} [Group X] (Q : Subgroup X) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ι : X →* G), Function.Injective ι →
    CharTwo (Q.map ι) ∧ ¬ HasChi0Block (Q.map ι)

theorem GoodSub.of_quotient {X : Type} [Group X] {P : Subgroup X} {T : Type} [Group T]
    (q : ↥P →* T) (hq : Function.Surjective q) (hT : IsSimpleGroup T) (hT2 : ¬ IsPGroup 2 T)
    (hker : IsPGroup 2 q.ker)
    (hC : ∀ x : ↥P, (∀ n : ↥P, n ∈ q.ker → x * n = n * x) → x ∈ q.ker)
    (hord : ¬ Chi0Order (Nat.card T)) : GoodSub P :=
  fun _ _ _ ι hι => charTwo_not_hasChi0Block_map ι hι q hq hT hT2 hker hC hord

theorem GoodSub.of_parabolicFacts {X : Type} [Group X] [Finite X] {P Q : Subgroup X}
    (h : Lie.ParabolicFacts P Q) : GoodSub P :=
  fun _ _ _ ι hι => ⟨(h.map ι hι).charTwo, (h.map ι hι).not_hasChi0Block⟩

section Frame

variable {G : Type} [Group G] [Finite G]

theorem pairConclusion_of_goodPair {L R : Subgroup G} {X : Type} [Group X] (φ : ↥L ≃* X)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) {Q₁ Q₂ : Subgroup X} (h1 : Q₁ ≠ ⊤) (h2 : Q₂ ≠ ⊤)
    (hsup : Q₁ ⊔ Q₂ = ⊤)
    (hinv : ∀ α : MulAut X,
      (((R ⊓ L).subgroupOf L).map φ.toMonoidHom).map α.toMonoidHom =
          ((R ⊓ L).subgroupOf L).map φ.toMonoidHom →
        Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂)
    (hQ₁ : GoodSub Q₁) (hQ₂ : GoodSub Q₂) : PairConclusion L R := by
  let ι : X →* G := L.subtype.comp φ.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.symm.injective
  have hrange : ι.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ.symm x).2
    · intro hg
      exact ⟨φ ⟨g, hg⟩, by simp [ι]⟩
  set S : Subgroup X := ((R ⊓ L).subgroupOf L).map φ.toMonoidHom with hSdef
  have hxS : ∀ x : X, x ∈ S ↔ ((φ.symm x : ↥L) : G) ∈ R := by
    intro x
    rw [hSdef, Subgroup.mem_map_equiv]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, (φ.symm x).2⟩
  have hinvR : ∀ r ∈ R, ∀ Q : Subgroup X,
      (∀ α : MulAut X, S.map α.toMonoidHom = S → Q.map α.toMonoidHom = Q) →
      r ∈ Subgroup.normalizer ((Q.map ι : Subgroup G) : Set G) := by
    intro r hr Q hQ
    let ψ : MulAut ↥L := L.normalizerMonoidHom ⟨r, hRN hr⟩
    let α : MulAut X := φ.symm.trans (ψ.trans φ)
    have hψ : ∀ y : ↥L, ((ψ y : ↥L) : G) = r * (y : G) * r⁻¹ := fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨r, hRN hr⟩ y
    have hια : ∀ x, ι (α x) = r * ι x * r⁻¹ := by
      intro x
      show (((φ.symm (φ (ψ (φ.symm x)))) : ↥L) : G) = r * ((φ.symm x : ↥L) : G) * r⁻¹
      rw [MulEquiv.symm_apply_apply]
      exact hψ _
    have hαx : ∀ x : X, α x ∈ S ↔ x ∈ S := by
      intro x
      rw [hxS, hxS]
      have : ((φ.symm (α x) : ↥L) : G) = r * ((φ.symm x : ↥L) : G) * r⁻¹ := hια x
      rw [this]
      constructor
      · intro h
        have h1 : r⁻¹ * (r * ((φ.symm x : ↥L) : G) * r⁻¹) * r ∈ R :=
          R.mul_mem (R.mul_mem (R.inv_mem hr) h) hr
        simpa [mul_assoc] using h1
      · intro h
        exact R.mul_mem (R.mul_mem hr h) (R.inv_mem hr)
    have hαS : S.map α.toMonoidHom = S := by
      ext y
      rw [Subgroup.mem_map_equiv]
      obtain ⟨x, rfl⟩ := α.surjective y
      rw [MulEquiv.symm_apply_apply]
      exact (hαx x).symm
    have hQα := hQ α hαS
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
    have hcomp : ((MulAut.conj r : MulAut G) : G →* G).comp ι = ι.comp α.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact (hια x).symm
    rw [hcomp, ← Subgroup.map_map, hQα]
  refine ⟨Q₁.map ι, Q₂.map ι, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (hQ₁ G ι hι).1, (hQ₂ G ι hι).1,
    (hQ₁ G ι hι).2, (hQ₂ G ι hι).2⟩
  · exact (Subgroup.map_le_range ι Q₁).trans hrange.le
  · exact (Subgroup.map_le_range ι Q₂).trans hrange.le
  · intro h
    apply h1
    rw [← hrange, MonoidHom.range_eq_map] at h
    exact Subgroup.map_injective hι h
  · intro h
    apply h2
    rw [← hrange, MonoidHom.range_eq_map] at h
    exact Subgroup.map_injective hι h
  · rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, hrange]
  · exact fun r hr => hinvR r hr Q₁ (fun α hα => (hinv α hα).1)
  · exact fun r hr => hinvR r hr Q₂ (fun α hα => (hinv α hα).2)

end Frame

section Invariance

open CFSG.QuasithinUnique.Setup.Family

theorem flagStabilizer_pair_invariant (α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2)))
    (hα : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2)) :
    (flagStabilizer 5 (ZMod 2) {1, 4}).map α.toMonoidHom = flagStabilizer 5 (ZMod 2) {1, 4} ∧
      (flagStabilizer 5 (ZMod 2) {2, 3}).map α.toMonoidHom = flagStabilizer 5 (ZMod 2) {2, 3} := by
  set β : MulAut (projectiveSL 5 (ZMod 2)) :=
    (projEquiv 5).symm.trans (α.trans (projEquiv 5)) with hβ
  have hβp : ∀ x : SpecialLinearGroup (Fin 5) (ZMod 2),
      β (proj 5 (ZMod 2) x) = proj 5 (ZMod 2) (α x) := by
    intro x
    have h1 : proj 5 (ZMod 2) x = projEquiv 5 x := rfl
    have h2 : proj 5 (ZMod 2) (α x) = projEquiv 5 (α x) := rfl
    rw [h1, h2, hβ]
    simp
  have hmap : ∀ Q : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2)),
      (Q.map (proj 5 (ZMod 2))).map β.toMonoidHom = (Q.map α.toMonoidHom).map (proj 5 (ZMod 2)) := by
    intro Q
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hβp x
  have hU : (projUnitriangular 5 (ZMod 2)).map β.toMonoidHom = projUnitriangular 5 (ZMod 2) := by
    rw [projUnitriangular, hmap, hα]
  obtain ⟨h1, h2⟩ := pair_invariant (n := 5) (by norm_num) β hU
  have e1 := map_proj_flagStabilizer_pair (n := 5) 1 (5 - 1)
  have e2 := map_proj_flagStabilizer_pair (n := 5) 2 (5 - 2)
  rw [← e1, hmap] at h1
  rw [← e2, hmap] at h2
  have hinj := Subgroup.map_injective (proj_injective_zmod_two 5)
  exact ⟨hinj h1, hinj h2⟩

end Invariance

end CFSG.QuasithinUnique.Vol2Native.L239.L52
