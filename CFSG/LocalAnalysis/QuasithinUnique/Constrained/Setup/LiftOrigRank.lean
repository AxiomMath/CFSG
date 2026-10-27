module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSectionRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.QuasithinUnique.Setup

section S3

abbrev SL2F2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

def sl2Vec3 : Fin 3 → (Fin 2 → ZMod 2) := ![![1, 0], ![0, 1], ![1, 1]]

def sl2Lab (v : Fin 2 → ZMod 2) : Fin 3 :=
  if v = ![1, 0] then 0 else if v = ![0, 1] then 1 else 2

def sl2Act (g : SL2F2) (i : Fin 3) : Fin 3 :=
  sl2Lab ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (sl2Vec3 i))

theorem sl2Act_bij : ∀ g : SL2F2, Function.Bijective (sl2Act g) := by decide +kernel

theorem sl2Act_mul : ∀ (g h : SL2F2) (i : Fin 3), sl2Act (g * h) i = sl2Act g (sl2Act h i) := by
  decide +kernel

theorem sl2Act_one : ∀ i : Fin 3, sl2Act 1 i = i := by decide +kernel

noncomputable def sl2ToPerm3 : SL2F2 →* Equiv.Perm (Fin 3) where
  toFun g := Equiv.ofBijective (sl2Act g) (sl2Act_bij g)
  map_one' := Equiv.ext sl2Act_one
  map_mul' g h := Equiv.ext fun i => sl2Act_mul g h i

theorem sl2ToPerm3_bijective : Function.Bijective sl2ToPerm3 := by
  have hinj : Function.Injective sl2ToPerm3 := by
    intro g h hgh
    have : ∀ g h : SL2F2, (∀ i, sl2Act g i = sl2Act h i) → g = h := by decide +kernel
    exact this g h fun i => congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) hgh
  refine ⟨hinj, ?_⟩
  have h1 : Nat.card SL2F2 = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h2 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  exact (Function.Injective.bijective_of_nat_card_le hinj (by rw [h1, h2])).2

noncomputable def sl2F2EquivPerm3 : SL2F2 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective sl2ToPerm3 sl2ToPerm3_bijective

theorem sl2_map_castHom_injective {F : Type*} [Field F] [CharP F 2] :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (ZMod.castHom (dvd_refl 2) F)) := by
  intro g h hgh
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F => x i j) hgh
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact (ZMod.castHom (dvd_refl 2) F).injective this

theorem exists_section_symThree_pow {P Λ : Type*} [Group P] [Group Λ] (ρ : P →* Λ) {F : Type*}
    [Field F] [CharP F 2] {r : ℕ} (Lc : Fin r → Subgroup Λ) (hrange : ∀ i, Lc i ≤ ρ.range)
    (hiso : ∀ i, Nonempty (↥(Lc i) ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Lc i, ∀ y ∈ Lc j, x * y = y * x)
    (hind : ∀ i, Lc i ⊓ (⨆ j, ⨆ (_ : j ≠ i), Lc j) = ⊥) :
    ∃ (Y₀ : Subgroup P) (f : ↥Y₀ →* (Fin r → Equiv.Perm (Fin 3))), Function.Surjective f := by
  classical
  let κ : SL2F2 →* Matrix.SpecialLinearGroup (Fin 2) F :=
    Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F)
  have hκ : Function.Injective κ := sl2_map_castHom_injective
  let θ : ∀ i, ↥(Lc i) ≃* Matrix.SpecialLinearGroup (Fin 2) F := fun i => (hiso i).some
  let ι : ∀ i, SL2F2 →* Λ := fun i => (Lc i).subtype.comp ((θ i).symm.toMonoidHom.comp κ)
  have hιinj : ∀ i, Function.Injective (ι i) := fun i =>
    (Lc i).subtype_injective.comp ((θ i).symm.injective.comp hκ)
  have hιle : ∀ i g, ι i g ∈ Lc i := fun i g => ((θ i).symm (κ g)).2
  have hcommι : Pairwise fun i j => ∀ (x : SL2F2) (y : SL2F2), Commute (ι i x) (ι j y) :=
    fun i j hij x y => hcomm i j hij _ (hιle i x) _ (hιle j y)
  have hindι : iSupIndep fun i => (ι i).range := by
    rw [iSupIndep_def]
    intro i
    rw [disjoint_iff, eq_bot_iff, ← hind i]
    refine inf_le_inf ?_ (iSup₂_mono fun j _ => ?_)
    · rintro _ ⟨g, rfl⟩
      exact hιle i g
    · rintro _ ⟨g, rfl⟩
      exact hιle j g
  let Φ : (Fin r → SL2F2) →* Λ := MonoidHom.noncommPiCoprod ι hcommι
  have hΦinj : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ι hindι hιinj
  have hΦrange : Φ.range ≤ ρ.range := by
    rw [show Φ.range = ⨆ i, (ι i).range from MonoidHom.noncommPiCoprod_range ι]
    refine iSup_le fun i => ?_
    rintro _ ⟨g, rfl⟩
    exact hrange i (hιle i g)
  let Y₀ : Subgroup P := Φ.range.comap ρ
  let g : ↥Y₀ →* ↥Φ.range := (ρ.comp Y₀.subtype).codRestrict Φ.range (fun y => y.2)
  have hg : Function.Surjective g := by
    rintro ⟨s, hs⟩
    obtain ⟨p, hp⟩ := hΦrange hs
    exact ⟨⟨p, show ρ p ∈ Φ.range by rw [hp]; exact hs⟩, Subtype.ext hp⟩
  let e : (Fin r → SL2F2) ≃* ↥Φ.range := MonoidHom.ofInjective hΦinj
  let π : (Fin r → SL2F2) ≃* (Fin r → Equiv.Perm (Fin 3)) :=
    MulEquiv.piCongrRight fun _ => sl2F2EquivPerm3
  refine ⟨Y₀, π.toMonoidHom.comp (e.symm.toMonoidHom.comp g), ?_⟩
  exact π.surjective.comp (e.symm.surjective.comp hg)

end S3

section Rank

variable {G : Type} [Group G] [Finite G]

theorem rank_le_of_sl2_family {X V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    {F : Type} [Field F] [CharP F 2] {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hle : ∀ i, Lc i ≤ autOn X V)
    (hiso : ∀ i, Nonempty (↥(Lc i) ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Lc i, ∀ y ∈ Lc j, x * y = y * x)
    (hind : ∀ i, Lc i ⊓ (⨆ j, ⨆ (_ : j ≠ i), Lc j) = ⊥) : r ≤ CFSG.pRank 3 X := by
  have hrange : ∀ i, Lc i ≤ (rho V X hX).range := fun i => by
    rw [range_rho hX]
    exact hle i
  obtain ⟨Y₀, f, hf⟩ := exists_section_symThree_pow (rho V X hX) Lc hrange hiso hcomm hind
  exact sym_three_pow_section_forces_three_rank r Y₀ f hf

end Rank

end CFSG.QuasithinUnique.Setup.Lift
