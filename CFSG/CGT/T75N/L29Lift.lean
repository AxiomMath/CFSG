module

public import CFSG.CGT.T75N.L29Central
public import CFSG.CGT.T75N.L29Natural
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.LieType.Steinberg.CentralExt.TorusLift

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups
open scoped commutatorElement

theorem even_card_of_pow {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [Finite V]
    {n : ℕ} (hn : n ≠ 0) (hcard : Nat.card V = Nat.card F ^ n) : Even (Nat.card V) := by
  have := Fintype.ofFinite F
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  rw [hcard, hq, ← pow_mul]
  exact Nat.even_pow.2 ⟨even_two, Nat.mul_ne_zero f.ne_zero hn⟩

theorem lemma29_core
    {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    {Y : Type} [Group Y] [Finite Y] (hperf : commutator Y = ⊤)
    (ε : Y ⧸ Subgroup.center Y ≃* PSL(m + 2, F))
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = Nat.card F ^ (m + 2))
    (ρ : Y →* MulAut V) (hρ : ρ.ker ≤ Subgroup.center Y)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ y : Y, ρ y v = w) :
    ∃ π : Y →* SpecialLinearGroup (Fin (m + 2)) F, Function.Surjective π ∧ π.ker = ρ.ker ∧
      (∀ y : Y, (QuotientGroup.mk (π y) : PSL(m + 2, F)) = ε (QuotientGroup.mk y)) ∧
      ∃ α : SpecialLinearGroup (Fin (m + 2)) F →* SpecialLinearGroup (Fin (m + 2)) F,
        (∀ g, α (α g) = g) ∧ ∃ φ : V ≃* Multiplicative (Fin (m + 2) → F),
          ∀ (y : Y) (v : V), φ (ρ y v) = Multiplicative.ofAdd
            ((α (π y) : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ Multiplicative.toAdd (φ v)) := by
  classical
  have hperfY : Group.IsPerfect Y := ⟨hperf⟩
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have : Finite ρ.range := Finite.of_surjective _ hsurj
  have hperfE : Group.IsPerfect ρ.range := Group.IsPerfect.ofSurjective hsurj
  let π₀ : Y →* PSL(m + 2, F) := ε.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hπ₀ker : π₀.ker = Subgroup.center Y := by
    ext y
    rw [MonoidHom.mem_ker]
    show ε (QuotientGroup.mk y) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hπ₀surj : Function.Surjective π₀ :=
    ε.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center Y))
  have hker : ρ.rangeRestrict.ker ≤ π₀.ker := by
    rw [MonoidHom.ker_rangeRestrict, hπ₀ker]
    exact hρ
  let π : ρ.range →* PSL(m + 2, F) :=
    (ρ.rangeRestrict.liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj)) ⟨π₀, hker⟩
  have hπ : ∀ y, π (ρ.rangeRestrict y) = π₀ y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y
  have hπsurj : Function.Surjective π := by
    intro p
    obtain ⟨y, hy⟩ := hπ₀surj p
    exact ⟨ρ.rangeRestrict y, by rw [hπ, hy]⟩
  have hπcen : π.ker ≤ Subgroup.center ρ.range := by
    intro x hx
    obtain ⟨y, rfl⟩ := hsurj x
    rw [MonoidHom.mem_ker, hπ] at hx
    have hy : y ∈ Subgroup.center Y := by
      rw [← hπ₀ker]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y', rfl⟩ := hsurj z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hy y']
  have htrE : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ h ∈ ρ.range, h v = w := by
    intro v w hv hw
    obtain ⟨y, hy⟩ := htrans v w hv hw
    exact ⟨ρ y, ⟨y, rfl⟩, hy⟩
  have hodd : Odd (Nat.card π.ker) :=
    odd_card_of_le_center (even_card_of_pow (by omega) hcard) ρ.range htrE π.ker hπcen
  obtain ⟨α', hα', -⟩ := CFSG.SectionRank.EvenCover.even_linear_existsUnique_lift
    (K := F) (n := m + 2) (by omega) hπsurj hπcen hodd
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 2)) F)))
  have hα'' : ∀ s, π (α' s) = QuotientGroup.mk s := fun s => by
    have := congrArg (fun f => f s) hα'
    exact this
  have hαsurj : Function.Surjective α' := by
    have hcomm : ∀ x y : ρ.range, ⁅x, y⁆ ∈ α'.range := by
      intro x y
      obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (π x)
      obtain ⟨s', hs'⟩ := QuotientGroup.mk_surjective (π y)
      have h1 : π x = π (α' s) := by rw [hα'' s, hs]
      have h2 : π y = π (α' s') := by rw [hα'' s', hs']
      rw [CFSG.LieType.Steinberg.CentralExt.TorusLift.commutatorElement_eq_of_map_eq hπcen h1 h2,
        ← map_commutatorElement]
      exact ⟨_, rfl⟩
    have hrange : α'.range = ⊤ := by
      rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := ρ.range), commutator_def,
        Subgroup.commutator_le]
      intro x _ y _
      exact hcomm x y
    intro x
    have hx : x ∈ α'.range := by
      rw [hrange]
      trivial
    exact hx
  let σ : SpecialLinearGroup (Fin (m + 2)) F →* MulAut V := ρ.range.subtype.comp α'
  have htrσ : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ g, σ g v = w := by
    intro v w hv hw
    obtain ⟨y, hy⟩ := htrans v w hv hw
    obtain ⟨s, hs⟩ := hαsurj (ρ.rangeRestrict y)
    refine ⟨s, ?_⟩
    have : σ s = ρ y := by
      show ((α' s : ρ.range) : MulAut V) = ρ y
      rw [hs]
      rfl
    rw [this]
    exact hy
  obtain ⟨α, hαα, φ, hφ⟩ := transitive_natural hV2 hcard σ htrσ
  have hσinj := injective_of_natural σ α hαα φ hφ
  have hαinj : Function.Injective α' := fun a b hab => hσinj (by
    show ((α' a : ρ.range) : MulAut V) = ((α' b : ρ.range) : MulAut V)
    rw [hab])
  let e' : SpecialLinearGroup (Fin (m + 2)) F ≃* ρ.range := MulEquiv.ofBijective α' ⟨hαinj, hαsurj⟩
  let πY : Y →* SpecialLinearGroup (Fin (m + 2)) F := e'.symm.toMonoidHom.comp ρ.rangeRestrict
  have hπY : ∀ y, α' (πY y) = ρ.rangeRestrict y := by
    intro y
    exact e'.apply_symm_apply _
  refine ⟨πY, e'.symm.surjective.comp hsurj, ?_, ?_, α, hαα, φ, ?_⟩
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show e'.symm (ρ.rangeRestrict y) = 1 ↔ ρ y = 1
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      have := congrArg Subtype.val h
      simpa using this
    · intro h
      exact Subtype.ext h
  · intro y
    rw [← hα'', hπY, hπ]
    rfl
  · intro y v
    have hσ : σ (πY y) = ρ y := by
      show ((α' (πY y) : ρ.range) : MulAut V) = ρ y
      rw [hπY]
      rfl
    rw [← hσ]
    exact hφ (πY y) v

end CFSG.CGT.T75N
