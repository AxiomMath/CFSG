module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddCharComplement
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddCharSylow

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension UnitaryOddCover
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {r : ℕ}

theorem levi_injective :
    Function.Injective ((hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h1 := eq_one_of_hypProj_lHom (h := h) (A := SpecialLinearGroup.toGL A) A.2 hA
  exact Subgroup.mem_bot.mpr (SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm))

variable {E : Type*} [Group E] {θ : E →* hypPSU h r 1}

theorem exists_levi_lift [Fact p.Prime] [Finite E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (hp : IsPGroup p θ.ker) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hr : 2 ≤ r) :
    ∃ Y : Subgroup E, (∀ y ∈ Y, θ y = 1 → y = 1) ∧
      ∀ A : SpecialLinearGroup (Fin r) K, ∃ y ∈ Y,
        θ y = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) := by
  have := h.finite
  have hK25 : 25 ≤ Nat.card K := by
    rw [h.card_eq_sq]
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
  set ι : SpecialLinearGroup (Fin r) K →* hypPSU h r 1 :=
    (hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL) with hιdef
  have hι : Function.Injective ι := levi_injective
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) K) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact CFSG.LinearGroups.special_linear_isPerfect hr (Or.inr ⟨s, hs⟩)
  have : Group.IsPerfect ι.range := Group.IsPerfect.range _
  set H := ι.range.comap θ with hH
  set Y := ⁅H, H⁆ with hY
  obtain ⟨θF, hθF, hθFι⟩ := SymplecticSixCover.exists_derivedComap_cover hθ ι hι
  have hθFker : ∀ z : Y, θF z = 1 ↔ θ z = 1 := fun z => by
    rw [← hθFι, ← map_one ι]
    exact hι.eq_iff.symm
  have : Group.IsPerfect Y := SymplecticSixCover.isPerfect_derivedComap hθ hC _
  have hcenF : θF.ker ≤ Subgroup.center Y := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
  have hpF : IsPGroup p θF.ker := fun z => by
    obtain ⟨n, hn⟩ := hp ⟨(z : Y), (hθFker z).mp z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  have hbot : θF.ker = ⊥ := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ker_eq_bot_of_sl_two_cover hp2 h.card (by rw [← h.card]; omega) θF hθF hcenF hpF
    · exact ker_eq_bot_of_sl_cover_of_three_le (by omega) hr3 θF hθF hcenF
  refine ⟨Y, fun y hy hy1 => ?_, fun A => ?_⟩
  · have hk : (⟨y, hy⟩ : Y) ∈ θF.ker := (hθFker _).mpr hy1
    rw [hbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  · obtain ⟨z, hz⟩ := hθF A
    exact ⟨z, z.2, by rw [← hθFι, hz]; rfl⟩

theorem ker_eq_bot_of_hypPSU [Fact p.Prime] [Finite E] [Group.IsPerfect E]
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (hp : IsPGroup p θ.ker)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hr : 2 ≤ r) : θ.ker = ⊥ := by
  obtain ⟨M₀, hM₀N, hM₀inj, hM₀surj, hM₀norm⟩ := exists_radical_complement hθ hC hq hr hp
  obtain ⟨Y, hYinj, hYsurj⟩ := exists_levi_lift hθ hC hp hp2 hq hr
  exact ker_eq_bot_of_lifts hθ hC hp (by omega) M₀ hM₀N hM₀inj hM₀surj hM₀norm Y hYinj
    fun A _ => hYsurj A

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverOddChar

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ClassicalGroups.UnitaryFlag

theorem odd_odd_dimensional_unitary_catalog_perfect_central_p_cover_trivial {E : Type*}
    {J : Type} [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp : IsPGroup p η.ker) {r f : ℕ} (hr : 2 ≤ r) (hq : 5 ≤ p ^ f)
    (hJ : CFSG.Blueprint.LieModel J .PSU (2 * r + 1) p f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · rw [pow_zero] at hq
        omega
      · exact hf
    have h : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 1) h
    let φ : hypPSU h r 1 ≃* J := (hypPSUEquivStatedProj h hR (by omega)).trans e.symm
    set η' : E →* hypPSU h r 1 := φ.symm.toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact φ.symm.map_eq_one_iff
    have hbot := UnitaryOddCoverOddChar.ker_eq_bot_of_hypPSU (φ.symm.surjective.comp hη)
      (hker ▸ hC) (hker ▸ hp) hp2 hq hr
    rw [hker] at hbot
    exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
