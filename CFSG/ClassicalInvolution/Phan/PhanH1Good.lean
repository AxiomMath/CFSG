module

public import CFSG.ClassicalInvolution.Phan.PhanB10Family
public import CFSG.ClassicalInvolution.Phan.PhanB3Good

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] {G : Type} [Group G]

structure WeakPhanB3 (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {G : Type} [Group G] (U : Fin 3 → Subgroup G) :
    Prop where
  comm : Commutes (U 0) (U 2)
  unitary : ∃ W, UnitaryBlockStandardPair K p f W (U 0) (U 1)
  symplectic : ∃ θ : StatedSp 2 F →* G, Function.Injective θ ∧
    (longBlock F 2 1).range.map θ = U 1 ∧ (twShort h2).range.map θ = U 2
  disj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥

variable {h2 : (2 : F) ≠ 0} {hK : Nat.card K = (p ^ f) ^ 2} (C : B2Coord hK F h2)

theorem WeakPhanB3.exists_good (hq : 5 ≤ p ^ f) (hmod : p ^ f % 4 = 3) {U : Fin 3 → Subgroup G}
    (hU : WeakPhanB3 K p f h2 U) :
    ∃ E : PhanFamilyB3 C G, GoodFamily E ∧ ∀ i, (E.ι i).range = U i := by
  obtain ⟨hcomm, ⟨W₁, h01⟩, ⟨ϑ, hϑinj, hLϑ, hSϑ⟩, hdisj⟩ := hU
  obtain ⟨θ₀, -, hker0, hU0, hU1⟩ := pair_normalize h01
  obtain ⟨-, hr0, hj, hr1⟩ := pair_block_inj hK hker0 hU0 hU1
  have hkinj : Function.Injective (ϑ.comp C.ℓ) := hϑinj.comp C.ℓ_inj
  have hkrange : (ϑ.comp C.ℓ).range = U 1 := by
    rw [MonoidHom.range_comp, C.ℓ_range, ← hLϑ]
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq hkinj hj (by rw [hkrange, hr1])
  have hαϑ : ∀ g, θ₀ (embSUid (unitaryInvolution K p f) 0 (α g)) = ϑ (C.ℓ g) := fun g => hα g
  have hsrange : C.s.range.map ϑ = U 2 := by rw [C.s_range]; exact hSϑ
  have hq7 : 7 ≤ p ^ f := by omega
  have hcomm' : ∀ x ∈ (B12 K p f).map θ₀, ∀ y ∈ C.s.range.map ϑ, x * y = y * x := by
    rw [hU0, hsrange]
    exact hcomm
  have htor := alpha_torus_le C hq7 hker0 hcomm' α hαϑ
  obtain ⟨β, hβ0, hβ12, hβ23⟩ := exists_mulAut_extend_zero hK α htor
  set θ₁ : Su K p f 3 →* G := θ₀.comp β.toMonoidHom with hθ₁
  have hker1 : θ₁.ker ≤ Subgroup.center (Su K p f 3) := ker_comp_mulEquiv_le_center hker0 β
  have hℓ : ϑ.comp C.ℓ = θ₁.comp (embSUid (unitaryInvolution K p f) 0) := by
    refine MonoidHom.ext fun g => ?_
    show ϑ (C.ℓ g) = θ₀ (β (embSUid (unitaryInvolution K p f) 0 g))
    rw [hβ0, hαϑ]
  have hB12 : (B12 K p f).map θ₁ = U 0 := by
    rw [hθ₁, map_comp_mulEquiv, hβ12, hU0]
  have hB23 : (B23 K p f).map θ₁ = U 1 := by
    rw [hθ₁, map_comp_mulEquiv, hβ23, hU1]
  obtain ⟨hi0, hr0', hi1, hr1'⟩ := pair_block_inj hK hker1 hB12 hB23
  have hr2' : (ϑ.comp C.s).range = U 2 := by
    rw [MonoidHom.range_comp]
    exact hsrange
  have hi2 : Function.Injective (ϑ.comp C.s) := hϑinj.comp C.s_inj
  let E : PhanFamilyB3 C G :=
    ⟨![θ₁.comp (embSUid (unitaryInvolution K p f) 2),
      θ₁.comp (embSUid (unitaryInvolution K p f) 0), ϑ.comp C.s], θ₁, ϑ, rfl, rfl, hℓ, rfl,
      fun a b => by
        have ha : (θ₁.comp (embSUid (unitaryInvolution K p f) 2)) a ∈ U 0 := by
          rw [← hr0']
          exact ⟨a, rfl⟩
        have hb : (ϑ.comp C.s) b ∈ U 2 := by
          rw [← hr2']
          exact ⟨b, rfl⟩
        exact hcomm _ ha _ hb⟩
  have hrange : ∀ i, (E.ι i).range = U i := by
    intro i
    fin_cases i
    · exact hr0'
    · show (θ₁.comp (embSUid (unitaryInvolution K p f) 0)).range = U 1
      rw [← hℓ]
      exact hkrange
    · exact hr2'
  refine ⟨E, ⟨?_, ?_, hker1, ?_⟩, hrange⟩
  · intro i
    fin_cases i
    · exact hi0
    · exact hi1
    · exact hi2
  · intro i j hij
    rw [hrange i, hrange j]
    exact hdisj i j hij
  · rw [(MonoidHom.ker_eq_bot_iff ϑ).mpr hϑinj]
    exact bot_le

end CFSG.ClassicalInvolution.PhanB3
