module

public import CFSG.ClassicalInvolution.Q3.Q3URStd
public import CFSG.ClassicalInvolution.Q3.Q3TY2
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped MatrixGroups

theorem pow_twelve_blockEmb2_three (i : Fin 3) :
    ∀ y ∈ (blockEmb2 (GaloisField 3 2) 3 1 3 i).range, y ^ 12 = 1 := by
  rintro _ ⟨A, rfl⟩
  rw [← map_pow, su2_pow_twelve A, map_one]

theorem tripleLift3 {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) (hO3 : ¬ 3 ∣ Nat.card O)
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4))
    {A B C : Subgroup Y} (hA : ∀ a ∈ A, a ^ 12 = 1) (hB : ∀ b ∈ B, b ^ 12 = 1)
    (hC : ∀ c ∈ C, c ^ 12 = 1) (θb : Su (GaloisField 3 2) 3 1 4 →* Y ⧸ O)
    (hker : θb.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4))
    (hA' : (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θb = A.map (QuotientGroup.mk' O))
    (hB' : (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θb = B.map (QuotientGroup.mk' O))
    (hC' : (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θb = C.map (QuotientGroup.mk' O)) :
    ∃ θ : Su (GaloisField 3 2) 3 1 4 →* Y, θ.range = (A ⊔ B) ⊔ (B ⊔ C) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = A ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = B ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = C := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  have hq2 : 3 ^ 1 ≠ 2 := by norm_num
  have : Group.IsPerfect (Su (GaloisField 3 2) 3 1 4) := isPerfect_su_three_le (by norm_num)
  let π := QuotientGroup.mk' O
  let P : Subgroup Y := (A ⊔ B) ⊔ (B ⊔ C)
  let π' : ↥P →* Y ⧸ O := π.comp P.subtype
  have hrange' : π'.range = (A.map π ⊔ B.map π) ⊔ (B.map π ⊔ C.map π) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_sup, Subgroup.map_sup,
      Subgroup.map_sup]
  have hgen : θb.range = A.map π ⊔ B.map π ⊔ C.map π := by
    rw [MonoidHom.range_eq_map, ← sup_range_blockEmb2_three hK hq2, Subgroup.map_sup,
      Subgroup.map_sup, hA', hB', hC']
  have hθ : ∀ s, θb s ∈ π'.range := fun s => by
    rw [hrange']
    have h1 : θb s ∈ θb.range := ⟨s, rfl⟩
    rw [hgen] at h1
    have hle : A.map π ⊔ B.map π ⊔ C.map π ≤ (A.map π ⊔ B.map π) ⊔ (B.map π ⊔ C.map π) :=
      sup_le le_sup_left (le_sup_of_le_right le_sup_right)
    exact hle h1
  have hZc : π'.ker ≤ Subgroup.center ↥P := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hdvd : Nat.card π'.ker ∣ Nat.card O := by
    let g : π'.ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  have hQ : Odd (Nat.card π'.ker) ∧ ¬ 3 ∣ Nat.card π'.ker :=
    ⟨hOodd.of_dvd_nat hdvd, fun h3 => hO3 (h3.trans hdvd)⟩
  let θc : Su (GaloisField 3 2) 3 1 4 →* π'.range := θb.codRestrict π'.range hθ
  have hdivQ : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ 3 ∣ n) → (Odd m ∧ ¬ 3 ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  obtain ⟨β, hβ⟩ := exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ 3 ∣ n) hdivQ hN
    π'.rangeRestrict π'.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hZc)
    (by rw [MonoidHom.ker_rangeRestrict]; exact hQ) θc
  let θY : Su (GaloisField 3 2) 3 1 4 →* Y := P.subtype.comp β
  have hπθ : ∀ x, π (θY x) = θb x := by
    intro x
    have h1 : π'.rangeRestrict (β x) = θc x := DFunLike.congr_fun hβ x
    have h2 : ((π'.rangeRestrict (β x) : π'.range) : Y ⧸ O) = θb x := by
      rw [h1]
      rfl
    exact h2
  have hπθY : π.comp θY = θb := MonoidHom.ext hπθ
  have hker0 : π.ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hOc
  have hcop : ∀ n ∈ π.ker, Nat.Coprime (orderOf n) 6 := by
    intro n hn
    rw [QuotientGroup.ker_mk'] at hn
    exact orderOf_coprime_six hOodd hO3 hn
  have hX : ∀ (i : Fin 3) (U : Subgroup Y), (∀ u ∈ U, u ^ 12 = 1) →
      (blockEmb2 (GaloisField 3 2) 3 1 3 i).range.map θb = U.map π →
      (blockEmb2 (GaloisField 3 2) 3 1 3 i).range.map θY = U := by
    intro i U hU hmap
    have hS12 : ∀ y ∈ (blockEmb2 (GaloisField 3 2) 3 1 3 i).range.map θY, y ^ 12 = 1 := by
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_pow, pow_twelve_blockEmb2_three i s hs, map_one]
    have hmap' : ((blockEmb2 (GaloisField 3 2) 3 1 3 i).range.map θY).map π = U.map π := by
      rw [Subgroup.map_map, hπθY]
      exact hmap
    refine le_antisymm ?_ ?_
    · refine le_of_map_le_of_exponent π hker0 hcop hS12 hU fun l hl => ?_
      rw [← hmap']
      exact ⟨l, hl, rfl⟩
    · refine le_of_map_le_of_exponent π hker0 hcop hU hS12 fun l hl => ?_
      rw [hmap']
      exact ⟨l, hl, rfl⟩
  have e0 := hX 0 A hA hA'
  have e1 := hX 1 B hB hB'
  have e2 := hX 2 C hC hC'
  refine ⟨θY, ?_, ?_, e0, e1, e2⟩
  · have hsup : A ⊔ B ⊔ C = (A ⊔ B) ⊔ (B ⊔ C) := by
      apply le_antisymm
      · exact sup_le le_sup_left (le_sup_of_le_right le_sup_right)
      · exact sup_le le_sup_left (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
    rw [MonoidHom.range_eq_map, ← sup_range_blockEmb2_three hK hq2, Subgroup.map_sup,
      Subgroup.map_sup, e0, e1, e2, hsup]
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hπθ, MonoidHom.mem_ker.mp hx, map_one]

theorem tripleOfLocImg3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hN : NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4))
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {L₀ L₁ L₂ : Subgroup G}
    (h₀ : L₀ ∈ centralizingMembers Ω {x}) (h₁ : L₁ ∈ centralizingMembers Ω {x})
    (h₂ : L₂ ∈ centralizingMembers Ω {x}) (θb : Su (GaloisField 3 2) 3 1 4 →* locQuot Ω x)
    (hker : θb.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4))
    (e₀ : (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θb = locImg Ω x L₀)
    (e₁ : (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θb = locImg Ω x L₁)
    (e₂ : (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θb = locImg Ω x L₂) :
    ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (L₀ ⊔ L₁) ⊔ (L₁ ⊔ L₂) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = L₀ ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = L₁ ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = L₂ := by
  have hexp : ∀ M ∈ centralizingMembers Ω {x},
      ∀ m ∈ M.subgroupOf (locLayer Ω x), m ^ 12 = 1 := by
    intro M hM m hm
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    have := pow_twelve_of_exact hz (hex M hM.1) (m : G) (Subgroup.mem_subgroupOf.mp hm)
    exact Subtype.ext (by simpa using this)
  obtain ⟨θ, hθr, hθk, f₀, f₁, f₂⟩ := tripleLift3
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) hO3 hN (hexp L₀ h₀) (hexp L₁ h₁)
    (hexp L₂ h₂) θb hker e₀ e₁ e₂
  have hmapsub : ∀ M : Subgroup G, M ∈ centralizingMembers Ω {x} →
      (M.subgroupOf (locLayer Ω x)).map (locLayer Ω x).subtype = M := fun M hM => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_centralizingLayer hM)]
  refine ⟨(locLayer Ω x).subtype.comp θ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hθr, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup,
      hmapsub L₀ h₀, hmapsub L₁ h₁, hmapsub L₂ h₂]
  · intro s hs
    apply hθk
    rw [MonoidHom.mem_ker] at hs ⊢
    exact Subtype.ext hs
  · rw [← Subgroup.map_map, f₀, hmapsub L₀ h₀]
  · rw [← Subgroup.map_map, f₁, hmapsub L₁ h₁]
  · rw [← Subgroup.map_map, f₂, hmapsub L₂ h₂]


theorem noCover_su4_three :
    NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n) (Su (GaloisField 3 2) 3 1 4) := by
  obtain ⟨e, -⟩ := CFSG.ClassicalInvolution.WeakCT.SU4.su4SpinMinus_exists (p := 3) (f := 1)
    (by norm_num) one_ne_zero (CFSG.LieType.Universal.minusCoeffs_irr 3 1)
  exact NoCover.of_mulEquiv e
    (Q3TY.spinMinus6_three_noCover (CFSG.LieType.Universal.minusCoeffs_irr 3 1))

end CFSG.ClassicalInvolution.Q3.Q3W
