module

public import CFSG.ClassicalInvolution.Q3.Q3TIYAtT
public import CFSG.ClassicalInvolution.Q3.Q3E8BCent

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn)


section Visible

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem ncard_commuting_J3 (hR : RouteD3Setup K z) (hT : IsTwinAt (conjClass3 K) K T z)
    (A : AtT3 K T J z t tY nY) (e : TwinElt K T z)
    {ã ã' : (modelUniv tY nY 3 1 Nat.prime_three).K} (huY : e.u ∈ locLayer (conjClass3 K) t)
    (hψu : A.c.d.ψ (ã * ã') = Gaps.locMk (conjClass3 K) t ⟨e.u, huY⟩) :
    Set.ncard {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧ Commutes N J} =
      1 + Nat.card {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
        R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
          R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} := by
  classical
  have hncs := not_commutes_self_of_mem3 hR
  have hJ₂u : A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  have hJ₂c : Commutes A.J₂ J := A.hJ₂iso J A.hJt A.hJ₂J.symm
  let W' : Set (Subgroup G) :=
    {N | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧ Commutes N J ∧ N ≠ A.J₂}
  have hW : {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧ Commutes N J} =
      insert A.J₂ W' := by
    ext N
    constructor
    · rintro ⟨hN, hNJ⟩
      by_cases h : N = A.J₂
      · exact Or.inl h
      · exact Or.inr ⟨hN, hNJ, h⟩
    · rintro (rfl | ⟨hN, hNJ, -⟩)
      · exact ⟨hJ₂u, hJ₂c⟩
      · exact ⟨hN, hNJ⟩
  have hnot : A.J₂ ∉ W' := fun h => h.2.2 rfl
  rw [hW, Set.ncard_insert_of_notMem hnot (Set.toFinite _), add_comm]
  congr 1
  let Ftgt : Set (Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K) :=
    {R | R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
      R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)}
  have hF : Nat.card {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
      R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
        R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} =
      Ftgt.ncard := Nat.card_coe_set_eq Ftgt
  rw [hF]
  have hmt : ∀ N ∈ W', N ∈ centralizingMembers (conjClass3 K) {t} := by
    rintro N ⟨hN, hNJ, -⟩
    exact ⟨hN.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hNJ y hy t A.clsJ.mem)⟩
  have hbig : ∀ N ∈ W', ∃ R, R ∈ fundamentalSubgroups tY
      (modelUniv tY nY 3 1 Nat.prime_three).D ∧
      locImg (conjClass3 K) t N = R.map A.c.d.ψ ∧
      R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K) := by
    intro N hNW
    obtain ⟨hN, hNJ, hNJ₂⟩ := hNW
    have hMt := hmt N ⟨hN, hNJ, hNJ₂⟩
    have hNJne : N ≠ J := fun h => hncs J A.hJt.1 (by rw [h] at hNJ; exact hNJ)
    obtain ⟨R, hR', hNR⟩ := A.c.big_of_ne A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso hMt hNJne
      hNJ₂
    refine ⟨R, hR', hNR, ?_⟩
    have h1 : locImg (conjClass3 K) t N ≤
        Subgroup.centralizer ({Gaps.locMk (conjClass3 K) t ⟨e.u, huY⟩} :
          Set (locQuot (conjClass3 K) t)) :=
      (le_centralizer_iff_locImg3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hMt ⟨e.u, huY⟩).mp hN.2
    exact (le_centralizer_iff_map3 A.c.d.ψ A.c.d.ker_le A.c.ker_cop (A.c.rf.y.pow3 R hR')
      (ã * ã')).mpr (by
      rw [hψu, ← hNR]
      exact h1)
  choose! R hRmem hRimg hRcent using hbig
  refine Set.ncard_congr (fun N _ => R N) ?_ ?_ ?_
  · intro N hN
    exact ⟨hRmem N hN, hRcent N hN⟩
  · intro N₁ N₂ h₁ h₂ h
    exact locImg_injOn3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 (hmt N₁ h₁) (hmt N₂ h₂)
      (by rw [hRimg N₁ h₁, hRimg N₂ h₂, h])
  · rintro R' ⟨hR', hRc⟩
    obtain ⟨L, hLmem, hLR⟩ := mem_locFamily_iff.mp (A.c.d.mem_fam R' hR')
    have hLJ : L ≠ J := by
      rintro rfl
      exact A.c.not_fund_of_isolated hLmem A.hJiso hR' hLR
    have hLJ₂ : L ≠ A.J₂ := by
      rintro rfl
      exact A.c.not_fund_of_isolated hLmem A.hJ₂iso hR' hLR
    have hLJc : Commutes L J := (A.hJiso L hLmem hLJ).symm
    have hLu : L ≤ Subgroup.centralizer ({e.u} : Set G) :=
      (le_centralizer_iff_locImg3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hLmem ⟨e.u, huY⟩).mpr (by
        rw [hLR, ← hψu]
        exact (le_centralizer_iff_map3 A.c.d.ψ A.c.d.ker_le A.c.ker_cop (A.c.rf.y.pow3 R' hR')
          (ã * ã')).mp hRc)
    have hLW : L ∈ W' := ⟨⟨hLmem.1, hLu⟩, hLJc, hLJ₂⟩
    refine ⟨L, hLW, ?_⟩
    exact eq_of_map_eq_of_pow3 A.c.d.ψ A.c.d.ker_le A.c.ker_cop
      (A.c.rf.y.pow3 _ (hRmem L hLW)) (A.c.rf.y.pow3 R' hR') ((hRimg L hLW).symm.trans hLR)

end Visible

section Corr

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem exists_corr_commuting3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) (i : ι) (hone : ∀ j : ι, j = i)
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind i)) {J : Subgroup G} (hJ : J ∈ centralizingMembers Ω {x}) :
    ∃ R₀ ∈ (D.kind i).fund, Corr3 Ω x D i J R₀ ∧
      Nat.card {S : Subgroup (D.kind i).G // S ∈ (D.kind i).fund ∧ Commutes S R₀} =
      Set.ncard {N : Subgroup G | N ∈ centralizingMembers Ω {x} ∧ Commutes N J} := by
  have hall : ∀ N ∈ centralizingMembers Ω {x}, N ∈ compMembers3 Ω x D i := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hone j ▸ hj⟩
  obtain ⟨R₀, hR₀⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hall J hJ)
  refine ⟨R₀, hR₀.2.1, hR₀, ?_⟩
  rw [show Nat.card {S : Subgroup (D.kind i).G // S ∈ (D.kind i).fund ∧ Commutes S R₀} =
      Set.ncard {S : Subgroup (D.kind i).G | S ∈ (D.kind i).fund ∧ Commutes S R₀} from
    Nat.card_coe_set_eq _]
  symm
  have hex' : ∀ N ∈ {N : Subgroup G | N ∈ centralizingMembers Ω {x} ∧ Commutes N J},
      ∃ R, Corr3 Ω x D i N R := fun N hN =>
    exists_corr_left3 hΩ hex hP1 hO3 D (hall N hN.1)
  choose! R hR using hex'
  refine Set.ncard_congr (fun N _ => R N) ?_ ?_ ?_
  · intro N hN
    exact ⟨(hR N hN).2.1, (corr_commutes3 hΩ hex hP1 hO3 hk (hR N hN) hR₀).mp hN.2⟩
  · intro N₁ N₂ h₁ h₂ h
    exact corr_unique_right3 hΩ hex hP1 hO3 (hR N₁ h₁) (h ▸ hR N₂ h₂)
  · rintro S ⟨hS, hSc⟩
    obtain ⟨N, hN⟩ := exists_corr_right3 hΩ D hsc hS
    have hNJ : Commutes N J := (corr_commutes3 hΩ hex hP1 hO3 hk hN hR₀).mpr hSc
    refine ⟨N, ⟨hN.1, hNJ⟩, ?_⟩
    exact corr_unique_left3 hk (hR N ⟨hN.1, hNJ⟩) hN

theorem exists_three_fund3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) (i : ι) (hone : ∀ j : ι, j = i)
    (hk : PowCop3 (D.kind i)) {J₁ J₂ J₃ : Subgroup G} (h₁ : J₁ ∈ centralizingMembers Ω {x})
    (h₂ : J₂ ∈ centralizingMembers Ω {x}) (h₃ : J₃ ∈ centralizingMembers Ω {x})
    (n₁₂ : J₁ ≠ J₂) (n₁₃ : J₁ ≠ J₃) (n₂₃ : J₂ ≠ J₃) (c₁₂ : Commutes J₁ J₂)
    (c₁₃ : Commutes J₁ J₃) (c₂₃ : Commutes J₂ J₃) :
    ∃ A ∈ (D.kind i).fund, ∃ B ∈ (D.kind i).fund, ∃ C ∈ (D.kind i).fund, A ≠ B ∧ A ≠ C ∧
      B ≠ C ∧ Commutes A B ∧ Commutes A C ∧ Commutes B C := by
  have hall : ∀ N ∈ centralizingMembers Ω {x}, N ∈ compMembers3 Ω x D i := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hone j ▸ hj⟩
  obtain ⟨A, hA⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hall J₁ h₁)
  obtain ⟨B, hB⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hall J₂ h₂)
  obtain ⟨C, hC⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (hall J₃ h₃)
  refine ⟨A, hA.2.1, B, hB.2.1, C, hC.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact n₁₂ (corr_unique_right3 hΩ hex hP1 hO3 hA hB)
  · rintro rfl
    exact n₁₃ (corr_unique_right3 hΩ hex hP1 hO3 hA hC)
  · rintro rfl
    exact n₂₃ (corr_unique_right3 hΩ hex hP1 hO3 hB hC)
  · exact (corr_commutes3 hΩ hex hP1 hO3 hk hA hB).mp c₁₂
  · exact (corr_commutes3 hΩ hex hP1 hO3 hk hA hC).mp c₁₃
  · exact (corr_commutes3 hΩ hex hP1 hO3 hk hB hC).mp c₂₃

end Corr

end CFSG.ClassicalInvolution.Q3.Q3TIV
