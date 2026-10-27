module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Visible

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem ncard_commuting_J (S : RouteDSetup p f K z) (hT : IsTwinAt (𝒞 K) K T z)
    (A : AtT p f K T J z t tY nY) (e : TwinElt K T z) (htJ : t ∈ J)
    {ã ã' : (modelUniv tY nY p f Fact.out).K} (huY : e.u ∈ locLayer (𝒞 K) t)
    (hψu : A.d.ψ (ã * ã') = locMk (𝒞 K) t ⟨e.u, huY⟩) :
    Set.ncard {N : Subgroup G | N ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes N J} =
      1 + Nat.card {R : Subgroup (modelUniv tY nY p f Fact.out).K //
        R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
          R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY p f Fact.out).K)} := by
  classical
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  have hJ₂u : A.J₂ ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  have hJ₂c : Commutes A.J₂ J := A.hJ₂iso J A.hJt A.hJ₂J.symm
  let W' : Set (Subgroup G) :=
    {N | N ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes N J ∧ N ≠ A.J₂}
  have hW : {N : Subgroup G | N ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes N J} =
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
  let Ftgt : Set (Subgroup (modelUniv tY nY p f Fact.out).K) :=
    {R | R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
      R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY p f Fact.out).K)}
  have hF : Nat.card {R : Subgroup (modelUniv tY nY p f Fact.out).K //
      R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
        R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY p f Fact.out).K)} =
      Ftgt.ncard := Nat.card_coe_set_eq Ftgt
  rw [hF]
  have hmt : ∀ N ∈ W', N ∈ centralizingMembers (𝒞 K) {t} := by
    rintro N ⟨hN, hNJ, -⟩
    exact ⟨hN.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hNJ y hy t htJ)⟩
  have hbig : ∀ N ∈ W', ∃ R, R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D ∧
      locImg (𝒞 K) t N = R.map A.d.ψ ∧
      R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY p f Fact.out).K) := by
    intro N hNW
    obtain ⟨hN, hNJ, hNJ₂⟩ := hNW
    have hMt := hmt N ⟨hN, hNJ, hNJ₂⟩
    have hNJne : N ≠ J := fun h => hncs J A.hJt.1 (by rw [h] at hNJ; exact hNJ)
    obtain ⟨R, hR, hNR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
      A.hJiso A.hJ₂iso hMt hNJne hNJ₂
    refine ⟨R, hR, hNR, ?_⟩
    have h1 : locImg (𝒞 K) t N ≤ Subgroup.centralizer ({locMk (𝒞 K) t ⟨e.u, huY⟩} : Set _) :=
      (le_centralizer_iff_locImg S.inClass A.hP1 hMt ⟨e.u, huY⟩).mp hN.2
    exact (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf R hR) (ã * ã')).mpr (by
      rw [hψu, ← hNR]
      exact h1)
  choose! R hRmem hRimg hRcent using hbig
  refine Set.ncard_congr (fun N _ => R N) ?_ ?_ ?_
  · intro N hN
    exact ⟨hRmem N hN, hRcent N hN⟩
  · intro N₁ N₂ h₁ h₂ h
    exact locImg_injOn S.inClass A.hP1 (hmt N₁ h₁) (hmt N₂ h₂)
      (by rw [hRimg N₁ h₁, hRimg N₂ h₂, h])
  · rintro R' ⟨hR', hRc⟩
    obtain ⟨L, hLmem, hLR⟩ := mem_locFamily_iff.mp (A.d.mem_fam R' hR')
    have hLJ : L ≠ J := by
      rintro rfl
      exact not_fund_of_isolated S.inClass A.hP1 A.rf A.d hLmem A.hJiso hR' hLR
    have hLJ₂ : L ≠ A.J₂ := by
      rintro rfl
      exact not_fund_of_isolated S.inClass A.hP1 A.rf A.d hLmem A.hJ₂iso hR' hLR
    have hLJc : Commutes L J := commutes_symm (A.hJiso L hLmem hLJ)
    have hLu : L ≤ Subgroup.centralizer ({e.u} : Set G) :=
      (le_centralizer_iff_locImg S.inClass A.hP1 hLmem ⟨e.u, huY⟩).mpr (by
        rw [hLR, ← hψu]
        exact (le_centralizer_iff_map A.d.ψ A.d.ker_le (A.rf.perf R' hR') (ã * ã')).mp hRc)
    have hLW : L ∈ W' := ⟨⟨hLmem.1, hLu⟩, hLJc, hLJ₂⟩
    refine ⟨L, hLW, ?_⟩
    exact eq_of_map_eq_of_central A.d.ψ A.d.ker_le (A.rf.perf _ (hRmem L hLW))
      (A.rf.perf R' hR') ((hRimg L hLW).symm.trans hLR)

end Visible

end CFSG.ClassicalInvolution.RouteD.TWY
