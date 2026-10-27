module

public import CFSG.ClassicalInvolution.Q3.Q3TIVLayer
public import CFSG.ClassicalInvolution.Q3.Q3WARoot
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Block
public import CFSG.ClassicalInvolution.Q3.Q3NGInv
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.Q3.Q3WAStarMain
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TIV
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)

section Defs

variable {G : Type} [Group G]

@[expose] def phi3 (K T : Subgroup G) (z : G) : Set (Subgroup G) :=
  {N | N ∈ centralizingMembers (conjClass3 K) {z} ∧ N ≠ K ∧ N ≠ T}

@[expose] def xGen3 (K T : Subgroup G) (z : G) : Subgroup G :=
  ⨆ N ∈ phi3 K T z, N

@[expose] def normX3 (K T : Subgroup G) (z : G) : Subgroup G :=
  Subgroup.normalizer (xGen3 K T z : Set G)

theorem mem_normX3_iff {K T : Subgroup G} {z g : G} :
    g ∈ normX3 K T z ↔ conjSub g (xGen3 K T z) = xGen3 K T z :=
  G2D4Models.normalizer_iff_conjSub_eq

theorem conjSub_iSup₂3 (g : G) (s : Set (Subgroup G)) :
    conjSub g (⨆ N ∈ s, N) = ⨆ N ∈ conjSub g '' s, N := by
  rw [iSup_image]
  unfold conjSub
  rw [Subgroup.map_iSup]
  refine iSup_congr fun N => ?_
  rw [Subgroup.map_iSup]

theorem conjSub_le_centralizer_singleton3 {N : Subgroup G} {a : G}
    (h : N ≤ Subgroup.centralizer ({a} : Set G)) (g : G) :
    conjSub g N ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hy)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = (g * a * g⁻¹) * y := by group

theorem isTwinAt_conj3 {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K T : Subgroup G} {z : G}
    (h : IsTwinAt Ω K T z) (g : G) :
    IsTwinAt Ω (conjSub g K) (conjSub g T) (g * z * g⁻¹) where
  mem := by
    rw [centralizingMembers_conj hΩ g z]
    exact ⟨T, h.mem, rfl⟩
  ne := fun hEq => h.ne (conjSub_injective g hEq)
  comm_T := by
    intro N hN hNT
    rw [centralizingMembers_conj hΩ g z] at hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN
    exact (commutes_conjSub_iff g).mpr (h.comm_T N₀ hN₀ fun hEq => hNT (by rw [hEq]))
  comm_K := by
    intro N hN hNK
    rw [centralizingMembers_conj hΩ g z] at hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN
    exact (commutes_conjSub_iff g).mpr (h.comm_K N₀ hN₀ fun hEq => hNK (by rw [hEq]))

end Defs

section Count

variable {G : Type} [Group G] [Finite G] {K T : Subgroup G} {z : G} {tY : StatedLieTag}
  {nY : ℕ}


theorem conjSub_phi_eq3 (c : TwinLoc3 tY nY (conjClass3 K) z) (hKcls : IsClassicalMember3 K z)
    (hT : IsTwinAt (conjClass3 K) K T z) (g : G)
    (hg : ∀ N ∈ phi3 K T z, Commutes (conjSub g K) N) :
    conjSub g '' phi3 K T z = phi3 K T z := by
  classical
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hKΩ, isSubnormal_le hKcls.subnormal⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = conjSub g K := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : G, w = g * z * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨TM, hTMdef⟩ : ∃ TM : Subgroup G, TM = conjSub g T := ⟨_, rfl⟩
  have hMΩ : M ∈ conjClass3 K := by
    rw [hMdef]
    exact c.hΩ.conjInvariant g K hKΩ
  have hTM : IsTwinAt (conjClass3 K) M TM w := by
    rw [hMdef, hTMdef, hw]
    exact isTwinAt_conj3 c.hΩ.conjInvariant hT g
  have hclsw : IsClassicalMember3 M w := by
    rw [hMdef, hw]
    exact hKcls.conj g
  have hMself : ¬ Commutes M M := Q3W.not_commutes_self3 hclsw
  have hgM : ∀ N ∈ phi3 K T z, Commutes M N := by
    intro N hN
    rw [hMdef]
    exact hg N hN
  have hΦw : ∀ N ∈ phi3 K T z, N ∈ centralizingMembers (conjClass3 K) {w} ∧ N ≠ M := by
    intro N hN
    refine ⟨⟨hN.1.1, fun n hn => ?_⟩, fun hEq => hMself (hEq ▸ hgM N hN)⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hgM N hN w hclsw.mem n hn).symm
  have hΦsub : phi3 K T z ⊆ conjSub g '' phi3 K T z := by
    intro N hN
    have hNw : N ∈ {L | L ∈ centralizingMembers (conjClass3 K) {w} ∧ L ≠ M ∧ L ≠ TM} := by
      refine ⟨(hΦw N hN).1, (hΦw N hN).2, fun hEq => ?_⟩
      obtain ⟨L', hL', hL'N, hnc⟩ := c.exists_noncomm_of_ne hKz hT.mem hT.ne.symm hKiso hTiso
        hN.1 hN.2.1 hN.2.2
      have hL'K : L' ≠ K := fun h => hnc (by
        rw [h]
        exact (hKiso N hN.1 hN.2.1).symm)
      have hL'T : L' ≠ T := fun h => hnc (by
        rw [h]
        exact (hTiso N hN.1 hN.2.2).symm)
      have hL'Φ : L' ∈ phi3 K T z := ⟨hL', hL'K, hL'T⟩
      exact hnc (by
        rw [hEq]
        exact hTM.comm_T L' (hΦw L' hL'Φ).1 (fun h => hL'N (by rw [hEq, h])))
    refine ⟨conjSub g⁻¹ N, ⟨⟨c.hΩ.conjInvariant g⁻¹ N hNw.1.1, ?_⟩, ?_, ?_⟩,
      conjSub_conjSub_inv g N⟩
    · have := conjSub_le_centralizer_singleton3 hNw.1.2 g⁻¹
      rwa [show g⁻¹ * w * g⁻¹⁻¹ = z by rw [hw]; group] at this
    · intro h
      apply hNw.2.1
      rw [hMdef, ← h, conjSub_conjSub_inv]
    · intro h
      apply hNw.2.2
      rw [hTMdef, ← h, conjSub_conjSub_inv]
  exact (Set.eq_of_subset_of_ncard_le hΦsub (Set.ncard_image_le (Set.toFinite _))
    (Set.toFinite _)).symm

theorem conjSub_xGen_eq3 (c : TwinLoc3 tY nY (conjClass3 K) z) (hKcls : IsClassicalMember3 K z)
    (hT : IsTwinAt (conjClass3 K) K T z) (g : G)
    (hg : ∀ N ∈ phi3 K T z, Commutes (conjSub g K) N) :
    conjSub g (xGen3 K T z) = xGen3 K T z := by
  unfold xGen3
  rw [conjSub_iSup₂3, conjSub_phi_eq3 c hKcls hT g hg]

end Count

end CFSG.ClassicalInvolution.Q3.Q3TZ
