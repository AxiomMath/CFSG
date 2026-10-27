module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExcl
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorFrame
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorTwin

public section

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem torusFixedP_of_node_system (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    {j : Fin 6 → Subgroup G} (hj : NodeSystem p f (edgeD 6) Ω K z j)
    (hjimg : ∀ a, locImg Ω z (j a) =
      (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (hβ0 : Commutes β (j 0)) (ht : t * z * t⁻¹ = z) :
    TorusFixedP (by norm_num : 3 ≤ 6) c ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f
      Fact.out).D.rank) ht := by
  classical
  have hΩ := c.hΩ
  have hp : p.Prime := Fact.out
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hadm : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.mpr c.hf, by norm_num⟩
  have hF := Gaps.orthFacts_plus (p := p) (f := f) (m := 6) c.hp2 (by norm_num) c.hq
  have hMz : j 0 ∈ centralizingMembers Ω {z} := hj.mem 0
  obtain ⟨xM, hxM⟩ := hΩ.classical (j 0) hMz.1
  obtain ⟨j', hj', hj'0, hj'1⟩ := c.exists_nodeSystem_of_pair hsingle hshape hβ htβ hKβ hMz.1 hxM
    (hj.commK 0) hβ0
  have hj'0' : j' 0 = K := hj'0
  have hj'1' : j' 1 = β := hj'1
  have hKN : ∀ a : Fin 6, ¬ edgeD 6 0 a → ¬ edgeD 6 a 0 → a ≠ 0 → Commutes K (j' a) := by
    intro a h1 h2' h3
    have := hj'.comm 0 a (Ne.symm h3) h1 h2'
    rwa [hj'0'] at this
  have hβN : ∀ a : Fin 6, ¬ edgeD 6 1 a → ¬ edgeD 6 a 1 → a ≠ 1 → Commutes β (j' a) := by
    intro a h1 h2' h3
    have := hj'.comm 1 a (Ne.symm h3) h1 h2'
    rwa [hj'1'] at this
  have hmem : ∀ a : Fin 6, Commutes K (j' a) → j' a ∈ centralizingMembers Ω {z} := fun a h =>
    mem_centralizingMembers_of_commutes (hj'.mem a).1 c.hz.mem (commutes_symm h)
  have hK3 := hKN 3 (by decide) (by decide) (by decide)
  have hK4 := hKN 4 (by decide) (by decide) (by decide)
  have hK5 := hKN 5 (by decide) (by decide) (by decide)
  have hβ3 := hβN 3 (by decide) (by decide) (by decide)
  have hβ4 := hβN 4 (by decide) (by decide) (by decide)
  have hβ5 := hβN 5 (by decide) (by decide) (by decide)
  have hz3 := hmem 3 hK3
  have hz4 := hmem 4 hK4
  have hz5 := hmem 5 hK5
  obtain ⟨W34, hW34⟩ := hj'.pair 3 4 (by decide)
  obtain ⟨W35, hW35⟩ := hj'.pair 3 5 (by decide)
  have hW43 := CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW34
  have hc45 : Commutes (j' 4) (j' 5) := hj'.comm 4 5 (by decide) (by decide) (by decide)
  have hL3 : IsLayerMember c (j' 3) := IsLayerMember.of_not_commutes c hz3 hz4
    (ne_of_linearBlockStandardPair hW34) (not_commutes_of_linearBlockStandardPair hW34)
  have hL4 : IsLayerMember c (j' 4) := IsLayerMember.of_not_commutes c hz4 hz3
    (ne_of_linearBlockStandardPair hW43) (not_commutes_of_linearBlockStandardPair hW43)
  have hW53 := CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW35
  have hL5 : IsLayerMember c (j' 5) := IsLayerMember.of_not_commutes c hz5 hz3
    (ne_of_linearBlockStandardPair hW53) (not_commutes_of_linearBlockStandardPair hW53)
  obtain ⟨R3, hR3, h3R⟩ := hL3.exists_fund
  obtain ⟨R4, hR4, h4R⟩ := hL4.exists_fund
  obtain ⟨R5, hR5, h5R⟩ := hL5.exists_fund
  obtain ⟨w3, hw3⟩ := hΩ.classical _ hz3.1
  obtain ⟨w4, hw4⟩ := hΩ.classical _ hz4.1
  obtain ⟨w5, hw5⟩ := hΩ.classical _ hz5.1
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadm
  have hRM : rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup
      ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank) ∈
      fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D :=
    rankOne_mem_fundamental _ (hl _ trivial)
  have hMcomm : ∀ (a : Fin 6) (R : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K),
      j' a ∈ centralizingMembers Ω {z} → locImg Ω z (j' a) = R.map c.d.ψ →
      Commutes (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup
        ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f Fact.out).D.rank)) R := by
    intro a R hz hR
    exact (c.commutes_iff_fund hMz hz hRM (hjimg 0) hR).mp (hj'.commK a)
  have hlin : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K},
      L ∈ centralizingMembers Ω {z} → L' ∈ centralizingMembers Ω {z} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D →
      R' ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D →
      locImg Ω z L = R.map c.d.ψ → locImg Ω z L' = R'.map c.d.ψ →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W L L') →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W R R' := by
    intro L L' R R' hL hL' hR hR' hLR hLR' ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members c.hP1 hL hL' hW
    rw [hLR, hLR'] at hW'
    exact hF.lift c.d.ψ c.d.ker_le R hR R' hR' ⟨W', hW'⟩
  obtain ⟨N, hNz, hN5N, hWN⟩ := c.exists_distinguisher hsingle hshape hβ htβ hKβ hz4.1 hz5.1 hK4
    hβ4 hK5 hβ5 hc45
  have hLN : IsLayerMember c N := IsLayerMember.of_not_commutes c hNz hz4
    (ne_of_linearBlockStandardPair hWN.choose_spec).symm
    (fun h => not_commutes_of_linearBlockStandardPair hWN.choose_spec (commutes_symm h))
  obtain ⟨RN, hRN, hNR⟩ := hLN.exists_fund
  obtain ⟨wN, hwN⟩ := hΩ.classical _ hNz.1
  obtain ⟨hne43, hnc43, hcw43, hnw43⟩ := TypeEPattern.stdPair_data h2 hw4 hw3 ⟨_, hW43⟩
  obtain ⟨hne35, hnc35, hcw35, hnw35⟩ := TypeEPattern.stdPair_data h2 hw3 hw5 ⟨_, hW35⟩
  obtain ⟨hne4N, hnc4N, hcw4N, hnw4N⟩ := TypeEPattern.stdPair_data h2 hw4 hwN hWN
  refine torusFixedP_of_chain_model c ht _ hR4 hR3 hR5 hRN hRM
    (c.modelAdj_of_adj hz4 hz3 hR4 hR3 h4R h3R hw4 hw3 hne43 hnc43 hcw43 hnw43)
    (c.modelAdj_of_adj hz3 hz5 hR3 hR5 h3R h5R hw3 hw5 hne35 hnc35 hcw35 hnw35)
    (hlin hz4 hz3 hR4 hR3 h4R h3R ⟨_, hW43⟩) (hlin hz3 hz5 hR3 hR5 h3R h5R ⟨_, hW35⟩)
    ((c.commutes_iff_fund hz4 hz5 hR4 h4R h5R).mp hc45) (hMcomm 4 R4 hz4 h4R)
    (hMcomm 3 R3 hz3 h3R) (hMcomm 5 R5 hz5 h5R)
    (c.modelAdj_of_adj hz4 hNz hR4 hRN h4R hNR hw4 hwN hne4N hnc4N hcw4N hnw4N)
    ((c.commutes_iff_fund hz5 hNz hR5 h5R hNR).mp hN5N) ?_ ?_ ?_
  · exact fun y hy => c.fixed_of_commutes ht htβ hz4 hβ4 _ (by rw [h4R]; exact ⟨y, hy, rfl⟩)
  · exact fun y hy => c.fixed_of_commutes ht htβ hz3 hβ3 _ (by rw [h3R]; exact ⟨y, hy, rfl⟩)
  · exact fun y hy => c.fixed_of_commutes ht htβ hz5 hβ5 _ (by rw [h5R]; exact ⟨y, hy, rfl⟩)

end CFSG.ClassicalInvolution.RouteD.ETCtx
