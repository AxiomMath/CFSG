module

public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCTSystem_standard
  rankOne_eq_range)


theorem exists_centre_sl4_three
    {L₀ L : Subgroup (modelUniv .PSL 4 3 1 Nat.prime_three).K}
    (hL₀ : L₀ ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D)
    (hL : L ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D)
    (hne : L ≠ L₀) (hnc : ¬ Commutes L₀ L₀) (c : Commutes L₀ L) :
    ∃ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D,
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R L₀) ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R L := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨hp, Nat.one_pos, by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hsc := ModelFacts.fundamentalSingleClass .PSL 4 3 1 hp trivial hadm (by decide) (by decide)
  have hB := rankOne_mem_fund_sl4_three hadm
  set D := (modelUniv .PSL 4 3 1 Nat.prime_three).D with hD
  obtain ⟨g, hg⟩ := hsc _ (hB 0) L₀ hL₀
  have hB2 := CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups (hB 2) g
  have h02 : Commutes (rankOne D.rootGroup (0 : Fin 3)) (rankOne D.rootGroup (2 : Fin 3)) :=
    sl_nodes_comm (GaloisField 3 1) 0 2 (by decide)
  have hc02 : Commutes L₀ (conjSub g (rankOne D.rootGroup (2 : Fin 3))) := by
    rw [hg]
    exact (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff g).mpr h02
  have hne02 : conjSub g (rankOne D.rootGroup (2 : Fin 3)) ≠ L₀ := by
    intro h
    exact hnc (Eq.mp (congrArg (Commutes L₀) h) hc02)
  have hLeq : L = conjSub g (rankOne D.rootGroup (2 : Fin 3)) :=
    fund_sl4_eq_of_commutes (p := 3) (f := 1) (by norm_num) hL₀ hL hB2 hne hne02 c hc02
  obtain ⟨W₀, hW₀⟩ := sl_nodes_pair (GaloisField 3 1) 0 1 rfl
  obtain ⟨W₁, hW₁⟩ := sl_nodes_pair (GaloisField 3 1) 1 2 rfl
  refine ⟨conjSub g (rankOne D.rootGroup (1 : Fin 3)),
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups (hB 1) g, ?_, ?_⟩
  · rw [hg]
    exact ⟨_, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm
      (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₀ g)⟩
  · rw [hLeq]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ g⟩

theorem TCtx3.exists_nodes_D5 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
    {K : Subgroup G} (c : TCtx3 .PSL 4 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfix : HasFixedMember Ω K β z) :
    ∃ j : Fin 3 → Subgroup G, (∀ a, j a ∈ Ω) ∧ (∀ a, Commutes K (j a)) ∧
      (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) ∧ Commutes (j 1) (j 2) ∧
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j 0) (j 1)) ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (j 0) (j 2) := by
  obtain ⟨M, hMΩ, hKM, hβM, hMnc⟩ := hfix
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hKM.symm
  have hβK : β ≠ K := fun e => by
    obtain ⟨W, hW⟩ := hKβ
    exact ne_of_linearBlockStandardPair hW e.symm
  have hncKβ : ¬ Commutes K β := by
    obtain ⟨W, hW⟩ := hKβ
    exact not_commutes_of_linearBlockStandardPair hW
  have hMK : M ≠ K := fun e => by
    subst e
    exact not_commutes_self3 c.hz hKM
  obtain ⟨N', hN'z, hN'M, hnc⟩ : ∃ N' ∈ centralizingMembers Ω {z}, N' ≠ M ∧ ¬ Commutes M N' := by
    by_contra hcon
    push Not at hcon
    exact hMnc fun N hN hNM => hcon N hN hNM
  have hMQ : ¬ locImg Ω z M ≤ c.d.Q₁ := fun hMQ =>
    hMnc fun N hN hNM => c.commutes_T_of_ne hMz hMQ hN hNM
  obtain ⟨R_M, hR_M, hMR⟩ := c.exists_fund_of_ne hMz hMK hMQ
  obtain ⟨g, hg⟩ := hsingle M hMΩ
  have hzx : IsClassicalMember3 M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  have hO3_x : LocalOddThreeFree3 Ω (g * z * g⁻¹) :=
    localOddThreeFree3_conj c.hΩ.conjInvariant g z c.hO3
  obtain ⟨dx', hQx⟩ := exists_dictT2_of_member3 c.hY hMΩ hzx
    (ShapeDictT2.conj3 c.hΩ.conjInvariant g c.d)
  let cx : TCtx3 .PSL 4 Ω M (g * z * g⁻¹) :=
    { hΩ := c.hΩ, hex := c.hex, hK := hMΩ, hz := hzx, hP1 := hP1_x, hO3 := hO3_x,
      d := dx', hQ₀ := hQx, hY := c.hY }
  have hKx : K ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    mem_centralizingMembers_of_commutes c.hK hzx.mem hKM
  have hβx : β ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    mem_centralizingMembers_of_commutes hβ hzx.mem hβM
  have hMx : M ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    ⟨hMΩ, isSubnormal_le hzx.subnormal⟩
  have hKQ : ¬ locImg Ω (g * z * g⁻¹) K ≤ cx.d.Q₁ := by
    intro hKQ
    have hcomm : ∀ N ∈ centralizingMembers Ω {g * z * g⁻¹}, N ≠ K → Commutes K N :=
      fun N hN hNK => cx.commutes_T_of_ne hKx hKQ hN hNK
    have hconj : ∃ g' : G, K = conjSub g' M :=
      ⟨g⁻¹, by rw [hg, ← conjSub_mul, inv_mul_cancel, conjSub_one]⟩
    have heq := centralizingMembers_eq_of_twin3 c.hΩ hzx c.hz hconj hKx hcomm
    have hN'x : N' ∈ centralizingMembers Ω {g * z * g⁻¹} := heq ▸ hN'z
    exact hnc (cx.commutes_K_of_ne hN'x hN'M)
  obtain ⟨T₀, hT₀x, hT₀Q⟩ := cx.exists_twin
  have hKT₀ : K ≠ T₀ := fun e => hKQ (e ▸ hT₀Q.le)
  have hT₀K : Commutes T₀ K := cx.commutes_T_of_ne hT₀x (hT₀Q.le) hKx hKT₀
  have hβT₀ : β ≠ T₀ := fun e => hncKβ (e ▸ hT₀K.symm)
  have hT₀β : Commutes T₀ β := cx.commutes_T_of_ne hT₀x (hT₀Q.le) hβx hβT₀
  have hMT₀ : M ≠ T₀ := (cx.twin_ne hT₀x hT₀Q.le).symm
  have hT₀M : Commutes T₀ M := cx.commutes_T_of_ne hT₀x (hT₀Q.le) hMx hMT₀
  have hT₀Ω : T₀ ∈ Ω := hT₀x.1
  have hT₀z : T₀ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hT₀Ω c.hz.mem hT₀K
  have hT₀Q' : ¬ locImg Ω z T₀ ≤ c.d.Q₁ := by
    intro hQ
    obtain ⟨zT, hzT⟩ := c.hΩ.classical T₀ hT₀Ω
    have hconjz : ∃ g' : G, T₀ = conjSub g' K := hsingle T₀ hT₀Ω
    have hconjx : ∃ g' : G, T₀ = conjSub g' M := by
      obtain ⟨g₁, hg₁⟩ := hconjz
      exact ⟨g₁ * g⁻¹, by rw [hg₁, hg, ← conjSub_mul]; simp [mul_assoc]⟩
    have e1 := centralizingMembers_eq_of_twin3 c.hΩ c.hz hzT hconjz hT₀z
      (fun N hN hNT => c.commutes_T_of_ne hT₀z hQ hN hNT)
    have e2 := centralizingMembers_eq_of_twin3 c.hΩ hzx hzT hconjx hT₀x
      (fun N hN hNT => cx.commutes_T_of_ne hT₀x hT₀Q.le hN hNT)
    have hβz : β ∈ centralizingMembers Ω {z} := by
      have : β ∈ centralizingMembers Ω {zT} := e2 ▸ hβx
      exact e1 ▸ this
    exact hncKβ (c.commutes_K_of_ne hβz hβK)
  obtain ⟨R_T, hR_T, hT₀R⟩ := c.exists_fund_of_ne hT₀z hKT₀.symm hT₀Q'
  have hcomm_R : Commutes R_M R_T :=
    (c.commutes_iff_fund hMz hT₀z hR_M hMR hT₀R).mp hT₀M.symm
  have hne_R : R_T ≠ R_M := fun e => hMT₀ (c.eq_of_locImg_eq hMz hT₀z (by rw [hMR, hT₀R, e]))
  have hnc_R : ¬ Commutes R_M R_M := fun h => by
    obtain ⟨zM, hzM⟩ := c.hΩ.classical M hMΩ
    exact not_commutes_self3 hzM ((c.commutes_iff_fund hMz hMz hR_M hMR hMR).mpr h)
  obtain ⟨R_c, hR_c, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩ :=
    exists_centre_sl4_three hR_M hR_T hne_R hnc_R hcomm_R
  obtain ⟨N₁, hN₁z, hN₁K, -, hN₁R⟩ := c.exists_member_of_fund hR_c
  obtain ⟨V₁, hV₁⟩ := c.stdPair_of_fund hN₁z hMz hW₁ hN₁R hMR
  obtain ⟨V₂, hV₂⟩ := c.stdPair_of_fund hN₁z hT₀z hW₂ hN₁R hT₀R
  refine ⟨![N₁, M, T₀], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    fin_cases a
    · exact hN₁z.1
    · exact hMΩ
    · exact hT₀Ω
  · intro a
    fin_cases a
    · exact c.commutes_K_of_ne hN₁z hN₁K
    · exact hKM
    · exact hT₀K.symm
  · intro a ha
    fin_cases a
    · simp at ha
    · exact hβM
    · exact hT₀β.symm
  · exact hT₀M.symm
  · exact ⟨V₁, hV₁⟩
  · exact ⟨V₂, hV₂⟩

end CFSG.ClassicalInvolution.Q3.Q3TC
