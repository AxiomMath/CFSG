module

public import CFSG.ClassicalInvolution.RouteD.TwinTenRow
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSL

public section

namespace CFSG.ClassicalInvolution.RouteD

open scoped MatrixGroups Matrix
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups Commutes modelUniv conjSub conjSub_mul
  conjSub_one InClass IsClassicalMember LocalOddCentral ExactMembers centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCTSystem_standard
  rankOne_eq_range)

variable {p f : ℕ} [hp : Fact p.Prime]

theorem sl4_involution_eq_of_spaces {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {hn : 2 ≤ 4}
    {L₁ : Subgroup SL(4, F)} {i₁ i₂ : SL(4, F)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (hV : minusSpace i₁ = minusSpace i₂) (hW : fixSpace i₁ = fixSpace i₂) : i₁ = i₂ := by
  have c := h₁.isCompl h2
  have hmul : ∀ v : Fin 4 → F, (i₁ : Matrix (Fin 4) (Fin 4) F) *ᵥ v =
      (i₂ : Matrix (Fin 4) (Fin 4) F) *ᵥ v := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      (c.sup_eq_top ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule F (Fin 4 → F))))
    have ha2 : a ∈ minusSpace i₂ := hV ▸ ha
    have hb2 : b ∈ fixSpace i₂ := hW ▸ hb
    rw [Matrix.mulVec_add, Matrix.mulVec_add, mem_minusSpace.mp ha, mem_fixSpace.mp hb,
      mem_minusSpace.mp ha2, mem_fixSpace.mp hb2]
  refine Subtype.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
  simpa using hmul v


theorem fund_sl4_eq_of_commutes (hp2 : p ≠ 2)
    {L₀ L L' : Subgroup (modelUniv .PSL 4 p f hp.out).K}
    (hL₀ : L₀ ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D)
    (hL : L ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D)
    (hL' : L' ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D)
    (hne : L ≠ L₀) (hne' : L' ≠ L₀) (c : Commutes L₀ L) (c' : Commutes L₀ L') : L = L' := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  rw [fundamentalSubgroups_psl_eq (p := p) (f := f) (m := 3) (by norm_num)] at hL₀ hL hL'
  obtain ⟨i₀, h₀⟩ := hL₀
  obtain ⟨i₁, h₁⟩ := hL
  obtain ⟨i₂, h₂'⟩ := hL'
  obtain ⟨le01, le10, -⟩ := le_of_commutes h2 (by norm_num) h₀ h₁ hne.symm c
  obtain ⟨le02, le20, -⟩ := le_of_commutes h2 (by norm_num) h₀ h₂' hne'.symm c'
  have hV0 := h₀.finrank_minusSpace h2
  have hV1 := h₁.finrank_minusSpace h2
  have hV2 := h₂'.finrank_minusSpace h2
  have hW0 := finrank_fixSpace_of_isLongRootSL2 h2 h₀
  have hW1 := finrank_fixSpace_of_isLongRootSL2 h2 h₁
  have hW2 := finrank_fixSpace_of_isLongRootSL2 h2 h₂'
  have e1 : minusSpace i₀ = fixSpace i₁ := Submodule.eq_of_le_of_finrank_eq le01 (by omega)
  have e1' : minusSpace i₁ = fixSpace i₀ := Submodule.eq_of_le_of_finrank_eq le10 (by omega)
  have e2 : minusSpace i₀ = fixSpace i₂ := Submodule.eq_of_le_of_finrank_eq le02 (by omega)
  have e2' : minusSpace i₂ = fixSpace i₀ := Submodule.eq_of_le_of_finrank_eq le20 (by omega)
  have hi : i₁ = i₂ := sl4_involution_eq_of_spaces h2 h₁ (e1'.trans e2'.symm) (e1.symm.trans e2)
  subst hi
  exact (h₁.eq_longRootGroup h2).trans (h₂'.eq_longRootGroup h2).symm


theorem sl_nodes_comm (F : Type) [Field F] (i j : Fin 3) (hij : (i : ℕ) + 1 < j) :
    Commutes (rankOne (SpecialLinear.rootGroup 3 F) i)
      (rankOne (SpecialLinear.rootGroup 3 F) j) := by
  rw [rankOne_eq_range, rankOne_eq_range]
  intro x hx y hy
  exact (weakCTSystem_standard (K := F) 3).comm i j hij x hx y hy

theorem sl_nodes_pair (F : Type) [Field F] (i j : Fin 3) (hj : (j : ℕ) = i + 1) :
    ∃ W, LinearBlockStandardPair F W (rankOne (SpecialLinear.rootGroup 3 F) i)
      (rankOne (SpecialLinear.rootGroup 3 F) j) := by
  rw [rankOne_eq_range, rankOne_eq_range]
  exact ⟨_, (weakCTSystem_standard (K := F) 3).pair i j hj⟩

theorem exists_centre_sl4 (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f)
    {L₀ L : Subgroup (modelUniv .PSL 4 p f hp.out).K}
    (hL₀ : L₀ ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D)
    (hL : L ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D)
    (hne : L ≠ L₀) (hnc : ¬ Commutes L₀ L₀) (c : Commutes L₀ L) :
    ∃ R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D,
      (∃ W, LinearBlockStandardPair (GaloisField p f) W R L₀) ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W R L := by
  obtain ⟨hf, -⟩ := card_galoisField_of_four_le (p := p) (f := f) hq
  have hadm : StatedLieAdmissible .PSL 4 p f :=
    ⟨hp.out, Nat.one_le_iff_ne_zero.mpr hf, by show 2 ≤ 4; omega,
      fun h => by have := congrArg Prod.fst h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this⟩
  have hsc := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSL 4 p f hp.out trivial
    hadm (by decide) (by decide)
  have hl := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .PSL 4 p f hp.out trivial
    hadm
  set D := (modelUniv .PSL 4 p f hp.out).D with hD
  have hB : ∀ i : Fin 3, rankOne D.rootGroup i ∈
      fundamentalSubgroups .PSL (modelUniv .PSL 4 p f hp.out).D := fun i =>
    rankOne_mem_fundamental D (hl i trivial)
  obtain ⟨g, hg⟩ := hsc _ (hB 0) L₀ hL₀
  have hB2 := CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups (hB 2) g
  have h02 : Commutes (rankOne D.rootGroup (0 : Fin 3)) (rankOne D.rootGroup (2 : Fin 3)) :=
    sl_nodes_comm (GaloisField p f) 0 2 (by decide)
  have hc02 : Commutes L₀ (conjSub g (rankOne D.rootGroup (2 : Fin 3))) := by
    rw [hg]
    exact (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff g).mpr h02
  have hne02 : conjSub g (rankOne D.rootGroup (2 : Fin 3)) ≠ L₀ := by
    intro h
    exact hnc (Eq.mp (congrArg (Commutes L₀) h) hc02)
  have hLeq : L = conjSub g (rankOne D.rootGroup (2 : Fin 3)) :=
    fund_sl4_eq_of_commutes hp2 hL₀ hL hB2 hne hne02 c hc02
  obtain ⟨W₀, hW₀⟩ := sl_nodes_pair (GaloisField p f) 0 1 rfl
  obtain ⟨W₁, hW₁⟩ := sl_nodes_pair (GaloisField p f) 1 2 rfl
  refine ⟨conjSub g (rankOne D.rootGroup (1 : Fin 3)),
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups (hB 1) g, ?_, ?_⟩
  · rw [hg]
    exact ⟨_, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm
      (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₀ g)⟩
  · rw [hLeq]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ g⟩

variable {G : Type} [Group G]

theorem TCtx.exists_nodes_D5 [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
    (c : TCtx p f .PSL 4 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .PSL 4 Ω z) {β : Subgroup G} (hβ : β ∈ Ω)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : HasFixedMember Ω K β z) :
    ∃ j : Fin 3 → Subgroup G, (∀ a, j a ∈ Ω) ∧ (∀ a, Commutes K (j a)) ∧
      (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) ∧ Commutes (j 1) (j 2) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 1)) ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 2) := by
  obtain ⟨M, hMΩ, hKM, hβM, hMnc⟩ := hfix
  have hf : 0 < f := Nat.pos_of_ne_zero c.hf
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
    exact not_commutes_self_of_mem c.hΩ c.hK hKM
  obtain ⟨N', hN'z, hN'M, hnc⟩ : ∃ N' ∈ centralizingMembers Ω {z}, N' ≠ M ∧ ¬ Commutes M N' := by
    by_contra hcon
    push Not at hcon
    exact hMnc fun N hN hNM => hcon N hN hNM
  have hMQ : ¬ locImg Ω z M ≤ c.d.Q₁ := fun hMQ =>
    hMnc fun N hN hNM => c.commutes_T_of_ne hMz hMQ hN hNM
  obtain ⟨R_M, hR_M, hMR⟩ := c.exists_fund_of_ne hMz hMK hMQ
  obtain ⟨g, hg⟩ := hsingle M hMΩ
  have hzx : IsClassicalMember p f M (g * z * g⁻¹) := by
    rw [hg]
    exact c.hz.conj g
  have hshape_x : LocalShapeT p f 2 .PSL 4 Ω (g * z * g⁻¹) := hshape.conj c.hΩ.conjInvariant g
  have hP1_x : LocalOddCentral Ω {g * z * g⁻¹} :=
    Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
  obtain ⟨dx⟩ := hshape_x.nonempty_dictT2 c.hY.ne_d4 c.hY.sc c.hΩ hMΩ hzx
  obtain ⟨dx', hQx⟩ := exists_dictT2_of_member c.hY hMΩ hzx dx
  let cx : TCtx p f .PSL 4 Ω M (g * z * g⁻¹) :=
    { hp2 := c.hp2, hq := c.hq, hΩ := c.hΩ, hex := c.hex, hK := hMΩ, hz := hzx, hP1 := hP1_x,
      d := dx', hQ₀ := hQx, hY := c.hY }
  have hKx : K ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    mem_centralizingMembers_of_commutes c.hK hzx.mem hKM
  have hβx : β ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    mem_centralizingMembers_of_commutes hβ hzx.mem hβM
  have hMx : M ∈ centralizingMembers Ω {g * z * g⁻¹} :=
    ⟨hMΩ, le_centralizer_of_isClassicalMember hzx⟩
  have hKQ : ¬ locImg Ω (g * z * g⁻¹) K ≤ cx.d.Q₁ := by
    intro hKQ
    have hcomm : ∀ N ∈ centralizingMembers Ω {g * z * g⁻¹}, N ≠ K → Commutes K N :=
      fun N hN hNK => cx.commutes_T_of_ne hKx hKQ hN hNK
    have hconj : ∃ g' : G, K = conjSub g' M :=
      ⟨g⁻¹, by rw [hg, ← conjSub_mul, inv_mul_cancel, conjSub_one]⟩
    have heq := centralizingMembers_eq_of_twin c.hp2 hf c.hΩ hzx c.hz hconj hKx hcomm
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
    have e1 := centralizingMembers_eq_of_twin c.hp2 hf c.hΩ c.hz hzT hconjz hT₀z
      (fun N hN hNT => c.commutes_T_of_ne hT₀z hQ hN hNT)
    have e2 := centralizingMembers_eq_of_twin c.hp2 hf c.hΩ hzx hzT hconjx hT₀x
      (fun N hN hNT => cx.commutes_T_of_ne hT₀x hT₀Q.le hN hNT)
    have hβz : β ∈ centralizingMembers Ω {z} := by
      have : β ∈ centralizingMembers Ω {zT} := e2 ▸ hβx
      exact e1 ▸ this
    exact hncKβ (c.commutes_K_of_ne hβz hβK)
  obtain ⟨R_T, hR_T, hT₀R⟩ := c.exists_fund_of_ne hT₀z hKT₀.symm hT₀Q'
  have hcomm_R : Commutes R_M R_T :=
    (c.commutes_iff_fund hMz hT₀z hR_M hMR hT₀R).mp hT₀M.symm
  have hne_R : R_T ≠ R_M := fun e => hMT₀ (c.eq_of_locImg_eq hMz hT₀z (by rw [hMR, hT₀R, e]))
  have hnc_R : ¬ Commutes R_M R_M := fun h =>
    not_commutes_self_of_mem c.hΩ hMΩ ((c.commutes_iff_fund hMz hMz hR_M hMR hMR).mpr h)
  obtain ⟨R_c, hR_c, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩ := exists_centre_sl4 c.hp2
    (by have := c.hq; omega) hR_M hR_T hne_R hnc_R hcomm_R
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


end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinSL4Bridge (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSL 4 (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ j : Fin 3 → Subgroup G, (∀ a, j a ∈ conjClass K) → (∀ a, Commutes K (j a)) →
          (∀ a : Fin 3, 1 ≤ a.val → Commutes β (j a)) → Commutes (j 1) (j 2) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 1)) →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (j 0) (j 2)) →
          ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j 0)

theorem twinSL4Pattern_of_bridge (h : TwinSL4Bridge p f) : TwinSL4Pattern p f := by
  intro G _ _ _ hnab K z S hS β hβ t ht hKβ hfix
  obtain ⟨c⟩ := TCtx.nonempty_A3 S.odd S.five S.inClass S.exact (mem_conjClass_self K) S.cls S.p1
    hS
  obtain ⟨j, hjΩ, hjK, hjβ, hj12, hp01, hp02⟩ := c.exists_nodes_D5 (single_class K) hS hβ hKβ hfix
  have hbr := h G hnab K z S hS β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02
  refine ⟨j, hjΩ, hjK, ?_, ?_, ?_, ?_⟩
  · intro a ha x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hjβ a ha t ht.mem x hx).symm
  · intro a b hab h1 h2
    fin_cases a <;> fin_cases b <;>
      first
      | exact absurd rfl hab
      | exact absurd (by unfold edgeD; decide) h1
      | exact absurd (by unfold edgeD; decide) h2
      | exact hj12
      | exact hj12.symm
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | exact hp01
      | exact hp02
      | exact absurd hab (by unfold edgeD; decide)
  · intro a ha
    obtain rfl : a = 0 := Fin.ext ha
    exact hbr

theorem pieceTwinSL4_of_bridge (h : TwinSL4Bridge p f) : PieceTwinSL4 p f :=
  pieceTwinSL4_of_pattern (twinSL4Pattern_of_bridge h)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
