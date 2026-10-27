module

public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem amalgamHypV_of_hyp1223_F4 (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight)
    {T L V H : Subgroup G} (hyp : Hyp1223 G T L V)
    (huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → L ⊔ T ≤ M' →
      M' = Subgroup.normalizer (L : Set G))
    (hTH : T ≤ H) (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) :
    AmalgamHypV ((L ⊔ T) ⊔ H) (L ⊔ T) H T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, hfsu⟩, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨-, -, hO⟩ := h3228 G T L V hfsu
  rw [hyp.conjClosure_eq, conjClosure_eq_of_le_normalizer hTV] at hO
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hyp.irrPlus.2.2.1 hTV
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hVT
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVLT hLTV hVp
  have hO1 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h => hyp.irrPlus.2.1 (le_bot_iff.1 (h ▸ hVO))
  refine ⟨⟨rfl, charTwo_of_inH hyp.qtke.2.1 (hyp.sylow.1.toSylow hyp.sylow.2)
      ⟨le_sup_right, hO1⟩, isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right,
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH, ?_⟩,
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hred⟩, ?_⟩
  · by_contra hne
    obtain ⟨M', hM', hle⟩ := exists_inM_of_pCoreOf_ne_bot hne
    rw [huniq M' hM' (le_sup_left.trans hle)] at hle
    exact hHM (le_sup_right.trans hle)
  · rw [← hO]
    have hCN : L ⊔ T ≤ Subgroup.normalizer
        (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTV)
    refine le_antisymm ?_ (F7.pCoreOf_mono_of_le_normalizer inf_le_left hCN)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hO ▸ inf_le_right)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem lemma12_4_1_of_F4
    (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h3228 : Stmt3_2_2_eight)
    (h1227 : Stmt12_2_7_F4) (h1232 : Cor12_3_2_F4) : Lemma12_4_1_F4 := by
  intro G _ _ T L V hyp hCZ hV hs
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon

  obtain ⟨-, h331B⟩ := h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow
  obtain ⟨⟨-, -, huniq⟩, -, ⟨H, hH⟩, -, -⟩ := h331B L hyp.maximal hyp.quasisimple
  rw [hyp.conjClosure_eq] at huniq hH
  have hTH : T ≤ H := hH.1.1
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := hH.2.1
  have hamal := amalgamHypV_of_hyp1223_F4 h1222 h3228 hyp huniq hTH hHM
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  by_cases hW : weakClosureW0 T V ≤ pCoreOf 2 H
  ·
    have hb := even_critDist_of_weakClosureW0_le_G₂ hamal hV1 hW
    obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hamal hV1
    have hc := commutator_V_Vv_of_even hamal hV1 hb hγ hVγ
    obtain ⟨x, rfl⟩ := exists_smul_eq_γ₀ (vtype_eq_false_of_even hamal.gen (by rw [hγ]; exact hb))
    rw [Vv_smul_γ₀ hamal.normalizes] at hc
    obtain ⟨hne, hcl, -, -⟩ := hc
    have e1 : conjSub (x : G) V = CFSG.conjugate V (x : G)⁻¹ := by
      ext y
      show y ∈ conjSub (x : G) V ↔ y ∈ conjSubgroup V (x : G)⁻¹
      rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
    rw [e1] at hne hcl
    exact hcon _ hne hcl

  obtain ⟨g, hgT, hgO⟩ : ∃ g : G, conjSub g V ≤ T ∧ ¬ conjSub g V ≤ pCoreOf 2 H := by
    by_contra h
    push Not at h
    exact hW (iSup₂_le fun g hg => h g hg)
  have hAeq : conjSub g V = conjSubgroup V g⁻¹ := by
    ext y
    rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
  rw [hAeq] at hgT hgO
  set A := conjSubgroup V g⁻¹ with hAdef
  have hAel : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hV g⁻¹
  have hsA : E3.sParam hAel = E3.sParam hV := E3.sParam_conj hV g⁻¹ hAel

  obtain ⟨⟨hred2, hCT, -, -⟩, -⟩ := h1227 G T L V H hyp hCZ hH
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_left
  have hVHH : VZ T H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hTH (hZT hz))) (H.inv_mem hh)
  have hredVH : IsTwoReducedIn H (VZ T H) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVHH, hred2⟩
  have hVHel : IsElemAbelian 2 (VZ T H) := hredVH.2.2.1
  have hVHp : IsPGroup 2 (VZ T H) := fun x => ⟨1, Subtype.ext (by simpa using hVHel.2 x x.2)⟩
  have hAH : A ≤ H := hgT.trans hTH
  have hAV : ¬ A ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
    hgO (by rw [← hCT]; exact le_inf hgT h)

  have hA2 : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B ≤ 1 →
      VZ T H ⊓ Subgroup.centralizer (B : Set G) = VZ T H ⊓ Subgroup.centralizer (A : Set G) := by
    intro B hBA hm
    have hs' : E3.mQuot A B < E3.sParam hAel := by
      rw [hsA]
      omega
    exact (E3.e3_6 hAel hBA le_rfl hs' hVHp).1.symm
  by_cases hsolv : Group.IsSolvable ↥H
  ·
    have hHN := hredVH.2.1
    have hX : E3.aSet 2 (autI hVHel H) = ∅ :=
      E3.aSet_two_eq_empty (fun w => IntMod.sq_eq_one w) (isSolvable_autI hVHel hHN hsolv)
        (pCore_autI_eq_bot_of_reduced hredVH hVHel)
    have hAN : A ≤ Subgroup.normalizer (VZ T H : Set G) := hAH.trans hHN
    have hbar1 : autI hVHel A ≠ ⊥ := fun hb => hAV ((autI_eq_bot_iff hVHel hAN).1 hb)
    obtain ⟨B', hB'A, hmB', hfix⟩ : ∃ B' ≤ autI hVHel A, E3.mQuot (autI hVHel A) B' < 2 ∧
        fixV B' ≠ fixV (autI hVHel A) := by
      by_contra hcon'
      push Not at hcon'
      have hmem : autI hVHel A ∈ E3.aSet 2 (autI hVHel H) :=
        ⟨autI_mono hVHel hAH, hbar1, isElemAbelian2_autI hVHel hAel hAN, hcon'⟩
      rw [hX] at hmem
      exact hmem
    have hBA : preI hVHel A hAN B' ≤ A := preI_le hVHel
    have hmAB : E3.mQuot A (preI hVHel A hAN B') ≤ 1 := by
      rw [← E3.mQuot_autI_preI hVHel hAN hB'A]
      omega
    have hC := hA2 _ hBA hmAB
    apply hfix
    rw [← autI_preI hVHel (hA := hAN) hB'A]
    ext v
    rw [mem_fixV_autI hVHel (hBA.trans hAN) v, mem_fixV_autI hVHel hAN v]
    constructor
    · intro hv
      have h1 : v.val ∈ VZ T H ⊓ Subgroup.centralizer
          ((preI hVHel A hAN B' : Subgroup G) : Set G) := ⟨v.val_mem, hv⟩
      rw [hC] at h1
      exact h1.2
    · intro hv
      have h1 : v.val ∈ VZ T H ⊓ Subgroup.centralizer (A : Set G) := ⟨v.val_mem, hv⟩
      rw [← hC] at h1
      exact h1.2

  rcases h1232 G T L V H hyp hCZ hH with h | ⟨hLie, -, -, hsum⟩
  · exact hsolv h
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hsylH : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH
  rw [← VZ_eq_VZ_oTwoUpper hsylH] at hsum
  obtain ⟨W, hW, hWle⟩ : ∃ W : Subgroup G, IsA5ModuleUnder (oTwoUpper H) W ∧
      W ≤ ⁅VZ T H, oTwoUpper H⁆ := by
    rcases hsum with h | ⟨W₁, W₂, hW₁, -, -, hsup⟩
    · exact ⟨_, h, le_rfl⟩
    · exact ⟨W₁, hW₁, hsup ▸ le_sup_left⟩
  have hWV : W ≤ VZ T H :=
    hWle.trans (commutator_le_of_le_normalizer (hKH.trans hredVH.2.1))
  have hO2K : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.centralizer (VZ T H : Set G) := by
    have h1 : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H := F7.pCoreOf_mono_of_le_normalizer hKH hHK
    rw [← hCT] at h1
    exact h1.trans inf_le_right
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hLie
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hCW := inf_centralizer_le_of_a5Module hW hWV e.isSimpleGroup hO2K
  exact A5Mod.false_of_a5Module hKH hHK (fun h hh => exists_pow_mem_oTwoUpper H hh) hredVH hWV hW
    hCW hAH hAel hAV hA2

end CFSG.Quasithin.H13
